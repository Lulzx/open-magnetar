//! Sum-check per docs/spec/03-sumcheck.md and CONVENTIONS C3.
//! Mirrors `reference/openmagnetar/sumcheck.py` byte for byte in its
//! transcript interaction.

use core::fmt;

use om_field::{K, U256};
use om_transcript::{Transcript, u64le};

use rayon::prelude::*;

use crate::mle::{PAR_THRESHOLD, bind_low_in_place};

/// Verification failure (Python `sumcheck.VerificationError`; defined here
/// and reused by every later crate, per C8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerificationError(String);

impl VerificationError {
    /// A verification error with the given message.
    pub fn new(message: impl Into<String>) -> Self {
        VerificationError(message.into())
    }

    /// The error message.
    pub fn message(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for VerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for VerificationError {}

/// A sum-check proof: per round, `[g(t_0), g(t_2), …, g(t_d)]` (C3) —
/// `degree` field elements, omitting `t_1 = 1`, which the verifier derives
/// as `g(1) = claim + g(0)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckProof {
    pub round_msgs: Vec<Vec<K>>,
}

/// A boxed summand combine function over per-table values, as built by
/// [`batched_combine`] and as accepted (by reference) by [`sumcheck_prove`].
/// `Send + Sync` so the prover may evaluate it from rayon threads.
pub type BoxedCombine = Box<dyn Fn(&[K]) -> K + Send + Sync>;

/// Normative cap on one powers-of-γ claim batch (spec 03 §3.6):
/// `(n−1)/|K| < 2^{-120}` only up to `n = 256`.
pub const MAX_BATCH_CLAIMS: usize = 256;

fn sublabel(label: &[u8], suffix: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(label.len() + suffix.len());
    out.extend_from_slice(label);
    out.extend_from_slice(suffix);
    out
}

/// The transcript binding run by both parties before round 1 (spec 03 §3.4;
/// Python `sumcheck._init`, also used directly by `router.py`):
///
/// ```text
/// absorb_k    (label ‖ "/claim",  claim)
/// absorb_bytes(label ‖ "/params", u64le(num_vars) ‖ u64le(degree))
/// ```
pub fn sumcheck_init(
    transcript: &mut Transcript,
    label: &[u8],
    claim: K,
    num_vars: usize,
    degree: usize,
) {
    transcript.absorb_k(&sublabel(label, b"/claim"), claim);
    let mut params = [0u8; 16];
    params[..8].copy_from_slice(&u64le(num_vars as u64));
    params[8..].copy_from_slice(&u64le(degree as u64));
    transcript.absorb_bytes(&sublabel(label, b"/params"), &params);
}

/// Evaluate at `r` the unique polynomial of degree `< ys.len()` with value
/// `ys[k]` at the small-integer point `t_k` (C1), by the Lagrange formula
/// of spec 03 §3.4 (characteristic 2: subtraction is addition).
pub fn interpolate_eval(ys: &[K], r: K) -> K {
    let n = ys.len();
    let ts: Vec<K> = (0..n).map(|k| K::t(k as u128)).collect();
    let mut acc = K::ZERO;
    for k in 0..n {
        let (mut num, mut den) = (K::ONE, K::ONE);
        for j in 0..n {
            if j != k {
                num *= r + ts[j];
                den *= ts[k] + ts[j];
            }
        }
        acc += ys[k] * num / den;
    }
    acc
}

/// `Σ_i combine([T[i] for T in tables])` over equal-length tables.
///
/// Parallel for large tables: `K` addition is XOR, so the reduction order
/// does not affect the result. This is the honest prover's claim sum that
/// callers compute before [`sumcheck_prove`].
///
/// # Panics
/// Panics if `tables` is empty.
pub fn combine_sum(tables: &[Vec<K>], combine: &(dyn Fn(&[K]) -> K + Sync)) -> K {
    assert!(!tables.is_empty(), "combine_sum: no tables");
    let size = tables[0].len();
    if size >= PAR_THRESHOLD {
        let n = tables.len();
        let (acc, _) = (0..size)
            .into_par_iter()
            .fold(
                || (K::ZERO, Vec::with_capacity(n)),
                |(mut acc, mut vals), i| {
                    vals.clear();
                    vals.extend(tables.iter().map(|tb| tb[i]));
                    acc += combine(&vals);
                    (acc, vals)
                },
            )
            .reduce(
                || (K::ZERO, Vec::new()),
                |(a, _), (b, scratch)| (a + b, scratch),
            );
        acc
    } else {
        let mut acc = K::ZERO;
        let mut vals: Vec<K> = Vec::with_capacity(tables.len());
        for i in 0..size {
            vals.clear();
            vals.extend(tables.iter().map(|tb| tb[i]));
            acc += combine(&vals);
        }
        acc
    }
}

/// Fast degree-2 round evaluations `[g(0), g(1), g(t_2)]` for the product of
/// two tables `a[i] * b[i]`, accumulating unreduced `U256` products and
/// using the characteristic-2 identity `g(X) = s0 + (s0 + s1 + sd) X + sd X^2`
/// where `sd = Σ_i (a[2i] + a[2i+1])(b[2i] + b[2i+1])`.
pub fn sumcheck_round_evals_mul2(a: &[K], b: &[K]) -> [K; 3] {
    let half = a.len() / 2;
    let [u0, u1, ud] = if a.len() >= PAR_THRESHOLD {
        (0..half)
            .into_par_iter()
            .with_min_len(2048)
            .fold(
                || [U256::ZERO; 3],
                |mut acc, i| {
                    let (a0, a1) = (a[2 * i], a[2 * i + 1]);
                    let (b0, b1) = (b[2 * i], b[2 * i + 1]);
                    acc[0] += a0.clmul(b0);
                    acc[1] += a1.clmul(b1);
                    acc[2] += (a0 + a1).clmul(b0 + b1);
                    acc
                },
            )
            .reduce(
                || [U256::ZERO; 3],
                |mut x, y| {
                    x[0] += y[0];
                    x[1] += y[1];
                    x[2] += y[2];
                    x
                },
            )
    } else {
        let mut acc = [U256::ZERO; 3];
        for i in 0..half {
            let (a0, a1) = (a[2 * i], a[2 * i + 1]);
            let (b0, b1) = (b[2 * i], b[2 * i + 1]);
            acc[0] += a0.clmul(b0);
            acc[1] += a1.clmul(b1);
            acc[2] += (a0 + a1).clmul(b0 + b1);
        }
        acc
    };
    let (s0, s1, sd) = (u0.reduce(), u1.reduce(), ud.reduce());
    [s0, s1, s0 + (s0 + s1 + sd).mul_x() + sd.mul_x().mul_x()]
}

/// One round's evaluations `[g(t_0), …, g(t_degree)]` for the low variable
/// of `tables`, i.e. `Σ_i combine` of the pair interpolants
/// `T[2i] + t·(T[2i] + T[2i+1])` at each `t_k`, `k = 0..=degree`.
///
/// Parallel for large tables (exact: each `g(t_k)` is a XOR-sum of the same
/// per-`i` terms as the sequential loop).
pub fn sumcheck_round_evals(
    tables: &[Vec<K>],
    combine: &(dyn Fn(&[K]) -> K + Sync),
    degree: usize,
) -> Vec<K> {
    if tables.len() == 2
        && degree == 2
        && combine(&[K::ONE, K::ONE]) == K::ONE
        && combine(&[K::ONE, K::ZERO]) == K::ZERO
        && combine(&[K::ZERO, K::ONE]) == K::ZERO
        && combine(&[K::ZERO, K::ZERO]) == K::ZERO
    {
        return sumcheck_round_evals_mul2(&tables[0], &tables[1]).to_vec();
    }
    let half = tables[0].len() / 2;
    let n = tables.len();
    if tables[0].len() >= PAR_THRESHOLD {
        let (ev, ..) = (0..half)
            .into_par_iter()
            .with_min_len(1024)
            .fold(
                || {
                    (
                        vec![K::ZERO; degree + 1],
                        vec![K::ZERO; n],
                        vec![K::ZERO; n],
                        vec![K::ZERO; n],
                    )
                },
                |(mut ev, mut base, mut diff, mut vals), i| {
                    for (idx, table) in tables.iter().enumerate() {
                        let (a, b) = (table[2 * i], table[2 * i + 1]);
                        base[idx] = a;
                        diff[idx] = a + b;
                    }
                    ev[0] += combine(&base);
                    for (k, slot) in ev.iter_mut().enumerate().skip(1) {
                        let ku = k as u128;
                        for idx in 0..n {
                            vals[idx] = base[idx] + diff[idx].mul_t(ku);
                        }
                        *slot += combine(&vals);
                    }
                    (ev, base, diff, vals)
                },
            )
            .reduce(
                || {
                    (
                        vec![K::ZERO; degree + 1],
                        Vec::new(),
                        Vec::new(),
                        Vec::new(),
                    )
                },
                |(mut a, _, _, _), (b, base, diff, vals)| {
                    for (x, y) in a.iter_mut().zip(&b) {
                        *x += *y;
                    }
                    (a, base, diff, vals)
                },
            );
        ev
    } else {
        let mut ev = vec![K::ZERO; degree + 1];
        let mut base = vec![K::ZERO; n];
        let mut diff = vec![K::ZERO; n];
        let mut vals = vec![K::ZERO; n];
        for i in 0..half {
            for (idx, table) in tables.iter().enumerate() {
                let (a, b) = (table[2 * i], table[2 * i + 1]);
                base[idx] = a;
                diff[idx] = a + b;
            }
            ev[0] += combine(&base);
            for (k, slot) in ev.iter_mut().enumerate().skip(1) {
                let ku = k as u128;
                for idx in 0..n {
                    vals[idx] = base[idx] + diff[idx].mul_t(ku);
                }
                *slot += combine(&vals);
            }
        }
        ev
    }
}

/// Prove `Σ_b combine([T[b] for T in tables]) == claim`, where `combine`
/// must have degree at most `degree` in each variable (spec 03 §3.5).
///
/// `tables` is taken by value because the prover binds the tables in place
/// round by round (Python copies them internally). Bit-valued tables,
/// which Python accepts and coerces, must be converted by the caller via
/// [`K::from_bit`].
///
/// Returns `(proof, challenges r (x_1 first), [MLE of each table at r])`.
/// With `0` variables the proof is empty and the evals are `[T_k[0]]`.
///
/// # Panics
/// Panics where Python raises `ValueError`: `degree < 1`; no tables, or
/// tables not sharing a nonzero power-of-two length; or the claim being
/// inconsistent with the tables (`g(0) + g(1) != claim` in some round).
pub fn sumcheck_prove(
    claim: K,
    tables: Vec<Vec<K>>,
    combine: &(dyn Fn(&[K]) -> K + Sync),
    degree: usize,
    transcript: &mut Transcript,
    label: &[u8],
) -> (SumcheckProof, Vec<K>, Vec<K>) {
    assert!(!tables.is_empty(), "sumcheck_prove: no tables");
    let m = tables[0].len().trailing_zeros() as usize;
    let (proof, rs, tables) =
        sumcheck_prove_rounds(claim, tables, combine, degree, m, transcript, label);
    (proof, rs, tables.iter().map(|t| t[0]).collect())
}

/// [`sumcheck_prove`] over only the low `rounds` variables of the
/// tables: the claim is `sum_x combine(tables at x)` over all
/// entries, the sum-check binds `rounds` variables (low first) and
/// returns the bound tables of length `size / 2^rounds`. With
/// `rounds = log2(size)` it is [`sumcheck_prove`]. The transcript
/// records `num_vars = rounds`, exactly as [`sumcheck_prove`] would
/// on tables split into `size / 2^rounds` blocks whose `combine` sums
/// over the blocks.
///
/// # Panics
/// As [`sumcheck_prove`], plus if `2^rounds` exceeds the table length.
pub fn sumcheck_prove_rounds(
    claim: K,
    mut tables: Vec<Vec<K>>,
    combine: &(dyn Fn(&[K]) -> K + Sync),
    degree: usize,
    rounds: usize,
    transcript: &mut Transcript,
    label: &[u8],
) -> (SumcheckProof, Vec<K>, Vec<Vec<K>>) {
    assert!(degree >= 1, "degree must be >= 1");
    assert!(!tables.is_empty(), "sumcheck_prove: no tables");
    let size = tables[0].len();
    assert!(
        size != 0 && size.is_power_of_two() && tables.iter().all(|t| t.len() == size),
        "tables must share a power-of-two length"
    );
    let m = rounds;
    assert!(1usize << m <= size, "more rounds than table variables");
    sumcheck_init(transcript, label, claim, m, degree);
    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    let mut msgs = Vec::with_capacity(m);
    let mut rs = Vec::with_capacity(m);
    let mut cur = claim;
    for _ in 0..m {
        // Evaluations of g_i at t_0, t_1 (check only), t_2..t_degree.
        let ev = sumcheck_round_evals(&tables, combine, degree);
        assert_eq!(
            ev[0] + ev[1],
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let mut msg = Vec::with_capacity(degree);
        msg.push(ev[0]);
        msg.extend_from_slice(&ev[2..]);
        transcript.absorb_ks(&msg_label, &msg);
        let r = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(r);
        cur = interpolate_eval(&ev, r);
        for t in &mut tables {
            bind_low_in_place(t, r);
        }
    }
    (SumcheckProof { round_msgs: msgs }, rs, tables)
}

/// Verify a sum-check proof (spec 03 §3.4), returning
/// `(r, expected value of the summand at r)`. The verifier never accepts or
/// rejects a *value*: the caller compares the returned value with `g(r)`.
///
/// # Errors
/// Returns [`VerificationError`] if the number of rounds is not `num_vars`
/// (checked before any transcript interaction, as in Python) or if a round
/// message does not have exactly `degree` elements (checked per round, in
/// round order, before that round is absorbed).
///
/// # Panics
/// Panics if `degree < 1` (Python raises `ValueError`).
pub fn sumcheck_verify(
    claim: K,
    num_vars: usize,
    degree: usize,
    proof: &SumcheckProof,
    transcript: &mut Transcript,
    label: &[u8],
) -> Result<(Vec<K>, K), VerificationError> {
    assert!(degree >= 1, "degree must be >= 1");
    if proof.round_msgs.len() != num_vars {
        return Err(VerificationError::new("wrong number of rounds"));
    }
    sumcheck_init(transcript, label, claim, num_vars, degree);
    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    let mut rs = Vec::with_capacity(num_vars);
    let mut cur = claim;
    for msg in &proof.round_msgs {
        if msg.len() != degree {
            return Err(VerificationError::new("malformed round message"));
        }
        transcript.absorb_ks(&msg_label, msg);
        let r = transcript.challenge_k(&chal_label);
        // Values at t_0, t_1 (derived), t_2..t_d.
        let mut ys = Vec::with_capacity(degree + 1);
        ys.push(msg[0]);
        ys.push(cur + msg[0]);
        ys.extend_from_slice(&msg[1..]);
        cur = interpolate_eval(&ys, r);
        rs.push(r);
    }
    Ok((rs, cur))
}

/// Random-linear-combination batching of equal-`num_vars` claims
/// (spec 03 §3.6): absorbs `label ‖ "/claims"`, squeezes
/// `γ = challenge_k(label ‖ "/gamma")`, and returns
/// `(coeffs [1, γ, γ^2, …], combined claim Σ_i γ^i claim_i)`.
///
/// # Panics
/// Panics if there are more than [`MAX_BATCH_CLAIMS`] (256) claims, before
/// any transcript interaction. Python raises `ValueError` here (a caller
/// bug, not a verification failure), which maps to a panic as in
/// `om-transcript`.
pub fn batch_claims(claims: &[K], transcript: &mut Transcript, label: &[u8]) -> (Vec<K>, K) {
    assert!(
        claims.len() <= MAX_BATCH_CLAIMS,
        "powers-of-gamma batching is limited to 256 claims (03.6)"
    );
    transcript.absorb_ks(&sublabel(label, b"/claims"), claims);
    let gamma = transcript.challenge_k(&sublabel(label, b"/gamma"));
    let mut coeffs = Vec::with_capacity(claims.len());
    let mut p = K::ONE;
    for _ in claims {
        coeffs.push(p);
        p *= gamma;
    }
    let mut combined = K::ZERO;
    for (&c, &x) in coeffs.iter().zip(claims) {
        combined += c * x;
    }
    (coeffs, combined)
}

/// Build a single `combine` over the concatenated table list (spec 03 §3.6):
/// the returned function splits its input by `arities`, applies the
/// corresponding per-claim `combine`, and returns
/// `Σ_i coeffs[i] · combines[i](slice_i)`.
///
/// # Panics
/// Panics if `coeffs`, `combines`, and `arities` have different lengths
/// (Python's `zip` would silently truncate). The returned function panics
/// if its input is shorter than the sum of `arities`.
pub fn batched_combine(
    coeffs: Vec<K>,
    combines: Vec<BoxedCombine>,
    arities: Vec<usize>,
) -> BoxedCombine {
    assert_eq!(
        coeffs.len(),
        combines.len(),
        "batched_combine: length mismatch"
    );
    assert_eq!(
        coeffs.len(),
        arities.len(),
        "batched_combine: length mismatch"
    );
    Box::new(move |vals: &[K]| {
        let mut out = K::ZERO;
        let mut pos = 0;
        for ((&c, f), &a) in coeffs.iter().zip(&combines).zip(&arities) {
            out += c * f(&vals[pos..pos + a]);
            pos += a;
        }
        out
    })
}

// ---- Spec 03 §3.9: Univariate skip (version-2 extension) ----

/// A sum-check proof with a `k`-variable univariate skip in round 0 (spec 03 §3.9):
/// `skip_msg` holds the `d · (2^k - 1)` evaluations `s(t_j)` for `j = 0..=d_s`
/// omitting `j = 2^k - 1`, and `round_msgs` holds the `m - k` standard round messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnivariateSkipProof {
    pub skip_msg: Vec<K>,
    pub round_msgs: Vec<Vec<K>>,
}

/// Lagrange basis weights `[L_0(z), …, L_{2^k - 1}(z)]` on the `B`-subspace
/// `D = {t_0, …, t_{2^k - 1}}` (spec 03 §3.9). For `a < 2^k` and `z = t_b` (`b < 2^k`),
/// `L_a(t_b) = [a == b]`.
///
/// # Panics
/// Panics if `k == 0` or `k > 16`.
pub fn lagrange_subspace_weights(k: usize, z: K) -> Vec<K> {
    assert!((1..=16).contains(&k), "skip parameter k must be in 1..=16");
    let dom = 1usize << k;
    let ts: Vec<K> = (0..dom).map(|a| K::t(a as u128)).collect();
    // If z is one of the subspace points t_b, return the unit vector e_b directly.
    for (b, &tb) in ts.iter().enumerate() {
        if z == tb {
            let mut out = vec![K::ZERO; dom];
            out[b] = K::ONE;
            return out;
        }
    }
    // Common product P(z) = Π_{b < 2^k} (z + t_b), and on an F_2-linear subspace
    // Π_{b != a} (t_a + t_b) = Π_{u != 0} t_u is a non-zero constant C independent of a!
    let mut prod_num = K::ONE;
    let mut den_const = K::ONE;
    for (u, &tu) in ts.iter().enumerate() {
        prod_num *= z + tu;
        if u != 0 {
            den_const *= tu;
        }
    }
    let factor = prod_num / den_const;
    ts.iter().map(|&ta| factor / (z + ta)).collect()
}

/// Bind the low `k` variables of `table` against the Lagrange subspace weights
/// `weights = lagrange_subspace_weights(k, z)`:
/// `out[b'] = Σ_{a < 2^k} weights[a] · table[a + 2^k · b']`.
pub fn bind_low_subspace(table: &[K], weights: &[K]) -> Vec<K> {
    let dom = weights.len();
    assert!(
        dom.is_power_of_two() && table.len().is_multiple_of(dom),
        "bind_low_subspace: table length must be a multiple of weights.len()"
    );
    let out_len = table.len() / dom;
    let eval_chunk = |chunk: &[K]| -> K {
        let mut acc = om_field::U256::ZERO;
        for (&w, &v) in weights.iter().zip(chunk) {
            acc += w.clmul(v);
        }
        acc.reduce()
    };
    if table.len() >= PAR_THRESHOLD && out_len >= 64 {
        table.par_chunks(dom).map(eval_chunk).collect()
    } else {
        table.chunks(dom).map(eval_chunk).collect()
    }
}

/// Prove a sum-check with a `k`-variable univariate skip on round 0 (spec 03 §3.9).
///
/// Replaces the first `k` variables (`1 <= k <= m`) with a single univariate round
/// of degree `d_s = degree * (2^k - 1)` over `D = {t_0, …, t_{2^k - 1}}`, followed
/// by `m - k` ordinary sum-check rounds.
///
/// Returns `(proof, point [r_0, r_1, …, r_{m-k}], [T̂(r_0, r') for T in tables])`.
///
/// # Panics
/// Panics if `degree < 1`, `k < 1`, `k > m`, tables do not share a power-of-two
/// length, or the claim is inconsistent with the tables.
pub fn sumcheck_prove_skip(
    claim: K,
    tables: Vec<Vec<K>>,
    combine: &(dyn Fn(&[K]) -> K + Sync),
    degree: usize,
    k: usize,
    transcript: &mut Transcript,
    label: &[u8],
) -> (UnivariateSkipProof, Vec<K>, Vec<K>) {
    assert!(degree >= 1, "degree must be >= 1");
    assert!(!tables.is_empty(), "sumcheck_prove_skip: no tables");
    let size = tables[0].len();
    assert!(
        size != 0 && size.is_power_of_two() && tables.iter().all(|t| t.len() == size),
        "tables must share a power-of-two length"
    );
    let m = size.trailing_zeros() as usize;
    assert!(
        k >= 1 && k <= m,
        "skip parameter k must satisfy 1 <= k <= m"
    );

    sumcheck_init(transcript, label, claim, m, degree);
    let dom = 1usize << k;
    let ds = degree * (dom - 1);
    let blocks = size / dom;
    let n_tabs = tables.len();

    // Evaluate s(t_j) for j = 0..=ds.
    // For j < dom, T̂(t_j, b') = T[j + dom * b'] directly.
    // For j >= dom, T̂(t_j, b') = Σ_{a < dom} L_a(t_j) * T[a + dom * b'].
    let mut s_evals = vec![K::ZERO; ds + 1];
    for (j, slot) in s_evals.iter_mut().enumerate() {
        if j < dom {
            let mut acc = K::ZERO;
            let mut vals = vec![K::ZERO; n_tabs];
            for b in 0..blocks {
                let idx = j + dom * b;
                for (ti, tab) in tables.iter().enumerate() {
                    vals[ti] = tab[idx];
                }
                acc += combine(&vals);
            }
            *slot = acc;
        } else {
            let w = lagrange_subspace_weights(k, K::t(j as u128));
            let bound: Vec<Vec<K>> = tables.iter().map(|t| bind_low_subspace(t, &w)).collect();
            *slot = combine_sum(&bound, combine);
        }
    }

    let sub_sum = s_evals[..dom].iter().fold(K::ZERO, |acc, &x| acc + x);
    assert_eq!(
        sub_sum, claim,
        "claim inconsistent with tables on skipped subspace"
    );

    // Send s(t_j) for j = 0..=ds, omitting j = dom - 1.
    let mut skip_msg = Vec::with_capacity(ds);
    for (j, &v) in s_evals.iter().enumerate() {
        if j != dom - 1 {
            skip_msg.push(v);
        }
    }
    transcript.absorb_ks(&sublabel(label, b"/skip/msg"), &skip_msg);
    let r0 = transcript.challenge_k(&sublabel(label, b"/skip/chal"));

    let mut cur = interpolate_eval(&s_evals, r0);
    let w_r0 = lagrange_subspace_weights(k, r0);
    let mut bound_tables: Vec<Vec<K>> =
        tables.iter().map(|t| bind_low_subspace(t, &w_r0)).collect();

    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    let rem = m - k;
    let mut msgs = Vec::with_capacity(rem);
    let mut rs = Vec::with_capacity(1 + rem);
    rs.push(r0);

    for _ in 0..rem {
        let ev = sumcheck_round_evals(&bound_tables, combine, degree);
        assert_eq!(
            ev[0] + ev[1],
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let mut msg = Vec::with_capacity(degree);
        msg.push(ev[0]);
        msg.extend_from_slice(&ev[2..]);
        transcript.absorb_ks(&msg_label, &msg);
        let r = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(r);
        cur = interpolate_eval(&ev, r);
        for t in &mut bound_tables {
            bind_low_in_place(t, r);
        }
    }

    let final_evals = bound_tables.iter().map(|t| t[0]).collect();
    (
        UnivariateSkipProof {
            skip_msg,
            round_msgs: msgs,
        },
        rs,
        final_evals,
    )
}

/// Verify a univariate-skip sum-check proof (spec 03 §3.9), returning
/// `(point [r_0, r_1, …, r_{m-k}], expected final value)`.
///
/// # Errors
/// Returns [`VerificationError`] if `k < 1`, `k > num_vars`, `skip_msg` does
/// not have `degree * (2^k - 1)` elements, or `round_msgs` does not have
/// `num_vars - k` messages of length `degree`.
pub fn sumcheck_verify_skip(
    claim: K,
    num_vars: usize,
    degree: usize,
    k: usize,
    proof: &UnivariateSkipProof,
    transcript: &mut Transcript,
    label: &[u8],
) -> Result<(Vec<K>, K), VerificationError> {
    assert!(degree >= 1, "degree must be >= 1");
    if k < 1 || k > num_vars || k > 16 {
        return Err(VerificationError::new("invalid skip parameter k"));
    }
    let dom = 1usize << k;
    let ds = degree * (dom - 1);
    let rem = num_vars - k;
    if proof.skip_msg.len() != ds {
        return Err(VerificationError::new("malformed skip round message"));
    }
    if proof.round_msgs.len() != rem {
        return Err(VerificationError::new("wrong number of rounds"));
    }

    sumcheck_init(transcript, label, claim, num_vars, degree);
    transcript.absorb_ks(&sublabel(label, b"/skip/msg"), &proof.skip_msg);
    let r0 = transcript.challenge_k(&sublabel(label, b"/skip/chal"));

    // Reconstruct s(t_0)..s(t_{ds}) with s(t_{dom - 1}) = claim + Σ_{a < dom - 1} s(t_a).
    let mut derived = claim;
    for &v in &proof.skip_msg[..dom - 1] {
        derived += v;
    }
    let mut s_evals = Vec::with_capacity(ds + 1);
    s_evals.extend_from_slice(&proof.skip_msg[..dom - 1]);
    s_evals.push(derived);
    s_evals.extend_from_slice(&proof.skip_msg[dom - 1..]);

    let mut cur = interpolate_eval(&s_evals, r0);
    let mut rs = Vec::with_capacity(1 + rem);
    rs.push(r0);

    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    for msg in &proof.round_msgs {
        if msg.len() != degree {
            return Err(VerificationError::new("malformed round message"));
        }
        transcript.absorb_ks(&msg_label, msg);
        let r = transcript.challenge_k(&chal_label);
        let mut ys = Vec::with_capacity(degree + 1);
        ys.push(msg[0]);
        ys.push(cur + msg[0]);
        ys.extend_from_slice(&msg[1..]);
        cur = interpolate_eval(&ys, r);
        rs.push(r);
    }
    Ok((rs, cur))
}
