//! Sum-check per docs/spec/03-sumcheck.md and CONVENTIONS C3.
//! Mirrors `reference/openmagnetar/sumcheck.py` byte for byte in its
//! transcript interaction.

use core::fmt;

use om_field::K;
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
    let half = tables[0].len() / 2;
    let n = tables.len();
    if tables[0].len() >= PAR_THRESHOLD {
        let (ev, ..) = (0..half)
            .into_par_iter()
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
