//! Ligerito over K (spec 04 §4.4, §4.4a, §4.6, §4.7).
//! Mirrors `reference/openmagnetar/ligerito.py` byte for byte in its
//! transcript interaction, including the `gs > 1` composition of §4.4a.

use om_field::K;
use om_sumcheck::{SumcheckProof, VerificationError, eq_table, sumcheck_prove, sumcheck_verify};
use om_transcript::{Hasher, Transcript, u64le};
use rayon::prelude::*;

/// Tables at least this large use rayon (exact elementwise maps / XOR sums).
const PAR_THRESHOLD: usize = 1 << 14;

use crate::merkle::{Digest, MerkleTree, verify_multi};
use crate::ntt;

// ---------------------------------------------------------------- parameters

/// Ligerito parameter set `(n, ks, rs, ts, gs)` (§4.4, §4.6).
/// An empty `gs` means all repetitions are 1, as in Python.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LigeritoParams {
    /// Variables of the committed polynomial.
    pub n: usize,
    /// Fold arity per committed level.
    pub ks: Vec<usize>,
    /// `log2(1/rate)` per committed level.
    pub rs: Vec<usize>,
    /// Queries per committed level.
    pub ts: Vec<usize>,
    /// Gap-amplification repetitions per level; empty means all 1.
    pub gs: Vec<usize>,
}

impl LigeritoParams {
    /// Parameters with `gs` all 1.
    ///
    /// # Panics
    /// Panics where Python raises `ValueError` (see [`LigeritoParams::with_gs`]).
    pub fn new(n: usize, ks: Vec<usize>, rs: Vec<usize>, ts: Vec<usize>) -> Self {
        Self::with_gs(n, ks, rs, ts, Vec::new())
    }

    /// Parameters with explicit gap-amplification repetitions (§4.4a).
    ///
    /// # Panics
    /// Panics if `ks`/`rs`/`ts` lengths differ or are zero, any `k/r/t < 1`,
    /// `gs` mismatches or has an entry `< 1`, or `Σ ks ≥ n`.
    pub fn with_gs(
        n: usize,
        ks: Vec<usize>,
        rs: Vec<usize>,
        ts: Vec<usize>,
        gs: Vec<usize>,
    ) -> Self {
        assert!(
            ks.len() == rs.len() && rs.len() == ts.len() && !ks.is_empty(),
            "ks, rs, ts must have equal non-zero length"
        );
        assert!(
            ks.iter().all(|&k| k >= 1) && rs.iter().all(|&r| r >= 1) && ts.iter().all(|&t| t >= 1),
            "k, r, t must be >= 1"
        );
        assert!(
            gs.is_empty() || (gs.len() == ks.len() && gs.iter().all(|&g| g >= 1)),
            "gs must match ks and be >= 1"
        );
        assert!(
            ks.iter().sum::<usize>() < n,
            "folds must leave at least one variable (final polynomial)"
        );
        LigeritoParams { n, ks, rs, ts, gs }
    }

    /// Repetitions at level `i` (Python `reps`).
    pub fn reps(&self, i: usize) -> usize {
        if self.gs.is_empty() { 1 } else { self.gs[i] }
    }

    /// Extra variables of the level-`(i+1)` polynomial: `ceil(log2 gs_i)`.
    pub fn sbits(&self, i: usize) -> usize {
        (usize::BITS - (self.reps(i) - 1).leading_zeros()) as usize
    }

    /// Number of committed levels `L`.
    pub fn levels(&self) -> usize {
        self.ks.len()
    }

    /// Variables of the level-`i` polynomial (`n_0 = n`; `i = L`: final).
    pub fn n_i(&self, i: usize) -> usize {
        self.n - self.ks[..i].iter().sum::<usize>() + (0..i).map(|j| self.sbits(j)).sum::<usize>()
    }

    /// Variables of one folded row `g^(j)` of level `i`.
    pub fn m_i(&self, i: usize) -> usize {
        self.n_i(i) - self.ks[i]
    }

    /// Variables of the final polynomial `n_L`.
    pub fn n_final(&self) -> usize {
        self.n_i(self.levels())
    }

    /// `log2 N_i`, the codeword length exponent of level `i`.
    pub fn log_codeword(&self, i: usize) -> usize {
        self.m_i(i) + self.rs[i]
    }

    /// Canonical `enc_params` byte layout (§4.1): `u64le(n) ‖ u64le(L) ‖`
    /// per level `u64le(k) ‖ u64le(r) ‖ u64le(t)`, plus the `GAPREPS`
    /// suffix iff some `gs_i > 1`.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&u64le(self.n as u64));
        out.extend_from_slice(&u64le(self.levels() as u64));
        for i in 0..self.levels() {
            out.extend_from_slice(&u64le(self.ks[i] as u64));
            out.extend_from_slice(&u64le(self.rs[i] as u64));
            out.extend_from_slice(&u64le(self.ts[i] as u64));
        }
        if (0..self.levels()).any(|i| self.reps(i) > 1) {
            out.extend_from_slice(b"GAPREPS");
            for i in 0..self.levels() {
                out.extend_from_slice(&u64le(self.reps(i) as u64));
            }
        }
        out
    }

    /// Alias for [`LigeritoParams::encode`] (the §4.1 name).
    pub fn enc_params(&self) -> Vec<u8> {
        self.encode()
    }
}

/// `t = ceil(bits / -log2((1+ρ)/2))`, `ρ = 2^-r` (unique-decoding radius).
pub fn queries_provable(r: usize, bits: u32) -> usize {
    let rho = 2f64.powi(-(r as i32));
    (f64::from(bits) / -((1.0 + rho) / 2.0).log2()).ceil() as usize
}

/// `t = ceil(bits / r)` (conjectured profile, §4.7).
pub fn queries_conjectured(r: usize, bits: u32) -> usize {
    (bits as usize).div_ceil(r)
}

/// Fold arities with the §4.6 defaults (`final = 6`, `max_k = 5`).
pub fn schedule(n: usize) -> Vec<usize> {
    schedule_with(n, 6, 5)
}

/// Split `n - final` over `ceil((n-final)/max_k)` levels, larger first.
///
/// # Panics
/// Panics if `n ≤ final` (Python raises `ValueError`).
pub fn schedule_with(n: usize, final_vars: usize, max_k: usize) -> Vec<usize> {
    assert!(n > final_vars, "n too small");
    let total = n - final_vars;
    let levels = total.div_ceil(max_k);
    let (base, extra) = (total / levels, total % levels);
    (0..levels)
        .map(|i| if i < extra { base + 1 } else { base })
        .collect()
}

/// Bits of the conservative proximity-gap term `k·N/|K|` for one fold.
pub fn gap_bits_single(k: usize, log_n_cw: usize) -> f64 {
    128.0 - ((k << log_n_cw) as f64).log2()
}

/// Smallest `m` with `(kN/|K|)^m ≤ 2^-120` (gap amplification, §4.7).
pub fn gap_reps(k: usize, log_n_cw: usize) -> usize {
    gap_reps_bits(k, log_n_cw, 120)
}

/// [`gap_reps`] with an explicit bit target (Python `gap_reps(..., bits)`).
pub fn gap_reps_bits(k: usize, log_n_cw: usize, bits: u32) -> usize {
    ((f64::from(bits) / gap_bits_single(k, log_n_cw)).ceil() as usize).max(1)
}

/// Build parameters for a profile: `"provable-120"` (t from
/// [`queries_provable`], `gs` from [`gap_reps`]) or `"conjectured-100"`
/// (t from [`queries_conjectured`], `gs` all 1), mirroring Python
/// `make_params(n, profile, r)`.
///
/// # Panics
/// Panics on an unknown profile (Python raises `ValueError`).
pub fn make_params(n: usize, profile: &str, r: usize) -> LigeritoParams {
    let ks = schedule(n);
    let levels = ks.len();
    match profile {
        "provable-120" => {
            let t = queries_provable(r, 120);
            let base = LigeritoParams::new(n, ks.clone(), vec![r; levels], vec![t; levels]);
            let gs: Vec<usize> = ks
                .iter()
                .enumerate()
                .map(|(i, &k)| gap_reps(k, base.log_codeword(i)))
                .collect();
            let gs = if gs.iter().any(|&g| g > 1) {
                gs
            } else {
                Vec::new()
            };
            LigeritoParams::with_gs(n, ks, vec![r; levels], vec![t; levels], gs)
        }
        "conjectured-100" => {
            let t = queries_conjectured(r, 100);
            LigeritoParams::new(n, ks, vec![r; levels], vec![t; levels])
        }
        _ => panic!("unknown profile"),
    }
}

/// Per-level soundness terms in bits (`log2(1/error)`), Python
/// `soundness_bits` dict for one level.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SoundnessBits {
    /// Level index.
    pub level: usize,
    /// Sum-check term.
    pub sumcheck: f64,
    /// β-batching term.
    pub batch: f64,
    /// Proximity-gap term (includes the repetition factor).
    pub gap: f64,
    /// Query term.
    pub query: f64,
}

/// Per-level error terms under the formulas of §4.7. The query term uses the
/// provable formula unless `profile != "provable-120"`, as in Python.
pub fn soundness_bits(p: &LigeritoParams, profile: &str) -> Vec<SoundnessBits> {
    (0..p.levels())
        .map(|i| {
            let rho = 2f64.powi(-(p.rs[i] as i32));
            let delta = (1.0 - rho) / 2.0;
            let n_cw = 1usize << p.log_codeword(i);
            let (k, t) = (p.ks[i], p.ts[i]);
            SoundnessBits {
                level: i,
                sumcheck: 127.0 - (k as f64).log2(),
                batch: 128.0 - (t as f64).log2(),
                gap: p.reps(i) as f64 * (128.0 - ((k * n_cw) as f64).log2()),
                query: if profile == "provable-120" {
                    t as f64 * -(1.0 - delta).log2()
                } else {
                    (t * p.rs[i]) as f64
                },
            }
        })
        .collect()
}

// ----------------------------------------------------------------- structures

/// Commitment data of one level (prover state).
#[derive(Clone, Debug)]
pub struct LevelData {
    /// The level polynomial table.
    pub f: Vec<K>,
    /// Fold arity of this level.
    pub k: usize,
    /// `log2(1/rate)` of this level.
    pub r: usize,
    /// Encoded rows: `cw[row][q]`.
    pub cw: Vec<Vec<K>>,
    /// Merkle tree over the columns.
    pub tree: MerkleTree,
}

impl LevelData {
    /// Column `q`: all rows at codeword position `q`, in row order.
    pub fn column(&self, q: usize) -> Vec<K> {
        self.cw.iter().map(|row| row[q]).collect()
    }
}

/// One level's opening: opened columns and the Merkle multi-path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LevelOpening {
    /// One column per (sorted, deduplicated) query index.
    pub columns: Vec<Vec<K>>,
    /// Authentication hashes (§4.2).
    pub auth: Vec<Digest>,
}

/// A Ligerito opening proof (§4.1). The field `final_poly` is Python's
/// `final` (a keyword-adjacent name in Rust style).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LigeritoProof {
    /// Roots of committed levels `1..L-1`.
    pub roots: Vec<Digest>,
    /// One sum-check proof per level (`k_i` rounds).
    pub sumchecks: Vec<SumcheckProof>,
    /// One level opening per level.
    pub openings: Vec<LevelOpening>,
    /// The final polynomial `f_L`, `2^n_final` elements in the clear.
    pub final_poly: Vec<K>,
}

impl LigeritoProof {
    /// Canonical reference byte layout (§4.8): roots, per level the
    /// sum-check messages, per level the columns then `auth`, then the
    /// final polynomial; K elements in C1 encoding.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for root in &self.roots {
            out.extend_from_slice(root);
        }
        for sc in &self.sumchecks {
            for msg in &sc.round_msgs {
                for x in msg {
                    out.extend_from_slice(&x.to_bytes());
                }
            }
        }
        for op in &self.openings {
            for col in &op.columns {
                out.extend_from_slice(&column_bytes(col));
            }
            for a in &op.auth {
                out.extend_from_slice(a);
            }
        }
        for x in &self.final_poly {
            out.extend_from_slice(&x.to_bytes());
        }
        out
    }
}

/// Serialize a column as concatenated 16-byte C1 encodings (§4.2).
pub fn column_bytes(col: &[K]) -> Vec<u8> {
    let mut out = Vec::with_capacity(16 * col.len());
    for x in col {
        out.extend_from_slice(&x.to_bytes());
    }
    out
}

/// Encode the rows of `f` and commit to the columns (§4.4).
pub fn commit_level(h: Hasher, f: Vec<K>, k: usize, r: usize) -> LevelData {
    let rows = 1 << k;
    let cols = f.len() / rows;
    let encode_row =
        |i: usize| ntt::encode(&(0..cols).map(|j| f[i + rows * j]).collect::<Vec<_>>(), r);
    let cw: Vec<Vec<K>> = if f.len() >= PAR_THRESHOLD && rows > 1 {
        (0..rows).into_par_iter().map(encode_row).collect()
    } else {
        (0..rows).map(encode_row).collect()
    };
    let n_cw = cw[0].len();
    let leaf = |q: usize| column_bytes(&(0..rows).map(|i| cw[i][q]).collect::<Vec<_>>());
    let leaves: Vec<Vec<u8>> = if n_cw * rows >= PAR_THRESHOLD {
        (0..n_cw).into_par_iter().map(leaf).collect()
    } else {
        (0..n_cw).map(leaf).collect()
    };
    let tree = MerkleTree::new(h, &leaves);
    LevelData { f, k, r, cw, tree }
}

/// Commit to `table` (level 0), returning `(root, state)`.
///
/// # Panics
/// Panics if `table.len() != 2^n` (Python raises `ValueError`).
pub fn commit(p: &LigeritoParams, h: Hasher, table: &[K]) -> (Digest, LevelData) {
    assert_eq!(table.len(), 1 << p.n, "table must have 2^n entries");
    let ld = commit_level(h, table.to_vec(), p.ks[0], p.rs[0]);
    let root = ld.tree.root();
    (root, ld)
}

/// Setup absorption (§4.1): `pcs/params` then `pcs/root`.
pub fn absorb_setup(p: &LigeritoParams, root: &[u8], tr: &mut Transcript) {
    tr.absorb_bytes(b"pcs/params", &p.encode());
    tr.absorb_bytes(b"pcs/root", root);
}

/// A product-form weight term `(α, γ-vector, d-vector)` (§4.4):
/// `α · Π_u (γ_u + d_u x_u)`.
pub type Term = (K, Vec<K>, Vec<K>);

/// The hypercube table of a product-form term, LSB-first (C2).
pub fn term_table(term: &Term) -> Vec<K> {
    let (alpha, cs, ds) = term;
    let mut t = vec![*alpha];
    for (&c, &d) in cs.iter().zip(ds) {
        let lo: Vec<K> = t.iter().map(|&e| e * c).collect();
        let hi: Vec<K> = t.iter().map(|&e| e * (c + d)).collect();
        t = lo.into_iter().chain(hi).collect();
    }
    t
}

/// Draw `t` query indices and return the sorted, deduplicated set (§4.4).
pub fn sample_indices(tr: &mut Transcript, bits: usize, t: usize) -> Vec<usize> {
    let mut set: Vec<usize> = (0..t)
        .map(|_| tr.challenge_index(b"pcs/query/idx", bits as u32) as usize)
        .collect();
    set.sort_unstable();
    set.dedup();
    set
}

/// `g[y] = Σ_a eq(ρ, a) f[a + 2^k y]` (bind the low `k` variables).
pub fn fold_table(f: &[K], k: usize, rho: &[K]) -> Vec<K> {
    let rows = 1 << k;
    let er = eq_table(rho);
    let fold = |chunk: &[K]| {
        er.iter()
            .zip(chunk)
            .fold(K::ZERO, |acc, (&e, &x)| acc + e * x)
    };
    if f.len() >= PAR_THRESHOLD {
        f.par_chunks(rows).map(fold).collect()
    } else {
        f.chunks(rows).map(fold).collect()
    }
}

/// Product-form `(γ, d)` of `eq(bits(j), ·)` over `s` extra variables (§4.4a).
pub fn selector(j: usize, s: usize) -> (Vec<K>, Vec<K>) {
    (
        (0..s)
            .map(|u| K::ONE + K::from_u128(((j >> u) & 1) as u128))
            .collect(),
        vec![K::ONE; s],
    )
}

type CommitFn<'a> = &'a dyn Fn(Hasher, Vec<K>, usize, usize) -> LevelData;

/// Prover (Python `open_`). The transcript must already contain setup
/// ([`absorb_setup`]); absorbs `pcs/point` and `pcs/value` first.
///
/// # Panics
/// Panics if the point has the wrong length (Python raises `ValueError`).
pub fn open_(
    p: &LigeritoParams,
    h: Hasher,
    ld0: &LevelData,
    r: &[K],
    y: K,
    tr: &mut Transcript,
) -> LigeritoProof {
    open_inner(p, h, ld0, r, y, tr, &commit_level)
}

#[allow(clippy::too_many_arguments, clippy::needless_range_loop)]
fn open_inner(
    p: &LigeritoParams,
    h: Hasher,
    ld0: &LevelData,
    r: &[K],
    y: K,
    tr: &mut Transcript,
    commit_fn: CommitFn<'_>,
) -> LigeritoProof {
    assert_eq!(r.len(), p.n, "point has wrong length");
    tr.absorb_ks(b"pcs/point", r);
    tr.absorb_k(b"pcs/value", y);
    let mut f = ld0.f.clone();
    let mut b = eq_table(r);
    let mut c = y;
    let mut ld = ld0.clone();
    let (mut roots, mut scs, mut ops) = (Vec::new(), Vec::new(), Vec::new());
    let mut final_poly = Vec::new();
    for i in 0..p.levels() {
        let (k, reps, s, m) = (p.ks[i], p.reps(i), p.sbits(i), p.m_i(i));
        let (rows, cols) = (1 << k, f.len() >> k);
        let tabs: Vec<Vec<K>> = if f.len() >= PAR_THRESHOLD {
            // `collect` of an indexed parallel iterator preserves order, so
            // the `f` tables precede the `b` tables exactly as sequentially.
            let mut tabs: Vec<Vec<K>> = (0..cols)
                .into_par_iter()
                .map(|y_| f[y_ * rows..(y_ + 1) * rows].to_vec())
                .collect();
            let b_tabs: Vec<Vec<K>> = (0..cols)
                .into_par_iter()
                .map(|y_| b[y_ * rows..(y_ + 1) * rows].to_vec())
                .collect();
            tabs.extend(b_tabs);
            tabs
        } else {
            let mut tabs: Vec<Vec<K>> = (0..cols)
                .map(|y_| f[y_ * rows..(y_ + 1) * rows].to_vec())
                .collect();
            tabs.extend((0..cols).map(|y_| b[y_ * rows..(y_ + 1) * rows].to_vec()));
            tabs
        };
        let combine = |v: &[K]| (0..cols).fold(K::ZERO, |acc, a| acc + v[a] * v[cols + a]);
        let (proof, rho, fin) = sumcheck_prove(c, tabs, &combine, 2, tr, b"pcs/sumcheck");
        scs.push(proof);
        let (g, bp) = (&fin[..cols], &fin[cols..]);
        let cp = g.iter().zip(bp).fold(K::ZERO, |acc, (&x, &z)| acc + x * z);
        let mut rhos = vec![rho];
        for _ in 1..reps {
            rhos.push(tr.challenge_ks(b"pcs/fold", k));
        }
        let mut f_next = g.to_vec();
        for rj in &rhos[1..] {
            f_next.extend(fold_table(&f, k, rj));
        }
        f_next.resize(1 << (m + s), K::ZERO);
        let last = i == p.levels() - 1;
        let nxt = if last {
            tr.absorb_ks(b"pcs/final", &f_next);
            None
        } else {
            let nxt = commit_fn(h, f_next.clone(), p.ks[i + 1], p.rs[i + 1]);
            roots.push(nxt.tree.root());
            tr.absorb_bytes(b"pcs/root", &nxt.tree.root());
            Some(nxt)
        };
        let idx = sample_indices(tr, p.log_codeword(i), p.ts[i]);
        let cols_data: Vec<Vec<K>> = idx.iter().map(|&q| ld.column(q)).collect();
        ops.push(LevelOpening {
            columns: cols_data.clone(),
            auth: ld.tree.open(&idx).expect("sampled indices are valid"),
        });
        let flat: Vec<K> = cols_data.iter().flatten().copied().collect();
        tr.absorb_ks(b"pcs/cols", &flat);
        if last {
            final_poly = f_next;
            break;
        }
        let betas: Vec<K> = (0..reps).map(|_| tr.challenge_k(b"pcs/beta")).collect();
        let ers: Vec<Vec<K>> = rhos.iter().map(|rj| eq_table(rj)).collect();
        c = cp;
        let mut b_next = bp.to_vec();
        b_next.resize(1 << (m + s), K::ZERO);
        let off = 1 << m;
        for j in 0..reps {
            let mut pw = K::ONE;
            for (q_idx, (q, col)) in idx.iter().zip(&cols_data).enumerate() {
                let _ = q_idx;
                pw *= betas[j];
                let vq = ers[j]
                    .iter()
                    .zip(col)
                    .fold(K::ZERO, |acc, (&e, &x)| acc + e * x);
                c += pw * vq;
                let row = ntt::basis_row(*q, m, p.log_codeword(i));
                for u in 0..off {
                    b_next[j * off + u] += pw * row[u];
                }
            }
        }
        b = b_next;
        f = f_next;
        ld = nxt.expect("non-final level commits the next level");
    }
    LigeritoProof {
        roots,
        sumchecks: scs,
        openings: ops,
        final_poly,
    }
}

/// Verifier (Python `verify`). The transcript must already contain setup;
/// absorbs `pcs/point` and `pcs/value` first.
///
/// # Errors
/// Returns [`VerificationError`] on any failed check (§4.4, §4.4a).
#[allow(clippy::too_many_arguments, clippy::needless_range_loop)]
pub fn verify(
    p: &LigeritoParams,
    h: Hasher,
    root: &[u8],
    r: &[K],
    y: K,
    proof: &LigeritoProof,
    tr: &mut Transcript,
) -> Result<(), VerificationError> {
    if r.len() != p.n {
        return Err(VerificationError::new("point has wrong length"));
    }
    if proof.roots.len() != p.levels() - 1
        || proof.sumchecks.len() != p.levels()
        || proof.openings.len() != p.levels()
        || proof.final_poly.len() != 1 << p.n_final()
    {
        return Err(VerificationError::new("malformed proof"));
    }
    tr.absorb_ks(b"pcs/point", r);
    tr.absorb_k(b"pcs/value", y);
    let mut terms: Vec<Term> = vec![(
        K::ONE,
        r.iter().map(|&x| K::ONE + x).collect(),
        vec![K::ONE; p.n],
    )];
    let mut c = y;
    let mut cur_root: Digest = root.to_vec();
    for i in 0..p.levels() {
        let (k, reps, s, m) = (p.ks[i], p.reps(i), p.sbits(i), p.m_i(i));
        let (rho, cp) = sumcheck_verify(c, k, 2, &proof.sumchecks[i], tr, b"pcs/sumcheck")?;
        let (zc, zd) = selector(0, s);
        terms = terms
            .into_iter()
            .map(|(a, cs, ds)| {
                let factor = prod(&cs[..k], &ds[..k], &rho);
                let mut ncs = cs[k..].to_vec();
                ncs.extend_from_slice(&zc);
                let mut nds = ds[k..].to_vec();
                nds.extend_from_slice(&zd);
                (a * factor, ncs, nds)
            })
            .collect();
        let mut rhos = vec![rho];
        for _ in 1..reps {
            rhos.push(tr.challenge_ks(b"pcs/fold", k));
        }
        let last = i == p.levels() - 1;
        if last {
            tr.absorb_ks(b"pcs/final", &proof.final_poly);
        } else {
            tr.absorb_bytes(b"pcs/root", &proof.roots[i]);
        }
        let lb = p.log_codeword(i);
        let idx = sample_indices(tr, lb, p.ts[i]);
        let op = &proof.openings[i];
        if op.columns.len() != idx.len() || op.columns.iter().any(|col| col.len() != 1 << k) {
            return Err(VerificationError::new("malformed opening"));
        }
        let col_bytes: Vec<Vec<u8>> = op.columns.iter().map(|col| column_bytes(col)).collect();
        verify_multi(h, &cur_root, 1 << lb, &idx, &col_bytes, &op.auth)?;
        let flat: Vec<K> = op.columns.iter().flatten().copied().collect();
        tr.absorb_ks(b"pcs/cols", &flat);
        let ers: Vec<Vec<K>> = rhos.iter().map(|rj| eq_table(rj)).collect();
        let vs: Vec<Vec<K>> = ers
            .iter()
            .map(|er| {
                op.columns
                    .iter()
                    .map(|col| {
                        er.iter()
                            .zip(col)
                            .fold(K::ZERO, |acc, (&e, &x)| acc + e * x)
                    })
                    .collect()
            })
            .collect();
        if last {
            let f_final = &proof.final_poly;
            for j in 0..reps {
                let g = &f_final[j << m..(j + 1) << m];
                for (q, &vq) in idx.iter().zip(&vs[j]) {
                    let row = ntt::basis_row(*q, m, lb);
                    let got = g
                        .iter()
                        .zip(&row)
                        .fold(K::ZERO, |acc, (&a, &z)| acc + a * z);
                    if got != vq {
                        return Err(VerificationError::new(
                            "final polynomial inconsistent with opened column",
                        ));
                    }
                }
            }
            let tabs: Vec<Vec<K>> = terms.iter().map(term_table).collect();
            let mut tot = K::ZERO;
            for j in 0..f_final.len() {
                let bj = tabs.iter().fold(K::ZERO, |acc, tb| acc + tb[j]);
                tot += f_final[j] * bj;
            }
            if tot != cp {
                return Err(VerificationError::new("final inner-product claim fails"));
            }
            return Ok(());
        }
        let betas: Vec<K> = (0..reps).map(|_| tr.challenge_k(b"pcs/beta")).collect();
        c = cp;
        for j in 0..reps {
            let mut pw = K::ONE;
            let (jc, jd) = selector(j, s);
            for (q, &vq) in idx.iter().zip(&vs[j]) {
                pw *= betas[j];
                c += pw * vq;
                let a = ntt::gen_weights(*q, m, lb);
                let mut cs = vec![K::ONE; m];
                cs.extend_from_slice(&jc);
                let mut ds: Vec<K> = a.iter().map(|&x| K::ONE + x).collect();
                ds.extend_from_slice(&jd);
                terms.push((pw, cs, ds));
            }
        }
        cur_root = proof.roots[i].clone();
    }
    Ok(())
}

fn prod(cs: &[K], ds: &[K], rho: &[K]) -> K {
    cs.iter()
        .zip(ds)
        .zip(rho)
        .fold(K::ONE, |acc, ((&c, &d), &x)| acc * (c + d * x))
}

#[cfg(test)]
mod tests {
    //! Ports of the Python cheating-prover tests, which monkeypatch
    //! `commit_level`; here they use the `open_inner` commit hook.
    use super::*;
    use om_sumcheck::mle_eval;

    struct Rng(u64);
    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }
        fn k(&mut self) -> K {
            K::from_u128(u128::from(self.next_u64()) | (u128::from(self.next_u64()) << 64))
        }
        fn ks(&mut self, n: usize) -> Vec<K> {
            (0..n).map(|_| self.k()).collect()
        }
    }

    fn verify_fresh(p: &LigeritoParams, root: &[u8], r: &[K], y: K, pf: &LigeritoProof) -> bool {
        let mut tv = Transcript::new_default(b"t");
        absorb_setup(p, root, &mut tv);
        verify(p, Hasher::Sha256, root, r, y, pf, &mut tv).is_err()
    }

    #[test]
    fn cheating_prover_inconsistent_fold() {
        // test_ligerito.py::test_cheating_prover_inconsistent_fold
        let p = LigeritoParams::new(10, vec![3, 3], vec![1, 2], vec![40, 5]);
        let mut rng = Rng(5);
        let tab = rng.ks(1 << p.n);
        let mut tr = Transcript::new_default(b"t");
        let (root, ld) = commit(&p, Hasher::Sha256, &tab);
        absorb_setup(&p, &root, &mut tr);
        let r = rng.ks(p.n);
        let y = mle_eval(&tab, &r);
        let target = 1 << (p.n - p.ks[0]);
        let evil = |h: Hasher, mut f: Vec<K>, k: usize, rr: usize| {
            if f.len() == target {
                f[3] += K::ONE;
            }
            commit_level(h, f, k, rr)
        };
        let pf = open_inner(&p, Hasher::Sha256, &ld, &r, y, &mut tr, &evil);
        assert!(
            verify_fresh(&p, &root, &r, y, &pf),
            "non-fold must be caught"
        );
    }

    #[test]
    fn cheating_in_each_repetition() {
        // test_ligerito.py::TestGapAmplification::test_cheating_in_each_repetition
        let p = LigeritoParams::with_gs(10, vec![3, 3], vec![1, 2], vec![30, 30], vec![3, 3]);
        let m = p.m_i(0);
        for rep in 0..3 {
            let mut rng = Rng(9);
            let tab = rng.ks(1 << p.n);
            let mut tr = Transcript::new_default(b"t");
            let (root, ld) = commit(&p, Hasher::Sha256, &tab);
            absorb_setup(&p, &root, &mut tr);
            let r = rng.ks(p.n);
            let y = mle_eval(&tab, &r);
            let target = 1 << p.n_i(1);
            let evil = |h: Hasher, mut f: Vec<K>, k: usize, rr: usize| {
                if f.len() == target {
                    f[(rep << m) + 1] += K::ONE;
                }
                commit_level(h, f, k, rr)
            };
            let pf = open_inner(&p, Hasher::Sha256, &ld, &r, y, &mut tr, &evil);
            assert!(
                verify_fresh(&p, &root, &r, y, &pf),
                "rep {rep} must be caught"
            );
        }
    }
}
