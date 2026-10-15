//! The Spartan family (spec 06 §6.3–6.8). Mirrors
//! `reference/openmagnetar/spartan.py` byte for byte in its transcript
//! interaction.
//!
//! One code path covers Construction 1 / SIMD / BinarySpartan (`T = 1`
//! relation, no layout) and Construction 2, Virtual Spartan (`T = 2`
//! relations, segment layout, optional cross-step). Every transcript
//! label is `P ‖ "/" ‖ …` for the caller-supplied prefix `P` (`b"vsp"`
//! in the full protocol and in the reference tests, per spec 06 §6.3).
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - The witness `W` is `&[Vec<bool>]` and the public inputs `X` are
//!   `&[Vec<K>]`; Python's mixed `0`/`1`-int-or-`K` entries are
//!   converted by the caller ([`K::from_bit`]).
//! - Python `ValueError`s in [`prove`] (and from [`check_layout`],
//!   including inside [`verify`]) **panic**; `VerificationError` is
//!   returned as `Err` from [`verify`]. The prover-side `VerificationError`s
//!   of Python's cross-step setup likewise panic in [`prove`].
//! - The claim type is [`Claim`], re-exported from `om-mosaic`
//!   (Python's `spartan.py` imports `Claim` from `mosaic.py`); the
//!   whole-`W` claim of the no-layout mode keeps Python's sentinel
//!   `comp_id = -1`, hence `i64` ids.

use om_field::K;
use om_sumcheck::{
    SumcheckProof, VerificationError, bind_low, eq_eval, eq_table, interpolate_eval, mle_eval,
    mle_eval_bits, sumcheck_prove, sumcheck_verify,
};
use om_transcript::{Transcript, u64le};

use crate::r1cs::{R1CS, build_z, check_witness_bits, public_part, simd_satisfied};

/// An evaluation claim `p~_{comp_id}(point) = value` on a component
/// polynomial (Python `mosaic.Claim`, re-exported from `om-mosaic`;
/// `comp_id = -1` denotes the whole witness matrix `W` in the
/// no-layout mode).
pub use om_mosaic::Claim;

/// What a column segment is handed to (spec 06 §6.5; Python's
/// `"direct"` / `"virtual"` / `"pad"`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SegmentKind {
    Direct,
    Virtual,
    Pad,
}

impl SegmentKind {
    /// The Python / vector spelling of this kind.
    pub fn as_str(self) -> &'static str {
        match self {
            SegmentKind::Direct => "direct",
            SegmentKind::Virtual => "virtual",
            SegmentKind::Pad => "pad",
        }
    }

    /// Parse the Python / vector spelling, if it is one of the three.
    pub fn from_name(s: &str) -> Option<Self> {
        match s {
            "direct" => Some(SegmentKind::Direct),
            "virtual" => Some(SegmentKind::Virtual),
            "pad" => Some(SegmentKind::Pad),
            _ => None,
        }
    }
}

/// A column segment of `W`: columns
/// `[block * 2^log_cols, (block+1) * 2^log_cols)` (spec 06 §6.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Segment {
    pub seg_id: i64,
    pub kind: SegmentKind,
    pub log_cols: usize,
    pub block: usize,
}

/// The cross-step designation (spec 06 §6.6): whole segments `in_id`
/// and `out_id` of equal size `2^lam`, with public bit-vector boundary
/// states `init` and `fin` of length `2^lam`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossStep {
    pub in_id: i64,
    pub out_id: i64,
    pub init: Vec<bool>,
    pub fin: Vec<bool>,
}

/// A Spartan proof (field order as in spec 06 §6.7).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpartanProof {
    /// `[t][round] -> [g(t_0), g(t_2), g(t_3)]`, `rho + s` rounds each.
    pub outer_msgs: Vec<Vec<Vec<K>>>,
    /// `[t] -> [v_A, v_B, v_C]`.
    pub outer_finals: Vec<Vec<K>>,
    pub inner: SumcheckProof,
    pub v_w: K,
    /// One per non-pad segment, in layout order.
    pub seg_vals: Vec<K>,
    pub xs_proof: Option<SumcheckProof>,
    /// `[v_in, v_out]`.
    pub xs_vals: Option<Vec<K>>,
}

fn lbl(p: &[u8], parts: &[&[u8]]) -> Vec<u8> {
    let mut out = p.to_vec();
    for part in parts {
        out.push(b'/');
        out.extend_from_slice(part);
    }
    out
}

fn bits_of(v: usize, n: usize) -> Vec<K> {
    (0..n).map(|k| K::from_bit((v >> k) & 1 == 1)).collect()
}

/// Validate a segment layout (spec 06 §6.5): kind well-formed by
/// construction, ids distinct, each segment inside `[0, 2^(nu-1))`,
/// pairwise disjoint.
///
/// # Panics
/// Panics on an invalid layout (Python raises `ValueError`).
pub fn check_layout(segs: &[Segment], nu: usize) {
    assert!(nu >= 1, "nu must be at least 1");
    let cols = 1usize << (nu - 1);
    let mut used: Vec<(i64, usize, usize)> = Vec::new();
    for s in segs {
        assert!(
            used.iter().all(|&(id, _, _)| id != s.seg_id),
            "duplicate segment id"
        );
        assert!(s.log_cols < nu, "segment out of range");
        let (lo, hi) = (s.block << s.log_cols, (s.block + 1) << s.log_cols);
        assert!(hi <= cols, "segment out of range");
        for &(_, a, b) in &used {
            assert!(!(lo < b && a < hi), "segments overlap");
        }
        used.push((s.seg_id, lo, hi));
    }
}

/// The MLE of the `next` indicator `N(a, b) = [int(b) = int(a)+1 and
/// int(a) < 2^s - 1]`, LSB-first (C2), `s = a.len()`:
/// `N~ = sum_i [prod_{j<i} a_j (1+b_j)] (1+a_i) b_i [prod_{j>i} eq_j]`
/// (spec 06 §6.6). For `s = 0` this is `0`.
///
/// # Panics
/// Panics if `a.len() != b.len()` (Python raises `IndexError`).
pub fn next_mle(a: &[K], b: &[K]) -> K {
    assert_eq!(a.len(), b.len(), "next_mle: length mismatch");
    let s = a.len();
    let mut suffix = vec![K::ONE; s + 1];
    for j in (0..s).rev() {
        suffix[j] = suffix[j + 1] * (K::ONE + a[j] + b[j]);
    }
    let (mut acc, mut prefix) = (K::ZERO, K::ONE);
    for i in 0..s {
        acc += prefix * (K::ONE + a[i]) * b[i] * suffix[i + 1];
        prefix *= a[i] * (K::ONE + b[i]);
    }
    acc
}

/// The values at `r_u` of the MLEs of the public `u`-tables `a_out`,
/// `a_in` of the cross-step sum-check (spec 06 §6.6 step 4):
/// `(A_out, A_in)`.
pub fn xs_weights(tau_u: &[K], gamma: K, r_u: &[K]) -> (K, K) {
    let (mut prod_tau, mut prod_r, mut prod_nr) = (K::ONE, K::ONE, K::ONE);
    for (&t, &r) in tau_u.iter().zip(r_u) {
        prod_tau *= t;
        prod_r *= r;
        prod_nr *= K::ONE + r;
    }
    let a_out = eq_eval(tau_u, r_u) + prod_tau * prod_r + gamma * gamma * prod_r;
    let a_in = next_mle(tau_u, r_u) + gamma * prod_nr;
    (a_out, a_in)
}

/// The flat bit table of one segment over all instances:
/// index = local column + `2^log_cols` * instance (Python
/// `spartan._segment_table`, also used by `protocol.py`).
pub fn segment_table(w: &[Vec<bool>], sg: &Segment) -> Vec<bool> {
    let (off, n) = (sg.block << sg.log_cols, 1usize << sg.log_cols);
    w.iter()
        .flat_map(|row| (0..n).map(move |y| row[off + y]))
        .collect()
}

/// `g(t) = sum_i E(t)(A(t)B(t) + C(t))` at `t_0..t_3`, where
/// `T(t) = T[2i] + t (T[2i] + T[2i+1])`.
fn g_evals(e: &[K], a: &[K], b: &[K], c: &[K]) -> [K; 4] {
    let mut acc = [K::ZERO; 4];
    for i in 0..e.len() / 2 {
        for (k, slot) in acc.iter_mut().enumerate() {
            let t = K::t(k as u128);
            let at = |tab: &[K]| tab[2 * i] + t * (tab[2 * i] + tab[2 * i + 1]);
            *slot += at(e) * (at(a) * at(b) + at(c));
        }
    }
    acc
}

fn default_names(t: usize) -> Vec<Vec<u8>> {
    if t <= 2 {
        [b"bin".to_vec(), b"fld".to_vec()][..t].to_vec()
    } else {
        (0..t).map(|i| format!("r{i}").into_bytes()).collect()
    }
}

fn resolve_names(names: Option<&[Vec<u8>]>, t: usize) -> Vec<Vec<u8>> {
    match names {
        Some(n) if !n.is_empty() => n.to_vec(),
        _ => default_names(t),
    }
}

/// Steps 0–1: absorb the shape and the public inputs, squeeze `tau_t`
/// per relation.
#[allow(clippy::too_many_arguments)]
fn setup(
    transcript: &mut Transcript,
    p: &[u8],
    t: usize,
    rho: usize,
    nu: usize,
    s: usize,
    nx: usize,
    x: &[Vec<K>],
    names: &[Vec<u8>],
) -> Vec<Vec<K>> {
    let mut shape = Vec::with_capacity(40);
    for v in [t, rho, nu, s, nx] {
        shape.extend_from_slice(&u64le(v as u64));
    }
    transcript.absorb_bytes(&lbl(p, &[b"shape"]), &shape);
    let flat: Vec<K> = x.iter().flat_map(|row| row.iter().copied()).collect();
    transcript.absorb_ks(&lbl(p, &[b"pub"]), &flat);
    names
        .iter()
        .map(|nm| transcript.challenge_ks(&lbl(p, &[b"tau", nm]), rho + s))
        .collect()
}

/// `PF = sum_u eq(r_inst, u) (1, x_u)`, a table of length `2^(nu-1)`
/// (spec 06 §6.1).
fn fold_public(x: &[Vec<K>], nu: usize, r_inst: &[K]) -> Vec<K> {
    let eqi = eq_table(r_inst);
    let half = 1usize << (nu - 1);
    let mut out = vec![K::ZERO; half];
    for (u, xu) in x.iter().enumerate() {
        let pp = public_part(xu, nu);
        for k in 0..half {
            out[k] += eqi[u] * pp[k];
        }
    }
    out
}

/// The Spartan prover (spec 06 §6.3, 6.5, 6.6). Returns
/// `(proof, claims)`. `unchecked` skips the satisfiability check (and
/// the outer-claim check); it exists for negative tests only, as in
/// Python.
///
/// # Panics
/// Panics where Python raises `ValueError`: no relations; relations not
/// sharing `(rho, nu)`; instance count not a power of two; `W`/`X` row
/// counts differing; malformed witness rows; witness not satisfying
/// the SIMD R1CS (unless `unchecked`); public inputs of unequal
/// length; invalid layout; invalid cross-step designation.
#[allow(clippy::too_many_arguments)]
pub fn prove(
    rels: &[R1CS],
    w: &[Vec<bool>],
    x: &[Vec<K>],
    transcript: &mut Transcript,
    p: &[u8],
    names: Option<&[Vec<u8>]>,
    segments: Option<&[Segment]>,
    cross: Option<&CrossStep>,
    unchecked: bool,
) -> (SpartanProof, Vec<Claim>) {
    let t = rels.len();
    let names = resolve_names(names, t);
    let (rho, nu) = {
        let first = rels.first().expect("no relations");
        (first.rho, first.nu)
    };
    assert!(
        rels.iter().all(|r| (r.rho, r.nu) == (rho, nu)),
        "relations must share (rho, nu)"
    );
    let q = w.len();
    assert!(
        q.is_power_of_two(),
        "number of instances must be a power of two"
    );
    let s = q.trailing_zeros() as usize;
    assert_eq!(x.len(), q, "W and X must have one row per instance");
    check_witness_bits(w, nu);
    if !unchecked {
        assert!(
            simd_satisfied(rels, w, x),
            "witness does not satisfy the SIMD R1CS"
        );
    }
    let nx = x[0].len();
    assert!(
        x.iter().all(|xi| xi.len() == nx),
        "public inputs must have equal length"
    );
    if let Some(segs) = segments {
        check_layout(segs, nu);
    }

    let tau = setup(transcript, p, t, rho, nu, s, nx, x, &names);

    // Outer tables, index = row + 2^rho * instance.
    let zs: Vec<Vec<K>> = w
        .iter()
        .zip(x)
        .map(|(wi, xi)| build_z(wi, xi, nu))
        .collect();
    let mut tabs: Vec<[Vec<K>; 4]> = Vec::with_capacity(t);
    for (ti, rel) in rels.iter().enumerate() {
        let mut cols: [Vec<K>; 3] = [Vec::new(), Vec::new(), Vec::new()];
        for z in &zs {
            for (m, mat) in rel.mats().into_iter().enumerate() {
                cols[m].extend(mat.mul_vec(z));
            }
        }
        let [ca, cb, cc] = cols;
        tabs.push([eq_table(&tau[ti]), ca, cb, cc]);
    }
    if !unchecked {
        for tab in &tabs {
            let ev = g_evals(&tab[0], &tab[1], &tab[2], &tab[3]);
            assert!(ev[0] + ev[1] == K::ZERO, "outer claim is non-zero");
        }
    }

    let mut msgs: Vec<Vec<Vec<K>>> = vec![Vec::new(); t];
    let mut r_row: Vec<Vec<K>> = vec![Vec::new(); t];
    let mut r_inst: Vec<K> = Vec::new();
    for _ in 0..rho {
        for ti in 0..t {
            let ev = g_evals(&tabs[ti][0], &tabs[ti][1], &tabs[ti][2], &tabs[ti][3]);
            let msg = vec![ev[0], ev[2], ev[3]];
            transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"msg"]), &msg);
            let r = transcript.challenge_k(&lbl(p, &[b"outer", &names[ti], b"row"]));
            msgs[ti].push(msg);
            r_row[ti].push(r);
            tabs[ti] = [
                bind_low(&tabs[ti][0], r),
                bind_low(&tabs[ti][1], r),
                bind_low(&tabs[ti][2], r),
                bind_low(&tabs[ti][3], r),
            ];
        }
    }
    for _ in 0..s {
        let evs: Vec<[K; 4]> = (0..t)
            .map(|ti| g_evals(&tabs[ti][0], &tabs[ti][1], &tabs[ti][2], &tabs[ti][3]))
            .collect();
        for ti in 0..t {
            let msg = vec![evs[ti][0], evs[ti][2], evs[ti][3]];
            transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"msg"]), &msg);
            msgs[ti].push(msg);
        }
        let r = transcript.challenge_k(&lbl(p, &[b"outer", b"inst"]));
        r_inst.push(r);
        for tab in &mut tabs {
            *tab = [
                bind_low(&tab[0], r),
                bind_low(&tab[1], r),
                bind_low(&tab[2], r),
                bind_low(&tab[3], r),
            ];
        }
    }
    let finals: Vec<Vec<K>> = (0..t)
        .map(|ti| vec![tabs[ti][1][0], tabs[ti][2][0], tabs[ti][3][0]])
        .collect();
    for ti in 0..t {
        transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"final"]), &finals[ti]);
    }
    let alpha = transcript.challenge_ks(&lbl(p, &[b"alpha"]), 3 * t);

    // Inner sum-check over columns.
    let mut v_star = K::ZERO;
    let mut mcomb = vec![K::ZERO; 1 << nu];
    for (ti, rel) in rels.iter().enumerate() {
        for (m, mat) in rel.mats().into_iter().enumerate() {
            let a = alpha[3 * ti + m];
            v_star += a * finals[ti][m];
            let ft = mat.fold_rows(&r_row[ti]);
            for (dst, y) in mcomb.iter_mut().zip(&ft) {
                *dst += a * *y;
            }
        }
    }
    let eqi = eq_table(&r_inst);
    let half = 1usize << (nu - 1);
    let mut wfold = vec![K::ZERO; half];
    for (u, wu) in w.iter().enumerate() {
        for c in 0..half {
            if wu[c] {
                wfold[c] += eqi[u];
            }
        }
    }
    let mut zfold = wfold.clone();
    zfold.extend(fold_public(x, nu, &r_inst));
    let (inner, r_y, _) = sumcheck_prove(
        v_star,
        vec![mcomb, zfold],
        &|v: &[K]| v[0] * v[1],
        2,
        transcript,
        &lbl(p, &[b"inner"]),
    );
    let r_col: Vec<K> = r_y[..nu - 1].to_vec();
    let v_w = mle_eval(&wfold, &r_col);
    transcript.absorb_k(&lbl(p, &[b"vw"]), v_w);

    let mut claims: Vec<Claim> = Vec::new();
    let mut seg_vals: Vec<K> = Vec::new();
    match segments {
        None => {
            let mut point = r_col.clone();
            point.extend_from_slice(&r_inst);
            claims.push(Claim {
                comp_id: -1,
                point,
                value: v_w,
            });
        }
        Some(segs) => {
            for sg in segs {
                if sg.kind == SegmentKind::Pad {
                    continue;
                }
                let tbl = segment_table(w, sg);
                let mut point: Vec<K> = r_col[..sg.log_cols].to_vec();
                point.extend_from_slice(&r_inst);
                let v = mle_eval_bits(&tbl, &point);
                transcript.absorb_k(&lbl(p, &[b"seg"]), v);
                seg_vals.push(v);
                claims.push(Claim {
                    comp_id: sg.seg_id,
                    point,
                    value: v,
                });
            }
        }
    }
    let mut proof = SpartanProof {
        outer_msgs: msgs,
        outer_finals: finals,
        inner,
        v_w,
        seg_vals,
        xs_proof: None,
        xs_vals: None,
    };

    if let Some(cross) = cross {
        cross_prove(
            &mut proof,
            &mut claims,
            segments,
            cross,
            w,
            s,
            transcript,
            p,
            unchecked,
        );
    }
    (proof, claims)
}

struct XsSetup {
    lam: usize,
    tau: Vec<K>,
    gamma: K,
    claim: K,
    seg_in: Segment,
    seg_out: Segment,
}

fn xs_setup(
    cross: &CrossStep,
    segments: Option<&[Segment]>,
    s: usize,
    transcript: &mut Transcript,
    p: &[u8],
) -> Result<XsSetup, VerificationError> {
    let find = |id: i64| {
        segments
            .unwrap_or(&[])
            .iter()
            .find(|sg| sg.seg_id == id)
            .copied()
    };
    let (si, so) = match (find(cross.in_id), find(cross.out_id)) {
        (Some(si), Some(so))
            if si.kind != SegmentKind::Pad
                && so.kind != SegmentKind::Pad
                && si.log_cols == so.log_cols
                && cross.in_id != cross.out_id =>
        {
            (si, so)
        }
        _ => return Err(VerificationError::new("cross-step segments invalid")),
    };
    let lam = si.log_cols;
    if cross.init.len() != (1usize << lam) || cross.fin.len() != (1usize << lam) {
        return Err(VerificationError::new(
            "cross-step public state has wrong length",
        ));
    }
    let as_ks = |bits: &[bool]| -> Vec<K> { bits.iter().map(|&b| K::from_bit(b)).collect() };
    transcript.absorb_ks(&lbl(p, &[b"xs", b"init"]), &as_ks(&cross.init));
    transcript.absorb_ks(&lbl(p, &[b"xs", b"fin"]), &as_ks(&cross.fin));
    let tau = transcript.challenge_ks(&lbl(p, &[b"xs", b"tau"]), lam + s);
    let gamma = transcript.challenge_k(&lbl(p, &[b"xs", b"gamma"]));
    let claim = gamma * mle_eval_bits(&cross.init, &tau[..lam])
        + gamma * gamma * mle_eval_bits(&cross.fin, &tau[..lam]);
    Ok(XsSetup {
        lam,
        tau,
        gamma,
        claim,
        seg_in: si,
        seg_out: so,
    })
}

#[allow(clippy::too_many_arguments)]
fn cross_prove(
    proof: &mut SpartanProof,
    claims: &mut Vec<Claim>,
    segments: Option<&[Segment]>,
    cross: &CrossStep,
    w: &[Vec<bool>],
    s: usize,
    transcript: &mut Transcript,
    p: &[u8],
    unchecked: bool,
) {
    let setup = xs_setup(cross, segments, s, transcript, p).expect("cross-step segments invalid");
    let (lam, gamma) = (setup.lam, setup.gamma);
    let mut claim = setup.claim;
    let (q, n) = (1usize << s, 1usize << lam);
    let (eqk, equ) = (eq_table(&setup.tau[..lam]), eq_table(&setup.tau[lam..]));
    let a_out_u: Vec<K> = (0..q)
        .map(|u| {
            (if u != q - 1 { equ[u] } else { K::ZERO })
                + (if u == q - 1 { gamma * gamma } else { K::ZERO })
        })
        .collect();
    let a_in_u: Vec<K> = (0..q)
        .map(|u| {
            (if u >= 1 { equ[u - 1] } else { K::ZERO }) + (if u == 0 { gamma } else { K::ZERO })
        })
        .collect();
    let tbl_in = segment_table(w, &setup.seg_in);
    let tbl_out = segment_table(w, &setup.seg_out);
    let size = n * q;
    let e: Vec<K> = (0..size).map(|i| eqk[i % n]).collect();
    let ao: Vec<K> = (0..size).map(|i| a_out_u[i / n]).collect();
    let ai: Vec<K> = (0..size).map(|i| a_in_u[i / n]).collect();
    let as_ks = |bits: &[bool]| -> Vec<K> { bits.iter().map(|&b| K::from_bit(b)).collect() };
    if unchecked {
        // A cheating prover proves the *true* sum instead of the
        // public claim.
        claim = K::ZERO;
        for i in 0..size {
            claim += e[i] * (ao[i] * K::from_bit(tbl_out[i]) + ai[i] * K::from_bit(tbl_in[i]));
        }
    }
    let (sc, r, fin) = sumcheck_prove(
        claim,
        vec![e, ao, as_ks(&tbl_out), ai, as_ks(&tbl_in)],
        &|v: &[K]| v[0] * (v[1] * v[2] + v[3] * v[4]),
        2,
        transcript,
        &lbl(p, &[b"xs", b"sc"]),
    );
    let (v_out, v_in) = (fin[2], fin[4]);
    transcript.absorb_ks(&lbl(p, &[b"xs", b"final"]), &[v_in, v_out]);
    proof.xs_proof = Some(sc);
    proof.xs_vals = Some(vec![v_in, v_out]);
    claims.push(Claim {
        comp_id: cross.in_id,
        point: r.clone(),
        value: v_in,
    });
    claims.push(Claim {
        comp_id: cross.out_id,
        point: r,
        value: v_out,
    });
}

/// The Spartan verifier (spec 06 §6.3, 6.5, 6.6, 6.8). Returns the
/// output claims on success.
///
/// # Errors
/// Returns [`VerificationError`] mirroring Python's `verify` (see spec
/// 06 §6.8 for the ordered checks).
///
/// # Panics
/// Panics if `rels` is empty or the layout is invalid (Python raises
/// `IndexError` / `ValueError` — caller errors, not proof failures).
#[allow(clippy::too_many_arguments)]
#[allow(clippy::needless_range_loop)]
pub fn verify(
    rels: &[R1CS],
    s: usize,
    x: &[Vec<K>],
    proof: &SpartanProof,
    transcript: &mut Transcript,
    p: &[u8],
    names: Option<&[Vec<u8>]>,
    segments: Option<&[Segment]>,
    cross: Option<&CrossStep>,
) -> Result<Vec<Claim>, VerificationError> {
    let t = rels.len();
    let names = resolve_names(names, t);
    let (rho, nu) = {
        let first = rels.first().expect("no relations");
        (first.rho, first.nu)
    };
    let q = 1usize << s;
    if x.len() != q {
        return Err(VerificationError::new("wrong number of public inputs"));
    }
    let nx = x[0].len();
    if x.iter().any(|xi| xi.len() != nx) {
        return Err(VerificationError::new(
            "public inputs must have equal length",
        ));
    }
    if let Some(segs) = segments {
        check_layout(segs, nu);
    }
    if proof.outer_msgs.len() != t || proof.outer_finals.len() != t {
        return Err(VerificationError::new("malformed proof"));
    }
    if proof.outer_msgs.iter().any(|m| m.len() != rho + s) {
        return Err(VerificationError::new("wrong number of outer rounds"));
    }
    let tau = setup(transcript, p, t, rho, nu, s, nx, x, &names);

    let mut cur = vec![K::ZERO; t];
    let step = |cur: &mut [K], ti: usize, msg: &[K], r: K| -> Result<(), VerificationError> {
        if msg.len() != 3 {
            return Err(VerificationError::new("malformed outer message"));
        }
        let ys = [msg[0], cur[ti] + msg[0], msg[1], msg[2]];
        cur[ti] = interpolate_eval(&ys, r);
        Ok(())
    };

    let mut r_row: Vec<Vec<K>> = vec![Vec::new(); t];
    let mut r_inst: Vec<K> = Vec::new();
    for i in 0..rho {
        for ti in 0..t {
            let msg = &proof.outer_msgs[ti][i];
            transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"msg"]), msg);
            let r = transcript.challenge_k(&lbl(p, &[b"outer", &names[ti], b"row"]));
            step(&mut cur, ti, msg, r)?;
            r_row[ti].push(r);
        }
    }
    for i in 0..s {
        for ti in 0..t {
            transcript.absorb_ks(
                &lbl(p, &[b"outer", &names[ti], b"msg"]),
                &proof.outer_msgs[ti][rho + i],
            );
        }
        let r = transcript.challenge_k(&lbl(p, &[b"outer", b"inst"]));
        for ti in 0..t {
            step(&mut cur, ti, &proof.outer_msgs[ti][rho + i], r)?;
        }
        r_inst.push(r);
    }
    for ti in 0..t {
        let fv = &proof.outer_finals[ti];
        if fv.len() != 3 {
            return Err(VerificationError::new("malformed terminal values"));
        }
        let mut point = r_row[ti].clone();
        point.extend_from_slice(&r_inst);
        if cur[ti] != eq_eval(&tau[ti], &point) * (fv[0] * fv[1] + fv[2]) {
            return Err(VerificationError::new("outer sum-check final check failed"));
        }
        transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"final"]), fv);
    }
    let alpha = transcript.challenge_ks(&lbl(p, &[b"alpha"]), 3 * t);
    let mut v_star = K::ZERO;
    for ti in 0..t {
        for m in 0..3 {
            v_star += alpha[3 * ti + m] * proof.outer_finals[ti][m];
        }
    }
    let (r_y, e) = sumcheck_verify(
        v_star,
        nu,
        2,
        &proof.inner,
        transcript,
        &lbl(p, &[b"inner"]),
    )?;
    let mut mf = K::ZERO;
    for (ti, rel) in rels.iter().enumerate() {
        for (m, mat) in rel.mats().into_iter().enumerate() {
            mf += alpha[3 * ti + m] * mat.mle(&r_row[ti], &r_y);
        }
    }
    let r_col: Vec<K> = r_y[..nu - 1].to_vec();
    let top = r_y[nu - 1];
    let pub_eval = mle_eval(&fold_public(x, nu, &r_inst), &r_col);
    let v_z = (K::ONE + top) * proof.v_w + top * pub_eval;
    if e != mf * v_z {
        return Err(VerificationError::new("inner sum-check final check failed"));
    }
    transcript.absorb_k(&lbl(p, &[b"vw"]), proof.v_w);

    let mut claims: Vec<Claim> = Vec::new();
    match segments {
        None => {
            let mut point = r_col.clone();
            point.extend_from_slice(&r_inst);
            claims.push(Claim {
                comp_id: -1,
                point,
                value: proof.v_w,
            });
        }
        Some(segs) => {
            let real: Vec<&Segment> = segs
                .iter()
                .filter(|sg| sg.kind != SegmentKind::Pad)
                .collect();
            if proof.seg_vals.len() != real.len() {
                return Err(VerificationError::new("wrong number of segment claims"));
            }
            let mut acc = K::ZERO;
            for (sg, &v) in real.iter().zip(&proof.seg_vals) {
                transcript.absorb_k(&lbl(p, &[b"seg"]), v);
                let qi = &r_col[sg.log_cols..];
                acc += eq_eval(qi, &bits_of(sg.block, nu - 1 - sg.log_cols)) * v;
                let mut point: Vec<K> = r_col[..sg.log_cols].to_vec();
                point.extend_from_slice(&r_inst);
                claims.push(Claim {
                    comp_id: sg.seg_id,
                    point,
                    value: v,
                });
            }
            if acc != proof.v_w {
                return Err(VerificationError::new(
                    "segment claims inconsistent with v_W",
                ));
            }
        }
    }
    if let Some(cross) = cross {
        let xs = xs_setup(cross, segments, s, transcript, p)?;
        let (lam, gamma) = (xs.lam, xs.gamma);
        let (xs_proof, xs_vals) = match (&proof.xs_proof, &proof.xs_vals) {
            (Some(sc), Some(vals)) if vals.len() == 2 => (sc, vals),
            _ => return Err(VerificationError::new("missing cross-step proof")),
        };
        let (r, e) = sumcheck_verify(
            xs.claim,
            lam + s,
            2,
            xs_proof,
            transcript,
            &lbl(p, &[b"xs", b"sc"]),
        )?;
        let (v_in, v_out) = (xs_vals[0], xs_vals[1]);
        let (a_out, a_in) = xs_weights(&xs.tau[lam..], gamma, &r[lam..]);
        if e != eq_eval(&xs.tau[..lam], &r[..lam]) * (a_out * v_out + a_in * v_in) {
            return Err(VerificationError::new("cross-step final check failed"));
        }
        transcript.absorb_ks(&lbl(p, &[b"xs", b"final"]), &[v_in, v_out]);
        claims.push(Claim {
            comp_id: cross.in_id,
            point: r.clone(),
            value: v_in,
        });
        claims.push(Claim {
            comp_id: cross.out_id,
            point: r,
            value: v_out,
        });
    }
    Ok(claims)
}
