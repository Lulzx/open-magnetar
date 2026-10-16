//! BinaryRouter (docs/spec/08-router.md): shift and sub-word store
//! instances. Mirrors `reference/openmagnetar/router.py` byte for byte in
//! its transcript interaction.
//!
//! `wbits` is log2 of the word width `W`. The specification fixes
//! `wbits = 6` (`W = 64`); smaller values exist only to keep tests fast.
//! For stores the offset has `wbits - 3` bits (3 for `W = 64`).

use om_field::K;
use om_memcheck::onehot::EvalClaim;
use om_sumcheck::{
    SumcheckProof, VerificationError, bind_low_in_place, combine_sum, eq_eval, eq_table,
    interpolate_eval, sumcheck_init, sumcheck_prove, sumcheck_round_evals, sumcheck_verify,
};
use om_transcript::Transcript;
use rayon::prelude::*;

use crate::sublabel;

/// Shift kind 0: `src << amt` (CONVENTIONS C7).
pub const SLL: usize = 0;
/// Shift kind 1: `src >> amt` logical.
pub const SRL: usize = 1;
/// Shift kind 2: `src >> amt` arithmetic.
pub const SRA: usize = 2;
/// Shift kind 3: `sext32((src << amt)[31:0])`, `amt < 32`.
pub const SLLW: usize = 3;
/// Shift kind 4: `sext32(src[31:0] >> amt)`, `amt < 32`.
pub const SRLW: usize = 4;
/// Shift kind 5: `sext32(src[31:0] >>a amt)`, `amt < 32`.
pub const SRAW: usize = 5;
/// Shift kind 6: `sext32(src[31:0])`, `amt = 0`.
pub const SEXT32: usize = 6;
/// Shift kind 7: `zext32(src[31:0])`, `amt = 0`.
pub const ZEXT32: usize = 7;

/// Names of the eight shift kinds, in kind order (C7).
pub const KIND_NAMES: [&str; 8] = [
    "SLL", "SRL", "SRA", "SLLW", "SRLW", "SRAW", "SEXT32", "ZEXT32",
];

// ------------------------------------------------------------------- shifts

/// Whether routing `(amt, kind)` is valid at word-width log `wbits`:
/// kinds 0–2 take any `amt < W`, kinds 3–5 take `amt < W/2`, kinds 6–7
/// (and, as in Python, any other kind value) take only `amt = 0`.
pub fn shift_valid(kind: usize, amt: usize, wbits: usize) -> bool {
    let w = 1usize << wbits;
    match kind {
        SLL | SRL | SRA => amt < w,
        SLLW | SRLW | SRAW => amt < w / 2,
        _ => amt == 0,
    }
}

/// Source bit index feeding output bit `o` under routing `(amt, kind)`,
/// or `None` (invalid routings, and outputs with no source, are `None`:
/// `R_sh` has no entry, so the output bit is 0).
///
/// # Panics
/// Panics for a kind outside `0..8` whose amount passes
/// [`shift_valid`]'s fallback (`amt == 0`), mirroring Python's
/// `ValueError("bad kind")`.
pub fn shift_source(kind: usize, amt: usize, o: usize, wbits: usize) -> Option<usize> {
    let w = 1usize << wbits;
    let h = w / 2;
    if !shift_valid(kind, amt, wbits) {
        return None;
    }
    match kind {
        SLL => {
            if o >= amt {
                Some(o - amt)
            } else {
                None
            }
        }
        SRL => {
            if o + amt < w {
                Some(o + amt)
            } else {
                None
            }
        }
        SRA => Some((o + amt).min(w - 1)),
        SLLW => {
            if o < h {
                if o >= amt { Some(o - amt) } else { None }
            } else {
                Some(h - 1 - amt)
            }
        }
        SRLW => {
            if o < h {
                if o + amt < h { Some(o + amt) } else { None }
            } else if amt == 0 {
                Some(h - 1 + amt)
            } else {
                None
            }
        }
        SRAW => {
            if o < h {
                Some((o + amt).min(h - 1))
            } else {
                Some(h - 1)
            }
        }
        SEXT32 => {
            if o < h {
                Some(o)
            } else {
                Some(h - 1)
            }
        }
        ZEXT32 => {
            if o < h {
                Some(o)
            } else {
                None
            }
        }
        _ => panic!("bad kind"),
    }
}

/// Support of `R_sh`: tuples `(o, u, h)` with `h = amt + W * kind`, in
/// Python's enumeration order (kind, then amount, then output bit).
/// `|supp R_sh| = 12512` at `wbits = 6`.
pub fn shift_entries(wbits: usize) -> Vec<(usize, usize, usize)> {
    let w = 1usize << wbits;
    let mut out = Vec::new();
    for kind in 0..8 {
        for amt in 0..w {
            for o in 0..w {
                if let Some(u) = shift_source(kind, amt, o, wbits) {
                    out.push((o, u, amt + w * kind));
                }
            }
        }
    }
    out
}

/// Reference shift semantics with integer arithmetic (independent of
/// [`shift_source`]); returns 0 for invalid routings. `src` is masked to
/// `W` bits first, as in Python.
pub fn apply_shift(kind: usize, amt: usize, src: u64, wbits: usize) -> u64 {
    let w = 1u128 << wbits;
    let h = w / 2;
    let (m, mh) = ((1u128 << w) - 1, (1u128 << h) - 1);
    if !shift_valid(kind, amt, wbits) {
        return 0;
    }
    let sext = |x: u128| {
        if (x >> (h - 1)) & 1 == 1 {
            x | (m ^ mh)
        } else {
            x
        }
    };
    // Python's arithmetic shift of the signed value, via sign extension
    // to 128 bits followed by a logical shift (callers mask to `w`/`h`).
    let sgn_shift = |x: u128, width: u128| {
        let ext = if (x >> (width - 1)) & 1 == 1 {
            x | (!0u128 << width)
        } else {
            x
        };
        ext >> amt
    };
    let src = u128::from(src) & m;
    let amt = amt as u32;
    let out = match kind {
        SLL => (src << amt) & m,
        SRL => src >> amt,
        SRA => sgn_shift(src, w) & m,
        SLLW => sext((src << amt) & mh),
        SRLW => sext((src & mh) >> amt),
        SRAW => sext(sgn_shift(src & mh, h) & mh),
        SEXT32 => sext(src & mh),
        _ => src & mh, // ZEXT32 (any other valid kind, as in Python's fallthrough)
    };
    out as u64
}

/// `R̃_sh(r_o, r_u, r_h)`, `r_h = r_hlo ∥ r_hhi` (`h = amt + W*kind`),
/// by the `O(|supp R|)` eq-table sum of spec 08 §8.2 (Python
/// `shift_R_eval`).
pub fn shift_r_eval(r_o: &[K], r_u: &[K], r_h: &[K], wbits: usize) -> K {
    let (eo, eu, eh) = (eq_table(r_o), eq_table(r_u), eq_table(r_h));
    let mut acc = K::ZERO;
    for (o, u, h) in shift_entries(wbits) {
        acc += eo[o] * eu[u] * eh[h];
    }
    acc
}

// ------------------------------------------------------------------- stores

/// Whether the store `(h, a)` — width `2^h` bytes at byte offset `a` —
/// is valid: the width fits the word, `a` is a byte offset in the word,
/// and `a mod 2^h = 0` (natural alignment, C5/C7).
pub fn store_valid(h: usize, a: usize, wbits: usize) -> bool {
    let nbytes = (1usize << wbits) / 8;
    let w = 1usize << h;
    w <= nbytes && a.is_multiple_of(w) && a < nbytes
}

/// Support of `R_st`: tuples `(o, u, h, a)`, in Python's enumeration
/// order. Inside the store lane each output bit has exactly two sources
/// (the old bit `u = o` and the store-source bit `u = W + 8(b−a) + i`),
/// so the routed sum is the XOR increment (spec 08 §8.3).
/// `|supp R_st| = 512` at `wbits = 6`.
pub fn store_entries(wbits: usize) -> Vec<(usize, usize, usize, usize)> {
    let w = 1usize << wbits;
    let mut out = Vec::new();
    for h in 0..4 {
        for a in 0..w / 8 {
            if !store_valid(h, a, wbits) {
                continue;
            }
            for b in a..a + (1 << h) {
                for i in 0..8 {
                    let o = 8 * b + i;
                    out.push((o, o, h, a));
                    out.push((o, w + 8 * (b - a) + i, h, a));
                }
            }
        }
    }
    out
}

/// Reference store increment (`old ⊕ new`) for a store of width `2^h`
/// bytes at byte offset `a`; 0 if `(h, a)` is invalid. The store writes
/// the low `2^h` bytes of `src` at byte offset `a`.
pub fn apply_store(old: u64, src: u64, h: usize, a: usize, wbits: usize) -> u64 {
    if !store_valid(h, a, wbits) {
        return 0;
    }
    let w = 1u128 << h;
    let mask = ((1u128 << (8 * w)) - 1) << (8 * a);
    let (old, src) = (u128::from(old), u128::from(src));
    let new = (old & !mask) | ((src << (8 * a)) & mask);
    (old ^ new) as u64
}

/// `R̃_st(r_o, r_u, r_h, r_a)`: multilinear in the offset arguments
/// `r_a`, by the `O(|supp R|)` eq-table sum of spec 08 §8.3 (Python
/// `store_R_eval`).
pub fn store_r_eval(r_o: &[K], r_u: &[K], r_h: &[K], r_a: &[K], wbits: usize) -> K {
    let (eo, eu, eh) = (eq_table(r_o), eq_table(r_u), eq_table(r_h));
    let ea = eq_table(r_a);
    let mut acc = K::ZERO;
    for (o, u, h, a) in store_entries(wbits) {
        acc += eo[o] * eu[u] * eh[h] * ea[a];
    }
    acc
}

// --------------------------------------------------------------- witnesses

/// Shift-instance witness tables (Python `shift_witness`'s dict), all
/// flat with the first-listed index in the low bits (C2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShiftWitness {
    /// Source bits `X(u, j)`, flat `u + W·j`.
    pub x: Vec<bool>,
    /// Amount one-hot `Q_lo(h_lo, j)`, flat `h_lo + W·j`; all zero on a
    /// cycle without a shift.
    pub qlo: Vec<bool>,
    /// Kind one-hot `Q_hi(h_hi, j)`, flat `h_hi + 8·j`; all zero on a
    /// cycle without a shift.
    pub qhi: Vec<bool>,
    /// Output bits `Y(o, j)`, flat `o + W·j`.
    pub y: Vec<bool>,
}

/// One shift cycle: `(src_word, route)` with `route = (amt, kind)`, or
/// `None` for a cycle without a shift.
pub type ShiftCycle = (u64, Option<(usize, usize)>);

/// Build the shift witness from per-cycle `(src_word, route)` pairs,
/// where `route` is `(amt, kind)` or `None` for a non-shift cycle.
pub fn shift_witness(cycles: &[ShiftCycle], wbits: usize) -> ShiftWitness {
    let w = 1usize << wbits;
    let (mut x, mut qlo, mut qhi, mut y) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for &(src, route) in cycles {
        x.extend((0..w).map(|u| bit(src, u)));
        let (mut lo, mut hi) = (vec![false; w], vec![false; 8]);
        let mut out = 0u64;
        if let Some((amt, kind)) = route {
            lo[amt] = true;
            hi[kind] = true;
            out = apply_shift(kind, amt, src, wbits);
        }
        qlo.extend(lo);
        qhi.extend(hi);
        y.extend((0..w).map(|o| bit(out, o)));
    }
    ShiftWitness { x, qlo, qhi, y }
}

/// Store-instance witness tables (Python `store_witness`'s dict), all
/// flat with the first-listed index in the low bits (C2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoreWitness {
    /// Source bits `X(u, j)`, flat `u + 2W·j`: `u < W` is old-word bit
    /// `u`, `u ≥ W` is store-source bit `u − W`.
    pub x: Vec<bool>,
    /// Width one-hot `Q_st(h, j)`, flat `h + 4·j`; all zero on a
    /// non-store cycle.
    pub q: Vec<bool>,
    /// Offset-bit tables: `abits[b][j]` is bit `b` of cycle `j`'s byte
    /// offset `a` (`wbits − 3` tables of length `2^n`).
    pub abits: Vec<Vec<bool>>,
    /// Increment bits `Inc(o, j)`, flat `o + W·j`.
    pub inc: Vec<bool>,
}

/// One store cycle: `(old_word, src_word, route)` with
/// `route = (width, offset)`, or `None` for a non-store cycle.
pub type StoreCycle = (u64, u64, Option<(usize, usize)>);

/// Build the store witness from per-cycle `(old_word, src_word, route)`
/// triples, where `route` is `(width, offset)` or `None` for a
/// non-store cycle (whose offset bits are recorded as 0).
pub fn store_witness(cycles: &[StoreCycle], wbits: usize) -> StoreWitness {
    let (w, na) = (1usize << wbits, wbits - 3);
    let (mut x, mut q, mut inc) = (Vec::new(), Vec::new(), Vec::new());
    let mut abits: Vec<Vec<bool>> = vec![Vec::new(); na];
    for &(old, src, route) in cycles {
        x.extend((0..w).map(|u| bit(old, u)));
        x.extend((0..w).map(|u| bit(src, u)));
        let mut width = [false; 4];
        let (mut increment, mut a) = (0u64, 0usize);
        if let Some((h, off)) = route {
            a = off;
            width[h] = true;
            increment = apply_store(old, src, h, a, wbits);
        }
        q.extend(width);
        inc.extend((0..w).map(|o| bit(increment, o)));
        for (b, table) in abits.iter_mut().enumerate() {
            table.push((a >> b) & 1 == 1);
        }
    }
    StoreWitness { x, q, abits, inc }
}

fn bit(word: u64, i: usize) -> bool {
    // Python shifts are unbounded; bits at or above 64 of a u64 are 0.
    i < 64 && (word >> i) & 1 == 1
}

// ----------------------------------------------------------- shift protocol

/// A router proof: the routing sum-check and the claimed evaluations
/// (shift: `[X~, Q̃_lo, Q̃_hi]`; store: `[X~, Q̃, ã_1, …, ã_na]`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RouterProof {
    pub sc: SumcheckProof,
    pub evals: Vec<K>,
}

fn absorb_claim(transcript: &mut Transcript, label: &[u8], r_o: &[K], r_j: &[K], y: K) {
    transcript.absorb_ks(&sublabel(label, b"/point_o"), r_o);
    transcript.absorb_ks(&sublabel(label, b"/point_c"), r_j);
    transcript.absorb_k(&sublabel(label, b"/y"), y);
}

fn shift_claims(n: usize, wbits: usize, r: &[K], evals: &[K]) -> Vec<EvalClaim> {
    let (s_j, s_u) = (&r[..n], &r[n..n + wbits]);
    let (s_lo, s_hi) = (&r[n + wbits..n + 2 * wbits], &r[n + 2 * wbits..]);
    let claim = |poly: &str, low: &[K], value: K| EvalClaim {
        poly: poly.to_string(),
        point: [low, s_j].concat(),
        value,
    };
    vec![
        claim("shift/src", s_u, evals[0]),
        claim("shift/qlo", s_lo, evals[1]),
        claim("shift/qhi", s_hi, evals[2]),
    ]
}

fn mul5(v: &[K]) -> K {
    v[0] * v[1] * v[2] * v[3] * v[4]
}

fn bits_to_k(table: &[bool]) -> Vec<K> {
    table.iter().map(|&b| K::from_bit(b)).collect()
}

/// Prove the shift routing identity against the input claim
/// `Ỹ(r_o ∥ r_j) = y` (spec 08 §8.2): one sum-check over `n + 2·wbits + 3`
/// variables (cycle, source, amount, kind) of uniform degree 4. The
/// sum-check claim is the actual sum of the prover's tables (`y` is only
/// absorbed), so a wrong `Y` fails verification, as in Python.
///
/// Returns the proof and the output claims `shift/src`, `shift/qlo`,
/// `shift/qhi` at the sum-check point.
///
/// # Panics
/// Panics on malformed witness tables (indexing), as Python raises.
#[allow(clippy::too_many_arguments)]
pub fn shift_prove(
    n: usize,
    wit: &ShiftWitness,
    r_o: &[K],
    r_j: &[K],
    y: K,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
) -> (RouterProof, Vec<EvalClaim>) {
    let (t, w) = (1usize << n, 1usize << wbits);
    absorb_claim(transcript, label, r_o, r_j, y);
    let eo = eq_table(r_o);
    let mut rr = vec![K::ZERO; w * 8 * w]; // flat u + W*h
    for (o, u, h) in shift_entries(wbits) {
        rr[u + w * h] += eo[o];
    }
    let eqj = eq_table(r_j);
    let (x, qlo, qhi) = (bits_to_k(&wit.x), bits_to_k(&wit.qlo), bits_to_k(&wit.qhi));
    let mut tabs: Vec<Vec<K>> = vec![Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new()];
    for hhi in 0..8 {
        for hlo in 0..w {
            for u in 0..w {
                for j in 0..t {
                    tabs[0].push(eqj[j]);
                    tabs[1].push(x[u + w * j]);
                    tabs[2].push(qlo[hlo + w * j]);
                    tabs[3].push(qhi[hhi + 8 * j]);
                    tabs[4].push(rr[u + w * (hlo + w * hhi)]);
                }
            }
        }
    }
    let claim = combine_sum(&tabs, &mul5);
    let (sc, r, mles) = sumcheck_prove(claim, tabs, &mul5, 4, transcript, &sublabel(label, b"/sc"));
    let evals = vec![mles[1], mles[2], mles[3]];
    transcript.absorb_ks(&sublabel(label, b"/evals"), &evals);
    let claims = shift_claims(n, wbits, &r, &evals);
    (RouterProof { sc, evals }, claims)
}

/// Verify a shift router proof against the input claim
/// `Ỹ(r_o ∥ r_j) = y`, returning the output claims (spec 08 §8.2).
///
/// # Errors
/// Returns [`VerificationError`] on a malformed `evals` length (checked
/// before any transcript interaction, as in Python), a bad sum-check, or
/// a failed final check
/// `eq(r_j, s_j) · X~ · Q̃_lo · Q̃_hi · R̃_sh(r_o, s_u, s_h)`.
#[allow(clippy::too_many_arguments)]
pub fn shift_verify(
    n: usize,
    r_o: &[K],
    r_j: &[K],
    y: K,
    proof: &RouterProof,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
) -> Result<Vec<EvalClaim>, VerificationError> {
    if proof.evals.len() != 3 {
        return Err(VerificationError::new("shift: malformed evals"));
    }
    absorb_claim(transcript, label, r_o, r_j, y);
    let m = n + 2 * wbits + 3;
    let (r, expected) = sumcheck_verify(y, m, 4, &proof.sc, transcript, &sublabel(label, b"/sc"))?;
    transcript.absorb_ks(&sublabel(label, b"/evals"), &proof.evals);
    let (s_j, s_u) = (&r[..n], &r[n..n + wbits]);
    let r_h = &r[n + wbits..];
    let (x, qlo, qhi) = (proof.evals[0], proof.evals[1], proof.evals[2]);
    let val = eq_eval(r_j, s_j) * x * qlo * qhi * shift_r_eval(r_o, s_u, r_h, wbits);
    if val != expected {
        return Err(VerificationError::new("shift: final check failed"));
    }
    Ok(shift_claims(n, wbits, &r, &proof.evals))
}

// ----------------------------------------------------------- store protocol

fn store_claims(n: usize, wbits: usize, r: &[K], evals: &[K]) -> Vec<EvalClaim> {
    let na = wbits - 3;
    let (s_j, s_u, s_h) = (&r[..n], &r[n..n + wbits + 1], &r[n + wbits + 1..]);
    let mut out = vec![
        EvalClaim {
            poly: "store/src".to_string(),
            point: [s_u, s_j].concat(),
            value: evals[0],
        },
        EvalClaim {
            poly: "store/q".to_string(),
            point: [s_h, s_j].concat(),
            value: evals[1],
        },
    ];
    out.extend((0..na).map(|b| EvalClaim {
        poly: format!("store/a{b}"),
        point: s_j.to_vec(),
        value: evals[2 + b],
    }));
    out
}

fn store_combine(na: usize) -> impl Fn(&[K]) -> K {
    move |v: &[K]| {
        let (eq, x, q) = (v[0], v[1], v[2]);
        let ab = &v[3..3 + na];
        let mut acc = K::ZERO;
        for a in 0..(1usize << na) {
            let mut e = v[3 + na + a];
            for (b, &abit) in ab.iter().enumerate() {
                e *= K::ONE + abit + K::from_bit((a >> b) & 1 == 1);
            }
            acc += e;
        }
        eq * x * q * acc
    }
}

/// Prove the store routing identity against the input claim
/// `Ĩnc(r_o ∥ r_j) = y` (spec 08 §8.3): one sum-check over
/// `n + wbits + 1 + 2` variables (cycle, source, width) of degree
/// `3 + (wbits − 3)`. The sum-check claim is the actual sum of the
/// prover's tables (`y` is only absorbed), as in Python.
///
/// Returns the proof and the output claims `store/src`, `store/q`,
/// `store/a0`…`store/a{na−1}` at the sum-check point.
///
/// # Panics
/// Panics on malformed witness tables (indexing), as Python raises.
#[allow(clippy::too_many_arguments)]
pub fn store_prove(
    n: usize,
    wit: &StoreWitness,
    r_o: &[K],
    r_j: &[K],
    y: K,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
) -> (RouterProof, Vec<EvalClaim>) {
    let (t, w, na) = (1usize << n, 1usize << wbits, wbits - 3);
    let na_count = 1usize << na;
    absorb_claim(transcript, label, r_o, r_j, y);
    let eo = eq_table(r_o);
    let mut ra = vec![vec![K::ZERO; 2 * w * 4]; na_count]; // flat u + 2W*h per offset a
    for (o, u, h, a) in store_entries(wbits) {
        ra[a][u + 2 * w * h] += eo[o];
    }
    let eqj = eq_table(r_j);
    let x = bits_to_k(&wit.x);
    let q = bits_to_k(&wit.q);
    let ab: Vec<Vec<K>> = wit.abits.iter().map(|tab| bits_to_k(tab)).collect();
    let mut tabs: Vec<Vec<K>> = (0..3 + na + na_count).map(|_| Vec::new()).collect();
    for h in 0..4 {
        for u in 0..2 * w {
            for j in 0..t {
                tabs[0].push(eqj[j]);
                tabs[1].push(x[u + 2 * w * j]);
                tabs[2].push(q[h + 4 * j]);
                for b in 0..na {
                    tabs[3 + b].push(ab[b][j]);
                }
                for a in 0..na_count {
                    tabs[3 + na + a].push(ra[a][u + 2 * w * h]);
                }
            }
        }
    }
    let f = store_combine(na);
    let claim = combine_sum(&tabs, &f);
    let (sc, r, mles) = sumcheck_prove(
        claim,
        tabs,
        &f,
        3 + na,
        transcript,
        &sublabel(label, b"/sc"),
    );
    let mut evals = vec![mles[1], mles[2]];
    evals.extend((0..na).map(|b| mles[3 + b]));
    transcript.absorb_ks(&sublabel(label, b"/evals"), &evals);
    let claims = store_claims(n, wbits, &r, &evals);
    (RouterProof { sc, evals }, claims)
}

/// Verify a store router proof against the input claim
/// `Ĩnc(r_o ∥ r_j) = y`, returning the output claims (spec 08 §8.3).
///
/// # Errors
/// Returns [`VerificationError`] on a malformed `evals` length (checked
/// before any transcript interaction, as in Python), a bad sum-check, or
/// a failed final check
/// `eq(r_j, s_j) · X~ · Q̃ · R̃_st(r_o, s_u, s_h, (ã_1, …, ã_na))`.
#[allow(clippy::too_many_arguments)]
pub fn store_verify(
    n: usize,
    r_o: &[K],
    r_j: &[K],
    y: K,
    proof: &RouterProof,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
) -> Result<Vec<EvalClaim>, VerificationError> {
    let na = wbits - 3;
    if proof.evals.len() != 2 + na {
        return Err(VerificationError::new("store: malformed evals"));
    }
    absorb_claim(transcript, label, r_o, r_j, y);
    let m = n + wbits + 1 + 2;
    let (r, expected) = sumcheck_verify(
        y,
        m,
        3 + na,
        &proof.sc,
        transcript,
        &sublabel(label, b"/sc"),
    )?;
    transcript.absorb_ks(&sublabel(label, b"/evals"), &proof.evals);
    let (s_j, s_u, s_h) = (&r[..n], &r[n..n + wbits + 1], &r[n + wbits + 1..]);
    let (x, q) = (proof.evals[0], proof.evals[1]);
    let a_vals = &proof.evals[2..];
    let val = eq_eval(r_j, s_j) * x * q * store_r_eval(r_o, s_u, s_h, a_vals, wbits);
    if val != expected {
        return Err(VerificationError::new("store: final check failed"));
    }
    Ok(store_claims(n, wbits, &r, &proof.evals))
}

// ---------------------------------------------------------------- fast provers
// Same transcript and proof as `shift_prove` / `store_prove`, but memory
// proportional to the compact per-cycle witness (spec 08, Integration
// notes: informative; the dense functions remain the definition).
//
// * The witness is held as per-cycle words and selector bytes
//   ([`ShiftCompact`], [`StoreCompact`]), never as `T × W` field or bool
//   tables.
// * `eq(r_j, ·)` is never bound: after binding `s_0..s_{i-1}` it equals
//   `es · eq(r_j[i..], ·)` with the scalar `es = Π_l eq(r_l, s_l)`, and
//   the suffix `eq` is a split table (two `√`-size halves).
// * For the first `DIRECT_ROUNDS` cycle rounds the bound value of a
//   per-cycle table at a position, `Σ_b eq(s_<i, b) · F(cycle)`, is
//   gathered directly from the compact words (set bits only, and only in
//   pairs whose selectors are non-zero). Afterwards the bound tables
//   (`T / 2^DIRECT_ROUNDS` positions) are materialised and bound in place.
// * Per pair, each factor is linear in `t`, so the routed source sum
//   `B_h(t) = Σ_u X_u(t)·R(u, h)` is computed once from its values at
//   `t = 0, 1`.
// Field arithmetic is exact, so every round message equals the dense
// prover's (checked against `shift_prove` / `store_prove` in the tests).

/// Selector byte meaning "no one-hot entry on this cycle" in
/// [`ShiftCompact`] and [`StoreCompact`].
pub const NO_ROUTE: u8 = u8::MAX;

/// Cycle rounds computed directly from the compact witness before the
/// bound tables are materialised (at `T / 2^8` positions).
pub const DIRECT_ROUNDS: usize = 8;

/// Compact shift witness: per cycle the source word, the amount
/// (`Q_lo`'s hot index) and the kind (`Q_hi`'s hot index), with
/// [`NO_ROUTE`] for an all-zero selector. Equivalent to
/// [`ShiftWitness`] minus `Y` (which the prover never reads).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShiftCompact {
    /// Source word `X(·, j)` (bits at or above `W` are ignored).
    pub src: Vec<u64>,
    /// Amount `h_lo` with `Q_lo(h_lo, j) = 1`, or [`NO_ROUTE`].
    pub amt: Vec<u8>,
    /// Kind `h_hi` with `Q_hi(h_hi, j) = 1`, or [`NO_ROUTE`].
    pub kind: Vec<u8>,
}

impl ShiftCompact {
    /// From per-cycle `(src_word, route)` pairs, as [`shift_witness`].
    pub fn from_cycles(cycles: &[ShiftCycle]) -> Self {
        let byte = |v: usize| u8::try_from(v).expect("route fits a byte");
        ShiftCompact {
            src: cycles.iter().map(|c| c.0).collect(),
            amt: cycles
                .iter()
                .map(|c| c.1.map_or(NO_ROUTE, |r| byte(r.0)))
                .collect(),
            kind: cycles
                .iter()
                .map(|c| c.1.map_or(NO_ROUTE, |r| byte(r.1)))
                .collect(),
        }
    }

    /// From the dense witness tables.
    ///
    /// # Panics
    /// Panics if a selector is not one-hot or all-zero on some cycle.
    pub fn from_witness(wit: &ShiftWitness, wbits: usize) -> Self {
        let w = 1usize << wbits;
        let t = wit.qhi.len() / 8;
        ShiftCompact {
            src: (0..t)
                .map(|j| pack_word(&wit.x[w * j..w * (j + 1)]))
                .collect(),
            amt: (0..t).map(|j| hot(&wit.qlo[w * j..w * (j + 1)])).collect(),
            kind: (0..t).map(|j| hot(&wit.qhi[8 * j..8 * (j + 1)])).collect(),
        }
    }
}

/// Compact store witness: per cycle the old word, the store-source word,
/// the width (`Q_st`'s hot index, or [`NO_ROUTE`]) and the byte offset
/// whose low `wbits − 3` bits are the `a_b` tables. Equivalent to
/// [`StoreWitness`] minus `Inc` (which the prover never reads).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoreCompact {
    /// Old word, `X(u, j)` for `u < W`.
    pub old: Vec<u64>,
    /// Store-source word, `X(W + u, j)`.
    pub src: Vec<u64>,
    /// Width `h` with `Q_st(h, j) = 1`, or [`NO_ROUTE`].
    pub width: Vec<u8>,
    /// Offset: `a_b(j) = (off >> b) & 1`.
    pub off: Vec<u8>,
}

impl StoreCompact {
    /// From per-cycle `(old, src, route)` triples, as [`store_witness`]
    /// (a non-store cycle has offset 0).
    pub fn from_cycles(cycles: &[StoreCycle]) -> Self {
        let byte = |v: usize| u8::try_from(v).expect("route fits a byte");
        StoreCompact {
            old: cycles.iter().map(|c| c.0).collect(),
            src: cycles.iter().map(|c| c.1).collect(),
            width: cycles
                .iter()
                .map(|c| c.2.map_or(NO_ROUTE, |r| byte(r.0)))
                .collect(),
            off: cycles
                .iter()
                .map(|c| c.2.map_or(0, |r| byte(r.1)))
                .collect(),
        }
    }

    /// From the dense witness tables.
    ///
    /// # Panics
    /// Panics if the width selector is not one-hot or all-zero on some
    /// cycle.
    pub fn from_witness(wit: &StoreWitness, wbits: usize) -> Self {
        let w = 1usize << wbits;
        let t = wit.q.len() / 4;
        StoreCompact {
            old: (0..t)
                .map(|j| pack_word(&wit.x[2 * w * j..2 * w * j + w]))
                .collect(),
            src: (0..t)
                .map(|j| pack_word(&wit.x[2 * w * j + w..2 * w * (j + 1)]))
                .collect(),
            width: (0..t).map(|j| hot(&wit.q[4 * j..4 * (j + 1)])).collect(),
            off: (0..t)
                .map(|j| {
                    wit.abits
                        .iter()
                        .enumerate()
                        .map(|(b, tab)| u8::from(tab[j]) << b)
                        .sum()
                })
                .collect(),
        }
    }
}

fn pack_word(bits: &[bool]) -> u64 {
    bits.iter()
        .enumerate()
        .fold(0, |acc, (i, &b)| acc | (u64::from(b) << i))
}

fn hot(bits: &[bool]) -> u8 {
    let mut it = bits.iter().enumerate().filter(|(_, b)| **b).map(|(i, _)| i);
    let h = it.next().map_or(NO_ROUTE, |i| {
        u8::try_from(i).expect("selector index fits a byte")
    });
    assert!(it.next().is_none(), "selector is not one-hot");
    h
}

fn tpt(a: K, b: K, t: K) -> K {
    a + t * (a + b)
}

fn word_mask(wbits: usize) -> u64 {
    if wbits >= 6 {
        u64::MAX
    } else {
        (1u64 << (1usize << wbits)) - 1
    }
}

/// Add `w` to `out[u]` for every set bit `u` of `word`.
fn acc_bits(mut word: u64, w: K, out: &mut [K]) {
    while word != 0 {
        out[word.trailing_zeros() as usize] += w;
        word &= word - 1;
    }
}

/// `eq(r, ·)` as the product of two half tables (C2: low index bits pair
/// with the first coordinates).
struct SplitEq {
    lo: Vec<K>,
    hi: Vec<K>,
    lbits: usize,
}

impl SplitEq {
    fn new(r: &[K]) -> Self {
        let lbits = r.len() / 2;
        SplitEq {
            lo: eq_table(&r[..lbits]),
            hi: eq_table(&r[lbits..]),
            lbits,
        }
    }

    fn get(&self, p: usize) -> K {
        self.lo[p & ((1 << self.lbits) - 1)] * self.hi[p >> self.lbits]
    }
}

/// The per-cycle side of a routing instance: a cycle's features are its
/// non-selector values (`nx`, gathered only for active pairs) followed by
/// its selector values (`ns`), all multilinear in the cycle.
trait CycleInstance: Sync {
    fn nx(&self) -> usize;
    fn ns(&self) -> usize;
    /// `x += w · (non-selector features of cycle j)`.
    fn acc_x(&self, j: usize, w: K, x: &mut [K]);
    /// `s += w · (selector features of cycle j)`.
    fn acc_sel(&self, j: usize, w: K, s: &mut [K]);
    /// Whether a pair with selector halves `s0`, `s1` can contribute.
    fn active(&self, s0: &[K], s1: &[K]) -> bool;
    /// `out[k] += Σ (summand without eq)` at `t_k` for a pair of
    /// positions with features `f0`, `f1` (`ts.len() = out.len()`).
    fn eval_pair(&self, f0: &[K], f1: &[K], ts: &[K], out: &mut [K]);
}

/// The state after the `n` cycle rounds.
struct CycleRounds {
    /// Features at the bound cycle point (`nx + ns` values).
    feats: Vec<K>,
    /// `eq(r_j, s_j)`.
    es: K,
    rs: Vec<K>,
    msgs: Vec<Vec<K>>,
    /// Running claim (`None` if `n = 0`: the claim is not yet fixed).
    cur: Option<K>,
}

fn add_into(acc: &mut [K], v: &[K]) {
    for (a, &b) in acc.iter_mut().zip(v) {
        *a += b;
    }
}

type PairFn<'a> = dyn Fn(usize, &mut [K], &mut [K]) -> bool + Sync + 'a;

/// `Σ_p` of the per-pair evaluations (`f` returns `false` for a pair that
/// contributes nothing). Exact in any order: `K` addition is XOR.
fn sum_pairs(pairs: usize, nf: usize, npts: usize, f: &PairFn<'_>) -> Vec<K> {
    let zero = || vec![K::ZERO; npts];
    (0..pairs)
        .into_par_iter()
        .fold(
            || (zero(), vec![K::ZERO; 2 * nf], zero()),
            |(mut acc, mut buf, mut tmp), p| {
                tmp.fill(K::ZERO);
                if f(p, &mut buf, &mut tmp) {
                    add_into(&mut acc, &tmp);
                }
                (acc, buf, tmp)
            },
        )
        .map(|(acc, _, _)| acc)
        .reduce(zero, |mut a, b| {
            add_into(&mut a, &b);
            a
        })
}

/// Run the `n` cycle rounds of a router sum-check, initialising it at
/// round 0 with the actual table sum, as the dense prover.
#[allow(clippy::too_many_arguments)]
fn cycle_rounds<I: CycleInstance>(
    inst: &I,
    n: usize,
    r_j: &[K],
    degree: usize,
    direct: usize,
    transcript: &mut Transcript,
    label: &[u8],
    m_total: usize,
) -> CycleRounds {
    let (nx, nf) = (inst.nx(), inst.nx() + inst.ns());
    let ts: Vec<K> = (0..=degree).map(|k| K::t(k as u128)).collect();
    let direct = direct.min(n);
    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    let (mut rs, mut msgs, mut cur, mut es) = (Vec::new(), Vec::new(), None, K::ONE);
    let mut feats: Vec<K> = Vec::new();
    for i in 0..n {
        let eqs = SplitEq::new(&r_j[i + 1..]);
        let pairs = 1usize << (n - i - 1);
        let sums = if i < direct {
            let wt = eq_table(&rs);
            let half = 1usize << i;
            sum_pairs(pairs, nf, degree + 1, &|p, buf, tmp| {
                let base = p << (i + 1);
                let (f0, f1) = buf.split_at_mut(nf);
                f0[nx..].fill(K::ZERO);
                f1[nx..].fill(K::ZERO);
                for (b, &wb) in wt.iter().enumerate() {
                    inst.acc_sel(base + b, wb, &mut f0[nx..]);
                    inst.acc_sel(base + half + b, wb, &mut f1[nx..]);
                }
                if !inst.active(&f0[nx..], &f1[nx..]) {
                    return false;
                }
                f0[..nx].fill(K::ZERO);
                f1[..nx].fill(K::ZERO);
                for (b, &wb) in wt.iter().enumerate() {
                    inst.acc_x(base + b, wb, &mut f0[..nx]);
                    inst.acc_x(base + half + b, wb, &mut f1[..nx]);
                }
                inst.eval_pair(f0, f1, &ts, tmp);
                let e = eqs.get(p);
                tmp.iter_mut().for_each(|v| *v *= e);
                true
            })
        } else {
            if i == direct {
                feats = materialize(inst, &eq_table(&rs), direct, n);
            }
            let feats = &feats;
            sum_pairs(pairs, nf, degree + 1, &|p, _, tmp| {
                let f0 = &feats[2 * p * nf..(2 * p + 1) * nf];
                let f1 = &feats[(2 * p + 1) * nf..(2 * p + 2) * nf];
                if !inst.active(&f0[nx..], &f1[nx..]) {
                    return false;
                }
                inst.eval_pair(f0, f1, &ts, tmp);
                let e = eqs.get(p);
                tmp.iter_mut().for_each(|v| *v *= e);
                true
            })
        };
        let ev: Vec<K> = sums
            .iter()
            .zip(&ts)
            .map(|(&s, &t)| es * (K::ONE + r_j[i] + t) * s)
            .collect();
        if i == 0 {
            let claim = ev[0] + ev[1];
            sumcheck_init(transcript, label, claim, m_total, degree);
            cur = Some(claim);
        }
        assert_eq!(
            Some(ev[0] + ev[1]),
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let mut msg = vec![ev[0]];
        msg.extend_from_slice(&ev[2..]);
        transcript.absorb_ks(&msg_label, &msg);
        let r = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(r);
        cur = Some(interpolate_eval(&ev, r));
        es *= K::ONE + r_j[i] + r;
        if i >= direct {
            bind_positions(&mut feats, nf, r);
        }
    }
    if direct == n {
        feats = materialize(inst, &eq_table(&rs), n, n);
    }
    CycleRounds {
        feats,
        es,
        rs,
        msgs,
        cur,
    }
}

/// The bound features at all `2^(n−k)` positions after `k` bound cycle
/// variables with weights `wt = eq_table(s_<k)`.
fn materialize<I: CycleInstance>(inst: &I, wt: &[K], k: usize, n: usize) -> Vec<K> {
    let (nx, nf) = (inst.nx(), inst.nx() + inst.ns());
    let mut feats = vec![K::ZERO; nf << (n - k)];
    feats.par_chunks_mut(nf).enumerate().for_each(|(q, f)| {
        let (x, s) = f.split_at_mut(nx);
        for (b, &wb) in wt.iter().enumerate() {
            inst.acc_x((q << k) + b, wb, x);
            inst.acc_sel((q << k) + b, wb, s);
        }
    });
    feats
}

/// Bind the lowest position variable at `r` in place (position-major
/// layout, `nf` features per position).
fn bind_positions(feats: &mut Vec<K>, nf: usize, r: K) {
    let half = feats.len() / nf / 2;
    for q in 0..half {
        for f in 0..nf {
            feats[q * nf + f] = tpt(feats[2 * q * nf + f], feats[(2 * q + 1) * nf + f], r);
        }
    }
    feats.truncate(half * nf);
}

/// Linear-in-`t` evaluations of `(a, b)` at the points `ts`.
fn lin(a: K, b: K, ts: &[K], out: &mut [K]) {
    for (o, &t) in out.iter_mut().zip(ts) {
        *o = tpt(a, b, t);
    }
}

/// Indices `i` with `s0[i]` or `s1[i]` non-zero, into `buf`; returns the
/// count.
fn nonzero_idx(s0: &[K], s1: &[K], buf: &mut [usize]) -> usize {
    let mut c = 0;
    for (i, (a, b)) in s0.iter().zip(s1).enumerate() {
        if !a.is_zero() || !b.is_zero() {
            buf[c] = i;
            c += 1;
        }
    }
    c
}

fn dot(x: &[K], cols: &[(usize, K)]) -> K {
    cols.iter().fold(K::ZERO, |acc, &(u, c)| acc + x[u] * c)
}

/// Upper bound on the number of evaluation points (`degree + 1 ≤ 7`).
const MAXPTS: usize = 8;

struct ShiftInst<'a> {
    wit: &'a ShiftCompact,
    w: usize,
    mask: u64,
    /// `cols[h]`: the non-zero `(u, R_{r_o}(u, h))`.
    cols: Vec<Vec<(usize, K)>>,
}

impl CycleInstance for ShiftInst<'_> {
    fn nx(&self) -> usize {
        self.w
    }
    fn ns(&self) -> usize {
        self.w + 8
    }
    fn acc_x(&self, j: usize, w: K, x: &mut [K]) {
        acc_bits(self.wit.src[j] & self.mask, w, x);
    }
    fn acc_sel(&self, j: usize, w: K, s: &mut [K]) {
        let (a, k) = (self.wit.amt[j], self.wit.kind[j]);
        if a != NO_ROUTE {
            s[usize::from(a)] += w;
        }
        if k != NO_ROUTE {
            s[self.w + usize::from(k)] += w;
        }
    }
    fn active(&self, s0: &[K], s1: &[K]) -> bool {
        let w = self.w;
        let any =
            |r: std::ops::Range<usize>| r.into_iter().any(|h| !s0[h].is_zero() || !s1[h].is_zero());
        any(0..w) && any(w..w + 8)
    }
    fn eval_pair(&self, f0: &[K], f1: &[K], ts: &[K], out: &mut [K]) {
        let w = self.w;
        let np = ts.len();
        let (x0, s0) = f0.split_at(w);
        let (x1, s1) = f1.split_at(w);
        let (mut lo, mut hi) = ([0usize; 64], [0usize; 8]);
        let nlo = nonzero_idx(&s0[..w], &s1[..w], &mut lo);
        let nhi = nonzero_idx(&s0[w..], &s1[w..], &mut hi);
        let mut qlt = [[K::ZERO; MAXPTS]; 64];
        for &hl in &lo[..nlo] {
            lin(s0[hl], s1[hl], ts, &mut qlt[hl][..np]);
        }
        let (mut qht, mut inner) = ([K::ZERO; MAXPTS], [K::ZERO; MAXPTS]);
        for &hh in &hi[..nhi] {
            lin(s0[w + hh], s1[w + hh], ts, &mut qht[..np]);
            inner[..np].fill(K::ZERO);
            for &hl in &lo[..nlo] {
                let cols = &self.cols[hl + w * hh];
                if cols.is_empty() {
                    continue;
                }
                let (b0, b1) = (dot(x0, cols), dot(x1, cols));
                for k in 0..np {
                    inner[k] += qlt[hl][k] * tpt(b0, b1, ts[k]);
                }
            }
            for k in 0..np {
                out[k] += qht[k] * inner[k];
            }
        }
    }
}

/// Fast shift prover: identical transcript and proof to [`shift_prove`]
/// (Python `shift_prove_fast`), from the dense witness tables.
///
/// # Panics
/// Panics on malformed witness tables (indexing, non-one-hot selectors).
#[allow(clippy::too_many_arguments)]
pub fn shift_prove_fast(
    n: usize,
    wit: &ShiftWitness,
    r_o: &[K],
    r_j: &[K],
    y: K,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
) -> (RouterProof, Vec<EvalClaim>) {
    let compact = ShiftCompact::from_witness(wit, wbits);
    shift_prove_compact(n, &compact, r_o, r_j, y, transcript, label, wbits)
}

/// Fast shift prover on the compact witness: identical transcript and
/// proof to [`shift_prove`], with memory `O(T)` words plus
/// `O(T / 2^DIRECT_ROUNDS)` field elements.
///
/// # Panics
/// Panics if the witness does not have `2^n` cycles.
#[allow(clippy::too_many_arguments)]
pub fn shift_prove_compact(
    n: usize,
    wit: &ShiftCompact,
    r_o: &[K],
    r_j: &[K],
    y: K,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
) -> (RouterProof, Vec<EvalClaim>) {
    shift_prove_compact_with(n, wit, r_o, r_j, y, transcript, label, wbits, DIRECT_ROUNDS)
}

/// [`shift_prove_compact`] with an explicit number of direct cycle
/// rounds (every value gives the same proof; exposed for tests).
#[doc(hidden)]
#[allow(clippy::too_many_arguments)]
pub fn shift_prove_compact_with(
    n: usize,
    wit: &ShiftCompact,
    r_o: &[K],
    r_j: &[K],
    y: K,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
    direct: usize,
) -> (RouterProof, Vec<EvalClaim>) {
    let w = 1usize << wbits;
    let t = 1usize << n;
    assert!(
        wit.src.len() == t && wit.amt.len() == t && wit.kind.len() == t,
        "shift witness must have 2^n cycles"
    );
    absorb_claim(transcript, label, r_o, r_j, y);
    let eo = eq_table(r_o);
    let mut rr = vec![K::ZERO; w * 8 * w]; // flat u + W*h
    for (o, u, h) in shift_entries(wbits) {
        rr[u + w * h] += eo[o];
    }
    let cols = (0..8 * w)
        .map(|h| {
            (0..w)
                .filter(|&u| !rr[u + w * h].is_zero())
                .map(|u| (u, rr[u + w * h]))
                .collect()
        })
        .collect();
    let inst = ShiftInst {
        wit,
        w,
        mask: word_mask(wbits),
        cols,
    };
    let m_total = n + 2 * wbits + 3;
    let sc_label = sublabel(label, b"/sc");
    let cr = cycle_rounds(&inst, n, r_j, 4, direct, transcript, &sc_label, m_total);
    let (x, ql, qh) = (&cr.feats[..w], &cr.feats[w..2 * w], &cr.feats[2 * w..]);
    let nr = w * w * 8;
    let tabs = vec![
        vec![cr.es; nr],
        (0..nr).map(|i| x[i % w]).collect(),
        (0..nr).map(|i| ql[(i / w) % w]).collect(),
        (0..nr).map(|i| qh[i / (w * w)]).collect(),
        rr,
    ];
    let cur = cr.cur.unwrap_or_else(|| {
        let claim = combine_sum(&tabs, &mul5);
        sumcheck_init(transcript, &sc_label, claim, m_total, 4);
        claim
    });
    let (mut rs, mut msgs) = (cr.rs, cr.msgs);
    let fin = dense_rounds(
        tabs,
        &mul5,
        4,
        cur,
        transcript,
        &sc_label,
        m_total - n,
        &mut rs,
        &mut msgs,
    );
    let evs = vec![fin[1][0], fin[2][0], fin[3][0]];
    transcript.absorb_ks(&sublabel(label, b"/evals"), &evs);
    let claims = shift_claims(n, wbits, &rs, &evs);
    (
        RouterProof {
            sc: SumcheckProof { round_msgs: msgs },
            evals: evs,
        },
        claims,
    )
}

struct StoreInst<'a> {
    wit: &'a StoreCompact,
    w: usize,
    na: usize,
    mask: u64,
    /// `cols[a * 4 + h]`: the non-zero `(u, R_{r_o,a}(u, h))`.
    cols: Vec<Vec<(usize, K)>>,
}

impl CycleInstance for StoreInst<'_> {
    fn nx(&self) -> usize {
        2 * self.w + self.na
    }
    fn ns(&self) -> usize {
        4
    }
    fn acc_x(&self, j: usize, w: K, x: &mut [K]) {
        let ww = self.w;
        acc_bits(self.wit.old[j] & self.mask, w, &mut x[..ww]);
        acc_bits(self.wit.src[j] & self.mask, w, &mut x[ww..2 * ww]);
        acc_bits(
            u64::from(self.wit.off[j]) & ((1 << self.na) - 1),
            w,
            &mut x[2 * ww..],
        );
    }
    fn acc_sel(&self, j: usize, w: K, s: &mut [K]) {
        let h = self.wit.width[j];
        if h != NO_ROUTE {
            s[usize::from(h)] += w;
        }
    }
    fn active(&self, s0: &[K], s1: &[K]) -> bool {
        s0.iter().chain(s1).any(|v| !v.is_zero())
    }
    fn eval_pair(&self, f0: &[K], f1: &[K], ts: &[K], out: &mut [K]) {
        let (w2, na) = (2 * self.w, self.na);
        let np = ts.len();
        let (x0, ab0, s0) = (&f0[..w2], &f0[w2..w2 + na], &f0[w2 + na..]);
        let (x1, ab1, s1) = (&f1[..w2], &f1[w2..w2 + na], &f1[w2 + na..]);
        // la[a][k] = Π_b (1 + ã_b(t_k) + a_b)
        let mut la = [[K::ONE; MAXPTS]; 8];
        let mut abt = [K::ZERO; MAXPTS];
        for b in 0..na {
            lin(ab0[b], ab1[b], ts, &mut abt[..np]);
            for (a, la_a) in la.iter_mut().enumerate().take(1 << na) {
                let bit = K::from_bit((a >> b) & 1 == 1);
                for k in 0..np {
                    la_a[k] *= K::ONE + abt[k] + bit;
                }
            }
        }
        let mut hs = [0usize; 4];
        let nh = nonzero_idx(s0, s1, &mut hs);
        let (mut qt, mut inner) = ([K::ZERO; MAXPTS], [K::ZERO; MAXPTS]);
        for &h in &hs[..nh] {
            lin(s0[h], s1[h], ts, &mut qt[..np]);
            inner[..np].fill(K::ZERO);
            for (a, la_a) in la.iter().enumerate().take(1 << na) {
                let cols = &self.cols[a * 4 + h];
                if cols.is_empty() {
                    continue;
                }
                let (b0, b1) = (dot(x0, cols), dot(x1, cols));
                for k in 0..np {
                    inner[k] += la_a[k] * tpt(b0, b1, ts[k]);
                }
            }
            for k in 0..np {
                out[k] += qt[k] * inner[k];
            }
        }
    }
}

/// Fast store prover: identical transcript and proof to [`store_prove`]
/// (Python `store_prove_fast`), from the dense witness tables.
///
/// # Panics
/// Panics on malformed witness tables (indexing, non-one-hot selectors).
#[allow(clippy::too_many_arguments)]
pub fn store_prove_fast(
    n: usize,
    wit: &StoreWitness,
    r_o: &[K],
    r_j: &[K],
    y: K,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
) -> (RouterProof, Vec<EvalClaim>) {
    let compact = StoreCompact::from_witness(wit, wbits);
    store_prove_compact(n, &compact, r_o, r_j, y, transcript, label, wbits)
}

/// Fast store prover on the compact witness: identical transcript and
/// proof to [`store_prove`], with memory `O(T)` words plus
/// `O(T / 2^DIRECT_ROUNDS)` field elements.
///
/// # Panics
/// Panics if the witness does not have `2^n` cycles.
#[allow(clippy::too_many_arguments)]
pub fn store_prove_compact(
    n: usize,
    wit: &StoreCompact,
    r_o: &[K],
    r_j: &[K],
    y: K,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
) -> (RouterProof, Vec<EvalClaim>) {
    store_prove_compact_with(n, wit, r_o, r_j, y, transcript, label, wbits, DIRECT_ROUNDS)
}

/// [`store_prove_compact`] with an explicit number of direct cycle
/// rounds (every value gives the same proof; exposed for tests).
#[doc(hidden)]
#[allow(clippy::too_many_arguments)]
pub fn store_prove_compact_with(
    n: usize,
    wit: &StoreCompact,
    r_o: &[K],
    r_j: &[K],
    y: K,
    transcript: &mut Transcript,
    label: &[u8],
    wbits: usize,
    direct: usize,
) -> (RouterProof, Vec<EvalClaim>) {
    let (t, w, na) = (1usize << n, 1usize << wbits, wbits - 3);
    let na_count = 1usize << na;
    assert!(
        wit.old.len() == t && wit.src.len() == t && wit.width.len() == t && wit.off.len() == t,
        "store witness must have 2^n cycles"
    );
    absorb_claim(transcript, label, r_o, r_j, y);
    let eo = eq_table(r_o);
    let mut ra = vec![vec![K::ZERO; 2 * w * 4]; na_count]; // flat u + 2W*h per offset a
    for (o, u, h, a) in store_entries(wbits) {
        ra[a][u + 2 * w * h] += eo[o];
    }
    let mut cols = Vec::with_capacity(4 * na_count);
    for r in &ra {
        for h in 0..4 {
            cols.push(
                (0..2 * w)
                    .filter(|&u| !r[u + 2 * w * h].is_zero())
                    .map(|u| (u, r[u + 2 * w * h]))
                    .collect(),
            );
        }
    }
    let inst = StoreInst {
        wit,
        w,
        na,
        mask: word_mask(wbits),
        cols,
    };
    let degree = 3 + na;
    let m_total = n + wbits + 1 + 2;
    let sc_label = sublabel(label, b"/sc");
    let cr = cycle_rounds(
        &inst, n, r_j, degree, direct, transcript, &sc_label, m_total,
    );
    let (x, ab, q) = (
        &cr.feats[..2 * w],
        &cr.feats[2 * w..2 * w + na],
        &cr.feats[2 * w + na..],
    );
    let nr = 2 * w * 4;
    let mut tabs: Vec<Vec<K>> = vec![
        vec![cr.es; nr],
        (0..nr).map(|i| x[i % (2 * w)]).collect(),
        (0..nr).map(|i| q[i / (2 * w)]).collect(),
    ];
    tabs.extend(ab.iter().map(|&v| vec![v; nr]));
    tabs.extend(ra);
    let f = store_combine(na);
    let cur = cr.cur.unwrap_or_else(|| {
        let claim = combine_sum(&tabs, &f);
        sumcheck_init(transcript, &sc_label, claim, m_total, degree);
        claim
    });
    let (mut rs, mut msgs) = (cr.rs, cr.msgs);
    let fin = dense_rounds(
        tabs,
        &f,
        degree,
        cur,
        transcript,
        &sc_label,
        m_total - n,
        &mut rs,
        &mut msgs,
    );
    let mut evs = vec![fin[1][0], fin[2][0]];
    evs.extend((0..na).map(|b| fin[3 + b][0]));
    transcript.absorb_ks(&sublabel(label, b"/evals"), &evs);
    let claims = store_claims(n, wbits, &rs, &evs);
    (
        RouterProof {
            sc: SumcheckProof { round_msgs: msgs },
            evals: evs,
        },
        claims,
    )
}

/// Continue a sum-check (already initialised) for `nrounds` rounds on
/// dense tables, appending to `rs`/`msgs`; returns the bound tables.
#[allow(clippy::too_many_arguments)]
fn dense_rounds(
    mut tabs: Vec<Vec<K>>,
    combine: &(dyn Fn(&[K]) -> K + Sync),
    degree: usize,
    mut cur: K,
    transcript: &mut Transcript,
    label: &[u8],
    nrounds: usize,
    rs: &mut Vec<K>,
    msgs: &mut Vec<Vec<K>>,
) -> Vec<Vec<K>> {
    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    for _ in 0..nrounds {
        let ev = sumcheck_round_evals(&tabs, combine, degree);
        assert_eq!(
            ev[0] + ev[1],
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let mut msg = vec![ev[0]];
        msg.extend_from_slice(&ev[2..]);
        transcript.absorb_ks(&msg_label, &msg);
        let r = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(r);
        cur = interpolate_eval(&ev, r);
        for tab in &mut tabs {
            bind_low_in_place(tab, r);
        }
    }
    tabs
}
