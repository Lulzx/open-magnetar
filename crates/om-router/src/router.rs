//! BinaryRouter (docs/spec/08-router.md): shift and sub-word store
//! instances. Mirrors `reference/openmagnetar/router.py` byte for byte in
//! its transcript interaction.
//!
//! `wbits` is log2 of the word width `W`. The specification fixes
//! `wbits = 6` (`W = 64`); smaller values exist only to keep tests fast.
//! For stores the offset has `wbits - 3` bits (3 for `W = 64`).

use std::collections::HashMap;

use om_field::K;
use om_memcheck::onehot::EvalClaim;
use om_sumcheck::{
    SumcheckProof, VerificationError, bind_low, eq_eval, eq_table, interpolate_eval, sumcheck_init,
    sumcheck_prove, sumcheck_verify,
};
use om_transcript::Transcript;

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
    let mut claim = K::ZERO;
    for i in 0..tabs[0].len() {
        let vals: Vec<K> = tabs.iter().map(|tab| tab[i]).collect();
        claim += mul5(&vals);
    }
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
    let mut claim = K::ZERO;
    for i in 0..tabs[0].len() {
        let vals: Vec<K> = tabs.iter().map(|tab| tab[i]).collect();
        claim += f(&vals);
    }
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
// Same transcript and proof as shift_prove / store_prove, but the first n
// rounds (cycle variables) exploit that Q is sparse per cycle. Informative
// only; the spec is the dense definition (spec 08, Integration notes).

fn tpt(a: K, b: K, t: K) -> K {
    a + t * (a + b)
}

fn bind_table(table: &[K], r: K) -> Vec<K> {
    (0..table.len() / 2)
        .map(|i| tpt(table[2 * i], table[2 * i + 1], r))
        .collect()
}

/// Continue a sum-check (already initialised) for `nrounds` rounds on
/// dense tables, appending to `rs`/`msgs`; returns the bound tables.
#[allow(clippy::too_many_arguments)]
fn dense_rounds(
    mut tabs: Vec<Vec<K>>,
    combine: &dyn Fn(&[K]) -> K,
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
        let half = tabs[0].len() / 2;
        let mut ev = Vec::with_capacity(degree + 1);
        for k in 0..=degree {
            let t = K::t(k as u128);
            let mut acc = K::ZERO;
            for i in 0..half {
                let vals: Vec<K> = tabs
                    .iter()
                    .map(|tab| tab[2 * i] + t * (tab[2 * i] + tab[2 * i + 1]))
                    .collect();
                acc += combine(&vals);
            }
            ev.push(acc);
        }
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
        tabs = tabs.iter().map(|tab| bind_low(tab, r)).collect();
    }
    tabs
}

/// Run the `n` cycle rounds over a sparse state. `evals_fn(state)` gives
/// `[g(t_0)..g(t_degree)]` (full, incl. `t_1`); the sum-check claim is
/// `g(0) + g(1)` of the first round, bound by [`sumcheck_init`] exactly
/// as the dense prover's table sum (Python `_sparse_phase`).
#[allow(clippy::too_many_arguments)]
fn sparse_phase<State, EvalsFn, BindFn>(
    n: usize,
    mut state: State,
    evals_fn: EvalsFn,
    bind_fn: BindFn,
    degree: usize,
    transcript: &mut Transcript,
    label: &[u8],
    m_total: usize,
) -> (State, Vec<K>, Vec<Vec<K>>, K)
where
    EvalsFn: Fn(&State) -> Vec<K>,
    BindFn: Fn(State, K) -> State,
{
    let mut ev = evals_fn(&state);
    let claim = ev[0] + ev[1];
    sumcheck_init(transcript, label, claim, m_total, degree);
    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    let (mut rs, mut msgs, mut cur) = (Vec::new(), Vec::new(), claim);
    for i in 0..n {
        if i > 0 {
            ev = evals_fn(&state);
        }
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
        state = bind_fn(state, r);
    }
    (state, rs, msgs, cur)
}

struct ShiftFastState {
    eq: Vec<K>,
    x: Vec<Vec<K>>,  // per source u, over cycles
    ql: Vec<Vec<K>>, // per amount, over cycles
    qh: Vec<Vec<K>>, // per kind, over cycles
}

/// Fast shift prover: identical transcript and proof to [`shift_prove`]
/// (Python `shift_prove_fast`).
///
/// # Panics
/// Panics on malformed witness tables (indexing), as Python raises.
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
    let (t, w) = (1usize << n, 1usize << wbits);
    absorb_claim(transcript, label, r_o, r_j, y);
    let eo = eq_table(r_o);
    let mut rh: HashMap<usize, HashMap<usize, K>> = HashMap::new();
    let mut rr = vec![K::ZERO; w * 8 * w];
    for (o, u, h) in shift_entries(wbits) {
        let d = rh.entry(h).or_default();
        *d.entry(u).or_insert(K::ZERO) += eo[o];
        rr[u + w * h] += eo[o];
    }
    let wit_x = bits_to_k(&wit.x);
    let wit_qlo = bits_to_k(&wit.qlo);
    let wit_qhi = bits_to_k(&wit.qhi);
    let st = ShiftFastState {
        eq: eq_table(r_j),
        x: (0..w)
            .map(|u| (0..t).map(|j| wit_x[u + w * j]).collect())
            .collect(),
        ql: (0..w)
            .map(|h| (0..t).map(|j| wit_qlo[h + w * j]).collect())
            .collect(),
        qh: (0..8)
            .map(|h| (0..t).map(|j| wit_qhi[h + 8 * j]).collect())
            .collect(),
    };
    let ts: Vec<K> = (0..5).map(|k| K::t(k as u128)).collect();
    let evals_fn = |s: &ShiftFastState| -> Vec<K> {
        let half = s.eq.len() / 2;
        let mut out = vec![K::ZERO; 5];
        for p in 0..half {
            let (e0, e1) = (s.eq[2 * p], s.eq[2 * p + 1]);
            let lo: Vec<usize> = (0..w)
                .filter(|&h| !s.ql[h][2 * p].is_zero() || !s.ql[h][2 * p + 1].is_zero())
                .collect();
            let hi: Vec<usize> = (0..8)
                .filter(|&h| !s.qh[h][2 * p].is_zero() || !s.qh[h][2 * p + 1].is_zero())
                .collect();
            if lo.is_empty() || hi.is_empty() {
                continue;
            }
            for (k, out_k) in out.iter_mut().enumerate() {
                let tt = ts[k];
                let et = tpt(e0, e1, tt);
                let xt: Vec<K> = (0..w)
                    .map(|u| tpt(s.x[u][2 * p], s.x[u][2 * p + 1], tt))
                    .collect();
                let mut acc = K::ZERO;
                for &hh in &hi {
                    let qh = tpt(s.qh[hh][2 * p], s.qh[hh][2 * p + 1], tt);
                    if qh.is_zero() {
                        continue;
                    }
                    let mut inner = K::ZERO;
                    for &hl in &lo {
                        let ql = tpt(s.ql[hl][2 * p], s.ql[hl][2 * p + 1], tt);
                        if ql.is_zero() {
                            continue;
                        }
                        let mut b = K::ZERO;
                        if let Some(d) = rh.get(&(hl + w * hh)) {
                            for (&u, &c) in d {
                                b += xt[u] * c;
                            }
                        }
                        inner += ql * b;
                    }
                    acc += qh * inner;
                }
                *out_k += et * acc;
            }
        }
        out
    };
    let bind_fn = |s: ShiftFastState, r: K| ShiftFastState {
        eq: bind_table(&s.eq, r),
        x: s.x.iter().map(|a| bind_table(a, r)).collect(),
        ql: s.ql.iter().map(|a| bind_table(a, r)).collect(),
        qh: s.qh.iter().map(|a| bind_table(a, r)).collect(),
    };
    let m_total = n + 2 * wbits + 3;
    let sc_label = sublabel(label, b"/sc");
    let (st, mut rs, mut msgs, cur) =
        sparse_phase(n, st, evals_fn, bind_fn, 4, transcript, &sc_label, m_total);
    let e = st.eq[0];
    let nr = w * w * 8;
    let tabs = vec![
        vec![e; nr],
        (0..nr).map(|i| st.x[i % w][0]).collect(),
        (0..nr).map(|i| st.ql[(i / w) % w][0]).collect(),
        (0..nr).map(|i| st.qh[i / (w * w)][0]).collect(),
        rr,
    ];
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
    let mles: Vec<K> = fin.iter().map(|tab| tab[0]).collect();
    let evs = vec![mles[1], mles[2], mles[3]];
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

struct StoreFastState {
    eq: Vec<K>,
    x: Vec<Vec<K>>,  // per source u, over cycles
    q: Vec<Vec<K>>,  // per width, over cycles
    ab: Vec<Vec<K>>, // per offset bit, over cycles
}

/// Fast store prover: identical transcript and proof to [`store_prove`]
/// (Python `store_prove_fast`).
///
/// # Panics
/// Panics on malformed witness tables (indexing), as Python raises.
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
    let (t, w, na) = (1usize << n, 1usize << wbits, wbits - 3);
    let na_count = 1usize << na;
    absorb_claim(transcript, label, r_o, r_j, y);
    let eo = eq_table(r_o);
    let mut rah: HashMap<(usize, usize), HashMap<usize, K>> = HashMap::new();
    let mut ra = vec![vec![K::ZERO; 2 * w * 4]; na_count];
    for (o, u, h, a) in store_entries(wbits) {
        let d = rah.entry((a, h)).or_default();
        *d.entry(u).or_insert(K::ZERO) += eo[o];
        ra[a][u + 2 * w * h] += eo[o];
    }
    let wit_x = bits_to_k(&wit.x);
    let wit_q = bits_to_k(&wit.q);
    let wit_ab: Vec<Vec<K>> = wit.abits.iter().map(|tab| bits_to_k(tab)).collect();
    let st = StoreFastState {
        eq: eq_table(r_j),
        x: (0..2 * w)
            .map(|u| (0..t).map(|j| wit_x[u + 2 * w * j]).collect())
            .collect(),
        q: (0..4)
            .map(|h| (0..t).map(|j| wit_q[h + 4 * j]).collect())
            .collect(),
        ab: (0..na)
            .map(|b| (0..t).map(|j| wit_ab[b][j]).collect())
            .collect(),
    };
    let degree = 3 + na;
    let ts: Vec<K> = (0..=degree).map(|k| K::t(k as u128)).collect();
    let evals_fn = |s: &StoreFastState| -> Vec<K> {
        let half = s.eq.len() / 2;
        let mut out = vec![K::ZERO; degree + 1];
        for p in 0..half {
            let hs: Vec<usize> = (0..4)
                .filter(|&h| !s.q[h][2 * p].is_zero() || !s.q[h][2 * p + 1].is_zero())
                .collect();
            if hs.is_empty() {
                continue;
            }
            for (k, out_k) in out.iter_mut().enumerate() {
                let tt = ts[k];
                let et = tpt(s.eq[2 * p], s.eq[2 * p + 1], tt);
                let xt: Vec<K> = (0..2 * w)
                    .map(|u| tpt(s.x[u][2 * p], s.x[u][2 * p + 1], tt))
                    .collect();
                let abt: Vec<K> = (0..na)
                    .map(|b| tpt(s.ab[b][2 * p], s.ab[b][2 * p + 1], tt))
                    .collect();
                let la: Vec<K> = (0..na_count)
                    .map(|a| {
                        let mut v = K::ONE;
                        for (b, &abt_b) in abt.iter().enumerate() {
                            v *= K::ONE + abt_b + K::from_bit((a >> b) & 1 == 1);
                        }
                        v
                    })
                    .collect();
                let mut acc = K::ZERO;
                for &h in &hs {
                    let qh = tpt(s.q[h][2 * p], s.q[h][2 * p + 1], tt);
                    if qh.is_zero() {
                        continue;
                    }
                    let mut inner = K::ZERO;
                    for (a, &la_a) in la.iter().enumerate() {
                        if la_a.is_zero() {
                            continue;
                        }
                        let mut b_acc = K::ZERO;
                        if let Some(d) = rah.get(&(a, h)) {
                            for (&u, &c) in d {
                                b_acc += xt[u] * c;
                            }
                        }
                        inner += la_a * b_acc;
                    }
                    acc += qh * inner;
                }
                *out_k += et * acc;
            }
        }
        out
    };
    let bind_fn = |s: StoreFastState, r: K| StoreFastState {
        eq: bind_table(&s.eq, r),
        x: s.x.iter().map(|a| bind_table(a, r)).collect(),
        q: s.q.iter().map(|a| bind_table(a, r)).collect(),
        ab: s.ab.iter().map(|a| bind_table(a, r)).collect(),
    };
    let m_total = n + wbits + 1 + 2;
    let sc_label = sublabel(label, b"/sc");
    let (st, mut rs, mut msgs, cur) = sparse_phase(
        n, st, evals_fn, bind_fn, degree, transcript, &sc_label, m_total,
    );
    let nr = 2 * w * 4;
    let mut tabs: Vec<Vec<K>> = vec![
        vec![st.eq[0]; nr],
        (0..nr).map(|i| st.x[i % (2 * w)][0]).collect(),
        (0..nr).map(|i| st.q[i / (2 * w)][0]).collect(),
    ];
    tabs.extend((0..na).map(|b| vec![st.ab[b][0]; nr]));
    tabs.extend(ra);
    let fin = dense_rounds(
        tabs,
        &store_combine(na),
        degree,
        cur,
        transcript,
        &sc_label,
        m_total - n,
        &mut rs,
        &mut msgs,
    );
    let mles: Vec<K> = fin.iter().map(|tab| tab[0]).collect();
    let mut evs = vec![mles[1], mles[2]];
    evs.extend((0..na).map(|b| mles[3 + b]));
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
