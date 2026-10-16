//! BinaryShout (spec 07 §7.4). Mirrors `reference/openmagnetar/shout.py`
//! byte for byte in its transcript interaction.

use om_field::K;
use om_sumcheck::{
    SumcheckProof, VerificationError, combine_sum, mle_eval, sumcheck_prove, sumcheck_verify,
};
use om_transcript::{Transcript, u64le};
use rayon::prelude::*;

use crate::onehot::PAR_THRESHOLD;
use crate::onehot::{
    AddrComps, EvalClaim, OneHotProof, VirtGroup, VirtProof, VirtTerm, onehot_prove, onehot_verify,
    virt_prove, virt_verify,
};
use crate::sublabel;

/// Parameters of one BinaryShout instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShoutParams {
    pub name: String,
    /// Table has `2^a` rows.
    pub a: usize,
    /// Number of address components, `d | a`.
    pub d: usize,
    /// `T = 2^n` cycles.
    pub n: usize,
}

/// One claim group: all claims at one cycle point `r_c`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShoutClaims {
    /// Cycle point, `K^n`.
    pub r_c: Vec<K>,
    /// Indices of the table columns claimed (increasing).
    pub cols: Vec<usize>,
    /// `rv_h~(r_c)` for `h` in `cols`.
    pub rv: Vec<K>,
    /// `f_t~(r_c)`, `t = 0..a-1` (`t = 0` is the LSB), or `None`.
    pub bits: Option<Vec<K>>,
}

/// Proof of one BinaryShout instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShoutProof {
    pub read: SumcheckProof,
    pub ra_evals: Vec<K>,
    pub virt: Option<VirtProof>,
    pub onehot: OneHotProof,
}

/// The component polynomial names `{name}/ra/{i}`, `i` 1-based.
pub fn comp_names(params: &ShoutParams) -> Vec<String> {
    (0..params.d)
        .map(|i| format!("{}/ra/{}", params.name, i + 1))
        .collect()
}

/// `ra~(k, r_c)` for all Boolean `k` (length `2^a`): a histogram of
/// the addresses weighted by `eq(r_c, j)` (§7.10), `O(T + 2^a)`.
fn ra_at(params: &ShoutParams, comps: &AddrComps, r_c: &[K]) -> Vec<K> {
    comps.ra_at(params.a, r_c)
}

/// The honest claim group at cycle point `r_c` for the given table and
/// address components. `cols = None` claims every column.
pub fn shout_honest_claims(
    params: &ShoutParams,
    table: &[Vec<K>],
    comps: &AddrComps,
    r_c: &[K],
    cols: Option<&[usize]>,
    with_bits: bool,
) -> ShoutClaims {
    let cols: Vec<usize> = match cols {
        None => (0..table.len()).collect(),
        Some(c) => c.to_vec(),
    };
    let ra = ra_at(params, comps, r_c);
    let mut rv = Vec::with_capacity(cols.len());
    for &h in &cols {
        let mut acc = K::ZERO;
        for (k, &v) in ra.iter().enumerate() {
            acc += v * table[h][k];
        }
        rv.push(acc);
    }
    let bits = if with_bits {
        let mut bits = Vec::with_capacity(params.a);
        for t in 0..params.a {
            let mut acc = K::ZERO;
            for (k, &v) in ra.iter().enumerate() {
                if (k >> t) & 1 == 1 {
                    acc += v;
                }
            }
            bits.push(acc);
        }
        Some(bits)
    } else {
        None
    };
    ShoutClaims {
        r_c: r_c.to_vec(),
        cols,
        rv,
        bits,
    }
}

fn phi_table(
    alpha0: K,
    alphas: Option<&[K]>,
    gammas: &[K],
    table: &[Vec<K>],
    cols: &[usize],
    a: usize,
) -> Vec<K> {
    let nk = 1usize << a;
    let base = |k: usize| {
        let mut v = alpha0;
        if let Some(alphas) = alphas {
            for (t, &al) in alphas.iter().enumerate().take(a) {
                if (k >> t) & 1 == 1 {
                    v += al;
                }
            }
        }
        v
    };
    let mut out: Vec<K> = if nk >= PAR_THRESHOLD {
        (0..nk).into_par_iter().map(base).collect()
    } else {
        (0..nk).map(base).collect()
    };
    for (&g, &h) in gammas.iter().zip(cols) {
        if nk >= PAR_THRESHOLD {
            out.par_iter_mut()
                .zip(&table[h])
                .for_each(|(v, &tv)| *v += g * tv);
        } else {
            for (v, &tv) in out.iter_mut().zip(&table[h]) {
                *v += g * tv;
            }
        }
    }
    out
}

fn absorb(tr: &mut Transcript, label: &[u8], groups: &[ShoutClaims]) {
    tr.absorb_bytes(&sublabel(label, b"/ngroups"), &u64le(groups.len() as u64));
    for g in groups {
        tr.absorb_ks(&sublabel(label, b"/point"), &g.r_c);
        let mut cols_bytes = Vec::with_capacity(8 * g.cols.len() + 1);
        for &h in &g.cols {
            cols_bytes.extend_from_slice(&u64le(h as u64));
        }
        cols_bytes.push(if g.bits.is_some() { 0x01 } else { 0x00 });
        tr.absorb_bytes(&sublabel(label, b"/cols"), &cols_bytes);
        tr.absorb_ks(&sublabel(label, b"/rv"), &g.rv);
        if let Some(bits) = &g.bits {
            tr.absorb_ks(&sublabel(label, b"/bits"), bits);
        }
    }
}

/// Per group `(α_{g,0}, α_{g,1..a} or None, γ_g)`, then `β`.
type GroupCoeffs = (K, Option<Vec<K>>, Vec<K>);

fn coeffs(
    tr: &mut Transcript,
    label: &[u8],
    a: usize,
    groups: &[ShoutClaims],
) -> (Vec<GroupCoeffs>, Vec<K>) {
    let mut out = Vec::with_capacity(groups.len());
    for g in groups {
        let alpha0 = tr.challenge_nonzero_k(&sublabel(label, b"/alpha0"));
        let alphas = if g.bits.is_some() {
            Some(tr.challenge_ks(&sublabel(label, b"/alpha"), a))
        } else {
            None
        };
        let gammas = tr.challenge_ks(&sublabel(label, b"/gamma"), g.cols.len());
        out.push((alpha0, alphas, gammas));
    }
    let beta = tr.challenge_ks(&sublabel(label, b"/beta"), groups.len());
    (out, beta)
}

/// The verifier's per-group claim `alpha0 + Σ α f + Σ γ rv`.
fn group_claim(g: &ShoutClaims, co: &GroupCoeffs) -> K {
    let (alpha0, alphas, gammas) = co;
    let mut c = *alpha0;
    if let (Some(alphas), Some(bits)) = (alphas, &g.bits) {
        for (&al, &f) in alphas.iter().zip(bits) {
            c += al * f;
        }
    }
    for (&ga, &v) in gammas.iter().zip(&g.rv) {
        c += ga * v;
    }
    c
}

/// Prove one BinaryShout instance (spec 07 §7.4). `table` is the public
/// table: `c` columns of `2^a` field elements. Returns the proof and
/// the output claims (virtualization claims, then one-hot claims).
pub fn shout_prove(
    params: &ShoutParams,
    table: &[Vec<K>],
    comps: &AddrComps,
    groups: &[ShoutClaims],
    transcript: &mut Transcript,
    label: &[u8],
) -> (ShoutProof, Vec<EvalClaim>) {
    let (a, d, n) = (params.a, params.d, params.n);
    absorb(transcript, label, groups);
    let (cos, beta) = coeffs(transcript, label, a, groups);
    let ra_rs: Vec<Vec<K>> = groups
        .iter()
        .map(|g| ra_at(params, comps, &g.r_c))
        .collect();
    let phis: Vec<Vec<K>> = groups
        .iter()
        .zip(&cos)
        .map(|(g, co)| phi_table(co.0, co.1.as_deref(), &co.2, table, &g.cols, a))
        .collect();
    let g_count = groups.len();
    let combine = {
        let beta = beta.clone();
        move |v: &[K]| {
            let mut acc = K::ZERO;
            for g in 0..g_count {
                acc += beta[g] * v[g] * v[g_count + g];
            }
            acc
        }
    };
    let mut tables = ra_rs;
    tables.extend(phis);
    // The honest prover sums its actual tables (not the claimed value).
    let claim = combine_sum(&tables, &combine);
    let (sc, r_k, mles) = sumcheck_prove(
        claim,
        tables,
        &combine,
        2,
        transcript,
        &sublabel(label, b"/read"),
    );
    let ra_evals = mles[..groups.len()].to_vec();
    transcript.absorb_ks(&sublabel(label, b"/ra_evals"), &ra_evals);
    let names = comp_names(params);
    let grp = VirtGroup {
        names: names.clone(),
        r_k,
        terms: groups
            .iter()
            .zip(&ra_evals)
            .map(|(g, &v)| VirtTerm {
                cyc: g.r_c.clone(),
                value: v,
            })
            .collect(),
    };
    let (vproof, mut claims) = virt_prove(
        &[grp],
        &[comps],
        a,
        d,
        n,
        transcript,
        &sublabel(label, b"/virt"),
    );
    let (oproof, oclaims) = onehot_prove(
        &[comps],
        &names,
        a / d,
        n,
        transcript,
        &sublabel(label, b"/onehot"),
    );
    claims.extend(oclaims);
    (
        ShoutProof {
            read: sc,
            ra_evals,
            virt: vproof,
            onehot: oproof,
        },
        claims,
    )
}

/// Verify one BinaryShout instance, returning the output claims.
/// `table` is the public table: `c` columns of `2^a` field elements.
///
/// # Errors
/// Returns [`VerificationError`] on malformed claims or proof or any
/// failing check.
pub fn shout_verify(
    params: &ShoutParams,
    table: &[Vec<K>],
    groups: &[ShoutClaims],
    proof: &ShoutProof,
    transcript: &mut Transcript,
    label: &[u8],
) -> Result<Vec<EvalClaim>, VerificationError> {
    let (a, d, n) = (params.a, params.d, params.n);
    for g in groups {
        if g.r_c.len() != n
            || g.rv.len() != g.cols.len()
            || g.bits.as_ref().is_some_and(|b| b.len() != a)
            || g.cols.iter().any(|&h| h >= table.len())
        {
            return Err(VerificationError::new("shout: malformed claims"));
        }
    }
    if proof.ra_evals.len() != groups.len() {
        return Err(VerificationError::new("shout: malformed proof"));
    }
    absorb(transcript, label, groups);
    let (cos, beta) = coeffs(transcript, label, a, groups);
    let mut claim = K::ZERO;
    for ((&b, g), co) in beta.iter().zip(groups).zip(&cos) {
        claim += b * group_claim(g, co);
    }
    let (r_k, expected) = sumcheck_verify(
        claim,
        a,
        2,
        &proof.read,
        transcript,
        &sublabel(label, b"/read"),
    )?;
    let mut val = K::ZERO;
    for (((&b, g), co), &ra) in beta.iter().zip(groups).zip(&cos).zip(&proof.ra_evals) {
        let (alpha0, alphas, gammas) = co;
        let mut phi = *alpha0;
        if let Some(alphas) = alphas {
            for (&al, &x) in alphas.iter().zip(&r_k) {
                phi += al * x;
            }
        }
        for (&ga, &h) in gammas.iter().zip(&g.cols) {
            phi += ga * mle_eval(&table[h], &r_k);
        }
        val += b * ra * phi;
    }
    if val != expected {
        return Err(VerificationError::new("shout: read check failed"));
    }
    transcript.absorb_ks(&sublabel(label, b"/ra_evals"), &proof.ra_evals);
    let names = comp_names(params);
    let grp = VirtGroup {
        names: names.clone(),
        r_k,
        terms: groups
            .iter()
            .zip(&proof.ra_evals)
            .map(|(g, &v)| VirtTerm {
                cyc: g.r_c.clone(),
                value: v,
            })
            .collect(),
    };
    let mut claims = virt_verify(
        &[grp],
        a,
        d,
        n,
        proof.virt.as_ref(),
        transcript,
        &sublabel(label, b"/virt"),
    )?;
    let oclaims = onehot_verify(
        &names,
        a / d,
        n,
        &proof.onehot,
        transcript,
        &sublabel(label, b"/onehot"),
    )?;
    claims.extend(oclaims);
    Ok(claims)
}
