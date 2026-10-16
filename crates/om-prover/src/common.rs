//! Helpers shared by prover and verifier (Python `protocol.py`'s
//! "shared helpers"): statement absorption, commitment absorption, the
//! transparent-mock root, `M_0` construction/evaluation, Spartan-claim
//! splitting, the bytecode Shout plan (§11.7) and Mosaic claim
//! assembly. `om-verifier` reuses this module unchanged.

use std::collections::BTreeMap;

use om_circuit::circuit as cpu;
use om_elf::{AbiError, build_m0};
use om_field::K;
use om_format::{PcsMode, PublicInstance, VerifyingKey};
use om_memcheck::onehot::{EvalClaim, bits_of};
use om_memcheck::shout::{ShoutClaims, ShoutParams};
use om_memcheck::twist::TwistOutput;
use om_mosaic::Claim;
use om_pcs::pcs::{BitPCS, Commitment};
use om_spartan::SegmentKind;
use om_sumcheck::{PackedBits, VerificationError, eq_eval, eq_table};
use om_transcript::{Transcript, u64le};

use crate::keygen::{Derived, Instance, REG_A};

/// Protocol transcript label (`protocol.LABEL`, §11.3).
pub const LABEL: &[u8] = b"openmagnetar/zkvm/v1";
/// Register-index Shout columns, in order (`protocol.REG_IDX_COLS`).
pub const REG_IDX_COLS: [&str; 3] = ["rs1", "rs2", "rd"];

/// Absorb the statement in §11.3 order (vk digest FIRST).
pub fn absorb_statement(tr: &mut Transcript, vk: &VerifyingKey, inst: &PublicInstance) {
    tr.absorb_bytes(b"vk/digest", &vk.digest());
    tr.absorb_bytes(b"stmt/T", &u64le(inst.t));
    tr.absorb_bytes(b"stmt/input", &inst.input);
    tr.absorb_bytes(b"stmt/output", &inst.output);
    tr.absorb_bytes(b"stmt/exit", &u64le(inst.exit_code));
}

/// A transcript initialized with [`LABEL`] and `vk`'s hasher, with the
/// statement absorbed (§11.3, step 1's first half).
pub fn transcript_with_statement(vk: &VerifyingKey, inst: &PublicInstance) -> Transcript {
    let mut tr = Transcript::new(LABEL, vk.hasher());
    absorb_statement(&mut tr, vk, inst);
    tr
}

/// Verifier-side commitment absorption (Python `_absorb_commitment`):
/// transparent mock absorbs `b"transparent"` and the root; Ligerito
/// builds the `BitPCS` and absorbs its setup, returning it.
///
/// # Errors
/// Returns [`VerificationError`] if the Ligerito parameters cannot be
/// derived for `inst.ell` (Python raises `KeyError_`, a rejection).
pub fn absorb_commitment(
    vk: &VerifyingKey,
    derived: &Derived,
    inst: &Instance,
    root: &[u8],
    tr: &mut Transcript,
) -> Result<Option<BitPCS>, VerificationError> {
    if vk.pcs == PcsMode::Transparent {
        tr.absorb_bytes(b"pcs/params", b"transparent");
        tr.absorb_bytes(b"pcs/root", root);
        return Ok(None);
    }
    let params = derived
        .ligerito_params(inst.ell)
        .map_err(|e| VerificationError::new(e.to_string()))?;
    let pcs = BitPCS::with_hasher(params, vk.hasher());
    let n = pcs.pcs.p.n;
    pcs.pcs.absorb_commitment(
        &Commitment {
            root: root.to_vec(),
            n,
        },
        tr,
    );
    Ok(Some(pcs))
}

/// The transparent mock's commitment root,
/// `H("openmagnetar/transparent-G/v1" || packed G)` with `G` packed
/// LSB-first per byte (Python `_transparent_root`).
pub fn transparent_root(vk: &VerifyingKey, g: &[bool]) -> Vec<u8> {
    let mut b = vec![0u8; g.len().div_ceil(8)];
    for (i, &bit) in g.iter().enumerate() {
        if bit {
            b[i / 8] |= 1 << (i % 8);
        }
    }
    let mut preimage = b"openmagnetar/transparent-G/v1".to_vec();
    preimage.extend_from_slice(&b);
    vk.hasher().digest(&preimage)
}

/// `M_0 = m0_program ∪ input_words(data)` (Python `_m0_words`).
///
/// # Errors
/// Returns [`AbiError`] if the input does not fit or the program image
/// reaches into the I/O window.
pub fn m0_words(vk: &VerifyingKey, data: &[u8]) -> Result<BTreeMap<usize, u64>, AbiError> {
    build_m0(&vk.m0_program, data, &vk.abi)
}

/// The `M̃_0` evaluator from the non-zero words of `M_0`, in
/// `O(nnz·(A + 64))` (Python `_m0_eval`; §11.6 step 4). The point is
/// `r_k ∥ r_o` with `|r_k| = a` (the RAM Twist address bits, which may
/// exceed the ABI's `A` after `choose_ad` padding; word indices are
/// then below `2^a` with zero high bits, as in Python).
pub fn m0_eval(words: &BTreeMap<usize, u64>, a: usize) -> impl Fn(&[K]) -> K {
    let nz: Vec<(usize, u64)> = words
        .iter()
        .filter(|&(_, &v)| v != 0)
        .map(|(&k, &v)| (k, v))
        .collect();
    move |pt: &[K]| {
        let (rk, ro) = (&pt[..a], &pt[a..]);
        let eo = eq_table(ro);
        let mut acc = K::ZERO;
        for &(k, v) in &nz {
            let mut s = 0u128;
            for (o, e) in eo.iter().enumerate().take(64) {
                if (v >> o) & 1 == 1 {
                    s ^= e.value();
                }
            }
            acc += eq_eval(rk, &bits_of(k as u64, a)) * K::from_u128(s);
        }
        acc
    }
}

/// Split Spartan output claims: `(virtual-by-name, direct in layout
/// order, cross-step claims)` (Python `_seg_claims`).
///
/// # Errors
/// Returns [`VerificationError`] unless there are exactly
/// `n_segments + 2` claims.
#[allow(clippy::type_complexity)]
pub fn seg_claims(
    derived: &Derived,
    claims: &[Claim],
) -> Result<(BTreeMap<&'static str, Claim>, Vec<Claim>, Vec<Claim>), VerificationError> {
    let nseg = derived.segments.len();
    if claims.len() != nseg + 2 {
        return Err(VerificationError::new(
            "unexpected number of Spartan claims",
        ));
    }
    let (mut virt, mut direct) = (BTreeMap::new(), Vec::new());
    for (sg, cl) in derived.segments.iter().zip(&claims[..nseg]) {
        if sg.kind == SegmentKind::Virtual {
            virt.insert(sg.name, cl.clone());
        } else {
            direct.push(cl.clone());
        }
    }
    Ok((virt, direct, claims[nseg..].to_vec()))
}

/// The common point of virtual claims `names`, split as
/// `(first ol coordinates, rest)` (Python `_same_point`).
///
/// # Errors
/// Returns [`VerificationError`] if a name is unknown or the points
/// differ.
pub fn same_point(
    virt: &BTreeMap<&'static str, Claim>,
    names: &[&str],
    ol: usize,
) -> Result<(Vec<K>, Vec<K>), VerificationError> {
    let mut pts: Vec<&Vec<K>> = Vec::with_capacity(names.len());
    for nm in names {
        pts.push(
            &virt
                .get(nm)
                .ok_or_else(|| VerificationError::new("missing virtual claim"))?
                .point,
        );
    }
    if pts.iter().any(|p| *p != pts[0]) {
        return Err(VerificationError::new("virtual claims at different points"));
    }
    Ok((pts[0][..ol].to_vec(), pts[0][ol..].to_vec()))
}

/// Convert an [`EvalClaim`] to a Mosaic [`Claim`] through `inst`'s
/// name->id map (Python `_to_mosaic`).
///
/// # Panics
/// Panics if `ec.poly` is not a known component (Python `KeyError`);
/// all names reaching here are fixed by the sub-protocols.
pub fn to_mosaic(inst: &Instance, ec: &EvalClaim) -> Claim {
    let id = inst
        .ids
        .get(ec.poly.as_str())
        .unwrap_or_else(|| panic!("unknown component {}", ec.poly));
    ec.to_mosaic_claim(*id)
}

/// `Σ_{t<A} eq(r_o, t)·f_t == v_ridx` (§11.6 step 4; Python
/// `_ram_bits_ok`).
pub fn ram_bits_ok(r_o: &[K], bits: &[K], v_ridx: K, a: usize) -> bool {
    let eo = eq_table(r_o);
    let mut acc = K::ZERO;
    for t in 0..a {
        acc += eo[t] * bits[t];
    }
    acc == v_ridx
}

/// The bytecode Shout table with point-dependent derived columns, and
/// the six claim groups of §11.7 (Python `protocol._Plan`).
#[derive(Clone, Debug)]
pub struct ShoutPlan {
    /// Table columns: 18 index columns, then one derived column per
    /// claimed ROM bit-field, each of length `2^rom_a`.
    pub table: Vec<Vec<K>>,
    /// The six claim groups, in §11.7 order.
    pub groups: Vec<ShoutClaims>,
    /// `shout/bytecode` parameters.
    pub params: ShoutParams,
}

impl ShoutPlan {
    /// Build the plan from the Spartan virtual claims, the register
    /// bit claims, the shift-router claims and the store-router `q`
    /// claim.
    ///
    /// # Errors
    /// Returns [`VerificationError`] on a bad selector-point or
    /// cycle-point length, or claims of one group at different cycle
    /// points.
    ///
    /// # Panics
    /// Panics if `sh_claims` has fewer than 3 entries (as Python
    /// raises `IndexError`); router outputs always have 3.
    pub fn new(
        derived: &Derived,
        n: usize,
        virt: &BTreeMap<&'static str, Claim>,
        reg_bits: &[K],
        sh_claims: &[EvalClaim],
        st_q: &EvalClaim,
    ) -> Result<ShoutPlan, VerificationError> {
        let (n_rom, rows) = (derived.n_rom, 1usize << derived.rom_a);
        let mut table: Vec<Vec<K>> = Vec::new();
        for nm in REG_IDX_COLS {
            for t in 0..REG_A {
                let mut col: Vec<K> = (0..n_rom)
                    .map(|k| {
                        K::from_bit((derived.rom[k].get(nm).expect("index column") >> t) & 1 == 1)
                    })
                    .collect();
                col.resize(rows, K::ZERO);
                table.push(col);
            }
        }
        let mut groups: Vec<ShoutClaims> = Vec::new();

        // One derived column D_{field,rho}; returns its index.
        let derived_col = |table: &mut Vec<Vec<K>>,
                           field_name: &str,
                           rho: &[K]|
         -> Result<usize, VerificationError> {
            let eq = eq_table(rho);
            let width = cpu::field(field_name).expect("ROM field name").width;
            if eq.len() != width {
                return Err(VerificationError::new("bad selector point length"));
            }
            let mut col: Vec<K> = (0..n_rom)
                .map(|k| {
                    let (mut v, mut acc, mut o) = (
                        derived.rom_fields[k]
                            .get(field_name)
                            .expect("ROM field name"),
                        0u128,
                        0usize,
                    );
                    while v != 0 {
                        if v & 1 == 1 {
                            acc ^= eq[o].value();
                        }
                        v >>= 1;
                        o += 1;
                    }
                    K::from_u128(acc)
                })
                .collect();
            col.resize(rows, K::ZERO);
            table.push(col);
            Ok(table.len() - 1)
        };

        // A Spartan-owned group: fields share a width (hence `ol`) and
        // must share their cycle point.
        let spartan_group = |table: &mut Vec<Vec<K>>,
                             groups: &mut Vec<ShoutClaims>,
                             fields: &[&str],
                             pre_cols: &[usize],
                             pre_rv: &[K]|
         -> Result<(), VerificationError> {
            let ol = cpu::field(fields[0])
                .expect("field name")
                .width
                .trailing_zeros() as usize;
            let mut pts: Vec<&Vec<K>> = Vec::with_capacity(fields.len());
            for f in fields {
                pts.push(
                    &virt
                        .get(f)
                        .ok_or_else(|| VerificationError::new("missing virtual claim"))?
                        .point,
                );
            }
            if pts.iter().any(|p| p[ol..] != pts[0][ol..]) {
                return Err(VerificationError::new(
                    "shout group at different cycle points",
                ));
            }
            let (mut cols, mut rv) = (pre_cols.to_vec(), pre_rv.to_vec());
            for f in fields {
                let cl = &virt[*f];
                cols.push(derived_col(table, f, &cl.point[..ol])?);
                rv.push(cl.value);
            }
            let c = pts[0][ol..].to_vec();
            if c.len() != n {
                return Err(VerificationError::new("bad cycle point length"));
            }
            groups.push(ShoutClaims {
                r_c: c,
                cols,
                rv,
                bits: None,
            });
            Ok(())
        };

        let idx_cols: Vec<usize> = (0..18).collect();
        spartan_group(
            &mut table,
            &mut groups,
            &["imm", "kc", "rpc", "rf", "Q_lo"],
            &idx_cols,
            reg_bits,
        )?;
        spartan_group(&mut table, &mut groups, &["upc", "seq", "tgt"], &[], &[])?;
        spartan_group(&mut table, &mut groups, &["Q_hi"], &[], &[])?;
        spartan_group(&mut table, &mut groups, &["st_w"], &[], &[])?;

        let (qlo, qhi) = (&sh_claims[1], &sh_claims[2]);
        let router_group = |table: &mut Vec<Vec<K>>,
                            groups: &mut Vec<ShoutClaims>,
                            c: &[K],
                            specs: &[(&str, &[K], K)]|
         -> Result<(), VerificationError> {
            let (mut cols, mut rv) = (Vec::new(), Vec::new());
            for &(f, rho, val) in specs {
                cols.push(derived_col(table, f, rho)?);
                rv.push(val);
            }
            if c.len() != n {
                return Err(VerificationError::new("bad cycle point length"));
            }
            groups.push(ShoutClaims {
                r_c: c.to_vec(),
                cols,
                rv,
                bits: None,
            });
            Ok(())
        };
        router_group(
            &mut table,
            &mut groups,
            &qlo.point[6..],
            &[
                ("Q_lo", &qlo.point[..6], qlo.value),
                ("Q_hi", &qhi.point[..3], qhi.value),
            ],
        )?;
        router_group(
            &mut table,
            &mut groups,
            &st_q.point[2..],
            &[("st_w", &st_q.point[..2], st_q.value)],
        )?;

        Ok(ShoutPlan {
            table,
            groups,
            params: ShoutParams {
                name: "shout/bytecode".to_string(),
                a: derived.rom_a,
                d: derived.rom_d,
                n,
            },
        })
    }
}

/// Assemble all Mosaic claims in the fixed order of §11.7 (Python
/// `_mosaic_claims`): direct Spartan, cross-step, register Twist,
/// RAM Twist, RAM Inc `y_0`, `shsrc`, `stc`, `off` bits, Shout.
#[allow(clippy::too_many_arguments)]
pub fn mosaic_claims(
    inst: &Instance,
    direct: &[Claim],
    xs: &[Claim],
    reg_out: &TwistOutput,
    ram_out: &TwistOutput,
    r_o: &[K],
    r_c: &[K],
    y0: K,
    sh_claims: &[EvalClaim],
    st_claims: &[EvalClaim],
    shout_claims: &[EvalClaim],
) -> Vec<Claim> {
    let mut out: Vec<Claim> = direct.to_vec();
    out.extend_from_slice(xs);
    out.extend(reg_out.claims.iter().map(|c| to_mosaic(inst, c)));
    out.extend(ram_out.claims.iter().map(|c| to_mosaic(inst, c)));
    let mut inc_pt = r_o.to_vec();
    inc_pt.extend_from_slice(r_c);
    out.push(to_mosaic(
        inst,
        &EvalClaim {
            poly: "twist/ram/inc".to_string(),
            point: inc_pt,
            value: y0,
        },
    ));
    out.push(to_mosaic(
        inst,
        &EvalClaim {
            poly: "shsrc".to_string(),
            point: sh_claims[0].point.clone(),
            value: sh_claims[0].value,
        },
    ));
    out.push(to_mosaic(
        inst,
        &EvalClaim {
            poly: "stc".to_string(),
            point: st_claims[0].point.clone(),
            value: st_claims[0].value,
        },
    ));
    for (b, c) in st_claims[2..].iter().enumerate() {
        let mut pt = vec![K::from_bit(b & 1 == 1), K::from_bit((b >> 1) & 1 == 1)];
        pt.extend_from_slice(&c.point);
        out.push(to_mosaic(
            inst,
            &EvalClaim {
                poly: "off".to_string(),
                point: pt,
                value: c.value,
            },
        ));
    }
    out.extend(shout_claims.iter().map(|c| to_mosaic(inst, c)));
    out
}

/// [`transparent_root`] over a packed `G`: identical preimage bytes
/// (packed words are little-endian bit order, as the root encoding).
pub fn transparent_root_packed(vk: &VerifyingKey, g: &PackedBits) -> Vec<u8> {
    let mut b = Vec::with_capacity(g.len().div_ceil(8));
    for &w in g.words() {
        b.extend_from_slice(&w.to_le_bytes());
    }
    b.truncate(g.len().div_ceil(8));
    let mut preimage = b"openmagnetar/transparent-G/v1".to_vec();
    preimage.extend_from_slice(&b);
    vk.hasher().digest(&preimage)
}
