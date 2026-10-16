//! The prover (spec §11.5): execution, then commit -> Virtual Spartan
//! -> register Twist -> RAM Twist (final memory) -> shift router ->
//! store router -> bytecode Shout -> Mosaic batching -> ring switching
//! -> Ligerito (or the test-only transparent mock). Mirrors the prover
//! side of `reference/openmagnetar/protocol.py`; the proof type is
//! `om_format::Proof`.

use std::collections::BTreeMap;
use std::fmt;

use om_circuit::circuit as cpu;
use om_elf::{AbiError, encode_region, extract_output};
use om_format::{PcsMode, PcsProof, Proof, PublicInstance, VerifyingKey};
use om_isa::bytecode::{TraceRecord, VirtualMachine};
use om_isa::riscv::Trap;
use om_memcheck::onehot::AddrComps;
use om_memcheck::shout::shout_prove;
use om_memcheck::twist::{self as tw, FinalMem, TwistClaims};
use om_mosaic::{batch_prove_packed, build_g_packed};
use om_pcs::pcs::BitPCS;
use om_router as rt;
use om_spartan::SegmentKind;
use om_spartan::spartan::{CrossStep, segment_table_packed};
use om_sumcheck::{PackedBits, VerificationError};
use om_transcript::Transcript;

use crate::common::{
    LABEL, ShoutPlan, absorb_commitment, absorb_statement, m0_words, mosaic_claims, same_point,
    seg_claims, transparent_root_packed,
};
use crate::keygen::{Derived, KeyError, WORD_BITS};

/// Default execution budget (Python `execute(max_cycles = 1 << 20)`).
pub const DEFAULT_MAX_CYCLES: usize = 1 << 20;

/// A test-only trace mutator (Python `hooks={"trace": fn}`).
pub type TraceHook<'a> = dyn FnMut(&mut Vec<TraceRecord>) + 'a;

/// A prover-side failure (Python raises `ValueError`/`AbiError`/`Trap`
/// or a sub-protocol assert; asserts that indicate a programming error
/// in a sub-crate still panic there, as in the other `om-*` crates).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProverError {
    /// v1 has no private input (Python `ValueError`).
    PrivateInputNotSupported,
    /// Key derivation failed.
    Key(KeyError),
    /// ABI failure (input too large, non-canonical output region...).
    Abi(AbiError),
    /// Execution trapped.
    Trap(Trap),
    /// An internal claim was inconsistent (should not happen for an
    /// honestly executed trace).
    Verification(VerificationError),
    /// Internal error with a static message.
    Internal(&'static str),
}

impl fmt::Display for ProverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProverError::PrivateInputNotSupported => {
                f.write_str("v1 has no private input: the input is public (spec 14.1)")
            }
            ProverError::Key(e) => write!(f, "{e}"),
            ProverError::Abi(e) => write!(f, "{e}"),
            ProverError::Trap(e) => write!(f, "{e}"),
            ProverError::Verification(e) => write!(f, "{e}"),
            ProverError::Internal(m) => f.write_str(m),
        }
    }
}

impl std::error::Error for ProverError {}

impl From<KeyError> for ProverError {
    fn from(e: KeyError) -> ProverError {
        ProverError::Key(e)
    }
}

impl From<AbiError> for ProverError {
    fn from(e: AbiError) -> ProverError {
        ProverError::Abi(e)
    }
}

impl From<Trap> for ProverError {
    fn from(e: Trap) -> ProverError {
        ProverError::Trap(e)
    }
}

impl From<VerificationError> for ProverError {
    fn from(e: VerificationError) -> ProverError {
        ProverError::Verification(e)
    }
}

/// One execution (Python `protocol.Execution`).
#[derive(Clone, Debug)]
pub struct Execution {
    /// The public instance `(T, input, output, exit_code)`.
    pub instance: PublicInstance,
    /// The padded trace, `T` cycles (last one `HALTED`).
    pub trace: Vec<TraceRecord>,
    /// Value of `a0` at `HALT`.
    pub exit_code: u64,
    /// Initial memory `M_0` (sparse).
    pub m0: BTreeMap<usize, u64>,
}

/// Execute the vk's program on `public_input`: build `M_0`, run the
/// virtual machine to `HALT` plus padding, extract the output
/// (Python `execute`). Derives from `vk` internally; use
/// [`execute_with_derived`] to reuse a [`Derived`].
///
/// # Errors
/// Returns [`ProverError`] if `M_0` cannot be built, execution traps
/// or exceeds `max_cycles`, or the output region is non-canonical (no
/// proof exists then).
pub fn execute(
    vk: &VerifyingKey,
    public_input: &[u8],
    max_cycles: usize,
) -> Result<Execution, ProverError> {
    execute_with_derived(&Derived::new(vk), public_input, max_cycles)
}

/// [`execute`] against a prebuilt [`Derived`].
///
/// # Errors
/// As [`execute`].
pub fn execute_with_derived(
    derived: &Derived,
    public_input: &[u8],
    max_cycles: usize,
) -> Result<Execution, ProverError> {
    let vk = &derived.vk;
    let m0 = m0_words(vk, public_input)?;
    let mut vm = VirtualMachine::new(derived.program.clone(), &m0, vk.abi.ram_log_words);
    let res = vm.run_padded(max_cycles)?;
    let output = extract_output(&res.ram, &vk.abi)?;
    let t = res.trace.len() as u64;
    Ok(Execution {
        instance: PublicInstance {
            t,
            input: public_input.to_vec(),
            output,
            exit_code: res.exit_code,
        },
        trace: res.trace,
        exit_code: res.exit_code,
        m0,
    })
}

/// Prove, returning just the proof (Python `protocol.prove`).
/// A private input is rejected: v1's input is public (§14.1).
///
/// # Errors
/// As [`prove_instance`], plus
/// [`ProverError::PrivateInputNotSupported`] if `private_input` is
/// `Some`.
pub fn prove(
    vk: &VerifyingKey,
    public_input: &[u8],
    private_input: Option<&[u8]>,
) -> Result<Proof, ProverError> {
    Ok(prove_instance_inner(vk, public_input, private_input, None, DEFAULT_MAX_CYCLES)?.1)
}

/// [`prove_instance`] with an explicit execution budget in cycles,
/// instead of [`DEFAULT_MAX_CYCLES`]. The budget is a local resource
/// limit only: it changes no proof byte for executions that fit.
///
/// # Errors
/// As [`prove_instance`].
pub fn prove_instance_with_max_cycles(
    vk: &VerifyingKey,
    public_input: &[u8],
    max_cycles: usize,
) -> Result<(PublicInstance, Proof), ProverError> {
    prove_instance_inner(vk, public_input, None, None, max_cycles)
}

/// Prove, returning `(public instance, proof)` (Python
/// `protocol.prove_instance` without hooks).
///
/// # Errors
/// Returns [`ProverError`] on execution failure, a non-canonical
/// output region, or an inconsistent internal claim.
pub fn prove_instance(
    vk: &VerifyingKey,
    public_input: &[u8],
    private_input: Option<&[u8]>,
) -> Result<(PublicInstance, Proof), ProverError> {
    prove_instance_inner(vk, public_input, private_input, None, DEFAULT_MAX_CYCLES)
}

/// [`prove_instance`] with a test-only trace mutator (Python
/// `hooks={"trace": fn}`, a cheating prover): the hook runs on the
/// execution trace before witness generation and the Spartan
/// satisfiability check is skipped.
///
/// # Errors
/// As [`prove_instance`].
pub fn prove_instance_with_trace_hook(
    vk: &VerifyingKey,
    public_input: &[u8],
    hook: &mut TraceHook<'_>,
) -> Result<(PublicInstance, Proof), ProverError> {
    prove_instance_inner(vk, public_input, None, Some(hook), DEFAULT_MAX_CYCLES)
}

fn prove_instance_inner(
    vk: &VerifyingKey,
    public_input: &[u8],
    private_input: Option<&[u8]>,
    mut hook: Option<&mut TraceHook<'_>>,
    max_cycles: usize,
) -> Result<(PublicInstance, Proof), ProverError> {
    if private_input.is_some() {
        return Err(ProverError::PrivateInputNotSupported);
    }
    let derived = Derived::new(vk);
    let ex = execute_with_derived(&derived, public_input, max_cycles)?;
    crate::memtrace::mark("execute");
    prove_execution(&derived, ex, &mut hook)
}

/// Prove an already-obtained [`Execution`] (the body of
/// `prove_instance` after `execute`). Exposed so tests (and the
/// cheating-prover hook) can mutate the trace between the phases,
/// exactly as Python's `hooks` do.
///
/// # Errors
/// Returns [`ProverError`] on an inconsistent internal claim or a
/// PCS/derivation failure.
pub fn prove_execution(
    derived: &Derived,
    mut ex: Execution,
    hook: &mut Option<&mut TraceHook<'_>>,
) -> Result<(PublicInstance, Proof), ProverError> {
    let vk = &derived.vk;
    let inst = ex.instance.clone();
    let di = derived.instance(inst.t)?;
    let (n, s) = (di.n, di.s);
    let unchecked = hook.is_some();
    if let Some(h) = hook.as_deref_mut() {
        h(&mut ex.trace);
    }
    let trace = &ex.trace;
    let public = cpu::public_inputs(&derived.program, ex.exit_code);
    let w = cpu::witness_packed(trace, &derived.cpu_params, Some(ex.exit_code));
    crate::memtrace::mark("witness");

    // Twist witnesses in compact form (one address per access and one
    // Inc word per cycle, spec 07 §7.10).
    let reg_wit = tw::build_witness_lean(
        &di.reg,
        &[0u64; 64],
        vec![
            trace.iter().map(|r| u32::from(r.rs1)).collect(),
            trace.iter().map(|r| u32::from(r.rs2)).collect(),
        ],
        trace.iter().map(|r| u32::from(r.rd)).collect(),
        &trace.iter().map(|r| r.rd_val).collect::<Vec<_>>(),
    );
    let ram_a = derived.ram_a;
    let m0_list: Vec<u64> = (0..1usize << ram_a)
        .map(|k| ex.m0.get(&k).copied().unwrap_or(0))
        .collect();
    let ridx: Vec<u32> = trace
        .iter()
        .map(|r| u32::try_from(r.ram_idx).expect("RAM word index fits in u32"))
        .collect();
    let ram_wit = tw::build_witness_lean(
        &di.ram,
        &m0_list,
        vec![ridx.clone()],
        ridx,
        &trace.iter().map(|r| r.ram_new).collect::<Vec<_>>(),
    );
    let sh_wit = rt::shift_witness(
        &trace
            .iter()
            .map(|r| {
                (
                    r.shift_src,
                    match (r.shift_amt, r.shift_kind) {
                        (Some(amt), Some(kind)) => Some((usize::from(amt), usize::from(kind))),
                        _ => None,
                    },
                )
            })
            .collect::<Vec<_>>(),
        WORD_BITS,
    );
    let mut st_wit = rt::store_witness(
        &trace
            .iter()
            .map(|r| {
                (
                    r.ram_old,
                    r.store_src,
                    r.store_width
                        .map(|wd| (usize::from(wd), usize::from(r.store_off))),
                )
            })
            .collect::<Vec<_>>(),
        WORD_BITS,
    );
    // The offset bits are the circuit's `off` segment, defined on
    // every cycle (not only on stores).
    st_wit.abits = (0..3)
        .map(|b| trace.iter().map(|r| (r.store_off >> b) & 1 == 1).collect())
        .collect();
    let sh_comps = AddrComps::from_addrs(
        trace.iter().map(|r| r.upc).collect(),
        derived.rom_a,
        derived.rom_d,
    );
    crate::memtrace::mark("component witnesses");

    let mut tables: BTreeMap<i64, PackedBits> = BTreeMap::new();
    for (i, sg) in derived.spartan_segments.iter().enumerate() {
        if sg.kind == SegmentKind::Direct {
            tables.insert(i as i64, segment_table_packed(&w, sg));
        }
    }
    for (x, comps) in [
        ("ra0", &reg_wit.ra[0]),
        ("ra1", &reg_wit.ra[1]),
        ("wa", &reg_wit.wa),
    ] {
        for i in 0..comps.d() {
            tables.insert(di.ids[&format!("twist/reg/{x}/{}", i + 1)], comps.packed(i));
        }
    }
    tables.insert(di.ids["twist/reg/inc"], reg_wit.inc_packed(di.reg.ell));
    for i in 0..ram_wit.ra[0].d() {
        tables.insert(
            di.ids[&format!("twist/ram/ra0/{}", i + 1)],
            ram_wit.ra[0].packed(i),
        );
    }
    tables.insert(di.ids["twist/ram/inc"], ram_wit.inc_packed(di.ram.ell));
    for i in 0..sh_comps.d() {
        tables.insert(
            di.ids[&format!("shout/bytecode/ra/{}", i + 1)],
            sh_comps.packed(i),
        );
    }
    let g = build_g_packed(&di.layout, &tables);
    drop(tables);
    crate::memtrace::mark("build G");

    // Step 1: statement, commitment.
    let mut tr = Transcript::new(LABEL, vk.hasher());
    absorb_statement(&mut tr, vk, &inst);
    let (pcs, pcs_state, root) = if vk.pcs == PcsMode::Transparent {
        let root = transparent_root_packed(vk, &g);
        absorb_commitment(vk, derived, &di, &root, &mut tr)?;
        (None, None, root)
    } else {
        let pcs = BitPCS::with_hasher(derived.ligerito_params(di.ell)?, vk.hasher());
        let (cm, st) = pcs.commit_packed(&g, &mut tr);
        let root = cm.root.clone();
        (Some(pcs), Some(st), root)
    };
    crate::memtrace::mark("commit");

    // Step 2: Virtual Spartan.
    let x: Vec<Vec<om_field::K>> = vec![Vec::new(); 1usize << s];
    let cross = CrossStep {
        in_id: derived.seg_id["S_in"],
        out_id: derived.seg_id["S_out"],
        init: cpu::init_vector(&public),
        fin: cpu::fin_vector(&public),
    };
    let (sp_proof, sp_claims) = om_spartan::spartan::prove(
        &derived.rels,
        &w,
        &x,
        &mut tr,
        b"vsp",
        None,
        Some(&derived.spartan_segments),
        Some(&cross),
        unchecked,
    );
    drop(w);
    crate::memtrace::mark("spartan");
    let (virt, direct, xs) = seg_claims(derived, &sp_claims)?;

    // Step 3: register Twist.
    let (r_o, r_c) = same_point(&virt, &["v1", "v2", "rdv"], 6)?;
    let honest_bits = tw::addr_bit_claims(&di.reg, &reg_wit, &r_c);
    let reg_bits: Vec<_> = honest_bits.iter().flatten().copied().collect();
    let reg_claims = TwistClaims {
        r_o: r_o.clone(),
        r_c: r_c.clone(),
        rv: vec![virt["v1"].value, virt["v2"].value],
        wv: virt["rdv"].value,
        bits: honest_bits,
    };
    let (reg_proof, reg_out) = tw::twist_prove(
        &di.reg,
        &[0u64; 64],
        &reg_wit,
        &reg_claims,
        &mut tr,
        b"twist/reg",
        None,
        false,
    );
    drop(reg_wit);
    crate::memtrace::mark("register twist");

    // Step 4: RAM Twist with final memory; Inc claim at the Spartan point.
    let (r_or, r_cr) = same_point(&virt, &["rw", "ridx"], 6)?;
    let ram_bits: Vec<_> = ram_wit.ra[0].bit_evals(ram_a, &r_cr);
    let y0 = tw::word_mle_eval(&ram_wit.inc, &r_or, &r_cr);
    tr.absorb_k(b"twist/ram/incwv", y0);
    let ram_claims = TwistClaims {
        r_o: r_or.clone(),
        r_c: r_cr.clone(),
        rv: vec![virt["rw"].value],
        wv: virt["rw"].value + y0,
        bits: vec![ram_bits.clone(), ram_bits.clone()],
    };
    let o = vk.abi.output_log_words;
    let final_mem = FinalMem {
        m: o as usize,
        s_out: derived.mm.output_base >> o,
        words: encode_region(&inst.output, o)?,
    };
    let (ram_proof, ram_out) = tw::twist_prove(
        &di.ram,
        &m0_list,
        &ram_wit,
        &ram_claims,
        &mut tr,
        b"twist/ram",
        Some(&final_mem),
        false,
    );
    drop((ram_wit, m0_list));
    crate::memtrace::mark("ram twist");

    // Step 5: routers.
    let (r_oy, r_cy) = same_point(&virt, &["Y"], 6)?;
    let (sh_proof, sh_claims) = rt::shift_prove_fast(
        n,
        &sh_wit,
        &r_oy,
        &r_cy,
        virt["Y"].value,
        &mut tr,
        b"router/shift",
        WORD_BITS,
    );
    let (st_proof, st_claims) = rt::store_prove_fast(
        n,
        &st_wit,
        &r_or,
        &r_cr,
        y0,
        &mut tr,
        b"router/store",
        WORD_BITS,
    );
    crate::memtrace::mark("routers");

    // Step 6: bytecode Shout.
    let plan = ShoutPlan::new(derived, n, &virt, &reg_bits, &sh_claims, &st_claims[1])?;
    let (shout_proof, shout_claims) = shout_prove(
        &plan.params,
        &plan.table,
        &sh_comps,
        &plan.groups,
        &mut tr,
        b"shout/bytecode",
    );
    drop(sh_comps);
    crate::memtrace::mark("shout");

    // Step 7: Mosaic, ring switching, PCS.
    let mclaims = mosaic_claims(
        &di,
        &direct,
        &xs,
        &reg_out,
        &ram_out,
        &r_or,
        &r_cr,
        y0,
        &sh_claims,
        &st_claims,
        &shout_claims,
    );
    if std::env::var_os("OM_TRACE_LAYOUT").is_some() {
        eprintln!("ell {} claims {}", di.layout.ell, mclaims.len());
        for pl in &di.layout.placements {
            let nnz = (0..1usize << pl.log_size)
                .filter(|&i| g.bit(pl.offset + i))
                .count();
            let nc = mclaims.iter().filter(|c| c.comp_id == pl.comp_id).count();
            eprintln!(
                "  comp {:>4} log {:>2} offset {:#x} claims {nc} nnz {nnz}",
                pl.comp_id, pl.log_size, pl.offset
            );
        }
    }
    let (batch, r_g, v_g) = batch_prove_packed(&di.layout, &mclaims, &g, &mut tr);
    crate::memtrace::mark("mosaic batch");
    let pcs_proof = if vk.pcs == PcsMode::Transparent {
        PcsProof::Transparent(g.to_bools())
    } else {
        let pcs = pcs.expect("ligerito pcs built at commit");
        let st = pcs_state.expect("ligerito state from commit");
        let (y, (rs_proof, lig_proof)) = pcs.open_packed(&st, &r_g, &mut tr);
        if y != v_g {
            return Err(ProverError::Internal("internal error: G(r_G) != v_G"));
        }
        PcsProof::Ligerito(rs_proof, lig_proof)
    };
    crate::memtrace::mark("pcs open");

    Ok((
        inst,
        Proof {
            log_t: u8::try_from(n).expect("n <= 40"),
            root,
            spartan: sp_proof,
            reg_bits,
            reg: reg_proof,
            ram_bits,
            ram_inc_wv: y0,
            ram: ram_proof,
            shift: sh_proof,
            store: st_proof,
            shout: shout_proof,
            mosaic: batch,
            pcs_proof,
        },
    ))
}
