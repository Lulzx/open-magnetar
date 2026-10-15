//! KeyGen (spec §11.2): verifying-key derivation. Mirrors
//! `reference/openmagnetar/keygen.py` (`keygen`, `keygen_from_elf`,
//! `Derived`, `Instance`); the `VerifyingKey` type itself lives in
//! `om_format` (see the crate docs for the `derived`/`digest` delta).

use std::collections::BTreeMap;
use std::fmt;

use om_circuit::circuit as cpu;
use om_elf::{ElfError, MemoryMap, Params as AbiParams, load as elf_load, memory_map};
use om_format::{FormatError, PcsMode, PcsProfile, ProofShape, VerifyingKey};
use om_isa::bytecode::{Program, Row, expand};
use om_memcheck::twist::TwistParams;
use om_mosaic::{Layout, compute_layout};
use om_pcs::ligerito::LigeritoParams;
use om_router::{shift_entries, store_entries};
use om_spartan::r1cs::{R1CS, RelationField};
use om_spartan::spartan::Segment as SpartanSegment;

/// `keygen.VK_VERSION` (also `om_format::VK_VERSION`).
pub const VK_VERSION: u8 = om_format::VK_VERSION;
/// `keygen.MAX_LOG_T`: `T <= 2^40` (§11.3).
pub const MAX_LOG_T: u32 = 40;
/// `keygen.LOG_CYCLES`: `c = 2` cycles per SIMD instance (§10.2).
pub const LOG_CYCLES: u32 = 2;
/// Register Twist address bits (`keygen.REG_A`).
pub const REG_A: usize = 6;
/// Register Twist address components (`keygen.REG_D`).
pub const REG_D: usize = 2;
/// Register Twist reads per cycle (`keygen.REG_P`).
pub const REG_P: usize = 2;
/// Word bit length is `2^WORD_BITS = 64` (`keygen.WORD_BITS`).
pub const WORD_BITS: usize = 6;

/// A key-generation or derivation failure (Python `KeyError_`, plus the
/// `AbiError`/`ElfError`/`FormatError` the Python constructor and ELF
/// loader surface).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KeyError {
    /// Python `KeyError_` with its message.
    Key(String),
    /// vk construction/validation failed (`om_format`).
    Format(FormatError),
    /// ELF loading failed.
    Elf(ElfError),
}

impl fmt::Display for KeyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KeyError::Key(m) => f.write_str(m),
            KeyError::Format(e) => write!(f, "{e}"),
            KeyError::Elf(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for KeyError {}

impl From<FormatError> for KeyError {
    fn from(e: FormatError) -> KeyError {
        KeyError::Format(e)
    }
}

impl From<ElfError> for KeyError {
    fn from(e: ElfError) -> KeyError {
        KeyError::Elf(e)
    }
}

impl From<om_elf::AbiError> for KeyError {
    fn from(e: om_elf::AbiError) -> KeyError {
        KeyError::Format(FormatError::BadAbiParams(e))
    }
}

/// KeyGen: `(code image, entry pc, data image, parameters) -> vk`
/// (Python `keygen`). [`Derived`] holds the rest.
///
/// # Errors
/// Returns [`KeyError`] for invalid ABI parameters, a `test` profile
/// with `pcs_t < 1`, a code image over `MAX_CODE`, or an `entry_pc`
/// outside the code image (via `om_format::VerifyingKey::new`, which
/// also computes `program_digest`).
#[allow(clippy::too_many_arguments)]
pub fn keygen(
    code: BTreeMap<u64, u32>,
    entry_pc: u64,
    m0_program: BTreeMap<usize, u64>,
    abi_params: AbiParams,
    pcs: PcsMode,
    pcs_profile: PcsProfile,
    pcs_r: u8,
    pcs_t: u32,
) -> Result<VerifyingKey, KeyError> {
    Ok(VerifyingKey::new(
        abi_params,
        code,
        entry_pc,
        m0_program,
        pcs,
        pcs_profile,
        pcs_r,
        pcs_t,
    )?)
}

/// KeyGen with Python's defaults after the images: Ligerito,
/// `provable-120`, `r = 2`, `t = 0`.
///
/// # Errors
/// As [`keygen`].
pub fn keygen_default(
    code: BTreeMap<u64, u32>,
    entry_pc: u64,
    m0_program: BTreeMap<usize, u64>,
    abi_params: AbiParams,
) -> Result<VerifyingKey, KeyError> {
    keygen(
        code,
        entry_pc,
        m0_program,
        abi_params,
        PcsMode::Ligerito,
        PcsProfile::Provable120,
        2,
        0,
    )
}

/// KeyGen from an ELF64 image (Python `keygen_from_elf`).
///
/// # Errors
/// Returns [`KeyError`] if the ELF does not load or the key is invalid.
#[allow(clippy::too_many_arguments)]
pub fn keygen_from_elf(
    elf: &[u8],
    abi_params: AbiParams,
    pcs: PcsMode,
    pcs_profile: PcsProfile,
    pcs_r: u8,
    pcs_t: u32,
) -> Result<VerifyingKey, KeyError> {
    let img = elf_load(elf, &abi_params)?;
    keygen(
        img.code,
        img.entry_pc,
        img.ram_words,
        abi_params,
        pcs,
        pcs_profile,
        pcs_r,
        pcs_t,
    )
}

/// Parameters that depend on `T` (Python `keygen.Instance`, §11.3).
#[derive(Clone, Debug)]
pub struct Instance {
    /// Trace length `T`.
    pub t: u64,
    /// `n = log2 T`.
    pub n: usize,
    /// `s = n - 2` (SIMD-instance bits).
    pub s: usize,
    /// Register Twist parameters `(6, 2, 2)`.
    pub reg: TwistParams,
    /// RAM Twist parameters `(ram_a, ram_d, 1)`.
    pub ram: TwistParams,
    /// `[(name, log_size)]` committed auxiliary components in id order
    /// (after the segments).
    pub comps: Vec<(String, usize)>,
    /// Component name -> id (segments first, then `comps`; the RAM
    /// `wa` names alias `ra0`).
    pub ids: BTreeMap<String, i64>,
    /// Mosaic layout of all committed components.
    pub layout: Layout,
    /// Variables of `G` (`layout.ell`).
    pub ell: usize,
}

/// Everything derived deterministically from a vk (Python
/// `keygen.Derived`): ROM, `s_1`/`s_2`, layout, `R_sh`/`R_st`. Python
/// caches this as `vk.derived`; `om_format::VerifyingKey` carries no
/// cache field, so callers build a `Derived` explicitly and reuse it.
#[derive(Debug)]
pub struct Derived {
    /// The verifying key this was derived from.
    pub vk: VerifyingKey,
    /// `cpu_circuit.Params(A, 2)`.
    pub cpu_params: cpu::Params,
    /// The expanded program (`bytecode.expand(code, entry_pc)`).
    pub program: Program,
    /// `program.rom`, rows indexed by micro-PC.
    pub rom: Vec<Row>,
    /// `N = |ROM|`.
    pub n_rom: usize,
    /// Bytecode Shout shape `a_B`.
    pub rom_a: usize,
    /// Bytecode Shout shape `d_B`.
    pub rom_d: usize,
    /// RAM Twist shape `a_R` (`choose_ad(A).0`, may exceed `A`).
    pub ram_a: usize,
    /// RAM Twist shape `d_R`.
    pub ram_d: usize,
    /// Witness segment layout (`cpu_circuit.layout`), 37 segments.
    pub segments: Vec<cpu::Segment>,
    /// Segment names in layout order.
    pub seg_names: Vec<&'static str>,
    /// Segment name -> layout index (its component id).
    pub seg_id: BTreeMap<&'static str, i64>,
    /// Spartan column bits `nu`.
    pub nu: usize,
    /// Spartan row bits `rho`.
    pub rho: usize,
    /// `[s_1 (B), s_2 (K)]` as sparse `R1CS(rho, nu)`.
    pub rels: Vec<R1CS>,
    /// The layout as Spartan segments (`id = index`, §6.5).
    pub spartan_segments: Vec<SpartanSegment>,
    /// `router.shift_entries(6)` (12512 entries).
    pub r_sh: Vec<(usize, usize, usize)>,
    /// `router.store_entries(6)` (512 entries).
    pub r_st: Vec<(usize, usize, usize, usize)>,
    /// ABI memory map.
    pub mm: MemoryMap,
    /// `cpu_circuit._rom_fields` of every ROM row.
    pub rom_fields: Vec<cpu::RomFields>,
}

impl Derived {
    /// Derive everything from `vk` (Python `Derived(vk)`).
    ///
    /// # Panics
    /// Panics if the (already validated) vk's memory map cannot be
    /// built, or on the `om-circuit` parameter asserts (`3 <= A <= 28`),
    /// as Python raises there.
    pub fn new(vk: &VerifyingKey) -> Derived {
        let cpu_params = cpu::Params {
            ram_log_words: vk.abi.ram_log_words,
            log_cycles: LOG_CYCLES,
        };
        let program = expand(&vk.code, vk.entry_pc);
        let rom = program.rom.clone();
        let n_rom = rom.len();
        let (rom_a, rom_d) = om_format::choose_ad(2.max((n_rom - 1).bit_length_usize()));
        let (ram_a, ram_d) = vk.ram_ad();
        let segments = cpu::layout(&cpu_params);
        let seg_names: Vec<&'static str> = segments.iter().map(|sg| sg.name).collect();
        let seg_id: BTreeMap<&'static str, i64> = segments
            .iter()
            .enumerate()
            .map(|(i, sg)| (sg.name, i as i64))
            .collect();
        let built = cpu::build(&cpu_params);
        let nu = (2 * cpu::num_w_cols(&cpu_params)).ilog2() as usize;
        let max_rows = built.s1.len().max(built.s2.len());
        let rho = if max_rows <= 1 {
            0
        } else {
            (usize::BITS - (max_rows - 1).leading_zeros()) as usize
        };
        let rels = vec![
            built.s1.to_r1cs(RelationField::B, rho, nu),
            built.s2.to_r1cs(RelationField::K, rho, nu),
        ];
        let spartan_segments = segments
            .iter()
            .enumerate()
            .map(|(i, sg)| SpartanSegment {
                seg_id: i as i64,
                kind: sg.kind,
                log_cols: sg.log_size,
                block: sg.offset >> sg.log_size,
            })
            .collect();
        let mm = memory_map(&vk.abi).expect("vk ABI parameters validated at construction");
        let rom_fields = rom.iter().map(cpu::rom_fields).collect();
        Derived {
            vk: vk.clone(),
            cpu_params,
            program,
            rom,
            n_rom,
            rom_a,
            rom_d,
            ram_a,
            ram_d,
            segments,
            seg_names,
            seg_id,
            nu,
            rho,
            rels,
            spartan_segments,
            r_sh: shift_entries(WORD_BITS),
            r_st: store_entries(WORD_BITS),
            mm,
            rom_fields,
        }
    }

    /// The per-`T` derivation (Python `Derived.instance`): Twist
    /// parameters, component list and ids, Mosaic layout.
    ///
    /// # Errors
    /// Returns [`KeyError`] unless `T` is a power of two in
    /// `[4, 2^40]`.
    pub fn instance(&self, t: u64) -> Result<Instance, KeyError> {
        if t < 4 || !t.is_power_of_two() || t > (1u64 << MAX_LOG_T) {
            return Err(KeyError::Key(format!(
                "T must be a power of two in [4, 2^{MAX_LOG_T}]"
            )));
        }
        let n = t.trailing_zeros() as usize;
        let s = n - LOG_CYCLES as usize;
        let reg = TwistParams::new("twist/reg", REG_A, REG_D, REG_P, n);
        let ram = TwistParams::new("twist/ram", self.ram_a, self.ram_d, 1, n);
        let mut comps: Vec<(String, usize)> = Vec::new();
        for x in ["ra0", "ra1", "wa"] {
            for i in 0..REG_D {
                comps.push((format!("twist/reg/{x}/{}", i + 1), REG_A / REG_D + n));
            }
        }
        comps.push(("twist/reg/inc".to_string(), WORD_BITS + n));
        for i in 0..self.ram_d {
            comps.push((
                format!("twist/ram/ra0/{}", i + 1),
                self.ram_a / self.ram_d + n,
            ));
        }
        comps.push(("twist/ram/inc".to_string(), WORD_BITS + n));
        for i in 0..self.rom_d {
            comps.push((
                format!("shout/bytecode/ra/{}", i + 1),
                self.rom_a / self.rom_d + n,
            ));
        }
        let mut ids: BTreeMap<String, i64> = self
            .segments
            .iter()
            .enumerate()
            .map(|(i, sg)| (sg.name.to_string(), i as i64))
            .collect();
        let nid0 = self.segments.len() as i64;
        for (j, (nm, _)) in comps.iter().enumerate() {
            ids.insert(nm.clone(), nid0 + j as i64);
        }
        for i in 0..self.ram_d {
            // RAM write address = read address (§7.9).
            let ra = ids[&format!("twist/ram/ra0/{}", i + 1)];
            ids.insert(format!("twist/ram/wa/{}", i + 1), ra);
        }
        let mut allc: Vec<(i64, usize)> = self
            .segments
            .iter()
            .enumerate()
            .filter(|(_, sg)| sg.kind == om_spartan::SegmentKind::Direct)
            .map(|(i, sg)| (i as i64, sg.log_size + s))
            .collect();
        allc.extend(comps.iter().map(|(nm, ls)| (ids[nm.as_str()], *ls)));
        let layout = compute_layout(
            &allc,
            if self.vk.pcs == PcsMode::Ligerito {
                8
            } else {
                0
            },
        );
        let ell = layout.ell;
        Ok(Instance {
            t,
            n,
            s,
            reg,
            ram,
            comps,
            ids,
            layout,
            ell,
        })
    }

    /// The Ligerito parameters for a `G` with `ell` variables (Python
    /// `Derived.ligerito_params`); delegates to
    /// `om_format::ligerito_params`, which ports the same derivation.
    ///
    /// # Errors
    /// Returns [`KeyError`] if `ell - 7 < 2` or the profile's shape is
    /// impossible.
    pub fn ligerito_params(&self, ell: usize) -> Result<LigeritoParams, KeyError> {
        Ok(om_format::ligerito_params(&self.vk, ell)?)
    }

    /// The `om_format::ProofShape` for `inst` (the quantities
    /// `decode_proof` reads off `Derived`/`Instance` in Python).
    pub fn proof_shape(&self, inst: &Instance) -> ProofShape {
        ProofShape {
            rho: self.rho,
            nu: self.nu,
            num_segments: self.segments.len(),
            rom_a: self.rom_a,
            rom_d: self.rom_d,
            ell: inst.ell,
        }
    }
}

/// `usize::bit_length` (Python `int.bit_length`).
trait BitLength {
    fn bit_length_usize(self) -> usize;
}

impl BitLength for usize {
    fn bit_length_usize(self) -> usize {
        (usize::BITS - self.leading_zeros()) as usize
    }
}
