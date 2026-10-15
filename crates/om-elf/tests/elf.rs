//! Port of `reference/tests/test_elf.py`, plus the remaining rejections
//! of spec 14.2 that Python's tests do not name (truncation, bad program
//! header table, segment outside the file, RVE/TSO, code-segment shape).

use std::collections::BTreeMap;

use om_elf::elf::PT_TLS;
use om_elf::{
    ElfError, PF_R, PF_W, PF_X, PT_GNU_STACK, PT_NOTE, Params, RAM_BASE, load, program_digest,
};

const P: Params = Params {
    ram_log_words: 12,
    input_log_words: 4,
    output_log_words: 4,
    max_code_words: 1 << 20,
    hash_profile: om_elf::Hasher::Sha256,
};
const ADDI: u32 = 0x0010_0093; // addi x1,x0,1
const ECALL: u32 = 0x0000_0073;
const TEXT: u64 = 0x1000_0000;

// Mirror of Python's make_elf.
struct ElfOpts {
    entry: u64,
    flags: u32,
    machine: u16,
    etype: u16,
    cls: u8,
    ph_extra: Vec<u32>,
}

impl Default for ElfOpts {
    fn default() -> Self {
        ElfOpts {
            entry: TEXT,
            flags: 0,
            machine: 243,
            etype: 2,
            cls: 2,
            ph_extra: Vec::new(),
        }
    }
}

/// segs: (vaddr, flags, data, memsz)
fn make_elf(segs: &[(u64, u32, Vec<u8>, u64)], opts: &ElfOpts) -> Vec<u8> {
    let (ehsize, phsize) = (64usize, 56usize);
    let nph = segs.len() + opts.ph_extra.len();
    let mut off = ehsize + phsize * nph;
    let mut body: Vec<u8> = Vec::new();
    let mut ph_bytes: Vec<u8> = Vec::new();
    for (vaddr, fl, data, memsz) in segs {
        ph_bytes.extend_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        ph_bytes.extend_from_slice(&fl.to_le_bytes());
        ph_bytes.extend_from_slice(&((off + body.len()) as u64).to_le_bytes());
        ph_bytes.extend_from_slice(&vaddr.to_le_bytes());
        ph_bytes.extend_from_slice(&vaddr.to_le_bytes());
        ph_bytes.extend_from_slice(&(data.len() as u64).to_le_bytes());
        ph_bytes.extend_from_slice(&memsz.to_le_bytes());
        ph_bytes.extend_from_slice(&8u64.to_le_bytes());
        body.extend_from_slice(data);
    }
    for t in &opts.ph_extra {
        ph_bytes.extend_from_slice(&t.to_le_bytes());
        ph_bytes.extend_from_slice(&[0u8; 44]);
        ph_bytes.extend_from_slice(&1u64.to_le_bytes()); // p_align; loader ignores it
    }
    let mut hdr = b"\x7fELF".to_vec();
    hdr.extend_from_slice(&[opts.cls, 1, 1, 0]);
    hdr.extend_from_slice(&[0u8; 8]);
    hdr.extend_from_slice(&opts.etype.to_le_bytes());
    hdr.extend_from_slice(&opts.machine.to_le_bytes());
    hdr.extend_from_slice(&1u32.to_le_bytes());
    hdr.extend_from_slice(&opts.entry.to_le_bytes());
    hdr.extend_from_slice(&64u64.to_le_bytes());
    hdr.extend_from_slice(&0u64.to_le_bytes());
    hdr.extend_from_slice(&opts.flags.to_le_bytes());
    hdr.extend_from_slice(&64u16.to_le_bytes());
    hdr.extend_from_slice(&56u16.to_le_bytes());
    hdr.extend_from_slice(&(nph as u16).to_le_bytes());
    hdr.extend_from_slice(&64u16.to_le_bytes());
    hdr.extend_from_slice(&0u16.to_le_bytes());
    hdr.extend_from_slice(&0u16.to_le_bytes());
    off = hdr.len() + ph_bytes.len();
    debug_assert_eq!(off, ehsize + phsize * nph);
    hdr.extend_from_slice(&ph_bytes);
    hdr.extend_from_slice(&body);
    hdr
}

fn code_seg(words: &[u32], vaddr: u64) -> (u64, u32, Vec<u8>, u64) {
    let d: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let n = d.len() as u64;
    (vaddr, PF_R | PF_X, d, n)
}

fn ok_segs() -> Vec<(u64, u32, Vec<u8>, u64)> {
    vec![code_seg(&[ADDI, ECALL], TEXT)]
}

#[test]
fn ok() {
    let data = (RAM_BASE, PF_R | PF_W, vec![1, 2, 3, 0, 0, 0, 0, 0, 9], 32);
    let mut segs = ok_segs();
    segs.push(data);
    let opts = ElfOpts {
        ph_extra: vec![PT_GNU_STACK],
        ..ElfOpts::default()
    };
    let img = load(&make_elf(&segs, &opts), &P).unwrap();
    assert_eq!(img.code, BTreeMap::from([(TEXT, ADDI), (TEXT + 4, ECALL)]));
    assert_eq!(img.entry_pc, TEXT);
    assert_eq!(img.ram_words, BTreeMap::from([(0, 0x03_02_01), (1, 9)]));
}

#[test]
fn unaligned_data_packing() {
    let mut segs = ok_segs();
    segs.push((RAM_BASE + 3, PF_R | PF_W, vec![0xaa, 0xbb], 2));
    let img = load(&make_elf(&segs, &ElfOpts::default()), &P).unwrap();
    assert_eq!(img.ram_words, BTreeMap::from([(0, 0xBBAA << 24)]));
}

#[test]
fn zero_memsz_load_skipped_and_note_ignored() {
    let mut segs = ok_segs();
    segs.push((0, PF_R, Vec::new(), 0)); // skipped before any range check
    let opts = ElfOpts {
        ph_extra: vec![PT_NOTE],
        ..ElfOpts::default()
    };
    let img = load(&make_elf(&segs, &opts), &P).unwrap();
    assert_eq!(img.code.len(), 2);
    assert!(img.ram_words.is_empty());
}

#[test]
fn errors() {
    let ok = ok_segs();
    let d = ElfOpts::default;
    let with_data = |seg: (u64, u32, Vec<u8>, u64)| {
        let mut s = ok.clone();
        s.push(seg);
        make_elf(&s, &d())
    };
    let two_data = {
        let mut s = ok.clone();
        s.push((RAM_BASE, PF_R, vec![b'x'; 16], 16));
        s.push((RAM_BASE + 8, PF_R, vec![b'y'], 1));
        make_elf(&s, &d())
    };
    let code_overlap = {
        let mut s = ok.clone();
        s.push(code_seg(&[ADDI, ECALL], TEXT));
        make_elf(&s, &d())
    };
    let cases: Vec<(&str, Vec<u8>, ElfError)> = vec![
        (
            "rvc",
            make_elf(&ok, &ElfOpts { flags: 1, ..d() }),
            ElfError::RvcFlag,
        ),
        (
            "float",
            make_elf(&ok, &ElfOpts { flags: 4, ..d() }),
            ElfError::FloatAbiFlag,
        ),
        (
            "rve",
            make_elf(&ok, &ElfOpts { flags: 8, ..d() }),
            ElfError::RveTsoFlag,
        ),
        (
            "tso",
            make_elf(&ok, &ElfOpts { flags: 0x10, ..d() }),
            ElfError::RveTsoFlag,
        ),
        (
            "machine",
            make_elf(&ok, &ElfOpts { machine: 62, ..d() }),
            ElfError::BadMachine,
        ),
        (
            "dyn",
            make_elf(&ok, &ElfOpts { etype: 3, ..d() }),
            ElfError::BadType,
        ),
        (
            "elf32",
            make_elf(&ok, &ElfOpts { cls: 1, ..d() }),
            ElfError::NotElf64LittleEndian,
        ),
        (
            "entry",
            make_elf(
                &ok,
                &ElfOpts {
                    entry: TEXT + 8,
                    ..d()
                },
            ),
            ElfError::BadEntryPoint,
        ),
        (
            "entry unaligned",
            make_elf(
                &ok,
                &ElfOpts {
                    entry: TEXT + 2,
                    ..d()
                },
            ),
            ElfError::BadEntryPoint,
        ),
        (
            "wx",
            make_elf(
                &[(TEXT, PF_R | PF_W | PF_X, ADDI.to_le_bytes().to_vec(), 4)],
                &d(),
            ),
            ElfError::ExecutableWritableSegment,
        ),
        (
            "code in ram",
            make_elf(
                &[code_seg(&[ADDI, ECALL], RAM_BASE)],
                &ElfOpts {
                    entry: RAM_BASE,
                    ..d()
                },
            ),
            ElfError::CodeSegmentOutOfRange,
        ),
        (
            "rvc insn",
            make_elf(&[code_seg(&[0x4501, ECALL], TEXT)], &d()),
            ElfError::Non32BitInstruction { addr: TEXT },
        ),
        (
            "data below ram",
            with_data((0x2000_0000, PF_R, b"x".to_vec(), 1)),
            ElfError::DataSegmentOutOfRange,
        ),
        (
            "data in io",
            with_data((RAM_BASE + 8 * (4096 - 32), PF_R, b"x".to_vec(), 1)),
            ElfError::DataSegmentOutOfRange,
        ),
        (
            "data past ram",
            with_data((RAM_BASE + 8 * 4096, PF_R, b"x".to_vec(), 1)),
            ElfError::DataSegmentOutOfRange,
        ),
        ("overlap", two_data, ElfError::OverlappingDataSegments),
        (
            "code overlap",
            code_overlap,
            ElfError::OverlappingCodeSegments,
        ),
        (
            "no code",
            make_elf(&[(RAM_BASE, PF_R, b"x".to_vec(), 1)], &d()),
            ElfError::NoExecutableSegment,
        ),
        (
            "bad pt",
            make_elf(
                &ok,
                &ElfOpts {
                    ph_extra: vec![2],
                    ..d()
                },
            ),
            ElfError::UnsupportedProgramHeaderType { p_type: 2 },
        ),
        (
            "pt_tls",
            make_elf(
                &ok,
                &ElfOpts {
                    ph_extra: vec![PT_TLS],
                    ..d()
                },
            ),
            ElfError::UnsupportedProgramHeaderType { p_type: PT_TLS },
        ),
        ("garbage", b"hello".to_vec(), ElfError::NotElf),
        ("empty", Vec::new(), ElfError::NotElf),
        (
            "big-endian",
            {
                let mut e = make_elf(&ok, &d());
                e[5] = 2;
                e
            },
            ElfError::NotElf64LittleEndian,
        ),
        (
            "bad magic",
            {
                let mut e = make_elf(&ok, &d());
                e[1] = b'X';
                e
            },
            ElfError::NotElf,
        ),
        (
            "phnum zero",
            {
                let mut e = make_elf(&ok, &d());
                e[56..58].copy_from_slice(&0u16.to_le_bytes());
                e
            },
            ElfError::BadProgramHeaderTable,
        ),
        (
            "phentsize wrong",
            {
                let mut e = make_elf(&ok, &d());
                e[54..56].copy_from_slice(&32u16.to_le_bytes());
                e
            },
            ElfError::BadProgramHeaderTable,
        ),
        (
            "phoff out of file",
            {
                let mut e = make_elf(&ok, &d());
                e[32..40].copy_from_slice(&0x1_0000u64.to_le_bytes());
                e
            },
            ElfError::ProgramHeadersOutOfFile,
        ),
        (
            "phoff overflow",
            {
                let mut e = make_elf(&ok, &d());
                e[32..40].copy_from_slice(&u64::MAX.to_le_bytes());
                e
            },
            ElfError::ProgramHeadersOutOfFile,
        ),
        (
            "filesz > memsz",
            with_data((RAM_BASE, PF_R, vec![1, 2, 3, 4], 2)),
            ElfError::FileszExceedsMemsz,
        ),
        (
            "segment out of file",
            {
                // Segment 1's p_offset (phdr field at 64 + 8) points past EOF.
                let mut e = make_elf(&ok, &d());
                e[72..80].copy_from_slice(&0x1_0000u64.to_le_bytes());
                e
            },
            ElfError::SegmentOutOfFile,
        ),
        (
            "code filesz != memsz",
            {
                let word = ADDI.to_le_bytes().to_vec();
                make_elf(&[(TEXT, PF_R | PF_X, word, 8)], &d())
            },
            ElfError::BadCodeSegmentShape,
        ),
        (
            "code vaddr unaligned",
            make_elf(
                &[code_seg(&[ADDI], TEXT + 2)],
                &ElfOpts {
                    entry: TEXT + 2,
                    ..d()
                },
            ),
            ElfError::BadCodeSegmentShape,
        ),
        (
            "code at 2^32",
            make_elf(
                &[code_seg(&[ADDI], 1 << 32)],
                &ElfOpts {
                    entry: 1 << 32,
                    ..d()
                },
            ),
            ElfError::CodeSegmentOutOfRange,
        ),
        (
            "data vaddr overflow",
            with_data((u64::MAX - 1, PF_R, vec![1, 2, 3, 4], 4)),
            ElfError::DataSegmentOutOfRange,
        ),
    ];
    for (name, blob, want) in cases {
        assert_eq!(load(&blob, &P), Err(want), "case {name}");
    }
}

#[test]
fn truncated_files() {
    let full = make_elf(&ok_segs(), &ElfOpts::default());
    // Every proper prefix is rejected (never a panic, never a partial load).
    for n in 0..full.len() {
        assert!(load(&full[..n], &P).is_err(), "prefix of {n} bytes loaded");
    }
}

#[test]
fn code_too_large() {
    let mut p = P;
    p.max_code_words = 1;
    assert_eq!(
        load(&make_elf(&ok_segs(), &ElfOpts::default()), &p),
        Err(ElfError::CodeTooLarge)
    );
}

#[test]
fn invalid_params_rejected() {
    let p = Params::new(6, 6, 3);
    assert_eq!(
        load(&make_elf(&ok_segs(), &ElfOpts::default()), &p),
        Err(ElfError::Abi(om_elf::AbiError::IoWindowTooLarge))
    );
}

#[test]
fn deterministic_digest() {
    let mut segs = ok_segs();
    segs.push((RAM_BASE, PF_R, vec![5], 8));
    let e = make_elf(&segs, &ElfOpts::default());
    let a = load(&e, &P).unwrap();
    let b = load(&e, &P).unwrap();
    assert_eq!(
        program_digest(&a.code, a.entry_pc, &a.ram_words, &P),
        program_digest(&b.code, b.entry_pc, &b.ram_words, &P)
    );
    // Known answer computed with reference/openmagnetar/abi.py for the
    // `ok` test's image under Params(12, 4, 4).
    let code = BTreeMap::from([(TEXT, ADDI), (TEXT + 4, ECALL)]);
    let ram = BTreeMap::from([(0usize, 0x03_02_01u64), (1, 9)]);
    let hex: String = program_digest(&code, TEXT, &ram, &P)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    assert_eq!(
        hex,
        "28d6f9b559fef2d1675fd8f1e3f880bab8d6e561e424127f207ee965da20d814"
    );
}
