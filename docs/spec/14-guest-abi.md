# 14. Guest ABI and toolchain

**Status:** draft · **Paper:** —

## Scope
How guest programs are built for strict RV64I (Rust custom target JSON with
build-std on nightly; C via clang -march=rv64i -mabi=lp64), entry point,
memory map (code, data, stack, heap, input, output regions), syscalls,
termination, and the host SDK API.

## Resolved questions

1. **Rust target.** **[OM-choice]** A custom target JSON shipped in `guest/rust/riscv64i-open-magnetar-none-elf.json`, built with `-Zbuild-std=core,alloc,compiler_builtins -Zbuild-std-features=compiler-builtins-mem`. Rationale: no upstream target is strict RV64I without `M`/`C`; compiler_builtins supplies `__muldi3`, `__udivdi3` and similar as libcalls, so no `M` instructions are needed.
2. **Atomics and std.** **[OM-choice]** `no_std` + `alloc` only in v1, with a bump allocator that never frees and lives between `__heap_start` and `__heap_end`. The target sets `max-atomic-width = 0`, `atomic-cas = false`, single-threaded.
3. **I/O model.** **[OM-choice]** Both regions are memory-mapped. The input is part of `M_0`; the output is checked by the final-memory claim (C6). The "digest computed by the verifier" proposal is dropped: the verifier works with the raw input and output bytes, because it must evaluate `M̃_0` (input part) and the expected output MLE itself. The only digest is the program digest (14.3).

## Specification

Items marked **(normative)** bind the prover, verifier and reference model. Items marked **(informative)** describe the supplied tooling; any toolchain that produces an ELF accepted by 14.2 is conformant.

### 14.1 Parameters and memory map (normative)

Verifying-key parameters (all `[OM-choice]` defaults in brackets):

| Name | Meaning | Default |
|---|---|---|
| `A` | RAM has `2^A` words (C5) | 20 |
| `I` | input region has `2^I` words | 12 |
| `O` | output region has `2^O` words | 8 |
| `MAX_CODE` | maximum number of instructions | 2^20 |

Constraints: `1 <= I, O` and `max(I,O) + 1 <= A`. **[OM-choice]** `I` and `O` are verifying-key parameters, not per-proof: the final-memory claim and the output subcube have a fixed shape, which keeps the key, the circuit's public-input layout and the proof format fixed-size. A program that needs a larger region is run under another key. The key also fixes `A` and `MAX_CODE` (section 12 serializes them) and the hash profile.

Let `M = max(I, O)` and `N = 2^A`. All positions below are RAM word indices `w` (byte address `RAM_BASE + 8w`):

```
  0 .. D                       data: .rodata, .data, .bss    (D = end of bss, rounded up to a word)
  D .. S                       heap, growing up              (S = in_base - STACK_SIZE)
  S .. in_base                 stack, growing down; initial sp = RAM_BASE + 8*in_base
  in_base  = N - 2^(M+1)       input region,  2^I words (aligned to 2^I)
  out_base = in_base + 2^M     output region, 2^O words (aligned to 2^O)
```

`in_base` and `out_base` are multiples of `2^M`, so both regions are aligned power-of-two blocks. In the MLE of RAM the output region is the subcube with the `A - O` high variables fixed to `out_base >> O`. **[OM-choice]** The input region comes first and the output region second, both at the top of RAM, so that the stack can sit directly below them and both regions are aligned whatever `I` and `O` are. Unused words in the `2^M` window are always zero. `STACK_SIZE` is a tooling choice (default 64 KiB); the protocol only requires data segments to lie below `in_base` (14.2).

The initial register file is all zero (section 09) except that the runtime sets `sp` itself. The loader does not set registers.

**Addressing note (normative consequence of C5).** `RAM_BASE = 2^31`. On RV64, `lui` sign-extends, so `lui+addi` cannot form addresses `>= 2^31`. Guests MUST address RAM pc-relatively (`auipc`; LLVM code model `medium` / `-mcmodel=medany`). Code lives at addresses below `2^31`, so a pc-relative offset to RAM stays within +/- 2 GiB.

**Input encoding (normative).** For input bytes `x` of length `n`, region word 0 is `n` and word `1 + j` is `sum_{b<8} x[8j+b] << 8b` (little-endian, zero padded) for `j < ceil(n/8)`. All other words of the region are zero. Requires `1 + ceil(n/8) <= 2^I`. The guest reads the length word and then bytes with `lbu` (or `ld` if it likes).

**Output encoding (normative).** Same encoding with `O` in place of `I`. The output region is zero in `M_0`. At HALT the region MUST hold the *canonical* encoding of the public output bytes: the length word, the packed bytes, and zeros in every other word including padding bytes. A guest that writes anything else cannot produce a verifying proof for any claimed output. The supplied runtime only appends, which keeps the encoding canonical.

### 14.2 ELF loading (normative)

`load(elf_bytes, params) -> (code, entry_pc, m0_program)` where `code` maps `pc -> u32` instruction word, `entry_pc` is an integer, and `m0_program` maps RAM word index `-> u64` and lists only non-zero words. The procedure is exact and deterministic. Any failed check rejects the file (no partial result).

1. Header: magic `\x7fELF`; `EI_CLASS = 2` (ELF64); `EI_DATA = 1` (little-endian); `e_type = ET_EXEC (2)`; `e_machine = 243` (EM_RISCV). `e_flags` MUST have none of: RVC (bit 0), float ABI (bits 1-2), RVE (bit 3), TSO (bit 4). `e_phentsize = 56`, `e_phnum >= 1`, and the program header table lies inside the file. Section headers are ignored.
2. Program headers are processed in table order. `PT_NULL`, `PT_NOTE`, `PT_PHDR`, `PT_GNU_STACK` and `PT_RISCV_ATTRIBUTES` are ignored. Any other non-`PT_LOAD` type (`PT_DYNAMIC`, `PT_INTERP`, `PT_TLS`, ...) is rejected. A `PT_LOAD` with `p_memsz = 0` is skipped. Otherwise `p_filesz <= p_memsz` and the file bytes lie inside the file. A segment with both `PF_X` and `PF_W` is rejected.
3. **Executable segment** (`PF_X`): `p_vaddr` and `p_memsz` are multiples of 4, `p_filesz = p_memsz`, the range lies inside `[0, 2^32)` and does not intersect RAM. Each little-endian 32-bit word `w` at `p_vaddr + 4k` goes into `code`; `w mod 4` MUST be 3 (this rejects RVC halfwords and non-32-bit encodings). Code segments MUST NOT overlap. Code is not placed in RAM (Harvard, C5).
4. **Data segment** (no `PF_X`, whether `PF_W` or read-only): the byte range `[p_vaddr, p_vaddr + p_memsz)` MUST lie within `[RAM_BASE, RAM_BASE + 8*in_base)` (inside RAM, below the stack and I/O window) and MUST NOT overlap another data segment. File bytes are placed at `p_vaddr`; bytes from `p_filesz` to `p_memsz` (bss) are zero. Bytes are packed into words by C5 (byte `a` goes to word `(a - RAM_BASE) >> 3`, bits `8(a & 7)`..). Read-only data must be in RAM because loads read RAM; the CPU circuit has no instruction-fetch path to data, and conversely stores to "read-only" data are not prevented in v1 (the flag has no effect past loading).
5. After all segments: `code` MUST be non-empty with at most `MAX_CODE` entries; `entry_pc = e_entry` MUST be a multiple of 4 and a key of `code`. Zero words are dropped from `m0_program`.

Whether each instruction word is a valid RV64I instruction is decided by section 09's decoder, not by the loader; a program containing a reachable invalid instruction is unprovable, while an unreachable one is permitted in `code`.

### 14.3 Public instance and program digest (normative)

The prover and verifier agree on the verifying key, which contains the parameters of 14.1 and the program digest. The public instance of a claim is `(program_digest, input, output, exit_code)`:

- `program_digest = H(DOMAIN || A || I || O || MAX_CODE || entry_pc || |code| || sorted (pc, word)* || |m0| || sorted (w, v)*)`, where `DOMAIN = "open-magnetar/program/v1"`; `A, I, O` are single bytes; all other integers are 8-byte little-endian (instruction words 4 bytes); `H` is the configured hash (C4); and `m0` lists only non-zero words of the program's data image **excluding** the input region. (`reference/openmagnetar/abi.py: program_digest`.)
- `input` and `output` are byte strings; `exit_code` is the 64-bit value of `a0` at HALT.

**Inputs.** The verifier reconstructs `M_0 = m0_program ∪ input_words(input)` (14.1 encoding; the input region is disjoint from the data image by 14.2 step 4). `M̃_0` is evaluated in time linear in its non-zero words, as C6 states. Section 11 binds `program_digest` to the committed bytecode table and the program part of `M_0`.

**Outputs.** The verifier computes the expected output-region bit table: bit `o` of region word `u` sits at index `o + 64u` (C2, C5), a table of `2^(O+6)` bits, and evaluates its MLE at the point supplied by section 07 (length `O + 6`, `x_1` the in-word bit LSB). This is `abi.expected_output_mle_eval(output, params, r)`. It is compared with the final-memory claim restricted to the output subcube. If section 07 uses a different bit/word flattening, only that helper changes. The verifier MUST reject an output whose canonical encoding does not fit (`1 + ceil(m/8) > 2^O`). `exit_code` is checked by the CPU circuit's HALT cycle (section 10).

### 14.4 Syscalls and termination (normative)

Only HALT (C6). The runtime writes the output region, then executes `li a7, 0; ecall` with `a0` = exit code. `ECALL` with any other `a7`, `EBREAK`, `FENCE`-class system behaviour that section 09 leaves unprovable, and falling off the code are unprovable. Returning from `main` in `start.S` executes HALT with the return value as `a0`.

### 14.5 Toolchains (informative)

- **Rust.** Target JSON `guest/rust/riscv64i-open-magnetar-none-elf.json`: `llvm-target = riscv64`, `features = "-m,-a,-f,-d,-c,-zicsr,-zifencei"` (the `+e` RVE feature is not used), `llvm-abiname = lp64`, `max-atomic-width = 0`, `atomic-cas = false`, `panic-strategy = abort`, `relocation-model = static`, `code-model = medium`, `relax = false`, standard riscv64 data layout. Build: `cargo +nightly build --release --target guest/rust/riscv64i-open-magnetar-none-elf.json -Zbuild-std=core,alloc,compiler_builtins -Zbuild-std-features=compiler-builtins-mem`, linked with `guest/link.ld`. The Rust runtime crate (entry, panic handler, bump allocator, I/O helpers) is not yet written. The target is untested.
- **C.** `clang --target=riscv64 -march=rv64i -mabi=lp64 -mcmodel=medany -mno-relax -nostdlib -ffreestanding`. `-mno-relax` is needed because relaxation can introduce `gp`-relative code; `-mcmodel=medany` for the addressing note in 14.1.
- **Linker script** `guest/link.ld`: `.text` at `0x1000_0000` (outside RAM, `PT_LOAD` R+X); `.rodata/.data/.bss` from `RAM_BASE` (`PT_LOAD` R+W). Symbols `__stack_top`, `__input_base`, `__output_base`, `__stack_size` are supplied by the Makefile from `A, I, O`, via `--defsym`. This couples a build to a verifying key's `A, I, O`. A binary built for one `(A, I, O)` is only valid under that key.
- **Runtime** `guest/rt/start.S` sets `sp`, calls `main`, and halts with the return value; bss zeroing is optional (`OM_ZERO_BSS`) because RAM is zero in `M_0`. `guest/rt/om.h` gives `om_input_len`, `om_input`, `om_read_u64`, `om_write`, `om_write_u64`.
- **Example** `guest/examples/fib.c` and `guest/Makefile`.
- **Status.** No RISC-V-capable `clang`/`lld` was available in the environment where this was written (`clang --print-targets` lists no riscv). The C toolchain files, Makefile and Rust target JSON are therefore **untested**. The ELF loader is tested against ELF files built in the unit tests.

### 14.6 Bounds and faults (normative)

- Code: at most `MAX_CODE` instructions; code addresses below `2^32`.
- RAM: `2^A` words. Any access outside `[RAM_BASE, RAM_BASE + 8*2^A)` is unprovable (C5). Misaligned access is unprovable.
- **Stack overflow.** The stack is not guarded. If it grows below `RAM_BASE` the access is out of range and the program is unprovable. If it only runs into the heap or data it silently corrupts them, and the proof is still valid for that (wrong) execution. Running into the I/O window from below is not possible, since the stack grows down from `in_base`; a runaway heap into the stack is likewise unchecked. `__heap_end` lets the bump allocator fail instead.
- Trace length: executions longer than the key's maximum `T` are unprovable (section 10/13).

## Reference model

- `reference/openmagnetar/abi.py`: `Params`, `memory_map`, `encode_region`/`decode_region` (canonical, rejects non-canonical), `input_words`, `build_m0`, `extract_output`, `output_region_bits`, `expected_output_mle_eval` (lazy `mle.mle_eval`), `program_digest`, `PublicInstance`. The default `Params` mirror 14.1.
- `reference/openmagnetar/elf.py`: `load(elf_bytes, params) -> (code, entry_pc, ram_words)` and `ElfError`. Feeds `riscv.Machine(code, entry_pc, ram_words, ram_log_words)` after `abi.build_m0`.
- Tests: `reference/tests/test_elf.py`, `reference/tests/test_abi.py`.

## Requests to other sections

- **07 (Twist/Shout):** the final-memory claim for the output subcube must use the layout `index = o + 64*u` (bit index low) with point length `O+6`, or tell 14 the layout to change `expected_output_mle_eval`. Note `out_base` and `O` for fixing the high variables.
- **09/10:** confirm the initial register file is all zero and that HALT exposes `a0` as a public `exit_code`; confirm `Machine.__init__` accepts `ram_words` as non-zero-only sparse dict and that the pc keys of `code` are byte addresses.
- **11/12:** the verifying key carries `A, I, O, MAX_CODE`, the hash profile and `program_digest` as defined in 14.3.
- **CONVENTIONS (C6):** may cite 14.1 for the I/O region layout.

## Integration notes

* **Output MLE layout.** 11 does not call `abi.expected_output_mle_eval`. The final-memory claim of 07 7.6 evaluates the public output words in 07's own layout
  (`k_low + 2^m·o`, word index low, bit index high) inside `twist_verify`, from `final.words = abi.encode_region(output, O)`. The helper with layout `o + 64u`
  and point order `(bit, word)` is kept (tested) but is informative only; if a Rust implementation prefers it, 07's table order must be changed with it.
* The verifying key carries `A, I, O, MAX_CODE`, the hash profile and `program_digest` (12.2); it also carries the code and data images so that the verifier derives the ROM and `M_0` (11.2).
