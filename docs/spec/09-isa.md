# 09. ISA, virtual instructions and bytecode

**Status:** draft · **Paper:** §2.1, §5 (the paper gives no expansion tables; everything marked **[OM-choice]** is ours)

## Scope
Supported RV64I instructions and their exact semantics; ECALL/EBREAK handling; the virtual instruction set;
the deterministic expansion of each RV64I instruction into virtual instructions; the micro-PC; the bytecode
table ROM (its columns and encoding); virtual registers.

Reference model: `reference/openmagnetar/riscv.py` (decoder, plain interpreter, the oracle) and
`reference/openmagnetar/bytecode.py` (columns, `expand`, `datapath`, `VirtualMachine`).

## 9.1 RV64I semantics (normative)

Semantics are those of *The RISC-V Instruction Set Manual, Volume I: Unprivileged ISA*, RV64I base
(chapter "RV64I Base Integer Instruction Set"; chapter 2 for the RV32I subset it extends). Values are
`u64`; `sext32(x)` is the sign extension of bits 31..0; `s64` is the two's-complement view.

| Class | Instructions | Semantics |
|---|---|---|
| U | `LUI rd,imm` | `rd = sext32(imm20 << 12)` |
| U | `AUIPC rd,imm` | `rd = pc + sext32(imm20 << 12)` (mod 2^64) |
| J | `JAL rd,off` | `rd = pc + 4; pc = pc + off` |
| I | `JALR rd,rs1,imm` | `t = (rs1 + imm) & ~1; rd = pc + 4; pc = t` (rs1 is read before rd is written) |
| B | `BEQ BNE BLT BGE BLTU BGEU` | `pc = pc + off` if the comparison holds (signed for BLT/BGE) else `pc + 4` |
| load | `LB LH LW LD LBU LHU LWU` | `rd = ext(mem[rs1 + imm])`, sign-extended for `LB LH LW`, zero-extended for `LBU LHU LWU`, `LD` full word |
| store | `SB SH SW SD` | `mem[rs1 + imm] = rs2` truncated to the width |
| OP-IMM | `ADDI SLTI SLTIU XORI ORI ANDI` | `imm` is sign-extended to 64 bits; `SLTIU` compares unsigned against the sign-extended imm |
| OP-IMM | `SLLI SRLI SRAI` | 6-bit `shamt` (instruction bits 25:20, funct6 = 0 / 0b010000) |
| OP | `ADD SUB SLL SLT SLTU XOR SRL SRA OR AND` | shifts use `rs2[5:0]` |
| OP-IMM-32 | `ADDIW SLLIW SRLIW SRAIW` | 32-bit operation, result sign-extended; shamt 5 bits, instruction bit 25 must be 0 |
| OP-32 | `ADDW SUBW SLLW SRLW SRAW` | 32-bit operation on the low halves, result `sext32`; shifts use `rs2[4:0]` |
| MISC-MEM | `FENCE` | **NOP** (single-hart, no I/O ordering to preserve) |
| SYSTEM | `ECALL` | HALT iff `a7 (x17) = 0`, exit code `a0 (x10)`; any other `a7` is unprovable (C6) |
| SYSTEM | `EBREAK` | unprovable (C6) |

Writes to `x0` are discarded. Reading `x0` gives 0.

**Unprovable conditions (`Trap` in the model).** Illegal or unsupported encodings (anything not in the table:
`FENCE.I` and CSR instructions, the M/A/F/D/C extensions, reserved funct fields); `EBREAK`; `ECALL` with
`a7 != 0`; a misaligned load/store (address not a multiple of the access size, C5); a load/store outside
`[RAM_BASE, RAM_BASE + 8*2^A)`; a fetch from a pc that is not in the code image (including a jump or branch
target that is not 4-aligned or not in the code, and falling off the end of the code). The model raises
`Trap`; a prover MUST NOT produce a proof for such an execution, and the circuit makes it impossible (10.8).

**[OM-choice] `FENCE.I` is illegal.** It belongs to Zifencei, not RV64I; the guest toolchain never emits it.

**[OM-choice] one deviation of the proof system from the plain interpreter.** A load whose destination is
`x0` is expanded to a NOP (9.4), so a misaligned or out-of-range load into `x0` is not detected by the proof
system, whereas `riscv.Machine` traps. This costs nothing (the access has no architectural effect) and keeps the
invariant of 9.3 that every row with `rd = 0` has all result gates zero. Programs from the guest toolchain
never do this. The cross-check tests do not generate such programs.

## 9.2 Machine model recap

C5/C6 apply. The state is `(upc, regs[64], ram)` with 32 architectural registers and 32 virtual registers
(indices 32..63); only register index 32 (`TEMP_REG`) is used by the expansion. A virtual cycle reads
`rs1`, `rs2`, then writes `rd` (register Twist, `p = 2`), reads and then writes one RAM word (RAM Twist, `p =
1`), and fetches the ROM row at `upc`. RAM is word addressed; the 64-bit byte address is the adder output
`rs1 + imm` (10.5).

## 9.3 The virtual instruction set

A **virtual instruction is a ROM row**. The circuit (section 10) is one fixed datapath; the row's columns
steer it. There is no opcode field: the columns are the decoded control signals. This is the paper's
"decoded instruction fetched from the table".

Datapath semantics of one row (`bytecode.datapath` is the executable form; `r.x` is column `x`, `v1 = reg[rs1]`,
`v2 = reg[rs2]`, `rw` = RAM word read):

```
Bop  = r.b_imm ? r.imm : v2
S    = v1 + (Bop xor (r.sub ? 2^64-1 : 0)) + r.sub          (64-bit adder; carry-out cout)
Sp   = r.w ? sext32(S) : S
X    = v1 xor Bop            AND = v1 and Bop
T    = (r.c_add ? Sp : 0) xor (r.e ? X : 0) xor (r.g ? AND : 0)
cond = r.sh_imm xor (xor_k (r.bsel_k and v2[k]))             (bsel is one-hot or zero)
Y    = shift(r.Q_hi kind, r.Q_lo amount, v1)    or 0 if Q_lo/Q_hi are zero        (C7)
Gs   = cond ? (Sp xor Y) : 0
ltu  = not cout ;  cmp = (r.f_cmp and ltu) xor (r.f_lts and (v1[63] xor Bop[63]))
eq   = (S == 0)
take = r.br and (cmp xor (r.f_eq and eq) xor r.inv)
off  = S[2:0] ;  x3 = rw >> (8*off)
L    = (x3 and lanes(r.ln)) xor ((sign ? lanes(r.fill) : 0)),  sign = (ldsb and x3[7]) xor (ldsh and x3[15]) xor (ldsw and x3[31])
rd_val = T xor Gs xor L xor (r.g_slt and cmp) xor r.kc
new RAM word (stores) = routing of (rw, v2) by width r.st_w and offset off  (C7); otherwise unchanged
next upc = r.jalr ? upc_of_pc[(S and ~1)] : take ? r.tgt : r.seq
```

Notes. (i) `rd_val` is the *only* thing written, to register `r.rd` (index 0 means "no write"; the circuit forces
`rd_val = 0` through the gates, so the register increment is zero, C5). (ii) Immediate shifts and the stages of
register-amount shifts both use `c_add = 1` with `imm = 0`, so that `Sp = v1`: with `cond = 1` the result is
`Sp xor (Sp xor Y) = Y`, with `cond = 0` it is `Sp`. (iii) `w = 1` in a shift stage makes the "not shifted"
branch `sext32(v1)`, which normalizes word shifts (9.4). (iv) The RAM address is meaningful only when `r.mem`.

**Invariant (ROM well-formedness, verified by the verifier's derivation 9.7).** Every row with `rd = 0` has
`c_add = e = g = g_slt = sh_imm = bsel = ln = fill = kc = 0` and `Q_lo = Q_hi = 0`; hence `rd_val = 0`.
Every row with `mem = 0` has `ln = fill = st_w = a_* = 0`; every row with `mem = 1` has `b_imm = 1, sub = 0`.

### 9.3.1 Virtual instruction classes (what a row means)

| Class | Columns set (besides `rs1,rs2,rd,imm,kc,seq,tgt`) | Effect |
|---|---|---|
| `NOP` | none | nothing |
| `ADD/ADDW` (reg or imm via `b_imm`) | `c_add` (`w` for `ADDW/ADDIW`) | `rd = rs1 + B` |
| `SUB/SUBW` | `c_add, sub` (`w`) | `rd = rs1 - rs2` |
| `XOR`, `OR`, `AND` | `e` / `e,g` / `g` | bitwise (`OR = X xor AND`) |
| `SLT`, `SLTU` | `sub, f_lts/f_ltu, f_cmp, g_slt` | `rd = (rs1 < B)` |
| `SHIFT` (static) | `c_add, b_imm, sh_imm, Q_lo, Q_hi` | `rd = shift(kind, amt, rs1)` |
| `SHSTAGE k` | `c_add, b_imm, bsel = 1<<k, Q_lo = 2^k, Q_hi` (`w` for word kinds) | `rd = bit k of rs2 ? shift(kind, 2^k, rs1) : rs1` |
| `CONST` | `kc` | `rd = kc` (LUI, AUIPC, link address) |
| `LOAD` | `mem, b_imm, imm, ln, fill, ld*, a_*` | `rd = extract(ram[(rs1+imm)>>3])` |
| `STORE` | `mem, b_imm, imm, st_w, a_*` | `ram[...] = route(old, rs2)` |
| `BRANCH` | `sub, br, inv, f_eq/f_lts/f_ltu/f_cmp, tgt` | next upc = `tgt` if taken else `seq` |
| `JUMP` (JAL) | `kc`, `seq = target upc` | link in `rd`, static jump |
| `JUMPI` (JALR) | `b_imm, imm, kc, jalr` | link in `rd`, dynamic jump to `upc_of_pc[(rs1+imm)&~1]` |
| `HALT` | `ecall, rs1 = 10, rs2 = 17, seq = HALTED` | requires `x17 = 0` |
| `HALTED` | `halted, rs1 = 10` | padding row, loops on itself, binds the exit code |
| `TRAP` | `trap` | unsatisfiable: the circuit requires `trap = 0` |

## 9.4 Expansion of RV64I into virtual instructions (normative)

`bytecode.expand_instr` is the executable form.

| RV64I | Virtual rows | Cycles |
|---|---|---|
| `ADDI SLTI SLTIU XORI ORI ANDI ADDIW`, `ADD SUB SLT SLTU XOR OR AND ADDW SUBW` | 1 ALU row (rd = `x0` → NOP) | 1 |
| `LUI`, `AUIPC` | `CONST` with `kc = sext32(imm<<12)` / `pc + imm` (static: `pc` is public) | 1 |
| `JAL` | `JUMP`, `kc = pc+4` (0 if rd = x0), `seq =` head upc of `pc+off` (TRAP row if absent/misaligned) | 1 |
| `JALR` | `JUMPI` | 1 |
| `BEQ … BGEU` | `BRANCH`, `seq =` head of `pc+4`, `tgt =` head of `pc+off` | 1 |
| `LB LH LW LD LBU LHU LWU` | 1 `LOAD` (rd = x0 → NOP) | 1 |
| `SB SH SW SD` | 1 `STORE` | 1 |
| `SLLI SRLI SRAI SLLIW SRLIW SRAIW` | 1 `SHIFT` (kinds SLL, SRL, SRA, SLLW, SRLW, SRAW; amount = shamt) | 1 |
| `SLL SRL SRA` | 6 `SHSTAGE`, k = 0..5 | 6 |
| `SLLW SRLW SRAW` | 5 `SHSTAGE`, k = 0..4, `w = 1` | 5 |
| `FENCE` | 1 `NOP` | 1 |
| `ECALL` | 1 `HALT` row (then the `HALTED` row 0) | 1 |
| `EBREAK`, illegal encodings | 1 `TRAP` row | 1 |

**Sub-word loads (1 cycle, no expansion).** The row reads the *aligned* 64-bit word `ram[(rs1+imm)>>3]`; the
circuit extracts and sign-extends in-circuit (10.6). The byte offset is `(rs1+imm) & 7`; alignment is enforced by
the `a_h, a_w, a_d` flags.

**Sub-word stores (1 cycle).** The store router (08) consumes the old word, `rs2`, the one-hot `st_w` and the
offset (10.7). No read-modify-write expansion is needed.

**Register-amount shifts.** Stage `k` computes `t_{k+1} = bit_k(rs2) ? shift(t_k, 2^k) : t_k` where
`shift` is a static routing of C7 with amount `2^k` and `bit_k(rs2)` is selected from the register read value by
the one-hot `bsel` (10.4). Stage 0 reads `rs1`; stages 1.. read the virtual register 32; stage `k < last` writes
register 32; the last stage writes `rd`. All stages read `rs2` (unchanged until the last write, and the last
stage reads before it writes), so `rd = rs1` or `rd = rs2` is correct.

**[OM-choice] cycle counts of register shifts: 6 for the 64-bit forms, 5 for the word forms.** A
routing is chosen by the bytecode row, never by a register value, so each cycle can apply one static amount;
the amount `rs2[5:0]` has six bits, so six conditional stages are necessary in this scheme and a radix-4 stage
would need a 4-way dynamic choice among routings, which the router cannot do. The word forms need only five
stages (amount `rs2[4:0]`) because every stage has `w = 1`: the "not shifted" branch is `sext32(rs1)`, so the
normalization (`SEXT32`) that SLLW/SRLW/SRAW otherwise need is free, and the word kinds `SLLW/SRLW/SRAW`
(C7 kinds 3..5, `amt < 32`) are used per stage. Correctness for `SRLW` with amount 0 and bit 31 set: every
stage outputs `sext32(...)` of its input, so the result is `sext32(rs1[31:0])` as required. Rejected
alternatives: (a) a prefix `ZEXT32/SEXT32` row: one cycle worse; (b) two-bit stages: needs a data-dependent
routing; (c) a "mux router" (a third BinaryRouter whose selector is a register bit): extra sum-check and
committed selector for a rare instruction. Compilers emit register-amount shifts rarely compared with
immediate shifts, so the six-cycle cost is accepted.

**Fibonacci calibration.** A Fibonacci step `t = a + b; a = b; b = t` plus counter decrement and loop branch
is `add, addi, addi, addi, bne` = 5 single-cycle rows in this expansion; the paper counts 6 virtual cycles
for its step (its loop body is unspecified). Both agree that ordinary instructions are one cycle. The test
`test_fibonacci` checks that every instruction of that loop is exactly one cycle.

## 9.5 Micro-PC conventions

* The micro-PC `upc` is a 32-bit row index of the ROM.
* **`upc = 0` is the `HALTED` row** and **`upc = 1` is the `TRAP` row**; instruction rows follow in increasing
  `pc` order, the rows of one instruction contiguous. `Program.upc_of_pc[pc]` is the *head* (first) row.
* **Entry**: `entry_upc = upc_of_pc[entry_pc]` is public (section 10, `init`).
* **Halted**: the `HALT` row (`ecall = 1`) has `seq = 0`. The `HALTED` row has `seq = 0`, `rs1 = 10` (it
  reads `a0` every cycle, which is unchanged after HALT), `rd = 0`, no memory access. It is the only row
  with `halted = 1`. After HALT the trace is padded with `HALTED` cycles up to the power-of-two length `T`
  (`T >= 4`, and at least one `HALTED` cycle exists because the final cycle must be `HALTED`).
* **`TRAP`**: the `trap` flag makes the row unsatisfiable. Branches and jumps to a pc with no head row, an
  illegal instruction, `EBREAK`, and falling off the code end all lead to (or are) `TRAP` rows.
* The `seq` of the last row of an instruction is the head of `pc + 4`; for the last instruction of the code it
  is `TRAP` (falling off the end is unprovable).
* A virtual cycle that is not a head row is never a valid target for `JALR` (the circuit checks `head = 1`, 10.4).

## 9.6 The bytecode ROM (normative interface to 07 and 10)

The ROM has `N = 2 + (number of rows)` rows (the Shout table size is padded to a power of two by 07). Each row has
the columns below. `Width` is the number of bits; vector columns hold bit `i` at bit `i` of the integer. The
column order is `bytecode.COLUMNS`; this order is also the order in which section 07 concatenates the
columns of a read value (07 chooses how to pack them into Shout claim groups).

| Column | Width | Meaning |
|---|---|---|
| `upc` | 32 | the row index (an identity column, authenticated like any other) |
| `rpc` | 64 | the RV64I `pc` of the row's instruction (0 for `HALTED` and `TRAP`) |
| `rs1`, `rs2`, `rd` | 6, 6, 6 | register indices (0..63; 32 = the virtual temp). These are the *only* columns with no segment in `W`: register Twist (07) discharges its address claims directly against them (Construction 3, step 3) |
| `imm` | 64 | sign-extended immediate (ALU B operand, address offset); for static shifts it is 0 |
| `kc` | 64 | constant result (LUI, AUIPC, `pc+4` link) |
| `seq` | 32 | next micro-PC if not taken / not indirect |
| `tgt` | 32 | next micro-PC if a branch is taken |
| flags (1 bit each, `FLAG_NAMES` order) | 26 | `head halted ecall trap b_imm sub w c_add e g f_ltu f_lts f_cmp g_slt f_eq br inv sh_imm mem a_h a_w a_d jalr ldsb ldsh ldsw`, meanings in `bytecode._flags()` |
| `bsel` | 6 | one-hot (or zero): which bit of `rs2` conditions a shift stage |
| `ln`, `fill` | 8, 8 | load: byte lanes copied from the extracted word / filled with the sign |
| `st_w` | 4 | store width one-hot `{SB, SH, SW, SD}` (router `Q_st`); zero on non-stores (C7) |
| `Q_lo` | 64 | one-hot shift amount 0..63 (router `Q_lo`), all zero if no shift (C7) |
| `Q_hi` | 8 | one-hot shift kind 0..7 (router `Q_hi`), all zero if no shift (C7) |

Total width 430 bits per row. The shift selector is `Q_sh(h, j) = Q_lo(h_lo, j) · Q_hi(h_hi, j)` exactly as in C7.
Routings with invalid amounts are never emitted by `expand`. The store routing uses `st_w` and the three low bits
of the address (10.7).

## 9.7 How the verifier derives the ROM deterministically

Input: the code image `{pc -> 32-bit word}` and `entry_pc` produced by the section-14 ELF loader (executable
`PT_LOAD` segments, 4-byte instruction words at 4-aligned `pc`, a verifying-key bound `MAX_CODE`). Derivation:

1. Decode every word in ascending `pc` with the strict decoder (9.1); undecodable words decode to `ILLEGAL`.
2. Compute the row count of each instruction (table 9.4; it depends only on the instruction, and `rd = 0`
   cases, not on any other context).
3. Assign head micro-PCs: `HALTED = 0`, `TRAP = 1`, then consecutive.
4. Emit the rows (`expand`), resolving branch/jump targets through `upc_of_pc` (missing or misaligned target →
   `TRAP`).

The result depends only on the code image and `entry_pc`; the program digest of section 14 commits to
the image. The verifier evaluates `Val~` of the ROM in time linear in its size (07).

## Resolved questions

1. **Which instructions need multi-cycle expansion?** **[OM-choice]** Only register-amount shifts: 6 cycles
   (64-bit), 5 cycles (word). Everything else, including sub-word loads and stores, is 1 cycle, which matches the
   paper's six-cycle Fibonacci step being mostly 1:1.
2. **Misaligned access.** **[OM-choice]** Unprovable in v1 (C5), enforced by `a_h, a_w, a_d` rows (10.5).
3. **FENCE / ECALL / EBREAK / CSR.** **[OM-choice]** `FENCE` = one-cycle NOP (a zero-cycle elision would break the
   pc → micro-PC map used by JALR). `ECALL` = HALT only (C6); `EBREAK` and CSR/other instructions are unprovable.
   There is no input/output syscall; I/O goes through RAM (C6).
4. **Bytecode columns.** Specified in 9.6; the interface to 07 (Shout) and 10 (circuit).
5. **Constants instead of PC arithmetic. [OM-choice]** LUI, AUIPC, and the link address are ROM constants (`kc`),
   because `pc` is public in a Harvard machine. This removes the PC operand mux from the adder (64 committed
   bits per cycle) at the price of 64 more virtual ROM bits that cost the prover nothing.
6. **JALR and the pc → micro-PC map. [OM-choice]** JALR targets are found by a witness (`dynu`) that the
   circuit validates against the ROM (`rpc` of the fetched next row must equal the computed target, and the row
   must be a head row). No arithmetic relation between `pc` and micro-PC is needed, no extra table.

## Reference model

* `riscv.py`: `decode(word) -> Instr`, `Machine(code, entry_pc, ram_words, ram_log_words).run(max_cycles)`
  → `ExecResult(exit_code, regs, ram, instret)`, `Trap`, `alu`.
* `bytecode.py`: `COLUMNS`, `expand(code, entry_pc) -> Program(rom, columns, upc_of_pc, ...)`, `datapath`,
  `shift_apply`, `store_apply`, `VirtualMachine(program, ram_words, ram_log_words).run/run_padded` →
  `VMResult(exit_code, regs[64], ram, trace, instret)`. A trace record has: `upc, rom` (the row), `rs1, rs2, rd`,
  `v1, v2` (read values), `rd_old, rd_val`, `ram_idx, ram_old, ram_new, inc`, `shift_kind, shift_amt,
  shift_src, shift_out`, `store_width, store_off, store_src`, `take, dynu, next_upc`, and `dp` (all datapath
  intermediates).
* Tests: `reference/tests/test_isa_cpu.py` (decoder on many encodings; interpreter on hand-assembled
  programs: Fibonacci, loads/stores of all widths and offsets with sign extension, all shifts incl.
  register-amount, branches, JAL/JALR, LUI/AUIPC, traps; `VirtualMachine` vs `Machine` on random programs);
  helper assembler `reference/tests/asm.py`. Vectors: `reference/vectors/10-cpu/cpu.json` via
  `reference/gen_vectors_09_10.py`.

## Requests to other sections

* **14:** the loader MUST give `code` keyed by byte address (4-aligned) and an `entry_pc` in `code`; no
  compressed instructions. The initial register file is all zero (registers are `M_0` for register Twist).
  HALT exposes `a0` as the public `exit_code` through the `HALTED` row (10.9). The guest runtime must not
  load into `x0` expecting a fault.
* **07:** the register Twist takes the ROM columns `rs1, rs2, rd` (6 bits each) as its index claims; the
  bytecode Shout reads the whole row (430 bits) per cycle; register `32` is used as a scratch register
  (`rd_val` written there is a normal write).
