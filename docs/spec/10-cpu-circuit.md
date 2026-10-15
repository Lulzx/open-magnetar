# 10. CPU circuit

**Status:** draft · **Paper:** §5.1, §2.2(1). The paper gives only the idea (a bit-valued `W`, one SIMD R1CS over B for bit logic, one over K for packed muxes and linear checks); every concrete constraint below is **[OM-choice]**.

## Scope
The per-instance base R1CS over B (`s_1`) and over K (`s_2`); number of cycles per SIMD instance; the full
witness layout `W` partitioned into aligned segments, each marked direct or virtual and assigned an owner
(Twist-reg, Twist-RAM, Shout-bytecode, Router-shift, MosaicPCS); constraint-by-constraint datapath (adder,
comparator, logic, branch, PC update, load extract, store-copy binding); cross-step state and public binding.

Reference model: `reference/openmagnetar/cpu_circuit.py` (`layout`, `build_s1`, `build_s2`, `witness`, `check`,
`violations`, `stats`). The checker evaluates both relations on every instance directly, plus relations (X1)-(X3)
of section 06 6.6 and, if given the program, that the ROM-owned virtual segments equal the ROM row at the
claimed micro-PC. Constants below are for the default parameters (`Params(ram_log_words = A, log_cycles = 2)`).

## 10.1 Overview and conventions

* One SIMD instance = `2^c` consecutive virtual cycles ("slots" `t = 0 .. 2^c-1`). **[OM-choice] `c = 2`**
  (4 cycles per instance), justified in 10.2.
* `W` has one row (witness vector `w`, `NW = 2^13 = 8192` bits) per instance; `z = (w, 1)`, i.e. **`n_x = 0`**
  (06 6.1). All public data is bound through the carry-state segments (10.9).
* Packing (C1): a 64-bit word `a` with bits `a_0..a_63` is the K element `P(a) = Σ_j β_j a_j`, `β_j = X^j`.
  A K-relation row is `(Σ α_k z_k)·(Σ β_k z_k) = Σ γ_k z_k` with `α, β, γ ∈ K`; "`P(a)`" inside a row means
  the linear form with coefficient `X^j` on column `a_j`; a shifted word `P(a >> s)` puts coefficient `X^j` on
  column `a_{j+s}` (a pure relabeling: shifts inside rows cost nothing).
* Every field below is written per cycle. `f.i` is column `i` of field `f` in the current slot. ROM flags are
  columns of the virtual segment `rf`; `[1]` is the constant-one column. Over B, "`+`" is XOR.
* Both relations only ever evaluate to 0/1 on bit columns; the K-relation coefficient `X^j` selects bit `j`
  of the packed value.

## 10.2 Cycles per instance (Q1)

**[OM-choice] `c = 2`.** The constraint is that `W`'s row length is a power of two and every segment is an
aligned power-of-two block. All fields have per-cycle widths `64, 32, 16, 8, 4` or `128`, and the per-instance
state (10.9) has a fixed size of 512 bits that does not scale with `c`. Measured (`cpu_circuit.used_bits`
vs `num_w_cols`, per instance):

| `c` | used bits | `NW` | padding | `s_1` rows | `s_2` rows |
|---|---|---|---|---|---|
| 0 | 2400 | 4096 | 41% | 217 | 33 |
| 1 | 4288 | 8192 | 48% | 432 | 63 |
| **2** | **8192** | **8192** | **0%** | 862 | 123 |
| 3 | 15616 | 16384 | 4.7% | 1722 | 243 |
| 4 | 30720 | 32768 | 6.2% | 3442 | 483 |

`c = 2` is the least padded. It also keeps the per-instance state (512 direct bits) to 128 bits per cycle, and
the base matrices small (862 and 123 rows; verifier work is linear in the number of non-zeros, 5750 and
16089). Smaller `c` wastes space; larger `c` makes the base R1CS (which the verifier evaluates directly) larger
for no gain. The state chain inside an instance is by ordinary constraints (slot `t` → `t+1`); only the instance
boundary uses (X1)-(X3).

Row counts are padded to `2^ρ = 1024` (`ρ = 10`) for both relations and the column space is `2^ν = 16384`
(`ν = 14`; the second half holds `1`). Section 06's rectangular `(ρ, ν)` is used (06 6.1); this avoids padding
the 862 rows to 16384.

## 10.3 Witness layout (Q3)

Segments are aligned power-of-two blocks of columns of `w`. Within a segment, the per-cycle field is stored
**slot-major**: local column `= slot·width + bit`, so the segment's flat polynomial (06: index
`y + 2^ℓ·u`) is indexed `bit + width·cycle` with `cycle = slot + 4u`, which is exactly the "bit in the low 6
bits, cycle above it" layout that 07 (Twist/Shout value segments) and 08 (router tables `X(u, j)`, `Y(o, j)`)
expect. The layout is the buddy allocation "sort by descending size, then name, place consecutively"
(`cpu_circuit._layout`); all sizes are powers of two, so alignment is automatic; the verifier recomputes it.
Per-instance total 8192 bits; no column is uncovered (since the `ridx` widening, see Integration notes).

| Segment | bits/cycle | per-instance log size | Kind | Owner | Role |
|---|---|---|---|---|---|
| `v1` | 64 | 8 | virtual | twist-reg | `rs1` read value |
| `v2` | 64 | 8 | virtual | twist-reg | `rs2` read value |
| `rdv` | 64 | 8 | virtual | twist-reg | `rd` write value |
| `rw` | 64 | 8 | virtual | twist-ram | RAM word read (old word) |
| `ridx` | 64 | 8 | virtual | twist-ram | RAM word index (0 when no access); 64 wide so that its Spartan claim is at the same point as `rw` (11) |
| `Y` | 64 | 8 | virtual | router-shift | shift output |
| `imm`, `kc`, `rpc` | 64 each | 8 | virtual | shout-bytecode | ROM fields |
| `upc`, `seq`, `tgt` | 32 each | 7 | virtual | shout-bytecode | ROM fields |
| `rf` | 64 | 8 | virtual | shout-bytecode | packed ROM flags: the 26 flags, `bsel` (6), `ln` (8), `fill` (8) = 48 used bits (`cpu_circuit.FLAG_POS`) |
| `Q_lo` | 64 | 8 | virtual | shout-bytecode | router-shift selector (also consumed by 08) |
| `Q_hi` | 8 | 5 | virtual | shout-bytecode | router-shift selector |
| `st_w` | 4 | 4 | virtual | shout-bytecode | router-store selector |
| `Bop` | 64 | 8 | direct | mosaic | ALU B operand |
| `cin` | 64 | 8 | direct | mosaic | adder carry vector `c_0..c_63` |
| `nw` | 64 | 8 | direct | mosaic | zero-detect chain `n_1..n_63` (bit 0 unused) |
| `AND` | 64 | 8 | direct | mosaic | bitwise AND |
| `Dw` | 32 | 7 | direct | mosaic | word sign-extension correction (bits 32..63) |
| `T0, T1, T2` | 64 each | 8 | direct | mosaic | result-mux accumulators |
| `Gs` | 64 | 8 | direct | mosaic | gated shift/stage select |
| `shsrc` | 64 | 8 | direct | mosaic | copy of `v1`; router-shift source `X` |
| `stc` | 128 | 9 | direct | mosaic | store-router sources `X`: `[old RAM word (u < 64) | store source (u ≥ 64)]` |
| `off` | 4 | 4 | direct | mosaic | low 3 address bits (+1 zero pad); store-router offset claims |
| `x1, x2, x3` | 64 each | 8 | direct | mosaic | load barrel stages |
| `m` | 64 | 8 | direct | mosaic | load, lane-masked word |
| `L` | 64 | 8 | direct | mosaic | load result (0 on non-loads) |
| `fl` | 16 | 6 | direct | mosaic | single-bit witnesses: `cout, cond, p0..p5, u1, u2, rdslt, eqres, take, tb, th, tw` |
| `dynu` | 32 | 7 | direct | mosaic | dynamic JALR next micro-PC |
| `S_in`, `S_out` | per instance 256 | 8 | direct | mosaic | carry-in / carry-out state (10.9) |

The ROM columns `rs1, rs2, rd` have no segment: register Twist discharges its index claims directly
against them (Construction 3, step 3). The segments `shsrc`, `stc`, `off` are *direct* because the routers
need committed sources (§5.4); the `Y` segment is virtual because Virtual Spartan's claim on it is handed to the
shift router; `v1`, `v2`, `rdv`, `rw`, `ridx` are virtual because Twist authenticates them.

**Counts (default parameters, `cpu_circuit.stats`).**

* Witness columns per instance: `NW = 8192`, of which all 8192 are in segments (1920 per cycle: 1108 direct + 812 virtual, times 4, plus 512 state bits). Total **witness columns per cycle: 2048 used** (1920 + 128 state) out of 2048 allocated. Committed: direct = **1108 bits/cycle** (per-cycle fields) + **128 bits/cycle** (512-bit
  state / 4 cycles) = **1236 committed bits per cycle**; virtual = 812 bits per cycle (never committed).
* Committed bytes: `1236 / 8 ≈ 154.5 B` per cycle for the CPU witness segments (before the auxiliary Twist/Shout
  one-hot and increment polynomials of 07 and 08, which are counted in those sections).
* **Comparison with the paper.** Paper §6.5: the prover uses about 1.6 KiB of memory per cycle (1.0 KiB for the
  optimized variant). That figure is total prover memory (witness, one-hot addresses, increments, `Z`-folds,
  sum-check tables and encodings), so it is not directly comparable. Our direct witness alone is about 9% of
  1.6 KiB; the auxiliary committed vectors and the prover's expanded tables will dominate. We make no claim
  that the CPU witness is smaller than the paper's.

## 10.4 Decode use and the constraint families of `s_1` (B relation)

A B-relation row is `(Σ z)·(Σ z) = Σ z` over bits. Let (all per slot `t`)

    S_i = v1_i + Bop_i + sub + cin_i          (the adder sum bit, a linear form; `sub` is the ROM flag)

**Counts per cycle (`s_1`: 215 rows/cycle, 862 per instance including the instance-boundary rows):**

| # | Family | Rows | Formula (`A · B = C`) |
|---|---|---|---|
| 1 | adder carry (ripple, majority) | 64 | `(v1_i + cin_i)·(Bop_i + sub + cin_i) = cin_{i+1} + cin_i`, `i = 0..63`, with `cin_64 := fl.cout` |
| 2 | carry-in | 1 | `[1]·(cin_0 + sub) = 0` |
| 3 | low address bits | 3 | `[1]·(off_i + S_i) = 0`, `i = 0,1,2` |
| 4 | bitwise AND | 64 | `v1_i · Bop_i = AND_i` |
| 5 | zero detect chain | 63 | `S_i · n' = nw_i + S_i + n'` for `i = 1..63`, with `n' = S_0` for `i = 1` else `nw_{i-1}` (an OR chain: `nw_i = S_0 ∨ … ∨ S_i`) |
| 6 | shift-stage bit select | 6 | `bsel_k · v2_k = p_k`, `k = 0..5` |
| 7 | shift condition | 1 | `[1]·(cond + sh_imm + p_0 + … + p_5) = 0` |
| 8 | comparison | 2 | `f_cmp·(1 + cout) = u1`; `f_lts·(v1_63 + Bop_63) = u2` |
| 9 | SLT result bit | 1 | `g_slt·(u1 + u2) = rdslt` |
| 10 | equality | 1 | `f_eq·(1 + nw_63) = eqres` |
| 11 | branch decision | 1 | `br·(u1 + u2 + eqres + inv) = take` |
| 12 | load sign bits | 3 | `ldsb·x3_7 = tb`, `ldsh·x3_15 = th`, `ldsw·x3_31 = tw` |
| 13 | TRAP | 1 | `trap · [1] = 0` |
| 14 | alignment | 3 | `a_h · S_0 = 0`, `a_w · S_1 = 0`, `a_d · S_2 = 0` |
| 15 | JALR head | 1 | slots `t < 3`: `jalr·(1 + head_{t+1}) = 0`; slot 3: see 10.9 |

The ripple adder: `cin_{i+1} = maj(v1_i, b'_i, cin_i)` with `b'_i = Bop_i + sub`, and `(a+c)(b+c) = maj(a,b,c) + c`
over B. For subtraction `v1 - Bop` the carry-out `cout = cin_64` is "no borrow", so `ltu = 1 + cout`; signed
`lts = ltu + v1_63 + Bop_63`, hence rows 8 and 9. The equality test uses `S = v1 - v2` (the branch rows set
`sub = 1`) and the OR chain of row 5; `eq = 1 + nw_63`. **[OM-choice]** the chain (63 committed bits, 63
rows) is cheaper in committed bits than a K-relation inverse witness (128 bits).

**Decode use.** The row `ROM[upc]` supplies every flag; the circuit never decodes an instruction word. The
flags in the rows above are the virtual segment `rf`, authenticated by Shout (Construction 3, step 6).

## 10.5 `s_2` (K relation): ALU, result mux, RAM address

Rows are `α · β = γ` with each of `α, β, γ` a linear form over K; `P(·)` as in 10.1; `R64 = 0..63`.

| # | Family | Row (`A · B = C`) |
|---|---|---|
| 1 | B operand mux | `b_imm · (P(imm) + P(v2)) = P(Bop) + P(v2)` |
| 2 | word sign-extension | `w · Σ_{j=32}^{63} X^j (S_j + S_31) = Σ_{j=0}^{31} X^{j+32} Dw_j` (so `Sp := S + Dw` equals `sext32(S)` when `w = 1`, `S` otherwise) |
| 3 | `T0` | `c_add · P(Sp) = P(T0)`, with `P(Sp) = Σ_j X^j S_j + Σ_j X^{j+32} Dw_{j}` |
| 4 | `T1` | `e · P(X) = P(T1) + P(T0)`, `X_j = v1_j + Bop_j` |
| 5 | `T2` | `g · P(AND) = P(T2) + P(T1)` |
| 6 | shift select | `cond · (P(Sp) + P(Y)) = P(Gs)` |
| 7 | **write-back** | `[1] · (P(rdv) + P(T2) + P(Gs) + P(L) + X^0·rdslt + P(kc)) = 0` |
| 8 | shift source copy | `[1] · (P(shsrc) + P(v1)) = 0` |
| 9 | RAM index | `mem · Σ_{j<A} X^j S_{3+j} = Σ_{j<A} X^j ridx_j` |
| 10 | RAM index range | `[1] · Σ_{j=A}^{63} X^j ridx_j = 0` |
| 11 | RAM window | `mem · (Σ_{j=3+A}^{30} X^j S_j + X^{31}(S_31 + 1) + Σ_{j=32}^{63} X^j S_j) = 0` |
| 12 | exit code | `halted · (P(v1) + Σ_j X^j S_in.ex_j) = 0` |
| 13 | ECALL a7 | `ecall · P(v2) = 0` |

**ALU result mux (Q2).** `rd_val = T2 xor Gs xor L xor rdslt xor kc` with `T0 = c_add·S'`, `T1 = T0 + e·X`,
`T2 = T1 + g·AND`, `Gs = cond·(S' + Y)`. The classes are mutually exclusive in the ROM, so a sum of gated terms
is the mux. `Y` is zero when no shift is active (the router identity forces `Y = 0` when its selector is zero,
paper §5.4), `L` is zero off-loads (10.6), `kc` is a ROM constant, `rdslt` a bit in position 0. For an immediate
shift (`c_add = 1`, `imm = 0`, `cond = 1`): `T0 = v1`, `Gs = v1 + Y`, so `rd_val = Y`. For a register-amount
stage: `cond = bit_k(rs2)`. `OR` is `X + AND`. `LUI/AUIPC/link` use `kc` alone. `ADDW/SUBW/ADDIW` use `w = 1`.

**x0 writes (C5).** A write to `x0` needs a zero increment: the write value is `rd_val` and the register
Twist increment is `rd_val xor old`, with `old = 0` for `x0` (initial register file zero). The ROM invariant of
09 (every row with `rd = 0` has all result gates zero) gives `T2 = Gs = L = kc = rdslt = 0` and so `rd_val = 0`
by row 7; the circuit proves it with no extra constraint. A ROM row cannot violate this because the verifier
derives the ROM (09 9.7). **[OM-choice]** rather than a per-cycle "if rd = 0 then rd_val = 0" mux (64 K
products and a word), the invariant is placed in the public ROM. A non-writing cycle (store, branch, NOP)
has `rd = 0` and the same effect.

**RAM address (Q: alignment and range).** The byte address is `S = v1 + imm` from the adder (memory rows have
`b_imm = 1`, `sub = 0`). `ridx = (S - RAM_BASE) >> 3`. With `RAM_BASE = 2^31` and `A <= 28`, row 11 forces
`S_63..S_32 = 0`, `S_31 = 1`, `S_{30..3+A} = 0` when `mem = 1`, so `S ∈ [2^31, 2^31 + 8·2^A)`. Row 9 puts
`S_{3..2+A}` into `ridx` and zero on non-memory rows (word 0, zero increment, C5); row 10 zeroes the unused
index bits. Alignment is the B rows of family 14 (thermometer flags `a_h ≥ a_w ≥ a_d`). **[OM-choice]** `A <= 28`
(RAM at most 2 GiB) so that the window check is a pure bit pattern; section 14's default `A` fits.

## 10.6 Load path (Q4)

**[OM-choice] R1CS in v1, no third router.** For a load the row has `mem = 1` and the flags `ln, fill, ldsb,
ldsh, ldsw`. The circuit extracts `x3 = rw >> (8·off)` (barrel over the byte offset, three K rows), masks to the
byte lanes `ln`, and fills lanes `fill` with the sign bit.

* Barrel: `off_k · (P(x_k >> 8·2^k) + P(x_k)) = P(x_{k+1}) + P(x_k)` for `k = 0,1,2`, with `x_0 = rw`
  (shift amounts 8, 16, 32): 3 rows, `x_1..x_3` committed.
* Lanes: `ln_ℓ · Σ_{j=8ℓ}^{8ℓ+7} X^j x3_j = Σ_{j=8ℓ}^{8ℓ+7} X^j m_j`, `ℓ = 0..7`: 8 rows, `m` committed.
* Sign bit: B rows 12 (`tb, th, tw`: signed-size flag AND the bit at position 7, 15, 31).
* Sign fill: `(tb + th + tw) · Σ_ℓ fill_ℓ · (Σ_{j=8ℓ}^{8ℓ+7} X^j) = P(L) + P(m)`: 1 row, `L` committed.

`LD` has `ln = 0xFF`; `LW` has `ln = 0x0F`, `fill = 0xF0`, `ldsw = 1`; `LWU` the same with no sign flag.
`L` is zero on non-load rows because `ln = fill = 0`. The cost is 192 + 64 + 64 committed bits per cycle (`x1..x3`,
`m`, `L`) paid every cycle; a load router would save bits at the cost of a third sum-check. Measured, not
chosen on speed: kept R1CS (the paper's description does not include a load router).

## 10.7 Store copy-binding and the store router

For a store the new word is a routing of `(old, rs2)` (08): `Inc(o) = Σ X(u) Q_st(h) R_st(o, u, h, a)`. The
sources `X` must be in a direct segment: `stc = [old word | store source]` (128 bits). The R1CS binds it to the
originals in **every** cycle (not gated):

    [1]·(P(stc[0..64)) + P(rw)) = 0              (old RAM word)
    [1]·(P(stc[64..128)) + P(v2)) = 0            (store source = rs2 read value)

The offset `a` is the direct segment `off` with `[1]·(off_i + S_i) = 0` for `i = 0,1,2` (family 3). The width
selector is the ROM column `st_w` (one-hot over `{SB, SH, SW, SD}`, zero on non-stores); `a_h, a_w, a_d` force
the alignment that the router assumes (a misaligned store is unprovable, request from 08). RAM Twist's `Inc`
equals the routing on stores and the router's zero selector forces `Inc = 0` on all other cycles (08).

## 10.8 Shift source and output wiring; HALT; trap

* **Shift source.** `shsrc = v1` (K row 8, ungated); the router-shift source `X(u,j)` is `shsrc` (`u < 64`).
  **[OM-choice]** the shift source word is always `rs1`; register-amount stages read the amount from `rs2`.
* **Shift output.** `Y` is the virtual segment on which the router (08) consumes the Virtual-Spartan claim; the
  row `Gs` (row 6) and row 7 are the only places it is used. `Q_lo` and `Q_hi` are ROM-owned segments.
* **HALT.** The `HALT` row has `ecall = 1`: K row 13 forces `v2 = reg[x17] = 0`. It sets `seq = 0` (the
  `HALTED` row). The `HALTED` row (`halted = 1`, `rs1 = 10`) reads `a0` each cycle: K row 12
  `halted · (P(v1) + P(S_in.ex)) = 0` binds the value to the public exit code carried in the state (10.9). There is
  no way to reach `HALTED` except through `HALT`, because it is a ROM row only referenced by it and by itself.
* **TRAP.** B row 13 `trap·[1] = 0`: a trace that reaches any `TRAP` row has no satisfying witness.

## 10.9 PC and micro-PC update; cross-step state; public binding

**Micro-PC update (one K row per cycle).**

    take · (P(tgt) + P(seq)) = P(upc') + P(seq) + P(dynu)        (32-bit packed words)
    (1 + jalr) · P(dynu) = 0

so `upc' = seq + take·(tgt + seq) + dynu`: static rows use `seq`/`tgt` (rows with `take = 0` and `dynu = 0`),
and a `JALR` row (`seq = tgt = 0`, `take = 0`) uses the committed `dynu`. `upc'` is the `upc` segment of slot
`t+1`, or `S_out.upc` for slot 3.

**PC tracking [OM-choice].** The RV64I `pc` is not a separate committed word: it is the ROM column `rpc` of the
fetched row, i.e. a function of the micro-PC authenticated by Shout. Branches, `JAL`, `LUI`, `AUIPC` and
links are static (computed in the ROM), so the only place a dynamic `pc` arises is `JALR`. For `JALR`:

    jalr · Σ_{j=1}^{63} X^j (S_j + rpc'_j) = 0         (K: the target equals the next fetched row's pc)
    jalr · (1 + head') = 0                              (B: the next row is a head row)

with `rpc'` and `head'` taken from slot `t+1`. Bit 0 of the target is cleared by omitting `j = 0` (RV spec), and bit 1
must be 0 because `rpc` is 4-aligned (a misaligned target is unprovable). This costs 0 committed bits per cycle
instead of 64+32 for a shadowed `pc`/`upc` pair. The two rows together make `dynu` a witness validated by the ROM:
the prover can only land on the head row whose `rpc` equals the target (unique, 09 9.5).

**Cross-step (state carried over).** Section 06 6.6: two whole segments `S_in`, `S_out` of the same size
`2^λ`, `λ = 8` (256 bits); (X1) `S_in(u) = S_out(u-1)`, (X2) `S_in(0) = init`, (X3) `S_out(q-1) = fin`. Layout of
both (`ST_*` in `cpu_circuit`):

| Bits | Field | `S_in` meaning | `S_out` meaning |
|---|---|---|---|
| 0..31 | `upc` | micro-PC of slot 0 | micro-PC of the next cycle (`upc'` of slot 3) |
| 33..95 | `jt` (bit `j` at `32 + j`) | pending JALR target of the previous cycle | `S_j` of slot 3 (if `jalr`) |
| 96 | `jf` | previous cycle was a JALR | `jalr` flag of slot 3 |
| 97 | `halted` | halted flag of the previous cycle (carried, no further constraint) | `halted` flag of slot 3 |
| 98..161 | `ex` | exit code | exit code (equal to `S_in.ex`) |
| rest | zero | | |

Constraints (per instance, in addition to the per-slot rows): `[1]·(P(S_in.upc) + P(upc_slot0)) = 0`;
`jf_in · Σ_{j=1}^{63} X^j (jt_in_j + rpc_slot0_j) = 0` (K); `jf_in · (1 + head_slot0) = 0` (B);
slot 3: `upc'` writes `S_out.upc` (above), `jalr · Σ X^j S_j = Σ_{j=1}^{63} X^j S_out.jt_j` (K),
`[1]·(S_out.jf + jalr_3) = 0` and `[1]·(S_out.halted + halted_3) = 0` (B), and
`[1]·(P(S_out.ex) + P(S_in.ex)) = 0` (K). With (X1) the exit code is the same in every instance, and the JALR
expectation is carried across the boundary. Totals per instance: `s_1` has 862 rows (`4*215` per-slot rows, minus the slot-3 `jalr-head` row which becomes `jf-out`, plus `halted-out` and `jf-in-head`); `s_2` has 123 rows (`4*30` plus `s-in-upc`, `s-in-jalr`, `ex-carry`; slot 3 replaces the `jalr-target` row by `jalr-target-out` and slot 0..2 keep theirs: `4*30 + 3`).

**Public binding.** The public vectors of 06 6.6 (both in `B^256`):

* `init`: `upc = entry_upc` (bits 0..31), `ex = exit_code` (98..161); `jf = halted = 0`, everything else 0.
* `fin`: `upc = 0` (the `HALTED` row), `halted = 1`, `ex = exit_code`; `jf = 0`, `jt = 0`.

`entry_upc = upc_of_pc[entry_pc]` and `exit_code` are the public instance (09 9.5, 14.3); the verifier builds both
vectors from them. (X3) with `halted = 1` forces the last cycle to be the `HALTED` row (the only row with
`halted = 1`), and `upc' = 0` and `jalr = 0` there. The initial register file is zero and the initial RAM is
`M_0` (07). The paper's Remark 4 leaves all of this to "the next MLE"; we use section 06's state-segment form.

## 10.10 Cycle and instruction counts (summary)

| Instruction class | Virtual cycles |
|---|---|
| ALU, LUI, AUIPC, immediate shifts, loads, stores, branches, JAL, JALR, FENCE, ECALL | 1 |
| `SLL SRL SRA` | 6 |
| `SLLW SRLW SRAW` | 5 |

Per cycle, `s_1` has 215 rows (64 carry + 64 AND + 63 zero-chain + 24 other) and `s_2` has 30 rows (25 for the
datapath, 5 for the packed memory/loads). Direct bits per cycle: 1108 (+128 state).

## Resolved questions

1. **Cycles per instance. [OM-choice]** `c = 2` (10.2): 0% padding, 862/123 rows, state 128 bits/cycle.
2. **B relation vs K relation. [OM-choice]** B: carries (majority), AND, zero-detect, comparison bits,
   branch decision, sign bits, alignment, TRAP. K: operand and result muxes, word sign-extension, load barrel and
   lane masks, packed copy-bindings (shift source, store sources), RAM address and window, micro-PC update,
   JALR target match, exit-code and ECALL checks. Anything that is a gated 64-bit word is one K row; anything
   that is a per-bit product is B.
3. **Segment layout / padding. [OM-choice]** Buddy allocation as in 05 (sort by size descending then name);
   no column of the 8192 is padding (the 64-bit `ridx` uses the 128 columns that were spare).
4. **Load path. [OM-choice]** R1CS (barrel + lanes + sign fill, 10.6), no third router in v1. Cost 320
   committed bits per cycle; a load router is future work.
5. **ADD/SUB/SLT via ripple carry over B. [OM-choice]** Yes (10.4), exactly the paper's XOR + majority.
6. **Public x and cross-step.** `n_x = 0`; the state chain uses `S_in`/`S_out` (06 6.6), (10.9).
7. **PC tracked.** **[OM-choice]** as the ROM column `rpc` of the fetched row; only JALR needs a dynamic check
   (10.9). No separate `pc` witness.

## Reference model tests
`reference/tests/test_isa_cpu.py` (`TestCircuit`): layout is aligned and disjoint; honest executions
(with all instruction classes, JALR at every slot alignment, multi-instance) are accepted; dozens of distinct
single-bit corruptions (27 field/cycle cases over direct, virtual and ROM fields, plus S_in/S_out bits at the first and last instance; all rejected); wrong public entry or exit; a
truncated trace that does not end in `HALTED`; ROM-field tampering is caught when the program is supplied.

## Requests to other sections

* **06:** (i) The two relations have different row counts (862 and 123) padded to a common `2^ρ = 1024`; the
  column dimension is `2^ν = 16384`. A non-square `(ρ, ν)` is used (06 6.1); please confirm that the padding rows are all-zero
  rows. (ii) (X1)-(X3) is used with `λ = 8` and `n_x = 0`. The `S_in`/`S_out` segments are listed in the
  layout table (10.3); they are *not* per-cycle fields (their size is per instance).
* **07:** (i) RAM Twist: `wa ≡ ra`; non-memory cycles read word 0 with zero `Inc` (`ridx = 0` is forced by row 9);
  (ii) register Twist: the index columns are `rs1, rs2, rd` of the ROM row (no `W` segment), and `x0` writes
  have `rd_val = 0` by the ROM invariant (09 9.3); (iii) the ROM row is 430 bits wide, of which 424 bits are in
  `W` segments (10.3, the packed `rf` segment carries 48 meaningful flag bits).
* **08:** (i) The shift router source is the 64-bit segment `shsrc` and the output is `Y`; selector segments
  `Q_lo` (64 bits) and `Q_hi` (8 bits) are ROM-owned. (ii) The store router source is the 128-bit segment `stc`
  (old word then source), offset bits `off.0..2`, selector `st_w` (4 bits, zero on non-stores). (iii) The circuit
  enforces alignment (`a_h, a_w, a_d`) so the router never sees a misaligned store.
* **14:** `ex` in `S_in/S_out` is the public exit code (the value of `a0` at HALT); the loader MUST provide
  4-aligned `pc` keys; `A <= 28`.

## Integration notes

* **`ridx` widened from 32 to 64 bits per cycle** (`cpu_circuit.FIELDS`, row 10 of 10.5 now zeroes bits `A..63`). Why: Virtual Spartan's claim on a
  segment is at `(ρ_i ∥ r_inst)` with `ρ_i` the first `ℓ_i` coordinates of the column point, so a 32-bit segment has its cycle point shifted by one
  coordinate relative to a 64-bit one. RAM Twist takes the read value (`rw`, 64 bits) and the address-bit claims at **one** cycle point (07 7.5), so
  `rw` and `ridx` must have the same width. Effect: the 128 columns that were spare are used (`NW` stays 8192, padding 0%); virtual bits per cycle
  780 → 812; committed bits are unchanged. The checker, the witness and `test_isa_cpu` are unaffected; `vectors/10-cpu/cpu.json` was regenerated.
* **`off` is defined on every cycle** (it is `S & 7` of the adder output, also on loads and non-memory cycles); the store router's offset-bit claims
  `store/a_b` are claims on this segment, so the prover's offset tables for the router are the `off` bits of all cycles, not only of stores (the
  router's selector zero kills the non-store cycles). Implemented in `protocol.py`.

* 2026-10-16 (Rust `om-circuit` port): corrected the `s_2` non-zero count in 10.2 from 15961 to 16089 (the value in `cpu_circuit.stats()` and `vectors/10-cpu/cpu.json`; the spec prose was stale, behavior unchanged).
