# 08. BinaryRouter

**Status:** draft · **Paper:** §5.4 (Lemma 4)

## Scope
The routing identity `Y(o,j) = Σ_{u,h} X(u,j)·Q(h,j)·R(o,u,h)` and its sum-check;
the shift instance (sources, two-factor one-hot selector `Q_lo·Q_hi`, `R_sh`) and the
sub-word-store instance (old word + store source → `Inc`, selector over 4 widths,
`R_st` with 3 offset bits); verifier evaluation of `R̃`.

## Specification

Notation: `F = |K|`, `T = 2^n`, `W = 2^w` the word width. **The specification fixes `w = 6`, `W = 64`.**
The reference model takes `wbits = w` as a parameter only to keep tests fast (shift and store with
`wbits = 3, 4, 5` are scaled-down versions: half-word `W/2`, offset bits `w − 3`); everything
below is stated for `w = 6` with the general form in brackets. Tables are flat with the first-listed
index in the low bits (C2). Points are lists of `K`, `x_1` first. Claims `(poly, point, value)` as in 07.

### 8.1 The generic routing sum-check

Public structure `R : B^{w} × B^{s} × B^{η} → B` (output bit `o`, source `u`, routing `h`), sparse.
Witness: `X(u,j)` (source bits), `Q(h,j)` (selector, one-hot or zero), output `Y(o,j)` with
`Y(o,j) = Σ_{u,h} X(u,j)Q(h,j)R(o,u,h)` over `B` (a sum over `B` is XOR).

**Input claim:** `Y~(r_o ∥ r_j) = y` for `r_o ∈ K^w`, `r_j ∈ K^n` (flat `Y` index `o + W·j`).

**Reduction.** With `R_{r_o}(u,h) := Σ_o eq(r_o,o)·R(o,u,h) = R~(r_o, u, h)` (Boolean `u,h`),

    y = Σ_{j,u,h} eq(r_j, j) · X(u,j) · Q(h,j) · R_{r_o}(u,h).

Variables summed: the cycle bits `j` (first), then the source bits `u`, then the routing bits `h`
(`h_lo` before `h_hi` when `Q` has two factors). The sum-check variable order is therefore `x_1..x_n = j`,
then `u`, then `h`: domain index `j + T·(u + 2^s·h)`. `X(u,j)` and `Q(h,j)` are extended
constantly over the variables they do not depend on. The prover absorbs the claim first:
`absorb_ks(label‖b"/point_o", r_o)`, `absorb_ks(label‖b"/point_c", r_j)`, `absorb_k(label‖b"/y", y)`; the sum-check
base label is `label‖b"/sc"`; afterwards `absorb_ks(label‖b"/evals", evals)`.
The honest prover uses as the sum-check claim the actual sum of its tables (the verifier uses `y`), so a wrong `Y` fails the final check.

Final check: with sum-check point `(s_j, s_u, s_h)`, claimed `x = X~(s_u ∥ s_j)`, `q`-values
`Q~(s_h ∥ s_j)` (below), accept iff

    eq(r_j, s_j) · x · q · R~(r_o, s_u, s_h) = final value.

Outputs are evaluation claims at the cycle point `s_j` on `X` and `Q` (the polynomials
authenticated by MosaicPCS and, for `Q`, BinaryShout through the bytecode).
No commitment is made. Soundness: `D·(n + s + η)/F` with `D` the degree of the instance (below).

### 8.2 Shift instance

**Index sets.** `u ∈ [64]` (6 bits, bit position of the shift source word `src`), `o ∈ [64]`,
`h = h_lo + 64·h_hi` with `h_lo ∈ [64]` the **amount** and `h_hi ∈ [8]` the **kind** (C7).
`Q_sh(h,j) = Q_lo(h_lo,j)·Q_hi(h_hi,j)`, flat `Q_lo`: `h_lo + 64·j`, `Q_hi`: `h_hi + 8·j`; both all-zero on a cycle
without a shift. `X(u,j)` flat `u + 64·j` is the 64 bits of the shift-source word.

**`R_sh`** (`R_sh(o,u,h) = 1` iff `u = src_{kind,amt}(o)` below; `H = W/2 = 32`):

| kind | name | valid amounts | source `u` for output `o` (none ⇒ no entry, output 0) |
|---|---|---|---|
| 0 | SLL | 0..63 | `o − amt` if `o ≥ amt` |
| 1 | SRL | 0..63 | `o + amt` if `o + amt ≤ 63` |
| 2 | SRA | 0..63 | `min(o + amt, 63)` |
| 3 | SLLW | 0..31 | `o < 32`: `o − amt` if `o ≥ amt`; `o ≥ 32`: `31 − amt` |
| 4 | SRLW | 0..31 | `o < 32`: `o + amt` if `o + amt ≤ 31`; `o ≥ 32`: `31` if `amt = 0` |
| 5 | SRAW | 0..31 | `o < 32`: `min(o + amt, 31)`; `o ≥ 32`: `31` |
| 6 | SEXT32 | 0 | `o < 32`: `o`; `o ≥ 32`: `31` |
| 7 | ZEXT32 | 0 | `o < 32`: `o`; `o ≥ 32`: none |

(Rows 3–7 are `sext32`/`zext32` of the specified 32-bit result, C7.) Routings with invalid amounts
(`amt ≥ 32` for kinds 3–5, `amt ≠ 0` for kinds 6–7) have **no entries**, so their output is 0: a
selector that names an invalid routing forces `Y = 0`. **Validity of amounts is therefore enforced by
`R` itself** and by ROM content: the bytecode table (09) only contains valid selectors, and register-amount
shifts are expanded by 09/10 into static routings. A routing of kind 3–5 with `amt ≥ 32`
and a non-zero `Y` simply cannot be proved.
Every output bit has at most one source. `|supp R_sh| = 12512`
(`2080 + 2080 + 4096 + 1552 + 560 + 2048 + 64 + 32`). The reference test checks `R_sh` against an
independent integer implementation of all kinds for all valid amounts (`test_router.py::ShiftSpecTest`).

**`R̃_sh(r_o, r_u, r_h)`** with `r_h = r_{h_lo} ∥ r_{h_hi}` (9 coordinates, **[OM-choice]**
no closed form, an `O(|supp R|) ≤ O(H·64)` algorithm): compute `e_o = eq_table(r_o)`, `e_u = eq_table(r_u)`,
`e_h = eq_table(r_h)` (`64 + 64 + 512` entries) and return `Σ_{(o,u,h) ∈ supp} e_o[o]·e_u[u]·e_h[h]`:
`2·12512` multiplications. Rationale: `R` is a fixed public relation; the verifier can precompute the
per-`h` structure, and the sum is cheap relative to the PCS. (An implementation MAY group by kind and use the
translation structure of kinds 0–2.)

**Sum-check.** `n + 6 + 6 + 3` variables (`j`, `u`, `h_lo`, `h_hi`), **degree 4**, summand
`eq(r_j,j)·X(u,j)·Q_lo(h_lo,j)·Q_hi(h_hi,j)·R_{r_o}(u,h)`. Degree in `j`: 4 (this is the extra degree the
two-factor selector costs); degree 2 in `u` and in each `h` variable, sent with degree 4 everywhere
(C3 uses one degree per sum-check). **[OM-choice]** uniform degree 4, 4 elements per round.
Prover sends `evals = [X~(s_u∥s_j), Q~_lo(s_{h_lo}∥s_j), Q~_hi(s_{h_hi}∥s_j)]`.
Output claims: `(shift/src, s_u ∥ s_j, ·)`, `(shift/qlo, s_{h_lo} ∥ s_j, ·)`, `(shift/qhi, s_{h_hi} ∥ s_j, ·)`.
The `Q` claims go to the bytecode Shout as read-value claims at cycle point `s_j` (07, 11).
Input claim: from Virtual Spartan on the shift-output segment (06). Soundness: `4(n + 15)/F`.

### 8.3 Store instance

**Index sets.** Output `o ∈ [64]` (bit of `Inc`), source `u ∈ [128]` (7 bits): `u < 64` is the old word bit `u`,
`u ≥ 64` is bit `u − 64` of the store-source word (C7); `X(u,j)` flat `u + 128·j`. Width selector `h ∈ [4]`
(SB, SH, SW, SD = 1, 2, 4, 8 bytes), `Q_st(h,j)` flat `h + 4·j`, one-hot on store cycles, all-zero otherwise.
Offset `a ∈ B^3`: the low 3 bits of the byte address, with the bit-`b` table `a_b(j)` (`b = 0,1,2`).

**`R_st(o,u,h,a)`.** A pair `(h,a)` is *valid* iff `a mod 2^h = 0` (alignment; `a ∈ [0,8)`). For a valid `(h,a)` let the lane be bytes
`b ∈ [a, a + 2^h)`. For `o = 8b + i` in the lane (`i ∈ [0,8)`) `R_st = 1` for exactly two sources:

    u = o                          (old bit)
    u = 64 + 8·(b − a) + i         (store-source bit: the store writes the LOW 2^h bytes of the source word at byte offset a)

and `R_st = 0` everywhere else. Invalid `(h,a)` have no entries. **XOR-feed trick:** the
increment is `Inc = old ⊕ new`; inside the lane `new` = source bit, so `Inc(o) = old_o ⊕ src`. Feeding the
output from both bits makes the sum `Σ_u X(u,j)R(o,u,h,a) = old_o + src` over `B`, which is
the XOR (`1 + 1 = 0`); outside the lane no source feeds `o`, so `Inc(o) = 0`. `|supp R_st| = 512`
(`4 · 128`: each of the four widths contributes 128 entries over all valid offsets). The test checks
against an independent word-level store (`StoreSpecTest`). **Alignment is not enforced by `R`** (an
invalid `(h,a)` just forces `Inc = 0`): section 10 MUST make misaligned stores unprovable (C5).

**Non-store cycles.** `Q_st(·,j) = 0` makes the right side 0, so the identity forces `Inc(·,j) = 0`.
This also covers loads and cycles with no RAM access, which write back the same word. **Who enforces it:**
the router, provided `Q_st` is authenticated by the bytecode Shout (the ROM row of a non-store has an all-zero
width field). The RAM Twist only proves consistency of the history given `Inc`; the CPU circuit only needs to
make non-RAM cycles access word 0 and bind the `X` copies (old word to the RAM read value, store source to the register
read value). Test: `test_nonstore_cycle_inc_must_be_zero`.

**Input claim.** `Inc~(x_o ∥ x_c) = y` from the RAM Twist `inc_extra` output (07, 7.7); `r_o = x_o`, `r_j = x_c`.

**Sum-check.** `n + 7 + 2` variables (`j`, `u`, `h`), the factor `R_{r_o}(u,h,a(j))` depends on the cycle through the offset.
Write `R_{r_o,a}(u,h) = Σ_o eq(r_o,o)R_st(o,u,h,a)` for each of the 8 Boolean `a`
and, using that `R~_st` is multilinear in `a`,

    R~_st(r_o, u, h, ã(x)) = Σ_{a ∈ B^3} Π_{b=1}^{3} (1 + ã_b(x) + a_b) · R_{r_o,a}(u,h),

with `ã_b` the MLE of the offset-bit table `a_b`. Summand:
`eq(r_j,j)·X(u,j)·Q_st(h,j)·R~_st(r_o,u,h,ã(j))`. Degree in a cycle variable: `eq, X, Q` (3) plus 3 (three
offset factors): **degree 6** (`3 + (w − 3)` in general). Table list (in this order): `eq`, `X`, `Q`, `a_1, a_2, a_3`
(each a function of `j` only), then `R_{r_o,0}, …, R_{r_o,7}`. **The prover sends `ã_b(s_j)`**: `evals = [X~(s_u∥s_j), Q~(s_h∥s_j), ã_1(s_j), ã_2(s_j), ã_3(s_j)]`. This works because `s_j` is determined coordinate by
coordinate by the sum-check challenges, so `ã_b~(s_j)` is a fixed evaluation claim. The verifier checks

    eq(r_j, s_j) · X~ · Q~ · R~_st(r_o, s_u, s_h, (ã_1,ã_2,ã_3)) = final value,

with `R~_st(r_o,r_u,r_h,r_a) = Σ_{(o,u,h,a) ∈ supp} e_o[o]·e_u[u]·e_h[h]·e_a[a]` (`e_·` the eq tables of
the respective points; `e_a` has `8` entries, `r_a = (ã_1,ã_2,ã_3)`): `3·512` multiplications.
Outputs: `(store/src, s_u ∥ s_j, ·)`, `(store/q, s_h ∥ s_j, ·)`, `(store/a0, s_j, ã_1)`, `(store/a1, s_j, ã_2)`,
`(store/a2, s_j, ã_3)`. `store/q` goes to the bytecode Shout (width field), `store/a_b` are the low address bits
in a direct segment of `W` (10), `store/src` is the copy segment. Soundness: `6(n + 9)/F`.

### 8.4 Soundness summary

Each router instance is one sum-check, so the error is `D·m_total/F` with `(D, m_total) = (4, n+15)` for shifts and
`(6, n+9)` for stores, plus the error of whichever argument discharges the outputs (07, 05). Lemma 4's
`O(log T)/|K|` is the same quantity for fixed widths.

### 8.5 Resolved questions

1. **Shift routings.** Fully enumerated, 8.2: all kinds `× 64` amounts, invalid combinations empty. SRA/SRAW sign fill and the W-variant
   sign extension are repeated sources (`u = 63`, `u = 31`). **[OM-choice]** SEXT32/ZEXT32 are kinds 6 and 7 (C7) rather than separate
   instructions, so sub-word loads and `addiw`-style extensions reuse the shift router.
2. **Split.** `h = (amount 6 bits, kind 3 bits)` (C7) rather than `√H`-balanced, so `Q_lo` is the amount field of the bytecode row and `Q_hi`
   the kind field; `|h_lo| = 64`, `|h_hi| = 8`. **[OM-choice]**
3. **`R̃`.** `O(|supp|)` algorithms above (12512 and 512 terms). A closed form is not needed.
4. **Register-amount shifts** are expanded by 09 into static routings; the barrel-shifter proposal (6 conditional shifts by `1,2,4,8,16,32`) is
   in 09's hands. This section only requires every executed routing to have a valid `(amt, kind)`.

### 8.6 Reference model

`reference/openmagnetar/router.py`: `shift_entries`, `store_entries`, `apply_shift`, `apply_store`, `shift_R_eval`, `store_R_eval`,
`shift_witness`, `store_witness`, `shift_prove/verify`, `store_prove/verify`, with `wbits` (6 is the specification).
Tests: `reference/tests/test_router.py` (R against integer semantics for all kinds and widths; `R~` against the brute-force MLE; honest
proofs with `wbits = 3, 4, 5, 6`; wrong shift output, wrong store increment, wrong offset witness, non-zero output or `Inc` on a zero-selector cycle).
Vectors: `reference/vectors/08-router/` (`R_eval_wb6.json`, `shift_wb3.json`, `shift_wb6.json`, `store_wb4.json`, `store_wb6.json`).

## Requests to other sections

* **10:** make misaligned stores unprovable; bind the `X` copy segment (old word = RAM read value, store source = register read value) in every
  cycle; lay out `Y`, `X`, `Inc` as `o + 64·j`, `u + 64·j` (shift) and `u + 128·j` (store); store the amount/kind and width fields as one-hot bytecode fields
  (zero on non-shift, non-store rows); place `store/a_b` bits in a direct segment.
* **09:** ROM rows contain only valid `(amt, kind)` and `(width)` selectors; expansion of register-amount shifts.
* **11:** shift claims: input from Spartan; store: input from the RAM Twist `inc_extra` point; outputs `shift/qlo, shift/qhi, store/q` are bytecode
  Shout claims at the points `s_j` (the Shout group mechanism of 07 handles several points).
* **13:** soundness formulas of 8.4.

## Integration notes

* **Store router input point (changes the request to 11 above).** The input claim is not taken from RAM Twist's `inc_extra` point. RAM Twist's
  input claim `wv~(r_o ∥ r_c)` needs `Inc~(r_o ∥ r_c) = y_0` at the Spartan point anyway (`wv = rv + Inc` for the single-word RAM access, 11.5), so 11
  sends `y_0`, uses it for `wv`, and uses the same claim `(r_o, r_j, y) = (r_o, r_c, y_0)` as the store router's input and as a Mosaic claim on
  `twist/ram/inc`. `inc_extra` (07 7.7) stays in the API and is not used by 11.
* **Fast provers.** `router.py` gained `shift_prove_fast` and `store_prove_fast`: identical transcripts and proofs to `shift_prove`/`store_prove`
  (checked in `test_protocol.py::TestFastRouters`), but the `n` cycle rounds exploit that `Q` has one non-zero entry per cycle, which makes `W = 64`
  provable in pure Python (the dense prover needs about 10 s for `T = 8`). Informative; the dense functions remain the definition.
