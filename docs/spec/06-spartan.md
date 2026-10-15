# 06. Spartan family: SIMD R1CS, BinarySpartan, Virtual Spartan

**Status:** draft · **Paper:** §4.1–4.3, §5.1, §5.3, Remark 4

## Scope
SIMD R1CS over B and over K with shared witness W; the z = (w, 1, x) layout
and Eq. (1); outer and inner sum-checks; the lockstep dual outer sum-check with
shared instance challenges; the single batched inner sum-check; per-segment
claim split (Construction 2); cross-step constraints via the 'next' MLE; and
binding of the public initial and final state.

Notation: `|K| = 2^128`. All tables follow C2 (little-endian, `x_1` is the
LSB). Sum-checks follow C3 (messages `[g(t_0), g(t_2), …, g(t_d)]`) and are
run with `sumcheck_prove` / `sumcheck_verify` of section 03 whenever a single
sum-check is run (inner, cross-step). The lockstep outer phase cannot use that
API (two sum-checks share challenges), so this section writes it out. Its
messages and its per-round checks are exactly those of 03 for `d = 3`.

## Specification

### 6.1 R1CS and SIMD R1CS

**Base structure.** A base structure `s = (A, B, C)` over a field `F ∈ {B, K}`
has parameters `(ρ, ν)`: `A, B, C` are `2^ρ × 2^ν` matrices with entries in `F`
(entries are 0/1 for `F = B`). They are stored as sparse lists of
`(row, column, value)` triples. The vector `z` has length `2^ν` and is

    z = (w, 1, x) padded with zeros to length 2^ν,

with `|w| = 2^(ν−1)` (the witness is padded with zeros to exactly this length)
and `1 + |x| ≤ 2^(ν−1)`. So `w` occupies indices `[0, 2^(ν−1))`, the constant
`1` sits at index `2^(ν−1)`, `x` follows it, then zeros. A row `j` is satisfied
iff `(A z)_j · (B z)_j = (C z)_j`.

**[OM-choice] Rectangular structures.** The paper assumes square `m × m`
matrices with `|w| = 1 + |x| = m/2`. We allow `2^ρ` rows and `2^ν` columns
independently. Rationale: the CPU circuit's constraint count and its column
count are unrelated; padding one up to the other only costs prover time. The
paper's case is `ρ = ν`. Both relations of Virtual Spartan MUST use the same
`(ρ, ν)` (pad the smaller one with zero rows; zero rows are satisfied and, being
sparse, cost nothing in the prover of 6.9).

**SIMD instance.** `q = 2^s` instances share one structure. Instance `u` has a
witness row `W[u] ∈ B^(2^(ν−1))` and a public input `x_u ∈ F^{n_x}` (the same
length `n_x` for all `u`). `z_u = (W[u], 1, x_u)`. The SIMD relation holds iff
every instance is satisfied. For *two* relations `s_bin` (over B) and `s_fld`
(over K) sharing `W`, as in paper §5.1, both must hold on every `z_u`, with the
same `x_u`.

**Flattening of W (C2 exception).** `W` is the bit matrix with row `u` equal to
`W[u]`. Its polynomial is `W̃(c, u)` with the column variables `c = (c_1 …
c_{ν−1})` in the **low** variables and the instance variables `u = (u_1 … u_s)`
in the **high** variables, i.e. the flat vector has index
`c + 2^(ν−1)·u` and `W̃(r_col ∥ r_inst)` is its MLE evaluated at the
concatenated point. The `(Az)` vectors of the block-diagonal system are
flattened the same way: entry `row + 2^ρ·u`. A **row point** is therefore
`(r_row, r_inst) ∈ K^ρ × K^s` in variable order, with `r_row` in the low
variables.

**Eq. (1), adapted to C2.** The paper's "first coordinate `y[0]` splits `w` from
`(1, x)`" is, for little-endian indexing, the **highest** variable `y_ν` of the
column index (index bit `ν−1`): `y_ν = 0` selects `w` (the low half) and
`y_ν = 1` selects `(1, x)` (the high half). For `y = (y_1 … y_ν) ∈ K^ν`, with
`y' = (y_1 … y_{ν−1})`:

    z̃(y) = (1 + y_ν) · w̃(y') + y_ν · P̃(y'),    P = (1, x) padded to 2^(ν−1).       (6.1)

For SIMD, fold at the instance point `r_inst`:

    ZF(y) := Σ_u eq(r_inst, u) · z_u[y]      (a table of length 2^ν; z_u is the vector of instance u)
    ZF~(y) = (1 + y_ν) · W̃(y' ∥ r_inst) + y_ν · PF~(y'),
    PF     = Σ_u eq(r_inst, u) · (1, x_u)    (a table of length 2^(ν−1)).

The verifier computes `PF` in `O(q·n_x + 2^(ν−1))` and evaluates `PF~` by
`mle_eval`. **[OM-choice] v1 uses `n_x = 0`**: all public data of Magnetar
(initial and final state) is bound by the cross-step relation (6.6), so
`P = e_0` (the first unit vector), `PF = e_0` (since `Σ_u eq(r_inst,u) = 1`)
and `PF~(y') = Π_k (1 + y'_k)`, an `O(ν)` evaluation. The general `x_u` stays
in the definition so BinarySpartan standalone use (and the tests) can use it.
This resolves Q4 (see Resolved questions).

**Base-matrix MLE.** For `M ∈ {A, B, C}`:

    M̃(r_row, r_col) = Σ_{(i, j, v) ∈ nnz(M)} v · eq(r_row, bits_ρ(i)) · eq(r_col, bits_ν(j)),   r_col ∈ K^ν.

The verifier computes this in `O(nnz + 2^ρ + 2^ν)` field multiplications by
first building `eq_table(r_row)` and `eq_table(r_col)` (or `O(nnz·(ρ + ν))`
directly). Here `r_col` has all `ν` variables including the top one. For K
structures `v ∈ K`; for B structures `v = 1`.

### 6.2 K-relation details (Q2)

*Computing `A_2 z`.* Matrix entries are in `K`; `z` is a bit vector (or, for the
public part, `K` elements). For bit `z_j`, the product `v · z_j` is `v` or 0, so
`(A_2 z)_i = ⊕_{(i,j,v), z_j = 1} v` is an XOR of 128-bit constants, with no
`K` multiplication. A prover MAY precompute for each row the list of its
columns; no per-column packing table is required. For the public column
(`z_{2^(ν−1)} = 1`) and for `x`, the entry is multiplied by `x` in `K` as
usual. The result `A_2 z, B_2 z, C_2 z` are vectors over `K`, and the outer
sum-check treats them as arbitrary `K` tables. Over B the three vectors are
bit vectors, embedded in `K`.

*The packed example (§5.1).* With `β_i = X^i` (C1), the `b` bit constraints
`y_i = c · x_i` are one row: `A = (c at its column)`, `B = Σ_i X^i · [column
of x_i]`, `C = Σ_i X^i · [column of y_i]`. Then `(Az)(Bz) = c · pack(x)` and
`Cz = pack(y)`, where `pack` is the C1 packing, so the row holds iff all `b`
bit equations hold (the `X^i` are linearly independent over B, and `c, x_i,
y_i ∈ B`). Section 10 owns the actual K relation; `reference/openmagnetar/
toy_cpu.py` has this row and a variant with a K-valued coefficient in `A` and
`C`.

*Soundness caveat.* `W` is bit-valued by construction (it is committed as bits),
which is what makes a K-linear equation over packed groups equivalent to the
per-bit equations. Spartan does not enforce booleanity; the commitment does.

### 6.3 Construction 1 (Spartan reduction) as a RoK, SIMD form

This section defines one procedure parameterised by a list of `T` relations
(`T = 1` for Construction 1, SIMD Spartan and BinarySpartan; `T = 2` for
Virtual Spartan, with relation names `bin` and `fld`) and a transcript prefix
`P` (below). Call it `Spartan(P, rels, s, W, X)`. Differences from the paper are
**[OM-choice]**s listed in 6.10.

*Inputs.* Public: structures (from the verifying key), `s = log q`, and
`X = (x_u)`. Witness: `W`. The prover is given `W` before the reduction starts.
The surrounding protocol has already fixed the commitments that bind `W`'s
direct segments (section 11); no commitment is sent here.

**Transcript prefixes.** Every label below is `P ‖ "/" ‖ …`, with
`P = b"vsp"` for Virtual Spartan and for every use in section 11 (and in the
reference tests, including `T = 1`). Round names are the relation names `bin`
and `fld`, in that order; for `T = 1` the single relation is named `bin`
whatever its field.

**Step 0, binding of the shape and the public input.**

    absorb_bytes(P/shape, u64le(T) ‖ u64le(ρ) ‖ u64le(ν) ‖ u64le(s) ‖ u64le(n_x))
    absorb_ks   (P/pub,   [x_u[k] as K, for u = 0..q−1, k = 0..n_x−1])        # empty list when n_x = 0

(The verifying key digest is absorbed by section 11 before.) Bits and `F`
elements of `x` are converted to `K` by the embedding of C1.

**Step 1, outer challenges.** For `t` in relation order (`bin`, then `fld`):

    τ_t ← challenge_ks(P/tau/<name_t>, ρ + s)        (τ_t ∈ K^(ρ+s), variable order: row variables low, instance variables high)

**Step 2, the outer sum-check (zero-check) for each relation.** For relation
`t` define the tables over `{0,1}^(ρ+s)` (index `row + 2^ρ·u`):
`a_t[row + 2^ρ u] = (A_t z_u)_row`, similarly `b_t, c_t`, and `E_t = eq_table(τ_t)`.
The claim is

    0 = Σ_{x ∈ {0,1}^(ρ+s)} E_t(x) · ( a_t(x) · b_t(x) + c_t(x) ),

(the polynomial `g_t`, degree 3 in each variable, `+` is `−`). Its variables are
bound in the order `x_1 … x_{ρ+s}`: the `ρ` **row variables first**, then the
`s` **instance variables**. **[OM-choice] row-first**: this follows from C2
(instance index in the high bits) and C3 (low-to-high), and it lets a prover
treat one instance at a time during the first `ρ` rounds (6.9). The paper's
order `(r_inst, r_row)` is merely a notational choice, and soundness does not
depend on it.

The initial claim of every relation is the constant `0`, so nothing is absorbed
for it. **Rounds.** Let `claim_t` be the running claim of relation `t`,
initially `0`. Each round message `m = [g(t_0), g(t_2), g(t_3)]` is three `K`
elements. The verifier derives `g(1) = claim_t + g(0)`, interpolates `g`
through `t_0..t_3` and sets `claim_t ← g(r)` (03, 3.4).

* **Row rounds** `i = 1 … ρ`. For `t` in relation order: the prover sends
  `m_{t,i}`; both run
  `absorb_ks(P/outer/<name_t>/msg, m_{t,i})` and
  `r_{row,t,i} ← challenge_k(P/outer/<name_t>/row)`.
  (So the order within a round is: bin message, bin challenge, fld message, fld
  challenge. Each relation has its **own** row challenges.)
* **Instance rounds** `j = 1 … s`. The prover sends `m_{t,ρ+j}` for **all** `t`.
  Both absorb them in relation order with
  `absorb_ks(P/outer/<name_t>/msg, ·)`, and then squeeze **one** challenge
  `r_{inst,j} ← challenge_k(P/outer/inst)`, used by all relations. (So the
  shared instance challenge is drawn after both messages of that round.)

The row challenges are not shared although the instance challenges are,
because (paper §5.3, footnote 5) the two relations may use different
univariate-skip parameters. Skip is off in v1 (C3), so sharing them would also
be sound, and would save `ρ` field elements of challenge; we keep them
separate to leave the extension open **[OM-choice]**. The round counts are
`ρ + s` for every relation by 6.1.

**Step 3, terminal values.** The prover sends `v_{t,A}, v_{t,B}, v_{t,C}`, the
values at `(r_{row,t}, r_inst)` of the MLEs of `a_t, b_t, c_t`. The verifier
checks, for every `t`,

    claim_t = eq(τ_t, r_{row,t} ∥ r_inst) · ( v_{t,A} · v_{t,B} + v_{t,C} ),

where `claim_t` is the claim left by the last round. For `t` in order, both then
run `absorb_ks(P/outer/<name_t>/final, [v_{t,A}, v_{t,B}, v_{t,C}])`.

**Step 4, batching the terminal values.** For the `3T` values in the order
`(bin A, bin B, bin C, fld A, fld B, fld C)`, both squeeze

    α ← challenge_ks(P/alpha, 3T)        (independent coefficients α_{t,M})

and set `v⋆ = Σ_{t,M} α_{t,M} · v_{t,M}`. **[OM-choice]** independent
coefficients, as in the paper's Construction 2, also for `T = 1` (the paper's
Construction 1 uses `r, r^2`; independent ones give the same `1/|K|`-class error
and a single code path).

**Step 5, the inner sum-check over columns.** Define the public table
`MC(y) = Σ_{t,M} α_{t,M} · M̃_t(r_{row,t}, y)` over `y ∈ {0,1}^ν` (a table of
length `2^ν`: `MC = Σ α_{t,M} · fold_rows(M_t, r_{row,t})`) and the folded vector
`ZF` (6.1) of length `2^ν`: `ZF[c] = Σ_u eq(r_inst, u) W[u][c]` for `c < 2^(ν−1)`
and `ZF[2^(ν−1) + k] = PF[k]`. Run

    sumcheck(claim = v⋆, tables [MC, ZF], combine = product, d = 2, label = P/inner)

with `sumcheck_prove` / `sumcheck_verify` (03). It has `ν` rounds, so the
messages are `2` elements per round, and binds `y` to `r_y ∈ K^ν`. The
verifier gets the final claim `e′`.

**Step 6, the witness claim.** Write `r_col = (r_{y,1} … r_{y,ν−1})` and
`top = r_{y,ν}`. The prover sends `v_W = W̃(r_col ∥ r_inst)` and both run
`absorb_k(P/vw, v_W)`. The verifier computes `M̃_t(r_{row,t}, r_y)` for every
`t, M` by 6.1, `pf = PF~(r_col)`, `v_z = (1 + top)·v_W + top·pf`, and checks

    e′ = ( Σ_{t,M} α_{t,M} · M̃_t(r_{row,t}, r_y) ) · v_z .

**Step 7, output.**

* `Construction 1 / SIMD / BinarySpartan` (no segment layout): output the
  evaluation claim `W̃(r_col ∥ r_inst) = v_W` on the whole matrix (an
  `R^B_veval` instance, `ν − 1 + s` variables, prover also outputs `W`).
  For standalone BinarySpartan, ring switching (section 04) and the PCS follow.
* With a layout: continue with 6.5.

**Lemma 6.1** (the paper's Lemma 1, instantiated). Completeness is perfect.
Soundness error of the reduction for `T` relations, in terms of the
Schwartz–Zippel lemma and sum-check soundness:

    ε_outer  = T · ( (ρ + s) + 3(ρ + s) ) / |K|            # per relation: τ, then 3 per round
    ε_batch  = 1 / |K|                                      # six (3T) terminal values, independent α
    ε_inner  = 2ν / |K|                                     # degree 2, ν rounds
    ε_spartan = ε_outer + ε_batch + ε_inner = ( 4T(ρ+s) + 1 + 2ν ) / |K| .

Justification of `ε_outer`: if some row of some instance violates the
relation, `Σ_x eq(τ, x)(…)` is the evaluation at `τ` of the MLE of the
non-zero vector `(Az)∘(Bz) + Cz`, a non-zero multilinear polynomial in `τ` of
total degree at most `ρ + s`, so it is zero for at most `(ρ+s)/|K|` of the
`τ`. For non-zero sum the sum-check then fails with probability
`≥ 1 − 3(ρ+s)/|K|`. Sharing the instance challenges does not change this: each
relation's outer sum-check is an ordinary sum-check whose round challenges are
uniform and independent of the messages of that round, and the messages of the
other relation are fixed by the prover before the challenge is drawn. If the
terminal values are wrong, the `α`-combination `v⋆` is wrong except with
probability `1/|K|`. The inner claim is then false and the sum-check catches it
except with `2ν/|K|`. Knowledge soundness follows by the standard extractor
(the witness is the `W` that the claim at the end pins down).

### 6.4 BinarySpartan restriction

BinarySpartan is Construction 1 with `T ≥ 1` over `W ∈ B`. Nothing in 6.3
changes: both sum-checks run over `K`, and only the *tables* are special: `W`
and `A z` for a B-structure are bit-valued, and the first rounds can exploit it
(6.9). The output claim is on a bit-valued polynomial (`R^B_veval`), as required
by ring switching (04). The verifier **MUST** reject a proof for a structure
over `B` whose matrix entries are not in `{0, 1}` (a check on the verifying
key, not on the proof).

### 6.5 Construction 2: Virtual Spartan

Virtual Spartan is `Spartan(P = b"vsp", [s_bin, s_fld], …)` of 6.3 with
`T = 2`, followed by the segment split below. The ordered steps 0–6 of 6.3 are
exactly the paper's steps 1–4 (the lockstep outer sum-check, the six terminal
values, the batching, the single inner sum-check), and what follows implements
steps 5–8.

**Segment layout (public, from section 10).** A layout is an ordered list of
segments `(id, kind, ℓ_i, β_i)`:

* `id`: a `u32` that is also the component id used in section 05 (for direct
  segments) or the owner key in section 11 (for virtual segments);
* `kind ∈ {direct, virtual, pad}`;
* `ℓ_i ∈ [0, ν−1]`, the log of the segment's column count;
* `β_i ∈ [0, 2^(ν−1−ℓ_i))`, the block index: the segment's columns are
  `[β_i·2^(ℓ_i), (β_i + 1)·2^(ℓ_i))`. Equivalently, the column index has the
  fixed **suffix** `b_i = bits_{ν−1−ℓ_i}(β_i)` (little-endian) in its high
  `ν−1−ℓ_i` bits (C2), and the low `ℓ_i` bits are local.

Validity: aligned (by construction), inside `[0, 2^(ν−1))`, pairwise disjoint,
ids distinct. A verifier MUST reject an invalid layout. **Columns covered by no
segment and columns of `pad` segments are padding and must be zero in `W`.**
(`pad` entries are optional documentation of a deliberate gap; they behave
exactly like uncovered columns.) Layout order is the order of the list.
Non-pad segments appear in the proof and in the transcript in that order. The
polynomial of segment `i` is the flat table of `W_i` indexed
`y + 2^(ℓ_i)·u` (local column `y`, instance `u`), a bit-valued polynomial in
`ℓ_i + s` variables: its **Mosaic component log size is `ℓ_i + s`**.

**Steps 7–8: segment claims.** Split `r_col = (ρ_i, q_i)` with `ρ_i = r_col[0 :
ℓ_i]` (local) and `q_i = r_col[ℓ_i : ν−1]` (suffix variables). Because the
subcubes partition the columns of `W` (up to zero padding),

    W̃(r_col ∥ r_inst) = Σ_{i non-pad} eq(q_i, b_i) · W̃_i(ρ_i ∥ r_inst).             (6.2)

* The prover sends `v_i = W̃_i(ρ_i ∥ r_inst)` for every non-pad segment in
  layout order; each is absorbed with `absorb_k(P/seg, v_i)` (same label every
  time).
* The verifier checks `v_W = Σ_i eq(q_i, b_i)·v_i` with
  `eq(q_i, b_i) = Π_k (1 + q_{i,k} + b_{i,k})`, and aborts otherwise. Padding
  segments are absent from the sum (their `v_i` is 0 and is not sent), so a
  prover with non-zero padding columns fails this check.
* **Output claims**, in layout order: `(id_i, point = ρ_i ∥ r_inst, v_i)` for
  every non-pad segment. A claim on a `direct` segment is handed to section 05
  (as a claim on component `id_i`); a claim on a `virtual` segment goes to
  the auxiliary reduction named by `id_i` in section 11.

**v_W is sent although it is derivable** from the `v_i`: this follows the paper
(Step 4 uses it before the segments are known) and keeps the inner sum-check
check independent of the layout. Cost: one element.

**Lemma 6.2** (Lemma 3 of the paper). Virtual Spartan is a public-coin RoK
`R_dual → Π_i R^B_veval` over the non-pad segments, with knowledge error
`ε_vsp = ε_spartan` of Lemma 6.1 (`T = 2`): `(8(ρ+s) + 1 + 2ν)/|K|`. Step (6.2)
is an exact identity, so it adds no error. With cross-step constraints (6.6)
the error is `ε_vsp + ε_xs`.

### 6.6 Cross-step constraints (our design; the paper's Remark 4 omits them)

**[OM-choice]** Relation 3, over B, on the shared `W`. The layout designates two
**whole segments** `S_in` and `S_out` of the same size `2^λ` columns (`ℓ = λ`,
neither is `pad`), the carry-in and the carry-out state of an instance, and the
public vectors `init, fin ∈ B^(2^λ)`. Write `Win(k, u) = W[u][S_in + k]` and
`Wout(k, u) = W[u][S_out + k]` for `k ∈ [0, 2^λ)`, `u ∈ [0, q)`; these are
exactly the polynomials of the segments `S_in` and `S_out`
(flat index `k + 2^λ·u`). The relation is

    (X1)  Win(k, u)       = Wout(k, u − 1)    for all k and 1 ≤ u ≤ q − 1,
    (X2)  Win(k, 0)       = init(k)           for all k,
    (X3)  Wout(k, q − 1)  = fin(k)            for all k.

Rationale: the paper only says "next MLE [53]" (Setty–Thaler–Wahby, CCS,
ePrint 2023/552, and the Spartan/Jolt shift-sum-check technique). Using whole
segments makes the reduction output ordinary segment claims, so no new claim
type reaches Mosaic or the auxiliary arguments; any set of state fields (micro-PC,
PC, halted flag, …) is made carry-able by placing it into `S_in`/`S_out` in the
same order (section 10 decides which; see Requests). `q = 1` is allowed: (X1)
is empty and (X2), (X3) both apply to instance 0.

**Reduction.** It runs *after* the segment claims of 6.5 (its transcript
position is part of 6.5's output) and uses its own challenges, so its claims
are at a *different point* from the segment claims of 6.5.

1. Both parties absorb the public state:
   `absorb_ks(P/xs/init, init)`, `absorb_ks(P/xs/fin, fin)` (bits as `K`).
   (`len(init) = len(fin) = 2^λ` is checked by the verifier.)
2. `τ ← challenge_ks(P/xs/tau, λ + s)`, with `τ = (τ_k, τ_u)`, `τ_k ∈ K^λ`,
   `τ_u ∈ K^s`; then `γ ← challenge_k(P/xs/gamma)`.
3. Define the public tables over `u ∈ [0, q)`:

       a_out(u) = [u ≠ q−1]·eq(τ_u, u) + γ²·[u = q−1],
       a_in(u)  = [u ≥ 1]·eq(τ_u, u−1) + γ·[u = 0],

   and the claim `c = γ·init~(τ_k) + γ²·fin~(τ_k)` (the verifier computes both
   MLEs of the public vectors). The relation is checked by the sum-check

       c = Σ_{(k,u) ∈ {0,1}^(λ+s)}  eq(τ_k, k) · ( a_out(u) · Wout(k, u) + a_in(u) · Win(k, u) ),

   run with `sumcheck(c, 5 tables [eq_k, a_out, Wout, a_in, Win] extended to
   {0,1}^(λ+s) (index k + 2^λ·u), d = 2, label = P/xs/sc)`. Variables are `k`
   first, then `u`. The summand has degree 2 in each variable (each variable
   is either a `k` variable, appearing in `eq_k` and `W`, or a `u` variable,
   appearing in `a(u)` and `W`), so the C3 message has 2 elements; the
   *declared* degree is 2 (the reference passes a degree-3 `combine` on the
   extended tables: the true univariate has degree ≤ 2).
4. The sum-check returns `r = (r_k, r_u) ∈ K^(λ+s)` and the final claim `e`.
   The prover sends `v_in = W̃in(r)` and `v_out = W̃out(r)`;
   `absorb_ks(P/xs/final, [v_in, v_out])`. The verifier computes

       A_out = eq(τ_u, r_u) + (Π τ_u)(Π r_u) + γ²·(Π r_u),
       A_in  = N~(τ_u, r_u) + γ · Π (1 + r_u),

   and checks `e = eq(τ_k, r_k) · ( A_out · v_out + A_in · v_in )`.
5. **Output claims** (appended to those of 6.5, in this order):
   `(id(S_in), r, v_in)` and `(id(S_out), r, v_out)`. They have `λ + s`
   variables, the size of those components, so a component can carry several
   claims (05, "Several claims on one component").

**The `next` MLE.** `N(a, b) = 1` iff `int(b) = int(a) + 1` and
`int(a) < 2^s − 1` (little-endian integers, zero elsewhere on `{0,1}^s ×
{0,1}^s`); `N~` is its MLE. For `a, b ∈ K^s` (0-indexed bits `i`):

    N~(a, b) = Σ_{i=0}^{s−1} [ Π_{j<i} a_j (1 + b_j) ] · (1 + a_i) · b_i · [ Π_{j>i} (1 + a_j + b_j) ] .

(`a_i = 0, b_i = 1` at the position where the increment stops; lower bits
`a_j = 1, b_j = 0`; higher bits equal.) It is computed in `O(s)` with a running
prefix product and a suffix-product array (the reference implementation, tested
against brute force), and `N~ = 0` for `s = 0`. The weight `A_in` uses
`Σ_{u'} eq(τ_u, u')·N(u', ·) = N~(τ_u, ·)`, and `A_out` the MLE of
`u ↦ eq(τ_u, u)·[u ≠ q−1]`, which is `eq(τ_u, r_u) + eq(τ_u, 1^s)·eq(1^s, r_u)`
(note: the MLE of a pointwise product is *not* the product of MLEs, hence the
correction term; `eq(1^s, r_u) = Π r_u`, `eq(τ_u, 1^s) = Π τ_u`); the
indicators `[u = q−1]` and `[u = 0]` have MLEs `Π r_u` and `Π(1 + r_u)`.

**Why it is correct.** For all `(k, u')`, define `P(k,u') = [u' < q−1]·Wout(k,u')`
and `Q(k,u') = [u' < q−1]·Win(k, u'+1)`. (X1) is `P = Q` as tables. The sum in
step 3 equals

    Σ_{k, u' < q−1} eq(τ, (k, u')) · (Wout(k,u') + Win(k,u'+1))        (the shift term, zero iff X1 holds, for random τ)
      + γ · Σ_k eq(τ_k, k) · Win(k, 0) + γ² · Σ_k eq(τ_k, k) · Wout(k, q−1),

and if (X1)–(X3) hold it equals `c`. Conversely, the difference of the sum and
`c` is, as a polynomial in `(τ, γ)`, equal to `F1(τ) + γ·F2(τ_k) + γ²·F3(τ_k)`
with `F1 = (P + Q)~(τ)`, `F2 = (Win(·,0) + init)~(τ_k)`, `F3 = (Wout(·,q−1) +
fin)~(τ_k)`; it is non-zero as a polynomial iff one of the (X) equalities is
violated.

**Soundness.** `ε_xs`: that polynomial has total degree at most `(λ+s) + 2` in
`(τ, γ)`, and the sum-check has `λ+s` rounds of degree 2:

    ε_xs = ( (λ + s) + 2 + 2(λ + s) ) / |K| = ( 3(λ + s) + 2 ) / |K| .

**Cost.** `λ + s` extra rounds, `2(λ+s)` field elements in messages plus 2
element values, and two extra evaluation claims on `S_in`/`S_out`. The
verifier does `O(2^λ + s)` work. The prover does `O(2^λ·q)` work, linear in the
two state segments (a prover MAY use the sparsity of `eq_k` and fold state
`Win`, `Wout` incrementally).

**What this enforces.** With (X1)–(X3) and the per-instance relations, the
sequence of instances is a single execution from the public initial state to
the public final state. Section 10 puts micro-PC, PC, halted flag, and
whatever else must flow between instances in `S_in`/`S_out`. *Alternative
considered*: encode the chain in the relations by letting `x_u` contain the
previous instance's out-state. This makes `n_x` grow with `q` and the verifier
read `O(q·2^λ)` public data; we avoid it.

### 6.7 Complete transcript order (summary)

For `Spartan(P)` with `T` relations (labels are `P ‖ "/" ‖ …`):

| # | Action | Label |
|---|---|---|
| 0 | absorb shape (5 `u64le`) | `shape` |
| 0 | absorb public inputs | `pub` |
| 1 | squeeze `τ_t` (`ρ+s` elements), per relation | `tau/<name>` |
| 2 | row rounds, per round and per relation: absorb msg (3 K), squeeze `r_row` | `outer/<name>/msg`, `outer/<name>/row` |
| 2 | instance rounds, per round: absorb msg for each relation, squeeze one `r_inst` | `outer/<name>/msg`, `outer/inst` |
| 3 | absorb terminal values `[vA, vB, vC]` per relation | `outer/<name>/final` |
| 4 | squeeze `α` (`3T` elements) | `alpha` |
| 5 | inner sum-check (03 adds `/claim`, `/params`, `/msg`, `/chal`) | `inner` |
| 6 | absorb `v_W` | `vw` |
| 7 | absorb each non-pad `v_i` | `seg` |
| 8 | (cross-step) absorb `init`, `fin`; squeeze `τ` and `γ` | `xs/init`, `xs/fin`, `xs/tau`, `xs/gamma` |
| 9 | (cross-step) sum-check; absorb `[v_in, v_out]` | `xs/sc`, `xs/final` |

The inner and cross-step sum-checks therefore use the base labels
`vsp/inner` and `vsp/xs/sc`. Order of proof fields (for section 12): outer
messages (all of relation `bin`, then `fld`, each `ρ+s` messages of 3
elements), terminal values (3 per relation), inner messages (`ν` of 2),
`v_W`, `v_i` (layout order), cross-step messages (`λ+s` of 2) and
`[v_in, v_out]`. Element counts: `T·3(ρ+s) + 3T + 2ν + 1 + (#segments) +
2(λ+s) + 2`.

### 6.8 Verifier algorithm

`verify` checks, in order: shape and layout validity (6.5); `len(msgs) = ρ+s`
per relation; for each round the message has exactly 3 `K` elements (a wrong
count or type is a `VerificationError`); the outer final check of 3 per
relation; the inner sum-check and its final check; the segment identity
`v_W = Σ eq·v_i`; the cross-step sum-check and its final check. Any failure
raises `VerificationError` (03). Output claims are returned only on success.
Cost: `O(T(ρ+s)) + O(Σ nnz + T·2^ρ + 2^ν) + O(2ν) + O(#segments·ν) +
O(2^λ + s)` field operations (`O(n_x·q)` more if `n_x > 0`).

### 6.9 Prover algorithms (informative)

* **Tables.** `A_t z_u` is computed sparsely per instance (6.2): XOR of K
  constants for bit `z`. `E_t = eq(τ_t, ·)` is not materialised: it factors as
  `eq(τ_{t,row}, row) · eq(τ_{t,inst}, u)`; the row-phase tables are
  streamed per instance.
* **Small-value first rounds.** Over B (`T = bin`) `a, b, c` and the witness are
  bits, so the product `a·b` is a bit and round 1's `g(t_0), g(t_2), g(t_3)`
  need no `K·K` product (`a(t) = a_0 + t(a_0 + a_1)` is a `K`-linear
  combination of two bits). The first `~7` rounds (before the tables become
  dense `K` elements) can be run with `u64`/bit-sliced arithmetic.
* **Gruen eq-factoring (ePrint 2024/108).** In round `i`, `g(X) = eq_i(X)·h(X)`
  with `eq_i(X) = (1 + τ_i + X)·…`: it suffices to compute the degree-2 `h` at
  two points (`t_0`, `t_2`; `h(1)` follows from `g(0)+g(1) = claim`) and the
  message is `g(t) = eq_i(t)·h(t)`. This saves one of three evaluations per
  round, without changing the C3 message.
* **Dual in one pass.** The prover walks the `(row, u)` index space once per
  round and updates *both* relations' tables from the same loop over the
  shared witness, since the A/B/C tables depend only on `W` and the (sparse)
  matrix rows; the row-phase tables of the two relations are bound with
  different challenges, so they are separate accumulators, but the instance-phase
  tables are the bound tables of rounds `ρ+1…ρ+s` and share their challenge.
  Per round the prover emits its two messages (bin first, fld second) after
  the previous challenge is known.
* **Inner sum-check.** `MC` is built with `fold_rows` (one pass over `nnz`),
  `ZF` by one pass over `W` weighted by `eq_table(r_inst)`. These are the
  `O(q·2^(ν−1))` and `O(nnz)` steps; the sum-check is then a standard
  linear-time sum-check on two tables of length `2^ν`.
* **Cross-step.** `Win, Wout` are the two state segments: a table of
  `2^λ·q` bits each; the sum-check is cheap since the state is small.

### 6.10 Resolved questions

1. **Q1 (cross-step).** Resolved by **[OM-choice]** 6.6: a third B-relation on
   segments `S_in`, `S_out` with a shift sum-check using `N~`, public
   `init`/`fin` bound by (X2), (X3), outputting two extra claims at a separate
   point `(r_k, r_u)`. The state that crosses (micro-PC, PC, halted flag, …)
   is the content of `S_in`/`S_out`, chosen in section 10. Soundness entry:
   `ε_xs = (3(λ+s) + 2)/|K|` (section 13).
2. **Q2 (K-relation).** K-valued entries with bit `z`: XOR of constants
   (6.2). No separate coefficient table is needed.
3. **Q3 (outer degree over B).** Yes: degree-3 `g` and the C3 message of 3
   elements at the protocol level; the bit structure only affects prover
   arithmetic (6.9). (A B-only structure could use `(Az)` bits to skip `K·K`
   products, but not fewer messages.)
4. **Q4 (public x).** **[OM-choice]** `n_x = 0` in v1; the public initial and
   final state are `init`, `fin` of 6.6 (their values are derived from the
   verifying key / run header in section 11) and I/O bytes live in RAM, bound
   by `M_0` and the final-memory claim (C6). The mechanism for `n_x > 0` stays
   in the spec (6.1) and in the tests.

Other **[OM-choice]**s: rectangular `(ρ, ν)` (6.1); row-first binding order
(6.3); separate row challenges (6.3); independent `α` coefficients for every
`T` (6.3); `v_W` explicit (6.5); segments need not cover all columns, and
uncovered columns are zero padding (6.5).

### 6.11 Reference model and tests

Modules: `reference/openmagnetar/r1cs.py` (sparse matrices over B/K,
`mul_vec`, `mle`, `fold_rows`, `build_z`, `simd_satisfied`), `spartan.py`
(`prove`, `verify`, `Segment`, `CrossStep`, `next_mle`, `xs_weights`,
`check_layout`), `toy_cpu.py` (the toy two-relation example below), and
`mosaic.Claim`, the claim type shared with section 05. Toy example
(`toy_cpu.py`): `q = 4` instances of a 4-bit accumulator step `acc' = acc + a
mod 16` as a ripple-carry adder over B (8 rows), plus a packed mux `y = sel·x`
over K (2 rows, one with `X^5` coefficients), `ν = 6, ρ = 3`, with `S_in`,
`S_out` as 4-column state segments, `init = 0` and `fin` the final sum.
Tests (`reference/tests/test_spartan.py`): MLE and `fold_rows` against brute
force, `next_mle` against brute force, plain SIMD Spartan over B, over K, with
`q = 1`, with public inputs; Virtual Spartan completeness for `q = 1, 2, 4, 8`
and with non-zero `init`, with all output claims checked against direct MLE
evaluation of the witness segments; negative tests: unsatisfied B constraint,
unsatisfied K constraint, per-row valid but chain-inconsistent witness
(prover refuses, and a cheating prover's proof is rejected), wrong public
`init`/`fin`, each per-segment claim tampered, tampered outer (bin and fld,
row and instance rounds), terminal, inner, `v_W` and cross-step messages,
non-zero padding columns. Vectors: `reference/vectors/06-spartan/`
(`virtual_spartan_toy.json`, `simd_spartan_bin.json`, `next_mle.json`),
generated by `reference/gen_vectors_05_06.py`; they contain the witness, every
proof element, the output claims and the next challenge after the protocol
(`transcript_final`). Replay test: `reference/tests/test_vectors_05_06.py`.

### Requests to other sections

* **Section 10** (witness layout): provide `ν`, `ρ`, the segment list
  `(id, kind, ℓ_i, β_i)` with aligned blocks, **two state segments `S_in` and
  `S_out` of equal size** carrying everything that must cross instance
  boundaries (the same field order in both), and public `init`/`fin` as
  functions of the verifying key and run header. All other columns not in any
  segment must be genuinely unused (zero).
* **Section 11:** absorb the verifying-key digest and the run header (`init`,
  `fin` source) before calling `Spartan`; fix the claim order passed to 05
  (6.5 output order, then 6.6 claims); pass `s = log2(q)`.
* **Section 12:** proof field order in 6.7.
* **Section 13:** soundness entries `ε_spartan`, `ε_xs` of 6.3, 6.6.
* **Section 03:** none (the module uses `sumcheck_prove/verify` as specified;
  the lockstep outer rounds implement the same message format with a local
  Lagrange helper, `interpolate_eval`, `_interp`).
