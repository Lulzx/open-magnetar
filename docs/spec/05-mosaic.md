# 05. MosaicPCS

**Status:** draft · **Paper:** §5.2

## Scope
Layout algorithm placing N power-of-two-sized bit polynomials on disjoint
aligned subcubes of one hypercube, the suffix s_i of each, claim lifting
(Eq. 4), the batching sum-check, and hand-off to ring switching + PCS.

## Specification

Notation: `|K| = 2^128`; indexing and concatenation follow C2 (little-endian;
`r ∥ s` has `r` in the low variables and `s` in the high variables; a *suffix*
fixes the high variables).

### 5.1 Components

A **component** `p_i` is a bit-valued polynomial `p_i : {0,1}^(ℓ_i) → B`,
given as a table of `2^(ℓ_i)` bits. Each has a public **component id**
`id_i ∈ [0, 2^32)`, unique within a verifying key, and a log size `ℓ_i ≥ 0`.
Components are the direct segments of the R1CS witness (section 06, whose
log size is `ℓ_seg + s`) and the polynomials the auxiliary arguments commit to
(sections 07, 08). **All components are bit-valued**: a component table with an
entry outside `{0, 1}` is a prover error, and no verifier operation depends on
it except through the ring-switching step (04) that relies on `G` being bits.
The id and log size of every component are fixed by the verifying key (10, 11).

### 5.2 Layout algorithm (Q1, Q2)

**[OM-choice]** The layout is a deterministic function of the list
`L = [(id_i, ℓ_i)]` and a parameter `ℓ_min` from the verifying key, so the
prover and verifier compute it independently and the layout carries no proof
data.

    compute_layout(L, ℓ_min):
        reject if two entries share an id
        sort L by (ℓ desc, id asc)                     # canonical order, "layout order"
        cursor ← 0
        for (id, ℓ_i) in sorted L:
            offset_i ← cursor;  s_i ← offset_i >> ℓ_i  # offset_i is a multiple of 2^(ℓ_i)
            cursor ← cursor + 2^(ℓ_i)
        N_tot ← cursor                                 # = Σ 2^(ℓ_i)
        ℓ ← max( ceil_log2(N_tot), max_i ℓ_i, ℓ_min )
        return ℓ, [(id_i, ℓ_i, offset_i, s_i)]        # in layout order

`ceil_log2(1) = 0`. For an empty list the layout is rejected. **This is the
buddy allocation** the outline asks for: because the sizes are powers of two
sorted in non-increasing order, the running cursor is always a multiple of the
size of the next block (induction: the cursor is a sum of powers of two that
are each at least the current size), so sequential placement is aligned, has no
gaps between components, and is the unique minimal-prefix packing; no free
list or splitting is needed, and equal inputs give equal layouts regardless of
list order. All free space is one zero region at the end:
`[N_tot, 2^ℓ)`.

**The subcube of component `i`** is `{ x ∥ s_i : x ∈ {0,1}^(ℓ_i) }`, where the
suffix `s_i ∈ {0,1}^(ℓ−ℓ_i)` is the little-endian bit vector of the integer
`offset_i >> ℓ_i`. In index terms the entry `x` of `p_i` is entry
`offset_i + x` of `G`. Suffixes are pairwise distinct as subcubes: the index
intervals `[offset_i, offset_i + 2^(ℓ_i))` are disjoint and aligned.

**`G`** is the bit vector of length `2^ℓ` with `G[offset_i + x] = p_i[x]` and
zero elsewhere (including the tail).

**Interaction with packing (ℓ_min).** The PCS commits to the packing `P_G` of
`G` into `2^(ℓ−7)` elements of `K` (128 bits per element, C1; ring switching
of 04 requires `ℓ ≥ 7`). The PCS (04) has a minimum number of variables `μ_min`
for its packed polynomial (a verifying-key parameter of the Ligerito
configuration). **[OM-choice]**

    ℓ_min = 7 + μ_min

so `ℓ ≥ 7 + μ_min` always holds, and a small program does not produce a `G`
too small for the PCS; the extra space is zeros. Components with `ℓ_i < 7` are
legal: they occupy part of one packed `K` element.

**Wasted space (Q2).** **[OM-choice]** `ℓ` is the *minimal* admissible value
(above), and the zero tail is committed and encoded like any other region. The
waste is `2^ℓ − N_tot` bits. When `ℓ = ceil_log2(N_tot)` it is less than half
of `G` (and exactly 0 if `N_tot` is a power of two); when `ℓ_min` forces `ℓ`
higher the waste is larger but the program is small. Rationale: any non-minimal `ℓ`
adds proving cost without benefit, and the alternatives (a non-power-of-two
code length, or splitting the biggest component across two halves) complicate
the PCS and the lifting for a gain of at most `2×` in commit time. Section 10
SHOULD choose segment sizes so that `N_tot` sits just below a power of two
(the trace length `T` is already a power of two (C6)). The tail also is the
default place to put more components later, and the layout algorithm needs no
change for it.

### 5.3 Lifting (Eq. 4)

A claim on component `i` is `Claim(id_i, r, v)` with `r ∈ K^(ℓ_i)`: the
assertion `p̃_i(r) = v`. Fixing the high `ℓ − ℓ_i` variables of `G̃` to the
Boolean point `s_i` restricts `G` to the subcube of `i`, where it is `p_i`, so
for every `r ∈ K^(ℓ_i)` (Eq. 4, in C2 order):

    G̃(r ∥ s_i) = p̃_i(r).

The **lifted claim** is therefore `G̃(r ∥ s_i) = v`: the verifier appends the
suffix bits `s_i` as the high variables (as `K` elements `0` or `1`) to the
claim's point. The verifier MUST reject a claim whose id is unknown or whose
point length is not `ℓ_i` (`VerificationError`). No sum-check and no extra
message is needed for lifting.

### 5.4 The batching sum-check

*Input.* An ordered list of `n ≥ 1` claims `(id_j, r_j, v_j)`, `j = 0 … n−1`,
**in the order fixed by section 11**: Mosaic does not sort or deduplicate it.
The list, the ids and the points `r_j` are determined by the earlier
transcript and the verifying key; Mosaic absorbs only the values.

*Protocol* (the label `mos/batch` is the base label of 03's batching, 3.6):

1. `absorb_ks(mos/batch/claims, [v_0, …, v_{n−1}])`
2. `γ ← challenge_k(mos/batch/gamma)`; `α_j = γ^j` for `j = 0 … n−1` (so
   `α_0 = 1`). **[OM-choice]** powers of one challenge rather than `n`
   independent `α_j`: one squeeze, and the soundness loss is only `(n−1)/|K|`.
   (This is the paper's `α_i` with the specific choice `α_i = γ^i`; it agrees
   with 03's 3.6 convention.)
3. The claim is `c = Σ_j α_j · v_j`. Let `R_j = r_j ∥ s_{id_j}` be the lifted
   point, and

       E(x) = Σ_j α_j · eq(R_j, x),   x ∈ {0,1}^ℓ.

   The parties run the sum-check (03, `d = 2`, `ℓ` rounds, base label
   `mos/batch`; so 03 adds `/claim`, `/params`, `/msg`, `/chal`) for

       c = Σ_{x ∈ {0,1}^ℓ} E(x) · G(x),

   which holds since `Σ_x eq(R_j, x)·G(x) = G̃(R_j) = v_j`. The summand has
   degree 2 in each variable and messages have 2 elements. It binds `x` to
   `r_G ∈ K^ℓ` and leaves the final claim `e`.
4. The prover sends `v_G = G̃(r_G)` and both run `absorb_k(mos/vg, v_G)`.
5. The verifier checks `e = ( Σ_j α_j · eq(R_j, r_G) ) · v_G`, which costs
   `O(n·ℓ)`, and aborts otherwise.
6. **Output**: the claim `G̃(r_G) = v_G`.

The proof is `ℓ` messages of 2 `K` elements, then `v_G`: `2ℓ + 1` elements.

*Prover note (informative).* `eq(R_j, x)` is `eq(r_j, x_low) · [x_high = s_j]`,
since the suffix `s_j` is Boolean. So `E` is supported on the subcubes that
carry claims, and `E` is built in `O(Σ_j 2^(ℓ_{id_j}))` by adding
`α_j · eq_table(r_j)` into the block at `offset_{id_j}`; the sum-check is the
usual linear-time two-table sum-check on `(E, G)`, with `G` a bit vector in
the first rounds (small-value optimisation).

### 5.5 Hand-off to ring switching (section 04)

The output of Mosaic is exactly one claim

    G̃(r_G) = v_G,       r_G ∈ K^ℓ,  v_G ∈ K,

on the multilinear extension of a **bit-valued** vector `G` of `2^ℓ` entries
(C2 order). Section 04 owns everything after this: ring switching reduces it to
a claim `P̃_G(r⋆) = v⋆` on the packed polynomial (`P_G[v] = Σ_j X^j ·
G[j + 128·v]`, C1), and one PCS evaluation argument proves it against the
commitment `cm_G`. `ℓ ≥ 7 + μ_min` (5.2) is the precondition. This section
does not define `cm_G`, the PCS, or ring switching.

### 5.6 Several claims on one component

The same component may carry more than one claim, at different points: for
example the state segments `S_in` and `S_out` (section 06 6.5 and 6.6, a claim
at `ρ_i ∥ r_inst` and a claim at the cross-step point), the one-hot components
of Twist/Shout (07) that several reductions read, or a component referred to
by both an auxiliary reduction and by Virtual Spartan. Each claim is lifted
and batched independently with its own `α_j`, and no deduplication is done
(two claims at the same point are not special). The order of such claims is
fixed by 11; the recommended order is *layout order of the component, then the
reduction order within it* (06's claims first). A prover that holds two claims
`(id, r, v)` and `(id, r, v′)` with `v ≠ v′` cannot produce a valid proof,
since the sum-check target is an identity in `G` and the combined claim is
false by 5.7.

### 5.7 Soundness

If some claim `j` is false, `v_j ≠ G̃(R_j)`, the polynomial in `γ` given by
`Σ_j γ^j (v_j + G̃(R_j))` is non-zero of degree `≤ n−1`, so the batched claim
`c` differs from the true value of `Σ_x E(x)G(x)` except for at most `n−1`
values of `γ`. A false sum-check claim is rejected except with probability
`2ℓ/|K|` (degree 2, `ℓ` rounds, 03). The last check is an exact identity:

    ε_mosaic = ( 2ℓ + n − 1 ) / |K| .

(The paper writes `O(ℓ)/|K|` for independent `α_i`. For `n ≪ 2^100` the
powers variant costs nothing.) Layout and lifting have no error. Ring switching
and the PCS add their own (04, 13). Knowledge soundness: the extractor of the
PCS yields `P_G`, hence `G`; the claim at `r_G` and the sum-check force every
lifted claim to hold for it.

### 5.8 Resolved questions

1. **Q1.** **[OM-choice]** Yes, as in 5.2: sort by `(ℓ desc, id asc)`, buddy
   (sequential) allocation; the verifier recomputes it from the verifying key.
2. **Q2.** **[OM-choice]** `ℓ` is minimal subject to `ℓ ≥ 7 + μ_min`, the zero
   tail is committed; the waste is at most half of `G` and is a sizing
   concern for section 10 (5.2).
3. **Q3.** **[OM-choice]** Powers of one `γ` (5.4); loss `(n−1)/|K|`.

### 5.9 Reference model and tests

`reference/openmagnetar/mosaic.py`: `compute_layout`, `Layout`, `Placement`,
`build_G`, `lift_point`, `batch_prove`, `batch_verify`, `Claim`, `BatchProof`,
`eq_sum_table`. It uses `sumcheck_prove` / `sumcheck_verify` and the transcript
of 02, 03. Tests (`reference/tests/test_mosaic.py`): sorted order, alignment,
disjointness, contiguity, `ℓ`, `ℓ_min`, independence of input order, duplicate
ids rejected; Eq. (4) against direct evaluation of `G̃` for each component;
batching completeness with several claims on one component, checked against
direct evaluation `G̃(r_G) = v_G`; negative tests: tampered round message,
tampered `v_G`, tampered claim value, unknown component id, wrong point
length, a false claim (prover refuses). Vectors:
`reference/vectors/05-mosaic/layout.json` and `batch.json`, generated by
`reference/gen_vectors_05_06.py`, replayed in `reference/tests/
test_vectors_05_06.py`.

### Requests to other sections

* **Section 04:** state `μ_min` (the minimum packed-polynomial variable count)
  so that `ℓ_min = 7 + μ_min`; accept the input claim of 5.5 (bit-valued `G`,
  `ℓ ≥ 7`).
* **Sections 10, 11:** component ids (unique `u32`) and log sizes for every
  direct segment (`ℓ_seg + s`) and every auxiliary committed polynomial;
  the claim order of 5.4 and 5.6. Choose sizes so `N_tot` is just under a power
  of two.
* **Section 13:** soundness entry `ε_mosaic = (2ℓ + n − 1)/|K|`.
* **Section 12:** `BatchProof` serialization: `ℓ` messages of 2 elements,
  then `v_G`.
