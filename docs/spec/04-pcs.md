# 04. Polynomial commitment: Ligerito and ring switching

**Status:** draft · **Paper:** §3.6, §6, refs [13,44,5]

## Scope
The PCS trait (commit / open / verify for multilinear polynomials over K),
Merkle tree layout and hashing, the Reed–Solomon code over binary fields
(additive NTT), the Ligerito protocol, and ring switching from a bit-valued
MLE claim to a claim on the packed polynomial P over K.

## Resolved questions

All six outline questions are resolved below. Choices that the paper does not dictate are marked **[OM-choice]**.

1. **RS domain and additive FFT.** **[OM-choice]** LCH novel-polynomial-basis additive NTT over the GF(2)-subspace `U_m = span{X^0, …, X^{m-1}}`, so the evaluation point `ω_q` is the K element with integer value `q` (4.3). *Why:* the monomial packing basis of C1 already gives a canonical subspace basis; no basis search or field-tower structure is needed, and the point list is just `0, 1, 2, …`.
2. **Recursion shape.** **[OM-choice]** All levels use rate `ρ = 1/4` (`r = 2`), fold arity 4 or 5, and the final polynomial has `2^6` entries (4.6, 4.7).
3. **Conjectured profile.** **[OM-choice]** Yes: `conjectured-100`, opt-in, non-provable, for comparison only (4.7).
4. **Merkle.** **[OM-choice]** Binary tree, `leaf = H(0x00 ‖ column)`, `node = H(0x01 ‖ l ‖ r)`, deduplicated multi-path, ascending order (4.2).
5. **Ring switching.** Written out fully for `β_j = X^j` in 4.5. The tensor-algebra step is implemented with the right-coordinate vector `t ∈ K^128` of `K ⊗_B K`.
6. **Single point only.** **[OM-choice]** The PCS opens one point per proof. Batching across points and polynomials is the job of MosaicPCS (05).

## Specification

Notation: `|K| = 2^128`; `H` and the transcript are as in C4 and 02; MLE, `eq`, `bind_low` and sum-check are as in 03 and C2/C3. Integers `u64le(x)` are 8-byte little-endian. A "table" is a vector indexed per C2 (LSB = `x_1`).

### 4.1 PCS interface

A polynomial is given by a table `f ∈ K^{2^n}`; its multilinear extension is `f~(x) = Σ_b eq(x,b) f[b]`. The reference API (`pcs.py`, class `LigeritoPCS`) is:

    commit(f, transcript)                  -> (cm, state)    # absorbs setup into the transcript
    open(state, r ∈ K^n, transcript)       -> (y, proof)     # y = f~(r)
    verify(cm, r, y, proof, transcript)    -> accept | VerificationError

* **Commitment** `cm = (root)`, one hash output (32 bytes for the default profile). The public parameters `pp` are the Ligerito parameter set `LigeritoParams = (n, ks, rs, ts)` (4.6) and the hash profile. They are part of the verifying key and are not transmitted per proof.
* **Setup absorption** (both sides, in `commit` / before `verify`):
  `absorb_bytes(b"pcs/params", enc_params)` then `absorb_bytes(b"pcs/root", root)`, where `enc_params = u64le(n) ‖ u64le(L) ‖ (u64le(k_i) ‖ u64le(r_i) ‖ u64le(t_i))_{i=0..L-1}`.
* **Opening proof** `LigeritoProof` contains: the roots `root_1 … root_{L-1}` of the committed levels 1..L-1; per level `i` the sum-check proof (`k_i` rounds, each `[g(t_0), g(t_2)]`); per level `i` a *level opening* (the opened columns, one per query index, and the Merkle multi-path); and the final polynomial `f_L` (`2^{n_L}` K elements, in the clear). `y` is not part of the proof; the caller supplies it.
* `open` and `verify` begin by absorbing the claim: `absorb_ks(b"pcs/point", r)`, `absorb_k(b"pcs/value", y)`.
* **Bit-valued claims.** `BitPCS` (`pcs.py`) commits to a bit vector `w` of length `2^ℓ` (`ℓ ≥ 8`) by committing to its packing `P` (4.5) with Ligerito (`n = ℓ − 7`). Its `open` runs ring switching (4.5) and then opens `P~` at the point `r_s` that ring switching outputs, on the same transcript. Soundness is that of the composition (13).
* The interface is **single-point** (see Resolved questions, item 6).

### 4.2 Merkle trees

Let `H` be the configured hash with digest length `h_len` (32 for sha256 and sha3-256).

    hash_leaf(data)   = H(0x00 ‖ data)
    hash_node(l, r)   = H(0x01 ‖ l ‖ r)
    empty             = H(0x02)

**[OM-choice]** A tree over `M ≥ 1` leaves has depth `D = ceil(log2 M)` (`D = 0` for `M = 1`). The leaf layer is `hash_leaf(leaf_i)` for `i < M`, padded on the right with `empty` to `2^D` entries. Layer `j+1` is `hash_node` of consecutive pairs of layer `j` (entry `2i`, `2i+1`). The root is the single entry of layer `D`. The verifier knows `M` from the parameters; `M` is not hashed into the root. In Ligerito `M` is always a power of two, so padding never occurs there; it exists for other users (05, 12).

**Ligerito leaf.** The leaf for codeword position `q` of a level is the *column* `(c_0[q], …, c_{R-1}[q])`, all `R = 2^k` rows at position `q`, serialized as the concatenation of the 16-byte encodings (C1) in row order `0..R-1`. Length `16·R` bytes.

**Multi-opening of a set of leaves.** The query set is a strictly ascending list of distinct indices `i_1 < … < i_s`, all `< M`. The prover outputs the leaf data in this order and an authentication list `auth`, built level by level from the leaves up:

    cur = [i_1 … i_s]
    for level j = 0 .. D-1:
        S = set(cur)
        for i in cur (ascending):
            if (i XOR 1) not in S: append layer_j[i XOR 1] to auth
        cur = sorted(unique(i >> 1 for i in cur))

So at each level, siblings that are themselves on a queried path are omitted (deduplication), and the emitted siblings are in ascending order of the *queried node* at that level (for two nodes sharing a parent only one needs a sibling, and then neither does). The verifier replays exactly this traversal, consuming `auth` in order, computes the parents, and accepts iff the final node equals the root and `auth` is consumed exactly (no short or long lists). Indices not strictly ascending, an empty set, or an index `≥ M` are rejected. `auth` has no length prefix; its length is determined by the index set and `M`.

### 4.3 Reed–Solomon over K by additive NTT

**Domain.** **[OM-choice]** For `m ≥ 0` let `β_b = X^b` (the K element with integer value `2^b`) and `U_m = span_{GF(2)}{β_0, …, β_{m-1}}`. The point list is `ω_q = Σ_b q_b β_b`, which is the K element with integer value `q`, for `q ∈ [0, 2^m)`. The `U_m` are nested, so a longer codeword (smaller rate) extends a shorter one as a prefix. *Why:* it is the subspace the monomial packing basis already provides, with no search, and the Merkle position index is the point itself. Because every `U_m ⊂ U_{128}` is a subspace of a field, no coset or shift is used.

**Vanishing polynomials and basis.** For `i ≥ 0`: `W_i(x) = Π_{u ∈ U_i} (x − u)` (so `W_0 = x`), which is GF(2)-linear in `x`, and `Ŵ_i(x) = W_i(x) / W_i(β_i)`. Then `Ŵ_i(β_i) = 1` and `Ŵ_i` vanishes on `U_i`. The *novel basis* is
`X_j(x) = Π_{b : j_b = 1} Ŵ_b(x)` for `j ≥ 0` (`j_b` the bits of `j`), a degree-`j` polynomial, with `X_0 = 1`.

**Tables.** Define `w_{i,b} = W_i(β_b)` for `b ≥ i` by `w_{0,b} = β_b` and `w_{i+1,b} = w_{i,b} · (w_{i,b} + w_{i,i})`, and `ŵ_{i,b} = w_{i,b} / w_{i,i}` (so `ŵ_{i,i} = 1`). Linearity gives, for `q < 2^m` and `i < m`,
`Ŵ_i(ω_q) = ⊕_{b ≥ i, q_b = 1} ŵ_{i,b}`.

**Code.** The code `RS[μ, r]` has message length `2^μ`, rate `ρ = 2^{-r}`, codeword length `N = 2^{μ+r}` (`m = μ + r`). The encoding of `a = (a_0, …, a_{2^μ-1}) ∈ K^{2^μ}` (coefficients in the novel basis, which is the data itself) is

    Enc(a)[q] = Σ_j a_j · X_j(ω_q),     q ∈ [0, 2^m).

This is an RS code (evaluations of a polynomial of degree `< 2^μ` on a subspace). Its relative distance is `1 − ρ + 2^{-m}`, and the unique-decoding radius is `δ = (1−ρ)/2` (4.7).

**Generator column.** For a position `q`, `basis_row(q) = (X_j(ω_q))_{j<2^μ}` has product form: with `a_b = Ŵ_b(ω_q)` (`b < μ`), `X_j(ω_q) = Π_b a_b^{j_b}`. As a table over `{0,1}^μ` (C2 order) it is its own multilinear extension `Π_b (1 + x_b + x_b a_b)`. Ligerito uses this (4.4).

**Fast algorithm** (reference `ntt.encode`, `O(m·2^m)` K operations): pad `a` with zeros to length `2^m`, then

    for i = m-1 down to 0:
        for c in 0 .. 2^(m-1-i) - 1:
            t = ⊕_{d : c_d = 1} ŵ_{i, i+1+d}          # = Ŵ_i evaluated at the high part c·2^(i+1)
            for j in c·2^(i+1) .. c·2^(i+1) + 2^i − 1:
                a[j]       ← a[j] + t · a[j + 2^i]
                a[j + 2^i] ← a[j + 2^i] + a[j]          # uses the new a[j]
    return a                                          # a[q] = Enc(a)[q]

(Correctness: at stage `i`, split `P = P_0 + Ŵ_i P_1`; on a point whose bit `i` is 0 the value of `Ŵ_i` is `t`, on bit 1 it is `t + 1`.)

**Naive algorithm** (reference `ntt.encode_naive`): evaluate the definition, `O(4^m)`. The two MUST agree; `tests/test_ntt.py` cross-checks.

### 4.4 Ligerito

The structure follows Novakovic–Angeris (ePrint 2025/1187): reshape the polynomial into a matrix, encode the rows with a linear code, commit to the columns, then reduce the evaluation claim by a short sum-check, a recursive commitment to the folded polynomial, and a handful of column queries whose consistency is added to the next level's inner-product claim as extra weight. The following is **our** instantiation, written from the structure of that paper and the needs of this spec; the paper treats a small base field with an extension challenge field. **[OM-choice]** *Mapping onto K:* here the base field, code alphabet, and challenge field are all `K`, so there is no separate extension field. Every challenge is a K element and every message is a vector over K. The consequence for soundness (the proximity-gap term is `~N/|K|` with no extension gain) is accounted in 4.7.

**Parameters** `(n, ks, rs, ts)`; `L = |ks|` committed levels. Set `n_0 = n`, `n_{i+1} = n_i − k_i`, and the final size `n_L = n − Σ k_i ≥ 1`. Level `i` has fold arity `k_i`, rate `2^{-r_i}`, `t_i` queries, `R_i = 2^{k_i}` rows, `C_i = 2^{n_i − k_i} = 2^{n_{i+1}}` columns, codeword length `N_i = 2^{n_{i+1} + r_i}`.

**Matrix reshape. [OM-choice]** The table `f_i ∈ K^{2^{n_i}}` is read as an `R_i × C_i` matrix `W_i[a][j] = f_i[a + R_i·j]`. The row index is the **low** `k_i` index bits (variables `x_1..x_{k_i}`) and the column index `j` is the high bits. *Why:* C3 binds the low variables first, so binding `x_1..x_{k_i}` to challenges `ρ` is exactly the row combination `Σ_a eq(ρ,a) W_i[a][·]`, giving the folded table `g[j] = f_i~(ρ, j)` of `n_{i+1}` variables in C2 order.

**Commitment of a level.** Row `a` is encoded `c_a = Enc_{RS[n_{i+1}, r_i]}(W_i[a][·])` (length `N_i`). The Merkle leaves are the columns `col_i(q) = (c_0[q], …, c_{R_i-1}[q])`, `q < N_i` (4.2). The root is `root_i`. `commit` returns `root_0`; `root_i` for `i ≥ 1` is sent in the proof.

**Claim form.** At level `i` the prover and verifier hold an *inner-product claim*

    Σ_{x ∈ {0,1}^{n_i}} f_i[x] · b_i[x] = c_i                    (★_i)

where the verifier knows `b_i` as a sparse list of **product-form terms**: `b_i[x] = Σ_τ α_τ Π_{u=1}^{n_i} (γ_{τ,u} + d_{τ,u} x_u)` (each term a triple `(α, γ-vector, d-vector)`; note this is multilinear in `x`, and the table `b_i[x]` and its MLE coincide). Level 0 is the evaluation claim: `c_0 = y` and one term `(α=1, γ_u = 1 + r_u, d_u = 1)`, i.e. `b_0 = eq(r, ·)`.

**Level step `i = 0..L-1`.** In transcript order:

1. **Sum-check.** Run `k_i` rounds of the degree-2 sum-check of (03, C3) on `Σ_x f_i[x] b_i[x] = c_i`, binding `x_1, …, x_{k_i}`. The base label is `b"pcs/sumcheck"`; the instance parameters absorbed by 03 are `m = k_i`, `d = 2`. Round `j` message: `g_j(t_0), g_j(t_2)` where `g_j(X) = Σ_{x_{j+1},…} f_i · b_i` with earlier variables fixed to challenges. It yields `ρ_i ∈ K^{k_i}` and the reduced claim `c'_i = Σ_{y ∈ {0,1}^{n_{i+1}}} g[y] b'[y]` with `g = f_i(ρ_i, ·)` and `b'[y] = b_i(ρ_i, y)`. (The reference proves this with the 03 API by presenting `C_i` column tables of length `R_i` for each of `f` and `b` and `combine = Σ_y f_y·b_y`; this yields identical messages.) The verifier updates each term by `α ← α · Π_{u ≤ k_i}(γ_u + d_u ρ_u)` and deletes the first `k_i` entries of its `γ` and `d` vectors.
2. **Commit/send the fold.** If `i < L−1`: the prover builds the level-`(i+1)` commitment of `g` (with `k_{i+1}, r_{i+1}`), sends `root_{i+1}`; both absorb `absorb_bytes(b"pcs/root", root_{i+1})`. If `i = L−1`: the prover sends `f_L = g` in the clear (`2^{n_L}` K elements); both absorb `absorb_ks(b"pcs/final", f_L)`.
3. **Queries.** The verifier (both sides, from the transcript) draws `t_i` indices `q = challenge_index(b"pcs/query/idx", log2 N_i)`, successively; the query set `Q_i` is the **sorted, deduplicated** set (so `|Q_i| ≤ t_i`). The prover sends the columns `col_i(q)` for `q ∈ Q_i` in ascending order, with the Merkle multi-path (4.2) against `root_i`, in the *level opening*. Both absorb `absorb_ks(b"pcs/cols", all column entries, in order)`. The verifier checks the multi-path.
4. **Consistency.** For `q ∈ Q_i` the verifier computes `v_q = Σ_a eq(ρ_i, a) · col_i(q)[a]`. Honestly, `v_q = Enc(g)[q]` (the row combination commutes with the linear code).
   * **If `i = L−1`:** the verifier checks `Σ_j f_L[j] · X_j(ω_q) = v_q` for each `q ∈ Q_i` (it evaluates `basis_row(q)` with `μ = n_L`, `m = n_L + r_{L-1}`), and checks the final claim directly: `Σ_y f_L[y] · b'[y] = c'_{L-1}`, evaluating each term table. Accept iff all hold.
   * **Else:** draw `β = challenge_k(b"pcs/beta")`. For the queries in ascending order `q_1 < … < q_s`, with `β_m = β^m` (`m = 1..s`), set
     `c_{i+1} = c'_i + Σ_m β_m v_{q_m}` and `b_{i+1} = b' + Σ_m β_m · basis_row(q_m)`, i.e. one new product-form term per query: `(α = β_m, γ_u = 1, d_u = 1 + Ŵ_u(ω_{q_m}))` for `u = 1..n_{i+1}`. The next level proves (★_{i+1}) for the *committed* `f_{i+1} = g`. Continue with `i+1`, whose openings are checked against `root_{i+1}`.

*Why this is sound.* This is the `g = 1` case of the level-reduction theorem proved in 4.4a: if the decoded next-level polynomial differs from the true fold of the decoded `W_i`, their encodings differ in at least a `δ` fraction of positions outside the bad columns, so the queries expose some `q` with `Enc(g)[q] ≠ v_q` except with probability `(1−δ)^t`; the random batching `β` then makes (★_{i+1}) false for the decoded polynomial except with probability `t/|K|`, and the induction continues. 4.7 gives the error terms.

**Transcript order (complete, single opening).**

    absorb_bytes   pcs/params   enc_params          # setup, at commit
    absorb_bytes   pcs/root     root_0
    absorb_ks      pcs/point    r                   # at open / verify
    absorb_k       pcs/value    y
    for i in 0..L-1:
        [sum-check labelled pcs/sumcheck: absorb claim, params; per round absorb msg, squeeze chal]   (03)
        i < L-1: absorb_bytes pcs/root root_{i+1}      i = L-1: absorb_ks pcs/final f_L
        t_i x challenge_index pcs/query/idx
        absorb_ks pcs/cols
        i < L-1: challenge_k pcs/beta

**Sizes** (for `gs = 1`; 4.4a changes only `N_i` and `n_L`). Per level, the proof contains `|Q_i|·16·2^{k_i}` bytes of columns, the deduplicated auth hashes (about `|Q_i|·(log2 N_i − log2 |Q_i| + 2)` of them), `32` bytes of next root, and `32·k_i` bytes of sum-check messages (`2` K per round); plus `16·2^{n_L}` for the final polynomial. Table sizes are in 4.7.

### 4.4a Gap amplification: `gs_i > 1` (normative)

**[OM-choice]** Let `g = gs_i ≥ 1` be the repetition count of level `i` and `s = ceil(log2 g)`. With `g = 1` (`s = 0`) everything below degenerates to 4.4, byte for byte. Write `m_i = n_i − k_i` (variables of one folded row), so `N_i = 2^{m_i + r_i}`, and redefine `n_{i+1} = m_i + s_i` (4.4 had `s_i = 0`); the final size is `n_L = n_{L-1} − k_{L-1} + s_{L-1}`.

**Idea.** Fold the committed matrix `W_i` with `g` independent challenge vectors `ρ^{(0)}, …, ρ^{(g-1)}` (`ρ^{(0)}` is the sum-check's), put all `g` folded rows into **one** next-level polynomial `F` (block `j` of `F` is `g^{(j)} = f_i(ρ^{(j)}, ·)`), and let the same `t_i` opened columns check every block. No folded row is sent in the clear and no extra Merkle tree is committed; the price is `s` extra variables.

**The next-level polynomial.** `F ∈ K^{2^{m_i + s}}`, `F[y + 2^{m_i}·j] = g^{(j)}[y]` for `j < g`, `y < 2^{m_i}`, and `F[y + 2^{m_i}·j] = 0` for `g ≤ j < 2^s`. The extra variables are the **high** variables `x_{m_i+1..m_i+s}` (LSB-first, C2); block index `j` has bits `j_u`. `f_{i+1} := F` is committed at level `i+1` (4.4), or sent in the clear if `i = L−1`.

**Modified level step.** Steps 1 and 4 of 4.4 and the transcript change as follows; sampling and absorption are in this order.

1. Sum-check as in 4.4: `ρ^{(0)} = ρ_i`, claim `c'_i = ⟨g^{(0)}, b'⟩`.
2. **Extra folds.** For `j = 1 … g−1` successively, both sides squeeze `ρ^{(j)} = challenge_ks(b"pcs/fold", k_i)`. (None for `g = 1`.) These challenges depend on the transcript through the sum-check, hence after `root_i` was fixed.
3. **Commit/send** `F` instead of `g`: `root_{i+1}` is the root of the level-`(i+1)` commitment of `F` (`absorb_bytes pcs/root`), or `absorb_ks(b"pcs/final", F)` (all `2^{n_L}` entries, padding included) if `i = L−1`.
4. **Queries** exactly as 4.4 (`pcs/query/idx`, `pcs/cols`): the same set `Q_i` serves all repetitions. Every query column is used `g` times; no data are added to the opening.
5. **Consistency.** For `q ∈ Q_i` and `j < g`: `v^{(j)}_q = Σ_a eq(ρ^{(j)}, a)·col_i(q)[a]`; honestly `v^{(j)}_q = Enc(g^{(j)})[q]`.
   * **If `i = L−1`:** the verifier checks `Σ_y F[y + 2^{m_i} j]·X_y(ω_q) = v^{(j)}_q` for every `q ∈ Q_i`, `j < g` (`basis_row(q)` with `μ = m_i`), and the final claim `Σ_x F[x] b'_{ext}[x] = c'_i` (below).
   * **Else:** for `j = 0 … g−1` in order, squeeze `β_j = challenge_k(b"pcs/beta")` (for `g = 1` this is the single `β` of 4.4). With `q_1 < … < q_s` the sorted queries,
     `c_{i+1} = c'_i + Σ_{j<g} Σ_{m} β_j^m · v^{(j)}_{q_m}`,
     `b_{i+1} = (b' ‖ 0 ‖ …) + Σ_{j<g} Σ_m β_j^m · (e_j ⊗ basis_row(q_m))`,
     where `b'_{ext}` places `b'` in block 0 and `e_j ⊗ r` places the vector `r` in block `j`. In product form (4.4): the carried terms of the sum-check step get the extra pairs `(γ, d) = (1, 1)` for each of the `s` new variables (that is `eq(0, ·)`, selecting block 0), and each new term is `(α = β_j^m, γ_u = 1, d_u = 1 + Ŵ_u(ω_{q_m}))` for `u ≤ m_i` followed, for `u = 1..s`, by `(γ, d) = (1 + j_u, 1)` (that is `eq(j, ·)`, selecting block `j`). The terms are appended in the order `j` ascending, then `m` ascending.

**Transcript order of one level** (replaces the loop body of 4.4):

    [sum-check pcs/sumcheck]
    j = 1..g-1:  challenge_ks pcs/fold  (k_i)
    i < L-1: absorb_bytes pcs/root root_{i+1}     i = L-1: absorb_ks pcs/final F
    t_i x challenge_index pcs/query/idx
    absorb_ks pcs/cols
    i < L-1: g x challenge_k pcs/beta

**Proof contents.** Exactly as 4.4: `root_{i+1}`, sum-check messages, columns and `auth`, final polynomial (now `2^{n_L}` entries). `g` is a function of the parameters, not of the proof; a verifier MUST reject a proof whose final polynomial length differs from `2^{n_L}`.

**Soundness.** We prove the level reduction for every `g ≥ 1` (`g = 1` is 4.4). The proof is ours; it uses exactly one external statement, Lemma A below, whose exact form was checked against the source texts (audit 13.9(1), resolved 2026-10-16). Everything else, including the tensor factor `k`, the exponent `g`, and the use of the sum-check vector as `ρ^(0)`, is proved here.

*Definitions.* Fix level `i` and write `k = k_i`, `N = N_i`, `t = t_i`, `R = 2^k`, `ρ_code = 2^{-r_i}`, `δ = (1 − ρ_code)/2`, and `C = RS[m_i, r_i]` (4.3), of length `N` and distance `d = N − 2^{m_i} + 1`; note `δN = (d−1)/2` exactly. The *interleaved code* `C^R` is the set of `R × N` matrices whose every row is in `C`. The *column distance* of matrices `W, W'` is `#{q : col_W(q) ≠ col_{W'}(q)} / N`. `W` is *δ-close* to `C^R` if its column distance to some `Ŵ ∈ C^R` is `≤ δ`, and *δ-far* otherwise. If `W` is δ-close, every row is within `δN = (d−1)/2` of `C`, so `Ŵ` and its message matrix are unique; the message read as a table (4.4 reshape) is the *decoded* polynomial `f̂`. "Committed `W`" means the oracle behind `root_i`; for the Merkle instantiation this is extraction up to a hash collision, accounted separately (13.2 row 40). Define the level relation: `(root_i, b_i, c_i) ∈ R_i` iff the committed `W_i` is δ-close and its decoded `f̂_i` satisfies `(★_i)`. The committed matrix `W_i` is fixed before every challenge of the level (`root_0` at commit; `root_i`, `i ≥ 1`, absorbed in the previous level's step 3, before that level's queries and `β`s, hence before level `i` begins).

**Lemma A (single-step gap; external).** Let `M` be a `2R' × N` matrix, `δ`-far from `C^{2R'}` in column distance, and let `M'(ρ)` be the `R' × N` matrix with rows `(1+ρ)·M[2a] + ρ·M[2a+1]` (rows listed in pair order), the same `ρ` for every pair. Then `Pr_{ρ ← K}[M'(ρ) is δ-close to C^{R'}] ≤ N/|K|`. *Source (checked 2026-10-16, audit 13.9(1)).* For one row pair this is BCIKS, ePrint 2020/654, Theorem 4.1 (`δ ≤ (1−ρ)/2` with their `ρ = (k+1)/n` the rate, so our `δ` is their largest allowed radius; more than `n` close challenges imply correlated agreement; error `ε_U = n/q` in its Theorem 1.2). The interleaved form, one `ρ` for all pairs and column distance, is Theorem 2.3 of Diamond–Posen ePrint 2024/504 in its 2024-07 revision, stated for `e ≤ ⌊(d−1)/2⌋` with the same `n/|L|` and derived from BCIKS Thm 4.1 (their `(1−r, r)` is our `(1+ρ, ρ)` in characteristic 2; `U_0`, `U_1` are the even and odd rows). [5] (BCHKS) is not the source of this form: its new unique-decoding results need a radius strictly inside ours (13.9(1)).

**Lemma B (tensor fold).** For fixed `W` δ-far from `C^R` and uniform `ρ ← K^k`, the folded word `u(ρ) = Σ_a eq(ρ, a) W[a]` is δ-close to `C` with probability at most `kN/|K|`. *Proof.* Fold one variable at a time: `W^(0) = W`, and `W^(u+1)` pairs the rows of `W^(u)` differing in bit `u+1` with coefficients `(1+ρ_{u+1}, ρ_{u+1})` (C2: the `eq` factor `1 + ρ + b` is `1+ρ` for `b = 0` and `ρ` for `b = 1`), so `W^(k)` is the single row `u(ρ)`. Closeness is forward-preserved for *every* next challenge: if `W^(u)` is δ-close with decoded `Ŵ^(u)`, folding `Ŵ^(u)` with the same `ρ_{u+1}` gives a matrix in the interleaved code (rows are `K`-combinations of codewords) whose columns can differ from `W^(u+1)` only where `W^(u)` already differed from `Ŵ^(u)`, since the fold acts column by column. Hence `{W far, u close} ⊆ ∪_{u<k} {W^(u) far, W^(u+1) close}`. Conditioned on `ρ_1..ρ_u`, the matrix `W^(u)` is fixed and `ρ_{u+1}` is uniform and independent, so Lemma A bounds each term by `N/|K|`; the union bound over the `k` steps gives `kN/|K|`. ∎ (This is the "tensor-fold loss `k`" of 4.7, here proved rather than asserted.)

**Lemma C (all folds close).** If `W_i` is δ-far, then all `g` folded words `u^(j) = u(ρ^(j))` are δ-close to `C` with probability at most `(kN/|K|)^g`. *Proof.* In the interactive (pre-Fiat–Shamir) protocol the challenges are uniform: `ρ^(0)` is the vector of sum-check challenges, uniform in `K^k` and independent of `W_i`, which was committed before the level; the prover messages interleaved between its components do not change `W_i` or the distribution of the remaining components, so Lemma B applies to `ρ^(0)` exactly as to a fresh vector — this discharges the "shared prefix / `ρ^(0)` from the sum-check" step, and the Fiat–Shamir instantiation is by round-by-round soundness (13.1). For `j ≥ 1`, `ρ^(j)` is squeezed after the sum-check and after `ρ^(1..j-1)`; conditioned on that history, `W_i` is still the same fixed δ-far matrix and `ρ^(j)` is uniform in `K^k`, so Lemma B bounds the conditional probability that `u^(j)` is close by `kN/|K|`. Multiplying the `g` conditional bounds (chain rule) gives `(kN/|K|)^g`. No independence between the folds' bad sets is used. ∎

**Theorem (level reduction).** If `(root_i, b_i, c_i) ∉ R_i`, then except with probability at most `2k/|K| + t/|K| + (kN/|K|)^g + (1−δ)^t` over the level's challenges (`ρ^(0..g−1)`, the queries, the `β_j`), the verifier rejects at level `i` (when `i = L−1`) or continues with `(root_{i+1}, b_{i+1}, c_{i+1}) ∉ R_{i+1}`. At the final level the `t/|K|` term is absent.

*Proof.* By contradiction for `i < L−1`: assume the output is in `R_{i+1}`, i.e. the matrix behind `root_{i+1}` is δ-close with decoded `F̂` satisfying `(★_{i+1})`. Let `G_j` be block `j` of `F̂` (not the prover's intended `F`; the next level only ever sees `F̂`). Expanding `(★_{i+1})` by the definition of `b_{i+1}, c_{i+1}` in step 5 gives

    E(β_0..β_{g-1}) := Δ_0 + Σ_{j<g} Σ_{m≤s} β_j^m Δ_{j,m} = 0,

where `Δ_0 = c'_i − ⟨G_0, b'⟩` and `Δ_{j,m} = v^{(j)}_{q_m} − Enc(G_j)[q_m]` (using `⟨F̂, e_j ⊗ basis_row(q)⟩ = Σ_y G_j[y] X_y(ω_q) = Enc(G_j)[q]`). The transcript order matters: `root_{i+1}` (hence `F̂`), the query set `Q_i` and the opened columns (hence every `Δ`) are all fixed before any `β_j` is squeezed. The monomials `1, β_j^m` are pairwise distinct, so if any `Δ` is non-zero then `E` is a non-zero polynomial of total degree `≤ s ≤ t`, and Schwartz–Zippel gives `Pr[E = 0] ≤ t/|K|`, independent of `g` (this is why the batching term of 4.7 is unchanged). Henceforth assume every `Δ = 0`.

*Case 1: `W_i` is δ-far.* By Lemma C, except with probability `(kN/|K|)^g` some fold `u^(j)` is δ-far from `C`. Fix such a `j`. `Enc(G_j) ∈ C`, so it differs from `u^(j)` in at least `δN` positions; those positions are fixed before the queries are drawn (`ρ^(j)` and `root_{i+1}` precede `Q_i`), and `v^{(j)}_q = u^(j)[q]` by definition. The `t` queries are sampled with replacement, so they all miss the differing positions with probability at most `(1−δ)^t`; otherwise some `Δ_{j,m} ≠ 0`, contradiction. One far fold suffices, so there is no union bound (and no factor `g`) in the query term.

*Case 2: `W_i` is δ-close but `⟨f̂_i, b_i⟩ ≠ c_i`.* Let `ĝ^(j) = f̂_i(ρ^(j), ·)` be the fold of the decoded message, and `D` the set of columns where `W_i` differs from `Ŵ_i`, `|D| ≤ δN`. By linearity of the fold and of `Enc`, `u^(j)[q] = Enc(ĝ^(j))[q]` for `q ∉ D`. Only `j = 0` is needed here: if `G_0 ≠ ĝ^(0)`, the codewords `Enc(G_0)` and `Enc(ĝ^(0))` differ in at least `d > (1−ρ_code)N` positions, hence in at least `(1−ρ_code)N − δN = δN` positions outside `D`, where `Δ_{0,·} ≠ 0`; the queries miss all of them with probability at most `(1−δ)^t`. So `G_0 = ĝ^(0)`, and `Δ_0 = 0` reads `⟨f̂_i(ρ^(0), ·), b'⟩ = c'_i`. But the sum-check of 03 applied to the (known) summand `f̂_i · b_i` of per-variable degree 2 — with arbitrary prover messages, exactly as in its soundness statement — says a false claim `⟨f̂_i, b_i⟩ ≠ c_i` reduces to a true reduced claim with probability at most `2k/|K|` over `ρ^(0)`. Contradiction.

*Final level `i = L−1`.* Here `F` is sent in the clear, so `F̂ = F`, and the verifier checks every `Δ_{j,q} = 0` and the final claim directly; there is no `β` and no batching error. Cases 1 and 2 apply verbatim with `G_j` the blocks of `F`. ∎

Iterating the theorem from level 0 (where `R_0` with `b_0 = eq(r, ·)` says the decoded `f̂_0` satisfies `f̂_0~(r) = y`) to the final direct check gives the soundness of `open`/`verify`, with per-level error `2k/|K| + t/|K| + (kN/|K|)^g + (1−δ)^t`, as in the ledger (13.5). Tests: completeness for `g = 2, 3`, wrong value, tampering of every block of the final polynomial, and a prover that commits a level polynomial wrong in block `j` for each `j` (`tests/test_ligerito.py`, `TestGapAmplification`), and the real `provable-120` profile (`TestProvable120`, `test_protocol.TestProvable120EndToEnd`).


### 4.5 Ring switching

Setting (paper §4.3, Diamond–Posen ePrint 2024/504, 2025-09 revision, §3: Construction 3.1, Theorem 3.5, Remark 3.4, specialised to our basis; the paper's general B-basis `(β_v)` with `β_0 = 1` is `β_j = X^j`. The 2024-07 revision numbered this §4 and ran the sum-check over the tensor algebra without the `ρ` batching. Comparison and the two [OM-choice] deviations: 13.9(2)). `κ = 7`, `128 = 2^κ`. Let `w ∈ B^{2^ℓ}` with `ℓ ≥ 8`, `n = ℓ − κ`.

**Packing.** `P ∈ K^{2^n}`, `P[v] = Σ_{j<128} X^j · w[j + 128 v]` (C1, C2). Equivalently the K integer value of `P[v]` has bit `j` equal to `w[j + 128v]`. This is `K.pack` on consecutive 128-bit blocks.

**Claim.** `w~(r) = y`, `r = (r_lo ∥ r_hi)`, `r_lo = (r_1..r_7)`, `r_hi = (r_8..r_ℓ)` (C2: low variables first). Then `y = Σ_j eq(r_lo, j) s_j` where the **partial evaluations** are
`s_j = Σ_{v ∈ {0,1}^n} eq(r_hi, v) · w[j + 128 v] ∈ K`, `j < 128`.

**Tensor algebra.** `A = K ⊗_B K`, a commutative K-algebra (K acting on the left factor). Two coordinate systems: *left* coordinates `Σ_j s_j ⊗ β_j` (K-basis `1⊗β_j`), and *right* coordinates `Σ_i β_i ⊗ t_i` with `t_i ∈ K`. Converting an element from left to right coordinates: write each `s_j = Σ_i s_{j,i} β_i` (`s_{j,i} ∈ B` the bits of the integer value), then
`t_i = Σ_j s_{j,i} β_j`, that is `t_i = K.pack(bit_i(s_0), …, bit_i(s_127))`, a 128×128 bit-matrix transpose.

The key identity: the element `ŝ = Σ_v eq(r_hi, v) ⊗ P[v]` has left coordinates `s_j` (because `P[v] = Σ_j w_j(v) β_j` with `w_j(v) ∈ B` moves across `⊗`), and right coordinates
`c_i = Σ_v E_i(v) P[v]`, where `E_i(v) = bit_i(eq(r_hi, v)) ∈ B` (expand `eq(r_hi, v) = Σ_i E_i(v) β_i`).

**Protocol.**

1. Both absorb `absorb_ks(b"rs/point", r)`, `absorb_k(b"rs/value", y)`.
2. Prover sends `s = (s_0, …, s_127)` (128 K elements, 2048 bytes). Verifier checks `Σ_j eq(r_lo, j) s_j = y`, else reject. Both `absorb_ks(b"rs/s", s)`.
3. Verifier sends `ρ = challenge_ks(b"rs/rho", 7)`. Both compute `c = transpose(s)` (right coordinates) and the target `T = Σ_{i<128} eq(ρ, i) · c_i`, with `eq(ρ, i)` over the 7 bits of `i` (C2).
4. **Sum-check** (03, C3) with label `b"rs/sumcheck"`, `n` rounds, degree 2, claim `T`, on the summand `P[v] · a[v]`, where
   `a[v] = Σ_{i<128} eq(ρ, i) · E_i(v)` (a K-valued table; entry `v` is `Σ_i eq(ρ,i)` over the set bits of the integer value of `eq(r_hi, v)`).
   The prover table for `a` is computed directly. It outputs the challenge point `r_s ∈ K^n` and the final claim `F = P~(r_s) · a~(r_s)`.
5. The verifier computes `a~(r_s)` by the **tensor recursion**: start from `T_0 = 1 ⊗ 1` (right coordinates `t = (1, 0, …, 0)`); for `u = 1..n` update
   `T ← T · ((1 + r_{7+u}) ⊗ (1 + z_u) + r_{7+u} ⊗ z_u)`, `z = r_s`,
   where multiplying `T = Σ_i β_i ⊗ t_i` by a pure tensor `x ⊗ y` is `t'_m = y · Σ_i bit_m(x · β_i) · t_i` (`x·β_i` is a K product; `bit_m` its integer-value bit). Finally `a~(r_s) = Σ_i eq(ρ, i) · t_i`. (Reason: `T = Σ_v eq(r_hi, v) ⊗ eq(z, v)` has right coordinates `t_i = Σ_v E_i(v) eq(z,v)`, the MLE of `E_i` at `z`.) Cost: `O(n·128)` K multiplications plus `O(n·128²)` bit operations. The reference also implements the direct `O(2^n)` evaluation (`mle_eval` of the `a` table) for cross-checking.
6. The verifier rejects if `a~(r_s) = 0` **[OM-choice]** (probability `≤ n/|K|` over honest `r_s`; avoids a division by zero). Otherwise it outputs the PCS claim **`P~(r_s) = v` with `v = F / a~(r_s)`**.

**Output.** `(r_s, v)`; the PCS (4.1) then proves `P~(r_s) = v` on the same transcript. `RingSwitchProof = (s, sum-check messages)`: `2048 + 32n` bytes.

**Soundness.** If `s` passes check 2 and the sum-check target is consistent with `P`, i.e. `c = c*` (the true right coordinates), then `ŝ` has the same left coordinates as the true `ŝ*`, so `s = s*` and `y = w~(r)`. A wrong `c ≠ c*` survives step 3 only if `Σ_i eq(ρ,i)(c_i − c*_i) = 0` for random `ρ`: probability `≤ 7/|K|` (multilinear Schwartz–Zippel). The sum-check adds `2n/|K|`. So `ε_RS ≤ (7 + 2n)/|K| ≤ 2^{-121}` for `n ≤ 60`. Negative tests in `tests/test_ring_switch.py` exercise a wrong `y`, tampered `s` and sum-check messages, and a dishonest `w`. This is the bound of Diamond–Posen Theorem 3.5, `(κ + 2ℓ')/|L|` (§3.2), with `κ = 7`, `ℓ' = n`.

### 4.6 Parameters, structure

`LigeritoParams` is the tuple `(n, ks, rs, ts)` of 4.4. Constraints: `L ≥ 1`, all `k_i, r_i, t_i ≥ 1`, `Σ k_i < n`, and `N_i ≥ t_i` is not required (queries are sampled with replacement and then deduplicated).

**[OM-choice] Default schedule.** `r_i = 2` (rate `1/4`) at every level. The final polynomial has `n_L = 6` variables. The fold arities are obtained by splitting `n − 6` into `L = ceil((n−6)/5)` parts as evenly as possible, larger parts first (`schedule(n)` in `ligerito.py`: `n = 20 → [5,5,4]`, `22 → [4,4,4,4]`, `24 → [5,5,4,4]`). *Why:* arity 4–5 keeps each leaf at 256–512 bytes, balancing column payload against path length; rate 1/4 sits near the query-count/proof-size knee (see the rate sweep in 4.7). These are tunable without protocol change since `LigeritoParams` is in the verifying key (12).

### 4.7 Parameter profiles and soundness

Let `λ` be the target bits. Per level `i` write `ρ = 2^{-r_i}`, `δ = (1 − ρ)/2` (unique-decoding radius), `N = N_i`, `k = k_i`, `t = t_i`.

**Error terms of level `i`** (each a probability that a malicious prover wins at that stage, given the earlier stages did not):

| term | bound | source |
|---|---|---|
| sum-check, `k` rounds, degree 2 | `2k/|K|` (reported as `127 − log2 k` bits) | 03, Schwartz–Zippel |
| batching of the `|Q_i| ≤ t` queries into (★_{i+1}) | `t/|K|` (`128 − log2 t` bits) | degree-`t` polynomial in `β` |
| proximity gap of the tensor fold of `W_i` | `ε_gap = k·N/|K|` (`128 − log2(kN)` bits) | BCIKS ePrint 2020/654 Thm 4.1, interleaved as in Diamond–Posen 2024/504 (2024-07) Thm 2.3 (RS up to the unique-decoding radius: error `N/|F|` per fold challenge; Lemma A of 4.4a), tensor-fold loss `k` by induction over the `k` fold variables (Lemma B of 4.4a; the same bound as DP 2024/504 Thm 2.4 / Diamond–Gruen Cor. 1) |
| queries miss all bad positions | `(1 − δ)^t` (`t·(−log2(1−δ))` bits) | a differing pair of codewords at distance `≥ δ` after decoding to within `δ` |

The final-level inner-product check and the final column checks are exact (no error beyond the query term). Ring switching adds `ε_RS` (4.5).

**Profile `provable-120`** (proven bounds only, within the unique-decoding radius, per BCIKS Thm 4.1 as used in Lemma A of 4.4a). The number of queries at level `i` is

    t_i = ceil( λ / −log2( (1 + ρ_i) / 2 ) ),     λ = 120,  ρ_i = 2^{-r_i}

(from `(1 − δ)^t = ((1+ρ)/2)^t ≤ 2^{-λ}`). For `r = 1,2,3,4` (`ρ = 1/2, 1/4, 1/8, 1/16`): `t = 290, 177, 145, 132`. With the default `r = 2`, `t = 177` at every level. The sum-check and batching terms are then `≥ 124.7` and `≥ 120.5` bits (`t/|K| = 2^{-120.5}`).

**Profile `conjectured-100`** (**not provable**: it relies on the conjectured RS proximity-gap/up-to-capacity list decoding behaviour; comparison only; MUST be opt-in, MUST NOT be used for the production claim of 120 bits, and MUST be recorded in the verifying key so a proof cannot be passed off under the default profile). Queries: `t_i = ceil( 100 / r_i )` (soundness `ρ^t`, as if the proximity radius were `1 − ρ`); `r = 2 → t = 50`. The gap and batching terms are not accounted for in this profile.

**Gap amplification (see 4.4a and 13.5).** With the conservative bound `ε_gap = k·N/|K|` one fold challenge reaches only `128 − log2(kN)` bits, which is 104.7 to 118.0 bits for the levels of the default schedules, so `provable-120` additionally uses **`gs_i` independent fold-challenge vectors per level**, composed as in 4.4a, so the gap term becomes `(kN/|K|)^{gs_i}`. The profile chooses the smallest `gs_i` with `gs_i·(128 − log2(k_i N_i)) ≥ 120`; this is `gs_i = 2` at every level of every default schedule (gap bits 205 to 232). `LigeritoParams` has the optional field `gs` (default empty = all 1, encoded in `enc_params` only when some `gs_i > 1`, as the suffix `"GAPREPS" ‖ u64le(gs_i)…`). **Status:** implemented and tested (`ligerito.open_/verify`, `make_params`, `soundness_bits`, `params.py`; the real `provable-120` profile runs end to end in `tests/test_ligerito.py` and `tests/test_protocol.py`). The alternative (not used): the sharper unique-decoding bounds of ECCC TR25-169 [5]. Checked against its full text on 2026-10-16 (13.5, option 1): Theorem 1.3 has a proximity loss `ε*` that 4.4a does not handle, and the lossless Corollary 1.4 (`a > γn + 1`) holds only slightly inside our radius and would gain about 1.4 bits per level, not enough for `gs = 1`. No claim rests on it.

**Table** (`r = 2`, `t = 177` provable or `50` conjectured; sizes in KiB from `params.proof_size_bytes`, an expected-value model including ring switching; the "1 rep" column is the former conservative accounting on the same schedule and is **not** 120-bit).

| `n` (packed vars) | levels `ks` | final `n_L` (`gs = 2`) | provable-120 (`gs = 2`) | same schedule, 1 rep (not 120-bit) | conjectured-100 | `gap` bits per level (`gs = 2`) |
|---|---|---|---|---|---|---|
| 20 | [5,5,4] | 9 | 357 KiB | 322 KiB | 106 KiB | 217.4, 225.4, 232.0 |
| 22 | [4,4,4,4] | 10 | 415 KiB | 354 KiB | 117 KiB | 212.0, 218.0, 224.0, 230.0 |
| 24 | [5,5,4,4] | 10 | 509 KiB | 448 KiB | 144 KiB | 209.4, 217.4, 224.0, 230.0 |

(`n` packed variables correspond to `2^{n+7}` witness bits. For the full machine at `T = 2^22` the Mosaic polynomial has about `2^33` bits, i.e. `n = 26`, schedule `[5,5,5,5]`: about 624 KiB provable, see 13.5.) Per level the sum-check bits are `≥ 124.7`, the batching bits `120.5`, the query bits `≥ 120.0`, the gap bits `≥ 205`. The cost of `gs = 2` is only the one extra variable per level (4.4a): deeper Merkle paths and a final polynomial of `2^{n_L}` entries with `n_L = 6 + L` instead of 6. The size model's absolute values are about 15% above the previous sampled estimates for the 1-rep schedule (different auth-path model); treat sizes as estimates until the Rust prover measures them.

**Derivation of `t` from rate.** The proximity step maps a possibly non-codeword matrix to a folded word; if the prover's next-level polynomial is not the fold, `Enc(g)` and the (decoded) fold differ in at least `δ·N` positions (distance `1−ρ` minus the `δ` slack = `δ`). Each independent query lands there with probability `≥ δ`. Hence escape probability `≤ (1−δ)^t`, and `t ≥ λ/ −log2(1−δ)` with `1 − δ = (1+ρ)/2`.

### 4.8 Reference model

Modules (all in `reference/openmagnetar/`, pure Python, stdlib only, coded against the shared API of C8):

| module | content |
|---|---|
| `merkle.py` | `MerkleTree`, `hash_leaf`, `hash_node`, `verify_multi` (4.2) |
| `ntt.py` | `encode` (fast), `encode_naive`, `basis_row`, `gen_weights`, `what_beta` (4.3) |
| `ligerito.py` | `LigeritoParams`, `make_params`, `schedule`, `queries_provable/conjectured`, `soundness_bits`, `commit`, `open_`, `verify`, `LigeritoProof.to_bytes` (4.4, 4.6, 4.7) |
| `ring_switch.py` | `pack`, `rs_prove`, `rs_verify`, `a_eval`, `a_table` (4.5) |
| `pcs.py` | `LigeritoPCS`, `BitPCS` (4.1) |

`LigeritoProof.to_bytes()` is the reference canonical byte layout used for the vector hash: concatenation of `roots`, per level the sum-check messages, per level the columns then `auth`, then `final`, all K in C1 encoding; it is **not** the on-wire format (12 owns that).

Tests: `tests/test_merkle.py`, `test_ntt.py`, `test_ligerito.py`, `test_ring_switch.py`, `test_pcs_vectors.py`. They cover completeness at toy sizes (`n ≤ 12`, `t ≤ 8`), fast-vs-naive NTT, tampering of every proof component (sum-check message, column value, auth path, next root, final polynomial, commitment, claimed value, point), a cheating prover that commits a non-fold, ring-switching negatives, and replay of the vectors. Vectors: `reference/vectors/04-pcs/{merkle,ntt,ring_switch,ligerito}.json`, produced by `reference/gen_vectors_04.py` (inputs derived from SHA-256 in counter mode; field elements as 32-hex little-endian).

### Requests to other sections

* **13-security:** (1) **Resolved in 13.5 and 4.4a** (gap amplification, `gs_i = 2`). (2) Add `ε_RS ≤ (7 + 2n)/|K|` for ring switching, and the Ligerito terms of 4.7, to the per-step accounting. (3) Round-by-round soundness for the `β`-batching and the query steps is as above.
* **12-proof-format:** serialize `LigeritoParams` (n, ks, rs, ts) and the profile name in the verifying key; the proof layout of 4.1 (roots, per-level sum-check messages, openings with `auth` lists of known length, final polynomial). `auth` is not length-prefixed; its length follows from the index set (derive it during parsing).
* **05-mosaic / 11-protocol:** the PCS is single-point; `open` consumes the transcript, so 11 must fix where the commitment and `(r, y)` are absorbed relative to the preceding stages (4.1 absorbs `pcs/params`, `pcs/root`, then `pcs/point`, `pcs/value`; ring switching absorbs `rs/point`, `rs/value` again). For witness commitments the number of committed packed variables must be `n = ℓ − 7 ≥ 1` and `ℓ ≥ 8`.
* **02-transcript:** labels used here: `pcs/params`, `pcs/root`, `pcs/point`, `pcs/value`, `pcs/sumcheck`, `pcs/final`, `pcs/query/idx`, `pcs/cols`, `pcs/beta`, `pcs/fold`, `rs/point`, `rs/value`, `rs/s`, `rs/rho`, `rs/sumcheck` (all listed in the table in 02 2.7 since 2026-10-16).
* **01-fields:** the packing `P[v] = K.pack(w[128v .. 128v+127])` and `U_m` as the integers `[0, 2^m)` should be cited from 01.

## Integration notes

* 2026-10-16 (agent for 13/15): replaced the "Known gap" paragraph, the table and the gap column of 4.7 by the gap-amplification text above; added the optional `gs` field to `LigeritoParams` (4.6) and `reference/openmagnetar/ligerito.py` (`gs`, `reps`, `gap_reps`, `make_params`, `soundness_bits`, `encode`; `open_`/`verify` raised `NotImplementedError` when `gs_i > 1`, superseded by the 2026-10-16 note below). Existing vectors are unchanged (`gs` is absent from `encode()` when all 1). The `soundness_bits()` gap column now includes the repetition factor. Request to 12: serialize `gs` in the verifying key when present.

* **Proof framing (12).** The Ligerito openings are serialized with a `u32` count of columns and a `u32` count of authentication hashes per level, instead of deriving
  the path length from the query set while parsing as the request to 12 above suggests; this keeps the parser independent of the transcript. `gs` is not stored in the vk: the vk holds
  `(profile, r, t)` and the parameters, including `gs`, are re-derived by `make_params` (12.2). `gs > 1` is implemented (4.4a); `protocol.py` end-to-end tests use both the `test` profile (`t = 8`, `gs = 1`, fast) and the real `provable-120` profile.

* 2026-10-16 (gs > 1): specified the composition of repeated folds in the new 4.4a (all folds in one next-level polynomial `F` with `s = ceil(log2 gs)` extra high variables, one root, shared queries, one `β_j` per repetition, new label `pcs/fold`); `LigeritoParams.n_i`, `m_i`, `n_final`, `log_codeword`, `sbits` account for the extra variables; `open_/verify` no longer raise for `gs > 1`; new test classes `TestGapAmplification`, `TestProvable120` and `test_protocol.TestProvable120EndToEnd`. `gs = 1` transcripts and vectors are unchanged. `params.proof_size_bytes` no longer multiplies a level by `gs` (357/415/509 KiB at `n = 20/22/24`, 624 KiB at `n = 26`, was 641/705/893/1101). Label `pcs/fold` is new for 02. The earlier note that `protocol.py` end-to-end tests must use the `test` profile is obsolete: `provable-120` (`t = 177`, `gs = 2`) runs through the whole protocol in the tests (about 8 s for the Fibonacci program, 68 Mosaic claims).

* 2026-10-16 (soundness proof): replaced the 4.4a soundness sketch with a written proof (interleaved column distance and the level relation `R_i`; Lemma A the external single-step gap; Lemma B the tensor factor `k`; Lemma C "all folds close" `≤ (kN/|K|)^g`, including `ρ^(0)` from the sum-check; level-reduction theorem with the far/close case split against the *decoded* next polynomial `F̂`). Error terms and the protocol are unchanged, so no code or vectors change. 4.4's "why sound" paragraph now cites the theorem; 13.5 and 13.9(1) narrowed accordingly. `pcs/fold` and the other `pcs/*`/`rs/*` labels are now listed in 02 2.7.

* 2026-10-16 (audit 13.9(1)/(2) against the source PDFs): Lemma A's citation changed from BCHKS [5] to BCIKS ePrint 2020/654 Theorem 4.1 with the interleaved lift of Diamond–Posen 2024/504 (2024-07) Theorem 2.3, both checked verbatim; the 4.7 table source, the `provable-120` heading and the TR25-169 "alternative" sentence updated accordingly (13.5 option 1 has the full-text reading). 4.5 now cites Construction 3.1 / Theorem 3.5 of the 2025-09 revision of 2024/504, whose error term `(κ + 2ℓ')/|L|` is exactly our `(7 + 2n)/|K|`. No protocol, error-term or vector change.
