# 03. Multilinear extensions and sum-check

**Status:** draft · **Paper:** §3.1–3.2, refs [3,12,22]

## Scope
MLE and eq definitions, the variable binding order, sum-check round message
format (which evaluations are sent, compressed or not), the univariate-skip
first round, and the prover algorithms (linear-time, with special handling of
bit-valued inputs).

## Specification

### 3.1 Multilinear extensions and eq

For `v ∈ K^(2^ℓ)` (or `B^(2^ℓ)`), indexed by little-endian bits (C2), the MLE is

    ṽ(x) = Σ_{b ∈ {0,1}^ℓ} v[b] · eq(x, b),

where in characteristic 2

    eq(x, b) = Π_{i=1}^{ℓ} (1 + x_i + b_i)   (= Π x_i b_i + (1+x_i)(1+b_i)).

`ṽ` is the unique multilinear polynomial agreeing with `v` on `{0,1}^ℓ`, and
`ṽ(x_1 … x_ℓ)` has `x_1` paired with the **least significant** index bit.
Properties used throughout: `eq(x, y) = eq(y, x)`; `Σ_b eq(x, b) = 1`;
`eq(x, y) = Π (1 + x_i + y_i)` for any `x, y ∈ K^ℓ`.

**Eq table.** `eq_table(r)` returns the vector of length `2^ℓ` with entry
`i = eq(r, bits(i))`. Build it by `T ← [1]`, then for `j = 1..ℓ`:
`T ← [T[i]·(1 + r_j) for all i] ‖ [T[i]·r_j for all i]` (the new variable becomes
the next higher index bit). Cost `2^ℓ` multiplications.

**Binding.** `bind_low(T, r)` fixes `x_1 = r`:

    T'[i] = T[2i] + r·(T[2i] + T[2i+1]) = (1+r)·T[2i] + r·T[2i+1],   i < |T|/2 .

`mle_eval(T, r)` applies `bind_low` with `r_1, r_2, …` in turn, and returns the
single remaining entry: `ṽ(r)` in `O(2^ℓ)`. Entries may be `K` elements or bits.

**Suffix property** (C2). Binding the low variables of an `ℓ`-variable table to
`r_lo` yields a table over the remaining high variables; a contiguous aligned
block of `2^k` entries is the table of the polynomial obtained by fixing the
high variables to the block's index.

### 3.2 The relation

Let `g : K^m → K` be a polynomial with individual degree `≤ d` in each
variable, and `claim ∈ K`. Sum-check reduces

    claim = Σ_{b ∈ {0,1}^m} g(b)

to the claim `y = g(r)` for a challenge point `r ∈ K^m`. It runs `m` rounds, is
perfectly complete, and has soundness error at most `d·m / |K| = d·m / 2^128`
(the sum of the per-round error `d/|K|` of a degree-`d` univariate).
`g` is a polynomial the verifier either can evaluate itself or reduces further
(through the claims of the calling section). In the reference API, `g` is given
as `combine(tables)`, a degree-`≤ d`-per-variable polynomial applied to the
values of `MLE` tables (`g(x) = combine(T̃_1(x), …, T̃_n(x))`).

### 3.3 Round message format (C3)

Variables are bound in order `x_1, x_2, …, x_m` (low to high). In round `i` the
prover's univariate is

    g_i(t) = Σ_{b ∈ {0,1}^(m−i)} g(r_1, …, r_{i−1}, t, b),   deg g_i ≤ d .

Let `claim_i` be the current claim (`claim_1 = claim`, `claim_{i+1} = g_i(r_i)`).
Then `g_i(0) + g_i(1) = claim_i`, in characteristic 2.

**[OM-choice]** (Q2) The prover message of round `i` is the `d` field elements

    msg_i = [ g_i(t_0), g_i(t_2), g_i(t_3), …, g_i(t_d) ],

i.e. evaluations at `t_0 = 0` and `t_2 = X, t_3 = X+1, …, t_d` (integer points
of 1.1), omitting `t_1 = 1`, which the verifier derives as
`g_i(1) = claim_i + g_i(0)`. (There is no evaluation at infinity.) Rationale:
`d` elements per round, no division by a leading coefficient, and the same
rule for every `d ≥ 1`. For `d = 1` the message is the single element `g_i(0)`.
`d = 0` is not allowed. A message is encoded as `d` concatenated 16-byte `K`
encodings (1.2).

### 3.4 Protocol

**Transcript binding** **[OM-choice]**. Before round 1 both parties run

    absorb_k    (label ‖ b"/claim",  claim)
    absorb_bytes(label ‖ b"/params", u64le(m) ‖ u64le(d))

where `label` is the sum-check's base label (2.7), for example
`b"spartan/outer"`. Rationale: bind the claim and shape even if the caller
forgets. (Callers MUST still have the claim determined by previous transcript
data.) Then for each round `i = 1..m`:

1. Prover sends `msg_i`. Both absorb it: `absorb_ks(label ‖ b"/msg", msg_i)`.
2. Both squeeze `r_i = challenge_k(label ‖ b"/chal")`. (Each absorb resets the
   counter, so this is counter 0.)
3. Both set `claim_{i+1} = g_i(r_i)` as computed by the interpolation below.

The verifier ends with the point `r = (r_1..r_m)` and `claim_{m+1}`, which the
calling protocol must compare with `g(r)` (computed from the evaluations that
the caller obtains or checks otherwise).

**Verifier algorithm** `sumcheck_verify(claim, m, d, proof, transcript, label)`:

    require len(proof.round_msgs) == m and each msg has exactly d elements,
        else raise VerificationError
    run the transcript binding above
    cur ← claim
    for each msg:
        absorb msg; r ← squeeze
        ys ← [msg[0], cur + msg[0]] ‖ msg[1:]       # values at t_0, t_1, t_2..t_d
        cur ← Lagrange(ys, r)
    return (r_1..r_m, cur)

**Lagrange evaluation at points `t_0..t_d`.** For `ys[k] = g(t_k)`, `k = 0..d`:

    g(r) = Σ_{k=0}^{d} ys[k] · Π_{j≠k} (r + t_j) / (t_k + t_j)

(characteristic 2: subtraction is addition). The denominators are non-zero since
`t_k + t_j = t_{k xor j} ≠ 0` for `k ≠ j`. Implementations MAY precompute the
denominators and use barycentric forms. The result is unique, so every
implementation yields the same bytes.

The verifier function never accepts or rejects a *value*; the check that decides
acceptance is the caller's comparison of `cur` with `g(r)` at the end. A
tampered message or a wrong initial claim therefore results in a final-value
mismatch, with probability at least `1 − d·m/|K|`.

### 3.5 Generic prover

`sumcheck_prove(claim, tables, combine, d, transcript, label)` returns
`(proof, r, evals)` where `evals[k] = T̃_k(r)`. The tables have equal
power-of-two length `2^m`; at the start the prover has `T_k^{(0)} = T_k`.

    run the transcript binding
    for round i = 1..m:
        for t in t_0, t_1, t_2, …, t_d:
            g_i(t) = Σ_{b < |T|/2}  combine( [ T_k[2b] + t·(T_k[2b] + T_k[2b+1]) for each table k ] )
        require g_i(0) + g_i(1) == claim_i    (an honest prover: raise otherwise)
        send [g_i(t_0), g_i(t_2), …, g_i(t_d)]; absorb; squeeze r_i
        claim_{i+1} ← Lagrange([g_i(t_0), …, g_i(t_d)], r_i)
        T_k ← bind_low(T_k, r_i)
    evals ← [T_k[0]]

`T_k[2b] + t·(T_k[2b] + T_k[2b+1])` is the evaluation at `x_1 = t` of the
degree-1 interpolation of the table pair (the line through `(0, T[2b])` and
`(1, T[2b+1])`). The cost is `O(d·n·2^m)` plus `combine` per entry. `m = 0` gives
an empty proof and `evals = [T_k[0]]`.

The **table-list form** requires `combine` to have degree at most `d` in each
variable once the tables are replaced by the multilinear `T̃_k`. If `combine` has
total degree `n` in the tables then `d = n`.

### 3.6 Batching sum-checks of equal `num_vars`

Given claims `c_1..c_n` for summands `g_1..g_n` over the same `m` variables,
**[OM-choice]** combine them with powers of one challenge:

    absorb_ks(label ‖ b"/claims", [c_1..c_n])
    γ ← challenge_k(label ‖ b"/gamma")
    ρ_i = γ^(i−1)   (ρ_1 = 1),    claim = Σ_i ρ_i c_i,    g = Σ_i ρ_i g_i,

and run one sum-check on `g` with `d = max_i d_i`. Rationale: a single
challenge and a sequence of powers keep the message count minimal; the additional
soundness loss is `(n−1)/|K|`: if some `c_i ≠ Σ g_i`, then the combined claim
is false except for at most `n−1` values of `γ` (a non-zero polynomial of degree
`n−1`). **Cap (normative):** `n ≤ 256` claims per powers-of-`γ` batch, because `(n−1)/|K| < 2^{-120}` only up to `n = 256`; callers with more claims MUST split the batch (each chunk with its own `γ`) or use independent challenges, and 05.4 states the cap for Mosaic. After the sum-check the verifier needs each `g_i(r)` separately, and
recombines `Σ ρ_i g_i(r)` to compare. The reference model provides
`batch_claims` (returns `ρ` and the combined claim) and `batched_combine`
(builds the combined summand over the concatenated table list). Claims with
different `num_vars` are not batched here: the caller embeds the smaller
into the larger through the suffix property (3.1) or uses the lifting of 05.

### 3.7 Soundness

Single sum-check: error `≤ d·m/2^128`. With the batching of 3.6: add
`(n−1)/2^128`. For `m ≤ 40`, `d ≤ 4`, `n ≤ 2^20` the total error is below
`2^−100` by a wide margin; the global accounting is in 13. The Fiat–Shamir
transform adds the standard hash-chain loss (13).

### 3.8 Prover optimizations (informative)

None of these changes any transcript, message or proof byte.

* **Gruen's eq-factoring** (ePrint 2024/108). For `g(x) = eq(τ, x)·h(x)` the
  round univariate factors as `g_i(t) = ℓ_i(t)·q_i(t)` with the linear
  `ℓ_i(t) = (1 + τ_i + t)·eq(τ_{<i}, r_{<i})` (the eq factor of the bound
  variables, a scalar, folded into `ℓ_i`) and `q_i` of degree `d − 1`; the
  remaining `eq(τ_{>i}, ·)` is a table. The prover evaluates `q_i` at only
  `d − 1` points. If `τ_i ≠ 0`, `ℓ_i(1) ≠ 0` and `q_i(1) = (claim_i + ℓ_i(0) q_i(0)) / ℓ_i(1)`,
  from `g_i(0) + g_i(1) = claim_i`; this gives `d` points for `q_i`, from which
  `g_i(t_k) = ℓ_i(t_k) q_i(t_k)` is derived for the wire format (3.3). If
  `τ_i = 0` the prover falls back to evaluating `q_i` at one more point.
* **Split eq (Dao–Thaler, ePrint 2024/1210).** Write `eq(τ, x) =
  eq(τ_hi, x_hi)·eq(τ_lo, x_lo)` and store two tables of size `2^(m/2)` instead of
  one of size `2^m`, and recombine on the fly. Memory drops to `O(2^(m/2))` for
  the eq part.
* **Bit-valued first rounds.** If tables are `B`-valued, then after `j` rounds
  an entry is a degree-`j` multilinear combination of bits with `K` coefficients.
  In round 1 `T[2b] + t·(T[2b] + T[2b+1])` has `B`-valued `T`, so products are
  masks and XORs; the sum over `b` for a degree-2/3 product of bit tables can
  be accumulated as *counts* of bit patterns (a small histogram over `{0,1}^n`)
  and multiplied by the `K` factors only once per pattern. After a few rounds
  the tables become dense `K` values and the generic loop takes over. The switch
  round is an implementation choice.
* **Streaming / memory.** Delaying the first `s` binds (re-reading the original
  bit table) trades time for memory, as in Spartan-style provers.

### 3.9 Univariate skip (OPTIONAL extension, OFF in v1)

**[OM-choice]** (Q3) Univariate skip is **off in v1**: the verifying-key field
`sumcheck_version` is `1` and every sum-check follows 3.3–3.5. A later
version `2` MAY enable it, and a verifier MUST reject a proof that uses it unless
the key says `sumcheck_version = 2`. Specification of the version-2 extension,
for a skip parameter `k ≥ 1` (a verifying-key parameter for each sum-check that
uses it, `k ≤ m`):

* Let `D = {t_0, …, t_{2^k − 1}}`. This is the `B`-subspace spanned by
  `1, X, …, X^{k−1}`. Let `L_a(z)`, `a ∈ [0, 2^k)`, be the Lagrange basis on `D`
  (`L_a(t_b) = [a = b]`, degree `2^k − 1`).
* The first `k` variables `x_1..x_k` are replaced by one univariate variable
  `z`. For each table, `T̂(z, b') = Σ_a L_a(z)·T[a + 2^k·b']` (the low-degree
  extension of the first `k` index bits over `D`).
* The round-0 polynomial `s(z) = Σ_{b'} combine(T̂_1(z,b'), …)` has degree at
  most `d_s = d·(2^k − 1)`, and the claim satisfies `Σ_{a<2^k} s(t_a) = claim`.
* The prover sends `d_s` elements `s(t_j)` for `j = 0..d_s`, omitting `j = 2^k − 1`
  (which the verifier derives as `claim + Σ_{a<2^k−1} s(t_a)`). The message is
  absorbed with the label `label ‖ b"/skip/msg"`, the challenge `r_0` is
  `challenge_k(label ‖ b"/skip/chal")`, and the new claim is `s(r_0)` by
  Lagrange interpolation over `t_0..t_{d_s}`. The remaining `m − k` rounds are
  ordinary rounds (3.4) with `label` unchanged.
* The output point is `(r_0, r_1, …, r_{m−k})`. Per-table claims are `T̂(r_0, r')`,
  **not** `T̃(r)`: the `k` skipped coordinates are weighted by `L_a(r_0)` instead
  of `eq(·, a)`. Each calling section that enables skip MUST state how this
  claim is consumed (for the outer sum-checks of 06, the weight vector
  `(L_a(r_0))_a` replaces `eq_table(r_low)` on the low `k` index bits).
* Soundness error becomes `(d·(2^k−1) + d·(m−k)) / |K|`.

Both `reference/openmagnetar/sumcheck.py` and `crates/om-sumcheck` implement the standalone univariate-skip prover and verifier (`UnivariateSkipProof`, `lagrange_subspace_weights`, `bind_low_subspace`, `sumcheck_prove_skip`, `sumcheck_verify_skip`).

### 3.10 Reference model

`reference/openmagnetar/mle.py` (`eq_table`, `eq_eval`, `bind_low`, `mle_eval`)
and `reference/openmagnetar/sumcheck.py` (`SumcheckProof`, `sumcheck_prove`,
`sumcheck_verify`, `UnivariateSkipProof`, `sumcheck_prove_skip`, `sumcheck_verify_skip`,
`lagrange_subspace_weights`, `bind_low_subspace`, `VerificationError`, plus `interpolate_eval`, `batch_claims`,
`batched_combine`) with the signatures of C8. Labels appended to the caller's
base label: `/claim`, `/params`, `/msg`, `/chal` (3.4), `/claims`, `/gamma`
(3.6). Tests: `reference/tests/test_mle.py` (brute-force MLE, eq table, packing
identities of 01), `reference/tests/test_sumcheck.py` (completeness for `d =
1,2,3` and `m = 0..5`, bit-valued tables, an eq-weighted cubic, tampered and
wrong-length messages, wrong claim, batching). Vectors:
`reference/vectors/03-sumcheck/sumcheck.json` (one per `d = 1,2,3`, `m = 3`,
with tables, claim, messages, challenges and final claim) and `mle.json`,
generated by `reference/gen_vectors_01_03.py`.

## Resolved questions

1. Binding order: low-to-high (3.3, C3).
2. Round message: `d` evaluations at `t_0, t_2..t_d`, `g(1)` derived; no point at
   infinity (3.3) **[OM-choice]**.
3. Univariate skip: optional version-2 extension, off in v1 (3.9) **[OM-choice]**.
4. Gruen eq-factoring: a pure prover optimization, no transcript change (3.8).

## Requests to other sections

- 06 SHOULD say which sum-checks (if any) use `sumcheck_version = 2`, and how the
  skipped-coordinate weights `L_a(r_0)` are consumed.
- 11 MUST ensure that every sum-check claim is determined by transcript state
  before the sum-check starts (the sum-check also absorbs the claim, 3.4), and
  list the base labels.

## Integration notes

* 2026-10-16 (13): 3.6 now states the limit `n ≤ 256` for powers-of-`γ` batching at 120-bit soundness (13.2 note 3). `sumcheck.batch_claims` raises `ValueError` above 256 claims, and Mosaic (05) enforces the same cap.
