# 01. Fields and encodings

**Status:** draft · **Paper:** §3, §4.3

## Scope
B = GF(2), K = GF(2^128), the canonical embedding B ↪ K, the B-basis β_0..β_127
used for packing 128 witness bits per K element, and byte encodings of field
elements and bit vectors. Index conventions: little-endian, as in §3.

## Specification

### 1.1 The fields

`B = GF(2) = {0, 1}`. `K = GF(2^128)` is defined as

    K = GF(2)[X] / (X^128 + X^7 + X^2 + X + 1)

**[OM-choice]** The modulus is `m(X) = X^128 + X^7 + X^2 + X + 1` (the standard
low-weight irreducible pentanomial of degree 128; as an integer, `(1<<128) | 0x87`).
Rationale: the cheapest reduction after a carry-less multiply (see 1.6). We do
not use the POLYVAL/GHASH polynomial, because we do not need its bit-reflected
layout, and ring switching and Ligerito (04) need no tower or subspace structure
from `K` beyond what the monomial basis gives.

An element of `K` is a polynomial `a(X) = Σ_{i<128} a_i X^i` with `a_i ∈ B`. It is
**identified with the 128-bit unsigned integer** `Σ a_i 2^i`. Addition is XOR of
these integers (so `-a = a` and `a + a = 0`). Multiplication is polynomial
multiplication followed by reduction modulo `m(X)`. This is the plain polynomial
basis and is **not** GHASH's bit-reflected convention. The reference model's
field tests check the field axioms and `a · a^(2^128−2) = 1` on random elements.

`B` embeds in `K` as `0 ↦ 0`, `1 ↦ 1`. `K` is a 128-dimensional vector space
over `B`.

**Small integers as points.** For an integer `k` with `0 ≤ k < 2^128`, `t_k ∈ K`
is the element whose integer value is `k`. So `t_0 = 0`, `t_1 = 1`, `t_2 = X`,
`t_3 = X + 1`, `t_4 = X^2`. The `t_k` are pairwise distinct, which is all that
sum-check interpolation (03) needs. Note `t_k + t_j = t_{k xor j}`.

**[OM-choice]** No subfield tower `GF(2^8), GF(2^16), …` is part of the format.
Rationale: nothing in the protocol needs it. Optimizations that exploit small
values (bit-valued tables, `B × K` products) are specializations of arithmetic
in `K` and MUST NOT change any transcript, proof or commitment byte.

### 1.2 Byte encodings

| Object | Encoding |
|---|---|
| `a ∈ K` | 16 bytes, little-endian: byte `i` holds integer bits `8i..8i+7`. Byte 0 holds the coefficients of `X^0..X^7`. |
| `a ∈ K^n` | the `n` encodings concatenated, with no count prefix (the count comes from context or an enclosing length field, see 12). |
| bit vector `w ∈ B^N` | `ceil(N/8)` bytes, bit `i` at byte `⌊i/8⌋`, bit position `i mod 8` (LSB-first). Unused high bits of the last byte MUST be zero, and a decoder MUST reject non-zero padding. |

Every 16-byte string is a valid, canonical encoding of exactly one element. A
decoder MUST reject any other length and has no other failure mode. Test-vector
JSON writes a `K` element as the 32-character lowercase hex of this encoding.

**Consequence.** For `N` a multiple of 128 the bit-vector encoding is
byte-identical to the encoding of the packed `K` vector of 1.3. Implementations
MAY exploit this (packing is a `memcpy` on a little-endian machine).

### 1.3 Packing

Let `ℓ ≥ 7` and let `w ∈ B^(2^ℓ)` be a bit vector, indexed by `i ∈ [0, 2^ℓ)` with
little-endian bits (C2). Write `i = j + 128·v` with `j ∈ [0, 128)` and
`v ∈ [0, 2^(ℓ−7))`. The paper's `w(u_j, v)` is `w[j + 128 v]`: the **low 7 index
bits select the bit position within an element, and the high `ℓ−7` bits select
the element**. This follows C2.

**[OM-choice]** The packing basis is the monomial basis `β_j = X^j`, `j = 0..127`.
Rationale: it makes packing the identity on the encoding (1.2), and ring
switching (04) needs only that `{β_j}` is a `B`-basis.

The packed vector `P ∈ K^(2^(ℓ−7))` is

    P[v] = Σ_{j=0}^{127} β_j · w[j + 128 v]
         = the element whose integer value is Σ_j w[j+128v] · 2^j .

`unpack` is the inverse (`P[v].unpack()` returns `w[128v .. 128v+127]`). Both
directions are bijections `B^128 ↔ K`. For `ℓ < 7` there is no packing: such a
vector MUST first be zero-padded to length `2^7` (the padding policy for the
committed layout is in 05).

### 1.4 Bit-vector MLE versus packed MLE (the ring-switching identity)

Let `r = (r_lo ∥ r_hi)` with `r_lo ∈ K^7` and `r_hi ∈ K^(ℓ−7)` (C2: `r_lo`
binds the 7 low variables). Let `w_j ∈ B^(2^(ℓ−7))` be the row
`w_j[v] = w[j + 128 v]`, and define the 128 **row evaluations**

    s_j := w̃_j(r_hi) ∈ K ,   j = 0..127 .

Then for every `w` and `r`:

* **(I1)** `w̃(r_lo ∥ r_hi) = Σ_j eq(r_lo, j) · s_j`
* **(I2)** `P̃(r_hi) = Σ_j β_j · s_j`

*Proof.* (I1): expand `w̃(r) = Σ_{j,v} w[j+128v] eq(r_lo,j) eq(r_hi,v)` and sum
over `v` first. (I2): `P̃(r_hi) = Σ_v eq(r_hi,v) Σ_j β_j w[j+128v]`, and sum over
`v` first. ∎

(I1) is the virtual evaluation claim on the bit vector (`R^B_veval`), and (I2)
relates it to the claim on the packed polynomial that the PCS opens. The `s_j`
are not known to the verifier. The ring-switching reduction (specified in 04,
following Diamond–Posen) links them: the prover sends
`ŝ = Σ_v eq(r_hi, v) ⊗ P[v] ∈ K ⊗_B K`, whose 128 columns (column `j` paired with
`β_j = X^j`) are the `s_j`. The verifier checks (I1) from those columns, and a
sum-check reduces the consistency of `ŝ` to a single evaluation of `P̃`. This
section fixes only the index convention: the 7 *low* variables are the ones that
are switched. The reference model checks (I1) and (I2) numerically in
`reference/tests/test_mle.py`.

### 1.5 Mixed operands

A bit `b ∈ B` used as an operand of `K` arithmetic is its embedding. Reference
code MAY accept Python `0`/`1` for bits. A product `b · a` with `b ∈ B` is `a`
if `b = 1` and `0` otherwise (one AND-mask in fast code).

### 1.6 Implementation note (informative)

* **Multiplication.** On AArch64 use `PMULL`/`PMULL2` (64×64→128 carry-less) and on
  x86-64 `PCLMULQDQ`. A 128×128 product needs 3 (Karatsuba) or 4 of them and
  gives a 256-bit product `(hi, lo)`.
* **Reduction.** With `X^128 ≡ X^7 + X^2 + X + 1 = 0x87`, fold `hi` twice:
  `t = hi · 0x87` (a carry-less multiply by an 8-bit constant, or the shift-xor
  `hi ^ hi<<1 ^ hi<<2 ^ hi<<7`, up to 135 bits); `lo ^= t mod 2^128`; the
  overflow `t >> 128` (at most 7 bits) is folded once more as
  `lo ^= (t >> 128) · 0x87`. Barrett reduction costs two more `PMULL`s but has
  no data-dependent steps. No bit reflection is needed.
* **Squaring** is linear over `B` (bit spreading, then reduction) and cheaper
  than a general multiply.
* **Inversion**: `a^(2^128−2)` with an Itoh–Tsujii addition chain, or batch
  inversion (Montgomery's trick).
* **`B × K`** products are masks, and `B × B` products are ANDs. Sum-check first
  rounds over bit tables use them (03, section 3.8).

### 1.7 Reference model

`reference/openmagnetar/field.py` (class `K`; its API is fixed by C8 and is not
changed here). Packing is `K.pack`/`K.unpack`; encodings are
`to_bytes`/`from_bytes`. The identities of 1.4 are tested in
`reference/tests/test_mle.py`.

## Resolved questions

1. Representation of K: `X^128+X^7+X^2+X+1`, polynomial basis (1.1) **[OM-choice]**.
2. Packing basis: monomial `β_j = X^j` (1.3) **[OM-choice]**.
3. Subfields: not part of the format (1.1) **[OM-choice]**.
4. Byte encoding: 16 bytes little-endian, every string valid (1.2).

## Requests to other sections

- 04 SHOULD state ring switching in terms of (I1)/(I2) and the `K ⊗_B K` column
  convention above.
- 05 owns the padding policy for vectors shorter than `2^7`.
