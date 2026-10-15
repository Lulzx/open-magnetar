# 01. Fields and encodings

**Status:** outline · **Paper:** §3, §4.3

## Scope
B = GF(2), K = GF(2^128), the canonical embedding B ↪ K, the B-basis β_0..β_127
used for packing 128 witness bits per K element, and byte encodings of field
elements and bit vectors. Index conventions: little-endian, as in §3.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Which irreducible polynomial / representation of K?
   - *Proposed:* POLYVAL/GHASH polynomial x^128+x^127+x^126+x^121+1 (POLYVAL) or x^128+x^7+x^2+x+1. Prefer the one with the cheapest reduction after PMULL/PCLMULQDQ; must be compatible with the additive-FFT basis Ligerito needs (see 04).
2. **Q:** Packing basis β_j: monomial basis {1, X, …, X^127}, or a basis chosen to make ring switching cheaper?
   - *Proposed:* Monomial basis, unless 04 shows ring switching needs a tower or other structure.
3. **Q:** Do we need GF(2^k) subfields (k = 8, 16, 32, 64) for small-field optimizations (univariate skip, first sum-check rounds over bits)?
   - *Proposed:* Not for the K representation itself. Treat optimizations over B as specializations of the arithmetic (bits × K).
4. **Q:** Canonical byte encoding of K elements
   - *Proposed:* 16 bytes, little-endian coefficient order. Non-canonical encodings cannot exist, since every 128-bit string is valid.

## Specification

_To be written._
