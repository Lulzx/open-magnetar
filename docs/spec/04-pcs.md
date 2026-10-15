# 04. Polynomial commitment: Ligerito and ring switching

**Status:** outline · **Paper:** §3.6, §6, refs [13,44,5]

## Scope
The PCS trait (commit / open / verify for multilinear polynomials over K),
Merkle tree layout and hashing, the Reed–Solomon code over binary fields
(additive NTT), the Ligerito protocol, and ring switching from a bit-valued
MLE claim to a claim on the packed polynomial P over K.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Reed–Solomon over binary fields: which additive FFT (Lin–Chung–Han novel basis) and which evaluation domain?
   - *Proposed:* LCH additive NTT over a GF(2)-subspace of K, as in Binius/FRI-Binius. Exact basis to be specified.
2. **Q:** Ligerito recursion depth, per-level code rates and dimensions
   - *Proposed:* Pick to meet 120-bit provable (unique decoding radius, [5]); parameter table lives in 13.
3. **Q:** Proven unique-decoding parameters imply ~2× queries vs. list-decoding conjecture. Offer a 'conjectured' profile?
   - *Proposed:* Yes, behind an explicit opt-in flag, clearly labelled non-provable, for comparison only.
4. **Q:** Merkle leaf = one codeword column (many K elements) hashed together; tree arity; leaf hashing domain separation
   - *Proposed:* Binary tree, SHA-256, leaf = H(0x00 ‖ column bytes), node = H(0x01 ‖ l ‖ r). Specify batching of paths (multi-proof / path pruning).
5. **Q:** Ring switching (Diamond–Posen [13]) exact protocol and its interaction with the packing basis in 01
   - *Proposed:* Follow [13] §4. Write it out fully here, since the paper treats it as a black box.
6. **Q:** Should the PCS trait support multiple opening points natively (batching inside PCS) or only single-point?
   - *Proposed:* Single-point; batching is done by MosaicPCS (05).

## Specification

_To be written._
