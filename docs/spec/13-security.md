# 13. Security analysis and parameters

**Status:** outline · **Paper:** §3.2, §6.1, Theorem 1, ref [5]

## Scope
Per-step soundness error accounting (each sum-check, batching, one-hot,
lockstep outer, inner, router, Twist/Shout, Mosaic batching, ring switching,
Ligerito) under the 'every round ≤ 2^-120' interpretation the paper uses;
Ligerito parameter derivation at unique-decoding radius; hash output length
requirements (collision resistance for Merkle, ROM for Fiat–Shamir, including
round-by-round soundness for FS security).

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** The paper's '120 bits: every round has soundness error ≤ 2^-120'. Is round-by-round soundness the right notion for FS here, and what is the end-to-end bound?
   - *Proposed:* Adopt round-by-round soundness (needed for FS security without the Q-factor loss); document both per-round and total bounds.
2. **Q:** Hash output: SHA-256 gives 128-bit collision resistance classically and ~85 bits against quantum collision finding (BHT). Is that acceptable for 'post-quantum'?
   - *Proposed:* Document it. Offer SHA-384/SHA3-384 as a stronger PQ profile.

## Specification

_To be written._
