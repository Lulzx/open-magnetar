# 02. Fiat–Shamir transcript

**Status:** outline · **Paper:** §3.4 (public-coin RoK + Fiat–Shamir)

## Scope
The transcript object, domain separation, absorbing protocol messages, and
squeezing challenges in K, as K^n vectors, and as bit strings (Merkle query
indices). Hash-function abstraction (`Hasher`).

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Construction: duplex sponge over SHA3/Keccak vs. a hash-chain over SHA-256?
   - *Proposed:* Hash chain: state ← H(tag ‖ state ‖ len ‖ msg); challenge_i = H("chal" ‖ state ‖ i). Same construction for every hash, with SHA-256 the default.
2. **Q:** What is bound at transcript init (protocol id, version, program digest, trace length, public I/O, parameters)?
   - *Proposed:* All of them. The verifying key digest MUST be absorbed before cm_G.
3. **Q:** Uniform sampling of query indices from hash output
   - *Proposed:* Rejection sampling, or a 64-bit output reduced mod 2^k (exact, since domains are powers of two).
4. **Q:** Sampling rules with exclusions, e.g. the one-hot check resamples r when some c_h = 0 (§4.4), and α_0 ≠ 0
   - *Proposed:* Deterministic re-squeeze loop with a counter; specify it exactly.
5. **Q:** Proof-of-work grinding to reduce query count?
   - *Proposed:* Not by default (keep 120-bit provable without grinding). MAY be an optional parameter, accounted for in 13.

## Specification

_To be written._
