# 05. MosaicPCS

**Status:** outline · **Paper:** §5.2

## Scope
Layout algorithm placing N power-of-two-sized bit polynomials on disjoint
aligned subcubes of one hypercube, the suffix s_i of each, claim lifting
(Eq. 4), the batching sum-check, and hand-off to ring switching + PCS.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Layout algorithm: deterministic, from the vk only (sort by size descending, buddy allocation)?
   - *Proposed:* Yes: sort by (log-size desc, component id), then buddy-allocate. Deterministic, so the verifier recomputes it.
2. **Q:** Wasted space when the total isn't a power of two (the zero region still gets committed and encoded)
   - *Proposed:* Measure it; consider letting the top-level ℓ be minimal and accept the padding.
3. **Q:** Batching sum-check: one α_i per claim, or powers of one α?
   - *Proposed:* Powers of one α (one squeeze). The soundness loss is #claims/|K|, which is negligible.

## Specification

_To be written._
