# 06. Spartan family: SIMD R1CS, BinarySpartan, Virtual Spartan

**Status:** outline · **Paper:** §4.1–4.3, §5.1, §5.3, Remark 4

## Scope
SIMD R1CS over B and over K with shared witness W; the z = (w, 1, x) layout
and Eq. (1); outer and inner sum-checks; the lockstep dual outer sum-check with
shared instance challenges; the single batched inner sum-check; per-segment
claim split (Construction 2); cross-step constraints via the 'next' MLE; and
binding of the public initial and final state.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Cross-step constraints: the paper omits them (Remark 4). How exactly does the 'next' MLE [53] enter, and which state crosses instance boundaries (micro-PC, PC, halted flag)?
   - *Proposed:* Spec a 'shift' sum-check over instance coordinates relating segment S_out of instance j-1 to S_in of instance j, with the first/last instances bound to public values. Needs its own soundness entry in 13.
2. **Q:** Is the K-coefficient relation evaluated with K-valued matrix entries, and how do we compute A_2·z efficiently when z is bits?
   - *Proposed:* Precompute per-column packed coefficients; A_2 z is a sum of K constants selected by bits (XOR of table entries).
3. **Q:** Outer sum-check degree over B-relation: since witness is bits, does A_1z·B_1z − C_1z still need the full degree-3 treatment?
   - *Proposed:* Yes at the protocol level; the prover's first rounds can use bit-level tricks.
4. **Q:** Public input x layout: where do inp/out hashes or values live?
   - *Proposed:* x = (initial state, final state, I/O digest); actual I/O bytes go in RAM regions bound via M_0 / final-memory claims (see 14).

## Specification

_To be written._
