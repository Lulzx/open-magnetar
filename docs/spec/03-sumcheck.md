# 03. Multilinear extensions and sum-check

**Status:** outline · **Paper:** §3.1–3.2, refs [3,12,22]

## Scope
MLE and eq definitions, the variable binding order, sum-check round message
format (which evaluations are sent, compressed or not), the univariate-skip
first round, and the prover algorithms (linear-time, with special handling of
bit-valued inputs).

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Variable binding order: low-to-high or high-to-low?
   - *Proposed:* Low-to-high (bind x_1 first), matching little-endian indexing and the 'suffix selects the subcube' convention in 05/06.
2. **Q:** Round message encoding: send d+1 evaluations, or d evaluations and derive one from the claim?
   - *Proposed:* Send evaluations at {0, ∞, 2..} minus the derivable one. Over characteristic 2, use points {0,1,X,X+1,…} from K; the exact point set must be specified.
3. **Q:** Univariate skip (Gruen [22]): the paper mentions different parameters for the two outer sum-checks but gives none.
   - *Proposed:* Spec an optional k-variable skip for the outer sum-checks; start with k=0 (off) for correctness and add it in the optimization milestone.
4. **Q:** Gruen's eq-factoring optimization for eq(τ,x)·(…) sum-checks
   - *Proposed:* Yes, it is purely a prover optimization and does not change the transcript.

## Specification

_To be written._
