# 11. Complete protocol

**Status:** outline · **Paper:** §5.5, Construction 3, Lemma 5, Theorem 1

## Scope
Prover and verifier pseudo-code for Construction 3, steps 1–7, with every
transcript interaction in order and every claim routed per the claim graph.
Preprocessing (KeyGen) outputs: ROM, s_1, s_2, layout L, R_sh, R_st, Mosaic
layout, vk digest.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Trace length T: fixed per vk, or chosen per proof (vk contains program only, T in the instance)?
   - *Proposed:* Per proof, with T a power of two in a bounded range; layout derived from (program, T).
2. **Q:** Padding cycles after halt
   - *Proposed:* A 'halted' virtual instruction self-loop at a fixed micro-PC with no memory effects.

## Specification

_To be written._
