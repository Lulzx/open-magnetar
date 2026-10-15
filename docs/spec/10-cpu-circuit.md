# 10. CPU circuit

**Status:** outline · **Paper:** §5.1, §2.2(1)

## Scope
The per-instance base R1CS over B (s_1) and over K (s_2); number of cycles per
SIMD instance; the full witness layout W partitioned into aligned segments,
each marked direct or virtual and assigned an owner (Twist-reg, Twist-RAM,
Shout-bytecode, Router-shift, MosaicPCS); constraint-by-constraint datapath
(adder, comparator, logic, branch, PC update, load extract, store-copy binding).

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Cycles per SIMD instance (the paper says 'several consecutive cycles')
   - *Proposed:* Choose 2^c cycles so per-instance column count is a power of two with little padding; c = 1 or 2 initially, then tune.
2. **Q:** Which operations go in the B relation vs the K relation
   - *Proposed:* B: adder carries, comparisons, bitwise logic, decode checks. K: word-wide muxes (result select, PC select, write-back select), packed equality/copy constraints.
3. **Q:** Segment layout: alignment forces power-of-two segment sizes; how do we minimize padding?
   - *Proposed:* Buddy-pack segments within the column space, same algorithm as 05.
4. **Q:** Load path: RAM is 64-bit words; byte/half/word loads need extraction + sign-extension — R1CS or a third router instance?
   - *Proposed:* R1CS in v1 (mux over 8/4/2 lanes); measure, then consider a 'load router'.
5. **Q:** ADD/SUB/SLT via ripple-carry over B (64 carries, majority constraints)
   - *Proposed:* Yes, as the paper hints (XOR + majority logic).

## Specification

_To be written._
