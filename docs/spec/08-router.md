# 08. BinaryRouter

**Status:** outline · **Paper:** §5.4

## Scope
The routing identity Y(o,j) = Σ_{u,h} X(u,j)·Q(h,j)·R(o,u,h) and its sum-check;
the shift instance (sources, two-factor one-hot selector Q_lo·Q_hi, R_sh) and the
sub-word-store instance (old word + store source → Inc, selector over 4 widths,
R_st with 3 offset bits); verifier evaluation of R̃.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Exact enumeration of shift routings h ('a few hundred'): SLL/SRL/SRA × amount 0..63 (+ W variants for SLLW/SRLW/SRAW with sign extension)
   - *Proposed:* Enumerate explicitly; SRA's sign fill is a source u = sign bit; W variants need sign-extension of bit 31.
2. **Q:** Split h = (h_lo, h_hi) widths
   - *Proposed:* Pick to make |h_lo|, |h_hi| ≈ √H, e.g. 16 × 32.
3. **Q:** Closed-form MLE of R_sh and R_st so the verifier evaluates them in O(log) or O(H) time
   - *Proposed:* Derive in spec; it must be cheap.
4. **Q:** Register-amount shifts expand into a fixed sequence of static routings: what sequence?
   - *Proposed:* Barrel-shifter decomposition: 6 conditional static shifts by 1,2,4,8,16,32, each selected by a bit of rs2. Cost: 6 virtual cycles; alternative designs welcome.

## Specification

_To be written._
