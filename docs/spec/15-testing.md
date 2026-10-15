# 15. Testing and conformance

**Status:** outline · **Paper:** —

## Scope
The Python reference model (reference/): field arithmetic, transcript,
sum-check, MLE, CPU circuit witness generation and constraint checking,
Twist/Shout/Router identities on small instances. Test-vector format consumed
by Rust tests. Riscv-tests / riscv-arch-test conformance for the emulator.
Negative tests: tampered proofs, wrong I/O, malicious witnesses for each relation.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** How far does the reference model go: full prover/verifier, or just the arithmetization + individual sub-protocols?
   - *Proposed:* Arithmetization (emulator, witness, constraints, identities) in full; sub-protocols individually at toy sizes. No full Ligerito in Python.
2. **Q:** Python version and dependencies
   - *Proposed:* Pure Python 3.12+, no deps beyond the stdlib (hashlib), so it stays easy to audit.

## Specification

_To be written._
