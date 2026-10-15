# 00. Overview

**Status:** outline · **Paper:** §2

## Scope
End-to-end architecture: Harvard RV64I machine, micro-PC, the five online phases
(execute, commit, Virtual Spartan, discharge virtual claims, single PCS opening).
Includes the **claim graph**: every evaluation claim, who produces it, who consumes it.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Should the claim graph be machine-readable (e.g. a table generated from the reference model) so the Rust and Python implementations can be cross-checked?
   - *Proposed:* Yes: generate it from the reference model and check it into the docs.

## Specification

_To be written._
