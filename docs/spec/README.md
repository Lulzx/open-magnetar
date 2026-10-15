# open-magnetar specification

This directory is the normative specification for open-magnetar. Code in
`crates/` and the reference model in `reference/` MUST agree with it. If they
disagree, the spec is the source of truth, or the spec is fixed first.

The key words MUST, MUST NOT, SHOULD, SHOULD NOT and MAY are used as in
RFC 2119.

Paper references such as "§5.3" refer to Setty, *Magnetar*, ePrint 2026/2423.

## Status legend

- `outline`: scope and open questions only
- `draft`: content written and under review
- `stable`: reviewed; changes need a spec-change note

## Sections

| # | File | Topic | Paper | Status |
|---|------|-------|-------|--------|
| 00 | [00-overview.md](00-overview.md) | Architecture, data flow, claim graph | §2 | outline |
| 01 | [01-fields.md](01-fields.md) | GF(2), GF(2^128), packing basis, encodings | §3, §4.3 | draft |
| 02 | [02-transcript.md](02-transcript.md) | Fiat–Shamir transcript, hashing, challenge sampling | §3.4 | draft |
| 03 | [03-sumcheck.md](03-sumcheck.md) | Multilinear extensions, eq, sum-check, univariate skip | §3.1–3.2 | draft |
| 04 | [04-pcs.md](04-pcs.md) | PCS trait, Merkle trees, Ligerito, ring switching | §3.6, §6 | draft |
| 05 | [05-mosaic.md](05-mosaic.md) | MosaicPCS layout, lifting, batching | §5.2 | draft |
| 06 | [06-spartan.md](06-spartan.md) | SIMD R1CS, BinarySpartan, Virtual Spartan, cross-step constraints | §4.1–4.3, §5.1, §5.3 | draft |
| 07 | [07-twist-shout.md](07-twist-shout.md) | BinaryTwist, BinaryShout, one-hot check | §4.4 | draft |
| 08 | [08-router.md](08-router.md) | BinaryRouter for shifts and sub-word stores | §5.4 | draft |
| 09 | [09-isa.md](09-isa.md) | RV64I semantics, virtual instructions, bytecode table | §2.1, §5 | draft |
| 10 | [10-cpu-circuit.md](10-cpu-circuit.md) | Witness layout, segments, the two R1CS relations | §5.1 | draft |
| 11 | [11-protocol.md](11-protocol.md) | Full prover/verifier composition | §5.5 | outline |
| 12 | [12-proof-format.md](12-proof-format.md) | Proof and key serialization | — | outline |
| 13 | [13-security.md](13-security.md) | Soundness accounting, parameter selection | §3.2, §6.1, Thm 1 | draft |
| 14 | [14-guest-abi.md](14-guest-abi.md) | Guest toolchain, memory map, I/O, termination | — | draft |
| 15 | [15-testing.md](15-testing.md) | Reference model, test vectors, conformance | — | draft |

## Suggested writing order

Each section depends only on earlier ones in this order:

01 → 02 → 03 → 04 → 13 (PCS parameters) → 06 → 07 → 08 → 05 → 09 → 10 → 11 → 12 → 14 → 15 → 00 (finalized last)

## Where we depart from the paper

The paper gives the architecture but leaves out several details. Every choice
we make that the paper does not dictate MUST be marked in the spec text with
**[OM-choice]** and a short rationale. That way readers can tell paper-mandated
behavior from our own decisions.
