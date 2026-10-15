# open-magnetar

An independent, open-source implementation of the **Magnetar** protocol: a
transparent, hash-based, post-quantum proof system for RV64I program executions
(a zkVM), described in

> Srinath Setty. *Magnetar: High-speed post-quantum RV64 zkVM from standard
> hashes.* 2026. [ePrint 2026/2423](https://eprint.iacr.org/2026/2423)

> **Disclaimer.** This project is not affiliated with, endorsed by, or derived
> from code by Microsoft or Microsoft Research. It is a clean-room
> re-implementation based on the public paper. Where the paper leaves details
> unspecified, this project makes its own choices, documented in
> [`docs/spec/`](docs/spec/). Performance and proof sizes will differ from those
> reported in the paper.

## Status

**Pre-alpha: specification phase.**

- **Specification.** All sections 00–15 of [`docs/spec/`](docs/spec/) are at
  `draft` status. Start with [`00-overview.md`](docs/spec/00-overview.md) and
  [`CONVENTIONS.md`](docs/spec/CONVENTIONS.md). Every design decision the
  paper does not dictate is marked **[OM-choice]**.
- **Reference model.** [`reference/`](reference/) holds an executable,
  stdlib-only Python model of every component. It includes an end-to-end
  prover and verifier that prove tiny RV64I programs: Fibonacci, loads and
  stores, and register-amount shifts. It is slow by design and exists to pin
  down the spec and generate test vectors.
- **Rust implementation.** Not started; it comes after spec review.

Known open items are tracked in
[`13-security.md` §13.9](docs/spec/13-security.md), the "unverified against
source" audit list. Parts of the Ligerito, ring-switching and Twist/Shout
sections were derived without access to the original papers and need review.

**This code has not been audited. Do not use it to secure anything of value.**
The reference model is not zero-knowledge.

## Quick start

```sh
# run the reference-model test suite (pure Python 3.12+, no dependencies)
python3 -m unittest discover -s reference/tests -t reference

# regenerate JSON test vectors
python3 reference/gen_vectors_01_03.py   # likewise gen_vectors_04.py ... gen_vectors_11_12.py
```

## Design at a glance

| Component | Role | Spec |
|---|---|---|
| Dual SIMD R1CS (GF(2) and GF(2^128)) over one bit-valued witness | CPU fetch-decode-execute | [06](docs/spec/06-spartan.md), [10](docs/spec/10-cpu-circuit.md) |
| Virtual Spartan | Reduces both relations to one claim per witness segment | [06](docs/spec/06-spartan.md) |
| BinaryTwist / BinaryShout | Register, RAM and bytecode consistency | [07](docs/spec/07-twist-shout.md) |
| BinaryRouter | Shifts and sub-word stores | [08](docs/spec/08-router.md) |
| MosaicPCS + ring switching + Ligerito | One commitment, one opening | [05](docs/spec/05-mosaic.md), [04](docs/spec/04-pcs.md) |
| SHA-256 Fiat–Shamir transcript | Non-interactive proofs | [02](docs/spec/02-transcript.md) |

## Goals

- Proves RV64I executions (the M extension is planned later).
- Security rests only on standard hash functions (SHA-256 by default, SHA3-256
  optional). No elliptic curves, lattices, algebraic hashes, trusted setup, or
  conjectured proximity gaps.
- 120 bits of provable security by default.
- All arithmetic is over GF(2) and GF(2^128). The PCS is Ligerito.

## Repository layout

```
docs/spec/            normative specification (sections 00–15 + CONVENTIONS.md)
reference/            executable Python reference model
  openmagnetar/       one module per protocol component, plus protocol.py (end to end)
  tests/              unit, sub-protocol, end-to-end and negative tests
  vectors/            JSON test vectors for future implementations
guest/                guest toolchain: linker script, runtime, Rust target JSON (untested)
crates/               Rust workspace members (not yet created)
```

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.

Unless you explicitly state otherwise, any contribution you intentionally
submit for inclusion in this work, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
