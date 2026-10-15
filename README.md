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

**Pre-alpha: specification phase.** No usable code yet. The spec is being
written first; see [`docs/spec/README.md`](docs/spec/README.md).

**This code has not been audited. Do not use it to secure anything of value.**

## Goals

- Proves RV64I executions (the M extension is planned later).
- Security rests only on standard hash functions (SHA-256 by default, SHA3-256
  optional). No elliptic curves, lattices, algebraic hashes, trusted setup, or
  conjectured proximity gaps.
- 120 bits of provable security by default.
- All arithmetic is over GF(2) and GF(2^128). The PCS is Ligerito.

## Repository layout

```
docs/spec/   normative specification (written first)
reference/   executable Python reference model; generates test vectors
crates/      Rust workspace members (not yet created)
```

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.

Unless you explicitly state otherwise, any contribution you intentionally
submit for inclusion in this work, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
