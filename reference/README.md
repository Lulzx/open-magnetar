# Reference model

An executable Python model of open-magnetar (pure Python 3.12+, stdlib only).
It exists to:

1. pin down the arithmetization (RV64I emulator, virtual-instruction expansion,
   witness layout, both R1CS relations, Twist/Shout/Router identities)
   unambiguously, alongside `docs/spec/`;
2. generate test vectors that the Rust crates must reproduce.

It is not a prover and makes no performance claims. See `docs/spec/15-testing.md`.
