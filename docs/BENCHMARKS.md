# Benchmarks

Measured 2026-10-16 on an Apple M4 Pro (24 GiB RAM), Rust release build
(`cargo build -p om --release`, thin LTO), unless stated otherwise. These
numbers are for the implementation as it stands: correct and byte-compatible
with the Python reference model, but with a deliberately straightforward
prover (see "Why the prover is slower than the paper" below).

Guests were built with the Homebrew LLVM toolchain (`brew install llvm lld`,
see `guest/Makefile`) and proved through the `om` CLI with
`Params(ram_log_words=16, input=14, output=14)` (spec 14 defaults; the guest
ELFs for these runs were linked with `A=16` region bases to match).

## End-to-end guests (proved and verified)

| Guest | Profile | T (cycles) | Prove | Verify | Proof size |
|---|---|---|---|---|---|
| fibonacci, fib(19) = 4181 | test (t = 8) | 256 | 0.95 s | 15 ms | 23,526 B |
| fibonacci, fib(19) = 4181 | provable-120 (t = 177, gs = 2) | 256 | 0.81 s | 23 ms | 83,654 B |
| sha256 of `"abc"` | test (t = 8) | 8,192 | 61.7 s | 52 ms | 34,526 B |
| erc20-transfer (3 accounts) | test (t = 8) | 512 | 1.40 s | 16 ms | 25,974 B |

Outputs were checked independently (fib value, SHA-256 digest `ba7816bf…`,
post-transfer balances 70/80). The remaining twelve Table 1 workloads
(hot-cell-increment, stream-copy, pointer-chase, binary-search,
radix-sort-u64, lz4-decode, varint-decode, keccak-f1600, sha256-merkle-path,
erc20-transfer-from, erc20-mixed-block, evm-erc20-transfer) build as guests
and pass 47 host-oracle execution cases in the reference interpreter; they
have not each been proved end-to-end yet.

## Test suites

| Suite | Count | Wall time (debug) |
|---|---|---|
| Rust workspace (`cargo test --workspace`) | 331 tests, 0 failures | ~1 min |
| Python reference (`unittest discover`) | 223 tests, 0 failures | 114 s |
| Guest oracle executions (Python harness) | 47 cases, all pass | ~1 min |

Every `reference/vectors/**/*.json` file (27 files) is reproduced
byte-for-byte by the corresponding Rust crate's tests, including the
end-to-end Fibonacci proof (15,630 bytes) and its verifying key.

## Proof-size model at scale (not measured at that size)

From `params.proof_size_bytes` (spec 04.7 / 13.5), provable-120 profile:

| `n_pack` | Ligerito opening |
|---|---|
| 20 | 357 KiB |
| 22 | 415 KiB |
| 24 | 509 KiB |
| 26 (T = 2^22 machine) | 624 KiB, ≈ 656 KiB whole proof |

The paper reports at most 599 KiB for the whole proof, so the model is in the
paper's range. Treat absolute values as estimates (±15%) until a T = 2^22
proof is actually generated and measured.

## Comparison with the paper, honestly

| Quantity | Paper (Magnetar) | This implementation |
|---|---|---|
| Proving throughput | ~1.45 M fib steps/s (≈ 7 M cycles/s class) | ~10^2–10^3 cycles/s at small T (see below) |
| Proof size | ≤ 599 KiB | 84 KiB measured at T = 256; ≈ 656 KiB modelled at T = 2^22 |
| Verifier time | ~13 ms | 14–52 ms measured at the sizes above |

The verifier is in the paper's ballpark. The prover is not — by orders of
magnitude — for a structural reason: both the Python reference model and this
faithful Rust port materialise the dense `T · 2^a` tables of the Twist
read/write sum-check (spec 07.5), so proving cost grows with the RAM address
space (`2^a`), not just with the trace. The paper's prover (and spec 07.10,
which is informative only) uses a sparse, linear-in-T algorithm. Closing that
gap means implementing the sparse prover algorithms of 07.10 (and analogous
sparsity in Shout/Spartan witness handling); the transcript, proof format and
verifier would not change. A rayon pass over the dense hot loops (sum-check
rounds, table construction, Ligerito row encodes, Merkle layers) already gave
4–8× (sha256 prove: 510 s → 62 s) with bit-identical proofs, which is the
current state of optimisation: parallel, but asymptotically the reference
algorithm.

Other paper comparisons: security is the 120-bit provable profile by default
(no conjectured proximity gaps, no grinding), SHA-256 by default, strict
RV64I only, no zero-knowledge and no recursion — matching the v1 scope of
`docs/spec/`.
