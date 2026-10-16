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
post-transfer balances 70/80).

### Further Table 1 workloads proved 2026-10-16

Eight more guests were proved and verified end to end through the `om` CLI
(test profile, `A = 16`), with outputs checked against `om run`:

| Guest | T (cycles) | Proof size |
|---|---|---|
| hot-cell-increment (100 iterations from 41) | 1,024 | 27,558 B |
| stream-copy (28 bytes) | 256 | 23,622 B |
| pointer-chase (16 nodes, 20 steps) | 1,024 | 27,590 B |
| binary-search (8 keys, 2 queries) | 512 | 25,462 B |
| varint-decode (3 values) | 512 | 25,558 B |
| lz4-decode (one match sequence) | 256 | 23,494 B |
| erc20-transfer-from (3 accounts) | 1,024 | 27,894 B |
| erc20-mixed-block (3 accounts, 2 transfers) | 512 | 25,878 B |

That made 11 of the 15 Table 1 workloads proved end to end.

### After the sparse Twist prover (2026-10-16)

The sparse `rw` prover of spec 07.10 was then implemented in the Rust
prover (`om-memcheck`), with proof bytes unchanged. Three of the four
remaining workloads then proved at `A = 16`, test profile:

| Guest | T (cycles) | Prove | Proof size |
|---|---|---|---|
| sha256-merkle-path (depth 2) | 32,768 | under 5 min (not timed) | 40,382 B |
| keccak-f1600 (one permutation) | 32,768 | 18.8 s | 39,806 B |
| evm-erc20-transfer (embedded runtime) | 65,536 | 53.6 s | 43,646 B |

Before this change, a `sha256-merkle-path` attempt at `A = 16` was
killed by the OS for memory use, and a `keccak-f1600` attempt was
stopped by hand for the same reason.

The last workload, `radix-sort-u64`, is still not proved. It needs
`A = 17` at load time, because its static buffers (about 384 KiB) do
not fit under the I/O window at `A = 16`, and an execution budget
above the default `2^20` cycles (the CLI now takes `--max-cycles`;
its sorted output is correct under `om run`). A proof attempt at
`A = 17` with a `2^24` budget ran 330 s and was killed by the OS at
10.2 GiB resident memory. At its trace length (padded to
`T = 2^22`) the bottleneck is no longer Twist: the Spartan witness
and the Mosaic commitment tables are still dense in `T`, so this
workload waits on sparse handling there, not on the prover of 07.10.
Fourteen of the fifteen Table 1 workloads are now proved end to end.

The scale of the remaining problem, from `cpu_circuit.stats`: one
instance holds 4 cycles and 8,192 witness bits, and the relations have
862 (GF(2)) and 123 (GF(2^128)) rows, padded to `2^10`. At
`T = 2^22` there are `2^20` instances, so the witness alone is
`2^20 * 8,192` bits held as bytes, and each Spartan outer table has
`2^20 * 2^10 = 2^30` field elements (16 GiB per table in `K`).
Constant factor reductions were made after the killed attempt
(in-place binding of the Spartan outer tables instead of allocating
a fresh table per round, and freeing the witness and the component
table map as soon as their consumers are done; proof bytes unchanged,
verified at test sizes). They lower the peak but do not change this
scaling, and no further attempt at this size was made on a laptop.

The Spartan outer and cross-step sum-checks were then made sparse in
the same style as Twist: the row (and column) rounds stream over
instances against sparse matrices folded by the challenges seen so
far, and only the instance rounds run densely, on tables of length
`q`. The shared sum-check prover also binds its tables in place now,
which cuts the transient peak of every sum-check including the
Mosaic batch. Proof bytes are unchanged again (all reference vectors
still reproduce byte for byte, 332 Rust tests).

The Mosaic batch step and the witness representation were then made
sparse and packed in the same spirit. The batch sum-check keeps
only suffixes whose bound `G` value is nonzero and recomputes the
`eq` side from the lifted claim points, so neither `2^ell` field
table is built. The circuit witness is generated directly in
packed form (one bit per bit, in `u64` words), the Spartan prover
reads it through a bit-row trait without expanding it, `G` is
assembled and committed in packed form, and ring switching packs
from words. Proof bytes unchanged again (335 tests). What remains
dense at `T = 2^22` is the commitment itself: the packed polynomial
has `2^(ell-7)` field entries (about `2^26` there) and the Ligerito
and ring-switching sum-checks work on tables of that size, the
Twist component tables are still held as bools inside their
witnesses, and the execution trace itself is one record per cycle.
No attempt at this size has been made since these changes, on
purpose, so `radix-sort-u64` remains unproved until the remaining
dense parts are streamed as well or a larger machine is used.

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

The verifier is in the paper's ballpark. The prover is closer than it
was, but still well behind the paper. The Twist read/write sum-check no
longer materialises dense `T · 2^a` tables: the Rust prover implements
the sparse algorithm of spec 07.10 for that step (proof bytes
unchanged), which is what made the `T = 32768` and `T = 65536`
workloads above practical at all. What remains dense is the Spartan
witness handling and the Mosaic commitment tables, both linear in `T`
with large constants, plus the Python reference model, which is dense
throughout by design. The paper's prover is sparse in those parts too.
A rayon pass over the hot loops (sum-check rounds, table construction,
Ligerito row encodes, Merkle layers) gave 4–8× (sha256 prove:
510 s → 62 s) with bit-identical proofs. Throughput is of the order
of a thousand cycles per second at the sizes measured here, against
the paper's figure in the millions.

Other paper comparisons: security is the 120-bit provable profile by default
(no conjectured proximity gaps, no grinding), SHA-256 by default, strict
RV64I only, no zero-knowledge and no recursion — matching the v1 scope of
`docs/spec/`.
