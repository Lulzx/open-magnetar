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

The last workload, `radix-sort-u64`, needs `A = 17` at load time (its
static buffers, about 384 KiB, do not fit under the I/O window at
`A = 16`) and an execution budget above the default `2^20` cycles. Its
run is padded to `T = 2^22`. Two proof attempts at that size were
killed by the OS at 10.2 and 12.6 GiB resident memory.

## Bounded-memory prover, and the first T = 2^22 proof (2026-10-16)

The prover was then profiled per phase (`OM_TRACE=1` prints time, RSS
and the heap peak of every phase; it costs nothing when unset). At
`T = 2^15` almost every phase, scaled to `2^22`, would have needed more
than 24 GiB on its own. The previous Mosaic batch prover was also slow:
it spent 259 s of a 276 s keccak proof. Every phase was rewritten to
work from packed bits or compact per-cycle data. Proof bytes are
unchanged throughout: every reference vector still reproduces, and a
full keccak proof is byte-identical before and after.

- **Mosaic batch.** The first 10 rounds are computed straight from the
  packed bits of `G` (split-eq sums over set bits per claim region).
  Then the bound `G` and `E` tables (`2^(ell-10)` entries) are built and
  the remaining rounds run densely in place.
- **PCS.** The commit hashes columns as it serializes them. Afterwards
  only the Merkle tree is kept: the opening re-packs `f` from `G` and
  re-encodes only the queried columns. The Ligerito opening takes its
  state by value and runs the level sum-check over whole tables in
  place. Ring switching uses split-eq tables, and the opened value comes
  from its partial evaluations, not from a `2^ell` eq table.
- **Spartan.** Segment claims are read from the packed witness rows,
  without a table over `2^(log_cols + s)` points. The satisfiability
  check reuses the first outer round.
- **Twist/Shout.** Witnesses are one address or word per cycle. The
  read/write sum-check answers cell lookups from a per-address write
  log (the old range scan was close to quadratic on hot cells). The
  other sum-checks build their tables row by row after three direct
  rounds.
- **Routers.** They work from compact per-cycle witnesses (words plus
  selector bytes), with the eq factor split, and materialise only
  `T/256` positions.
- **Trace.** The execution trace (hundreds of bytes per cycle) is freed
  once the witnesses are built.
- **Verifier.** The public-input fold of the Spartan verifier visited
  `q · 2^(nu-1)` zeros; it now visits only non-zero entries. Same
  value, so no protocol change.

### radix-sort-u64 at T = 2^22

Proved and verified with the `om` CLI. Test profile (`t = 8`), `A = 17`,
`I = O = 14`, `--max-cycles 16777216`, input of 8,192 random keys. The
public instance carries the 64 KiB sorted output, which matches an
independent sort of the input.

| Quantity | Value |
|---|---|
| T (cycles, padded) | 4,194,304 |
| Prove (wall) | 107 s (≈ 39 k cycles/s; 794 s CPU on 12 cores) |
| Peak resident memory | 10.1 GiB (`/usr/bin/time -l`) |
| Verify | 0.42 s wall, 30 ms CPU, 67 MiB resident |
| Proof size | 61,446 B |

Per phase (heap peak within the phase, from `OM_TRACE`):

| Phase | Ends at | Heap peak |
|---|---|---|
| execute | 0.8 s | 1.5 GiB (the trace) |
| packed witness | 17.7 s | 2.6 GiB |
| component witnesses | 18.1 s | 2.9 GiB |
| build G | 25.3 s | 3.1 GiB |
| commit | 36.8 s | 8.5 GiB (codeword rows) |
| Virtual Spartan | 88.4 s | 3.4 GiB |
| register Twist | 91.8 s | 3.0 GiB |
| RAM Twist (A = 17) | 96.0 s | 2.7 GiB |
| routers | 96.7 s | 2.1 GiB |
| bytecode Shout | 97.0 s | 2.0 GiB |
| Mosaic batch | 99.8 s | 2.2 GiB |
| ring switching + Ligerito open | 107.0 s | 7.9 GiB |

All fifteen Table 1 workloads are now proved and verified end to end.
The two largest transients are the level-0 codeword rows during commit
and the level-0 tables during the opening. Both could be streamed
further if a smaller footprint is wanted.

The same build on smaller workloads (`A = 16`, test profile):

| Guest | T | Prove before | Prove now | Proof size |
|---|---|---|---|---|
| keccak-f1600 | 32,768 | 18.8 s (276 s just before this change) | 0.97 s | 40,158 B (byte-identical before/after) |
| sha256 of `"abc"` | 8,192 | 61.7 s | 0.27 s | 34,526 B (as recorded above) |

## Test suites

| Suite | Count | Wall time (debug) |
|---|---|---|
| Rust workspace (`cargo test --workspace`) | 343 tests, 0 failures | ~1 min |
| Python reference (`unittest discover`) | 223 tests, 0 failures | 114 s |
| Guest oracle executions (Python harness) | 47 cases, all pass | ~1 min |

Every `reference/vectors/**/*.json` file (27 files) is reproduced
byte-for-byte by the corresponding Rust crate's tests, including the
end-to-end Fibonacci proof (15,630 bytes) and its verifying key.

## Proof-size model at scale

From `params.proof_size_bytes` (spec 04.7 / 13.5), provable-120 profile:

| `n_pack` | Ligerito opening |
|---|---|
| 20 | 357 KiB |
| 22 | 415 KiB |
| 24 | 509 KiB |
| 26 (T = 2^22 machine) | 624 KiB, ≈ 656 KiB whole proof |

The paper reports at most 599 KiB for the whole proof, so the model is in the
paper's range. The only proof measured at T = 2^22 so far is at the test
profile (`t = 8`, 61,446 B). Treat the provable-120 figures as estimates
(±15%) until a provable-120 proof at that size is generated; it needs
`t = 177` queries per level and `gs = 2`, so prover memory and time grow
only modestly, but it has not been run.

## Comparison with the paper, honestly

| Quantity | Paper (Magnetar) | This implementation |
|---|---|---|
| Proving throughput | ~1.45 M fib steps/s (≈ 7 M cycles/s class) | ≈ 39 k cycles/s at T = 2^22, test profile (see above) |
| Proof size | ≤ 599 KiB | 61 KiB measured at T = 2^22 (test profile); ≈ 656 KiB modelled at provable-120 |
| Verifier time | ~13 ms | 15–52 ms at small T; 0.42 s wall (30 ms CPU) at T = 2^22 |

The prover is still more than two orders of magnitude behind the paper,
but its memory is now bounded by small constants times `T` bits, plus
transients of a few field elements per committed bit at commit and open
time. A `T = 2^22` proof fits in about 10 GiB on a laptop. The Python
reference model stays dense throughout by design.

Other paper comparisons: security is the 120-bit provable profile by default
(no conjectured proximity gaps, no grinding), SHA-256 by default, strict
RV64I only, no zero-knowledge and no recursion — matching the v1 scope of
`docs/spec/`.
