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
| fibonacci, fib(19) = 4181 | test (t = 8) | 256 | 0.03 s | 10 ms | 23,526 B |
| fibonacci, fib(19) = 4181 | provable-120 (t = 177, gs = 2) | 256 | 0.03 s | 20 ms | 83,654 B |
| sha256 of `"abc"` | test (t = 8) | 8,192 | 0.15 s | 10 ms | 34,526 B |
| erc20-transfer (3 accounts) | test (t = 8) | 512 | 0.03 s | 10 ms | 25,398 B |
| keccak-f1600 (one permutation) | test (t = 8) | 32,768 | 0.27 s | 10 ms | 39,806 B |
| keccak-f1600 (one permutation) | provable-120 (t = 177, gs = 2) | 32,768 | 0.27 s | 30 ms | 289,406 B |

Outputs were checked independently (fib value, SHA-256 digest `ba7816bf…`,
post-transfer balances 70/80, Keccak-f[1600] state).

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
| keccak-f1600 (one permutation) | 32,768 | 18.8 s (now 0.27 s) | 39,806 B |
| evm-erc20-transfer (embedded runtime) | 65,536 | 53.6 s | 43,646 B |

Before this change, a `sha256-merkle-path` attempt at `A = 16` was
killed by the OS for memory use, and a `keccak-f1600` attempt was
stopped by hand for the same reason.

The last workload, `radix-sort-u64`, needs `A = 17` at load time (its
static buffers, about 384 KiB, do not fit under the I/O window at
`A = 16`) and an execution budget above the default `2^20` cycles. Its
run is padded to `T = 2^22`. Two proof attempts at that size were
killed by the OS at 10.2 and 12.6 GiB resident memory.

## Bounded-memory prover and throughput optimizations at T = 2^22 (2026-10-16)

The prover was profiled per phase (`OM_TRACE=1` prints time, RSS
and the heap peak of every phase; it costs nothing when unset). Every
phase was first rewritten to work from packed bits or compact per-cycle
data (bringing `T = 2^22` to 107 s and 10.1 GiB RSS), and then
optimized across the workspace (bringing `T = 2^22` down to 20.8 s at
the `test` profile and 21.6 s at `provable-120`, a 5.1× speedup). Proof
bytes are unchanged throughout: every reference vector still reproduces,
and `T = 2^22` proofs are byte-identical before and after.

- **Field and hashing (`om-field`, `om-transcript`, `om-pcs`).** Compile-time
  `PMULL` / `PCLMULQDQ` dispatch and inlining in `K::mul`, shift-and-XOR
  `K::mul_x` / `K::mul_t` for small sum-check evaluation points, hardware
  AArch64 SHA-256 (`vsha256hq_u32` / `vsha256su0q_u32`), and zero-allocation
  slice-streaming `digest_slices` in Merkle leaves/nodes and transcript
  squeezes.
- **Bitwise witness and `G` construction (`om-circuit`, `om-mosaic`,
  `om-spartan`).** `witness_packed` packs `u64` words directly into
  `PackedBits` without string lookups or per-bit loops (cutting witness
  packing at `T = 2^22` from 16.9 s to 0.12 s), and `build_g_packed` /
  `segment_table_packed` copy aligned `u64` word slices directly (cutting
  `build G` from 7.2 s to 0.12 s).
- **PCS (`om-pcs`).** `commit_stripped` encodes one coset at a time in
  column-major layout (`encode_coset_col_major`), where each column is a
  contiguous `[K; 2^k]` slice, hashing leaves from a stack buffer without
  retaining all `2^r` cosets in memory (cutting `commit` at `T = 2^22`
  from 11.5 s / 8.5 GiB phase heap peak to 2.65 s / 4.7 GiB). During
  opening, `open_owned_repack` avoids holding duplicate level-0 tables
  during sum-check, re-encodes only queried cosets in column-major order,
  and accumulates `b_next` via split tensor basis tables in parallel
  (cutting `provable-120` opening to 3.09 s). Ring switching parallelizes
  `pack_packed` and uses 16 byte lookup tables in `a_table`.
- **Virtual Spartan (`om-spartan`).** Outer sparse rows are compiled into
  word-level bitmask and geometric `X^j` evaluators (`CompiledRow`) over
  active row pairs only, reducing quadratic evaluations to 7 `K` muls per
  pair and multiplying by `eq_row` once after the instance reduction.
  Folded sparse rows are reused directly for the inner column sum-check,
  `segment_values` reads directly from `wfold`, and `cross_prove` folds
  `S_out`/`S_in` across instances once before the column rounds (cutting
  Spartan at `T = 2^22` from 51.6 s to 7.15–7.65 s).
- **Twist/Shout (`om-memcheck`).** Witnesses are one address or word per
  cycle; `AddrComps::packed` and `inc_packed` operate on `u64` words;
  `rw_sumcheck_sparse` accumulates per-pair scalars in registers without
  per-pair heap allocations.
- **Mosaic batch (`om-mosaic`).** The first 10 rounds stream from packed
  bits of `G`, and the dense phase uses a 3-mul characteristic-2
  quadratic identity.

### radix-sort-u64 at T = 2^22 (`provable-120` and `test` profiles)

Proved and verified with the `om` CLI at both the full-security
`provable-120` profile (`t = 177`, `gs = 2`) and the `test` profile
(`t = 8`), `A = 17`, `I = O = 14`, `--max-cycles 16777216`, input of
8,192 random keys. The public instance carries the 64 KiB sorted output,
which matches an independent sort of the input.

| Quantity | `provable-120` (`t = 177, gs = 2`) | `test` (`t = 8`) | Previous `test` baseline |
|---|---|---|---|
| T (cycles, padded) | 4,194,304 | 4,194,304 | 4,194,304 |
| Prove (wall) | 21.6 s (≈ 194 k cycles/s; 187 s CPU) | 20.8 s (≈ 202 k cycles/s; 173 s CPU) | 107 s (≈ 39 k cycles/s; 794 s CPU) |
| Peak resident memory | 8.2 GiB (`/usr/bin/time -l`), 6.3 GiB heap peak | 7.7 GiB (`/usr/bin/time -l`), 6.1 GiB heap peak | 10.1 GiB (`/usr/bin/time -l`), 8.5 GiB heap peak |
| Verify | 60 ms wall, 60 ms CPU, 88 MiB resident | 20 ms wall, 30 ms CPU, 66 MiB resident | 0.42 s wall, 30 ms CPU, 67 MiB resident |
| Proof size | 603,942 B (589.8 KiB) | 60,806 B | 61,446 B |

Per phase at `T = 2^22` (`provable-120` profile, from `OM_TRACE`):

| Phase | Ends at | Phase duration | Heap peak | Previous ends at (`test`) |
|---|---|---|---|---|
| execute | 0.76 s | 0.76 s | 1.5 GiB (the trace) | 0.8 s |
| packed witness | 0.88 s | 0.12 s | 2.5 GiB | 17.7 s (16.9 s) |
| component witnesses | 1.18 s | 0.30 s | 2.8 GiB | 18.1 s (0.4 s) |
| build G | 1.29 s | 0.11 s | 3.1 GiB | 25.3 s (7.2 s) |
| commit | 3.96 s | 2.67 s | 4.7 GiB | 36.8 s (11.5 s, 8.5 GiB) |
| Virtual Spartan | 11.61 s | 7.65 s | 3.4 GiB | 88.4 s (51.6 s) |
| register Twist | 13.14 s | 1.53 s | 2.9 GiB | 91.8 s (3.4 s) |
| RAM Twist (A = 17) | 15.12 s | 1.98 s | 2.7 GiB | 96.0 s (4.2 s) |
| routers | 15.69 s | 0.57 s | 2.1 GiB | 96.7 s (0.7 s) |
| bytecode Shout | 16.00 s | 0.31 s | 2.0 GiB | 97.0 s (0.3 s) |
| Mosaic batch | 18.51 s | 2.51 s | 2.2 GiB | 99.8 s (2.8 s) |
| ring switching + Ligerito open | 21.60 s | 3.09 s | 6.3 GiB | 107.0 s (7.2 s, 7.9 GiB) |

The same build on smaller workloads (`A = 16`):

| Guest | Profile | T | Prove before | Prove now | Proof size |
|---|---|---|---|---|---|
| keccak-f1600 | test | 32,768 | 0.97 s (18.8 s / 276 s earlier) | 0.27 s | 39,806 B |
| keccak-f1600 | provable-120 | 32,768 | — | 0.27 s | 289,406 B |
| sha256 of `"abc"` | test | 8,192 | 0.27 s (61.7 s earlier) | 0.15 s | 34,526 B |
| fib(19) | provable-120 | 256 | 0.81 s | 0.03 s | 83,654 B |

## Test suites

| Suite | Count | Wall time |
|---|---|---|
| Rust workspace (`cargo test --workspace --release`) | 346 tests, 0 failures | ~15 s |
| Python reference (`unittest discover`) | 223 tests, 0 failures | 114 s |
| Guest oracle executions (Python harness) | 47 cases, all pass | ~1 min |

Every `reference/vectors/**/*.json` file (27 files) is reproduced
byte-for-byte by the corresponding Rust crate's tests, including the
end-to-end Fibonacci proof (15,630 bytes) and its verifying key.

## Proof-size model vs measured at scale

From `params.proof_size_bytes` (spec 04.7 / 13.5), `provable-120` profile:

| `n_pack` | Modelled Ligerito opening | Measured whole proof (`provable-120`) |
|---|---|---|
| 20 | 357 KiB | — |
| 22 | 415 KiB | — |
| 24 | 509 KiB | — |
| 26 (`T = 2^22`, `A = 17`) | 624 KiB (≈ 656 KiB whole proof) | **603,942 B (589.8 KiB)** |

The measured `provable-120` proof at `T = 2^22` is 603,942 B (589.8 KiB) —
about 10% smaller than the 656 KiB upper-bound model because Merkle
multi-paths deduplicate shared internal sibling hashes across the `t = 177`
queries, and below the paper's ≤ 599 KiB figure.

## Comparison with the paper, honestly

| Quantity | Paper (Magnetar) | This implementation |
|---|---|---|
| Proving throughput | ~1.45 M fib steps/s (≈ 7 M cycles/s class) | ≈ 202 k cycles/s (`test`) / ≈ 194 k cycles/s (`provable-120`) at T = 2^22 |
| Proof size | ≤ 599 KiB | **589.8 KiB (603,942 B)** measured at T = 2^22 (`provable-120`); 59.4 KiB at `test` |
| Verifier time | ~13 ms | 10–30 ms at small T; 20 ms (`test`) / 60 ms (`provable-120`) at T = 2^22 |

The prover is now ~5.1× faster than the initial bounded-memory baseline
(20.8 s vs 107 s at `T = 2^22`), though still roughly 35× behind the
paper's reported throughput. A `T = 2^22` full-security `provable-120`
proof runs in 21.6 s and fits in 8.2 GiB RSS (6.3 GiB heap peak) on a
laptop. The Python reference model stays dense throughout by design.

Other paper comparisons: security is the 120-bit provable profile by default
(no conjectured proximity gaps, no grinding), SHA-256 by default, strict
RV64I only, no zero-knowledge and no recursion — matching the v1 scope of
`docs/spec/`.
