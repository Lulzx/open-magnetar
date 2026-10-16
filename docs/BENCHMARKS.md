# Benchmarks

Measured 2026-10-16 on an Apple M4 Pro (24 GiB RAM), Rust release build
(`cargo build -p om --release`, thin LTO), unless stated otherwise. These
numbers are for the implementation as it stands: correct and byte-compatible
with the Python reference model, with a bounded-memory parallel prover
(see "Side-by-side comparison with the Magnetar paper (§6) at T = 2^22" below).

Guests were built with the Homebrew LLVM toolchain (`brew install llvm lld`,
see `guest/Makefile`) and proved through the `om` CLI with
`Params(ram_log_words=16, input=14, output=14)` (spec 14 defaults; the guest
ELFs for these runs were linked with `A=16` region bases to match).

## End-to-end guests (proved and verified)

| Guest | Profile | T (cycles) | Prove | Verify | Proof size |
|---|---|---|---|---|---|
| fibonacci, fib(19) = 4181 | test (t = 8) | 256 | 0.02 s | 10 ms | 23,526 B |
| fibonacci, fib(19) = 4181 | provable-120 (t = 177, gs = 2) | 256 | 0.02 s | 20 ms | 83,654 B |
| sha256 of `"abc"` | test (t = 8) | 8,192 | 0.07 s | 10 ms | 34,526 B |
| erc20-transfer (3 accounts) | test (t = 8) | 512 | 0.02 s | 10 ms | 25,398 B |
| keccak-f1600 (one permutation) | test (t = 8) | 32,768 | 0.14 s | 10 ms | 39,806 B |
| keccak-f1600 (one permutation) | provable-120 (t = 177, gs = 2) | 32,768 | 0.14 s | 30 ms | 288,926 B |

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
| keccak-f1600 (one permutation) | 32,768 | 18.8 s (now 0.14 s) | 39,806 B |
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
data (bringing `T = 2^22` to 107 s and 10.1 GiB RSS), then optimized
across the workspace to 20.7 s, and further accelerated via multi-round
bit-table deferral and LUT-based sum-checks to **8.55 s** at the `test`
profile and **8.82 s** at `provable-120` (a **12.5× speedup** over the
107 s baseline). Proof bytes are unchanged throughout: every reference
vector still reproduces, and `T = 2^22` proofs are byte-identical before
and after.

- **Field, hashing, and sum-check primitives (`om-field`, `om-transcript`,
  `om-sumcheck`).** Compile-time `PMULL` / `PCLMULQDQ` dispatch and inlining
  in `K::mul`, shift-and-XOR `K::mul_x` / `K::mul_t` for small sum-check
  evaluation points, hardware AArch64 SHA-256 (`vsha256hq_u32` /
  `vsha256su0q_u32`), and zero-allocation slice-streaming `digest_slices` in
  Merkle leaves/nodes and transcript squeezes. `eq_table` uses L1/L2-resident
  row-chunked tensor products, `bind_low_in_place` folds in 8192-element chunks
  with contiguous `copy_within`, and degree-2 product sum-checks use the 3-mul
  characteristic-2 quadratic identity over unreduced `U256` accumulators.
- **Bitwise witness and `G` construction (`om-circuit`, `om-mosaic`,
  `om-spartan`).** `witness_packed` packs `u64` words directly into
  `PackedBits` without string lookups or per-bit loops (cutting witness
  packing at `T = 2^22` from 16.9 s to 0.13 s), and `build_g_packed` /
  `segment_table_packed` copy aligned `u64` word slices directly (cutting
  `build G` from 7.2 s to 0.09 s).
- **PCS (`om-pcs`).** `commit_stripped` encodes one coset at a time in
  column-major layout (`encode_coset_col_major`) with L2 cache-tiled bottom
  butterfly stages (`TILE_ELEMS = 2^15`), hashing leaves from a stack buffer
  without retaining all `2^r` cosets in memory (cutting `commit` at `T = 2^22`
  from 11.5 s / 8.5 GiB phase heap peak to 1.22 s / 4.6 GiB). During opening,
  `open_owned_repack` avoids holding duplicate level-0 tables during sum-check,
  re-encodes only queried cosets in column-major order, and accumulates
  `b_next` via split tensor basis tables in parallel (cutting `provable-120`
  opening + ring switching to 1.66 s). Ring switching hoists `hi[vh]`
  multiplications with zero-word skipping in `partial_evals_packed` and uses
  $\mathbb{F}_2$-linear 16-byte lookup tables per `v_hi` in `a_table` (eliminating
  all $2^{26}$ field multiplications).
- **Virtual Spartan (`om-spartan`).** Purely $\text{GF}(2)$ relations (`bin` /
  R1CS 1) pre-evaluate bit-packed `a_bits` and `b_bits` words (`FlatGf2Mat`,
  `Gf2RelCache`) once before Round 0 while checking satisfiability and
  accumulating Round 0 bitmasks, then evaluate Rounds $1\dots 9$ and the final
  bound column tables directly from those packed bits via nibble/byte subset-sum
  LUTs (`Gf2RoundLut`). Linear `C` sums (`c_sums`) are pre-folded across
  instances once before Round 0 and bound in place each round so `C` is never
  evaluated on `w[u]` in Rounds $1\dots \rho-1$. Outer sparse rows in R1CS 2
  (`fld`) use flattened `CompiledRow` word-level evaluators, and `cross_prove`
  evaluates segments via byte subset-sum LUTs (cutting Spartan at `T = 2^22`
  from 51.6 s → 9.33 s → **1.54 s**).
- **Twist/Shout (`om-memcheck`).** Witnesses are one address or word per
  cycle; `AddrComps::packed` and `inc_packed` operate on `u64` words;
  `lazy::sumcheck_prove_rows` switches from packed bits to dense tables after
  1 direct round (`DIRECT_ROUNDS = 1`) with hoisted split-`eq` outer factors;
  and `WriteLog` precomputes $\mathbb{F}_2$-linear `aval0`/`inc_val` words,
  evaluates Round 0 `aval` and `cross` in $O(1)$ without binary searches, and
  binds write groups in place after each cycle round (cutting Twist + Shout at
  `T = 2^22` from 7.9 s → 3.68 s → **2.38 s**).
- **Mosaic batch (`om-mosaic`).** Phase 1 computes `region_sums` over the 1 GiB
  packed `G` in a **single pass** before Round 0 and binds each claim's
  $2^{10}$-entry table in place across the first 10 rounds, then binds `G`
  into dense tables using word-aligned zero-skipping byte-LUTs and runs the
  remaining 23 rounds with `sumcheck_round_evals_mul2` (cutting Mosaic batch
  at `T = 2^22` from 2.8 s → 2.21 s → **0.27 s**).

### radix-sort-u64 at T = 2^22 (`provable-120` and `test` profiles)

Proved and verified with the `om` CLI at both the full-security
`provable-120` profile (`t = 177`, `gs = 2`) and the `test` profile
(`t = 8`), `A = 17`, `I = O = 14`, `--max-cycles 16777216`, input of
8,192 random keys. The public instance carries the 64 KiB sorted output,
which matches an independent sort of the input.

| Quantity | `provable-120` (`t = 177, gs = 2`) | `test` (`t = 8`) | Previous (`provable-120` / `test`) | Initial `test` baseline |
|---|---|---|---|---|
| T (cycles, padded) | 4,194,304 | 4,194,304 | 4,194,304 | 4,194,304 |
| Prove (wall) | **8.82 s** (≈ 476 k cycles/s; 66.8 s CPU) | **8.55 s** (≈ 491 k cycles/s; 66.3 s CPU) | 20.7 s / 19.9 s (189 s / 186 s CPU) | 107 s (≈ 39 k cycles/s; 794 s CPU) |
| Peak memory | 8.4 GiB footprint (5.8 GiB heap peak) | 8.3 GiB footprint (5.7 GiB heap peak) | 8.4 GiB (6.0 / 5.8 GiB heap peak) | 10.1 GiB (8.5 GiB heap peak) |
| Verify | 50 ms wall, 50 ms CPU, 47.9 MiB RSS | 10 ms wall, 20 ms CPU, 26.8 MiB RSS | 50 ms / 10 ms | 0.42 s wall, 67 MiB RSS |
| Proof size | 603,942 B (589.8 KiB) | 60,806 B | 603,942 B / 60,806 B | 61,446 B |

Per phase at `T = 2^22` (`provable-120` profile, from `OM_TRACE`):

| Phase | Ends at | Phase duration | Heap peak | Previous (`provable-120`) | Initial (`test`) |
|---|---|---|---|---|---|
| execute | 0.76 s | 0.76 s | 1.5 GiB (the trace) | 0.75 s (0.75 s) | 0.8 s (0.8 s) |
| packed witness | 0.89 s | 0.13 s | 2.5 GiB | 0.87 s (0.12 s) | 17.7 s (16.9 s) |
| component witnesses | 1.18 s | 0.29 s | 2.8 GiB | 1.16 s (0.29 s) | 18.1 s (0.4 s) |
| build G | 1.27 s | 0.09 s | 2.4 GiB | 1.24 s (0.08 s) | 25.3 s (7.2 s) |
| commit | 2.49 s | **1.22 s** | 4.6 GiB | 2.73 s (1.49 s) | 36.8 s (11.5 s, 8.5 GiB) |
| Virtual Spartan | 4.03 s | **1.54 s** | 3.2 GiB | 12.06 s (9.33 s) | 88.4 s (51.6 s) |
| register Twist | 4.82 s | **0.79 s** | 2.6 GiB | 13.52 s (1.46 s) | 91.8 s (3.4 s) |
| RAM Twist (A = 17) | 6.21 s | **1.39 s** | 2.4 GiB | 15.44 s (1.92 s) | 96.0 s (4.2 s) |
| routers | 6.63 s | 0.42 s | 1.7 GiB | 15.83 s (0.39 s) | 96.7 s (0.7 s) |
| bytecode Shout | 6.83 s | **0.20 s** | 1.7 GiB | 16.13 s (0.30 s) | 97.0 s (0.3 s) |
| Mosaic batch | 7.10 s | **0.27 s** | 1.8 GiB | 18.34 s (2.21 s) | 99.8 s (2.8 s) |
| ring switching + Ligerito open | 8.76 s | **1.66 s** | 5.8 GiB | 20.62 s (2.28 s) | 107.0 s (7.2 s, 7.9 GiB) |

The same build on smaller workloads (`A = 16`):

| Guest | Profile | T | Earlier | Previous | Prove now | Proof size |
|---|---|---|---|---|---|---|
| keccak-f1600 | test | 32,768 | 18.8 s (276 s initial) | 0.27 s | **0.14 s** | 39,806 B |
| keccak-f1600 | provable-120 | 32,768 | — | 0.27 s | **0.14 s** | 288,926 B |
| sha256 of `"abc"` | test | 8,192 | 61.7 s | 0.15 s | **0.07 s** | 34,526 B |
| fib(19) | provable-120 | 256 | 0.81 s | 0.03 s | **0.02 s** | 83,654 B |

## Test suites

For published SHA-256 values checked through guest execution, proving, and
verification, see [Public-vector validation](VALIDATION.md). That report
also records rejection checks and reproduction commands.

| Suite | Count | Wall time |
|---|---|---|
| Rust workspace (`cargo test --workspace --release`, incl. fuzzing & 4-way differential tests) | 362 tests, 0 failures | ~3 s |
| Python reference (`unittest discover`) | 227 tests, 0 failures | ~120 s |
| RV64I conformance runner (`reference/run_conformance.py --prove`) | 46 programs (all 40 RV64I instructions), 0 failures | ~6 s |
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

## Side-by-side comparison with the Magnetar paper (§6) at T = 2^22

| Metric | Magnetar Paper (§6) | `open-magnetar` (`provable-120`) | `open-magnetar` (`test`) | Gap / Status |
|---|---|---|---|---|
| **Proof size** | ≤ 599 KiB | **589.8 KiB (603,942 B)** | **59.4 KiB (60,806 B)** | **Ahead of paper** (~9 KiB smaller than the paper's 599 KiB figure) |
| **Verifier time** | ~13 ms | **50 ms** (47.9 MiB RSS) | **10 ms** (26.8 MiB RSS) | **Same order of magnitude** (~3.8× at `provable-120` due to $g_s = 2$ gap-amplification repetitions; faster at `test`) |
| **Prover throughput** | 7.2–8.7 M cycles/s (~0.5–0.6 s at $2^{22}$) | **~476k cycles/s** (8.82 s wall, 66.8 s CPU) | **~491k cycles/s** (8.55 s wall, 66.3 s CPU) | **~15× behind** (improved **12.5×** from the initial 39k cycles/s / 107 s baseline) |
| **Committed bits / cycle** | ~1,500 bits/cycle | **1,556 bits/cycle** ($A = 20$), **1,540** ($A = 17$) | **1,556 / 1,540 bits/cycle** | **Matches paper** ($\ell = 33$, $n_{\text{pack}} = 26$ at $T = 2^{22}$) |
| **Prover peak memory** | Not reported | **5.8 GiB heap / 8.4 GiB footprint** | **5.7 GiB heap / 8.3 GiB footprint** | **Fits comfortably** on a 16–24 GiB laptop |
| **120-bit RBR soundness** | Claimed 120-bit provable | **Enforced ≥ 120.0 bits** on all 40 ledger rows ($g_s = 2, t = 177$) | N/A ($t = 8$) | **Strictly stronger accounting**: includes $g_s = 2$ repetition to close the tensor-fold proximity-gap loss |

### Breakdown of Prover Wall Time at T = 2^22 (8.76 s total in `OM_TRACE=1`)

| Phase | Wall Time ($T = 2^{22}$) | Share | Previous (20.62 s) | Speedup | Notes on Remaining Gap |
|---|---:|---:|---:|---:|---|
| **Twist & Shout (`om-memcheck`)** | **2.38 s** | 27% | 3.68 s | **1.55×** | Register Twist (0.79 s), RAM Twist (1.39 s), and Bytecode Shout (0.20 s) fold dense $K = \text{GF}(2^{128})$ tables over $n = 22$ cycle variables after the initial bit-table/sparse rounds. |
| **Ligerito Open + Ring Switching (`om-pcs`)** | **1.66 s** | 19% | 2.28 s | **1.37×** | To keep peak heap under 6 GiB on a laptop, `open_owned_repack` discards the 16 GiB level-0 codeword during commit and re-encodes only queried cosets + folds on the fly, plus runs $g_s = 2$ gap-amplification repetitions per level. |
| **Execute + Witness + Routers** | **1.69 s** | 19% | 1.63 s | ~1.0× | Single-threaded RV64I interpretation + trace recording (0.76 s), witness + component packing + `build G` (0.51 s), and shift/store routers (0.42 s). |
| **Virtual Spartan (`om-spartan`)** | **1.54 s** | 18% | 9.33 s | **6.06×** | Multi-round bit-table deferral (`Gf2RelCache` + `Gf2RoundLut`) and pre-folded linear $C$ sums (`c_sums`) reduced Spartan by 6.1×; remaining time is R1CS 2 (`fld`) word-level evaluation and the $s = 20$ dense instance rounds. |
| **PCS Commit (`om-pcs`)** | **1.22 s** | 14% | 1.49 s | **1.22×** | Encodes $2^{26}$ packed $K$ elements (1 GiB) at rate $1/4$ (4 GiB codeword) via L2-tiled additive LCH NTT and hashes $2^{22}$ columns of 16 KiB each with hardware SHA-256. |
| **Mosaic Batch (`om-mosaic`)** | **0.27 s** | 3% | 2.21 s | **8.19×** | Single-pass `region_sums` + zero-skipping byte-LUT binding reduced 68-claim batching over $\ell = 33$ variables to 0.27 s. |

Other paper comparisons: security is the 120-bit provable profile by default
(no conjectured proximity gaps, no grinding), SHA-256 by default, strict
RV64I only, no zero-knowledge and no recursion — matching the v1 scope of
`docs/spec/`.
