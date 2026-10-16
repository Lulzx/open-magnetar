# 15. Testing and conformance

**Status:** draft · **Paper:** —

## Scope
How open-magnetar is tested: the layers, the test-vector formats under `reference/vectors/`, how Rust crates consume
them, RISC-V conformance, the negative-test catalogue, differential testing, fuzzing, and CI. Security accounting
is in 13; the calculator `reference/openmagnetar/params.py` is tested by `reference/tests/test_params.py`.

## 15.1 Resolved questions

1. **How far does the reference model go?** **[OM-choice]** The arithmetization (emulator, virtual-instruction
   expansion, witness, both R1CS relations, cross-step constraints) in full; every sub-protocol (transcript, sum-check,
   PCS, Mosaic, Spartan, Twist/Shout/one-hot, routers) as a real prover and verifier at toy sizes; the Ligerito PCS
   at `n <= 12` only. There is **no** full-size end-to-end prover in Python; the end-to-end protocol (11) is a small
   composed model (`protocol.py`, owned by the author of 11) on toy parameters. Performance is the Rust crates' job.
2. **Python and dependencies.** **[OM-choice]** Pure Python 3.12+, stdlib only (`unittest`, `hashlib`, `json`, `random`),
   for auditability (C8). Suite: `cd <repo> && python3 -m unittest discover -s reference/tests -t reference`
   (192 tests, about one minute).

## 15.2 Layers

| layer | what | where | gate |
|---|---|---|---|
| L0 unit | field, NTT, Merkle, MLE, transcript, hasher, encodings | `test_field, test_ntt, test_merkle, test_mle, test_transcript, test_hashing` | every PR |
| L1 sub-protocol | one reduction, honest prover accepted, tampered/malicious prover rejected | `test_sumcheck, test_ligerito, test_ring_switch, test_mosaic, test_spartan, test_onehot, test_shout, test_twist, test_router` | every PR |
| L2 arithmetization | emulator vs. virtual machine vs. circuit | `test_isa_cpu, test_abi, test_elf` | every PR |
| L3 end-to-end | composed prover/verifier on toy programs (11) | `test_protocol` (when present) | every PR |
| L4 conformance | riscv-tests / riscv-arch-test (15.5), vector replay by the Rust crates | `reference/run_conformance.py`, Rust CI | nightly / every PR for vectors |
| L5 accounting | soundness ledger, parameter profiles | `test_params` | every PR |

Rule: a spec section is not `stable` until its L1 tests contain, for each of its soundness-ledger rows in 13, a test that
a prover violating exactly that step is rejected (15.4).

## 15.3 Test vectors

Vectors are JSON under `reference/vectors/<section>/`, produced by `reference/gen_vectors_*.py`, replayed by
`tests/test_pcs_vectors.py`, `test_vectors_05_06.py`, `test_vectors_07_08.py` and others. Conventions (C8): `K`
elements are 32 lowercase hex characters (16 bytes little-endian, C1); small integers (indices, words) are decimal JSON numbers or
strings (64-bit words are decimal strings when they exceed 2^53); byte strings are lowercase hex; labels are ASCII.
All inputs are derived deterministically (SHA-256 in counter mode or seeded `random.Random`), so regeneration is
bit-for-bit reproducible; regeneration changing a vector is a spec change and needs a CHANGELOG line.

| dir | files | content (top-level keys) |
|---|---|---|
| `02-transcript/` | `transcript.json` | `vectors[]`: protocol label, hash profile, operation list (`absorb_*`, `challenge_*`) and the expected outputs |
| `03-sumcheck/` | `mle.json`, `sumcheck.json` | `mle`: `r, eq_table, table, mle_eval`. `sumcheck`: `vectors[]` with claim, tables, degree, label, `round_msgs`, challenges, final value |
| `04-pcs/` | `merkle.json`, `ntt.json`, `ring_switch.json`, `ligerito.json` | Merkle roots and multi-opening `auth`; `what_beta` and encode I/O; ring switching: `ell, bits, point, value, packed, s` and sum-check messages; Ligerito: params, table, point, value, proof hash |
| `05-mosaic/` | `layout.json`, `batch.json` | layout algorithm inputs and outputs (ids, sizes, offsets, suffixes); a batched claim set and the reduction transcript |
| `06-spartan/` | `next_mle.json`, `simd_spartan_bin.json`, `virtual_spartan_toy.json` | the shift-MLE evaluations of 6.6; a full BinarySpartan transcript; a toy Virtual Spartan with layout, segment claims and cross-step |
| `07-twist-shout/` | `lt.json`, `onehot.json`, `shout_d{1,2}.json`, `twist_{reg,ram}_*.json` | `LT` evaluations; one-hot instance (`instance`, `proof`, `claims`, `cube_root_of_unity_c_zero`); Shout/Twist: `params`, address/witness, claim groups, `proof` (round messages and evals), `output_claims`, `final_memory`, `final_spec` |
| `08-router/` | `R_eval_wb*.json`, `shift_wb*.json`, `store_wb*.json` | `R~` evaluations for shifts and stores; instances with `claim` (`r_o, r_j, y`), `cycles`, `params`, `proof.evals`, `output_claims` |
| `10-cpu/` | `cpu.json` | a program (`code` by byte address, `entry_pc`), `decode` samples, `rom_head`, `upc_of_pc`, `cycles`, `exit_code` |
| `09-isa/`, `11`, `12`, `14` | none yet | to be added with those sections' fixtures |

**Consumption by Rust crates.** Each crate has an integration test that (1) loads every JSON file of its sections with
`serde_json`, (2) reconstructs the inputs, (3) runs the *prover* with a transcript seeded identically and compares
every message byte-for-byte with the vector (determinism is required: no randomness in provers, challenges only from the
transcript), (4) runs the *verifier* on the vector's proof, and (5) mutates the proof (15.4) and checks rejection. The
vector directory is read through a `OPEN_MAGNETAR_VECTORS` path variable (default `reference/vectors`) so that
the Rust repo can vendor or symlink it. Any change to a vector in a PR requires the corresponding Rust change in the same
PR or a tracked issue. Missing: vectors for the end-to-end proof (after 11/12 are stable); a JSON schema file per directory
is a todo (the key lists above are normative until then).

## 15.4 Negative-test catalogue

Every reduction has tests of the form "an honest prover is accepted; each of these is rejected". Tests live next to the
section's L1 tests; the catalogue is the checklist.

| relation / step | malicious strategy (must be rejected) |
|---|---|
| transcript (02) | different label/order/profile; challenge reuse; truncated input |
| sum-check (03) | wrong claim; tampered round message `i`; wrong degree (too many/few elements); wrong final evaluation |
| Merkle/Ligerito (04) | flipped bit in: a column, an auth hash, a root, a sum-check message, the final polynomial, the claimed value, the point; unsorted/duplicate query indices; auth too short/long; committing a non-fold (`test_ligerito`); a word `delta`-far from the code |
| ring switching (04 4.5) | wrong `y`, tampered `s`, tampered sum-check, non-bit `w` |
| Mosaic (05) | a false claim among `n`; wrong layout; component of wrong size; entry not in `{0,1}`; non-zero padding |
| Spartan (06) | violated row in one instance (each of the two relations, each row family); wrong `alpha` combination; wrong `v_W`; non-zero padding columns; broken (X1), (X2) or (X3) chain; matrix entry outside `{0,1}` for a B-structure |
| one-hot (07 7.2) | row of weight 2; weight 0 (caught by row-sum); `c_h = 0` challenge (resample path) |
| Shout (07 7.4) | wrong read value; wrong address bit claim; weight 0 and 2; wrong ROM row; group claim at wrong point |
| Twist (07 7.5-7.7) | inconsistent read; wrong written value; wrong `Inc`; shared write-address violation; wrong final memory; wrong output region; `Inc` non-zero on non-store |
| routers (08) | wrong shifted output; invalid `(amt, kind)`; misaligned store; non-zero `Inc` on a non-store cycle; wrong `X` copy |
| CPU circuit (10) | single-bit corruption of every field of every segment (27 cases in `test_isa_cpu`), wrong public entry or exit, wrong ROM row, instruction fetched from the wrong micro-PC, `x0` write, out-of-range RAM, `ECALL` with `a7 != 0`, `EBREAK`, misaligned access |
| whole proof (11/12) | any single byte flip of a valid proof (fuzz, 15.7); proof for another program/input/output; wrong vk digest; proof truncated or padded |

For the ledger of 13.2 an additional property test (`tests/test_params.py`) checks that the formulas used by the calculator
agree with the sections' lemmas.

## 15.5 RISC-V conformance

**[OM-choice]** Two external suites, both for RV64I only (`rv64ui` user-mode tests; no `M/A/F/D/C`, no CSR, no
`fence` effects).

* **riscv-tests** (`isa/rv64ui-p-*`): the self-checking ELFs. The loader (`elf.py`, 14) maps them; the reference
  `riscv.Machine` runs them; the pass condition is the standard `tohost` write, translated into `ECALL a7 = 0` with `a0 = 0`
  by a one-time link-time shim (14). Tests that need unsupported features (`fence_i`, `ma_data`, misaligned accesses, CSR)
  are listed in a skip file with the reason (misaligned data is unprovable in v1, C5).
* **riscv-arch-test** (RV64I): signature-based. The signature region is declared as the program's output region (C6) and
  compared to the reference signatures. This also exercises the final-memory claim.

Execution targets: `riscv.Machine` (L2, Python), then the Rust emulator (same ELFs), then the proof path, where each test
ELF must produce a **verifying proof** with `T` padded to a power of two (the small tests make this cheap).
`reference/run_conformance.py` downloads nothing, takes either `--elf-dir <dir>` of prebuilt ELFs (with optional `--skip-file`
and `--prove`) or runs its built-in 40-instruction RV64I conformance suite across `Machine`, `VirtualMachine`, `cpu_circuit`,
and `protocol`, reporting pass/skip/fail per test.

## 15.6 Differential testing

Three independent executors of the same program must agree:

1. `riscv.Machine`: the architectural emulator (09), the oracle.
2. `bytecode.VirtualMachine`: executes the *expanded* virtual-instruction program (ROM rows, micro-PC) and checks each
   register/RAM effect against 1.
3. The circuit: `cpu_circuit.witness(trace)` followed by `cpu_circuit.check(W, public)` on the trace of 2 (and the Twist/Shout/router
   witnesses built from the same trace).

Property: for random programs (generator: random straight-line and looping RV64I from the supported set with bounded
memory, ending in `ECALL`) the three agree on registers, RAM, exit code, PC trace, and the circuit accepts. Mutation
variant: mutate one executed cycle of the trace in a way the emulator would reject (wrong result, wrong register, wrong
store) and check the circuit rejects. Seeds are fixed in CI, the nightly job uses fresh seeds and prints the failing seed.
The Rust emulator joins as a fourth executor, and the Rust and Python traces are compared cycle by cycle.

## 15.7 Fuzzing

Targets (`crates/om-verifier/tests/fuzz.rs` in Rust; Python mirror in `reference/tests/`):

1. **Proof parser** (12): arbitrary bytes into `decode_proof`: must never panic, allocate more than a bound derived
   from the vk, or loop; structured fuzzing by mutating a valid proof (bit flips, truncation, duplication, length-field
   edits). Valid-proof mutations must be rejected by `verify`, never accepted.
2. **vk parser** and **ELF loader** (14): arbitrary bytes into `decode_vk`, `decode_instance`, and `om_elf::load`.
3. **Verifier, whole**: random vk-compatible proofs; invariant: reject.
4. **Merkle multi-opening** (04 4.2): random index sets and `auth` lists, including non-ascending and duplicated indices.
5. **Transcript**: encoding round trips and domain-separation (no two distinct operation lists give the same state).

Corpus seeds: the vectors of 15.3. Crash corpora are kept in the repo.

## 15.8 CI layout

* **PR gate (minutes):** `python3 -m unittest discover` (about 1 min), Rust `cargo test` including vector replay, `clippy`,
  `fmt`, and the `params` ledger test.
* **Nightly:** differential random programs with fresh seeds, riscv-tests/arch-test, fuzzers for a fixed time, vector
  regeneration check (regenerate all vectors, `git diff --exit-code reference/vectors`).
* **Release:** full-size proof of the benchmark workloads, verification time and proof size recorded against the table of 13.5.
* Matrix: Linux and macOS; Rust stable plus the minimum supported version; hash profiles `sha256` and `sha3-256` for
  every L1 test that takes a profile.

## Requests to other sections

* **11/12:** a fixed fixture set for end-to-end vectors; a stable `Proof::from_bytes` error type for the fuzzers.
* **14:** the `tohost`-to-`ECALL` shim for riscv-tests (15.5).
* **09:** a table of RV64I instructions with the name of the test that covers each.
