# 00. Overview

**Status:** draft · **Paper:** §2

This section is informative. It explains how the pieces fit together, collects every **[OM-choice]** of the other sections in one place, and lists where open-magnetar differs from the paper
(Setty, *Magnetar*, ePrint 2026/2423). The normative text is in the numbered sections and in [CONVENTIONS.md](CONVENTIONS.md); if this page disagrees with them, they win.

## 0.1 What the system proves

Given a RISC-V program (RV64I, no extensions), a public input and a claimed output and exit code, the prover convinces a verifier that running the program on the input halts after `T` virtual cycles
with that exit code and leaves exactly that output in the output region. The proof system is a SNARK over a **binary field** `GF(2^128)` (01) with a hash-based, post-quantum polynomial commitment
(Ligerito, 04). The machine is Harvard (public read-only code, a RAM of `2^A` 64-bit words), one instruction per *virtual cycle* except register-amount shifts (5 or 6 cycles) (09).
Everything the prover commits to is a **bit vector**, which is what makes binary fields cheap.

## 0.2 Architecture

```
 ELF (14) --load--> code image, data image                              public instance:
        |                                                                (T, input, output, exit code)
        v                                                                       |
  KeyGen (11.2) --> vk = params + program (12.2) --> vk digest ---+---------+---+
        |                                                         |         |
        |   ROM (09), s1/s2 (10), layout, R_sh/R_st (08)          v         v
        v                                          +----------------------------------+
  execute (09)  -->  trace of T cycles             |  Fiat-Shamir transcript (02)     |
        |                                          |  vk digest, T, in, out, exit ... |
        v                                          +----------------+-----------------+
  witness W (10): T/4 rows x 8192 bits                              |
  + Twist/Shout/Router tables (07, 08)                              |
        |                                                           |
        |  direct segments + one-hot comps + Inc  = bit vector G    |
        |  commit(G)  ----------------------------root------------->|
        v                                                           v
 +--------------------------------------------------------------------------------+
 |  Virtual Spartan (06): outer zero-check on s1 (B) and s2 (K) in lockstep,       |
 |  inner sum-check, split W into segments, cross-step chain S_in/S_out            |
 +----------+------------------------------+--------------------------+-----------+
   direct   |                              | virtual segment claims   |
   segments |                              v                          |
      |     |   v1,v2,rdv      rw,ridx            Y        imm kc rpc upc seq tgt rf Q_lo Q_hi st_w
      |     |       |             |               |                       |
      |     |       v             v               v                       |
      |     |  Register Twist  RAM Twist       Shift router               |
      |     |  (07, a=6,p=2)   (07, final      (08)                       |
      |     |       |           memory vs       |   \                     |
      |     |       |           public output)  |    '--- Q_lo,Q_hi ---+  |
      |     |       |             |    '-- Inc --> Store router (08)    |  |
      |     |       |             |                |  '-- Q_st ------+  |  |
      |     |       '--- reg index bits ------------------------------+--+--+
      |     |                                                          v
      |     |                                              Bytecode Shout (07)  <- ROM (public)
      |     |                                                          |
      v     v                                                          v
 +--------------------------------------------------------------------------------+
 |  MosaicPCS (05): lift every remaining claim on a component to G, batch them     |
 |  into ONE claim  G~(r_G) = v_G  (one sum-check)                                 |
 +----------------------------------------+---------------------------------------+
                                          v
              ring switching (04.5): bit claim -> packed K claim  --> Ligerito (04.4)
                                          |
                                          v
                              proof (12): ~0.5-1.1 MiB at T = 2^22
```

The same picture as a list: **commit -> Virtual Spartan -> Twist (registers, RAM) -> routers (shift, store) -> Shout (bytecode) -> Mosaic -> ring switching -> Ligerito.** The order
of the transcript is the order of the proof fields (11.5, 12.4).

## 0.3 The claim graph in one paragraph

Spartan's output is a list of evaluation claims, one per segment of the witness matrix. A *direct* segment is committed, so its claim goes straight to Mosaic. A *virtual* segment is not committed:
it is authenticated by a memory-checking argument. The register values `v1, v2, rdv` go to the register Twist, the RAM word `rw` and index `ridx` go to the RAM Twist, the shift result `Y` goes to the shift
router, and the ROM-owned fields (`imm`, `kc`, `rpc`, `upc`, `seq`, `tgt`, flags, router selectors) go to the bytecode Shout. These arguments in turn
emit claims on the one-hot address components and increments they commit to, on the router's source segments (direct), and on the ROM through more Shout claims (register indices, router selectors).
The final-memory claim ties the RAM to the public output. Every committed polynomial claim lands in Mosaic. The full table with producers, points and consumers is [11.7](11-protocol.md).

## 0.4 Sizes at a glance

| Quantity | Value |
|---|---|
| cycles per SIMD instance | 4 (10.2) |
| witness per instance | 8192 bits (`ν = 14`), 862 rows over B and 123 over K padded to `2^10` (10) |
| committed bits per cycle (default `A = 20`, ROM `2^16`) | 1556: 1108 direct + 128 state + 112 register Twist + 144 RAM Twist + 64 Shout (11.4) |
| virtual (uncommitted) bits per cycle | 812 |
| `G` at `T = 2^22` | `2^33` bits (`ℓ = 33`), packed `n = 26` |
| proof at `T = 2^22` | about 525 KiB with one proximity repetition, about 1.13 MiB with the gap amplification `gs = 2` of the 120-bit provable profile (12.5); the paper reports about 600 KiB |

## 0.5 Section map

| # | Section | One line |
|---|---|---|
| 01 | [fields](01-fields.md) | `GF(2^128)`, packing, encodings |
| 02 | [transcript](02-transcript.md) | hash-chain Fiat-Shamir |
| 03 | [sumcheck](03-sumcheck.md) | MLE, `eq`, sum-check message format |
| 04 | [pcs](04-pcs.md) | Merkle, RS code, Ligerito, ring switching, parameters |
| 05 | [mosaic](05-mosaic.md) | layout of `G`, lifting, batching |
| 06 | [spartan](06-spartan.md) | SIMD R1CS, Virtual Spartan, cross-step |
| 07 | [twist-shout](07-twist-shout.md) | one-hot check, Shout, Twist, final memory |
| 08 | [router](08-router.md) | shift and store routing |
| 09 | [isa](09-isa.md) | RV64I semantics, virtual instructions, ROM |
| 10 | [cpu-circuit](10-cpu-circuit.md) | witness layout, `s_1`, `s_2` |
| 11 | [protocol](11-protocol.md) | KeyGen, prover, verifier, claim graph |
| 12 | [proof-format](12-proof-format.md) | canonical encodings, size model |
| 13 | [security](13-security.md) | soundness accounting |
| 14 | [guest-abi](14-guest-abi.md) | ELF loading, memory map, I/O |
| 15 | [testing](15-testing.md) | conformance and test vectors |

## 0.6 Every **[OM-choice]** (decisions the paper does not dictate)

Grouped by section; each item points at the section that justifies it. Cross-cutting ones are in [CONVENTIONS.md](CONVENTIONS.md) (C1-C8).

* **Conventions.** Little-endian indexing and sum-check variable order (C2, C3); `K = GF(2)[X]/(X^128 + X^7 + X^2 + X + 1)`, plain polynomial basis, 16-byte little-endian encoding (C1); word-addressed RAM at
  `0x8000_0000` (C5); one syscall, HALT (C6); the router indices (C7).
* **[01 fields](01-fields.md).** The low-weight pentanomial modulus; no subfield tower; packing basis `β_j = X^j`; byte encoding with every string valid.
* **[02 transcript](02-transcript.md).** Hash chain, not a sponge; init binds only the protocol label and hash profile, with the statement absorbed by 11 (vk digest first); index sampling by low bits; non-zero challenges by
  re-squeeze; no grinding in v1.
* **[03 sumcheck](03-sumcheck.md).** Message `[g(0), g(t_2) … g(t_d)]` (the claim determines `g(1)`); claim and parameters absorbed before round 1; powers-of-`γ` claim batching; univariate skip off in v1 (a version-2
  option).
* **[04 pcs](04-pcs.md).** LCH additive NTT over `U_m`; Ligerito over `K` with rate 1/4, arity 4-5, a final polynomial of `2^6` entries; binary Merkle with domain-separated leaves; ring switching for the
  monomial basis; two parameter profiles (`provable-120` with gap amplification, `conjectured-100` opt-in).
* **[05 mosaic](05-mosaic.md).** Sort by `(size desc, id asc)` buddy layout; `ℓ` minimal subject to `ℓ_min`, zero tail committed; powers of one challenge for the batching; several claims on one component allowed.
* **[06 spartan](06-spartan.md).** Rectangular `(ρ, ν)`; `n_x = 0` with all public data through the cross-step relation; row-first binding; separate row challenges per relation, shared instance challenge; independent `α`
  for the batching; explicit `v_W`; segments need not cover the columns; cross-step constraints as a third relation on two whole segments with a `next` MLE.
* **[07 twist-shout](07-twist-shout.md).** Frobenius one-hot check with the resampling rule; several claim groups in one Shout instance; one read/write sum-check for all accesses with the row-sum folded in by `α_0`,
  cycle variables first; final-memory claim for the output (ours); `d` by the `a_c ≤ 4` rule (registers `d = 2`); `M_0` evaluated by the verifier.
* **[08 router](08-router.md).** `h = (amount, kind)` split; invalid routings have no entries; `R̃` by an `O(|supp|)` algorithm; uniform degree per instance; SEXT32/ZEXT32 as shift kinds; the XOR-feed trick for stores.
* **[09 isa](09-isa.md).** `FENCE.I` illegal; a load into `x0` is a NOP (the one deviation from the plain interpreter); register-amount shifts cost 6 or 5 cycles; `FENCE` is a one-cycle NOP; `ECALL` is HALT only;
  micro-PC convention with `HALTED = 0`, `TRAP = 1`.
* **[10 cpu-circuit](10-cpu-circuit.md).** `c = 2` cycles per instance; the B/K split of constraints; the zero-detect chain; `rd = 0` handled by a ROM invariant; load path in the R1CS (no third router); `A ≤ 28`; PC
  tracked as the ROM column `rpc`; `ridx` 64 bits wide (11).
* **[11 protocol](11-protocol.md).** `T` per proof; `HALTED` padding to a power of two; the vk carries the program; derived Shout columns for bit-level claims; six Shout groups; the RAM `wv = rv + Inc` with the store
  router at the Spartan point; RAM address bits bound to `ridx` by a deterministic check; the transparent test-only PCS.
* **[12 proof-format](12-proof-format.md).** Hand-written canonical format; lengths derived from `(vk, T)`; explicit counts only in Ligerito openings.
* **[14 guest-abi](14-guest-abi.md).** Rust and C toolchain conventions; `no_std` with a bump allocator; memory-mapped I/O with fixed `(I, O)` in the key; input region then output region at the top of RAM.

## 0.7 Deviations from the paper

1. **Field and basis details** the paper leaves to the implementation (01), including the packing basis `β_j = X^j` and the encoding.
2. **Fiat-Shamir transcript**, hashing and label discipline are ours (02); the paper does not specify them.
3. **Spartan:** rectangular matrices; row-first variable order; a cross-step relation on two state segments (the paper's Remark 4 says only "the next MLE") (06).
4. **Twist/Shout:** one combined read/write sum-check with the row-sum check folded in (paper: one sum-check per identity); the Frobenius one-hot check written out, with the resampling rule; multi-point
   Shout claims; the **final-memory claim** for the output, which the paper does not specify (07).
5. **Ligerito over `K` only** (no separate extension field), with an explicit level schedule and parameter profiles; the proximity-gap accounting needs `gs = 2` repetitions to reach 120 provable bits (04, 13).
6. **Routers:** `h = (amount, kind)` instead of a `√H` split; shift kinds include SEXT32/ZEXT32; loads are handled by the R1CS, not a third router (08, 10).
7. **ISA:** a load into `x0` is a NOP; `FENCE` costs a cycle; only HALT is a syscall; misaligned access is unprovable (09, C5, C6).
8. **Circuit:** 4 cycles per instance, concrete constraint families for both relations; the PC is a ROM column, not a witness word (10).
9. **Protocol composition** (11): the claim graph above, derived Shout columns instead of packed bytecode claims, `T` per proof, a program-carrying verifying key and a ROM evaluated by the verifier in linear time (a committed
   ROM would need more of 04/05 and is future work).
10. **Proof size:** about 525 KiB at one repetition and about 1.13 MiB at the repetition level required for the provable claim, against about 600 KiB in the paper (12.5).

## 0.8 Where to go next

Reading order for a new implementer: CONVENTIONS, 01-03, then 11 (the claim graph) for the map, then 06, 07, 08, 10 in that order, 05 and 04 last. The Python reference model
(`reference/openmagnetar/`, run with `python3 -m unittest discover -s reference/tests -t reference`) is executable documentation; `protocol.py` composes everything.

## Resolved questions

1. **Machine-readable claim graph.** The claim graph is a table in 11.7 and is *executable* in `protocol.py` (`_mosaic_claims`, `_Plan`, the step order of `prove_instance`/`verify_strict`). A generated table was not
   needed for the reference model; a Rust implementation SHOULD check its claim order against the vector `reference/vectors/11-12/fib_ligerito_test.json`, which fixes the complete transcript. **[OM-choice]**
