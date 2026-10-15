# 11. Complete protocol

**Status:** draft · **Paper:** §5.5, Construction 3, Lemma 5, Theorem 1

## Scope
Key generation, the exact statement that is bound into the transcript, prover and verifier pseudo-code for
Construction 3 with every transcript interaction in order, the claim graph, the list of committed components,
and the resolution of the requests other sections made to this one. Reference model: `reference/openmagnetar/keygen.py`
(`keygen`, `VerifyingKey`, `Derived`, `Instance`), `protocol.py` (`prove`, `prove_instance`, `verify`, `execute`),
tests `reference/tests/test_protocol.py`, vector `reference/vectors/11-12/fib_ligerito_test.json`
(`reference/gen_vectors_11_12.py`).

Notation: `T = 2^n` cycles, `n ≥ 2`; `c = 2` cycles per SIMD instance, `q = 2^s = T/4` instances, `s = n − 2`.
`A, I, O` are the RAM, input and output sizes of 14.1. `ρ = 10`, `ν = 14`, `λ = 8` (06, 10). `ℓ` is the number of variables of `G`.
All labels are byte strings per 02.7.

## 11.1 The protocol in one page

Statement: "the program of the vk, run on public input `x` (placed in RAM by `M_0`), halts after `T` virtual cycles with exit code `e`, leaving
the canonical encoding of output `y` in the output region".

1. **Commit.** The prover executes the program, builds `W` and all auxiliary witnesses, forms the bit vector `G` of all committed components (11.4) and commits to it (04).
2. **Virtual Spartan** (06) on `s_1, s_2, W` with the cross-step relation: outputs one claim per segment of `W` (direct and virtual) and two claims on `S_in, S_out`.
3. **Register Twist** (07) discharges the claims on `v1, v2, rdv`. **4. RAM Twist** (07) discharges `rw`, `ridx`, and the final memory against the public output.
5. **Routers** (08): the shift router discharges `Y`; the store router discharges the increment of the RAM Twist.
6. **Bytecode Shout** (07) discharges every claim on a ROM-owned segment, the register-index claims of step 3 and the selector claims of step 5.
7. **Mosaic** (05) batches all remaining claims on committed components into one claim on `G`; **ring switching** and **Ligerito** (04) prove it.

The structure is the paper's Construction 3; what the paper leaves open and we fixed is marked **[OM-choice]** below.

## 11.2 KeyGen

`keygen(code, entry_pc, m0_program, abi_params, pcs, pcs_profile, pcs_r, pcs_t) → vk`; `vk.derived` computes the rest.

**Verifying key content (serialized in 12.2, in this order).** `VK_VERSION`; hash profile; `A, I, O, MAX_CODE`; `program_digest` (14.3); `entry_pc`;
the code image `{pc ↦ word}`; the data image `m0_program` (non-zero words of the program's RAM image, input region excluded); PCS mode, profile, `r`, `t`.
**[OM-choice]** The vk is *program-specific and carries the program* (code and data image, `O(|program|)` bytes) rather than only a digest. Rationale: the
verifier must derive the ROM (09 9.7) and evaluate `M̃_0` (07, C6) itself, both in time linear in the program (07's request); a vk with only a
digest would need a committed ROM, which is out of scope for v1. `program_digest` is recomputed by the parser and must match.

**vk digest.** `vk_digest = H("openmagnetar/vk/v1" ‖ encode_vk(vk))` with `H` the configured hash (C4). It is absorbed first (11.3).

**Derived objects** (functions of the vk, and of `T` for the last three; every party recomputes them, none is transmitted):

| Object | Definition |
|---|---|
| ROM | `bytecode.expand(code, entry_pc).rom`, rows indexed by micro-PC (`HALTED = 0`, `TRAP = 1`), `N = |ROM|` |
| Shout shape `(a_B, d_B)` | `a_B = max(2, ⌈log2 N⌉)`, then the rule of 07.9: smallest `d | a_B` with `a_B/d ≤ 4`; if that gives `a_c = 1`, `a_B` is rounded up to a multiple of 4 (`keygen.choose_ad`) |
| RAM shape `(A, d_R)` | same rule applied to `A` (`A = 4: d = 1`; `A = 20: d = 5`; `A = 24: d = 6`) |
| `s_1`, `s_2` | `cpu_circuit.build_s1/s2` for `Params(A, 2)`, as sparse `R1CS(ρ, ν)`; both padded to `2^ρ` rows with all-zero rows (answers 10's request to 06) |
| witness layout `L` | `cpu_circuit.layout`: 37 segments (21 direct, 16 virtual), as `spartan.Segment(id = index in layout, kind, ℓ_i, β_i)` (06 6.5) |
| `R_sh`, `R_st` | `router.shift_entries(6)` (12512 entries), `router.store_entries(6)` (512 entries) (08) |
| register Twist | `(a, d, p) = (6, 2, 2)`, `n`, `ℓ_w = 6`, name `twist/reg` |
| RAM Twist | `(a, d, p) = (A, d_R, 1)`, name `twist/ram`; final-memory spec `(m, s_out) = (O, out_base >> O)` (14.1) |
| component list and ids (11.4) | per `T` |
| Mosaic layout | `mosaic.compute_layout(direct segment components + auxiliary components, ℓ_min)`; `ℓ_min = 8` for Ligerito, `0` for the transparent mock |
| Ligerito parameters | `n_L = ℓ − 7`; `make_params(n_L, profile, r)`, or for the `test` profile `schedule(n_L, final = min(6, n_L − 1))` with `t` queries per level |

**[OM-choice]** Component ids: direct segments have id = their index in the layout (0..36); the auxiliary components follow in the order of the table in 11.4.
The RAM write-address components are *aliases* of the RAM read-address components (`twist/ram/wa/i ↦ twist/ram/ra0/i`, 07.9), so they have no id of their own.

## 11.3 Statement, trace length and transcript init

**[OM-choice] `T` is per proof** (resolves the outline's Q1): it is part of the public instance, a power of two with `4 ≤ T ≤ 2^40`; the key does not depend on it; the layout, the
`Twist`/`Shout` parameters and `G` are functions of `(vk, T)`. **[OM-choice] Padding** (Q2): after `HALT` the machine runs `HALTED` cycles (09, C6) until `T`
is the least power of two (at least 4) strictly greater than the number of real cycles (`VirtualMachine.run_padded`); the last cycle is always `HALTED`.
The verifier accepts any `T` that makes the checks pass; nothing in the key bounds it.

The public instance is `(T, input, output, exit_code)` (14.3 plus `T`). Transcript:

    tr = Transcript(b"openmagnetar/zkvm/v1")                       # 02.3
    tr.absorb_bytes(b"vk/digest",   vk_digest)                     # 32 bytes, FIRST
    tr.absorb_bytes(b"stmt/T",      u64le(T))
    tr.absorb_bytes(b"stmt/input",  input)
    tr.absorb_bytes(b"stmt/output", output)
    tr.absorb_bytes(b"stmt/exit",   u64le(exit_code))

The public vectors of 06 6.6 follow from the statement: `init = cpu.init_vector(entry_upc, exit_code)`, `fin = cpu.fin_vector(exit_code)` with
`entry_upc = upc_of_pc[entry_pc]`. `M_0 = m0_program ∪ input_words(input)` (14.1). The verifier first checks that `exit_code < 2^64`, that `output` has a canonical
encoding in `2^O` words (`abi.encode_region` raises otherwise), that the input fits, and `4 ≤ T = 2^n`.

## 11.4 Committed components (the vector `G`)

All components are bit tables (05.1). `ac(a,d) = a/d`. Sizes are `log2` of the number of bits.

| # | Component (name) | id | `log2` size | Bits per cycle |
|---|---|---|---|---|
| 1 | 21 direct segments of `W`: `Bop cin nw AND T0 T1 T2 Gs shsrc x1 x2 x3 m L` (64 each), `Dw dynu` (32), `stc` (128), `fl` (16), `off` (4) | layout index | `ℓ_i + s` | 1108 |
| 2 | `S_in`, `S_out` (256 bits per *instance* each) | layout index | `8 + s` | 2 × 256/4 = 128 |
| 3 | `twist/reg/ra0/i`, `ra1/i`, `wa/i` (`i = 1..2`) | next ids | `3 + n` | `3·d·2^{6/d} = 48` |
| 4 | `twist/reg/inc` | | `6 + n` | 64 |
| 5 | `twist/ram/ra0/i` (`i = 1..d_R`) | | `A/d_R + n` | `d_R·2^{A/d_R}` |
| 6 | `twist/ram/inc` | | `6 + n` | 64 |
| 7 | `shout/bytecode/ra/i` (`i = 1..d_B`) | | `a_B/d_B + n` | `d_B·2^{a_B/d_B}` |

Total bits per cycle `B = 1236 + 48 + 64 + d_R·2^{A/d_R} + 64 + d_B·2^{a_B/d_B}`. With `A = 20` (`d_R = 5`, 80) and a ROM of `2^16` rows (`d_B = 4`, 64):
**`B = 1556`**. The 16 virtual segments are never committed (`v1 v2 rdv rw ridx Y imm kc rpc upc seq tgt rf Q_lo Q_hi st_w`: 812 bits per cycle). `G` is the
concatenation of the components in the layout of 05.2 (sorted by size, then id), `ℓ = ⌈log2 Σ 2^{size}⌉` (at least `ℓ_min`); for the default
parameters at `T = 2^22`, `ℓ = 33` (the sum is `1556·T`, 76% of `2^33`). Register Twist uses `d = 2` (07.9); `d = 1` is also valid but is not what the key fixes.

## 11.5 Prover

`prove(vk, x) → (instance, proof)` (`protocol.prove_instance`; `protocol.prove` returns the proof). v1 has no private input: the input is public (14.1); a private input
is rejected. Steps in transcript order. "Base label" is the label passed to the sub-protocol; it appends its own suffixes (listed in 11.8).

0. **Execute.** `M_0 = m0_program ∪ input_words(x)`; run the virtual machine to `HALT` plus padding, giving the trace of `T` cycles, `exit_code` (value of `a0` at `HALT`) and the final RAM, from which
   `output = abi.extract_output` (non-canonical output region: no proof). `W = cpu.witness(trace)` (one row of `NW = 8192` bits per instance).
   Auxiliary witnesses: register Twist `(reads = rs1, rs2; write = rd; value = rd_val)` with `M_0 = 0`; RAM Twist (`read = write = ridx`, value = new word) with `M_0` as above;
   shift routing tables `(shsrc, (amt, kind))`; store routing tables `(old word, store source, (width, off))` with the offset bits taken from `off` on **every** cycle; Shout address chunks of `upc`.
1. **Commit.** Build all components, `G = build_G(layout, tables)`. Absorb the statement (11.3), then `commit(G)`: Ligerito: `absorb_bytes(b"pcs/params", enc_params)`, `absorb_bytes(b"pcs/root", root)`;
   transparent mock: `absorb_bytes(b"pcs/params", b"transparent")`, `absorb_bytes(b"pcs/root", H(G))`. Send `root`.
2. **Virtual Spartan.** `spartan.prove([s_1, s_2], W, X = [[]]·q, tr, P = b"vsp", segments, cross)`, with `cross = (S_in, S_out, init, fin)`. Output: claims `(id_i, ρ_i ∥ r_inst, v_i)` for the 37
   segments in layout order, then `(S_in, r_xs, v_in)`, `(S_out, r_xs, v_out)`. All sum-check claims are determined before the sum-check starts: the outer claims are the constant `0`; the inner claim `v⋆` and the
   cross-step claim `c` are absorbed by `03`'s `…/claim` before round 1 (this answers 03's request to 11).
3. **Register Twist.** All of `v1, v2, rdv` are 64-bit segments, so they have the same point `(ρ_6 ∥ r_c)`: `r_o = ρ_6` (first 6 coordinates), `r_c` = the other `n`. Prover computes the 18 address-bit claims
   `f_{x,t} = f~_{x,t}(r_c)` (`x = rs1, rs2, rd`; `t = 0..5`: bit `t` of the register index at cycle `j`), sends them as `reg_bits` (order `x`-major). Run
   `twist_prove(reg, M_0 = 0, claims = (r_o, r_c, rv = (v_{v1}, v_{v2}), wv = v_{rdv}, bits), base = b"twist/reg")`.
4. **RAM Twist.** `rw` and `ridx` are 64-bit: point `(r_o^R ∥ r_c^R)`. Send `f_t = f~_t(r_c^R)` for `t < A` (`ram_bits`) and `y_0 = Inc~_{ram}(r_o^R ∥ r_c^R)` (`ram_inc_wv`); `absorb_k(b"twist/ram/incwv", y_0)`.
   Run `twist_prove(ram, M_0, claims = (r_o^R, r_c^R, rv = (v_{rw}), wv = v_{rw} + y_0, bits = (f, f)), base = b"twist/ram", final = (O, out_base >> O, words(output)))`.
   (`wv = rv + Inc` because one word is read and written per cycle, `wa ≡ ra`.) `inc_extra` is not used.
5. **Shift router.** Input claim: `Y` at `(r_o^Y ∥ r_c^Y)` (64-bit segment, same point as above). `shift_prove(n, wit, r_o^Y, r_c^Y, v_Y, b"router/shift")`.
   **Store router.** Input: `(r_o, r_j, y) = (r_o^R, r_c^R, y_0)`. `store_prove(n, wit, …, b"router/store")`. (Resolves 08's request: the store input is the Inc claim at RAM's Spartan point; 08 integration notes.)
6. **Bytecode Shout.** Build the table (11.7) and the six claim groups; `shout_prove(a_B, d_B, n, table, groups, b"shout/bytecode")`.
7. **Mosaic and PCS.** Collect claims in the order of 11.7, `mosaic.batch_prove(layout, claims, G)` (base labels `mos/batch`, `mos/vg`) gives `(r_G, v_G)`. Ligerito: ring switching
   `rs_prove(G, r_G, v_G)` (labels `rs/…`) then `ligerito.open_` on the packed polynomial at `r_s` (labels `pcs/…`). Transparent mock: send `G`.

The proof is `(log T, root, spartan, reg_bits, reg, ram_bits, y_0, ram, shift, store, shout, mosaic, pcs)` — exactly the transcript order; 12 serializes it.

## 11.6 Verifier

`verify(vk, instance, proof) → bool`. Every failure (a `VerificationError` or any malformed or inconsistent input) is a rejection.

0. Check the instance (11.3), `proof.log_t = n`; derive everything of 11.2 for this `T`. Compute `M_0`, `words = encode_region(output, O)`, `init`, `fin`.
1. Absorb the statement and the commitment (`root`) exactly as the prover.
2. `spartan.verify(..., s, X, proof.spartan, tr, b"vsp", segments, cross)`: checks layout validity, the outer and inner sum-checks (verifier evaluates `M~_t(r_row, r_y)` for the six matrices),
   the segment identity `v_W = Σ eq(q_i, b_i) v_i`, the cross-step sum-check. Returns the claims.
3. The three register segments must be at one point (else reject). Run `twist_verify(reg, m0 = 0, …, b"twist/reg")` with `reg_bits` from the proof.
4. The `rw` and `ridx` claims must be at one point. **Check `Σ_{t<A} eq(r_o^R, t)·f_t = v_{ridx}`** (bits `t ≥ A` of `ridx` are zero by K-row 10 of 10.5). Absorb `y_0`. Run `twist_verify(ram, m0 = M̃_0, …, final)`, where
   `M̃_0(r_k ∥ r_o)` is computed from the non-zero words of `M_0` in `O(nnz·(A + 64))`.
5. `shift_verify`, `store_verify` as in 11.5.
6. Build the same table and groups from the Spartan, Twist and router claims, and `shout_verify`. (The verifier computes the derived columns, `O(N·|field|)` each, and `mle_eval` of the table columns, `O(N)` each: linear in the ROM.)
7. `mosaic.batch_verify(layout, claims, proof.mosaic)` → `(r_G, v_G)`; ring switching and Ligerito verify `G~(r_G) = v_G` against `root`
   (transparent mock: recompute `H(G)` from the revealed `G`, check it equals `root`, and compute `G~(r_G)` directly).

## 11.7 Claim graph (normative)

Every evaluation claim, who produces it, where, who consumes it, and how it is discharged. `c64 = (ρ_6 ∥ r_c)` denotes the point of any 64-bit-wide Spartan segment: first 6 coordinates are the in-word bit index `o`,
the remaining `n` are the cycle point; a segment of width `w = 2^k` has `o = ` its first `k` coordinates and cycle point the rest (`n = ℓ_i − k + s`).

| # | Claim | Producer | Point | Consumer | How discharged |
|---|---|---|---|---|---|
| 1 | `v1~, v2~, rdv~` | Spartan (virtual segments) | `c64` (same for the three) | register Twist input `rv_0, rv_1, wv` at `(r_o, r_c)` | Twist `rw` sum-check (07.5) |
| 2 | 18 register-index bit claims `f~_{x,t}(r_c)` | prover (`reg_bits`); input of register Twist | `r_c` of #1 | Shout group 1, as read values of the 18 index columns of the ROM table | Shout read sum-check (07.4); Twist binds them to its address one-hots |
| 3 | `rw~` | Spartan (virtual) | `c64` | RAM Twist input `rv`, and `wv = rv + y_0` | Twist |
| 4 | `ridx~` | Spartan (virtual) | `c64` | check `Σ_{t<A} eq(r_o,t) f_t = v_ridx` of the `A` RAM address-bit claims (prover-sent) | deterministic check (11.6 step 4); `f_t` are bound to the committed address one-hots by Twist (sound because Twist forces `f_t` to equal them; 07 integration notes) |
| 5 | RAM address-bit claims `f~_t(r_c)` (read = write, `wa ≡ ra`) | prover (`ram_bits`) | `r_c` of #3 | RAM Twist (`bits[0] = bits[1]`) | Twist |
| 6 | `y_0 = Inc~_{ram}(r_o ∥ r_c)` | prover (`ram_inc_wv`) | `c64` | (a) `wv` of RAM Twist, (b) input claim of the store router, (c) Mosaic claim on `twist/ram/inc` | (a) Twist, (b) router sum-check (08.3), (c) Mosaic |
| 7 | final memory: `Out~(r_low ∥ r_o^f) + M̃_0(r_kf ∥ r_o^f)` over the output subcube | verifier (from public `output`, `M_0`) | fresh `r_low, r_o^f` from `twist/ram/fin/…` | RAM Twist step 5 (07.6) | Twist `fin` sum-check; its outputs: `wa~` (virtualization term at `r_kf`) and `Inc~(r_o^f ∥ s_f)` (Mosaic) |
| 8 | `Y~` | Spartan (virtual) | `c64` | shift router input `(r_o, r_j, y)` | router sum-check (08.2) |
| 9 | `shift/src` `X~(s_u ∥ s_j)` | shift router | `(s_u, s_j)` | Mosaic on direct segment `shsrc` | Mosaic |
| 10 | `shift/qlo`, `shift/qhi` | shift router | `(s_lo ∥ s_j)`, `(s_hi ∥ s_j)` | Shout group 5 (cycle point `s_j`) | Shout, through derived columns (below) |
| 11 | `store/src` `X~(s_u ∥ s_j)`, `u` has 7 bits | store router | `(s_u, s_j)` | Mosaic on direct segment `stc` | Mosaic |
| 12 | `store/q` | store router | `(s_h ∥ s_j)` | Shout group 6 | Shout |
| 13 | `store/a_b`, `b = 0,1,2` | store router | `s_j` | Mosaic on direct segment `off` at `(bits(b) ∥ s_j)` (bit-selecting point) | Mosaic |
| 14 | ROM segments `imm kc rpc rf Q_lo` | Spartan (virtual, 64-bit) | `c64` | Shout group 1 (cycle point = `r_c`, derived column per field with `ρ_6`) | Shout |
| 15 | ROM segments `upc seq tgt` (32-bit) | Spartan | `(ρ_5 ∥ r_c')`, `r_c'` = other `n` coordinates | Shout group 2 | Shout |
| 16 | `Q_hi` (8-bit) | Spartan | `(ρ_3 ∥ r_c'')` | Shout group 3 | Shout |
| 17 | `st_w` (4-bit) | Spartan | `(ρ_2 ∥ r_c''')` | Shout group 4 | Shout |
| 18 | 21 direct segment claims `(id_i, ρ_i ∥ r_inst, v_i)` | Spartan | `ρ_i ∥ r_inst` | Mosaic | Mosaic |
| 19 | `S_in`, `S_out` cross-step claims | Spartan 6.6 | `(r_k, r_u)`, `λ + s` coordinates | Mosaic (several claims on one component, 05.6) | Mosaic |
| 20 | Twist virtualization claims `(name_i, r^{(i)} ∥ s, e_i)` and one-hot claims `(name, r ∥ s, e), (name, r' ∥ s, e')` for every register/RAM address component | Twist 07.3, 07.2 | per 07 | Mosaic on `twist/…/ra·/i`, `twist/…/wa/i` (RAM `wa` ↦ `ra0` alias) | Mosaic |
| 21 | Twist Inc claims `(inc, r_o ∥ r_j)`, `(inc, r_o ∥ s_v)`, [RAM: `(inc, r_o^f ∥ s_f)`] | Twist | per 07.5, 07.6 | Mosaic on `twist/reg/inc`, `twist/ram/inc` | Mosaic |
| 22 | Shout virtualization and one-hot claims | Shout | per 07 | Mosaic on `shout/bytecode/ra/i` | Mosaic |
| 23 | `G~(r_G) = v_G` | Mosaic | `r_G ∈ K^ℓ` | ring switching → `P~(r_s) = v` → Ligerito | 04 |

**Shout table and groups [OM-choice].** The Shout table has `2^{a_B}` rows (ROM padded with zero rows) and these columns: 18 *index columns* (bit `t` of `rs1`, `rs2`, `rd`, in this order) and,
for every Spartan or router claim on a ROM-owned *bit field* `φ` of width `w = 2^k` at a point whose first `k` coordinates are `ρ`, one *derived column*
`D_{φ,ρ}(row) = Σ_o eq(ρ, o)·bit_o(φ(row))` (a `K` element per row, computed by prover and verifier from the public ROM). Its read value is the claimed value:
`Σ_k ra~(k, c)·D_{φ,ρ}(k) = Σ_o eq(ρ,o)·bit_o~-of-φ~(c) = φ̃(ρ ∥ c)`, the segment's MLE at the claim's point. So a bit-level claim on a segment becomes an ordinary
Shout read-value claim (07.4) without any packing. Rationale: Shout's columns are arbitrary `K` columns (07.4), so no extra reduction is needed. The groups, in order (a group has one cycle point; columns are listed in increasing index):

| Group | Cycle point | Columns (index columns first, then derived, in this order) |
|---|---|---|
| 1 | `r_c` of #1 | 18 index columns (claims #2) ‖ `imm, kc, rpc, rf, Q_lo` at `ρ_6` (#14) |
| 2 | `r_c'` of #15 | `upc, seq, tgt` at `ρ_5` |
| 3 | `r_c''` of #16 | `Q_hi` at `ρ_3` |
| 4 | `r_c'''` of #17 | `st_w` at `ρ_2` |
| 5 | `s_j` of #10 | `Q_lo` at `s_lo` (6 coords), `Q_hi` at `s_hi` (3 coords) |
| 6 | `s_j` of #12 | `st_w` at `s_h` (2 coords) |

No address-bit claims are passed to Shout (`bits = None`): the ROM has an identity column `upc`, and claim #15 on the `upc` segment ties the read address to the circuit's micro-PC chain.
The α_0 term of 07.4 gives the row-sum check.

**Mosaic claim order** (05.4, 05.6; fixed): (1) the 21 direct Spartan claims in layout order; (2) `S_in`, then `S_out` cross-step claims; (3) register Twist outputs in 07.5 step 9 order (virtualization, one-hot, Inc);
(4) RAM Twist outputs likewise, then the Inc claim `y_0` at `(r_o ∥ r_c)`; (5) `shift/src` on `shsrc`; (6) `store/src` on `stc`, `store/a_0..a_2` on `off`; (7) Shout outputs (virtualization, one-hot).

## 11.8 Transcript labels in order

A sub-protocol appends its own suffixes to its base label; the sum-check helper adds `/claim`, `/params` (absorbed) and `/msg`, `/chal` (03.4). `[abs]` = absorb, `[sq]` = squeeze.

| Step | Base label | Operations and suffixes |
|---|---|---|
| init | protocol label `openmagnetar/zkvm/v1` | 02.3 |
| 1 | — | `vk/digest`, `stmt/T`, `stmt/input`, `stmt/output`, `stmt/exit` [abs]; `pcs/params`, `pcs/root` [abs] |
| 2 | `vsp` | `shape`, `pub`; `tau/bin`, `tau/fld` [sq]; `outer/bin/msg`, `outer/bin/row`, `outer/fld/msg`, `outer/fld/row`, `outer/inst`, `outer/<t>/final`; `alpha`; `inner` (sum-check); `vw`; `seg` ×37; `xs/init`, `xs/fin`, `xs/tau`, `xs/gamma`, `xs/sc` (sum-check), `xs/final` (06.7) |
| 3 | `twist/reg` | `point_o`, `point_c`, `rv`, `wv`, `bits`; `alpha0`, `alpha`, `beta`; `rw` (sum-check), `rw/evals`; `val`, `val/evals`; `virt/nu`, `virt/sc`, `virt/evals`; `onehot/r`, `onehot/rho`, `onehot/lambda`, `onehot/sc`, `onehot/evals` |
| 4 | `twist/ram/incwv` then `twist/ram` | as step 3, plus `fin/r_low`, `fin/r_o`, `fin` (sum-check), `fin/evals` (after `val/evals`, before `virt`); no `incx` |
| 5 | `router/shift`, `router/store` | `point_o`, `point_c`, `y`; `sc` (sum-check); `evals` (08.1) |
| 6 | `shout/bytecode` | `ngroups`, `point`, `cols`, `rv` (per group); `alpha0`, `gamma` (per group), `beta`; `read` (sum-check); `ra_evals`; `virt/nu`, `virt/sc`, `virt/evals`; `onehot/…` (07.4) |
| 7a | `mos` | `batch/claims` [abs of the claim values], `batch/gamma` [sq]; `batch` (sum-check); `vg` [abs] |
| 7b | `rs` | `point`, `value`; `s`; `rho`; `sumcheck` (sum-check) (04.5) |
| 7c | `pcs` | `point`, `value`; per level `sumcheck`, then `final` (last) or `root`, then `query/idx` ×t, `cols`, `beta` (04.4) |

Every claim that a sum-check proves is already fixed by transcript state before it starts: Spartan's outer claims are `0`, its inner and cross-step claims are functions of absorbed values; the Twist, Shout,
router, one-hot and virtualization claims are absorbed first by the sub-protocol (07.5 step 1, 07.4 step 1, 08.1); the Mosaic claim is `Σ α_j v_j` after `mos/batch/claims`; ring switching and Ligerito absorb `(r, y)` first.
The transparent mock absorbs `H(G)` as the root and checks it when it reads `G`.

## 11.9 Soundness (summary; 13 owns the accounting)

By Lemma 5 and Theorem 1 of the paper the soundness error of the whole protocol is the sum of the errors of its steps, each at most `2^-λ` for the `provable-120` profile:
`ε = ε_vsp + ε_xs + ε_twist(reg) + ε_twist(RAM, with final) + ε_shift + ε_store + ε_shout + ε_mosaic + ε_RS + ε_Lig`, with, for sections: 06 (`(8(ρ+s) + 1 + 2ν)/|K|`, `(3(λ+s)+2)/|K|`),
07 (7.2–7.6), 08 (8.4), 05 (`(2ℓ + n − 1)/|K|`), 04. Two terms are new here and have the stated form: the RAM bit check of 11.6 step 4 is deterministic given Twist's binding (error `0`), and the derived Shout columns
are public functions of the claim points (error `0`; the claim that Shout checks is exactly the segment evaluation). The soundness of the Fiat–Shamir transform (round-by-round) is in 13.

## 11.10 Resolved questions and **[OM-choice]** summary

1. **`T`** is per proof, in the instance (11.3). **[OM-choice]**
2. **Padding** after `HALT`: `HALTED` self-loop row, no effect on registers or RAM (C6, 10.9); `T` the least power of two strictly above the real cycle count. **[OM-choice]**
3. **vk carries the program** and is bound by its digest; `vk_digest` first in the transcript (11.2, 11.3). **[OM-choice]**
4. **Derived Shout columns** turn bit-level segment claims into read-value claims (11.7). **[OM-choice]**
5. **RAM `wv = rv + y_0`** with `y_0` sent by the prover; the store router takes `y_0` at the Spartan point instead of a separate random `inc_extra` point. **[OM-choice]**
6. **RAM address bits** are bound to `ridx` by a deterministic check; `ridx` is 64 bits wide so that its point equals that of `rw` (10 integration notes). **[OM-choice]**
7. **Six Shout groups**, no address-bit claims into Shout. **[OM-choice]**
8. **Transparent mock PCS** (`pcs = "transparent"`): test-only, reveals `G`; **MUST NOT** be used for anything but tests, and a vk with it records the mode so that its proofs cannot pass under a Ligerito key (the mode is part of `vk_digest`). **[OM-choice]**

## Requests to other sections

* **12:** serialize `(log T, root, …)` in the order of 11.5; shapes are derived from `(vk, T)`.
* **13:** the accounting of 11.9; `gs > 1` in `provable-120` is now implemented (04.4a) and `tests/test_protocol.py` runs the real profile end to end.
* **15:** test-vector `11-12/fib_ligerito_test.json` and the negative tests listed under 11.11 belong in the conformance list.

## 11.11 Reference model and tests

`keygen.py`, `protocol.py` as in Scope. Tests (`test_protocol.py`): completeness for a Fibonacci program (real Ligerito, tiny `test` profile with `t = 8`, `T = 32`, `ℓ = 16`) and for a program exercising
`sb sh sw sd lb lhu lw lbu ld` and the register-amount shifts `sll srl sraw` (transparent mock, `T = 64`); a program that copies a public input into the output; rejection for wrong output, wrong exit code,
wrong `T`, wrong input, a different vk; 16 tampered proof positions; truncated and trailing bytes; cheating provers that change one RAM read value, one register value, one shift output (all produce a proof that the verifier rejects);
round-trip of vk, instance and proof; the proof-size model against the exact encoding; fast routers equal to the dense ones; replay of the vector. Default `A = 4`, `I = O = 1` (16 RAM words) to keep Python fast.
Measured (Python 3.15, one core): prove 4.5 s, verify 2 s for `T = 32` transparent; the whole file runs in about 70 s.

## Integration notes

* See the integration notes in 01, 04, 07, 08, 10, 14. Summary of the cross-section changes made while composing: `ridx` widened to 64 bits (10); store router input is `y_0` at the Spartan point instead of the `inc_extra` point (07, 08);
  fast router provers (08); `K` multiplication speed-up (01); `off` is defined on all cycles (10); output-MLE helper of 14 unused (14); Ligerito framing with explicit counts (04, 12).
* 2026-10-16 (Mosaic claim cap, 05.4 / 13.2 note 3): the powers-of-`γ` batching of Mosaic (05.4, 03.6) is limited to **at most 256 claims** for 120 bits. The Mosaic claim list of 11.7 has a fixed length that does not depend on `T`: the 21 direct Spartan claims, `S_in`, `S_out`, the register and RAM Twist outputs, the `shsrc`, `stc`, `off` claims and the Shout outputs. The reference protocol produces **68 claims** for the Fibonacci test program (counted in `tests/test_protocol.py`, `TestProvable120EndToEnd.test_mosaic_claims_within_cap`), and the ledger budget of 13.2 assumes at most 128; both are `<= 256`. `mosaic.batch_prove/batch_verify` reject more than 256 claims.
* 2026-10-16 (PCS): `provable-120` (`gs = 2`) runs through the whole protocol in the reference tests (04.4a, about 8 s for `T = 32`).
