# 12. Proof and key formats

**Status:** draft · **Paper:** —

## Scope
Byte-level canonical serialization of the verifying key, the public instance and the proof; versioning; length rules; the proof-size model.
Reference model: `reference/openmagnetar/proof_format.py` (`encode_vk/decode_vk`, `encode_instance/decode_instance`, `encode_proof/decode_proof`,
`pcs_free_k_count`, `ligerito_expected_bytes`, `FormatError`); tests in `reference/tests/test_protocol.py`; vector `reference/vectors/11-12/fib_ligerito_test.json`.

## 12.1 Conventions

**[OM-choice] Hand-written canonical format** (the outline's question): no serde. Every object has exactly one valid encoding, and a parser MUST reject everything else.

* Integers are little-endian: `u8`, `u32le`, `u64le`. A `K` element is its 16-byte encoding (C1); every 16-byte string is a valid element, so there is no non-canonical `K`.
* Hashes and roots are `H.digest_size` bytes (32 for `sha256`, `sha3-256`).
* **Length rule [OM-choice].** A length is transmitted only where it is *not* a function of already-known data. The proof is parsed with the knowledge of `(vk, T)`; the numbers of
  sum-check rounds, message sizes and evaluations are all functions of `(vk, T)` (11.2, 12.3). The only length prefixes are the `u32` counts of columns and of authentication hashes inside Ligerito openings
  (12.3), plus the explicit `u64le` lengths of the variable data in the vk and the instance.
* **No trailing bytes.** After the last field the input MUST be exhausted; a shorter or longer input is rejected. Parsers MUST reject truncated input.
* **Versioning.** Each object starts with a 4-byte magic and a `u8` version: `OMVK`, `OMIN`, `OMPF`. This specification defines version 1 of each. A parser rejects any other
  version. Future incompatible changes bump the version; the vk digest (11.2) covers the vk version and mode, so proofs from different versions do not transfer.
* The proof does not contain the public instance (output, exit code, `T`); the verifier takes them separately, and the proof header repeats `log2 T` as a consistency check.

## 12.2 Verifying key (`OMVK`, version 1)

| Field | Encoding |
|---|---|
| magic, version | `"OMVK"`, `u8 = 1` |
| hash profile | `u8` length, then ASCII (`sha256`, `sha3-256`, …, 02.1) |
| `A`, `I`, `O` | three `u8` |
| `MAX_CODE` | `u64le` |
| `program_digest` | 32 bytes (14.3); the parser recomputes it from the images below and rejects a mismatch |
| `entry_pc` | `u64le` (must be a key of the code image) |
| code image | `u64le` count `≤ MAX_CODE`, then `count` entries `(u64le pc, u32le word)` in strictly increasing `pc` |
| data image | `u64le` count, then entries `(u64le word_index, u64le value)` in strictly increasing index, values non-zero |
| PCS | `u8 mode` (0 Ligerito, 1 transparent mock), `u8 profile` (0 `provable-120`, 1 `test`), `u8 r`, `u32le t` (queries per level; used by the `test` profile, 0 otherwise) |

Parameters derived from the vk are not stored: the ROM, `s_1`, `s_2`, `R_sh`, `R_st`, the layout, the component list, the Mosaic layout and the Ligerito parameters `(n, ks, rs, ts, gs)`
(derived by `make_params` for `provable-120`, so `gs` need not be stored; 04 integration notes). **[OM-choice]** The vk carries the code and data images (11.2).
`vk_digest = H("openmagnetar/vk/v1" ‖ encode_vk(vk))`.

## 12.3 Public instance (`OMIN`, version 1)

`"OMIN"`, `u8 = 1`, `u64le T`, `u64le |input|`, `input`, `u64le |output|`, `output`, `u64le exit_code`. The verifier additionally checks `4 ≤ T = 2^n ≤ 2^40`, the canonical-output rule of 14.3 and `exit_code < 2^64`.

## 12.4 Proof (`OMPF`, version 1)

Fields follow the transcript order of 11.5/11.8. `n = log2 T`, `s = n − 2`, `ρ = 10`, `ν = 14`, `λ = 8`, `a_R, d_R` and `a_B, d_B` from 11.2, `ℓ` from the layout. "Sum-check `(R, D)`" is `R` rounds of `D` `K` elements
(C3: `g(t_0), g(t_2), …, g(t_D)`).

| # | Field | Encoding (counts of `K` unless noted) |
|---|---|---|
| 0 | header | `"OMPF"`, `u8 = 1`, `u8 log2 T` (must equal `n`), `root` (digest) |
| 1 | Virtual Spartan (06.7) | outer messages of `bin`: `ρ + s` messages of 3, then of `fld` the same; terminal values: 3 (`bin`) then 3 (`fld`); inner sum-check `(ν, 2)`; `v_W`; `v_i` for each of the 37 non-pad segments in layout order; cross-step sum-check `(λ + s, 2)`; `v_in, v_out` |
| 2 | `reg_bits` | 18 |
| 3 | register Twist (07.5) | `rw` `(n + 6, 3)`; `rw_evals` 5; `val` `(n, 3)`; `val_evals` 2; virtualization (`d = 2`): sum-check `(n, 3)`, evals `3d = 6`; one-hot: sum-check `(n, 4)`, evals `2(p+1)d = 12` |
| 4 | `ram_bits` (`A`), `ram_inc_wv` (1) | `A + 1` |
| 5 | RAM Twist (07.5, 07.6) | `rw` `(n + A', 3)` (`A' = a_R`); `rw_evals` 4; `val` `(n, 3)`; `val_evals` 2; `fin` `(n, 2)`; `fin_evals` 2; if `d_R > 1`: virtualization `(n, d_R + 1)`, evals `3 d_R` (read, write, final write groups); one-hot `(n, 4)`, evals `2·2·d_R` |
| 6 | shift router | sum-check `(n + 15, 4)`; evals 3 |
| 7 | store router | sum-check `(n + 9, 6)`; evals 5 |
| 8 | bytecode Shout (07.4) | `read` `(a_B, 2)`; `ra_evals` 6 (six groups, 11.7); if `d_B > 1`: virtualization `(n, d_B + 1)`, evals `d_B`; one-hot `(n, 4)`, evals `2 d_B` |
| 9 | Mosaic (05.4) | sum-check `(ℓ, 2)`; `v_G` |
| 10 | PCS | **Ligerito:** ring switching `s` (128) and sum-check `(ℓ − 7, 2)`; then the Ligerito proof: roots `L − 1` (digest each); per level `i`: sum-check `(k_i, 2)`; `u32 c_i` (number of distinct queried columns, `≤ t_i`), `c_i` columns of `2^{k_i}` `K`; `u32 h_i`, `h_i` hashes (the deduplicated Merkle multi-path of 04.2, in the order produced by `MerkleTree.open`); finally `f_L`, `2^{n_L}` `K`. **Transparent mock:** `G` as `2^ℓ/8` bytes, bit `i` = bit `i mod 8` of byte `i/8` (test only) |

**[OM-choice]** The Ligerito framing differs from 04's request (derive the path length from the query set): explicit `u32` counts keep the parser free of transcript replay. The Merkle path length is checked by `verify_multi`
(wrong count: reject). A parser rejects `c_i > t_i`.

## 12.5 Size

For the default key, with `S = 37` segments and `n = log2 T`, the number of `K` elements outside the PCS opening is exact:

    N_K(n) = 8n + 134                       (Virtual Spartan; 6(ρ+s) + 6 + 2ν + 1 + S + 2(λ+s) + 2)
           + 18                              (reg_bits)
           + (13n + 43)                      (register Twist, d = 2)
           + (A + 1)                         (ram_bits, y_0)
           + R_twist(n)                      (RAM Twist, below)
           + (4n + 63) + (6n + 59)           (routers)
           + (2a_B + 6 + 4n + [d_B > 1]((d_B + 1)n + d_B) + 2d_B)     (Shout)
           + (2ℓ + 1)                        (Mosaic)
           + (128 + 2(ℓ − 7))                (ring switching)

with the RAM Twist term `R_twist(n) = 3(n + a_R) + 4 + 3n + 2 + 2n + 2 + [d_R > 1]((d_R + 1)n + 3d_R) + 4n + 4d_R`. This is implemented as `proof_format.pcs_free_k_count` and checked byte-exactly against `encode_proof`
in `test_size_model`. The proof size is `4 + 2 + |digest| + 16·N_K + |Ligerito opening|`.

**Concrete size, `T = 2^22`, provable-120 parameters of 04.7, default `A = 20` (`d_R = 5`), a ROM of `2^16` rows (`a_B = 16`, `d_B = 4`)** (an estimate; it is not an encoding of a real proof):

* committed bits per cycle `B = 1556` (11.4), `ℓ = 33`, packed variables `n_L = 26`, schedule `ks = [5, 5, 5, 5]`, `r = 2`, `t = 177` queries per level;
* `N_K(22) = 58·22 + 491 + 4·33 + 115 = 2014` `K` elements: **31.5 KiB** outside the PCS opening (`58n + 4ℓ + 606` for these parameters);
* Ligerito opening with **one** repetition per level (our size model, `ligerito_expected_bytes`): 493 KiB, total **≈ 525 KiB**;
* with the **gap amplification `gs = 2`** that 04.7/13.5 require for the 120-bit *provable* claim: the Ligerito opening is about 1101 KiB (04.7), total **≈ 1.13 MiB**. The reference prover/verifier do not implement `gs > 1`
  (04), so no proof of this size is produced by the reference model.

**Comparison with the paper (about 600 KiB).** The one-repetition figure (≈ 525 KiB) is within 15% of the paper's number, which fits a proof that does not pay for gap amplification; the
sound provable-120 figure is about twice that. The proof is dominated by the Ligerito opening (94% at `gs = 1`); the Twist/Shout/Spartan sum-check messages together are 31.5 KiB. The size of the test proof in the vector
(`T = 32`, `ℓ = 16`, `t = 8`) is 15 630 bytes, of which 12 454 are outside the PCS opening and 3 176 are the Ligerito opening.

## Resolved questions

1. **Serialization**: hand-written canonical format, 12.1. **[OM-choice]**
2. **Lengths**: derived from `(vk, T)`, except the Ligerito counts and the vk/instance data lengths. **[OM-choice]**
3. **vk content**: parameters, code and data images, PCS profile; the digest covers all of it. **[OM-choice]**

## Requests to other sections

* **04:** none beyond the integration note (explicit counts in the Ligerito opening).
* **11:** the proof field order is that of 11.5; the claim-graph shapes (six Shout groups, `S = 37`) are baked into the shape rules of 12.4.

## Integration notes

* The Ligerito opening is serialized with `u32` counts (see 04 integration notes). `gs` is not serialized; it is a function of `(profile, r, n_L)` through `make_params` (04 asked for it in the vk; derivation makes it redundant).
