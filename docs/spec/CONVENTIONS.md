# Cross-cutting conventions (normative)

This file fixes the decisions that more than one spec section depends on.
Every section MUST follow it. If a section needs to change a convention, it
changes this file first and records the change in the "Change log" at the
bottom. All items here are **[OM-choice]** unless noted.

## C1. Fields

- `B = GF(2)`. `K = GF(2^128) = GF(2)[X] / (X^128 + X^7 + X^2 + X + 1)`.
- A K element is identified with the 128-bit integer whose bit `i` is the
  coefficient of `X^i`. This is the plain polynomial basis; it is **not**
  GHASH's bit-reflected convention.
- Byte encoding: 16 bytes, little-endian (byte 0 holds bits 0..7). Every
  16-byte string is a valid, canonical encoding.
- B embeds in K as `0 ↦ 0`, `1 ↦ 1`.
- Packing basis (paper §4.3): `β_j = X^j` for `j = 0..127`. A group of 128
  bits `w_0..w_127` packs to the K element whose integer value has bit `j` =
  `w_j`.
- Small integers as field points: `t_k` is the K element with integer value
  `k`. For example `t_2 = X` and `t_3 = X + 1`.
- Reference implementation: `reference/openmagnetar/field.py` (class `K`).

## C2. Indexing, hypercube and MLE conventions

- A vector `v` of length `2^ℓ` is indexed by `i ∈ [0, 2^ℓ)`, identified with
  bits `(b_1, …, b_ℓ)` where `b_1` is the **least significant** bit of `i`.
  This is little-endian, as in paper §3.
- MLE variable `x_1` corresponds to `b_1` (the LSB).
- Concatenation of points: `r ∥ s` puts `r` in the low variables and `s` in
  the high variables. A *suffix* is a fixed setting of the high variables, so
  "segment with suffix `s`" means a contiguous, aligned block of indices
  `[s·2^{ℓ_i}, (s+1)·2^{ℓ_i})`.
- In characteristic 2, `eq(x, b) = Π_i (1 + x_i + b_i)`.
- Multi-dimensional tables such as `W(row j, column y)` and `ra(k, j)` are
  flattened with the **first-listed** coordinate in the **low** bits, unless a
  section explicitly says otherwise. For example, `ra(k, j)` has index
  `k + K·j`.
- **Exception, the witness matrix `W`.** Paper §4.2 writes `W̃(u, y)` with `u`
  the instance and `y` the column. Following C2's rule, the column index `y` is
  in the low bits and the instance index `u` in the high bits:
  `index = y + (m/2)·u`. So `W` is stored row-major, one SIMD instance per
  row. The `r_inst ∥ r_i` claims of Construction 2 are therefore written
  `(r_col-part, r_inst)` in variable order. Section 06 states this exactly.

## C3. Sum-check

- Variables are bound in order `x_1, x_2, …`, from low to high.
- In a round with a degree-`d` univariate `g_i`, the prover sends
  `g_i(t_0), g_i(t_2), g_i(t_3), …, g_i(t_d)`: `d` field elements, omitting
  `t_1 = 1`. The verifier derives `g_i(1) = claim + g_i(0)` (in characteristic
  2, `g(0) + g(1) = claim`), interpolates, and evaluates at the challenge.
- Each round message is absorbed into the transcript before the round
  challenge is squeezed.
- Univariate skip is OFF in v1. Section 03 MAY specify it as an optional,
  versioned extension.

## C4. Hashing and transcript

- `H` is the configured hash function: SHA-256 by default, SHA3-256 optional,
  each with a 32-byte output. The profile identifier is part of the verifying
  key and is absorbed first.
- The transcript is a hash chain. The exact byte layout is in section 02.
  Challenges in K are the first 16 bytes of a hash output, decoded per C1.
- Merkle trees use the same `H`, with domain-separated leaf and node hashing
  (section 04).

## C5. Machine model

- ISA: strict RV64I. Harvard architecture: code is public and read-only, and
  lives in the bytecode table, never in RAM.
- Registers: 32 architectural registers, indices 0–31, plus up to 32
  **virtual registers**, indices 32–63. A register index is 6 bits. `x0` reads
  as 0. This is enforced by the CPU circuit plus `M_0` (section 10).
- Each cycle reads two registers (`rs1`, `rs2`) and then writes one (`rd`).
  This is register Twist with `p = 2`. A cycle that writes nothing writes
  `x0` with a zero increment.
- RAM is **word-addressed** in 64-bit words, starting at
  `RAM_BASE = 0x8000_0000`, with `2^A` words where `A` is a verifying-key
  parameter. Byte address `addr` maps to word index
  `(addr − RAM_BASE) >> 3` and byte offset `addr & 7`. Any access outside
  `[RAM_BASE, RAM_BASE + 8·2^A)` is unprovable. Each cycle does one RAM read
  and then one RAM write (RAM Twist with `p = 1`). A cycle that does not
  access RAM reads and writes word 0 with a zero increment.
- Misaligned accesses (natural alignment violated) are unprovable in v1.
- Bit order inside a word: bit `o` of a 64-bit word is `(value >> o) & 1`.
  Byte lane `b` holds bits `8b..8b+7`, which is little-endian.

## C6. I/O and termination

- The only syscall is `ECALL` with `a7 = 0`: **HALT**, with exit code `a0`. An
  `ECALL` with any other `a7`, or any `EBREAK`, is unprovable in v1.
- **Input** is placed in RAM by `M_0`. `M_0` contains the program's data
  segments and the input region, as laid out by section 14. The verifier
  evaluates `M̃_0` itself in time linear in its number of non-zero words.
- **Output** lives in an output region that is an aligned power-of-two block
  of RAM words. It is bound by a **final-memory claim**: BinaryTwist for RAM
  outputs an evaluation of the memory state after the last cycle, restricted
  to the output subcube. The verifier compares it with the MLE of the public
  output words (section 07). The paper doesn't specify this mechanism; it is
  ours.
- After HALT, the machine executes padding cycles at a fixed `HALTED`
  micro-PC that loops on itself and has no register or RAM effect. The trace
  length `T` is a power of two.

## C7. BinaryRouter indices (shared by 08, 09, 10)

- **Shift routing index** `h = (h_lo, h_hi)`, where `h_lo` (6 bits) is the
  amount 0–63 and `h_hi` (3 bits) is the kind. `Q_sh(h, j) =
  Q_lo(h_lo, j) · Q_hi(h_hi, j)`. On a cycle without a shift, both one-hot
  fields in the bytecode row are all zero.

  | kind | name | output |
  |---|---|---|
  | 0 | SLL | `src << amt` (64-bit) |
  | 1 | SRL | `src >> amt` logical |
  | 2 | SRA | `src >> amt` arithmetic |
  | 3 | SLLW | `sext32((src << amt)[31:0])`, `amt < 32` |
  | 4 | SRLW | `sext32(src[31:0] >> amt)`, `amt < 32` |
  | 5 | SRAW | `sext32(src[31:0] >>a amt)`, `amt < 32` |
  | 6 | SEXT32 | `sext32(src[31:0])`, `amt = 0` |
  | 7 | ZEXT32 | `zext32(src[31:0])`, `amt = 0` |

  Routings with invalid amounts (`amt ≥ 32` for kinds 3–5, `amt ≠ 0` for
  kinds 6–7) map every output to zero; that is, `R_sh` has no entries for
  them. The source vector `X` is the 64 bits of the shift-source word (6-bit
  `u`). Section 10 says which word that is.
- **Store routing**: the width selector `h` is one-hot over
  `{0: SB, 1: SH, 2: SW, 3: SD}`, all zero on non-store cycles. Sources are
  `u ∈ [0, 128)`: `u < 64` is old-word bit `u`, and `u ≥ 64` is store-source
  bit `u − 64`. The offset `a ∈ B^3` is the low 3 bits of the byte address,
  and the alignment rules of C5 apply.

## C8. Reference model

- Pure Python 3.12+ using only the standard library. Package
  `reference/openmagnetar/`, tests in `reference/tests/test_*.py`.
- Run with `python3 -m unittest discover -s reference/tests -t reference`.
- Each spec section owns specific modules, listed in its "Reference model"
  subsection. A section MUST NOT edit modules owned by another section. If a
  shared module needs a change, the section notes it under "Requests to other
  sections".
- Test vectors are emitted as JSON under `reference/vectors/<section>/`, with
  field elements as 32-character lowercase hex of the little-endian bytes.
- **Shared Python API.** Sections 02 and 03 own these modules. Every other
  module codes against these exact signatures:

  ```python
  # field.py (exists): class K; K.ZERO, K.ONE, K.X, K.t(k), K.pack(bits), x.unpack(),
  #   x.to_bytes(), K.from_bytes(b), x.inv(), x.square(), random_k(rng)
  # hashing.py
  class Hasher:                        # profiles: "sha256" (default), "sha3-256"
      def __init__(self, profile: str = "sha256"): ...
      def digest(self, data: bytes) -> bytes: ...          # 32 bytes
  # transcript.py
  class Transcript:
      def __init__(self, protocol_label: bytes, hasher: Hasher | None = None): ...
      def absorb_bytes(self, label: bytes, data: bytes) -> None: ...
      def absorb_k(self, label: bytes, x: K) -> None: ...
      def absorb_ks(self, label: bytes, xs: list[K]) -> None: ...
      def challenge_k(self, label: bytes) -> K: ...
      def challenge_ks(self, label: bytes, n: int) -> list[K]: ...
      def challenge_nonzero_k(self, label: bytes) -> K: ...
      def challenge_index(self, label: bytes, bits: int) -> int: ...  # uniform in [0, 2^bits)
  # mle.py
  def eq_table(r: list[K]) -> list[K]: ...          # length 2^len(r); entry i = eq(r, bits(i)), C2 order
  def eq_eval(x: list[K], y: list[K]) -> K: ...     # prod(1 + x_i + y_i)
  def mle_eval(table: list, r: list[K]) -> K: ...   # table entries K or bits 0/1; len(table) == 2^len(r)
  def bind_low(table: list[K], r: K) -> list[K]: ...# fix x_1 = r, halving the table
  # sumcheck.py
  @dataclass
  class SumcheckProof:
      round_msgs: list[list[K]]   # per round: [g(t_0), g(t_2), ..., g(t_d)] (C3)
  def sumcheck_prove(claim: K, tables: list[list[K]], combine, degree: int,
                     transcript: Transcript, label: bytes
                     ) -> tuple[SumcheckProof, list[K], list[K]]:
      """Prove sum_{b} combine([T[b] for T in tables]) == claim.
      combine(vals: list[K]) -> K must have degree <= `degree` in each variable.
      Returns (proof, challenges r (x_1 first), [MLE of each table at r])."""
  def sumcheck_verify(claim: K, num_vars: int, degree: int, proof: SumcheckProof,
                      transcript: Transcript, label: bytes) -> tuple[list[K], K]:
      """Returns (r, expected value of the summand at r). Raises VerificationError on failure."""
  class VerificationError(Exception): ...   # defined in sumcheck.py; reuse everywhere
  ```

## Change log

- 2026-10-16: initial version.
