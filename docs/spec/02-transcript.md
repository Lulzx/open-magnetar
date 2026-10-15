# 02. Fiat–Shamir transcript

**Status:** draft · **Paper:** §3.4 (public-coin RoK + Fiat–Shamir)

## Scope
The transcript object, domain separation, absorbing protocol messages, and
squeezing challenges in K, as K^n vectors, and as bit strings (Merkle query
indices). Hash-function abstraction (`Hasher`).

## Specification

### 2.1 Hash profiles

A **hash profile** names the hash function `H` used by the transcript (and, per
C4, by Merkle trees in 04). The profile identifier is an ASCII string:

| profile id (absorbed bytes) | `H` | output size |
|---|---|---|
| `sha256` (default) | SHA-256 (FIPS 180-4) | 32 |
| `sha3-256` | SHA3-256 (FIPS 202) | 32 |
| `sha384` (optional, stronger PQ margin) | SHA-384 (FIPS 180-4) | 48 |

The identifier bytes are exactly the ASCII bytes shown, with no terminator, for
example `73 68 61 32 35 36` for `sha256`. An implementation MUST reject an
unknown profile. Whatever a challenge derivation needs from an output is taken
from its **first bytes** (2.5), so the profiles differ only in the state width
and in the hash. A verifying key (11, 12) records the profile; the transcript
binds it at init (2.3).

`Hasher(profile)` exposes `digest(data) -> bytes` (the output size above),
`digest_size` and `profile_id`.

### 2.2 Notation

* `u64le(n)`: the 8-byte little-endian encoding of `0 ≤ n < 2^64`.
* `enc(x) = u64le(len(x)) ‖ x` for a byte string `x`.
* `‖`: concatenation. `H`: the profile's hash.
* Domain-separation bytes: `0x00` init, `0x01` absorb, `0x02` squeeze.

### 2.3 State and initialization

**[OM-choice]** (Q1) The transcript is a **hash chain**, not a duplex sponge: a
state `S` (`digest_size` bytes) and a squeeze counter `c` (a non-negative
integer). Rationale: the same construction works for every hash profile, it is
a few lines of code, and it is cheap to verify inside the zkVM guest.

    Transcript(protocol_label):
        S ← H( 0x00 ‖ enc(b"openmagnetar/transcript/v1") ‖ enc(profile_id) ‖ enc(protocol_label) )
        c ← 0

`protocol_label` is a label (2.7) naming the protocol instance, for example
`b"openmagnetar/zkvm/v1"` for the top-level proof (11). The version string
`openmagnetar/transcript/v1` is fixed by this section; any change of the
construction MUST change it.

**[OM-choice]** (Q2) What is bound at init is only the protocol label and the
profile id. Everything else (verifying-key digest, program/bytecode digest,
trace length, public input and output, parameters) is **absorbed by 11
immediately after init, and before any prover commitment**, in the order that 11
fixes. In particular the verifying-key digest MUST be absorbed before `cm_G` or
any other commitment. Rationale: init stays a pure function of constants, and
11 is the one place where the full statement is assembled.

### 2.4 Absorbing

    absorb_bytes(label, data):
        S ← H( 0x01 ‖ S ‖ enc(label) ‖ enc(data) )
        c ← 0

* `absorb_k(label, x)` is `absorb_bytes(label, x.to_bytes())`: 16 data bytes.
* `absorb_ks(label, xs)` is `absorb_bytes(label, enc_K(xs[0]) ‖ … ‖ enc_K(xs[n−1]))`:
  `16n` data bytes. The element count is determined by the length prefix and is
  therefore bound. An empty list gives empty data.
* Integers MUST be absorbed as `u64le` through `absorb_bytes`, and commitments
  (Merkle roots) as their raw digest bytes.
* Every prover message MUST be absorbed before any challenge that depends on it
  is squeezed. Absorbing resets the squeeze counter.

Because both the label and the data are length-prefixed and every field has a
fixed or prefixed width, the encoding of `(S, label, data)` is injective.

### 2.5 Squeezing

    squeeze(label):                     # internal
        out ← H( 0x02 ‖ S ‖ u64le(c) ‖ enc(label) )
        c ← c + 1
        return out

Squeezing does not change `S`. Successive squeezes between two absorbs differ
through `c`. The label is part of the hash input, so two challenges with
different labels are independent even at the same counter.

* `challenge_k(label)`: `K.from_bytes(squeeze(label)[0:16])`. The first 16
  bytes, little-endian, per C1. Every outcome is valid and uniform.
* `challenge_ks(label, n)`: `n` successive calls `challenge_k(label)` (the
  counter distinguishes them). `n = 0` returns `[]` and squeezes nothing.
* `challenge_nonzero_k(label)` **[OM-choice]** (Q4): repeat
  `x ← challenge_k(label)` until `x ≠ 0` and return it. Each attempt consumes
  one counter value, so the procedure is deterministic and verifier and prover
  agree. The probability of a retry is `2^−128`. The same loop applies to any
  other exclusion rule (for example resampling `r` for the one-hot check in 07):
  the section defining the rule MUST say which label it uses and MUST use this
  loop (squeeze, test, re-squeeze with the next counter value) and no other.
* `challenge_index(label, bits)` for `0 ≤ bits ≤ 64`: let
  `v = int.from_bytes(squeeze(label)[0:8], "little")` and return
  `v mod 2^bits` (the low `bits` bits). This is **exactly uniform** on
  `[0, 2^bits)` because the domain is a power of two. `bits > 64` is an error,
  and for larger domains the caller draws several indices. `bits = 0` returns 0
  and still consumes one counter value. **[OM-choice]** (Q3), no rejection
  sampling is used anywhere. Domains that are not powers of two (for example a
  non-power-of-two column count) are not sampled this way. They MUST be avoided
  by the sections that define them.

Query indices for a Merkle tree are drawn with distinct counter values by
successive calls. Sampling *with replacement* is the default; a section that
needs distinct indices says so and defines the rejection loop as above.

### 2.6 Proof-of-work grinding

**[OM-choice]** (Q5) Grinding is **not** part of v1 and the default parameters
claim 120-bit provable security without it. A future parameter set MAY add it
as follows: after absorbing the last prover message the prover finds a
`u64` nonce such that, on a clone of the transcript after
`absorb_bytes(b"pow/nonce", u64le(nonce))`, `challenge_index(b"pow/check", w) = 0`.
Then the real transcript absorbs the same nonce and continues. The security
accounting is in 13.

### 2.7 Label naming rules

Labels are non-empty byte strings of printable ASCII, `0x21..0x7E` (no space,
no control characters), at most 255 bytes. Implementations MUST reject any other
label. Labels are hierarchical, with `/` as separator and lowercase
`[a-z0-9_-]` segments by convention:

    <component>/<protocol-step>/<item>

| Example | Meaning |
|---|---|
| `openmagnetar/zkvm/v1` | protocol label at init |
| `vk/digest` | verifying-key digest |
| `pcs/root` | Merkle root (commitment) |
| `spartan/outer/claim` | absorbed claim |
| `spartan/outer/round/msg`, `.../chal` | sum-check messages and challenges (03 appends `/claim`, `/params`, `/msg`, `/chal` to the label it is given) |
| `shout/onehot/r` | challenge vector |
| `pcs/query/idx` | Merkle query indices |
| `pcs/params` | Ligerito parameters `enc_params` (04 4.1, absorbed at commit) |
| `pcs/point`, `pcs/value` | opening point `r` and claimed value `y` (04 4.1) |
| `pcs/sumcheck` | base label of the per-level sum-check (04 4.4) |
| `pcs/fold` | extra fold-challenge vectors `rho^(j)`, `j = 1..g-1` (04 4.4a) |
| `pcs/final` | final polynomial `f_L` (or `F` when `gs > 1`), sent in the clear (04 4.4/4.4a) |
| `pcs/cols` | opened columns of a level, in query order (04 4.4) |
| `pcs/beta` | consistency-batching challenge(s): one `beta` for `gs = 1`, one `beta_j` per repetition for `gs > 1` (04 4.4/4.4a) |
| `rs/point`, `rs/value` | ring-switching point and claimed value (04 4.5) |
| `rs/s` | ring-switching partial evaluations `s` (04 4.5) |
| `rs/rho` | ring-switching challenge `rho` (04 4.5) |
| `rs/sumcheck` | base label of the ring-switching sum-check (04 4.5) |

Rules: (1) A label identifies the *role* of a value, never its position by number,
unless a loop index is part of the protocol, in which case the index is carried
in the data and not in the label. (2) A label used for absorbing a value of one
type MUST NOT be used for a different type. (3) The same label MAY be reused for
repeated rounds, because the chain state already separates them. (4) Each
section lists the labels it uses; 11 lists the full order. (5) Labels are
case-sensitive.

### 2.8 Test vectors

Known answers for the following script, with `protocol_label = b"om/test"`:

    absorb_bytes(b"test/bytes", b"hello")
    absorb_k(b"test/k", K(0x0123456789ABCDEF))
    absorb_ks(b"test/ks", [K(1), K.X, K.t(3)])
    c1 = challenge_k(b"test/c1");  c2 = challenge_k(b"test/c1")
    cs = challenge_ks(b"test/cs", 2)
    nz = challenge_nonzero_k(b"test/nz")
    i20 = challenge_index(b"test/idx", 20);  i64 = challenge_index(b"test/idx64", 64)

`sha256`: init state `094b8233cc2f99bca7fee328a3f2b29eb4bff8915e3eb5b3adf0bbe8206e9882`

| output | value |
|---|---|
| c1 | `4c85162be45b05c1f59f2b12a15c73dc` |
| c2 | `5733c6c44ed9f94c5a1519ac574aa4c7` |
| cs[0] | `f35bcd020b3cf51f3426741a833a144b` |
| cs[1] | `967a1c72fbdd750ccf143c4dfa6a500c` |
| nz | `37410dd286009e56ddb0b277a12a7c6b` |
| i20 | `316459` |
| i64 | `12779998978630712155` |

(K values as 32-hex of the 16-byte encoding.) `sha3-256` and `sha384` vectors
are in `reference/vectors/02-transcript/transcript.json`, which is generated
by `reference/gen_vectors_01_03.py`. `sha3-256` init state:
`f31a8620eba31624f6a84d013f212c1440a4af3158b0711b5583034ecf324d12`.

### 2.9 Reference model

`reference/openmagnetar/hashing.py` (`Hasher`) and
`reference/openmagnetar/transcript.py` (`Transcript`, plus the helpers `enc`
and `u64le`) with the signatures of C8. `Transcript.clone()` and the public
attributes `state` and `counter` exist for tests and for the grinding
procedure. Tests: `reference/tests/test_hashing.py`,
`reference/tests/test_transcript.py` (a hand-computed derivation of the chain,
determinism, framing, counter, retry loop, index range, and the JSON vectors).

## Resolved questions

1. Construction: hash chain with the byte layout of 2.3–2.5 **[OM-choice]**.
2. Init binding: protocol label and profile id only; 11 absorbs the rest right
   after, vk digest first (2.3) **[OM-choice]**.
3. Index sampling: low bits of the first 8 bytes, exact for powers of two (2.5)
   **[OM-choice]**.
4. Exclusion sampling: counter-driven re-squeeze loop (2.5) **[OM-choice]**.
5. Grinding: off in v1, optional procedure in 2.6 **[OM-choice]**.

## Requests to other sections

- 11 MUST fix the order and labels of the statement absorbed after init
  (vk digest first).
- 07 and 04 MUST name the label for their exclusion and query sampling.

## Integration notes

- 2026-10-16: added the `pcs/*` and `rs/*` labels of 04 (including `pcs/fold`
  from 04 4.4a) to the table in 2.7; previously only `pcs/root` and
  `pcs/query/idx` were listed. The labels themselves and all transcripts are
  unchanged, so existing vectors still pass.
- 2026-10-16 (Rust `om-transcript` port): the Python `_check_label` did not
  enforce the 255-byte cap of 2.7 (a 300-byte label was accepted). Fixed in
  `reference/openmagnetar/transcript.py` with a regression test
  (`test_label_rules`); no label in use exceeds 255 bytes, so transcripts and
  vectors are unchanged. The spec was already correct.
