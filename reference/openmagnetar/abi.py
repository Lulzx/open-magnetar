"""Guest ABI: memory map, I/O encoding, program digest (spec section 14).

Word indices are RAM word indices: word w is at byte address RAM_BASE + 8*w.
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass

RAM_BASE = 0x8000_0000
CODE_BASE = 0x1000_0000          # informative: default linker placement
MASK64 = (1 << 64) - 1
DIGEST_DOMAIN = b"open-magnetar/program/v1"


class AbiError(ValueError):
    pass


@dataclass(frozen=True)
class Params:
    """Verifying-key parameters relevant to the ABI."""
    ram_log_words: int = 20       # A: RAM has 2^A words
    input_log_words: int = 12     # I: input region has 2^I words
    output_log_words: int = 8     # O: output region has 2^O words
    max_code_words: int = 1 << 20  # max number of 32-bit instructions
    hash_profile: str = "sha256"

    def validate(self) -> None:
        m = max(self.input_log_words, self.output_log_words)
        if not (1 <= self.input_log_words and 1 <= self.output_log_words):
            raise AbiError("I and O must be >= 1")
        if m + 1 > self.ram_log_words:
            raise AbiError("2^(max(I,O)+1) must not exceed 2^A")
        if self.ram_log_words > 40:
            raise AbiError("A too large")
        if self.max_code_words < 1:
            raise AbiError("max_code_words must be >= 1")


@dataclass(frozen=True)
class MemoryMap:
    """All values are RAM word indices unless named *_addr."""
    ram_words: int
    io_window_base: int      # = input_base; stack top == io_window_base
    input_base: int
    output_base: int
    input_words: int
    output_words: int
    stack_top_addr: int      # initial sp (byte address)
    input_addr: int
    output_addr: int


def memory_map(p: Params) -> MemoryMap:
    p.validate()
    m = max(p.input_log_words, p.output_log_words)
    n = 1 << p.ram_log_words
    in_base = n - (1 << (m + 1))
    out_base = in_base + (1 << m)
    return MemoryMap(
        ram_words=n, io_window_base=in_base, input_base=in_base, output_base=out_base,
        input_words=1 << p.input_log_words, output_words=1 << p.output_log_words,
        stack_top_addr=RAM_BASE + 8 * in_base,
        input_addr=RAM_BASE + 8 * in_base, output_addr=RAM_BASE + 8 * out_base,
    )


# ---------------------------------------------------------------- encoding

def encode_region(data: bytes, log_words: int) -> list[int]:
    """Canonical region encoding: [len, packed words...], zero padded to 2^log_words."""
    size = 1 << log_words
    nw = (len(data) + 7) // 8
    if 1 + nw > size:
        raise AbiError("data does not fit in region")
    words = [0] * size
    words[0] = len(data)
    for i in range(nw):
        words[1 + i] = int.from_bytes(data[8 * i:8 * i + 8].ljust(8, b"\0"), "little")
    return words


def decode_region(words: list[int], log_words: int) -> bytes:
    """Inverse of encode_region; raises AbiError unless the region is canonical."""
    size = 1 << log_words
    if len(words) != size:
        raise AbiError("wrong region size")
    n = words[0]
    nw = (n + 7) // 8
    if 1 + nw > size:
        raise AbiError("declared length exceeds region")
    data = b"".join(w.to_bytes(8, "little") for w in words[1:1 + nw])[:n]
    if encode_region(data, log_words) != list(words):
        raise AbiError("non-canonical region (non-zero padding)")
    return data


def input_words(data: bytes, p: Params) -> dict[int, int]:
    """Sparse M_0 contribution of the input: word index -> value (non-zero only)."""
    mm = memory_map(p)
    w = encode_region(data, p.input_log_words)
    return {mm.input_base + i: v for i, v in enumerate(w) if v}


def build_m0(program_ram: dict[int, int], data: bytes, p: Params) -> dict[int, int]:
    """Full initial memory M_0 = program data image + input region."""
    mm = memory_map(p)
    for w in program_ram:
        if not (0 <= w < mm.io_window_base):
            raise AbiError("program data overlaps I/O window or is outside RAM")
    m0 = dict(program_ram)
    m0.update(input_words(data, p))
    return m0


def _region(final_ram, base: int, log_words: int) -> list[int]:
    get = final_ram.get if hasattr(final_ram, "get") else (lambda i, d=0: final_ram[i])
    return [get(base + i, 0) & MASK64 for i in range(1 << log_words)]


def output_region_words(final_ram, p: Params) -> list[int]:
    mm = memory_map(p)
    return _region(final_ram, mm.output_base, p.output_log_words)


def extract_output(final_ram, p: Params) -> bytes:
    """Output bytes from final RAM (dict word->u64 or list); raises if non-canonical."""
    return decode_region(output_region_words(final_ram, p), p.output_log_words)


# -------------------------------------------------------------- verifier side

def output_region_bits(output: bytes, p: Params) -> list[int]:
    """Bit table of the output region, index = o + 64*w (bit o of word w; C5, C2)."""
    words = encode_region(output, p.output_log_words)
    return [(v >> o) & 1 for v in words for o in range(64)]


def expected_output_mle_eval(output: bytes, p: Params, r: list):
    """MLE of the expected output-region bit table at r (len O+6, x_1 = bit 0 of
    the in-word bit index, then word-index bits). mle_eval imported lazily."""
    from .mle import mle_eval
    if len(r) != p.output_log_words + 6:
        raise AbiError("point has wrong length")
    return mle_eval(output_region_bits(output, p), r)


# ------------------------------------------------------------------- digest

def program_digest(code: dict[int, int], entry_pc: int, ram_words: dict[int, int],
                   p: Params) -> bytes:
    """Hash of the canonical program image (code, entry, data image, ABI params)."""
    h = hashlib.new("sha3_256" if p.hash_profile == "sha3-256" else "sha256")
    u64 = lambda x: (x & MASK64).to_bytes(8, "little")
    h.update(DIGEST_DOMAIN)
    h.update(bytes([p.ram_log_words, p.input_log_words, p.output_log_words]))
    h.update(u64(p.max_code_words))
    h.update(u64(entry_pc))
    h.update(u64(len(code)))
    for pc in sorted(code):
        h.update(u64(pc) + code[pc].to_bytes(4, "little"))
    nz = sorted((w, v) for w, v in ram_words.items() if v)
    h.update(u64(len(nz)))
    for w, v in nz:
        h.update(u64(w) + u64(v))
    return h.digest()


@dataclass(frozen=True)
class PublicInstance:
    program_digest: bytes
    input: bytes
    output: bytes
    exit_code: int  # a0 at HALT, u64
