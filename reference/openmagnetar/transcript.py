"""Fiat-Shamir transcript per docs/spec/02-transcript.md (hash chain)."""

from __future__ import annotations

import struct

from .field import K
from .hashing import Hasher

DOM_INIT = b"\x00"
DOM_ABSORB = b"\x01"
DOM_SQUEEZE = b"\x02"
VERSION_LABEL = b"openmagnetar/transcript/v1"


def u64le(n: int) -> bytes:
    if not 0 <= n < 1 << 64:
        raise ValueError("length out of u64 range")
    return struct.pack("<Q", n)


def enc(x: bytes) -> bytes:
    """Length-prefixed string: u64le(len) || x."""
    return u64le(len(x)) + x


def _check_label(label: bytes) -> None:
    if not isinstance(label, (bytes, bytearray)):
        raise TypeError("label must be bytes")
    if not label or any(c < 0x21 or c > 0x7E for c in label):
        raise ValueError("label must be non-empty printable ASCII without space")
    if len(label) > 255:
        raise ValueError("label must be at most 255 bytes (02 2.7)")


class Transcript:
    def __init__(self, protocol_label: bytes, hasher: Hasher | None = None):
        _check_label(protocol_label)
        self.hasher = hasher or Hasher("sha256")
        self.state = self.hasher.digest(
            DOM_INIT + enc(VERSION_LABEL) + enc(self.hasher.profile_id) + enc(bytes(protocol_label))
        )
        self.counter = 0

    def clone(self) -> "Transcript":
        t = object.__new__(Transcript)
        t.hasher, t.state, t.counter = self.hasher, self.state, self.counter
        return t

    # absorbing
    def absorb_bytes(self, label: bytes, data: bytes) -> None:
        _check_label(label)
        self.state = self.hasher.digest(DOM_ABSORB + self.state + enc(bytes(label)) + enc(bytes(data)))
        self.counter = 0

    def absorb_k(self, label: bytes, x: K) -> None:
        self.absorb_bytes(label, x.to_bytes())

    def absorb_ks(self, label: bytes, xs: list[K]) -> None:
        self.absorb_bytes(label, b"".join(x.to_bytes() for x in xs))

    # squeezing
    def _squeeze(self, label: bytes) -> bytes:
        _check_label(label)
        out = self.hasher.digest(DOM_SQUEEZE + self.state + u64le(self.counter) + enc(bytes(label)))
        self.counter += 1
        return out

    def challenge_k(self, label: bytes) -> K:
        return K.from_bytes(self._squeeze(label)[:16])

    def challenge_ks(self, label: bytes, n: int) -> list[K]:
        return [self.challenge_k(label) for _ in range(n)]

    def challenge_nonzero_k(self, label: bytes) -> K:
        while True:
            c = self.challenge_k(label)
            if c:
                return c

    def challenge_index(self, label: bytes, bits: int) -> int:
        if not 0 <= bits <= 64:
            raise ValueError("bits must be in 0..64")
        v = int.from_bytes(self._squeeze(label)[:8], "little")
        return v & ((1 << bits) - 1)
