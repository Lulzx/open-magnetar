"""Merkle trees per docs/spec/04-pcs.md section 4.2."""

from __future__ import annotations

from .hashing import Hasher
from .sumcheck import VerificationError

LEAF = b"\x00"
NODE = b"\x01"
EMPTY = b"\x02"


def hash_leaf(h: Hasher, data: bytes) -> bytes:
    return h.digest(LEAF + data)


def hash_node(h: Hasher, left: bytes, right: bytes) -> bytes:
    return h.digest(NODE + left + right)


def empty_hash(h: Hasher) -> bytes:
    return h.digest(EMPTY)


def tree_depth(num_leaves: int) -> int:
    if num_leaves < 1:
        raise ValueError("a Merkle tree needs at least one leaf")
    return (num_leaves - 1).bit_length()


class MerkleTree:
    def __init__(self, h: Hasher, leaves: list[bytes]):
        self.h = h
        self.num_leaves = len(leaves)
        depth = tree_depth(self.num_leaves)
        layer = [hash_leaf(h, x) for x in leaves]
        layer += [empty_hash(h)] * ((1 << depth) - len(layer))
        self.layers = [layer]
        while len(layer) > 1:
            layer = [hash_node(h, layer[i], layer[i + 1]) for i in range(0, len(layer), 2)]
            self.layers.append(layer)

    @property
    def root(self) -> bytes:
        return self.layers[-1][0]

    def open(self, indices: list[int]) -> list[bytes]:
        """Deduplicated multi-path. indices: strictly ascending."""
        check_indices(indices, self.num_leaves)
        auth: list[bytes] = []
        cur = list(indices)
        for lvl in range(len(self.layers) - 1):
            s = set(cur)
            for i in cur:
                if (i ^ 1) not in s:
                    auth.append(self.layers[lvl][i ^ 1])
            cur = sorted({i >> 1 for i in cur})
        return auth


def check_indices(indices: list[int], num_leaves: int) -> None:
    if not indices:
        raise VerificationError("empty index set")
    prev = -1
    for i in indices:
        if not (prev < i < num_leaves):
            raise VerificationError("indices must be strictly ascending and in range")
        prev = i


def verify_multi(h: Hasher, root: bytes, num_leaves: int, indices: list[int],
                 leaves: list[bytes], auth: list[bytes]) -> None:
    """Raises VerificationError unless `leaves` at `indices` are under `root`."""
    check_indices(indices, num_leaves)
    if len(leaves) != len(indices):
        raise VerificationError("leaf count mismatch")
    depth = tree_depth(num_leaves)
    nodes = {i: hash_leaf(h, x) for i, x in zip(indices, leaves)}
    pos = 0
    cur = list(indices)
    for _ in range(depth):
        s = set(cur)
        sib = {}
        for i in cur:
            if (i ^ 1) not in s:
                if pos >= len(auth):
                    raise VerificationError("authentication data too short")
                sib[i ^ 1] = auth[pos]
                pos += 1
        nxt = {}
        for i in cur:
            p = i >> 1
            if p in nxt:
                continue
            l, r = (i & ~1), (i | 1)
            lv = nodes[l] if l in nodes else sib[l]
            rv = nodes[r] if r in nodes else sib[r]
            nxt[p] = hash_node(h, lv, rv)
        nodes = nxt
        cur = sorted(nodes)
    if pos != len(auth):
        raise VerificationError("authentication data too long")
    if nodes.get(0) != root:
        raise VerificationError("Merkle root mismatch")
