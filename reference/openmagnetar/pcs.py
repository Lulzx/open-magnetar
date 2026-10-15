"""PCS interface (docs/spec/04-pcs.md section 4.1) with Ligerito and a bit-valued wrapper."""

from __future__ import annotations

from dataclasses import dataclass

from . import ligerito as lg
from . import ring_switch as rsw
from .field import K
from .hashing import Hasher
from .mle import mle_eval
from .sumcheck import VerificationError
from .transcript import Transcript


@dataclass
class Commitment:
    root: bytes
    n: int


class LigeritoPCS:
    def __init__(self, params: lg.LigeritoParams, hasher: Hasher | None = None):
        self.p = params
        self.h = hasher or Hasher("sha256")

    def commit(self, table: list[K], tr: Transcript):
        root, state = lg.commit(self.p, self.h, table)
        lg.absorb_setup(self.p, root, tr)
        return Commitment(root, self.p.n), state

    def absorb_commitment(self, cm: Commitment, tr: Transcript) -> None:
        lg.absorb_setup(self.p, cm.root, tr)

    def open(self, state, r: list[K], tr: Transcript):
        y = mle_eval(state.f, r)
        return y, lg.open_(self.p, self.h, state, r, y, tr)

    def verify(self, cm: Commitment, r: list[K], y: K, proof, tr: Transcript) -> None:
        if cm.n != self.p.n:
            raise VerificationError("commitment size mismatch")
        lg.verify(self.p, self.h, cm.root, r, y, proof, tr)


class BitPCS:
    """Commit to a bit vector (length 2^ell, ell >= 8): pack, commit; open via ring switching."""

    def __init__(self, params: lg.LigeritoParams, hasher: Hasher | None = None):
        self.pcs = LigeritoPCS(params, hasher)

    def commit(self, bits: list[int], tr: Transcript):
        cm, st = self.pcs.commit(rsw.pack(bits), tr)
        return cm, (st, bits)

    def open(self, state, r: list[K], tr: Transcript):
        st, bits = state
        y = mle_eval(bits, r)
        rs_proof, r_s, v = rsw.rs_prove(bits, r, y, tr)
        yp, pf = self.pcs.open(st, r_s, tr)
        assert yp == v
        return y, (rs_proof, pf)

    def verify(self, cm: Commitment, r: list[K], y: K, proof, tr: Transcript) -> None:
        rs_proof, pf = proof
        r_s, v = rsw.rs_verify(r, y, rs_proof, tr)
        self.pcs.verify(cm, r_s, v, pf, tr)
