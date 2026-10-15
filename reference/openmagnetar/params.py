"""Soundness calculator: the ledger of docs/spec/13-security.md.

Every row is a reduction of the protocol. Errors of field-sized steps are kept as
integer numerators over |K| = 2^128 (`rbr_num` = worst single round, `tot_num` = whole
reduction). PCS rows whose error is not of the form c/|K| carry `bits` directly.
`rbr_bits` is the quantity the paper calls "per-round soundness" (13.2).
"""

from __future__ import annotations

import math
from dataclasses import dataclass

from . import ligerito as lg

FIELD_BITS = 128
TARGET = 120
QUERY_BUDGET_LOG2 = 64          # random-oracle queries assumed for the hash row (13.7)
ELL_OFFSET = 11                 # log2(committed bits per cycle ~ 1572) rounded up; see 13.3


@dataclass(frozen=True)
class Machine:
    log_t: int                  # T = 2^log_t cycles
    c: int = 2                  # log2 cycles per instance (10.2)
    rho: int = 10               # row variables (10.2)
    nu: int = 14                # column variables (10.2)
    lam: int = 8                # state segment log size (10.9)
    reg_a: int = 6              # register file 2^6, d = 2
    reg_d: int = 2
    reg_p: int = 2
    ram_a: int = 24             # RAM words 2^A, d = 6
    ram_d: int = 6
    out_m: int = 10             # output region log size (7.6)
    rom_a: int = 16             # bytecode rows 2^16, d = 4
    rom_d: int = 4
    rom_groups: int = 3
    mosaic_claims: int = 128    # upper bound on the number of Mosaic claims (5.7); must stay <= 256
    ell_offset: int = ELL_OFFSET

    @property
    def s(self) -> int:
        return self.log_t - self.c

    @property
    def ell(self) -> int:       # log2 size of the Mosaic polynomial G (estimate)
        return self.log_t + self.ell_offset

    @property
    def n_pack(self) -> int:    # variables of the packed polynomial
        return self.ell - 7


@dataclass(frozen=True)
class Row:
    step: str
    section: str
    formula: str
    rbr_num: float | None = None     # worst round, numerator over |K|
    tot_num: float | None = None     # whole reduction, numerator over |K|
    bits_direct: float | None = None # for non-field rows (queries, gap^m, hash)
    provable: bool = True

    @property
    def rbr_bits(self) -> float:
        if self.bits_direct is not None:
            return self.bits_direct
        return math.inf if not self.rbr_num else FIELD_BITS - math.log2(self.rbr_num)

    @property
    def tot_bits(self) -> float:
        if self.bits_direct is not None:
            return self.bits_direct
        return math.inf if not self.tot_num else FIELD_BITS - math.log2(self.tot_num)


def _onehot(m: Machine, tag: str, sec: str, n: int, a_c: int) -> Row:
    return Row(f"{tag}: one-hot (Delta*)", sec, "4n sum-check + (n + 5a_c + 1) polynomial",
               rbr_num=max(4, n + 5 * a_c + 1), tot_num=5 * n + 5 * a_c + 1)


def _virt(tag: str, d: int, n: int) -> list[Row]:
    if d == 1:
        return []
    return [Row(f"{tag}: address virtualization", "07 7.3", "(d+1)n + 1",
                rbr_num=max(d + 1, 1), tot_num=(d + 1) * n + 1)]


def field_rows(m: Machine) -> list[Row]:
    n, s, rho, nu, lam = m.log_t, m.s, m.rho, m.nu, m.lam
    R: list[Row] = []
    # ---- Virtual Spartan (06 6.3, 6.5), T = 2 relations in lockstep
    R.append(Row("Spartan outer: tau (both relations)", "06 6.3", "2(rho+s)",
                 rbr_num=rho + s, tot_num=2 * (rho + s)))
    R.append(Row("Spartan outer: sum-check, lockstep bin+fld", "06 6.3", "2*3*(rho+s); shared instance rounds 6 per round",
                 rbr_num=6, tot_num=6 * (rho + s)))
    R.append(Row("Spartan: alpha batching of 6 terminal values", "06 6.3", "1", rbr_num=1, tot_num=1))
    R.append(Row("Spartan inner sum-check (single, both relations)", "06 6.3", "2 nu", rbr_num=2, tot_num=2 * nu))
    R.append(Row("Segment split (identity 6.2)", "06 6.5", "0 (exact)", rbr_num=0, tot_num=0))
    R.append(Row("Cross-step (X1)-(X3)", "06 6.6", "3(lam+s)+2",
                 rbr_num=(lam + s) + 2, tot_num=3 * (lam + s) + 2))
    # ---- Shout bytecode (07 7.4)
    ca = m.rom_a // m.rom_d
    R.append(Row("Shout bytecode: read sum-check + alpha/gamma/beta batching", "07 7.4", "2a + 2",
                 rbr_num=2, tot_num=2 * m.rom_a + 2))
    R += _virt("Shout bytecode", m.rom_d, n)
    R.append(_onehot(m, "Shout bytecode", "07 7.2", n, ca))
    # ---- Twist registers and RAM (07 7.5, 7.6, 7.7)
    for tag, a, d, p, fin in (("Twist reg", m.reg_a, m.reg_d, m.reg_p, False),
                              ("Twist RAM", m.ram_a, m.ram_d, 1, True)):
        R.append(Row(f"{tag}: read/write sum-check + (alpha,beta) batching", "07 7.5",
                     "3(n+a) + 2", rbr_num=3, tot_num=3 * (n + a) + 2))
        R.append(Row(f"{tag}: Val evaluation (LT)", "07 7.5", "3n", rbr_num=3, tot_num=3 * n))
        if fin:
            R.append(Row(f"{tag}: final-memory sum-check", "07 7.6", "2n + m + ell_word",
                         rbr_num=max(2, m.out_m + 6), tot_num=2 * n + m.out_m + 6))
        R += _virt(tag, d, n)
        R.append(_onehot(m, tag, "07 7.2", n, a // d))
    R.append(Row("Twist RAM: Inc at random point (inc_extra)", "07 7.7", "0 (exact)", rbr_num=0, tot_num=0))
    # ---- Router (08)
    R.append(Row("Router shift", "08 8.2", "4(n+15)", rbr_num=4, tot_num=4 * (n + 15)))
    R.append(Row("Router store", "08 8.3", "6(n+9)", rbr_num=6, tot_num=6 * (n + 9)))
    # ---- Mosaic batching (05 5.7) and ring switching (04 4.5)
    R.append(Row("Mosaic batching + lifting sum-check", "05 5.7", "2 ell + (#claims - 1)",
                 rbr_num=max(2, m.mosaic_claims - 1), tot_num=2 * m.ell + m.mosaic_claims - 1))
    R.append(Row("Ring switching", "04 4.5", "7 + 2 n_pack", rbr_num=7, tot_num=7 + 2 * m.n_pack))
    return R


def pcs_rows(m: Machine, p: lg.LigeritoParams, profile: str) -> list[Row]:
    prov = profile == "provable-120"
    R: list[Row] = []
    for i in range(p.levels):
        k, t, r = p.ks[i], p.ts[i], p.rs[i]
        rho = 2.0 ** -r
        N = 1 << p.log_codeword(i)
        R.append(Row(f"Ligerito L{i}: sum-check ({k} rounds)", "04 4.4", "2k", rbr_num=2, tot_num=2 * k))
        R.append(Row(f"Ligerito L{i}: beta batching of queries", "04 4.4", "t", rbr_num=t, tot_num=t))
        gb = p.reps(i) * (FIELD_BITS - math.log2(k * N))
        R.append(Row(f"Ligerito L{i}: proximity gap (reps={p.reps(i)})", "04 4.7", "(k N / |K|)^reps",
                     bits_direct=gb, provable=prov))
        qb = t * -math.log2((1 + rho) / 2) if prov else t * r
        R.append(Row(f"Ligerito L{i}: queries (t={t})", "04 4.7", "((1+rho)/2)^t" if prov else "rho^t (conjectured)",
                     bits_direct=qb, provable=prov))
    return R


def hash_row(q_log2: int = QUERY_BUDGET_LOG2, digest_bits: int = 256) -> Row:
    return Row(f"Hash: Merkle/commitment binding, Q=2^{q_log2} oracle queries", "13 13.7",
               "Q^2 / 2^(digest_bits)", bits_direct=digest_bits - 2 * q_log2)


@dataclass
class Ledger:
    machine: Machine
    profile: str
    params: lg.LigeritoParams
    rows: list[Row]

    @property
    def provable(self) -> bool:
        return self.profile == "provable-120" and all(r.provable for r in self.rows)

    def weakest(self, k: int = 5, key: str = "rbr_bits") -> list[Row]:
        return sorted(self.rows, key=lambda r: getattr(r, key))[:k]

    @property
    def min_rbr_bits(self) -> float:
        return min(r.rbr_bits for r in self.rows)

    @property
    def total_error_bits(self) -> float:
        """-log2 of the sum of every reduction's total error (union bound)."""
        s = sum(2.0 ** -r.tot_bits for r in self.rows)
        return -math.log2(s)


def ledger(log_t: int, profile: str = "provable-120", machine: Machine | None = None,
           params: lg.LigeritoParams | None = None) -> Ledger:
    m = machine or Machine(log_t)
    p = params or lg.make_params(m.n_pack, profile)
    return Ledger(m, profile, p, field_rows(m) + pcs_rows(m, p, profile) + [hash_row()])


def proof_size_bytes(p: lg.LigeritoParams, n_ring: bool = True) -> float:
    """Expected proof size of one opening, bytes (13.5). Repetition (gs>1) is modelled as
    repeating the level's columns, auth paths, root and sum-check messages gs times."""
    total = 0.0
    for i in range(p.levels):
        k, t = p.ks[i], p.ts[i]
        lb = p.log_codeword(i)
        N = 1 << lb
        q = N * (1 - (1 - 1 / N) ** t)                      # expected distinct queries
        cols = q * 16 * (1 << k)
        auth = q * max(lb - math.log2(q) + 2, 0) * 32
        total += p.reps(i) * (cols + auth + 32 + 32 * k)
    total += 16 * (1 << p.n_final)
    if n_ring:
        total += 2048 + 32 * p.n
    return total


def report(log_t: int, profile: str = "provable-120") -> str:
    L = ledger(log_t, profile)
    out = [f"T=2^{log_t} profile={profile} provable={L.provable} n_pack={L.machine.n_pack} "
           f"ks={L.params.ks} gs={L.params.gs or '1'} ts={L.params.ts}",
           f"{'step':62s} {'rbr bits':>9s} {'total bits':>10s}"]
    for r in L.rows:
        out.append(f"{r.step:62s} {r.rbr_bits:9.1f} {r.tot_bits:10.1f}")
    out.append(f"min per-round bits {L.min_rbr_bits:.1f}; union of all totals: {L.total_error_bits:.1f} bits; "
               f"proof ~{proof_size_bytes(L.params)/1024:.0f} KiB")
    return "\n".join(out)


if __name__ == "__main__":
    import sys
    for lt in (int(x) for x in (sys.argv[1:] or ["22"])):
        print(report(lt))
