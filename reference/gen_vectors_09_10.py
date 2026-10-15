"""Emit small test vectors for sections 09/10 into reference/vectors/10-cpu/.

Run from the repo root:  python3 reference/gen_vectors_09_10.py
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "tests"))

from openmagnetar import bytecode as bc          # noqa: E402
from openmagnetar import cpu_circuit as cpu      # noqa: E402
from openmagnetar.riscv import decode, Machine   # noqa: E402
from tests.asm import HALT, asm, program, li32   # noqa: E402

OUT = os.path.join(HERE, "vectors", "10-cpu")
A = 8


def main():
    os.makedirs(OUT, exist_ok=True)
    # decoder vectors
    dec = []
    for ins in [("addi", 5, 6, -1), ("sub", 1, 2, 3), ("srai", 3, 4, 63), ("lui", 7, 1), ("jal", 1, -4),
                ("beq", 1, 2, 8), ("lw", 1, 2, 4), ("sd", 1, 2, 8), ("sraw", 3, 4, 5), ("ecall",)]:
        w = asm(*ins)
        i = decode(w)
        dec.append(dict(word=f"{w:08x}", name=i.name, rd=i.rd, rs1=i.rs1, rs2=i.rs2, imm=i.imm))
    # bytecode expansion + trace + witness commitment-free digest for one program
    prog = li32(2, 0x89ABCDEF) + [("addi", 3, 0, 5), ("sll", 4, 2, 3), ("addi", 10, 4, 0)] + HALT
    code, entry = program(prog)
    p = bc.expand(code, entry)
    vm = bc.VirtualMachine(p, {}, A).run_padded(1000)
    par = cpu.Params(ram_log_words=A)
    W = cpu.witness(vm.trace, par)
    pub = cpu.public_inputs(p, vm.exit_code)
    ref = Machine(code, entry, {}, A).run(1000)
    assert ref.exit_code == vm.exit_code and cpu.check(W, pub, par, p)
    st = cpu.stats(par)
    out = dict(
        decode=dec,
        program=dict(code={f"{k:x}": f"{v:08x}" for k, v in code.items()}, entry_pc=f"{entry:x}"),
        rom_head=[{k: (hex(v) if v > 9 else v) for k, v in r.items() if v} for r in p.rom[:8]],
        upc_of_pc={f"{k:x}": v for k, v in p.upc_of_pc.items()},
        cycles=len(vm.trace), exit_code=vm.exit_code,
        trace_prefix=[dict(upc=r["upc"], rd=r["rd"], v1=hex(r["v1"]), v2=hex(r["v2"]), rd_val=hex(r["rd_val"]),
                           next_upc=r["next_upc"]) for r in vm.trace[:12]],
        witness_row_ones=[sum(r) for r in W],
        public=pub, stats=st,
        layout=[dict(name=s.name, log_size=s.log_size, offset=s.offset, kind=s.kind, owner=s.owner)
                for s in cpu.layout(par)],
    )
    with open(os.path.join(OUT, "cpu.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote", os.path.join(OUT, "cpu.json"))


if __name__ == "__main__":
    main()
