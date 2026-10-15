"""Emit protocol and format vectors for sections 11/12 into reference/vectors/11-12/.

Run from the repo root:  python3 reference/gen_vectors_11_12.py
The vector is a complete accepting proof (tiny Ligerito test profile) for a Fibonacci program, with the
canonical encodings of the verifying key, instance and proof, the vk digest and the size breakdown.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from openmagnetar import keygen, protocol  # noqa: E402
from openmagnetar import proof_format as pf  # noqa: E402
from tests.test_protocol import AP, fib_program  # noqa: E402
from tests.asm import program  # noqa: E402

OUT = os.path.join(HERE, "vectors", "11-12")


def main():
    os.makedirs(OUT, exist_ok=True)
    code, entry = program(fib_program())
    vk = keygen.keygen(code, entry, {}, AP, pcs="ligerito", pcs_profile="test", pcs_t=8)
    inst, proof = protocol.prove_instance(vk, b"")
    assert protocol.verify(vk, inst, proof)
    blob = pf.encode_proof(vk, proof)
    D = vk.derived
    I = D.instance(inst.T)
    out = dict(
        program=dict(code={f"{k:x}": f"{v:08x}" for k, v in code.items()}, entry_pc=f"{entry:x}"),
        abi=dict(A=AP.ram_log_words, I=AP.input_log_words, O=AP.output_log_words, max_code=AP.max_code_words),
        pcs=dict(mode=vk.pcs, profile=vk.pcs_profile, r=vk.pcs_r, t=vk.pcs_t),
        vk_hex=pf.encode_vk(vk).hex(), vk_digest=vk.digest().hex(),
        instance_hex=pf.encode_instance(inst).hex(), T=inst.T, exit_code=inst.exit_code,
        output_hex=inst.output.hex(),
        proof_hex=blob.hex(), proof_bytes=len(blob), ell=I.ell, components=len(I.layout.placements),
    )
    with open(os.path.join(OUT, "fib_ligerito_test.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote", len(blob), "byte proof; T =", inst.T, "ell =", I.ell)


if __name__ == "__main__":
    main()
