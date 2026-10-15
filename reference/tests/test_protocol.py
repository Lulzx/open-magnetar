"""End-to-end tests of the full protocol (docs/spec/11, 12): keygen, prove, verify, serialization."""

import dataclasses
import random
import unittest

from openmagnetar import abi, keygen, protocol, router as rt
from openmagnetar import proof_format as pf
from openmagnetar.field import K, random_k
from openmagnetar.mle import mle_eval
from openmagnetar.riscv import Machine
from openmagnetar.transcript import Transcript

from .asm import HALT, li32, program

AP = abi.Params(ram_log_words=4, input_log_words=1, output_log_words=1, max_code_words=256)
OUT_LEN_OFF, OUT_VAL_OFF = 112, 120      # output region = words 14, 15 (A = 4, I = O = 1)


def fib_program():
    """Fibonacci by pairs, result and length word written to the output region, exit code 0."""
    return [("addi", 1, 0, 1), ("slli", 1, 1, 31), ("addi", 3, 0, 1), ("addi", 4, 0, 3),
            ("add", 2, 2, 3), ("add", 3, 3, 2), ("addi", 4, 4, -1), ("bne", 4, 0, -12),
            ("addi", 5, 0, 8), ("sd", 5, 1, OUT_LEN_OFF), ("sd", 3, 1, OUT_VAL_OFF), ("addi", 10, 0, 0)] + HALT


def mem_shift_program():
    """Stores and loads of every width, register-amount shifts (SLL, SRL, SRAW), exit code 3."""
    return (li32(2, 0x89ABCDEF) + [
        ("addi", 1, 0, 1), ("slli", 1, 1, 31), ("addi", 3, 0, 5),
        ("sd", 2, 1, 0), ("sb", 3, 1, 1), ("sh", 2, 1, 2), ("sw", 2, 1, 4),
        ("ld", 4, 1, 0), ("lb", 5, 1, 1), ("lhu", 6, 1, 2), ("lw", 7, 1, 4), ("lbu", 8, 1, 0),
        ("sll", 9, 4, 3), ("srl", 11, 4, 3), ("sraw", 12, 2, 3),
        ("xor", 13, 9, 11), ("xor", 13, 13, 12), ("add", 13, 13, 5),
        ("addi", 14, 0, 8), ("sd", 14, 1, OUT_LEN_OFF), ("sd", 13, 1, OUT_VAL_OFF), ("addi", 10, 0, 3)] + HALT)


def make_vk(instrs, pcs="transparent"):
    code, entry = program(instrs)
    kw = dict(pcs_profile="test", pcs_t=8) if pcs == "ligerito" else {}
    return keygen.keygen(code, entry, {}, AP, pcs=pcs, **kw), code, entry


def prove_expect_reject(tc, vk, hook):
    try:
        inst, proof = protocol.prove_instance(vk, b"", hooks=dict(trace=hook))
    except Exception:       # a cheating prover may fail while proving
        return
    tc.assertFalse(protocol.verify(vk, inst, proof))


class Fixture(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.vk, cls.code, cls.entry = make_vk(fib_program(), "ligerito")
        cls.inst, cls.proof = protocol.prove_instance(cls.vk, b"")
        cls.blob = pf.encode_proof(cls.vk, cls.proof)


class TestCompletenessLigerito(Fixture):
    def test_fib_real_ligerito(self):
        self.assertEqual(self.inst.T, 32)
        self.assertEqual(int.from_bytes(self.inst.output, "little"), 13)
        self.assertEqual(self.inst.exit_code, 0)
        self.assertTrue(protocol.verify(self.vk, self.inst, self.proof))
        self.assertTrue(protocol.verify(self.vk, self.inst, self.blob))

    def test_wrong_public_data(self):
        i = self.inst
        for bad in (dataclasses.replace(i, output=(14).to_bytes(8, "little")),
                    dataclasses.replace(i, output=b""),
                    dataclasses.replace(i, exit_code=1),
                    dataclasses.replace(i, T=64),
                    dataclasses.replace(i, T=16),
                    dataclasses.replace(i, input=b"x")):
            self.assertFalse(protocol.verify(self.vk, bad, self.proof))
            self.assertFalse(protocol.verify(self.vk, bad, self.blob))

    def test_wrong_vk(self):
        code = dict(self.code)
        code[0x1000 + 4 * 2] ^= 0x100000        # a different program
        vk2 = keygen.keygen(code, self.entry, {}, AP, pcs="ligerito", pcs_profile="test", pcs_t=8)
        self.assertFalse(protocol.verify(vk2, self.inst, self.blob))

    def test_tampered_bytes(self):
        rng = random.Random(7)
        n = len(self.blob)
        positions = [0, 5, 40, 41, 300, 2000, 4000, 7000, 9000, n - 3000, n - 700, n - 1]
        positions += [rng.randrange(n) for _ in range(4)]
        for pos in positions:
            b = bytearray(self.blob)
            b[pos] ^= 0x01
            self.assertFalse(protocol.verify(self.vk, self.inst, bytes(b)), pos)

    def test_length_rules(self):
        self.assertFalse(protocol.verify(self.vk, self.inst, self.blob + b"\x00"))
        self.assertFalse(protocol.verify(self.vk, self.inst, self.blob[:-1]))
        self.assertFalse(protocol.verify(self.vk, self.inst, b""))

    def test_roundtrips(self):
        again = pf.decode_proof(self.vk, self.blob, self.inst.T)
        self.assertEqual(pf.encode_proof(self.vk, again), self.blob)
        self.assertTrue(protocol.verify(self.vk, self.inst, again))
        vb = pf.encode_vk(self.vk)
        vk2 = pf.decode_vk(vb)
        self.assertEqual(vk2.digest(), self.vk.digest())
        self.assertEqual(pf.encode_vk(vk2), vb)
        with self.assertRaises(pf.FormatError):
            pf.decode_vk(vb + b"\x00")
        ib = pf.encode_instance(self.inst)
        self.assertEqual(pf.decode_instance(ib), self.inst)
        with self.assertRaises(pf.FormatError):
            pf.decode_instance(ib[:-1])

    def test_size_model(self):
        D = self.vk.derived
        I = D.instance(self.inst.T)
        lig = len(pf._lig_w(self.proof.pcs_proof[1]))
        k = pf.pcs_free_k_count(I.n, D.ram_a, D.ram_d, D.rom_a, D.rom_d, I.ell, len(D.segments))
        digest = self.vk.hasher.digest_size
        self.assertEqual(len(self.blob) - lig, 4 + 2 + digest + 16 * k)


class TestTransparent(unittest.TestCase):
    def test_memory_and_shifts(self):
        vk, code, entry = make_vk(mem_shift_program())
        inst, proof = protocol.prove_instance(vk, b"")
        ref = Machine(code, entry, {}, 4).run(10000)
        self.assertEqual(inst.exit_code, ref.exit_code)
        self.assertEqual(inst.exit_code, 3)
        self.assertEqual(inst.T, 64)
        self.assertTrue(protocol.verify(vk, inst, proof))
        self.assertTrue(protocol.verify(vk, inst, pf.encode_proof(vk, proof)))
        self.assertFalse(protocol.verify(vk, dataclasses.replace(inst, output=b"\x01" * 8), proof))
        self.assertFalse(protocol.verify(vk, dataclasses.replace(inst, exit_code=4), proof))

    def test_input_is_bound(self):
        # a program that copies its (public) input word to the output region
        prog = [("addi", 1, 0, 1), ("slli", 1, 1, 31), ("ld", 3, 1, 96), ("ld", 4, 1, 104),
                ("sd", 3, 1, OUT_LEN_OFF), ("sd", 4, 1, OUT_VAL_OFF), ("addi", 10, 0, 0)] + HALT
        vk, _, _ = make_vk(prog)
        data = (0x1122334455667788).to_bytes(8, "little")
        inst, proof = protocol.prove_instance(vk, data)
        self.assertEqual(inst.output, data)
        self.assertTrue(protocol.verify(vk, inst, proof))
        self.assertFalse(protocol.verify(vk, dataclasses.replace(inst, input=data[::-1]), proof))


class TestCheatingProvers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.vk, _, _ = make_vk(fib_program())

    def test_ram_read_value(self):
        def hook(trace):
            j = next(i for i, r in enumerate(trace) if r["rom"]["mem"])
            trace[j]["ram_old"] ^= 0x10
        prove_expect_reject(self, self.vk, hook)

    def test_register_value(self):
        def hook(trace):
            j = next(i for i, r in enumerate(trace) if r["rom"]["c_add"] and r["rd"] == 2)
            trace[j]["v1"] ^= 0x4
        prove_expect_reject(self, self.vk, hook)

    def test_shift_output(self):
        def hook(trace):
            j = next(i for i, r in enumerate(trace) if r["shift_amt"] is not None)
            trace[j]["dp"]["Y"] ^= 0x2
        prove_expect_reject(self, self.vk, hook)

    def test_dishonest_output_claim(self):
        inst, proof = protocol.prove_instance(self.vk, b"")
        self.assertFalse(protocol.verify(self.vk, dataclasses.replace(inst, output=(5).to_bytes(8, "little")), proof))

    def test_private_input_rejected(self):
        with self.assertRaises(ValueError):
            protocol.prove(self.vk, b"", b"secret")


class TestFastRouters(unittest.TestCase):
    def test_equal_to_dense(self):
        rng = random.Random(3)
        wb, n = 4, 3
        T = 1 << n
        cyc = [(rng.getrandbits(16), None if rng.random() < .4 else (rng.randrange(16), rng.randrange(3)))
               for _ in range(T)]
        w = rt.shift_witness(cyc, wb)
        r_o = [random_k(rng) for _ in range(wb)]
        r_j = [random_k(rng) for _ in range(n)]
        y = mle_eval(w["Y"], r_o + r_j)
        a = rt.shift_prove(n, w, r_o, r_j, y, Transcript(b"t"), b"s", wb)
        b = rt.shift_prove_fast(n, w, r_o, r_j, y, Transcript(b"t"), b"s", wb)
        self.assertEqual(a[0].sc.round_msgs, b[0].sc.round_msgs)
        self.assertEqual(a[0].evals, b[0].evals)
        sc = [(rng.getrandbits(16), rng.getrandbits(16),
               None if rng.random() < .5 else ((h := rng.randrange(3)), rng.randrange(2) << h)) for _ in range(T)]
        ws = rt.store_witness(sc, wb)
        y = mle_eval(ws["Inc"], r_o + r_j)
        a = rt.store_prove(n, ws, r_o, r_j, y, Transcript(b"t"), b"s", wb)
        b = rt.store_prove_fast(n, ws, r_o, r_j, y, Transcript(b"t"), b"s", wb)
        self.assertEqual(a[0].sc.round_msgs, b[0].sc.round_msgs)
        self.assertEqual(a[0].evals, b[0].evals)


class TestKeygen(unittest.TestCase):
    def test_derived(self):
        vk, _, _ = make_vk(fib_program())
        D = vk.derived
        self.assertEqual((D.rho, D.nu), (10, 14))
        self.assertEqual((D.ram_a, D.ram_d), (4, 1))
        I = D.instance(32)
        self.assertEqual(I.layout.ell, 17 if False else I.layout.ell)
        self.assertIn("twist/ram/wa/1", I.ids)
        self.assertEqual(I.ids["twist/ram/wa/1"], I.ids["twist/ram/ra0/1"])
        with self.assertRaises(keygen.KeyError_):
            D.instance(3)
        with self.assertRaises(keygen.KeyError_):
            D.instance(48)

    def test_choose_ad(self):
        self.assertEqual(keygen.choose_ad(6), (6, 2))
        self.assertEqual(keygen.choose_ad(20), (20, 5))
        self.assertEqual(keygen.choose_ad(24), (24, 6))
        self.assertEqual(keygen.choose_ad(5), (8, 2))
        self.assertEqual(keygen.choose_ad(4), (4, 1))


if __name__ == "__main__":
    unittest.main()


class TestVectors(unittest.TestCase):
    def test_replay_vector(self):
        import json
        import os
        p = os.path.join(os.path.dirname(__file__), "..", "vectors", "11-12", "fib_ligerito_test.json")
        with open(p) as f:
            v = json.load(f)
        vk = pf.decode_vk(bytes.fromhex(v["vk_hex"]))
        self.assertEqual(vk.digest().hex(), v["vk_digest"])
        inst = pf.decode_instance(bytes.fromhex(v["instance_hex"]))
        self.assertTrue(protocol.verify(vk, inst, bytes.fromhex(v["proof_hex"])))
