import struct
import unittest

from openmagnetar.abi import RAM_BASE, Params
from openmagnetar.elf import ElfError, load, PF_R, PF_W, PF_X

P = Params(ram_log_words=12, input_log_words=4, output_log_words=4)
ADDI = 0x00100093  # addi x1,x0,1
ECALL = 0x00000073


def make_elf(segs, entry=0x1000_0000, flags=0, machine=243, etype=2, cls=2, ph_extra=()):
    """segs: list of (vaddr, flags, data, memsz). Returns ELF64 bytes."""
    phs = list(segs)
    ehsize, phsize = 64, 56
    off = ehsize + phsize * (len(phs) + len(ph_extra))
    body = b""
    ph_bytes = b""
    for vaddr, fl, data, memsz in phs:
        ph_bytes += struct.pack("<IIQQQQQQ", 1, fl, off + len(body), vaddr, vaddr,
                                len(data), memsz, 8)
        body += data
    for t in ph_extra:
        ph_bytes += struct.pack("<IIQQQQQQ", t, 0, 0, 0, 0, 0, 0, 1)
    ident = b"\x7fELF" + bytes([cls, 1, 1, 0]) + bytes(8)
    hdr = ident + struct.pack("<HHIQQQIHHHHHH", etype, machine, 1, entry, 64, 0, flags,
                              64, 56, len(phs) + len(ph_extra), 64, 0, 0)
    return hdr + ph_bytes + body


def code_seg(words=(ADDI, ECALL), vaddr=0x1000_0000):
    d = b"".join(struct.pack("<I", w) for w in words)
    return (vaddr, PF_R | PF_X, d, len(d))


class TestElf(unittest.TestCase):
    def test_ok(self):
        data = (RAM_BASE, PF_R | PF_W, bytes([1, 2, 3, 0, 0, 0, 0, 0, 9]), 32)
        code, entry, ram = load(make_elf([code_seg(), data], ph_extra=(0x6474E551,)), P)
        self.assertEqual(code, {0x1000_0000: ADDI, 0x1000_0004: ECALL})
        self.assertEqual(entry, 0x1000_0000)
        self.assertEqual(ram, {0: 0x030201, 1: 9})

    def test_unaligned_data_packing(self):
        data = (RAM_BASE + 3, PF_R | PF_W, b"\xaa\xbb", 2)
        _, _, ram = load(make_elf([code_seg(), data]), P)
        self.assertEqual(ram, {0: 0xBBAA << 24})

    def test_errors(self):
        ok = [code_seg()]
        bad = {
            "rvc": make_elf(ok, flags=1),
            "float": make_elf(ok, flags=4),
            "machine": make_elf(ok, machine=62),
            "dyn": make_elf(ok, etype=3),
            "elf32": make_elf(ok, cls=1),
            "entry": make_elf(ok, entry=0x1000_0008),
            "entry unaligned": make_elf(ok, entry=0x1000_0002),
            "wx": make_elf([(0x1000_0000, PF_R | PF_W | PF_X, b"\x93\0\x10\0", 4)]),
            "code in ram": make_elf([code_seg(vaddr=RAM_BASE)], entry=RAM_BASE),
            "rvc insn": make_elf([code_seg(words=(0x4501, ECALL))]),
            "data below ram": make_elf(ok + [(0x2000_0000, PF_R, b"x", 1)]),
            "data in io": make_elf(ok + [(RAM_BASE + 8 * (4096 - 32), PF_R, b"x", 1)]),
            "data past ram": make_elf(ok + [(RAM_BASE + 8 * 4096, PF_R, b"x", 1)]),
            "overlap": make_elf(ok + [(RAM_BASE, PF_R, b"x" * 16, 16), (RAM_BASE + 8, PF_R, b"y", 1)]),
            "code overlap": make_elf(ok + [code_seg()]),
            "no code": make_elf([(RAM_BASE, PF_R, b"x", 1)]),
            "bad pt": make_elf(ok, ph_extra=(2,)),
            "garbage": b"hello",
        }
        for name, blob in bad.items():
            with self.subTest(name):
                with self.assertRaises(ElfError):
                    load(blob, P)

    def test_code_too_large(self):
        with self.assertRaises(ElfError):
            load(make_elf([code_seg()]), Params(12, 4, 4, max_code_words=1))

    def test_deterministic_digest(self):
        from openmagnetar.abi import program_digest
        e = make_elf([code_seg(), (RAM_BASE, PF_R, b"\x05", 8)])
        a, b = load(e, P), load(e, P)
        self.assertEqual(program_digest(*a, P), program_digest(*b, P))


if __name__ == "__main__":
    unittest.main()
