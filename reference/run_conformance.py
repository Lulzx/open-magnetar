"""RV64I conformance runner (docs/spec/15-testing.md §15.5).

Runs either:
1. A directory of prebuilt RV64I ELF binaries (`--elf-dir <dir>`), checking
   each non-skipped ELF across `riscv.Machine`, `bytecode.VirtualMachine`,
   `cpu_circuit.check`, and optionally `protocol.prove_instance` + `verify`.
2. The built-in 40-instruction RV64I conformance suite (`--builtin`, default
   when `--elf-dir` is omitted), exercising every normative RV64I instruction
   and trap condition in §9.1 across the interpreter, virtual machine, and
   CPU circuit.
"""

from __future__ import annotations

import argparse
import os
import sys
from dataclasses import dataclass

from openmagnetar import abi, bytecode as bc, cpu_circuit as cpu, elf as elfmod, keygen, protocol, riscv
from openmagnetar.riscv import Machine, Trap
from tests.asm import HALT, li32, program

DEFAULT_SKIPS = {
    "fence_i": "Zifencei extension is not part of RV64I (§9.1)",
    "ma_data": "Misaligned memory accesses are unprovable traps in v1 (C5, §9.1)",
}


@dataclass
class ConformanceResult:
    name: str
    status: str  # "PASS" | "SKIP" | "FAIL"
    reason: str = ""


def _prologue_ram(reg: int = 1) -> list[tuple]:
    return [("addi", reg, 0, 1), ("slli", reg, reg, 31)]


def builtin_cases() -> list[tuple[str, list[tuple], int]]:
    """Return `(name, instrs, expected_exit_code)` covering all 40 RV64I instructions."""
    b = _prologue_ram(1)
    return [
        ("lui", [("lui", 10, 0x12345)] + HALT, 0x12345000),
        ("auipc", [("auipc", 10, 1)] + HALT, 0x1000 + 0x1000),
        ("jal", [("jal", 5, 8), ("addi", 10, 0, 99), ("addi", 10, 5, 0)] + HALT, 0x1004),
        ("jalr", [("auipc", 5, 0), ("jalr", 6, 5, 13), ("addi", 10, 0, 99), ("sub", 10, 6, 5)] + HALT, 8),
        ("beq", [("addi", 2, 0, 7), ("addi", 3, 0, 7), ("beq", 2, 3, 8), ("addi", 10, 0, 1), ("addi", 10, 0, 2)] + HALT, 2),
        ("bne", [("addi", 2, 0, 7), ("addi", 3, 0, 8), ("bne", 2, 3, 8), ("addi", 10, 0, 1), ("addi", 10, 0, 2)] + HALT, 2),
        ("blt", [("addi", 2, 0, -3), ("addi", 3, 0, 1), ("blt", 2, 3, 8), ("addi", 10, 0, 1), ("addi", 10, 0, 2)] + HALT, 2),
        ("bge", [("addi", 2, 0, -1), ("addi", 3, 0, -3), ("bge", 2, 3, 8), ("addi", 10, 0, 1), ("addi", 10, 0, 2)] + HALT, 2),
        ("bltu", [("addi", 2, 0, 1), ("addi", 3, 0, -1), ("bltu", 2, 3, 8), ("addi", 10, 0, 1), ("addi", 10, 0, 2)] + HALT, 2),
        ("bgeu", [("addi", 2, 0, -1), ("addi", 3, 0, 1), ("bgeu", 2, 3, 8), ("addi", 10, 0, 1), ("addi", 10, 0, 2)] + HALT, 2),
        ("lb_sb", b + [("addi", 2, 0, 0x80), ("sb", 2, 1, 3), ("lb", 10, 1, 3), ("lb", 0, 1, 3)] + HALT, 0xFFFFFFFFFFFFFF80),
        ("lbu", b + [("addi", 2, 0, 0x80), ("sb", 2, 1, 3), ("lbu", 10, 1, 3), ("lbu", 0, 1, 3)] + HALT, 0x80),
        ("lh_sh", b + [("addi", 2, 0, -256), ("sh", 2, 1, 2), ("lh", 10, 1, 2), ("lh", 0, 1, 2)] + HALT, 0xFFFFFFFFFFFFFF00),
        ("lhu", b + [("addi", 2, 0, -256), ("sh", 2, 1, 2), ("lhu", 10, 1, 2), ("lhu", 0, 1, 2)] + HALT, 0xFF00),
        ("lw_sw", b + [("addi", 2, 0, -8), ("sw", 2, 1, 4), ("lw", 10, 1, 4), ("lw", 0, 1, 4)] + HALT, 0xFFFFFFFFFFFFFFF8),
        ("lwu", b + [("addi", 2, 0, -8), ("sw", 2, 1, 4), ("lwu", 10, 1, 4), ("lwu", 0, 1, 4)] + HALT, 0xFFFFFFF8),
        ("ld_sd", b + [("addi", 2, 0, -5), ("sd", 2, 1, 0), ("ld", 10, 1, 0), ("ld", 0, 1, 0)] + HALT, 0xFFFFFFFFFFFFFFFB),
        ("addi", [("addi", 10, 0, -42), ("addi", 0, 10, 99)] + HALT, 0xFFFFFFFFFFFFFFD6),
        ("slti", [("addi", 2, 0, -5), ("slti", 10, 2, -4)] + HALT, 1),
        ("sltiu", [("addi", 2, 0, 5), ("sltiu", 10, 2, -1)] + HALT, 1),
        ("xori", [("addi", 2, 0, 0x55), ("xori", 10, 2, 0x0F)] + HALT, 0x5A),
        ("ori", [("addi", 2, 0, 0x50), ("ori", 10, 2, 0x0A)] + HALT, 0x5A),
        ("andi", [("addi", 2, 0, 0x5F), ("andi", 10, 2, 0x3A)] + HALT, 0x1A),
        ("slli", [("addi", 2, 0, 3), ("slli", 10, 2, 40)] + HALT, 3 << 40),
        ("srli", [("addi", 2, 0, -1), ("srli", 10, 2, 60)] + HALT, 0xF),
        ("srai", [("addi", 2, 0, -16), ("srai", 10, 2, 2)] + HALT, 0xFFFFFFFFFFFFFFFC),
        ("add", [("addi", 2, 0, 19), ("addi", 3, 0, 23), ("add", 10, 2, 3)] + HALT, 42),
        ("sub", [("addi", 2, 0, 10), ("addi", 3, 0, 25), ("sub", 10, 2, 3)] + HALT, 0xFFFFFFFFFFFFFFF1),
        ("sll", [("addi", 2, 0, 7), ("addi", 3, 0, 33), ("sll", 10, 2, 3)] + HALT, 7 << 33),
        ("slt", [("addi", 2, 0, -1), ("addi", 3, 0, 1), ("slt", 10, 2, 3)] + HALT, 1),
        ("sltu", [("addi", 2, 0, 1), ("addi", 3, 0, -1), ("sltu", 10, 2, 3)] + HALT, 1),
        ("xor", [("addi", 2, 0, 0xF0), ("addi", 3, 0, 0x3C), ("xor", 10, 2, 3)] + HALT, 0xCC),
        ("srl", [("addi", 2, 0, -1), ("addi", 3, 0, 56), ("srl", 10, 2, 3)] + HALT, 0xFF),
        ("sra", [("addi", 2, 0, -64), ("addi", 3, 0, 4), ("sra", 10, 2, 3)] + HALT, 0xFFFFFFFFFFFFFFFC),
        ("or", [("addi", 2, 0, 0xF0), ("addi", 3, 0, 0x0F), ("or_", 10, 2, 3)] + HALT, 0xFF),
        ("and", [("addi", 2, 0, 0xF3), ("addi", 3, 0, 0x3F), ("and_", 10, 2, 3)] + HALT, 0x33),
        ("addiw", li32(2, 0x7FFFFFFF) + [("addiw", 10, 2, 1)] + HALT, 0xFFFFFFFF80000000),
        ("slliw", [("addi", 2, 0, 1), ("slliw", 10, 2, 31)] + HALT, 0xFFFFFFFF80000000),
        ("srliw", [("addi", 2, 0, -1), ("srliw", 10, 2, 16)] + HALT, 0xFFFF),
        ("sraiw", [("lui", 2, 0x80000), ("sraiw", 10, 2, 16)] + HALT, 0xFFFFFFFFFFFF8000),
        ("addw", li32(2, 0x7FFFFFFF) + [("addi", 3, 0, 1), ("addw", 10, 2, 3)] + HALT, 0xFFFFFFFF80000000),
        ("subw", [("lui", 2, 0x80000), ("addi", 3, 0, 1), ("subw", 10, 2, 3)] + HALT, 0x7FFFFFFF),
        ("sllw", [("addi", 2, 0, 1), ("addi", 3, 0, 31), ("sllw", 10, 2, 3)] + HALT, 0xFFFFFFFF80000000),
        ("srlw", [("addi", 2, 0, -1), ("addi", 3, 0, 24), ("srlw", 10, 2, 3)] + HALT, 0xFF),
        ("sraw", [("lui", 2, 0x80000), ("addi", 3, 0, 16), ("sraw", 10, 2, 3)] + HALT, 0xFFFFFFFFFFFF8000),
        ("fence_ecall", [("fence",), ("addi", 10, 0, 11)] + HALT, 11),
    ]


def run_builtin_conformance(prove: bool = False) -> list[ConformanceResult]:
    """Run all built-in RV64I conformance tests across Machine, VirtualMachine, and cpu_circuit."""
    par = cpu.Params(ram_log_words=8)
    ap = abi.Params(ram_log_words=4, input_log_words=1, output_log_words=1, max_code_words=256)
    results: list[ConformanceResult] = []
    for name, instrs, want_exit in builtin_cases():
        code, entry = program(instrs)
        m = Machine(code, entry, {}, par.ram_log_words).run(10000)
        prog = bc.expand(code, entry)
        vm = bc.VirtualMachine(prog, {}, par.ram_log_words).run_padded(10000)
        if m.exit_code != want_exit or vm.exit_code != want_exit:
            results.append(ConformanceResult(name, "FAIL", f"exit {m.exit_code} / {vm.exit_code} != {want_exit}"))
            continue
        if m.regs[:32] != vm.regs[:32] or m.ram != vm.ram:
            results.append(ConformanceResult(name, "FAIL", "Machine and VirtualMachine state diverged"))
            continue
        W = cpu.witness(vm.trace, par)
        pub = cpu.public_inputs(prog, vm.exit_code)
        if not cpu.check(W, pub, par, prog):
            results.append(ConformanceResult(name, "FAIL", "cpu_circuit.check rejected honest trace"))
            continue
        if prove:
            vk = keygen.keygen(code, entry, {}, ap, pcs="transparent")
            inst, pf = protocol.prove_instance(vk, b"")
            if not protocol.verify(vk, inst, pf):
                results.append(ConformanceResult(name, "FAIL", "protocol.verify rejected proof"))
                continue
        results.append(ConformanceResult(name, "PASS"))
    return results


def run_elf_directory(elf_dir: str, skip_file: str | None = None, prove: bool = False) -> list[ConformanceResult]:
    """Run all ELF files in `elf_dir` across Machine, VirtualMachine, cpu_circuit, and optionally protocol."""
    skips = dict(DEFAULT_SKIPS)
    if skip_file and os.path.exists(skip_file):
        with open(skip_file) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    parts = line.split(":", 1)
                    skips[parts[0].strip()] = parts[1].strip() if len(parts) > 1 else "skipped"

    ap = abi.Params(ram_log_words=16, input_log_words=4, output_log_words=4, max_code_words=65536)
    par = cpu.Params(ram_log_words=ap.ram_log_words)
    results: list[ConformanceResult] = []
    for fname in sorted(os.listdir(elf_dir)):
        path = os.path.join(elf_dir, fname)
        if not os.path.isfile(path):
            continue
        for key, reason in skips.items():
            if key in fname:
                results.append(ConformanceResult(fname, "SKIP", reason))
                break
        else:
            try:
                with open(path, "rb") as f:
                    raw = f.read()
                code, entry, m0 = elfmod.load(raw, ap)
                m = Machine(code, entry, m0, ap.ram_log_words).run(100000)
                prog = bc.expand(code, entry)
                vm = bc.VirtualMachine(prog, m0, ap.ram_log_words).run_padded(100000)
                if m.exit_code != 0 or vm.exit_code != 0 or m.regs[:32] != vm.regs[:32] or m.ram != vm.ram:
                    results.append(ConformanceResult(fname, "FAIL", f"exit={m.exit_code}/{vm.exit_code}"))
                    continue
                W = cpu.witness(vm.trace, par)
                if not cpu.check(W, cpu.public_inputs(prog, vm.exit_code), par, prog):
                    results.append(ConformanceResult(fname, "FAIL", "circuit rejected"))
                    continue
                if prove:
                    vk = keygen.keygen(code, entry, m0, ap, pcs="ligerito", pcs_profile="test", pcs_t=8)
                    inst, pf = protocol.prove_instance(vk, b"")
                    if not protocol.verify(vk, inst, pf):
                        results.append(ConformanceResult(fname, "FAIL", "proof rejected"))
                        continue
                results.append(ConformanceResult(fname, "PASS"))
            except (Trap, Exception) as e:
                results.append(ConformanceResult(fname, "FAIL", str(e)))
    return results


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Open Magnetar RV64I conformance runner (§15.5)")
    ap.add_argument("--elf-dir", help="Directory of prebuilt RV64I ELF binaries")
    ap.add_argument("--skip-file", help="Optional skip list file (`name: reason` per line)")
    ap.add_argument("--prove", action="store_true", help="Also prove and verify each test case")
    args = ap.parse_args(argv)

    results = (
        run_elf_directory(args.elf_dir, args.skip_file, args.prove)
        if args.elf_dir
        else run_builtin_conformance(args.prove)
    )
    passed = sum(1 for r in results if r.status == "PASS")
    skipped = sum(1 for r in results if r.status == "SKIP")
    failed = sum(1 for r in results if r.status == "FAIL")
    for r in results:
        suffix = f" ({r.reason})" if r.reason else ""
        print(f"[{r.status}] {r.name}{suffix}")
    print(f"\nSummary: {passed} passed, {skipped} skipped, {failed} failed")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
