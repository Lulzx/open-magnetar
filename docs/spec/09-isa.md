# 09. ISA, virtual instructions and bytecode

**Status:** outline · **Paper:** §2.1, §5

## Scope
Supported RV64I instructions and their exact semantics; ECALL/EBREAK handling;
the virtual instruction set; the deterministic expansion of each RV64I
instruction into virtual instructions; the micro-PC; the bytecode table ROM
(its columns and encoding); virtual registers.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Which instructions need multi-cycle expansion? (Paper: Fibonacci step = 6 virtual cycles, which suggests mostly 1:1.)
   - *Proposed:* 1:1 except: register-amount shifts (see 08), sub-word loads (extract + sign-extend from 64-bit RAM word), misaligned access handling. Decide each case.
2. **Q:** Misaligned loads/stores (allowed by RV64I spec, may trap)
   - *Proposed:* Trap / unprovable in v1 (guest toolchain avoids them); revisit.
3. **Q:** FENCE, ECALL, EBREAK, CSR (Zicsr not in RV64I)
   - *Proposed:* FENCE = NOP; ECALL = syscall dispatch (halt, read input, write output); EBREAK = halt with failure.
4. **Q:** Bytecode ROM columns: decoded fields (opcode one-hots, rd/rs1/rs2, imm bits, routing selector fields, next-micro-PC, flags)
   - *Proposed:* Specify full column list; this is the interface between 09, 10 and 07.

## Specification

_To be written._
