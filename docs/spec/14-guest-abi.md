# 14. Guest ABI and toolchain

**Status:** outline · **Paper:** —

## Scope
How guest programs are built for strict RV64I (Rust custom target JSON with
build-std on nightly; C via clang -march=rv64i -mabi=lp64), entry point,
memory map (code, data, stack, heap, input, output regions), syscalls,
termination, and the host SDK API.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Rust guest target: custom JSON target (rv64i, no atomics) + build-std, or upstream an official target later?
   - *Proposed:* Custom JSON target shipped with the SDK; compiler-builtins provides mul/div libcalls.
2. **Q:** No 'A' extension means no atomics; std-free (no_std + alloc) guests only?
   - *Proposed:* no_std + alloc in v1, with a bump allocator.
3. **Q:** Input/output model: memory-mapped regions vs syscalls
   - *Proposed:* Both regions memory-mapped; their contents bound into the public instance as digests computed by the verifier.

## Specification

_To be written._
