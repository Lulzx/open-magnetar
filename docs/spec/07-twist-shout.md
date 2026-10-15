# 07. BinaryTwist and BinaryShout

**Status:** outline · **Paper:** §4.4, ref [55]

## Scope
Address decomposition into d one-hot components, the Frobenius-based one-hot
check (∆⋆), BinaryShout for the bytecode (Φ with α_0), BinaryTwist (Val
reconstruction via LT, read/write identities, row-sum-one check), and the
Inc-at-random-point output used by the store router.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Choice of d (number of address chunks) for registers (32 regs + virtual regs), RAM, and bytecode
   - *Proposed:* Registers: d=1 if virtual-register count ≤ 64. RAM: chosen to balance commit size vs rounds (e.g. 2^8-wide chunks). Bytecode: depends on program size, so it is a vk parameter.
2. **Q:** RAM address space: full 64-bit addresses are impossible as K=2^a. How are guest addresses mapped (bounded RAM size, word-addressed 64-bit words)?
   - *Proposed:* RAM is word (8-byte) addressed over a bounded region of size 2^a words fixed in the vk; out-of-range access is a guest fault (see 14).
3. **Q:** Initial memory M_0: how does the verifier evaluate its MLE cheaply when it contains program data/inputs?
   - *Proposed:* M_0 sparse: zero except program data + input region; verifier evaluates it in O(nonzeros).
4. **Q:** Final memory / outputs: Twist proves consistent reads; how are outputs bound?
   - *Proposed:* Outputs are read back by explicit 'output' virtual cycles, or via a final-state evaluation of Val at j = T. Decide here.
5. **Q:** Twist prover algorithm (the Val computation is the expensive part)
   - *Proposed:* Follow the 'local' / chunked algorithm of [55]; spec only the verifier-visible protocol here.

## Specification

_To be written._
