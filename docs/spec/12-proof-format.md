# 12. Proof and key formats

**Status:** outline · **Paper:** —

## Scope
Byte-level serialization of proofs, verifying keys and public instances;
versioning; canonical-encoding requirements.

## Open questions

Each question lists a *proposed* answer. These are not decisions until marked **[OM-choice]** in the spec body.

1. **Q:** Serialization: hand-written canonical encoder vs serde+bincode
   - *Proposed:* Hand-written canonical format, so encodings are unambiguous and other implementations can parse it. Serde only for convenience wrappers.

## Specification

_To be written._
