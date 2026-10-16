# Public-vector validation

## Recorded run

On 2026-10-16, the Rust CLI executed the C SHA-256 guest, generated real
Ligerito proofs, and verified them against three known SHA-256 answers.
All three outputs matched, all three proofs verified, and all six negative
checks below were rejected.

The run used the local working tree based on commit `9872a7e`, including
uncommitted implementation changes. These results do not describe that
commit alone. The host CLI and guest ELFs were freshly built for the run.

Configuration:

- Release Rust CLI, `provable-120` profile, Ligerito PCS, SHA-256 transcript
  hashing, default `pcs-r = 2`; no mock PCS.
- RV64I C guests compiled with LLVM clang and lld on macOS.
- RAM: `A = 16`; input and output regions: `I = O = 14`.
- Exact byte inputs, without trailing newlines.

## Known answers and proof results

The `abc` and 56-byte SHA-256 vectors appear in the test driver of
[RFC 6234, section 8.5](https://www.rfc-editor.org/rfc/rfc6234#section-8.5).
The empty-message digest was also checked. Every expected digest below was
independently checked with Python's `hashlib.sha256` before comparison with
the guest output.

| Case | Input bytes | Padded virtual cycles | Proof bytes | Output matches | Verification |
|---|---:|---:|---:|---|---|
| Empty message | 0 | 8,192 | 211,390 | Yes | Accepted |
| `abc` | 3 | 8,192 | 210,814 | Yes | Accepted |
| Standard 56-byte message | 56 | 16,384 | 245,214 | Yes | Accepted |

Exact inputs and expected hexadecimal digests:

```text
Input: empty byte string
SHA-256: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855

Input: abc
Input hex: 616263
SHA-256: ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad

Input: abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq
SHA-256: 248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
```

For each case, the serialized public instance contained the original input,
the expected 32-byte digest, and exit code zero. Execution through `om run`
also produced the expected digest.

## Rejection checks

Each check reused the accepted `abc` proof while changing one item.
Rejection required CLI exit code 1, rather than a crash or usage error.

| Change | Recorded rejection |
|---|---|
| Public input: `abc` to `abd` | `outer sum-check final check failed` |
| Public output: flip one digest bit | `outer sum-check final check failed` |
| Public exit code: 0 to 1 | `outer sum-check final check failed` |
| Verification key: use the Fibonacci guest's key | `too many opened columns` |
| Proof: flip the final byte's low bit | `malformed opening` |
| Program image: change one SHA-256 round constant and regenerate its key | `outer sum-check final check failed` |

The Fibonacci-key check rejected during proof parsing because the programs
have different proof layouts. The final check kept the SHA-256 code and
proof layout unchanged, but changed one bit of `K256[0]` in its initial
data image. Executing that altered guest on `abc` produced
`b043392194b879840f51dd682800237a4cf7efd7ff77ec43155a85800565e81c`.
The original proof failed under the altered image's valid key during the
Spartan check, exercising statement binding beyond layout validation.

## Host hashing checks

The following command also passed all five tests: SHA-256, SHA3-256,
SHA-384, padding/block boundaries, and hash-profile handling.

```sh
cargo test -p om-transcript --release --offline --test hashing
```

These test the host hash implementations. The guest proven above computes
SHA-256 only.

## Reproduce

Run from the repository root with Rust, Python 3, LLVM clang, and lld
installed. On the macOS/Homebrew setup used for this run, first set:

```sh
export PATH=/opt/homebrew/opt/llvm/bin:/opt/homebrew/opt/lld/bin:$PATH
cargo build -p om --release --offline
```

The script below builds both guest ELFs into a new temporary directory,
runs the three positive cases and six rejection cases, and leaves the
artifacts there for inspection. Set `CC` if LLVM clang is not named `clang`.
Proof sizes and error wording may change with later implementation changes.

```python
from pathlib import Path
import copy
import hashlib
import os
import subprocess
import sys
import tempfile

root = Path.cwd()
sys.path.insert(0, str(root / "reference"))
from openmagnetar.proof_format import decode_instance, encode_instance

out = Path(tempfile.mkdtemp(prefix="magnetar-public-vectors-"))
om = root / "target/release/om"
abi = ["--ram-log-words", "16", "--input-log-words", "14",
       "--output-log-words", "14"]

def run(args, expected=0, cwd=root):
    p = subprocess.run([str(x) for x in args], cwd=cwd,
                       capture_output=True, text=True, timeout=180)
    assert p.returncode == expected, (args, p.returncode, p.stdout, p.stderr)
    return p

def keygen(name):
    run([om, "keygen", "--elf", out / f"{name}.elf", "--out",
         out / f"{name}.vk", "--profile", "provable-120", *abi])

for name in ("sha256", "fib"):
    run([os.environ.get("CC", "clang"), "--target=riscv64", "-march=rv64i",
         "-mabi=lp64", "-mcmodel=medany", "-mno-relax", "-O2", "-nostdlib",
         "-ffreestanding", "-fno-pic", "-fno-builtin", "-I.", "-fuse-ld=lld",
         "-static", "-Wl,-T,link.ld", "-Wl,-z,max-page-size=8",
         "-Wl,--defsym=__stack_top=2147745792",
         "-Wl,--defsym=__input_base=2147745792",
         "-Wl,--defsym=__output_base=2147876864",
         "-Wl,--defsym=__stack_size=65536", "rt/start.S",
         f"examples/{name}.c", "-o", out / f"{name}.elf"], cwd=root / "guest")
    keygen(name)

vectors = [
    ("empty", b"", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("abc", b"abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("message56", b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
     "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
]
for name, message, digest in vectors:
    assert hashlib.sha256(message).hexdigest() == digest
    (out / f"{name}.input").write_bytes(message)
    p = run([om, "run", "--elf", out / "sha256.elf", "--input",
             out / f"{name}.input", *abi])
    assert f"output: {digest}" in p.stdout
    run([om, "prove", "--vk", out / "sha256.vk", "--elf", out / "sha256.elf",
         "--input", out / f"{name}.input", "--out", out / f"{name}.proof",
         "--instance", out / f"{name}.instance"])
    inst = decode_instance((out / f"{name}.instance").read_bytes())
    assert (inst.input, inst.output.hex(), inst.exit_code) == (message, digest, 0)
    run([om, "verify", "--vk", out / "sha256.vk", "--instance",
         out / f"{name}.instance", "--proof", out / f"{name}.proof"])
    print("PASS", name, inst.T, (out / f"{name}.proof").stat().st_size)

def reject(name, vk="sha256", instance="abc", proof="abc"):
    p = run([om, "verify", "--vk", out / f"{vk}.vk", "--instance",
             out / f"{instance}.instance", "--proof", out / f"{proof}.proof"],
            expected=1)
    print("PASS rejection", name, p.stderr.strip())
    return p

base = decode_instance((out / "abc.instance").read_bytes())
for name in ("wrong-input", "wrong-output", "wrong-exit"):
    inst = copy.deepcopy(base)
    if name == "wrong-input":
        inst.input = b"abd"
    elif name == "wrong-output":
        inst.output = bytes([inst.output[0] ^ 1]) + inst.output[1:]
    else:
        inst.exit_code = 1
    (out / f"{name}.instance").write_bytes(encode_instance(inst))
    reject(name, instance=name)

reject("different-program", vk="fib")
proof = bytearray((out / "abc.proof").read_bytes())
proof[-1] ^= 1
(out / "tampered.proof").write_bytes(proof)
reject("tampered-proof", proof="tampered")

elf = bytearray((out / "sha256.elf").read_bytes())
marker = bytes.fromhex("982f8a4291443771cffbc0b5a5dbb5e9")
assert elf.count(marker) == 1  # First four K256 words, little endian.
elf[elf.index(marker)] ^= 1
(out / "changed.elf").write_bytes(elf)
keygen("changed")
p = run([om, "run", "--elf", out / "changed.elf", "--input",
         out / "abc.input", *abi])
assert f"output: {base.output.hex()}" not in p.stdout
p = reject("different-program-image-same-layout", vk="changed")
assert "outer sum-check final check failed" in p.stderr
print("All checks passed. Artifacts:", out)
```

Save the Python block to a file or run it with `python3 -` and a heredoc.

## What this establishes

The checks demonstrate correct outputs and accepted proofs for these three
executions, plus rejection of the specific statement and proof mutations
listed above. The expected digests come from outside the implementation;
the reference model is used only to decode and re-encode public instances.

This run did not exercise external RISC-V conformance suites, arbitrary
malicious witnesses, recursion, or zero knowledge. It is not an independent
proof of soundness or a security audit. See [the testing specification](spec/15-testing.md)
and [security analysis](spec/13-security.md) for the broader validation scope.
