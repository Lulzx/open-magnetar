//! `om` — the Open Magnetar host CLI: `keygen`, `prove`, `verify`
//! and `run` over `om-sdk`. Argument parsing is hand-rolled (no CLI
//! dependency): every flag is `--name value`; `--help` works at every
//! level. Errors go to stderr with a nonzero exit code (1 for a
//! failure/rejection, 2 for a usage error).

use std::collections::HashMap;
use std::process::ExitCode;

use om_sdk::{
    AbiParams, Hasher, PcsMode, PcsProfile, SdkParams, decode_instance, decode_vk, encode_instance,
    encode_vk,
};

const USAGE: &str = "\
om — Open Magnetar host tool

Usage:
  om keygen --elf <path> --out <vk.bin> [keygen options]
  om prove  --vk <vk.bin> --elf <path> --out <proof.bin> [--input <file.bin>] [--instance <inst.bin>]
  om verify --vk <vk.bin> --instance <inst.bin> --proof <proof.bin>
  om run    --elf <path> [--input <file.bin>] [abi options]
  om --help

Run `om <command> --help` for a command's options.
";

const KEYGEN_USAGE: &str = "\
om keygen — generate a verifying key from a guest ELF

Usage: om keygen --elf <path> --out <vk.bin> [options]

Options:
  --elf <path>              guest ELF64 image (required)
  --out <vk.bin>            verifying-key output file (required)
  --profile <name>          PCS profile: provable-120 (default) | test
  --pcs <name>              PCS mode: ligerito (default) | mock
  --hash <name>             hash profile: sha256 (default) | sha3-256 | sha384
  --pcs-r <n>               Ligerito log inverse rate (default 2)
  --pcs-t <n>               queries per level, test profile (default 8)
  --ram-log-words <n>       A: RAM has 2^A words (default 20)
  --input-log-words <n>     I: input region has 2^I words (default 12)
  --output-log-words <n>    O: output region has 2^O words (default 8)
  --max-code-words <n>      maximum instruction words (default 1048576)
  --help                    show this help
";

const PROVE_USAGE: &str = "\
om prove — execute a guest ELF and prove the execution

Usage: om prove --vk <vk.bin> --elf <path> --out <proof.bin> [options]

Options:
  --vk <vk.bin>             verifying key from `om keygen` (required)
  --elf <path>              guest ELF64 image the vk was made from (required)
  --out <proof.bin>         proof output file (required)
  --input <file.bin>        public input bytes (default: empty)
  --instance <inst.bin>     public-instance output file (default: print fields only)
  --max-cycles <n>          execution budget in cycles (default: 1048576)
  --help                    show this help
";

const VERIFY_USAGE: &str = "\
om verify — verify a proof

Usage: om verify --vk <vk.bin> --instance <inst.bin> --proof <proof.bin>

Options:
  --vk <vk.bin>             verifying key (required)
  --instance <inst.bin>     public instance (required)
  --proof <proof.bin>       proof blob (required)
  --help                    show this help

Prints OK and exits 0 on accept; exits nonzero on reject.
";

const RUN_USAGE: &str = "\
om run — execute a guest ELF without proving

Usage: om run --elf <path> [options]

Options:
  --elf <path>              guest ELF64 image (required)
  --input <file.bin>        public input bytes (default: empty)
  --hash <name>             hash profile: sha256 (default) | sha3-256 | sha384
  --ram-log-words <n>       A: RAM has 2^A words (default 20)
  --input-log-words <n>     I: input region has 2^I words (default 12)
  --output-log-words <n>    O: output region has 2^O words (default 8)
  --max-code-words <n>      maximum instruction words (default 1048576)
  --help                    show this help

The ABI options must match the layout the guest was built for, as in
`om keygen`; they select the memory map the ELF is loaded under.
Prints the exit code and the output as hex.
";

/// A failure with its process exit code.
struct Failure {
    message: String,
    code: u8,
}

type CliResult<T> = Result<T, Failure>;

fn fail(message: impl Into<String>) -> Failure {
    Failure {
        message: message.into(),
        code: 1,
    }
}

fn usage_fail(message: impl Into<String>) -> Failure {
    Failure {
        message: message.into(),
        code: 2,
    }
}

impl From<om_sdk::SdkError> for Failure {
    fn from(e: om_sdk::SdkError) -> Failure {
        fail(e.to_string())
    }
}

/// Parsed `--name value` flags of one subcommand.
struct Flags {
    values: HashMap<String, String>,
    help: bool,
}

impl Flags {
    fn parse(args: &[String], allowed: &[&str]) -> CliResult<Flags> {
        let mut values = HashMap::new();
        let mut help = false;
        let mut it = args.iter();
        while let Some(arg) = it.next() {
            match arg.as_str() {
                "--help" | "-h" => help = true,
                name if name.starts_with("--") => {
                    let name = &name[2..];
                    if !allowed.contains(&name) {
                        return Err(usage_fail(format!("unknown option --{name}")));
                    }
                    let Some(value) = it.next() else {
                        return Err(usage_fail(format!("option --{name} needs a value")));
                    };
                    if values.insert(name.to_string(), value.clone()).is_some() {
                        return Err(usage_fail(format!("option --{name} given twice")));
                    }
                }
                other => return Err(usage_fail(format!("unexpected argument {other:?}"))),
            }
        }
        Ok(Flags { values, help })
    }

    fn get(&self, name: &str) -> Option<&str> {
        self.values.get(name).map(String::as_str)
    }

    fn required(&self, name: &str) -> CliResult<&str> {
        self.get(name)
            .ok_or_else(|| usage_fail(format!("missing required option --{name}")))
    }

    fn parse_or<T: std::str::FromStr>(&self, name: &str, default: T) -> CliResult<T> {
        match self.get(name) {
            None => Ok(default),
            Some(v) => v
                .parse::<T>()
                .map_err(|_| usage_fail(format!("option --{name}: invalid number {v:?}"))),
        }
    }
}

fn read_file(path: &str) -> CliResult<Vec<u8>> {
    std::fs::read(path).map_err(|e| fail(format!("cannot read {path}: {e}")))
}

fn write_file(path: &str, bytes: &[u8]) -> CliResult<()> {
    std::fs::write(path, bytes).map_err(|e| fail(format!("cannot write {path}: {e}")))
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// ABI parameters from the shared `--*-log-words`/`--hash` flags.
fn abi_params(flags: &Flags) -> CliResult<AbiParams> {
    let d = AbiParams::default();
    let hash_profile = match flags.get("hash").unwrap_or("sha256") {
        "sha256" => Hasher::Sha256,
        "sha3-256" => Hasher::Sha3_256,
        "sha384" => Hasher::Sha384,
        other => {
            return Err(usage_fail(format!(
                "unknown --hash {other:?} (sha256 | sha3-256 | sha384)"
            )));
        }
    };
    Ok(AbiParams {
        ram_log_words: flags.parse_or("ram-log-words", d.ram_log_words)?,
        input_log_words: flags.parse_or("input-log-words", d.input_log_words)?,
        output_log_words: flags.parse_or("output-log-words", d.output_log_words)?,
        max_code_words: flags.parse_or("max-code-words", d.max_code_words)?,
        hash_profile,
    })
}

fn cmd_keygen(args: &[String]) -> CliResult<()> {
    let flags = Flags::parse(
        args,
        &[
            "elf",
            "out",
            "profile",
            "pcs",
            "hash",
            "pcs-r",
            "pcs-t",
            "ram-log-words",
            "input-log-words",
            "output-log-words",
            "max-code-words",
        ],
    )?;
    if flags.help {
        print!("{KEYGEN_USAGE}");
        return Ok(());
    }
    let elf_path = flags.required("elf")?.to_string();
    let out_path = flags.required("out")?.to_string();
    let pcs = match flags.get("pcs").unwrap_or("ligerito") {
        "ligerito" => PcsMode::Ligerito,
        // "transparent" is the protocol name of the mock (§11.10 #8).
        "mock" | "transparent" => PcsMode::Transparent,
        other => {
            return Err(usage_fail(format!(
                "unknown --pcs {other:?} (ligerito | mock)"
            )));
        }
    };
    let pcs_profile = match flags.get("profile").unwrap_or("provable-120") {
        "provable-120" => PcsProfile::Provable120,
        "test" => PcsProfile::Test,
        other => {
            return Err(usage_fail(format!(
                "unknown --profile {other:?} (provable-120 | test)"
            )));
        }
    };
    // The reference test vk uses pcs_t = 8 (Python `make_vk`).
    let default_t = if pcs_profile == PcsProfile::Test {
        8
    } else {
        0
    };
    let params = SdkParams {
        abi: abi_params(&flags)?,
        pcs,
        pcs_profile,
        pcs_r: flags.parse_or("pcs-r", 2)?,
        pcs_t: flags.parse_or("pcs-t", default_t)?,
    };
    let elf = read_file(&elf_path)?;
    let vk = om_sdk::keygen_from_elf(&elf, &params)?;
    let blob = encode_vk(&vk);
    let digest = vk.digest();
    write_file(&out_path, &blob)?;
    println!("vk_digest: {}", hex(&digest));
    println!("vk_bytes: {}", blob.len());
    Ok(())
}

fn cmd_prove(args: &[String]) -> CliResult<()> {
    let flags = Flags::parse(
        args,
        &["vk", "elf", "out", "input", "instance", "max-cycles"],
    )?;
    if flags.help {
        print!("{PROVE_USAGE}");
        return Ok(());
    }
    let vk_path = flags.required("vk")?.to_string();
    let elf_path = flags.required("elf")?.to_string();
    let out_path = flags.required("out")?.to_string();
    let vk = decode_vk(&read_file(&vk_path)?).map_err(om_sdk::SdkError::from)?;
    let elf = read_file(&elf_path)?;
    let input = match flags.get("input") {
        Some(p) => read_file(p)?,
        None => Vec::new(),
    };
    let max_cycles: usize = flags.parse_or("max-cycles", om_sdk::DEFAULT_MAX_CYCLES)?;
    let (instance, proof_blob) = om_sdk::prove_with_max_cycles(&vk, &elf, &input, max_cycles)?;
    write_file(&out_path, &proof_blob)?;
    if let Some(inst_path) = flags.get("instance") {
        write_file(inst_path, &encode_instance(&instance))?;
    }
    println!("T: {}", instance.t);
    println!("exit_code: {}", instance.exit_code);
    println!("input_len: {}", instance.input.len());
    println!("output_len: {}", instance.output.len());
    println!("proof_bytes: {}", proof_blob.len());
    if flags.get("instance").is_none() {
        println!("input: {}", hex(&instance.input));
        println!("output: {}", hex(&instance.output));
    }
    Ok(())
}

fn cmd_verify(args: &[String]) -> CliResult<()> {
    let flags = Flags::parse(args, &["vk", "instance", "proof"])?;
    if flags.help {
        print!("{VERIFY_USAGE}");
        return Ok(());
    }
    let vk = decode_vk(&read_file(flags.required("vk")?)?).map_err(om_sdk::SdkError::from)?;
    let instance = decode_instance(&read_file(flags.required("instance")?)?)
        .map_err(om_sdk::SdkError::from)?;
    let proof_blob = read_file(flags.required("proof")?)?;
    om_sdk::verify(&vk, &instance, &proof_blob)?;
    println!("OK");
    Ok(())
}

fn cmd_run(args: &[String]) -> CliResult<()> {
    let flags = Flags::parse(
        args,
        &[
            "elf",
            "input",
            "hash",
            "ram-log-words",
            "input-log-words",
            "output-log-words",
            "max-code-words",
            "max-cycles",
        ],
    )?;
    if flags.help {
        print!("{RUN_USAGE}");
        return Ok(());
    }
    let elf = read_file(flags.required("elf")?)?;
    let input = match flags.get("input") {
        Some(p) => read_file(p)?,
        None => Vec::new(),
    };
    // Execution runs the program bound in a vk; keygen under the
    // requested ABI parameters is how the ELF gets loaded (§14.2).
    // The PCS fields are irrelevant without proving.
    let params = SdkParams::default().with_abi(abi_params(&flags)?);
    let vk = om_sdk::keygen_from_elf(&elf, &params)?;
    let max_cycles: usize = flags.parse_or("max-cycles", om_sdk::DEFAULT_MAX_CYCLES)?;
    let (output, exit_code) = om_sdk::execute_with_max_cycles(&vk, &elf, &input, max_cycles)?;
    println!("exit_code: {exit_code}");
    println!("output_len: {}", output.len());
    println!("output: {}", hex(&output));
    Ok(())
}

fn dispatch(args: &[String]) -> CliResult<()> {
    let Some(cmd) = args.first() else {
        return Err(usage_fail("missing command"));
    };
    match cmd.as_str() {
        "--help" | "-h" | "help" => {
            print!("{USAGE}");
            Ok(())
        }
        "keygen" => cmd_keygen(&args[1..]),
        "prove" => cmd_prove(&args[1..]),
        "verify" => cmd_verify(&args[1..]),
        "run" => cmd_run(&args[1..]),
        other => Err(usage_fail(format!("unknown command {other:?}"))),
    }
}

#[global_allocator]
static ALLOC: om_sdk::memtrace::CountingAlloc = om_sdk::memtrace::CountingAlloc;

fn main() -> ExitCode {
    om_sdk::memtrace::CountingAlloc::enable_from_env();
    let args: Vec<String> = std::env::args().skip(1).collect();
    match dispatch(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(f) => {
            eprintln!("error: {}", f.message);
            if f.code == 2 {
                eprint!("{USAGE}");
            }
            ExitCode::from(f.code)
        }
    }
}
