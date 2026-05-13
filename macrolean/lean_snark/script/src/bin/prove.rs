//! SP1 host program.
//!
//! Modes:
//!     <path>                          execute only (no proof)
//!     <path> --prove                  Core STARK proof (succinct, NOT zk)
//!     <path> --plonk                  zk-Plonk SNARK (zero-knowledge)
//!     <path> --groth16                zk-Groth16 SNARK (zero-knowledge)
//!
//! `--prove` (Core) is the default proving mode used for fast iteration —
//! the proof is succinct and publicly verifiable but does NOT hide the
//! witness (`flat_bytes`). `--plonk` and `--groth16` wrap the Core proof
//! in a SNARK that SP1 explicitly documents as zero-knowledge in
//! `sp1-verifier/src/{plonk,groth16}/mod.rs`. They take significantly longer
//! to generate but produce a constant-size proof and hide the witness.

use std::time::Instant;

use sp1_sdk::{
    blocking::{ProveRequest, Prover, ProverClient},
    include_elf, Elf, ProvingKey, SP1Stdin,
};

/// The ELF file for the SP1 guest — emitted by `script/build.rs`. The string
/// here must match the `name` of the guest's `[package]` in
/// `program/Cargo.toml` (`lean-snark-program`).
const LEAN_SNARK_ELF: Elf = include_elf!("lean-snark-program");

fn main() {
    sp1_sdk::utils::setup_logger();
    dotenv::dotenv().ok();

    let argv: Vec<String> = std::env::args().collect();
    let export_path = match argv.get(1) {
        Some(p) if !p.starts_with("--") => p.clone(),
        _ => {
            eprintln!(
                "Usage: {} <path-to-export-file> [--prove | --plonk | --groth16]",
                argv[0]
            );
            std::process::exit(2);
        }
    };

    #[derive(Clone, Copy, Debug)]
    enum ProveMode {
        Execute,
        Core,
        Plonk,
        Groth16,
    }
    let mode = if argv.iter().any(|a| a == "--groth16") {
        ProveMode::Groth16
    } else if argv.iter().any(|a| a == "--plonk") {
        ProveMode::Plonk
    } else if argv.iter().any(|a| a == "--prove") {
        ProveMode::Core
    } else {
        ProveMode::Execute
    };
    println!("Mode: {mode:?}");

    let ndjson_bytes = std::fs::read(&export_path).unwrap_or_else(|e| {
        eprintln!("failed to read {export_path}: {e}");
        std::process::exit(1);
    });
    println!("Read export file: {} bytes (NDJSON)", ndjson_bytes.len());

    // Flatten on the host: parse the NDJSON, build an `ExportFile`, bincode it
    // into a compact flat blob. The guest then skips JSON parsing entirely.
    let t = Instant::now();
    let flat_bytes = nanoda_lib::zkvm_entry::ndjson_to_flat_bytes(&ndjson_bytes)
        .expect("failed to flatten NDJSON");
    println!(
        "Flattened on host in {:.2?}: {} bytes ({}% of NDJSON)",
        t.elapsed(),
        flat_bytes.len(),
        (flat_bytes.len() * 100) / ndjson_bytes.len().max(1),
    );

    // For provenance: independently compute what the guest's `input_hash`
    // commitment should be. Done BEFORE we move `flat_bytes` into stdin
    // so we can cross-check the public-output hash matches.
    let host_side_input_hash: [u8; 32] = {
        use sha2::{Digest, Sha256};
        Sha256::digest(&flat_bytes).into()
    };

    // `write_vec` is SP1's fast byte-slice path — pairs with `read_vec` in the
    // guest.
    let mut stdin = SP1Stdin::new();
    stdin.write_vec(flat_bytes);

    let t = Instant::now();
    let client = ProverClient::from_env();
    println!("[timing] ProverClient::from_env in {:.2?}", t.elapsed());

    match mode {
        ProveMode::Execute => {
            let t = Instant::now();
            let (mut output, report) = client
                .execute(LEAN_SNARK_ELF, stdin)
                .run()
                .expect("execution failed");
            println!("Execution succeeded in {:.2?}", t.elapsed());
            println!("Cycle count: {}", report.total_instruction_count());

            // Public-values size (no proof generated in execute mode).
            print_sizes(None, output.as_slice().len(), None);

            let input_hash = output.read::<[u8; 32]>();
            let theorem_anchor = output.read::<[u8; 32]>();
            let num_checked = output.read::<u64>();
            print_public_output(&input_hash, &theorem_anchor, num_checked, &host_side_input_hash);
        }

        ProveMode::Core | ProveMode::Plonk | ProveMode::Groth16 => {
            let t = Instant::now();
            let pk = client.setup(LEAN_SNARK_ELF).expect("failed to setup elf");
            println!("[timing] client.setup (proving key gen) in {:.2?}", t.elapsed());

            let t = Instant::now();
            let mut proof = match mode {
                ProveMode::Core => client.prove(&pk, stdin).run(),
                ProveMode::Plonk => client.prove(&pk, stdin).plonk().run(),
                ProveMode::Groth16 => client.prove(&pk, stdin).groth16().run(),
                ProveMode::Execute => unreachable!(),
            }
            .expect("proof generation failed");
            println!(
                "[timing] client.prove ({mode:?}) in {:.2?}",
                t.elapsed()
            );

            let t = Instant::now();
            client
                .verify(&proof, pk.verifying_key(), None)
                .expect("proof verification failed");
            println!("[timing] client.verify in {:.2?}", t.elapsed());

            // Measure on-wire sizes BEFORE we destructively read public values
            // (read::<T>() advances the internal cursor; as_slice() is fine).
            let proof_size = bincode::serialize(&proof)
                .map(|b| b.len())
                .unwrap_or(0);
            let pv_size = proof.public_values.as_slice().len();
            let vk_size = bincode::serialize(pk.verifying_key())
                .map(|b| b.len())
                .unwrap_or(0);
            print_sizes(Some(proof_size), pv_size, Some(vk_size));

            let input_hash = proof.public_values.read::<[u8; 32]>();
            let theorem_anchor = proof.public_values.read::<[u8; 32]>();
            let num_checked = proof.public_values.read::<u64>();
            print_public_output(&input_hash, &theorem_anchor, num_checked, &host_side_input_hash);

            match mode {
                ProveMode::Core => {
                    println!(
                        "Note: Core mode produces a SUCCINCT proof — it is NOT zero-knowledge. \
                         The witness (flat_bytes) is committed to in the trace and recoverable. \
                         Use --plonk or --groth16 for zk."
                    );
                }
                ProveMode::Plonk | ProveMode::Groth16 => {
                    println!(
                        "Note: {mode:?} mode produces a zero-knowledge SNARK \
                         (per `sp1-verifier/src/{}/mod.rs`).",
                        match mode {
                            ProveMode::Plonk => "plonk",
                            ProveMode::Groth16 => "groth16",
                            _ => unreachable!(),
                        }
                    );
                }
                _ => {}
            }
        }
    }
}

fn print_public_output(
    input_hash: &[u8; 32],
    theorem_anchor: &[u8; 32],
    num_checked: u64,
    host_side_input_hash: &[u8; 32],
) {
    println!("Public output:");
    println!("  input_hash     = {}", hex(input_hash));
    println!("  theorem_anchor = {}", hex(theorem_anchor));
    println!("  num_declars    = {num_checked}");
    if input_hash != host_side_input_hash {
        eprintln!(
            "WARNING: input_hash mismatch! host computed {}",
            hex(host_side_input_hash)
        );
    }
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

/// Render a byte count in either bytes, KB, or MB depending on magnitude.
fn fmt_size(n: usize) -> String {
    if n < 1024 {
        format!("{n} bytes")
    } else if n < 1024 * 1024 {
        format!("{:.2} KB ({n} bytes)", n as f64 / 1024.0)
    } else {
        format!("{:.2} MB ({n} bytes)", n as f64 / (1024.0 * 1024.0))
    }
}

/// Print proof/public-values/vk sizes in a uniform block, with `--` for fields
/// not present in execute mode. Grep-friendly for the pipeline's summary table.
fn print_sizes(proof_size: Option<usize>, pv_size: usize, vk_size: Option<usize>) {
    println!("Sizes:");
    match proof_size {
        Some(n) => println!("  proof          = {}", fmt_size(n)),
        None    => println!("  proof          = -- (execute mode, no proof generated)"),
    }
    println!("  public_values  = {}", fmt_size(pv_size));
    match vk_size {
        Some(n) => println!("  verifying_key  = {}", fmt_size(n)),
        None    => println!("  verifying_key  = -- (execute mode)"),
    }
}
