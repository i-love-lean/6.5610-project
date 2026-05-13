//! Native sanity-check.
//!
//! Runs the modified `nanoda_lib` type-checker on a Lean 4 export file via
//! the NDJSON path, the flat-blob path, and the combined check+anchor path.
//! Cross-checks declaration counts and prints the resulting input hash and
//! theorem anchor — same values the SP1 guest will commit.
//!
//! Usage:
//!     cargo run --release --bin check_native -- <path-to-export>

use std::time::Instant;

use sha2::{Digest, Sha256};

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: check_native <path-to-export>");
        std::process::exit(2);
    });

    let read_start = Instant::now();
    let bytes = std::fs::read(&path).unwrap_or_else(|e| {
        eprintln!("failed to read {path}: {e}");
        std::process::exit(1);
    });
    println!("read {} bytes from {path} in {:?}", bytes.len(), read_start.elapsed());

    // Path 1: NDJSON straight into the type-checker.
    let t = Instant::now();
    let n_json = nanoda_lib::zkvm_entry::check_export_from_bytes(&bytes).unwrap_or_else(|e| {
        eprintln!("NDJSON path FAILED after {:?}: {e}", t.elapsed());
        std::process::exit(1);
    });
    println!("NDJSON path: {n_json} declarations in {:?}", t.elapsed());

    // Path 2: NDJSON -> flat blob -> simple type-check.
    let t = Instant::now();
    let flat_bytes = nanoda_lib::zkvm_entry::ndjson_to_flat_bytes(&bytes).unwrap_or_else(|e| {
        eprintln!("ndjson_to_flat_bytes FAILED: {e}");
        std::process::exit(1);
    });
    println!("flat blob: {} bytes (NDJSON was {})", flat_bytes.len(), bytes.len());
    let t2 = Instant::now();
    let n_flat =
        nanoda_lib::zkvm_entry::check_export_from_flat_bytes(&flat_bytes).unwrap_or_else(|e| {
            eprintln!("flat path FAILED after {:?}: {e}", t2.elapsed());
            std::process::exit(1);
        });
    println!(
        "flat path: {n_flat} declarations in {:?} (+{:?} flatten)",
        t2.elapsed(),
        t.elapsed() - t2.elapsed()
    );

    // Path 3: combined check + anchor — same code path the SP1 guest runs.
    let t = Instant::now();
    let outcome = nanoda_lib::zkvm_entry::check_and_anchor_flat_bytes(&flat_bytes)
        .unwrap_or_else(|e| {
            eprintln!("check_and_anchor FAILED after {:?}: {e}", t.elapsed());
            std::process::exit(1);
        });
    println!(
        "check+anchor: {} declarations in {:?}",
        outcome.num_declars,
        t.elapsed()
    );

    let input_hash: [u8; 32] = Sha256::digest(&flat_bytes).into();
    println!("public commitments (what the guest will commit):");
    println!("  input_hash     = {}", hex(&input_hash));
    println!("  theorem_anchor = {}", hex(&outcome.theorem_anchor));
    println!("  num_declars    = {}", outcome.num_declars);

    if n_json != n_flat || (n_flat as u64) != outcome.num_declars {
        eprintln!(
            "MISMATCH: NDJSON={n_json} flat={n_flat} check+anchor={}",
            outcome.num_declars
        );
        std::process::exit(1);
    }
    println!("OK: all paths agree on {n_json} declarations.");
}
