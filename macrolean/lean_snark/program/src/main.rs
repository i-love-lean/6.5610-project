//! SP1 guest program.
//!
//! Reads a *flat* (bincode-encoded) representation of a Lean 4 export from
//! the host, hashes the bytes, validates + type-checks every declaration,
//! and commits three values to the SP1 public output:
//!
//! 1. `input_hash`: SHA-256 of the input bytes (Layer 2). Binds the SNARK to
//!    a specific blob; combined with deterministic `ndjson_to_flat_bytes`,
//!    binds the SNARK to a specific NDJSON.
//! 2. `theorem_anchor`: SHA-256 over the canonical encoding of the
//!    user-facing theorem's name + type (Layer 4). Binds the SNARK to a
//!    specific theorem statement, independent of DAG layout.
//! 3. `num_declars`: declaration count (informational).
//!
//! Layers 1 (Config pin) and 5 (size cap) live inside
//! `nanoda_lib::zkvm_entry::check_and_anchor_flat_bytes`.

#![no_main]
sp1_zkvm::entrypoint!(main);

use sha2::{Digest, Sha256};

pub fn main() {
    // SP1 fast byte-slice path; pairs with `stdin.write_vec` on the host.
    let flat_bytes: Vec<u8> = sp1_zkvm::io::read_vec();

    // Layer 2: hash input bytes BEFORE doing anything else, so the
    // committed hash is over exactly what the guest received. Even if the
    // type-check later panics, this commit doesn't make it to the proof
    // (a panicking guest produces no proof) — but we want the hash logic
    // to be obviously independent of the rest.
    let input_hash: [u8; 32] = Sha256::digest(&flat_bytes).into();
    sp1_zkvm::io::commit(&input_hash);

    // Layers 1 + 4 + 5: validate, type-check, anchor.
    let outcome = nanoda_lib::zkvm_entry::check_and_anchor_flat_bytes(&flat_bytes)
        .expect("type checking failed");

    sp1_zkvm::io::commit(&outcome.theorem_anchor);
    sp1_zkvm::io::commit(&outcome.num_declars);
}
