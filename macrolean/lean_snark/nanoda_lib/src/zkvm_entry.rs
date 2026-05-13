//! In-memory entry point for the SP1 guest.
//!
//! The guest receives a byte slice containing a Lean 4 export and either
//! type-checks the NDJSON form directly (`check_export_from_bytes`, slow)
//! or the flat-blob form (`check_export_from_flat_bytes`, fast).
//!
//! ## Hardening notes (security layers 1–5)
//!
//! 1. **Pinned `Config`** — the guest *never* trusts the `Config` carried in
//!    the deserialised flat blob; it's overwritten with `default_zkvm_config()`
//!    before any type-checking runs.
//! 2. **Axiom whitelist** — after deserialisation, every `Declar::Axiom` is
//!    checked against `DEFAULT_PERMITTED_AXIOMS`. Anything outside that list
//!    causes a panic (which aborts proof generation).
//! 3. **Input-size cap** — the guest refuses inputs larger than `MAX_FLAT_BYTES`
//!    or with more than `MAX_DECLARS` declarations.
//! 4. **Input hash + theorem anchor** are committed by the guest's `main`;
//!    see `program/src/main.rs`. Determinism of `ndjson_to_flat_bytes` is
//!    covered by an integration test.

use std::error::Error;
use std::io::{BufReader, Cursor};

use crate::env::Declar;
use crate::flat::FlatExportFile;
use crate::parser::parse_export_file;
use crate::util::{Config, ExportFile, LeanDag, NamePtr};

/// The set of axioms we accept as a baseline — exactly Lean 4's kernel
/// primitives (`propext`, `Classical.choice`, `Quot.sound`,
/// `Lean.trustCompiler`). The blob's `Config` is ignored; this list is
/// enforced unconditionally inside the guest.
pub const DEFAULT_PERMITTED_AXIOMS: &[&str] = &[
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Lean.trustCompiler",
];

/// Hard cap on the size of a flat blob the guest will accept (256 MiB).
/// Anything bigger is rejected before deserialisation as a DoS guard.
pub const MAX_FLAT_BYTES: usize = 1 << 28;

/// Hard cap on the number of declarations in a flat blob (1 M). Beyond this
/// the proof would be impractical anyway; a low cap also makes the
/// post-deserialisation linear validation cheap.
pub const MAX_DECLARS: usize = 1_000_000;

/// Build the default `Config` used inside the zkVM guest. This is the policy
/// the guest enforces regardless of what the input blob claims.
pub fn default_zkvm_config() -> Config {
    Config {
        export_file_path: None,
        use_stdin: false,
        permitted_axioms: Some(
            DEFAULT_PERMITTED_AXIOMS.iter().map(|s| (*s).to_string()).collect(),
        ),
        // Layer 1: refuse unknown axioms outright, instead of silently
        // dropping them. Affects the host `parse_export_file` path; the
        // guest applies its own post-deserialisation check below.
        unpermitted_axiom_hard_error: true,
        nat_extension: true,
        string_extension: true,
        print_axioms: false,
        unsafe_permit_all_axioms: false,
    }
}

/// Parse the given NDJSON export bytes and type-check every declaration.
///
/// Returns the number of declarations that were successfully checked
/// (i.e. the size of the final declaration map). Any type-checking failure
/// inside `check_all_declars` panics, which in the SP1 guest aborts proof
/// generation — exactly the signal we want.
///
/// **For the SP1 guest, prefer [`check_export_from_flat_bytes`]** — running
/// JSON parsing inside the zkVM is expensive (every transient `String` and
/// `IndexSet` insert costs cycles in the proof). The flat path is ~3× cheaper.
pub fn check_export_from_bytes(export_bytes: &[u8]) -> Result<usize, Box<dyn Error>> {
    let config = default_zkvm_config();
    let reader = BufReader::new(Cursor::new(export_bytes));
    let (export_file, _skipped_axioms) = parse_export_file(reader, config)?;
    export_file.check_all_declars();
    Ok(export_file.declars.len())
}

// ---------------------------------------------------------------------------
// Flat-blob entry points: host parses NDJSON to a flat binary representation,
// guest deserialises it via bincode and calls `check_all_declars` directly.
// ---------------------------------------------------------------------------

/// Host-side helper: NDJSON bytes -> flat bincode blob.
///
/// Runs the full JSON parser, flattens the resulting `ExportFile`, and
/// bincode-serialises it. The output is what the SP1 guest reads via
/// [`check_export_from_flat_bytes`].
pub fn ndjson_to_flat_bytes(ndjson_bytes: &[u8]) -> Result<Vec<u8>, Box<dyn Error>> {
    let config = default_zkvm_config();
    let reader = BufReader::new(Cursor::new(ndjson_bytes));
    let (export_file, _skipped_axioms) = parse_export_file(reader, config)?;
    let flat = crate::flat::FlatExportFile::from_export_file(&export_file);
    Ok(bincode::serialize(&flat)?)
}

/// Guest-side entry: bincode-decode a `FlatExportFile`, rehydrate it into
/// an `ExportFile`, and type-check every declaration.
///
/// Implements security layers 1 (Config pin), 2/4 (caller hashes & anchors),
/// and 5 (size caps). The flow:
///
/// 1. Reject the input if it exceeds `MAX_FLAT_BYTES`.
/// 2. Bincode-deserialise into a `FlatExportFile`.
/// 3. **Pin the `Config`** to `default_zkvm_config()`, discarding whatever
///    the blob carried — otherwise an attacker could set
///    `unsafe_permit_all_axioms: true` and bypass the kernel's axiom check.
/// 4. Reject if the declaration count exceeds `MAX_DECLARS`.
/// 5. Rehydrate to an `ExportFile`.
/// 6. **Validate every `Declar::Axiom`** against the hard-coded whitelist.
///    The kernel's `check_declar` does NOT re-check axiom membership during
///    type-checking, so without this pass an attacker could ship a fake
///    axiom and the guest would happily accept it.
/// 7. Type-check.
pub fn check_export_from_flat_bytes(flat_bytes: &[u8]) -> Result<usize, Box<dyn Error>> {
    // Layer 5 — input size cap.
    if flat_bytes.len() > MAX_FLAT_BYTES {
        return Err(Box::from(format!(
            "flat blob too large: {} bytes (max {})",
            flat_bytes.len(),
            MAX_FLAT_BYTES
        )));
    }

    let mut flat: FlatExportFile = bincode::deserialize(flat_bytes)?;

    // Layer 1 — pin Config: ignore whatever the blob carried.
    flat.config = default_zkvm_config();

    // Layer 5 — declaration count cap.
    if flat.declars.len() > MAX_DECLARS {
        return Err(Box::from(format!(
            "too many declarations: {} (max {})",
            flat.declars.len(),
            MAX_DECLARS
        )));
    }

    let export_file: ExportFile<'_> = flat.into_export_file();

    // Layer 1 — axiom whitelist. The kernel doesn't enforce this, only the
    // parser does. After deserialisation we re-enforce it manually.
    validate_axioms(&export_file)?;

    export_file.check_all_declars();
    Ok(export_file.declars.len())
}

/// Walk the rehydrated `ExportFile`'s declar map and ensure that every
/// `Declar::Axiom` has a name in `DEFAULT_PERMITTED_AXIOMS`.
fn validate_axioms<'p>(ef: &ExportFile<'p>) -> Result<(), Box<dyn Error>> {
    let permitted: std::collections::HashSet<&'static str> =
        DEFAULT_PERMITTED_AXIOMS.iter().copied().collect();
    for (_n, declar) in &ef.declars {
        if let Declar::Axiom { info } = declar {
            let name = resolve_name(&ef.dag, info.name);
            if !permitted.contains(name.as_str()) {
                return Err(Box::from(format!(
                    "unpermitted axiom in flat blob: {name:?} (whitelist: {DEFAULT_PERMITTED_AXIOMS:?})"
                )));
            }
        }
    }
    Ok(())
}

/// Convenience wrapper around `flat::name_to_string` for the validation pass.
fn resolve_name<'p>(dag: &LeanDag<'p>, p: NamePtr<'p>) -> String {
    crate::flat::name_to_string(dag, p)
}

/// What the guest commits to the SP1 public output. The order of fields is
/// stable; verifiers `read::<[u8; 32]>()`, `read::<[u8; 32]>()`,
/// `read::<u64>()` in this order.
#[derive(Debug)]
pub struct GuestOutcome {
    /// Anchor for the user-facing theorem (the last declar in the export).
    /// Independent of NDJSON ordering and DAG layout — anchors only the
    /// statement (kind + name + universe params + type), not the proof.
    pub theorem_anchor: [u8; 32],
    /// Number of declarations admitted into the environment.
    pub num_declars: u64,
}

/// Guest-side end-to-end: validate, type-check, anchor.
///
/// Combines layers 1, 4, and 5. The caller (the SP1 guest) is responsible
/// for layer 2: hashing `flat_bytes` and committing the digest BEFORE
/// passing the bytes here. Doing the bytes-hash outside this function keeps
/// the input-binding commitment independent of the type-check logic.
pub fn check_and_anchor_flat_bytes(
    flat_bytes: &[u8],
) -> Result<GuestOutcome, Box<dyn Error>> {
    if flat_bytes.len() > MAX_FLAT_BYTES {
        return Err(Box::from(format!(
            "flat blob too large: {} bytes (max {})",
            flat_bytes.len(),
            MAX_FLAT_BYTES
        )));
    }
    let mut flat: FlatExportFile = bincode::deserialize(flat_bytes)?;
    flat.config = default_zkvm_config();
    if flat.declars.len() > MAX_DECLARS {
        return Err(Box::from(format!(
            "too many declarations: {} (max {})",
            flat.declars.len(),
            MAX_DECLARS
        )));
    }
    let export_file: ExportFile<'_> = flat.into_export_file();
    validate_axioms(&export_file)?;

    export_file.check_all_declars();

    // For an empty export there's nothing to anchor — commit the all-zero
    // sentinel so the public-output schema stays uniform. Verifiers should
    // treat all-zero as "no theorem anchored" and ignore.
    let theorem_anchor =
        crate::anchor::last_declaration_anchor(&export_file).unwrap_or([0u8; 32]);
    Ok(GuestOutcome {
        theorem_anchor,
        num_declars: export_file.declars.len() as u64,
    })
}
