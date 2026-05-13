# Lean 4 proofs as zk-SNARKs

A research project that takes a Lean 4 theorem with its proof, runs it through
a Rust implementation of Lean's kernel inside an SP1 zkVM, and produces a
zero-knowledge SNARK certifying that the proof type-checks. Built for MIT
6.5610.

The SNARK lets a verifier confirm "this Lean theorem statement has a proof"
without ever seeing the proof itself, in ~272 ms of verification work and
~1.5 KB of on-chain bytes.

---

## What this does

End to end:

1. Write a theorem `theorem T : τ := <proof>` in Lean 4.
2. `lean4export` serialises `T` plus its transitive kernel-level
   dependencies (constructors, recursors, definitions) as NDJSON.
3. A modified fork of [`nanoda_lib`](https://github.com/ammkrn/nanoda_lib)
   (a Rust port of Lean 4's kernel) type-checks every declaration.
4. That type-checker is compiled to RISC-V and run inside [SP1's
   zkVM](https://docs.succinct.xyz). SP1 emits a STARK proof of the
   execution.
5. Optionally, the STARK is wrapped via gnark's Plonk-BN254 backend into a
   constant-size zero-knowledge SNARK.
6. The guest commits three values to the public output: the SHA-256 of
   the input bytes, a canonical content-hash of the theorem statement, and
   the declaration count.

A verifier with the original Lean theorem statement can independently
recompute the theorem-statement hash and check it matches the SNARK's
public output — without ever seeing the proof body.

---

## Map of the project

```
6.5610/project/
├── README.md                ← (this file)
├── BENCHMARKS.md            ← cycle counts, wall times, soundness layers
├── run_pipeline.sh          ← end-to-end driver: lean → ndjson → flat → SP1 → proof
│
├── lean-example/            ← the Lean 4 project with our test theorems
│   ├── MyProject/
│   │   └── Basic.lean         our theorem statements (my_and_comm, thm1, etc.)
│   ├── MyProject.lean         root module
│   ├── Main.lean              CLI entry (unused; just makes Lake happy)
│   ├── exports/               *.ndjson written here by lean4export
│   ├── lakefile.toml
│   └── lean-toolchain
│
├── lean4export/             ← vendored exporter, lean → NDJSON
│   ├── Export.lean            exporter implementation
│   └── format_ndjson.md       NDJSON schema spec
│
├── nanoda_lib/              ← upstream reference clone (UNMODIFIED)
│   └── src/...                kept for `diff`ing against our fork; the
│                              actively-used copy lives at lean_snark/nanoda_lib/
│
└── lean_snark/              ← the SP1 host + guest + forked nanoda_lib
    ├── Cargo.toml             workspace (program + script; nanoda_lib is a path dep)
    ├── rust-toolchain
    │
    ├── program/             ← SP1 GUEST — compiled to RISC-V, executed inside the zkVM
    │   ├── Cargo.toml
    │   └── src/main.rs        ~30 lines: read input, hash, type-check, commit
    │
    ├── script/              ← SP1 HOST — runs natively on your laptop
    │   ├── build.rs           builds the guest as a side-effect
    │   └── src/bin/
    │       ├── prove.rs       execute / Core STARK / zk-Plonk / zk-Groth16
    │       └── check_native.rs    pure-native sanity check, no zkVM
    │
    └── nanoda_lib/          ← FORK of nanoda_lib, modified for SP1 compatibility
        ├── src/
        │   ├── tc.rs              kernel: inference, defeq, all reductions
        │   ├── inductive.rs       inductive type checking
        │   ├── quot.rs            quotient type rules
        │   ├── expr.rs            term data model
        │   ├── level.rs           universe levels
        │   ├── name.rs            hierarchical names
        │   ├── env.rs             declarations + environment
        │   ├── parser.rs          NDJSON parser (host-only path now)
        │   ├── util.rs            Ptr, LeanDag, TcCtx, Config
        │   ├── flat.rs            (new) flat binary blob (de)serialisation
        │   ├── anchor.rs          (new) canonical hash of theorem statement
        │   ├── zkvm_entry.rs      (new) SP1 entry point + axiom whitelist + size caps
        │   ├── union_find.rs      defeq cache
        │   └── unique_hasher.rs
        └── LICENSE                Apache-2.0 (preserved from upstream)
```

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                          HOST (your laptop)                      │
│                                                                  │
│   Lean source ──lake build──▶ .olean ──lean4export──▶ NDJSON     │
│                                                          │       │
│                                          ndjson_to_flat_bytes    │
│                                                          │       │
│                                          ┌───────────────▼─────┐ │
│                                          │  flat_bytes (bincode│ │
│                                          │   of FlatExportFile)│ │
│                                          └───────────┬─────────┘ │
│                                                      │           │
│                                          sp1_sdk: prove          │
│                                                      │           │
│   ┌──────────────────────────────────────────────────▼─────────┐ │
│   │              GUEST (RISC-V, inside SP1 zkVM)               │ │
│   │                                                            │ │
│   │   sp1_zkvm::io::read_vec()  ───▶  flat_bytes               │ │
│   │   sha256(flat_bytes)        ──┐                             │ │
│   │   commit(input_hash)         │                              │ │
│   │                              │                              │ │
│   │   bincode::deserialize       │                              │ │
│   │      ↓                       │                              │ │
│   │   pin Config + size caps     │                              │ │
│   │      ↓                       │                              │ │
│   │   FlatExportFile::into_export_file()  → ExportFile<'p>     │ │
│   │      ↓                       │                              │ │
│   │   validate_axioms (whitelist)│                              │ │
│   │      ↓                       │                              │ │
│   │   ExportFile::check_all_declars()  ← THE TYPE-CHECK         │ │
│   │      ↓                       │                              │ │
│   │   anchor::last_declaration_anchor()                         │ │
│   │   commit(theorem_anchor)                                    │ │
│   │   commit(num_declars)                                       │ │
│   └────────────────────────┬───────────────────────────────────┘ │
│                            ▼                                      │
│   ┌──────────────────────────────────────────────────────────┐   │
│   │  Core STARK proof  ──shrink──▶ wrap STARK ──gnark──▶     │   │
│   │  zk-Plonk SNARK  (~4 KB wrapped, constant size)          │   │
│   └──────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                                │
                                ▼
                       Verifier checks proof
                       (272 ms) + independently
                       recomputes theorem_anchor
                       from their copy of T.
```

The two halves of every SP1 project:

| | Host | Guest |
|---|---|---|
| Runs as | Native binary on your laptop | RISC-V binary inside the SP1 emulator |
| Cost | Free (your CPU) | Every instruction becomes constraints in the proof |
| Capabilities | Full OS — files, network, threads | Deterministic; one input channel + one public-output channel |
| Trust | None — host can do whatever | The SNARK certifies exactly what the guest does |
| Lives in | `lean_snark/script/` | `lean_snark/program/` |

`nanoda_lib` is compiled into **both** sides: natively (for the host's
`ndjson_to_flat_bytes` and `check_native` helpers) and to RISC-V (linked into
the guest ELF).

---

## Quick start

### Prerequisites

```zsh
# Rust toolchain (managed by lean_snark/rust-toolchain)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# SP1 toolchain
curl -L https://sp1.succinct.xyz | bash
sp1up

# Lean 4 toolchain (elan/lake; lean-toolchain pins the version)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### One-time setup

```zsh
# Build the Lean exporter
cd lean4export && lake build && cd ..

# Build SP1 host + guest binaries (also fetches dependencies)
cd lean_snark && cargo build --release --manifest-path script/Cargo.toml && cd ..
```

### Run end to end

```zsh
# From the repo root. Builds Lean, exports the theorem, runs native check,
# then SP1 execute.
./run_pipeline.sh MyProject.Basic my_and_comm

# Generate an actual Core STARK proof (succinct, ~14 s on a laptop, NOT zk):
./run_pipeline.sh MyProject.Basic my_and_comm --prove

# Generate a real zk-Plonk SNARK (~22 min first run including 3 GB download):
./run_pipeline.sh MyProject.Basic my_and_comm --plonk

# Run everything in sequence (execute + Core + Plonk + Groth16):
./run_pipeline.sh MyProject.Basic my_and_comm --all
```

Each run produces:
- `lean-example/exports/<decl>.ndjson` — the exported term DAG.
- `lean-example/exports/<decl>.bench.txt` — the raw log from this run.
- A summary table printed to stdout with cycle count, wall time, proof size,
  and the committed public values.

### Example theorems

Already wired up in [`lean-example/MyProject/Basic.lean`](lean-example/MyProject/Basic.lean):

| Theorem | Statement | NDJSON | Declars |
|---|---|---:|---:|
| `my_and_comm` | `(p q : Prop) (h : p ∧ q) : q ∧ p` | 5.5 KB | 6 |
| `thm1` | `¬¬¬A → ¬A` | 2.8 KB | ~5 |
| `and_comm_custom` | `a ∧ b ↔ b ∧ a` (zkPi-paper style) | 12 KB | ~15 |
| `nat_zero_add_comm` | `(n : Nat) : n + 0 = 0 + n` (by `simp`) | 58 KB | 57 |
| `add_comm_nat` | full term-mode `(n m : Nat) : n + m = m + n` | 61 KB | ~30 |

Adding your own: write a `theorem T : τ := <proof>` in
[`lean-example/MyProject/Basic.lean`](lean-example/MyProject/Basic.lean) (or
any file under `MyProject/`), then:

```zsh
./run_pipeline.sh MyProject.Basic T --prove
```

---

## What the SNARK proves

The literal cryptographic statement is:

> "I know an execution trace `W` such that the guest ELF (with hash `vk`) ran
> on `W`, halted cleanly, and the public-values digest committed by the
> program is exactly `H_pv = sha256(input_hash ‖ theorem_anchor ‖ num_declars)`."

Unfolded, given that the ELF is auditable and pinned by `vk`:

> "There exist input bytes `flat_bytes` with `sha256(flat_bytes) = input_hash`
> such that, after deserialisation, the rehydrated Lean environment is
> well-typed under the four whitelisted axioms (`propext`, `Classical.choice`,
> `Quot.sound`, `Lean.trustCompiler`), and the headline theorem's canonical
> statement hash is `theorem_anchor`."

The verifier checks:

1. The SNARK cryptographically verifies (intrinsic).
2. **Their** computation of `theorem_anchor` from the theorem statement they
   care about matches the public output. (Done by re-running [`anchor.rs`](lean_snark/nanoda_lib/src/anchor.rs)
   on a stub `theorem T : τ := sorry`.)
3. Optionally: **their** SHA-256 of the bytes that `ndjson_to_flat_bytes`
   produces on their NDJSON matches `input_hash`.

Together: "this SNARK certifies a Lean proof of *my* theorem statement,
type-checked under Lean's kernel rules."

### Soundness layering (security model)

Five hardening layers inside the guest, all enforced before type-checking
begins. See [`zkvm_entry.rs`](lean_snark/nanoda_lib/src/zkvm_entry.rs) for the
implementation.

| # | Layer | What it stops |
|---|---|---|
| 1 | **Pin Config** | Attacker can't set `unsafe_permit_all_axioms: true` in the blob |
| 2 | **`sha256(input)`** | Binds the SNARK to specific input bytes |
| 3 | **Axiom whitelist** | Rejects axioms outside the four-element Lean-kernel-primitive set |
| 4 | **Theorem anchor** | Binds the SNARK to a specific theorem statement |
| 5 | **Input-size caps** | DoS protection (256 MiB / 1 M declarations) |

The host-side `ndjson_to_flat_bytes` is tested for determinism in
[`tests/flat_determinism.rs`](lean_snark/nanoda_lib/tests/flat_determinism.rs).

### Trust assumptions

Whose correctness the verifier ultimately rests on:

| Component | Trust |
|---|---|
| `sp1-verifier` (on verifier's machine) | Audited Rust source; pin its version |
| The verifying key `vk` | Hash-pinned to a known-good guest ELF |
| The gnark Plonk circuit (encoding "STARK verifier accepts") | SP1 audits |
| The Plonk trusted-setup ceremony | ≥1 honest participant in Succinct's ceremony |
| `nanoda_lib` correctly implements Lean 4's kernel | Project-foundational; auditable |
| The four whitelisted axioms | Standard — Lean kernel primitives |
| `lean4` and `lean4export` | Standard Lean-pipeline assumption |
| Cryptographic primitives (BN254 pairings, SHA-256, FRI) | Industry-standard |

Nothing on the prover side is in the trusted base — a malicious prover
can refuse to produce proofs but cannot forge them.

---

## Performance

Snapshot on `my_and_comm` (laptop CPU, no GPU):

| Stage | Time | Notes |
|---|---|---|
| Native type-check (`check_native`) | 0.9 ms | `nanoda_lib` natively, no zkVM |
| SP1 execute (no proof) | 28 ms | RISC-V emulation, cycle count only |
| SP1 Core STARK | ~14 s | Succinct but NOT zk; ~2.7 MB proof |
| SP1 Compressed STARK | ~3 min | Constant-size STARK, no gnark wrap; not zk |
| SP1 zk-Plonk SNARK | ~13 min warm / ~22 min cold | ~4 KB wrapped, **zero-knowledge** |
| Verify Plonk SNARK | 272 ms | Constant time |

Cycle count for `my_and_comm`: **1,034,879** (with all five soundness
layers). About 213k cycles of that are SHA-256 + axiom validation + anchor
walk — the rest is actual Lean type-checking.

See [BENCHMARKS.md](BENCHMARKS.md) for the full breakdown, including
how cycles changed across optimization steps (Option B / flat-blob, ThinLTO,
soundness hardening), and the comparison with zkPi's hand-arithmetised
approach.

---

## Comparison with prior work

### zkPi (Stanford, ACM CCS 2024) — different architecture

zkPi hand-arithmetises Lean's kernel rules directly as R1CS constraints,
then proves each theorem via the Mirage SNARK system. For their
`and.comm` theorem: **32 s prove + 79 s per-theorem setup, 592 k
constraints**.

Our approach uses SP1's general-purpose zkVM: compile `nanoda_lib` to
RISC-V, prove "this RISC-V trace is valid." For the same theorem class:
**14 s Core / ~13 min Plonk, 27.6 M PLONK constraints** for the gnark wrap.

The trade-off in one sentence: zkPi pays per-theorem compile cost but
gets very tight constraints; we amortise the constraints across any
program but pay zkVM overhead per cycle. zkPi wins on a single small
theorem; the zkVM approach scales better across many theorems, swaps
language (Coq, Agda, etc.) trivially, and runs *any* Rust verifier code
not just Lean's kernel.

---

## Modifications to `nanoda_lib` (the fork)

The upstream `nanoda_lib` runs on a native OS and was modified for SP1
compatibility. Three categories of changes:

1. **Stripping non-zkVM machinery** — removed pretty-printer
   (`pretty_printer.rs`), debug-printer (`debug_printer.rs`), CLI binary
   (`main.rs`), filesystem-config-loader (`Config::TryFrom<&Path>`), and
   all pretty-printer-related fields on `Config`.
2. **Dropping to single-threaded execution** — deleted
   `tc::check_all_declars_par`; the kernel-checking logic is unchanged,
   just no threads.
3. **Downgrading from NDJSON to a binary blob** — added serde derives to
   every kernel data type, a manual `Serialize`/`Deserialize` for `Ptr<A>`
   (needed because of the phantom-lifetime `PhantomData<A>`), a new
   `FlatExportFile` mirror of `ExportFile` for serialisation, and host /
   guest entry points (`ndjson_to_flat_bytes` and
   `check_export_from_flat_bytes`). Cuts cycles ~50% by moving JSON
   parsing to the host.

Plus the five soundness layers (Config pin, SHA-256 commit, axiom
whitelist, theorem anchor, input-size caps).

Net diff vs upstream: deleted ~1,200 lines (pretty-printer + threading),
added ~700 lines (`flat.rs` + `anchor.rs` + `zkvm_entry.rs`), modified
~150 lines (derives, Config trimming).

---

## Status

What works:

- ✓ End-to-end pipeline: Lean theorem → SNARK proof → verification.
- ✓ Soundness layers 1–5 (Config pin, hash, anchor, whitelist, size caps).
- ✓ All four SP1 modes (`execute`, Core, Plonk, Groth16).
- ✓ Determinism test for the host-side converter.
- ✓ Cross-checking that the NDJSON path and flat path produce identical
  declaration counts and anchors.

Limitations / future work:

- No GPU proving wired up (would cut Plonk time ~5–10×).
- No SP1 prover-network integration (would offload the gnark wrap entirely).
- Anchor is hardcoded to the *last* declaration; would be cleaner to let
  the user specify the theorem name explicitly.
- `Lean.trustCompiler` is whitelisted (matches mathlib); soundness-critical
  use cases should drop it.
- SHA-256 in the guest is software (not the SP1 precompile patch); ~200 k
  extra cycles per proof. One-line Cargo patch away.
- IndexSet rebuild during deserialisation rehashes; ~30% more cycles
  could be saved by skipping it.

See [BENCHMARKS.md §12](BENCHMARKS.md) for a more detailed caveats list.

---

## Reproducing the benchmarks

The numbers in `BENCHMARKS.md` were taken with the following workflow:

```zsh
# Tiny example (~14 s Core, ~13 min Plonk warm)
./run_pipeline.sh MyProject.Basic my_and_comm --all

# zkPi comparison theorem
./run_pipeline.sh MyProject.Basic and_comm_custom --prove

# Larger workload (`by simp`-heavy)
./run_pipeline.sh MyProject.Basic nat_zero_add_comm --prove
```

Numbers are laptop-class CPU (no GPU). Per-stage timings are printed by
`prove.rs`; the summary table in `run_pipeline.sh` aggregates them.

---

## Layout of the code path (where to start reading)

- **The 30-line guest** — [`lean_snark/program/src/main.rs`](lean_snark/program/src/main.rs).
  This is what the SNARK certifies, top to bottom.
- **The host program** — [`lean_snark/script/src/bin/prove.rs`](lean_snark/script/src/bin/prove.rs).
- **The guest entry point in nanoda_lib** —
  [`lean_snark/nanoda_lib/src/zkvm_entry.rs`](lean_snark/nanoda_lib/src/zkvm_entry.rs).
  Implements the five soundness layers.
- **The flat (de)serialisation** —
  [`lean_snark/nanoda_lib/src/flat.rs`](lean_snark/nanoda_lib/src/flat.rs).
  How the host's parsed `ExportFile` becomes a bincode blob and back.
- **The theorem anchor** —
  [`lean_snark/nanoda_lib/src/anchor.rs`](lean_snark/nanoda_lib/src/anchor.rs).
  Canonical content-hash of a theorem statement, walks the term DAG.
- **The Lean kernel** —
  [`lean_snark/nanoda_lib/src/tc.rs`](lean_snark/nanoda_lib/src/tc.rs).
  Inference, defeq, all reductions. Largely upstream `nanoda_lib`.

---

## Attributions

- [`nanoda_lib`](https://github.com/ammkrn/nanoda_lib) by ammkrn — the Rust
  Lean-4 kernel this project forks. Apache-2.0; LICENSE preserved at
  `lean_snark/nanoda_lib/LICENSE`.
- [`lean4export`](https://github.com/leanprover/lean4export) by the Lean
  community — the exporter we use to dump theorems as NDJSON.
- [SP1](https://github.com/succinctlabs/sp1) by Succinct Labs — the zkVM
  we run `nanoda_lib` inside, and the SNARK system we wrap with.
- [zkPi (Borgeaud et al., ACM CCS 2024)](https://eprint.iacr.org/2024/267)
  — prior work on zk-proofs of Lean theorems via custom arithmetisation.
  Different architecture, useful comparison point.

---

## License

This is a class project for MIT 6.5610 — no top-level license applied.
Vendored subdirectories retain their upstream licenses (Apache-2.0 for
`nanoda_lib/` and `lean_snark/nanoda_lib/`; see their respective
`LICENSE` files).
