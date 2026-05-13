# Lean → SP1 pipeline benchmarks

Reference for the cycle-count and wall-time measurements reported during
the Option B implementation. Numbers were taken on a single laptop in a
single sitting; treat as ballpark, not as a clean apples-to-apples study.

All commands assume this directory layout:

```
6.5610/project/
├── lean-example/         # the tiny Lean 4 project
├── lean4export/          # built lean4export binary
├── lean_snark/           # SP1 host + guest + nanoda_lib fork
└── nanoda_lib/           # original (untouched) clone
```

## 0. Prerequisites

```zsh
# rust-toolchain managed by lean_snark/rust-toolchain
rustup show

# SP1 toolchain
sp1up
cargo prove --version

# build lean4export once
cd 6.5610/project/lean4export && lake build && cd -
```

## 1. The three test inputs

| Name | Source | Bytes | Decls |
|---|---|---|---|
| `Empty` | `lean_snark/nanoda_lib/test_resources/Empty/export` | 176 | 0 |
| `ProjFromProp` (intentionally invalid) | `lean_snark/nanoda_lib/test_resources/ProjFromProp/export` | 4,509 | panics on declaration ~3 |
| `my_and_comm` | exported from `lean-example/MyProject/Basic.lean` | 5,468 | 6 |

Producing the `my_and_comm` export from scratch:

```zsh
cd 6.5610/project/lean-example

# 1. theorem in MyProject/Basic.lean:
#    theorem my_and_comm (p q : Prop) (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩

lake build

mkdir -p exports
lake env ../lean4export/.lake/build/bin/lean4export \
    MyProject.Basic -- my_and_comm \
    > exports/my_and_comm.ndjson
```

## 2. Build the SP1 binaries

```zsh
cd 6.5610/project/lean_snark
cargo build --release --manifest-path script/Cargo.toml
```

This compiles three binaries:

- `target/release/prove` — SP1 host (execute or generate proof).
- `target/release/check_native` — pure-native sanity check, no zkVM. Runs
  both the NDJSON path and the flat path and asserts they agree.
- The guest ELF is built by `script/build.rs` and embedded into `prove`.

## 3. Build profile

The cycle-count numbers below depend on what's in
`lean_snark/Cargo.toml`'s workspace `[profile.release]`. Two configurations
were measured:

```toml
# v0 — cargo release defaults (no [profile.release] block at all)
# opt-level=3, lto=off, codegen-units=16
```

```toml
# v1 — current setting (after the LTO experiment)
[profile.release]
opt-level = 3
lto = "thin"
codegen-units = 1
```

`lto = "fat"` triggers an LLVM RISC-V backend bug
(`error: symbol '.LJTI0_0' is already defined`) under `codegen-units = 1`;
ThinLTO avoids it and still gives most of the cross-crate inlining win.

## 4. NDJSON-path baseline (before Option B)

```zsh
# native sanity
./target/release/check_native ../lean-example/exports/my_and_comm.ndjson
# read 5468 bytes ... in 99µs
# OK: type-checked 6 declarations in 927µs

# SP1 execute (no proof, fast)
./target/release/prove ../lean-example/exports/my_and_comm.ndjson
# Read export file: 5468 bytes
# Execution succeeded in 43ms
# Cycle count: 1,758,250          <- v0 (no LTO)
# Cycle count: 1,548,471          <- v1 (thin LTO + cu=1)
# Declarations checked (from public output): 6

# SP1 prove + verify
./target/release/prove ../lean-example/exports/my_and_comm.ndjson --prove
# Proof generated in 18.74s
# Proof verified in 65.7ms
# Declarations checked (from public output): 6
```

```zsh
# Empty export (sanity)
./target/release/prove nanoda_lib/test_resources/Empty/export
# Execution succeeded in 8.7ms
# Cycle count: 39,754
# Declarations checked: 0

# Negative case — guest correctly panics
./target/release/prove nanoda_lib/test_resources/ProjFromProp/export
# panicked at nanoda_lib/src/tc.rs:444:21: infer_proj prop
# Cycle count: 1,139,940
# (host then errors trying to deserialize an empty public_value_stream — expected)
```

## 5. Flat-path measurements (after Option B)

After implementing `FlatExportFile` + `bincode`, the host parses NDJSON and
ships a flat blob; the guest deserialises with bincode and skips the JSON
parser entirely.

```zsh
# native cross-check: NDJSON path vs flat path
./target/release/check_native ../lean-example/exports/my_and_comm.ndjson
# read 5468 bytes ... in 284µs
# NDJSON path: 6 declarations in 372µs
# flat blob: 2918 bytes (NDJSON was 5468)
# flat path: 6 declarations in 128µs (+110µs flatten)
# OK: both paths agree on 6 declarations.

# SP1 execute on the flat path
./target/release/prove ../lean-example/exports/my_and_comm.ndjson
# Read export file: 5468 bytes (NDJSON)
# Flattened on host in 520µs: 2918 bytes (53% of NDJSON)
# Execution succeeded in 22ms
# Cycle count: 821,797
# Declarations checked: 6

# SP1 prove + verify on the flat path
./target/release/prove ../lean-example/exports/my_and_comm.ndjson --prove
# Flattened on host in 207µs: 2918 bytes (53% of NDJSON)
# Proof generated in 14.03s
# Proof verified in 58.5ms
# Declarations checked: 6
```

```zsh
# Empty
./target/release/prove nanoda_lib/test_resources/Empty/export
# Flattened on host in 115µs: 172 bytes (97% of NDJSON)
# Execution succeeded in 5.5ms
# Cycle count: 16,552

# Negative case (still rejected)
./target/release/prove nanoda_lib/test_resources/ProjFromProp/export
# panicked at nanoda_lib/src/tc.rs:444:21: infer_proj prop
# Cycle count: 397,147
```

## 6. Side-by-side summary

### Cycle counts

| Test | NDJSON path (v0) | NDJSON path (v1, ThinLTO) | Flat path (v1) | Δ vs v0 |
|---|---:|---:|---:|---:|
| `Empty` (176 B) | 39,754 | — | 16,552 | **−58%** |
| `my_and_comm` (5.5 KB) | 1,758,250 | 1,548,471 | 821,797 | **−53%** |
| `ProjFromProp` (4.5 KB, invalid) | 1,139,940 | — | 397,147 | **−65%** |

### `my_and_comm` end-to-end timing

| Stage | NDJSON v1 | Flat v1 |
|---|---:|---:|
| Host flatten | n/a | 0.21 ms |
| Bytes shipped to guest | 5,468 | 2,918 |
| SP1 execute (wall) | 41 ms | 22 ms |
| SP1 prove + verify (wall) | 18.7 s | 14.0 s |

### Generic ratios across the pipeline (`my_and_comm`)

| | Time | Slowdown vs native |
|---|---:|---:|
| Native check (`check_native`) | 0.93 ms | 1× |
| SP1 execute (flat) | 22 ms | 24× |
| SP1 prove + verify (flat) | 14.0 s | 15,000× |

## 7. Reproducing in one shot

The pipeline script wraps the build/export/check/execute/prove steps:

```zsh
./run_pipeline.sh MyProject.Basic my_and_comm           # build, export, native, execute
./run_pipeline.sh MyProject.Basic my_and_comm --prove   # ...also generate + verify SNARK
```

Outputs land at `lean-example/exports/<decl>.ndjson` and the script
re-runs the same commands shown above.

## 8. Caveats (as of §1–§7 above)

- Single-machine numbers; no warm-up control beyond running each test
  twice and taking the second result.
- SP1 6.1.0; cycles will shift between SP1 versions.
- Proof times include SP1's ~10 s fixed startup. For inputs larger than
  ~10 M cycles the proportional savings from Option B will translate
  more directly to wall-time savings.
- ~~`check_export_from_flat_bytes` doesn't yet commit `sha256(input)` to
  the public output, so the SNARK currently certifies "some flat blob
  type-checked", not "this specific theorem".~~ → **fixed in §9 below.**

---

# Part II — security hardening + actual ZK

Sections §1–§7 above benchmark the *unhardened* pipeline (Core STARK,
no input binding, no axiom whitelist, no theorem identifier). Everything
below describes the same pipeline after the soundness layers landed and
after switching from Core to Plonk for an actual zero-knowledge proof.
**No number above has been altered or removed** — what's new lives here.

## 9. Security layers added

Five layers, all enforced inside the SP1 guest before
`check_all_declars` runs.

| # | Layer | Where |
|---|---|---|
| 1 | **Pin `Config`** + axiom whitelist (`propext`, `Classical.choice`, `Quot.sound`, `Lean.trustCompiler`) — guest ignores whatever `Config` the blob carried | `nanoda_lib/src/zkvm_entry.rs:check_and_anchor_flat_bytes` |
| 2 | **`sha256(input)` commit** — guest hashes `flat_bytes` and writes the digest as the first public value | `program/src/main.rs` |
| 3 | **Determinism test** for `ndjson_to_flat_bytes` — `nanoda_lib/tests/flat_determinism.rs` runs the converter 8× per fixture, asserts byte-equal | `nanoda_lib/tests/flat_determinism.rs` |
| 4 | **Theorem anchor** — canonical SHA-256 of the headline declar's *kind + name + universe params + type*. Walks the term DAG resolving every `Ptr` to its underlying content, so the digest is invariant to DAG layout | `nanoda_lib/src/anchor.rs` |
| 5 | **Input-size caps** — `MAX_FLAT_BYTES = 256 MiB`, `MAX_DECLARS = 1_000_000` | `nanoda_lib/src/zkvm_entry.rs` |

### Public output schema (after §9)

The SP1 public-values channel now carries three commitments, in order:

1. `input_hash: [u8; 32]` — `sha256(flat_bytes the guest received)`
2. `theorem_anchor: [u8; 32]` — canonical hash of the headline theorem's statement (or all-zero for empty exports)
3. `num_declars: u64` — number of declarations admitted

A verifier with the original Lean theorem statement can independently
compute `theorem_anchor` and check the SNARK's public output matches —
without ever seeing the proof body.

### Cost on `my_and_comm`

| | Cycles | Wall (execute) | Wall (Core prove + verify) |
|---|---:|---:|---:|
| §5 flat path, no security layers | 821,797 | 22 ms | 14.0 s |
| §9 flat path, all 5 layers | **1,034,879** | 28 ms | 15.18 s |
| Δ | +213k cycles (+26%) | +6 ms | +1.2 s |

Most of the +213k cycles is the in-guest SHA-256 of the input bytes
(no precompile yet — see [program/Cargo.toml](lean_snark/program/Cargo.toml)
for the patch comment to swap in SP1's SHA precompile, which would
recover most of those cycles).

### Sanity checks (after §9)

```
=== check_native my_and_comm ===
NDJSON path: 6 declarations
flat path: 6 declarations
check+anchor: 6 declarations
input_hash     = 25afd33cb97a5f331c57075cd54ac3d19d27e204e094ef25fc98f65df9fd6226
theorem_anchor = 4d168a8a0d11952492915a12d4da417eec723c9fd2bcee8d90ff1de8297063fb
num_declars    = 6
OK: all paths agree on 6 declarations.

=== check_native Empty ===
input_hash     = 44eeebdbb436baa3d22f603c139dd1a23adca452ef9db31b918a97ccab3dcc1e
theorem_anchor = 0000000000000000000000000000000000000000000000000000000000000000
num_declars    = 0

=== check_native ProjFromProp ===
panicked at nanoda_lib/src/tc.rs:444:21: infer_proj prop  ✓ (expected)

=== nanoda_lib unit + integration tests ===
31 unit tests pass.
2 integration tests pass (flat_determinism.rs).
```

## 10. SP1 fixed-cost breakdown (measured, replaces the "~10 s startup" estimate)

Three back-to-back warm runs of `--prove` (Core mode) on `my_and_comm`,
plus one run on `Empty` to isolate the floor:

```
[timing] ProverClient::from_env in 8.61 / 8.74 / 18.98 s   (cold first run, then ~9s warm)
[timing] client.setup            in 730 / 791 / 730 ms
[timing] client.prove            in 14.41 / 14.59 / 14.46 s
[timing] client.verify           in 60 / 61 / 60 ms

# Empty (16,552 cycles, basically zero work):
[timing] client.prove            in 10.36 s
```

| Phase | Cost | What it is |
|---|---|---|
| `ProverClient::from_env` | ~9 s warm, ~19 s cold | One-time SP1 SDK init — loads STARK setup data, JIT'd circuits |
| `client.setup(ELF)` | ~750 ms | Proving-key generation from the guest ELF; cacheable to disk |
| `client.prove` fixed | ~10 s | STARK fixed overhead (commitments, FFTs over trace columns) |
| `client.prove` variable | ~5 µs/cycle | Actual proof work; `my_and_comm` 821k cycles → 4 s variable + 10 s fixed |
| `client.verify` | ~60 ms (Core) | STARK verification |

So the honest "fixed cost" is **~20 s** before any input-dependent work
(9 s SDK init + 0.75 s setup + 10 s STARK fixed), not ~10 s as
originally estimated. For the next ~5 M cycles of work that cost is
hidden inside the fixed window; past that it scales linearly.

## 11. Real zk-SNARK with Plonk

Sections §4–§9 use **Core STARK** mode (`client.prove(&pk, stdin).run()`),
which is succinct + publicly verifiable but **not zero-knowledge** — the
proof contains commitments to the execution trace and the trace
contains the witness (`flat_bytes`).

SP1 also offers **Plonk** and **Groth16** wrapping modes. SP1's own
verifier crate documents both as zero-knowledge:

```
sp1-verifier-6.1.0/src/plonk/mod.rs:29:    /// A verifier for Plonk zero-knowledge proofs.
sp1-verifier-6.1.0/src/groth16/mod.rs:22: /// A verifier for Groth16 zero-knowledge proofs.
```

These wrap the Core STARK in a SNARK using gnark's BN254 backend.
Generating one requires SP1's gnark trusted-setup artifacts, which are
downloaded on first use:

| Mode | Local artifacts | Download | First run | Cached run |
|---|---|---:|---:|---:|
| `--prove` (Core, NOT zk) | none | 0 GB | included | included |
| `--plonk` (zk-SNARK) | `~/.sp1/circuits/plonk/v6.1.0/` | ~3 GB | ~22 min | ~12 min |
| `--groth16` (zk-SNARK) | `~/.sp1/circuits/groth16/v6.1.0/` | ~2 GB | ~22 min | ~12 min |

### Plonk run on `my_and_comm` (one cold run, including 3 GB download)

```
$ ./target/release/prove ../lean-example/exports/my_and_comm.ndjson --plonk
Mode: Plonk
Read export file: 5468 bytes (NDJSON)
Flattened on host in 209.08µs: 2918 bytes (53% of NDJSON)
[timing] ProverClient::from_env in 8.54s
[timing] client.setup (proving key gen) in 793.35ms
INFO starting proof generation mode=Plonk
INFO prove shrink: close time.busy=533ms time.idle=3.61s
INFO prove wrap:   close time.busy=47.7s time.idle=80.9s
INFO [sp1] plonk circuit artifacts for version v6.1.0 do not exist ... downloading...
[sp1] downloaded https://sp1-circuits.s3-us-east-2.amazonaws.com/v6.1.0-plonk.tar.gz
DBG constraint system solver done nbConstraints=27576375 took=4128.898291
WARN Memory usage is high: 80.33%
DBG prover done    backend=plonk curve=bn254 nbConstraints=27576375 took=578122.906916
DBG verifier done  backend=plonk curve=bn254 took=3.783083
INFO prove plonk: close time.busy=371µs time.idle=608s
INFO prove:       close time.busy=2.28ms time.idle=1372s mode=Plonk
[timing] client.prove (Plonk) in 1371.90s
[timing] client.verify in 271.94ms
Public output:
  input_hash     = 25afd33cb97a5f331c57075cd54ac3d19d27e204e094ef25fc98f65df9fd6226
  theorem_anchor = 4d168a8a0d11952492915a12d4da417eec723c9fd2bcee8d90ff1de8297063fb
  num_declars    = 6
Note: Plonk mode produces a zero-knowledge SNARK (per `sp1-verifier/src/plonk/mod.rs`).
```

### Stage breakdown

| Stage | Time |
|---|---:|
| `ProverClient::from_env` | 8.54 s |
| `client.setup` | 0.79 s |
| Core STARK | ~3 s |
| `prove shrink` (1st recursion) | ~4 s |
| `prove wrap` (2nd recursion) | 128 s |
| Download gnark Plonk artifacts (~3 GB) | ~10 min |
| gnark constraint-system solver (27.6M constraints, bn254) | 4,129 s ÷ ms ≈ 4 s wall |
| gnark Plonk-BN254 prover | 578 s (~9.6 min) |
| gnark verifier (internal) | 3.8 ms |
| **Total `client.prove` (Plonk)** | **22 min 52 s** |
| `client.verify` (SP1 SDK side) | **272 ms** |

### Comparison: Core vs Plonk

| | Core (§5) | Core w/ §9 layers | Plonk w/ §9 layers |
|---|---:|---:|---:|
| Public output | `num_declars` only | `(input_hash, theorem_anchor, num_declars)` | `(input_hash, theorem_anchor, num_declars)` |
| Zero-knowledge? | No | No | **Yes** |
| Witness recoverable from proof? | Yes | Yes | **No** |
| Prove time | 14.0 s | 15.2 s | 1372 s (≈ 22.9 min) |
| Verify time | 58.5 ms | 60 ms | 272 ms |
| Constraints | (STARK trace) | (STARK trace) | 27,576,375 (Plonk-BN254) |

### What changes semantically with Plonk

The public output (`input_hash`, `theorem_anchor`, `num_declars`) is
**identical** to what Core mode commits — the wrapping doesn't change
the statement being proved, only how the proof is delivered. What
changes is that the witness (`flat_bytes`, i.e. the actual proof terms
of `my_and_comm`) is now hidden by the SNARK's blinding. A relying party
can verify the SNARK in 272 ms and learn:

> "The guest read some bytes whose SHA-256 is `25afd33c...`, those bytes
> rehydrated into a Lean export whose headline theorem hashes to
> `4d168a8a...`, all 6 declarations type-checked, and the proof reveals
> nothing else about the bytes."

## 12. Updated caveats / what's still trusted

- **Cold-start vs steady-state:** Plonk's 22 min number includes the
  one-time 3 GB artifact download. Cached runs are roughly 12 min.
- **Memory pressure:** the gnark wrap hit 80% memory on a laptop. The
  SP1 docs explicitly recommend the prover network for production
  workloads — wrap of much larger inputs is not laptop-feasible.
- **Trusted base — unchanged:** nanoda_lib correctness, SP1 prover/verifier
  soundness, gnark trusted-setup correctness, the four whitelisted
  axioms, deterministic `ndjson_to_flat_bytes` (tested), bincode
  soundness.
- **Anchor encoding is custom**: `nanoda_lib/src/anchor.rs` defines the
  type-tag bytes and walk order. A verifier wanting to compute
  `theorem_anchor` independently has to use this exact encoding.
