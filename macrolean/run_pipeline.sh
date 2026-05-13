#!/usr/bin/env bash
# Runs the full Lean → SP1 pipeline for a single declaration.
#
# Usage:
#   ./run_pipeline.sh <module-name> <decl-name> [flags...]
#
# Mode flags (any combination — they accumulate):
#   --execute    SP1 execute (RISC-V emulation, cycle count, no proof). Default if no flag.
#   --prove      SP1 Core STARK proof (succinct, NOT zk).
#   --plonk      SP1 zk-Plonk SNARK   (succinct + zero-knowledge; ~22 min cold).
#   --groth16    SP1 zk-Groth16 SNARK (succinct + zero-knowledge; ~22 min cold).
#   --all        shorthand for --execute --prove --plonk --groth16  (full benchmark).
#
# Other flags:
#   --skip-build    don't run `lake build` (assume the .olean already exists).
#   --skip-export   don't re-run lean4export (assume the .ndjson is current).
#   --skip-native   don't run check_native.
#
# Examples:
#   ./run_pipeline.sh MyProject.Basic my_and_comm                 # build + export + native + execute
#   ./run_pipeline.sh MyProject.Basic my_and_comm --prove         # ...also Core proof
#   ./run_pipeline.sh MyProject.Basic my_and_comm --execute --prove --plonk
#   ./run_pipeline.sh MyProject.Basic my_and_comm --all           # all four prove modes
#   ./run_pipeline.sh MyProject.Basic my_and_comm --plonk --skip-build --skip-export
#
# Outputs:
#   $EXPORTS_DIR/<decl>.ndjson                  (the export, kept on disk)
#   $EXPORTS_DIR/<decl>.bench.txt               (one summary table per run)

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_DIR="$ROOT/lean-example"
SNARK_DIR="$ROOT/lean_snark"
EXPORT_BIN="$ROOT/lean4export/.lake/build/bin/lean4export"
EXPORTS_DIR="$LEAN_DIR/exports"

# ---------- arg parsing ----------
if [[ $# -lt 2 ]]; then
    cat >&2 <<EOF
Usage: $0 <module-name> <decl-name> [flags...]

Mode flags (any combination):
  --execute    cycle count only (default)
  --prove      Core STARK proof (NOT zk)
  --plonk      zk-Plonk SNARK   (~22 min cold, ~12 min warm)
  --groth16    zk-Groth16 SNARK (~22 min cold, ~12 min warm)
  --all        run all four

Skip flags:
  --skip-build    don't run lake build
  --skip-export   don't re-run lean4export
  --skip-native   don't run check_native
EOF
    exit 2
fi

MODULE="$1"
DECL="$2"
shift 2

DO_EXECUTE=0
DO_PROVE=0
DO_PLONK=0
DO_GROTH16=0
SKIP_BUILD=0
SKIP_EXPORT=0
SKIP_NATIVE=0

for arg in "$@"; do
    case "$arg" in
        --execute)     DO_EXECUTE=1 ;;
        --prove|--core) DO_PROVE=1 ;;
        --plonk)       DO_PLONK=1 ;;
        --groth16)     DO_GROTH16=1 ;;
        --all)         DO_EXECUTE=1; DO_PROVE=1; DO_PLONK=1; DO_GROTH16=1 ;;
        --skip-build)  SKIP_BUILD=1 ;;
        --skip-export) SKIP_EXPORT=1 ;;
        --skip-native) SKIP_NATIVE=1 ;;
        *)
            echo "Unknown flag: $arg" >&2
            exit 2
            ;;
    esac
done

# Default: execute-only if no mode flag was given
if (( DO_EXECUTE + DO_PROVE + DO_PLONK + DO_GROTH16 == 0 )); then
    DO_EXECUTE=1
fi

NDJSON="$EXPORTS_DIR/$DECL.ndjson"
BENCH="$EXPORTS_DIR/$DECL.bench.txt"

# ---------- pretty-printing helpers ----------
bold()  { printf "\033[1m%s\033[0m\n" "$*"; }
green() { printf "\033[32m%s\033[0m\n" "$*"; }
red()   { printf "\033[31m%s\033[0m\n" "$*"; }

step() { echo; bold "=== $* ==="; }

# Capture both stdout (for the user) and a tee'd copy (for the bench table).
LOG="$(mktemp -t lean_snark_pipeline.XXXXXX)"
trap "rm -f '$LOG'" EXIT

run_and_log() {
    local label="$1"; shift
    echo "[$label] $@" >> "$LOG"
    "$@" 2>&1 | tee -a "$LOG"
}

# Pull a "Cycle count: N" / "Proof generated in T" / "Proof verified in T"
# / "client.prove (...) in T" line out of the log for the most recent run.
extract_after() {
    local pattern="$1"
    grep -E --color=never "$pattern" "$LOG" | tail -1 | sed -E 's/.*'"$pattern"'.*/\1/' || true
}

# ---------- step 1: lake build ----------
if [[ $SKIP_BUILD -eq 0 ]]; then
    step "1. lake build  ($MODULE)"
    cd "$LEAN_DIR"
    lake build "$MODULE"
else
    step "1. lake build  (skipped via --skip-build)"
fi

# ---------- step 2: export ----------
if [[ $SKIP_EXPORT -eq 0 ]]; then
    step "2. lean4export  $MODULE -- $DECL"
    cd "$LEAN_DIR"
    mkdir -p "$EXPORTS_DIR"
    lake env "$EXPORT_BIN" "$MODULE" -- "$DECL" > "$NDJSON"
    SIZE=$(wc -c < "$NDJSON" | tr -d ' ')
    LINES=$(wc -l < "$NDJSON" | tr -d ' ')
    green "wrote $NDJSON ($SIZE bytes, $LINES lines)"
else
    step "2. lean4export  (skipped via --skip-export — using existing $NDJSON)"
    if [[ ! -f "$NDJSON" ]]; then
        red "no export at $NDJSON — drop --skip-export or run with no flag first"; exit 1
    fi
fi

# ---------- step 3: native sanity ----------
cd "$SNARK_DIR"
if [[ $SKIP_NATIVE -eq 0 ]]; then
    step "3. native nanoda_lib check"
    run_and_log "native" ./target/release/check_native "$NDJSON"
else
    step "3. native check  (skipped via --skip-native)"
fi

# ---------- step 4..n: each prove mode ----------
if [[ $DO_EXECUTE -eq 1 ]]; then
    step "execute (cycle count, no proof)"
    run_and_log "execute" ./target/release/prove "$NDJSON"
fi
if [[ $DO_PROVE -eq 1 ]]; then
    step "Core STARK prove (--prove)  — NOT zero-knowledge"
    run_and_log "core" ./target/release/prove "$NDJSON" --prove
fi
if [[ $DO_PLONK -eq 1 ]]; then
    step "Plonk zk-SNARK (--plonk)  — first run downloads ~3 GB"
    run_and_log "plonk" ./target/release/prove "$NDJSON" --plonk
fi
if [[ $DO_GROTH16 -eq 1 ]]; then
    step "Groth16 zk-SNARK (--groth16)  — first run downloads ~2 GB"
    run_and_log "groth16" ./target/release/prove "$NDJSON" --groth16
fi

# ---------- summary table ----------
step "summary"

# Helper: pull a numeric field out of $LOG, scoped to a labelled run.
# Args: <label> <regex with one capture group>
field_for() {
    local label="$1" pat="$2"
    awk -v label="[$label]" -v pat="$pat" '
        $0 == label" "$0 || index($0, label" ./") {in_block=1; next}
        in_block && /^\[.*\]/ {in_block=0}
        in_block && match($0, pat, m) {print m[1]; exit}
    ' "$LOG" 2>/dev/null || true
}

# Slice the log between consecutive section headers.
#
# Each section starts with `[<label>] ./...` (emitted by `run_and_log` above).
# We must NOT treat just-any-`[`-prefixed line as a boundary, because prove.rs
# prints lines like `[timing] ProverClient::from_env in 8.81s` — those would
# falsely end the section.
section_for() {
    local label="$1"
    awk -v label="$label" '
        # match the start-of-section line: [<label>] <something>
        $0 ~ "^\\["label"\\] " { in_block = 1; next }
        # match ANOTHER section header (any of our labels) to end the block
        in_block && /^\[(native|execute|core|compressed|plonk|groth16)\] / { exit }
        in_block { print }
    ' "$LOG"
}

# Column widths chosen so all 6 columns fit on an 80-column terminal.
printf "\n%-10s | %-10s | %-11s | %-11s | %-10s | %s\n" \
    "stage" "cycles" "wall (run)" "verify" "proof" "public output"
printf "%-10s-+-%-10s-+-%-11s-+-%-11s-+-%-10s-+-%s\n" \
    "----------" "----------" "-----------" "-----------" "----------" "------------"

print_row() {
    local label="$1"
    local section
    section=$(section_for "$label")
    [[ -z "$section" ]] && return

    # `grep -oE ... | head | sed` chains return non-zero when the pattern
    # isn't found, and that trips `set -euo pipefail` and silently aborts
    # the function before any row is printed. The trailing `|| true` makes
    # each subshell unconditionally succeed; an empty result falls through
    # to the `${var:-—}` defaults in the printf below.
    local cycles run verify proof hash anchor decls
    cycles=$(echo "$section"  | grep -oE 'Cycle count: [0-9,]+' | head -1 | sed 's/Cycle count: //' || true)
    run=$(echo "$section"     | grep -oE 'client\.prove \([A-Za-z]+\) in [0-9.]+s|Execution succeeded in [0-9.]+m?s|Proof generated in [0-9.]+s' | head -1 | sed -E 's/.*in //' || true)
    verify=$(echo "$section"  | grep -oE 'client\.verify in [0-9.]+m?s' | head -1 | sed -E 's/.*in //' || true)
    # Proof size: the `Sizes:` block emitted by prove.rs.
    # Matches lines like:   proof          = 2.67 MB (2795983 bytes)
    #               or:     proof          = 504 bytes
    proof=$(echo "$section"   | grep -oE 'proof[[:space:]]+= [^(]+(\([0-9]+ bytes\))?' | head -1 | sed -E 's/^proof[[:space:]]+= //; s/[[:space:]]+\(.*$//; s/[[:space:]]+$//' || true)
    hash=$(echo "$section"    | grep -oE 'input_hash[^=]*= [0-9a-f]+'  | head -1 | sed -E 's/.*= //' | cut -c1-8 || true)
    anchor=$(echo "$section"  | grep -oE 'theorem_anchor[^=]*= [0-9a-f]+' | head -1 | sed -E 's/.*= //' | cut -c1-8 || true)
    decls=$(echo "$section"   | grep -oE 'num_declars[^=]*= [0-9]+'   | head -1 | sed -E 's/.*= //' || true)

    printf "%-10s | %-10s | %-11s | %-11s | %-10s | hash=%s… anchor=%s… n=%s\n" \
        "$label" "${cycles:-—}" "${run:-—}" "${verify:-—}" "${proof:-—}" \
        "${hash:---------}" "${anchor:---------}" "${decls:-—}"
}

print_row native
print_row execute
print_row core
print_row plonk
print_row groth16

# Also persist the full log alongside the export.
cp "$LOG" "$BENCH"
green "raw log saved to $BENCH"

echo
green "pipeline complete."
