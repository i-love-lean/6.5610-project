#!/bin/sh
# Run every cert_*.lurk test and report pass/fail.
# Usage: ./run_cert_tests.sh [pattern]    (pattern is glob matched against name)
set -u
cd "$(dirname "$0")"
LURK="${LURK:-/home/danklishch/.cargo/bin/lurk}"
TIMEOUT="${TIMEOUT:-30}"
PATTERN="${1:-*}"

pass=0
fail=0
failed_names=""
total_t=0

for f in cert_*.lurk; do
  base=$(basename "$f" .lurk)
  case "$base" in cert_verifier|cert_helpers) continue ;; esac
  # Sqrt is too big to fit on this machine; skip by default unless caller
  # explicitly opts in via a matching pattern.
  if [ "$base" = "cert_dep_sqrt_two_irrational" ] && \
     [ "$PATTERN" = "*" ]; then continue; fi
  case "$base" in $PATTERN|cert_$PATTERN) : ;; *) continue ;; esac

  t0=$(date +%s)
  out=$(timeout "$TIMEOUT" "$LURK" load "$f" 2>&1)
  rc=$?
  t1=$(date +%s)
  dt=$((t1 - t0))
  total_t=$((total_t + dt))

  # The dump asserts (validate-trace 0) and (check-cert nil ...).  Each
  # successful !(assert ...) prints `t`; failure shows "assert failed".
  if [ $rc -eq 0 ] && ! echo "$out" | grep -q "assert failed\|Error"; then
    pass=$((pass + 1))
    printf "  ok    %-40s  %ss\n" "$base" "$dt"
  else
    fail=$((fail + 1))
    failed_names="$failed_names $base"
    printf "  FAIL  %-40s  %ss\n" "$base" "$dt"
    echo "$out" | tail -5 | sed 's/^/        /'
  fi
done

echo
echo "passed: $pass  failed: $fail  total time: ${total_t}s"
[ -n "$failed_names" ] && echo "failed:$failed_names"
[ "$fail" -eq 0 ]
