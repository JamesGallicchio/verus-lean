#!/usr/bin/env bash
# Verify the dalek b1..b5 minimal benchmarks through the production Boole verify
# path (JSON -> .boole.st -> #strata wrapper -> Strata.Boole.verify) with a
# chosen SMT solver.
#
# Usage:
#   tests/run_benchmarks.sh [solver] [benchmark ...]
#
# `solver` defaults to z3.  With no benchmark names, runs b1_minimal..b5_minimal.
# Examples:
#   tests/run_benchmarks.sh                 # all five, z3
#   tests/run_benchmarks.sh cvc5            # all five, cvc5
#   tests/run_benchmarks.sh z3 b2_minimal   # just b2, z3
#
# Exits non-zero if any requested benchmark is missing or fails to verify, so it
# cannot false-green.  (Explicit accumulation rather than `set -e`, so every
# benchmark still runs and reports before the overall pass/fail is decided.)
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VLIR="$SCRIPT_DIR/JSONFilesBoogie/vlir-tests"

solver="z3"
benches=()
for arg in "$@"; do
  case "$arg" in
    cvc5|z3) solver="$arg" ;;
    *) benches+=("$arg") ;;
  esac
done
if [ "${#benches[@]}" -eq 0 ]; then
  benches=(b1_minimal b2_minimal b3_minimal b4_minimal b5_minimal)
fi

echo "Dalek benchmarks via production runner (solver=$solver)"
rc=0
for b in "${benches[@]}"; do
  json="$VLIR/$b/$b.json"
  if [ ! -f "$json" ]; then
    echo "── $b: MISSING ($json)"
    rc=1
    continue
  fi
  echo "── $b ───────────────────────────────────────────────"
  if ! "$SCRIPT_DIR/run_tests.sh" --boole --verify --solver "$solver" "$json"; then
    echo "── $b: FAILED"
    rc=1
  fi
done
if [ "$rc" -ne 0 ]; then
  echo "run_benchmarks: one or more benchmarks were missing or failed."
fi
exit "$rc"
