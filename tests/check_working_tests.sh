#!/bin/bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
WORKING_LIST="${WORKING_LIST:-$ROOT_DIR/tests/working_tests.txt}"
STRATA_DIR="${STRATA_DIR:-$ROOT_DIR/../Strata}"
BOOLE_PROGRAMS_DIR="${BOOLE_PROGRAMS_DIR:-$ROOT_DIR/tests/BoolePrograms}"
# Set SKIP_STRATA_VERIFY=1 to skip Step 3 (faster regen-only run).
SKIP_STRATA_VERIFY="${SKIP_STRATA_VERIFY:-0}"

# Shared classify helper.
# shellcheck source=tests/lib/boole_verify.sh
source "$ROOT_DIR/tests/lib/boole_verify.sh"

usage() {
  echo "Usage: tests/check_working_tests.sh"
  echo "  WORKING_LIST        Test list (default: tests/working_tests.txt)"
  echo "  SKIP_STRATA_VERIFY  Set to 1 to skip Step 3 (Strata Boole verify)"
}

abs_existing_path() {
  local p="$1"
  if [ -f "$p" ]; then
    echo "$(cd "$(dirname "$p")" && pwd -P)/$(basename "$p")"
    return 0
  fi
  if [ -f "$ROOT_DIR/$p" ]; then
    echo "$(cd "$(dirname "$ROOT_DIR/$p")" && pwd -P)/$(basename "$ROOT_DIR/$p")"
    return 0
  fi
  return 1
}

while [ $# -gt 0 ]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown option: $1"; usage; exit 1 ;;
  esac
done

if [ ! -f "$WORKING_LIST" ]; then
  echo "Missing working test list: $WORKING_LIST"
  exit 1
fi

failures=()
verify_failures=()
verify_passed=0
verify_skipped_seq=0
verify_skipped_unsupported=0
verify_skipped_solver_timeout=0
verify_skipped_solver_unknown=0
verify_known_translator_bugs=0

: # `is_ignored_test` lives in tests/lib/boole_verify.sh (sourced above)

# For "negative" Verus tests (containing intentionally-unverifiable
# assertions), return a regex matching the obligation labels Strata is
# expected to report as failing. Empty return = strict mode (every
# obligation must pass for [verify] ✅ PASS). A pattern of `.` permits
# any obligation to fail (suitable for files whose entire contents are
# expect-failures, as indicated by their header comment).
#
# Obligation labels have the shape `<stable-prefix>_<idx>_<serial>`
# (e.g. `assert_15_1719`, `bitvector_query`, `triangle0_terminates_0`).
# The trailing `_<serial>` is a Provenance positional counter that
# *renumbers* whenever upstream Strata's metadata changes (the
# 2026-05-18 int-termination pull is one such event). Anchor patterns
# on the stable prefix (semantic name, or `<name>_<idx>_`) and never
# on the volatile serial, so a pin bump does not spuriously re-flag
# these as regressions. A genuinely new failing obligation has a
# different prefix and still surfaces.
# Thin delegator: the canonical pattern table lives in
# `tests/lib/boole_verify.sh::expected_boole_fail_pattern_for_wrapper`
# (sourced into both this script and `run_tests.sh`).  We resolve the
# `.rs` target to its `.lean` wrapper, then ask the shared helper.
# Keeping a single source of truth ensures `run_tests.sh --verify`
# (direct invocation) and the curated gate agree on which obligation
# failures are documented/expected.
expected_fail_pattern_for_target() {
  local wrapper
  wrapper="$(lean_wrapper_for_target "$1")"
  [ -z "$wrapper" ] && { echo ""; return; }
  expected_boole_fail_pattern_for_wrapper "$wrapper"
}

# Resolve the .lean wrapper path for a given .rs target. This mirrors
# resolve_boole_wrapper_for_rs_path in run_tests.sh, but is kept inline so this
# script can run without sourcing run_tests.sh's full helper set.
lean_wrapper_for_target() {
  local target="$1"
  local rel
  if [[ "$target" == "$ROOT_DIR/tests/VerusFiles/"* ]]; then
    rel="${target#$ROOT_DIR/tests/VerusFiles/}"
    rel="${rel%.rs}"
    echo "$BOOLE_PROGRAMS_DIR/vlir-tests/${rel}.lean"
  elif [[ "$target" == "$ROOT_DIR/tests/adopted_rust_verify_test/"* ]]; then
    rel="${target#$ROOT_DIR/tests/adopted_rust_verify_test/}"
    rel="${rel%.rs}"
    echo "$BOOLE_PROGRAMS_DIR/vlir-tests/tests__adopted_rust_verify_test__${rel}.lean"
  elif [[ "$target" == */verus/examples/guide/* ]]; then
    rel="$(basename "${target%.rs}")"
    echo "$BOOLE_PROGRAMS_DIR/verus-examples/guide__${rel}.lean"
  elif [[ "$target" == */verus/examples/* ]]; then
    rel="$(basename "${target%.rs}")"
    echo "$BOOLE_PROGRAMS_DIR/verus-examples/${rel}.lean"
  else
    echo ""
  fi
}

while IFS= read -r line || [ -n "$line" ]; do
  case "$line" in
    ""|\#*) continue ;;
  esac
  target="$line"

  if target_abs="$(abs_existing_path "$target")"; then
    target="$target_abs"
  fi

  echo ""
  echo "==> Test: $target"

  # Tests not suitable or valuable to run regression on (upstream-ignored,
  # empty-export, known-hang).  See `tests/ignored_tests.txt` for the list
  # and reason tags.  Skip silently rather than invoking Verus.
  if is_ignored_test "$target"; then
    echo "  [skipped] listed in tests/ignored_tests.txt"
    continue
  fi

  # Steps 1 + 2: Verus export → Boole generation (delegated to run_tests.sh).
  cmd=(./tests/run_tests.sh --boole --verbose "$target")
  run_log="$(mktemp)"
  set +e
  (cd "$ROOT_DIR" && "${cmd[@]}") 2>&1 | tee "$run_log"
  rc=$?
  set -e

  if grep -q "json missing" "$run_log"; then
    failures+=("$target")
    rm -f "$run_log"
    continue
  fi

  if [ $rc -ne 0 ]; then
    if ! grep -q "Boole:" "$run_log"; then
      failures+=("$target")
    fi
  fi
  rm -f "$run_log"

  # Step 3: Strata Boole verify — reuse run_tests.sh's classifier so both
  # scripts agree on pass / skip / fail semantics. The lake env lean output
  # itself contains per-obligation `Result: ✅ pass` / `Result: ❌ fail`
  # lines, which we surface verbatim before printing the per-test verdict.
  if [ "$SKIP_STRATA_VERIFY" != "1" ]; then
    lean_file="$(lean_wrapper_for_target "$target")"
    if [ -n "$lean_file" ] && [ -f "$lean_file" ]; then
      echo "=== Step 3: Strata Boole verify ==="
      verify_log="$(mktemp)"
      set +e
      run_boole_wrapper "$lean_file" "$verify_log"
      vrc=$?
      set -e
      # Stream the lake output (indented for visual nesting under the test).
      sed 's/^/  /' "$verify_log"
      expected_fail_pattern="$(expected_fail_pattern_for_target "$target")"
      known_translator_bug_pattern="$(known_translator_bug_pattern_for_wrapper "$lean_file")"
      category="$(classify_boole_verify_log "$verify_log" "$vrc" "$expected_fail_pattern" "$known_translator_bug_pattern")"
      case "$category" in
        pass)
          verify_passed=$((verify_passed + 1))
          if [ -n "$expected_fail_pattern" ]; then
            echo "  [verify] ✅ PASS (negative test; expected failures match)"
          else
            echo "  [verify] ✅ PASS (all obligations succeeded)"
          fi
          ;;
        skip_sequence)
          verify_skipped_seq=$((verify_skipped_seq + 1))
          echo "  [verify] ⏭  SKIP (Sequence support missing in Strata Boole verify)"
          ;;
        skip_gap)
          verify_skipped_unsupported=$((verify_skipped_unsupported + 1))
          err="$(grep "error:" "$verify_log" | head -1 | cut -c1-120 || true)"
          if [ -z "$err" ]; then
            err="$(awk '
              /^Obligation:/ { ob = $0; sub(/^Obligation: */, "", ob); next }
              /^Result: ❌ fail/ { print "failed obligation " ob; exit }
            ' "$verify_log" | cut -c1-120)"
          fi
          echo "  [verify] ⏭  SKIP (Strata gap): $err"
          ;;
        skip_solver_timeout)
          verify_skipped_solver_timeout=$((verify_skipped_solver_timeout + 1))
          err="$(grep -E "(cvc5|z3)[^\\n]*(interrupted by timeout|killed by)" "$verify_log" | head -1 | cut -c1-120 || true)"
          echo "  [verify] ⏭  SKIP (solver timeout): $err"
          ;;
        skip_solver_unknown)
          verify_skipped_solver_unknown=$((verify_skipped_solver_unknown + 1))
          n_unknown="$(grep -c "Result: ❓ unknown" "$verify_log" || true)"
          echo "  [verify] ⏭  SKIP (solver unknown on $n_unknown obligation(s))"
          ;;
        known_translator_bug)
          verify_known_translator_bugs=$((verify_known_translator_bugs + 1))
          err="$(grep "error:" "$verify_log" | head -1 | cut -c1-120 || true)"
          if [ -z "$err" ]; then
            err="$(awk '
              /^Obligation:/ { ob = $0; sub(/^Obligation: */, "", ob); next }
              /^Result: ❌ fail/ { print "failed obligation " ob; exit }
            ' "$verify_log" | cut -c1-120)"
          fi
          echo "  [verify] 🐞 KNOWN TRANSLATOR BUG: $err"
          ;;
        *)
          verify_failures+=("$target")
          # Report whichever failure surfaced first: a Lean error, or an
          # unexpected obligation failure.
          if grep -q "error:" "$verify_log"; then
            err="$(grep "error:" "$verify_log" | head -1 | cut -c1-120)"
            echo "  [verify] ❌ FAIL: $err"
          else
            unexpected="$(awk '
              /^Obligation:/ { ob = $0; sub(/^Obligation: */, "", ob); next }
              /^Result: ❌ fail/ { print "    - " ob }
            ' "$verify_log" | head -3)"
            echo "  [verify] ❌ FAIL: unexpected obligation failure(s):"
            printf '%s\n' "$unexpected"
          fi
          ;;
      esac
      rm -f "$verify_log"
    fi
  fi
done < "$WORKING_LIST"

echo ""
echo "==> Summary"
rc=0
if [ ${#failures[@]} -eq 0 ]; then
  echo "Generation: all working tests passed."
else
  echo "Generation regressions: ${failures[*]}"
  rc=1
fi
if [ "$SKIP_STRATA_VERIFY" != "1" ]; then
  echo "Strata verify: $verify_passed passed, $verify_skipped_seq skipped (Sequence), $verify_skipped_unsupported skipped (Strata gap), $verify_skipped_solver_timeout skipped (solver timeout), $verify_skipped_solver_unknown skipped (solver unknown), $verify_known_translator_bugs known translator bugs, ${#verify_failures[@]} failed"
  if [ ${#verify_failures[@]} -ne 0 ]; then
    echo "Verify regressions:"
    printf '  %s\n' "${verify_failures[@]}"
    rc=1
  fi
fi
exit $rc
