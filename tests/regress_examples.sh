#!/bin/bash
#
# regress_examples.sh — Boole pipeline regression runner across multiple
# suites. For each selected .rs input it invokes tests/run_tests.sh to run
# the full pipeline (Verus export → Boole generation → Strata Boole
# verify) and classifies the result using the shared classifier in
# tests/lib/boole_verify.sh.
#
# This script is the multi-suite sibling of tests/check_working_tests.sh,
# which reads from a single curated list. Use --all-suites to cover
# everything under tests/VerusFiles, tests/adopted_rust_verify_test,
# verus/examples, and verus/examples/guide.
#
# Historically this script drove the Core-dialect pipeline and reported
# "translate failures" / "strata parse failures" per stage. The Boole
# pipeline merges generation into a single stage and splits verify into
# pass / skip (Sequence) / skip (Strata gap) / fail — the summary lines
# below reflect that.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERUS_DIR="$(cd "$ROOT_DIR/../verus" && pwd -P)"
VERUSFILES_DIR="$ROOT_DIR/tests/VerusFiles"
ADOPTED_RVT_DIR="$ROOT_DIR/tests/adopted_rust_verify_test"
STRATA_DIR="${STRATA_DIR:-$(cd "$ROOT_DIR/../Strata" && pwd -P)}"
RVT_CURATED_LIST="${RVT_CURATED_LIST:-$ROOT_DIR/tests/rust_verify_generated_cases.txt}"
REGRESSION_LOGS_DIR="${REGRESSION_LOGS_DIR:-$ROOT_DIR/tests/RegressionLogs}"

# Shared Boole verify classifier.
# shellcheck source=tests/lib/boole_verify.sh
source "$ROOT_DIR/tests/lib/boole_verify.sh"

verbose=false
run_all_suites=false
declare -a selected_suites=()
declare -a requested_examples=()

usage() {
  cat <<'EOF'
Usage: tests/regress_examples.sh [options] [target.rs ...]

Runs the full Boole pipeline across one or more suites:
  Stage 1: Verus export (.rs -> JSON)
  Stage 2: verus-lean Boole generation (JSON -> .boole.st + .lean wrapper)
  Stage 3: Strata Boole verify (lake env lean <wrapper>) classified as
           pass / skip (Sequence) / skip (Strata gap) / fail

Options:
  --verbose         Stream sub-command output in addition to writing logs
  --all-suites      Run vlir-tests + verus-examples (+ guide subdir)
  --suite <name>    Add a suite: vlir-tests | verus-examples | rust-verify-generated
  --rvt-list <file> Curated list for rust-verify-generated suite
                    (default: tests/rust_verify_generated_cases.txt)
  -h, --help        Show this help

Examples:
  tests/regress_examples.sh --all-suites
  tests/regress_examples.sh --suite verus-examples
  tests/regress_examples.sh ../verus/examples/assertions.rs
EOF
}

is_known_suite() {
  case "$1" in
    vlir-tests|verus-examples|rust-verify-generated) return 0 ;;
    *) return 1 ;;
  esac
}

add_selected_suite() {
  local name="$1"
  local s
  for s in "${selected_suites[@]-}"; do
    [ "$s" = "$name" ] && return 0
  done
  selected_suites+=("$name")
}

# Main argument loop.
while [ $# -gt 0 ]; do
  case "$1" in
    --verbose) verbose=true; shift ;;
    --all-suites) run_all_suites=true; shift ;;
    --suite)
      if [ $# -lt 2 ]; then echo "Missing value for --suite"; usage; exit 1; fi
      if ! is_known_suite "$2"; then echo "Unknown suite: $2"; usage; exit 1; fi
      add_selected_suite "$2"
      shift 2
      ;;
    --rvt-list)
      if [ $# -lt 2 ]; then echo "Missing value for --rvt-list"; exit 1; fi
      RVT_CURATED_LIST="$2"
      shift 2
      ;;
    -h|--help) usage; exit 0 ;;
    --*) echo "Unknown option: $1"; usage; exit 1 ;;
    *) requested_examples+=("$1"); shift ;;
  esac
done

if $run_all_suites; then
  add_selected_suite vlir-tests
  add_selected_suite verus-examples
fi

# If neither --all-suites nor --suite nor explicit targets were given,
# default to vlir-tests (matches old behavior when invoked with no args).
if [ ${#selected_suites[@]} -eq 0 ] && [ ${#requested_examples[@]} -eq 0 ]; then
  selected_suites+=("vlir-tests")
fi

# Collect .rs files.
declare -a targets=()

add_rs_files_from_dir() {
  local dir="$1"
  [ -d "$dir" ] || return 0
  local f
  while IFS= read -r f; do
    targets+=("$f")
  done < <(find "$dir" -maxdepth 1 -type f -name '*.rs' | sort)
}

for suite in "${selected_suites[@]}"; do
  case "$suite" in
    vlir-tests)
      add_rs_files_from_dir "$VERUSFILES_DIR"
      add_rs_files_from_dir "$ADOPTED_RVT_DIR"
      ;;
    verus-examples)
      add_rs_files_from_dir "$VERUS_DIR/examples"
      add_rs_files_from_dir "$VERUS_DIR/examples/guide"
      ;;
    rust-verify-generated)
      if [ ! -f "$RVT_CURATED_LIST" ]; then
        echo "Missing rust-verify-generated list: $RVT_CURATED_LIST"
        exit 1
      fi
      while IFS= read -r line; do
        case "$line" in ""|\#*) continue ;; esac
        if [ -f "$line" ]; then
          targets+=("$line")
        elif [ -f "$ROOT_DIR/$line" ]; then
          targets+=("$ROOT_DIR/$line")
        fi
      done < "$RVT_CURATED_LIST"
      ;;
  esac
done

for example in "${requested_examples[@]}"; do
  if [ -f "$example" ]; then
    targets+=("$example")
  elif [ -f "$ROOT_DIR/$example" ]; then
    targets+=("$ROOT_DIR/$example")
  else
    echo "Missing target: $example"
    exit 1
  fi
done

if [ ${#targets[@]} -eq 0 ]; then
  echo "No targets selected."
  exit 1
fi

mkdir -p "$REGRESSION_LOGS_DIR"

# Resolve a .rs path to its Boole .lean wrapper (mirrors
# run_tests.sh::resolve_boole_wrapper_for_rs_path). Kept inline so this
# script is not coupled to run_tests.sh's internal helpers.
lean_wrapper_for_target() {
  local target="$1"
  local rel
  if [[ "$target" == "$VERUSFILES_DIR"/* ]]; then
    rel="${target#$VERUSFILES_DIR/}"
    rel="${rel%.rs}"
    echo "$ROOT_DIR/tests/BoolePrograms/vlir-tests/${rel}.lean"
  elif [[ "$target" == "$ADOPTED_RVT_DIR"/* ]]; then
    rel="${target#$ADOPTED_RVT_DIR/}"
    rel="${rel%.rs}"
    echo "$ROOT_DIR/tests/BoolePrograms/vlir-tests/tests__adopted_rust_verify_test__${rel}.lean"
  elif [[ "$target" == */verus/examples/guide/* ]]; then
    rel="$(basename "${target%.rs}")"
    echo "$ROOT_DIR/tests/BoolePrograms/verus-examples/guide__${rel}.lean"
  elif [[ "$target" == */verus/examples/* ]]; then
    rel="$(basename "${target%.rs}")"
    echo "$ROOT_DIR/tests/BoolePrograms/verus-examples/${rel}.lean"
  else
    echo ""
  fi
}

# Counters per stage + per verify category.
gen_failures=()
gen_missing_json=()
verify_passed=0
verify_skipped_seq=0
verify_skipped_gap=0
verify_failed=()

verbose_flag=()
$verbose && verbose_flag=(--verbose)

for target in "${targets[@]}"; do
  echo ""
  echo "==> $target"

  log="$(mktemp "$REGRESSION_LOGS_DIR/run.XXXXXX.log")"
  set +e
  (cd "$ROOT_DIR" && ./tests/run_tests.sh --boole "${verbose_flag[@]}" "$target") >"$log" 2>&1
  rc=$?
  set -e
  if $verbose; then
    cat "$log"
  fi

  if grep -q "json missing" "$log"; then
    gen_missing_json+=("$target")
    rm -f "$log"
    continue
  fi
  if [ $rc -ne 0 ] && ! grep -q "Boole:" "$log"; then
    gen_failures+=("$target")
    rm -f "$log"
    continue
  fi
  rm -f "$log"

  lean_file="$(lean_wrapper_for_target "$target")"
  if [ -z "$lean_file" ] || [ ! -f "$lean_file" ]; then
    # No wrapper produced (e.g. empty export) — not a verify regression.
    continue
  fi

  verify_log="$(mktemp "$REGRESSION_LOGS_DIR/verify.XXXXXX.log")"
  set +e
  (cd "$STRATA_DIR" && lake env lean "$lean_file") >"$verify_log" 2>&1
  vrc=$?
  set -e
  category="$(classify_boole_verify_log "$verify_log" "$vrc")"
  case "$category" in
    pass)
      verify_passed=$((verify_passed + 1))
      echo "  verify: PASS"
      ;;
    skip_sequence)
      verify_skipped_seq=$((verify_skipped_seq + 1))
      echo "  verify: SKIP (Sequence)"
      ;;
    skip_gap)
      verify_skipped_gap=$((verify_skipped_gap + 1))
      echo "  verify: SKIP (Strata gap)"
      ;;
    *)
      verify_failed+=("$target")
      echo "  verify: FAIL"
      grep "error:" "$verify_log" | head -2 || true
      ;;
  esac
  rm -f "$verify_log"
done

echo ""
echo "==> Boole regression summary"
echo "  generation failures: ${#gen_failures[@]}"
echo "  missing json:        ${#gen_missing_json[@]}"
echo "  verify passed:       $verify_passed"
echo "  verify skipped seq:  $verify_skipped_seq"
echo "  verify skipped gap:  $verify_skipped_gap"
echo "  verify failures:     ${#verify_failed[@]}"

rc=0
if [ ${#gen_failures[@]} -gt 0 ]; then
  echo ""
  echo "Generation failures:"
  printf '  %s\n' "${gen_failures[@]}"
  rc=1
fi
if [ ${#verify_failed[@]} -gt 0 ]; then
  echo ""
  echo "Verify failures:"
  printf '  %s\n' "${verify_failed[@]}"
  rc=1
fi
exit $rc
