#!/bin/bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERUS_DIR="$ROOT_DIR/../verus"
VERUS_SRC="$VERUS_DIR/source"
VERUS_EXAMPLES_DIR="$VERUS_DIR/examples"
VLIR_TESTS_DIR="$ROOT_DIR/tests/VerusFiles"
VERUS_BIN="$VERUS_SRC/target-verus/release/verus"
VERUS_LEAN="$ROOT_DIR/.lake/build/bin/verus-lean"
STRATA_DIR="$ROOT_DIR/../Strata"

JSON_BOOGIE_DIR="${JSON_BOOGIE_DIR:-$ROOT_DIR/tests/JSONFilesBoogie}"
CORE_DIR="${CORE_DIR:-$ROOT_DIR/tests/BoogieFiles}"
REGRESSION_LOGS_DIR="${REGRESSION_LOGS_DIR:-$ROOT_DIR/tests/RegressionLogs}"

STARTER_EXAMPLES=(
  "test.rs"
  "assertions.rs"
  "basic_failure.rs"
  "datatypes.rs"
  "adts_eq.rs"
  "structural.rs"
)

verbose=false
run_all_suites=false
declare -a selected_suites=()
declare -a requested_examples=()
STRATA_SOLVER="cvc5"
STRATA_SOLVER_TIMEOUT=""

usage() {
  cat <<'EOF'
Usage: tests/regress_examples.sh [options] [example ...]

Runs regression across 3 stages for each Verus example:
  1) Verus export (--export-lean-all)
  2) Verus-Lean JSON -> Core translation
  3) StrataVerify on generated Core file

Options:
  --verbose         Stream command output while also saving logs
  --all-suites      Run vlir-tests + verus-examples
  --suite <name>    Add a suite: vlir-tests | verus-examples
  --solver <name>   StrataVerify solver (default: cvc5)
  --solver-timeout <sec>
                    StrataVerify timeout in seconds
  --list            Print starter examples and available suites, then exit
  -h, --help        Show this help

Examples:
  tests/regress_examples.sh
  tests/regress_examples.sh datatypes
  tests/regress_examples.sh /abs/path/to/verus/examples/assertions.rs
  tests/regress_examples.sh --suite verus-examples
  tests/regress_examples.sh --suite vlir-tests
  tests/regress_examples.sh --all-suites

EOF
}

show_starter_list() {
  echo "Starter examples:"
  for ex in "${STARTER_EXAMPLES[@]}"; do
    echo "  $VERUS_EXAMPLES_DIR/$ex"
  done
  echo ""
  echo "Suites:"
  echo "  vlir-tests          -> $VLIR_TESTS_DIR/*.rs"
  echo "  verus-examples      -> $VERUS_EXAMPLES_DIR/*.rs + $VERUS_EXAMPLES_DIR/guide/**/*.rs"
}

is_known_suite() {
  case "$1" in
    vlir-tests|verus-examples) return 0 ;;
    *) return 1 ;;
  esac
}

suite_dir_of() {
  case "$1" in
    vlir-tests) (cd "$VLIR_TESTS_DIR" && pwd -P) ;;
    verus-examples) (cd "$VERUS_EXAMPLES_DIR" && pwd -P) ;;
    *) return 1 ;;
  esac
}

add_selected_suite() {
  local suite="$1"
  if ! is_known_suite "$suite"; then
    echo "Unknown suite: $suite" >&2
    echo "Valid suites: vlir-tests, verus-examples" >&2
    exit 1
  fi
  local s
  for s in "${selected_suites[@]-}"; do
    if [ "$s" = "$suite" ]; then
      return
    fi
  done
  selected_suites+=("$suite")
}

infer_suite_from_path() {
  local path="$1"
  local abs_dir abs_path
  local vlir_root examples_root
  abs_dir="$(cd "$(dirname "$path")" && pwd -P)"
  abs_path="$abs_dir/$(basename "$path")"
  vlir_root="$(suite_dir_of vlir-tests)"
  examples_root="$(suite_dir_of verus-examples)"
  case "$abs_path" in
    "$vlir_root"/*) echo "vlir-tests" ;;
    "$examples_root"/*) echo "verus-examples" ;;
    *) echo "external" ;;
  esac
}

add_case() {
  local suite="$1"
  local path="$2"
  local entry="${suite}|${path}"
  local e
  for e in "${cases[@]-}"; do
    if [ "$e" = "$entry" ]; then
      return
    fi
  done
  cases+=("$entry")
}

resolve_example_arg() {
  local arg="$1"
  if [ -f "$arg" ]; then
    local abs_dir
    local abs_path
    abs_dir="$(cd "$(dirname "$arg")" && pwd -P)"
    abs_path="$abs_dir/$(basename "$arg")"
    echo "$(infer_suite_from_path "$abs_path")|$abs_path"
    return
  fi

  local base
  local suite
  local dir
  local candidate
  local search_suites=()
  local matches=()
  base=$(basename "$arg")
  base=${base%.rs}

  if [ ${#selected_suites[@]} -gt 0 ]; then
    search_suites=("${selected_suites[@]}")
  else
    search_suites=("vlir-tests" "verus-examples")
  fi

  for suite in "${search_suites[@]}"; do
    dir="$(suite_dir_of "$suite")"
    candidate="$dir/$base.rs"
    if [ -f "$candidate" ]; then
      matches+=("$suite|$candidate")
    fi
  done

  if [ ${#matches[@]} -eq 0 ]; then
    echo "ERROR: example not found: $arg" >&2
    exit 1
  fi
  if [ ${#matches[@]} -gt 1 ]; then
    echo "ERROR: ambiguous example name '$arg'; use a full path." >&2
    printf '%s\n' "${matches[@]}" >&2
    exit 1
  fi
  echo "${matches[0]}"
}

add_suite_files() {
  local suite="$1"
  local dir
  local file
  local base
  dir="$(suite_dir_of "$suite")"
  if [ ! -d "$dir" ]; then
    echo "Missing suite directory: $dir" >&2
    exit 1
  fi
  if [ "$suite" = "verus-examples" ]; then
    # Keep this suite focused: only top-level examples and guide examples.
    # (No other subdirectories like pcm/, state_machines/, std_test/, etc.)
    while IFS= read -r file; do
      # `verified_vec.rs` currently fails before JSON export in upstream Verus
      # due unresolved `vstd::ptr`; skip it in bulk suite runs.
      base="$(basename "$file" .rs)"
      if [ "$base" = "verified_vec" ]; then
        continue
      fi
      add_case "$suite" "$file"
    done < <(find "$dir" -maxdepth 1 -type f -name '*.rs' | sort)

    if [ -d "$dir/guide" ]; then
      while IFS= read -r file; do
        add_case "$suite" "$file"
      done < <(find "$dir/guide" -type f -name '*.rs' | sort)
    fi
  else
    # VLIR tests are a flat directory.
    while IFS= read -r file; do
      add_case "$suite" "$file"
    done < <(find "$dir" -maxdepth 1 -type f -name '*.rs' | sort)
  fi
}

run_logged() {
  local logfile="$1"
  shift
  local rc
  local had_errexit=0
  # Preserve caller errexit mode so failed external commands can be captured
  # as return codes without accidentally terminating the whole regression run.
  case $- in
    *e*) had_errexit=1 ;;
  esac
  set +e
  if $verbose; then
    "$@" 2>&1 | tee "$logfile"
    rc=${PIPESTATUS[0]}
  else
    "$@" >"$logfile" 2>&1
    rc=$?
  fi
  if [ "$had_errexit" -eq 1 ]; then
    set -e
  else
    set +e
  fi
  return "$rc"
}

while [ $# -gt 0 ]; do
  case "$1" in
    --verbose) verbose=true; shift ;;
    --all-suites) run_all_suites=true; shift ;;
    --suite)
      if [ $# -lt 2 ]; then
        echo "Missing value for --suite"
        usage
        exit 1
      fi
      add_selected_suite "$2"
      shift 2
      ;;
    --suite=*)
      add_selected_suite "${1#*=}"
      shift
      ;;
    --solver)
      if [ $# -lt 2 ]; then
        echo "Missing value for --solver"
        usage
        exit 1
      fi
      STRATA_SOLVER="$2"
      shift 2
      ;;
    --solver-timeout)
      if [ $# -lt 2 ]; then
        echo "Missing value for --solver-timeout"
        usage
        exit 1
      fi
      STRATA_SOLVER_TIMEOUT="$2"
      shift 2
      ;;
    --solver=*)
      STRATA_SOLVER="${1#*=}"
      shift
      ;;
    --solver-timeout=*)
      STRATA_SOLVER_TIMEOUT="${1#*=}"
      shift
      ;;
    --list) show_starter_list; exit 0 ;;
    -h|--help) usage; exit 0 ;;
    --) shift; while [ $# -gt 0 ]; do requested_examples+=("$1"); shift; done ;;
    --*) echo "Unknown option: $1"; usage; exit 1 ;;
    *) requested_examples+=("$1"); shift ;;
  esac
done

declare -a STRATA_VERIFY_ARGS=()
if [ -n "$STRATA_SOLVER" ]; then
  STRATA_VERIFY_ARGS+=(--solver "$STRATA_SOLVER")
fi
if [ -n "$STRATA_SOLVER_TIMEOUT" ]; then
  STRATA_VERIFY_ARGS+=(--solver-timeout "$STRATA_SOLVER_TIMEOUT")
fi

if $run_all_suites; then
  add_selected_suite "vlir-tests"
  add_selected_suite "verus-examples"
fi

if [ ! -d "$VERUS_SRC" ]; then
  echo "Missing Verus source dir: $VERUS_SRC" >&2
  exit 1
fi
if [ ! -d "$VERUS_EXAMPLES_DIR" ]; then
  echo "Missing Verus examples dir: $VERUS_EXAMPLES_DIR" >&2
  exit 1
fi
if [ ! -d "$VLIR_TESTS_DIR" ]; then
  echo "Missing VLIR tests dir: $VLIR_TESTS_DIR" >&2
  exit 1
fi
if [ ! -d "$STRATA_DIR" ]; then
  echo "Missing Strata repo dir: $STRATA_DIR" >&2
  exit 1
fi
if [ ! -x "$VERUS_LEAN" ]; then
  echo "Missing verus-lean binary: $VERUS_LEAN (run lake build in verus-boogie)" >&2
  exit 1
fi

mkdir -p "$JSON_BOOGIE_DIR" "$CORE_DIR" "$REGRESSION_LOGS_DIR"

if [ ! -x "$VERUS_BIN" ]; then
  echo "Building Verus binary (not found at $VERUS_BIN)..."
  (
    cd "$VERUS_SRC"
    # shellcheck disable=SC1091
    source ../tools/activate
    vargo build --release --features lean
  )
fi

if [ -f "$VERUS_DIR/tools/activate" ]; then
  # shellcheck disable=SC1091
  source "$VERUS_DIR/tools/activate"
fi

export PATH="$ROOT_DIR/.local/bin:$PATH"

declare -a cases=()
if [ ${#requested_examples[@]} -gt 0 ]; then
  for req in "${requested_examples[@]}"; do
    resolved="$(resolve_example_arg "$req")"
    add_case "${resolved%%|*}" "${resolved#*|}"
  done
elif [ ${#selected_suites[@]} -gt 0 ]; then
  for suite in "${selected_suites[@]}"; do
    add_suite_files "$suite"
  done
else
  for starter in "${STARTER_EXAMPLES[@]}"; do
    add_case "verus-examples" "$VERUS_EXAMPLES_DIR/$starter"
  done
fi

if [ ${#cases[@]} -eq 0 ]; then
  echo "No regression cases selected." >&2
  exit 1
fi

run_id="$(date +%Y%m%d_%H%M%S)"
run_log_dir="$REGRESSION_LOGS_DIR/$run_id"
mkdir -p "$run_log_dir"

declare -a export_failures=()
declare -a expected_empty_exports=()
declare -a translation_failures=()
declare -a strata_parse_failures=()
declare -a verify_failures=()
declare -a ok_cases=()
declare -a mismatch_verus_pass_strata_fail=()
declare -a mismatch_verus_fail_strata_pass=()

echo "Regression run: $run_id"
echo "Cases: ${#cases[@]}"
echo "Logs: $run_log_dir"
echo ""

printf "%-40s  %-7s  %-5s  %-9s  %-7s  %s\n" "case" "verus" "json" "core" "verify" "classification"

for case_entry in "${cases[@]}"; do
  suite="${case_entry%%|*}"
  example="${case_entry#*|}"
  base="$(basename "$example" .rs)"
  suite_root="$(suite_dir_of "$suite" 2>/dev/null || true)"
  if [ -n "$suite_root" ] && [[ "$example" == "$suite_root/"* ]]; then
    rel_path="${example#$suite_root/}"
  else
    if [[ "$example" == "$ROOT_DIR/"* ]]; then
      rel_path="${example#$ROOT_DIR/}"
    elif [[ "$example" == "$VERUS_DIR/"* ]]; then
      rel_path="${example#$VERUS_DIR/}"
    else
      rel_path="$example"
    fi
  fi
  rel_no_ext="${rel_path%.rs}"
  # Use a path-derived key so examples with the same basename do not collide.
  case_key="${rel_no_ext//\//__}"
  case_key="${case_key// /_}"
  case_name="${suite}:${rel_no_ext}"

  suite_json_dir="$JSON_BOOGIE_DIR/$suite/$case_key"
  suite_core_dir="$CORE_DIR/$suite"
  mkdir -p "$suite_json_dir" "$suite_core_dir"
  json="$suite_json_dir/serialized_${base}.json"
  core="$suite_core_dir/serialized_${case_key}.core.st"
  log_safe="${suite//-/_}__${case_key}"

  log_export="$run_log_dir/${log_safe}.verus.log"
  log_translate="$run_log_dir/${log_safe}.translate.log"
  log_verify="$run_log_dir/${log_safe}.verify.log"

  # Keep a per-file backup to distinguish:
  # 1) stale JSON from a previous run (treat as export-missing), and
  # 2) JSON produced during this run, even when Verus exits non-zero.
  json_base_norm="${base//-/_}"
  json_alt1=""
  if [ "$json_base_norm" != "$base" ]; then
    json_alt1="$suite_json_dir/serialized_${json_base_norm}.json"
  fi
  json_alt2=""
  if [ "$base" = "recursion" ]; then
    json_alt2="$suite_json_dir/serialized_recursion_M.json"
  fi
  json_alt3="$suite_json_dir/serialized_${json_base_norm}_lib.json"

  old_json="$suite_json_dir/.serialized_${base}.json.prev.$$"
  had_old_json=false
  if [ -f "$json" ]; then
    had_old_json=true
    mv -f "$json" "$old_json"
  fi

  old_json_alt1=""
  had_old_json_alt1=false
  if [ -n "$json_alt1" ]; then
    old_json_alt1="$suite_json_dir/.serialized_${base//-/_}.json.prev.$$"
    if [ -f "$json_alt1" ]; then
      had_old_json_alt1=true
      mv -f "$json_alt1" "$old_json_alt1"
    fi
  fi

  old_json_alt2=""
  had_old_json_alt2=false
  if [ -n "$json_alt2" ]; then
    old_json_alt2="$suite_json_dir/.serialized_recursion_M.json.prev.$$"
    if [ -f "$json_alt2" ]; then
      had_old_json_alt2=true
      mv -f "$json_alt2" "$old_json_alt2"
    fi
  fi

  old_json_alt3="$suite_json_dir/.serialized_${json_base_norm}_lib.json.prev.$$"
  had_old_json_alt3=false
  if [ -f "$json_alt3" ]; then
    had_old_json_alt3=true
    mv -f "$json_alt3" "$old_json_alt3"
  fi

  set +e
  (
    cd "$suite_json_dir"
    # Some Verus examples are library-style (no `main`), so export in lib mode.
    run_logged "$log_export" "$VERUS_BIN" --export-lean-all "$example" --crate-type=lib
  )
  verus_rc=$?
  set -e

  json_fresh="no"
  if [ -f "$json" ]; then
    json_fresh="yes"
  elif [ -n "$json_alt1" ] && [ -f "$json_alt1" ]; then
    mv -f "$json_alt1" "$json"
    json_fresh="yes"
  elif [ -n "$json_alt2" ] && [ -f "$json_alt2" ]; then
    mv -f "$json_alt2" "$json"
    json_fresh="yes"
  elif [ -f "$json_alt3" ]; then
    mv -f "$json_alt3" "$json"
    json_fresh="yes"
  fi

  if [ "$json_fresh" = "yes" ]; then
    [ -f "$old_json" ] && rm -f "$old_json"
    [ -n "$old_json_alt1" ] && [ -f "$old_json_alt1" ] && rm -f "$old_json_alt1"
    [ -n "$old_json_alt2" ] && [ -f "$old_json_alt2" ] && rm -f "$old_json_alt2"
    [ -f "$old_json_alt3" ] && rm -f "$old_json_alt3"
  else
    if $had_old_json; then
      # Restore prior artifact so local state is preserved for manual inspection.
      mv -f "$old_json" "$json"
    fi
    if $had_old_json_alt1 && [ -n "$old_json_alt1" ]; then
      mv -f "$old_json_alt1" "$json_alt1"
    fi
    if $had_old_json_alt2 && [ -n "$old_json_alt2" ]; then
      mv -f "$old_json_alt2" "$json_alt2"
    fi
    if $had_old_json_alt3; then
      mv -f "$old_json_alt3" "$json_alt3"
    fi
  fi

  core_rc="-"
  verify_rc="-"
  classification=""
  expected_empty_export=false
  if [[ "$example" == */examples/guide/opaque.rs ]]; then
    expected_empty_export=true
  fi

  if [ "$json_fresh" != "yes" ]; then
    if $expected_empty_export; then
      expected_empty_exports+=("$case_name")
      classification="export-empty-expected"
    else
      export_failures+=("$case_name")
      classification="export-missing"
    fi
  else
    tmp_core="$suite_core_dir/.serialized_${base}.core.st.tmp.$$"
    set +e
    run_logged "$log_translate" "$VERUS_LEAN" boogie "$json" "$tmp_core"
    core_rc=$?
    set -e

    if [ "$core_rc" -eq 0 ] && [ -f "$tmp_core" ]; then
      mv -f "$tmp_core" "$core"

      set +e
      (
        cd "$STRATA_DIR"
        run_logged "$log_verify" lake exe StrataVerify ${STRATA_VERIFY_ARGS[@]-} "$core"
      )
      verify_rc=$?
      set -e

      if [ "$verify_rc" -ne 0 ]; then
        if grep -q "Successfully parsed\\." "$log_verify"; then
          verify_failures+=("$case_name")
          classification="verify-failed"
        else
          strata_parse_failures+=("$case_name")
          classification="strata-parse-failed"
        fi
      else
        ok_cases+=("$case_name")
        classification="ok"
      fi
    else
      if [ "$core_rc" -eq 0 ] && [ ! -f "$tmp_core" ]; then
        core_rc="missing"
      fi
      translation_failures+=("$case_name")
      classification="translate-failed"
      [ -f "$tmp_core" ] && rm -f "$tmp_core"
    fi
  fi

  if [ "$classification" = "ok" ] || [ "$classification" = "verify-failed" ]; then
    if [ "$verus_rc" -eq 0 ] && [ "$verify_rc" -ne 0 ]; then
      mismatch_verus_pass_strata_fail+=("$case_name")
    elif [ "$verus_rc" -ne 0 ] && [ "$verify_rc" -eq 0 ]; then
      mismatch_verus_fail_strata_pass+=("$case_name")
    fi
  fi

  printf "%-40s  %-7s  %-5s  %-9s  %-7s  %s\n" \
    "$case_name" "$verus_rc" "$json_fresh" "$core_rc" "$verify_rc" "$classification"
done

echo ""
echo "Summary:"
echo "  total cases: ${#cases[@]}"
echo "  ok: ${#ok_cases[@]}"
echo "  export failures: ${#export_failures[@]}"
echo "  expected empty exports: ${#expected_empty_exports[@]}"
echo "  translate failures: ${#translation_failures[@]}"
echo "  strata parse failures: ${#strata_parse_failures[@]}"
echo "  verify failures: ${#verify_failures[@]}"
echo "  mismatch (Verus pass, Strata fail): ${#mismatch_verus_pass_strata_fail[@]}"
echo "  mismatch (Verus fail, Strata pass): ${#mismatch_verus_fail_strata_pass[@]}"

if [ ${#ok_cases[@]} -gt 0 ]; then
  echo "  ok list: ${ok_cases[*]}"
  echo ""
fi
if [ ${#export_failures[@]} -gt 0 ]; then
  echo "  export failures list: ${export_failures[*]}"
  echo ""
fi
if [ ${#expected_empty_exports[@]} -gt 0 ]; then
  echo "  expected empty exports list: ${expected_empty_exports[*]}"
  echo ""
fi
if [ ${#strata_parse_failures[@]} -gt 0 ]; then
  echo "  strata parse failures list: ${strata_parse_failures[*]}"
  echo ""
fi
if [ ${#verify_failures[@]} -gt 0 ]; then
  echo "  verify failures list: ${verify_failures[*]}"
  echo ""
fi
if [ ${#mismatch_verus_pass_strata_fail[@]} -gt 0 ]; then
  echo "  mismatch list (Verus pass, Strata fail): ${mismatch_verus_pass_strata_fail[*]}"
  echo ""
fi
if [ ${#mismatch_verus_fail_strata_pass[@]} -gt 0 ]; then
  echo "  mismatch list (Verus fail, Strata pass): ${mismatch_verus_fail_strata_pass[*]}"
  echo ""
fi

echo "Detailed logs: $run_log_dir"
