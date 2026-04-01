#!/bin/bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERUS_DIR="$(cd "$ROOT_DIR/../verus" && pwd -P)"
VERUS_SRC="$VERUS_DIR/source"
VERUS_EXAMPLES_DIR="$VERUS_DIR/examples"
VERUS_TESTS_DIR="$VERUS_DIR/tests"
VLIR_TESTS_DIR="$ROOT_DIR/tests/VerusFiles"
RVT_DEBUG_INPUTS_DIR="$VERUS_SRC/target/debug/test_inputs"
RVT_RELEASE_INPUTS_DIR="$VERUS_SRC/target/release/test_inputs"
VERUS_BIN="$VERUS_SRC/target-verus/release/verus"
VERUS_LEAN="$ROOT_DIR/.lake/build/bin/verus-lean"
STRATA_DIR="$(cd "$ROOT_DIR/../Strata" && pwd -P)"

JSON_BOOGIE_DIR="${JSON_BOOGIE_DIR:-$ROOT_DIR/tests/JSONFilesBoogie}"
CORE_DIR="${CORE_DIR:-$ROOT_DIR/tests/BoogieFiles}"
REGRESSION_LOGS_DIR="${REGRESSION_LOGS_DIR:-$ROOT_DIR/tests/RegressionLogs}"
RVT_CURATED_LIST="${RVT_CURATED_LIST:-$ROOT_DIR/tests/rust_verify_generated_cases.txt}"

verbose=false
run_all_suites=false
declare -a selected_suites=()
declare -a requested_examples=()
STRATA_SOLVER="cvc5"
STRATA_SOLVER_TIMEOUT=""

usage() {
  cat <<'EOF'
Usage: tests/regress_examples.sh [options] [target.rs ...]

Runs regression across 3 stages for each Verus example:
  1) Verus export (--export-lean-all)
  2) Verus-Lean JSON -> Core translation
  3) strata verify on generated Core file

Options:
  --verbose         Stream command output while also saving logs
  --all-suites      Run vlir-tests + verus-examples
  --suite <name>    Add a suite: vlir-tests | verus-examples | rust-verify-generated
  --rvt-list <file> Curated path list for rust-verify-generated suite
                    (default: tests/rust_verify_generated_cases.txt)
  --solver <name>   strata verify solver (default: cvc5)
  --solver-timeout <sec>
                    strata verify timeout in seconds
  -h, --help        Show this help

Examples:
  tests/regress_examples.sh /abs/path/to/verus/examples/assertions.rs
  tests/regress_examples.sh tests/VerusFiles/FindMax.rs
  tests/regress_examples.sh --suite verus-examples
  tests/regress_examples.sh --suite vlir-tests
  tests/regress_examples.sh --suite rust-verify-generated
  tests/regress_examples.sh --all-suites

EOF
}

is_known_suite() {
  case "$1" in
    vlir-tests|verus-examples|rust-verify-generated) return 0 ;;
    *) return 1 ;;
  esac
}

suite_dir_of() {
  case "$1" in
    vlir-tests) (cd "$VLIR_TESTS_DIR" && pwd -P) ;;
    verus-examples) (cd "$VERUS_EXAMPLES_DIR" && pwd -P) ;;
    rust-verify-generated) (cd "$VERUS_SRC/target" && pwd -P) ;;
    *) return 1 ;;
  esac
}

add_selected_suite() {
  local suite="$1"
  if ! is_known_suite "$suite"; then
    echo "Unknown suite: $suite" >&2
    echo "Valid suites: vlir-tests, verus-examples, rust-verify-generated" >&2
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
  local vlir_root examples_root tests_root rvt_debug_root rvt_release_root
  abs_dir="$(cd "$(dirname "$path")" && pwd -P)"
  abs_path="$abs_dir/$(basename "$path")"
  vlir_root="$(suite_dir_of vlir-tests)"
  examples_root="$(suite_dir_of verus-examples)"
  tests_root="$(cd "$VERUS_TESTS_DIR" && pwd -P)"
  rvt_debug_root="$(cd "$RVT_DEBUG_INPUTS_DIR" 2>/dev/null && pwd -P || true)"
  rvt_release_root="$(cd "$RVT_RELEASE_INPUTS_DIR" 2>/dev/null && pwd -P || true)"
  case "$abs_path" in
    "$vlir_root"/*) echo "vlir-tests" ;;
    "$examples_root"/*) echo "verus-examples" ;;
    "$tests_root"/*) echo "vlir-tests" ;;
    "$rvt_debug_root"/*) echo "rust-verify-generated" ;;
    "$rvt_release_root"/*) echo "rust-verify-generated" ;;
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
  if [ ! -f "$arg" ]; then
    echo "ERROR: example path not found: $arg" >&2
    exit 1
  fi

  case "$arg" in
    *.rs) ;;
    *)
      echo "ERROR: expected a .rs file path, got: $arg" >&2
      exit 1
      ;;
  esac

  local abs_dir
  local abs_path
  abs_dir="$(cd "$(dirname "$arg")" && pwd -P)"
  abs_path="$abs_dir/$(basename "$arg")"

  local suite
  suite="$(infer_suite_from_path "$abs_path")"
  if [ "$suite" = "external" ]; then
    echo "ERROR: file must be under tests/VerusFiles, verus/examples, verus/tests," \
      "or verus/source/target/*/test_inputs for rust-verify-generated suite: $abs_path" >&2
    exit 1
  fi
  echo "$suite|$abs_path"
}

resolve_rvt_case_path() {
  local listed_path="$1"
  if [[ "$listed_path" == *"::"* ]]; then
    local test_file case_name
    local pattern
    local matches=()
    test_file="${listed_path%%::*}"
    case_name="${listed_path#*::}"
    pattern="${test_file}-*-${case_name}"

    if [ -d "$RVT_DEBUG_INPUTS_DIR" ]; then
      while IFS= read -r d; do
        matches+=("$d")
      done < <(find "$RVT_DEBUG_INPUTS_DIR" -maxdepth 1 -type d -name "$pattern" | sort)
    fi
    if [ -d "$RVT_RELEASE_INPUTS_DIR" ]; then
      while IFS= read -r d; do
        matches+=("$d")
      done < <(find "$RVT_RELEASE_INPUTS_DIR" -maxdepth 1 -type d -name "$pattern" | sort)
    fi

    if [ ${#matches[@]} -eq 0 ]; then
      echo "No generated rust_verify_test input matches selector: $listed_path" >&2
      echo "Expected a directory like: ${pattern}/test.rs under target/*/test_inputs" >&2
      exit 1
    fi
    if [ ${#matches[@]} -gt 1 ]; then
      local newest
      newest="${matches[0]}"
      local m
      for m in "${matches[@]}"; do
        if [ "$m" -nt "$newest" ]; then
          newest="$m"
        fi
      done
      echo "$newest/test.rs"
      return
    fi
    local match_file="${matches[0]}/test.rs"
    if [ ! -f "$match_file" ]; then
      echo "Matched generated input has no test.rs: ${matches[0]}" >&2
      exit 1
    fi
    echo "$match_file"
    return
  fi

  local candidate=""
  if [ -f "$listed_path" ]; then
    candidate="$listed_path"
  elif [ -f "$ROOT_DIR/$listed_path" ]; then
    candidate="$ROOT_DIR/$listed_path"
  elif [ -f "$VERUS_DIR/$listed_path" ]; then
    candidate="$VERUS_DIR/$listed_path"
  elif [ -f "$VERUS_SRC/$listed_path" ]; then
    candidate="$VERUS_SRC/$listed_path"
  else
    echo "Missing rust-verify-generated case path from list: $listed_path" >&2
    exit 1
  fi

  case "$candidate" in
    *.rs) ;;
    *)
      echo "rust-verify-generated entry is not an .rs file: $candidate" >&2
      exit 1
      ;;
  esac

  local abs_dir
  abs_dir="$(cd "$(dirname "$candidate")" && pwd -P)"
  echo "$abs_dir/$(basename "$candidate")"
}

add_suite_files() {
  local suite="$1"
  if [ "$suite" = "rust-verify-generated" ]; then
    if [ ! -f "$RVT_CURATED_LIST" ]; then
      echo "Missing rust-verify-generated list: $RVT_CURATED_LIST" >&2
      echo "Create it with one .rs path per line (comments with # are allowed)." >&2
      exit 1
    fi
    local line file count
    count=0
    while IFS= read -r line; do
      line="$(echo "$line" | sed -e 's/#.*$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')"
      [ -n "$line" ] || continue
      file="$(resolve_rvt_case_path "$line")"
      add_case "$suite" "$file"
      count=$((count + 1))
    done < "$RVT_CURATED_LIST"
    if [ "$count" -eq 0 ]; then
      echo "No rust-verify-generated cases found in $RVT_CURATED_LIST" >&2
      exit 1
    fi
    return
  fi

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
    # Fold in upstream verus/tests coverage that is not mirrored in VLIR tests.
    while IFS= read -r file; do
      local file_abs
      file_abs="$(cd "$(dirname "$file")" && pwd -P)/$(basename "$file")"
      base="$(basename "$file")"
      if [ -f "$VLIR_TESTS_DIR/$base" ]; then
        continue
      fi
      add_case "$suite" "$file_abs"
    done < <(find "$VERUS_TESTS_DIR" -maxdepth 1 -type f -name '*.rs' | sort)
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

is_strata_parse_failure_log() {
  local logfile="$1"
  rg -q \
    "expected token|unexpected token|unexpected end of input|parse error|parser error|invalid syntax" \
    "$logfile"
}

is_strata_type_failure_log() {
  local logfile="$1"
  rg -q \
    "Type checking error|Expression has type|Encountered .* expected|Undeclared type or category|Unknown variable|Unknown expr identifier|Unknown identifier|Arity mismatch|Expected category|modifies variables it is not allowed to|Unexpected argument|Unexpected arguments" \
    "$logfile"
}

# Known expected Verus/Strata outcome mismatches (kept out of mismatch counts).
is_expected_mismatch_verus_fail_strata_pass() {
  local case_name="$1"
  case "$case_name" in
    # Expected today: Verus marks this example failing, while current Strata
    # discharges the translated VC set. Keep it out of mismatch regressions.
    vlir-tests:LoopSimple) return 0 ;;
    *) return 1 ;;
  esac
}

run_export() {
  local dylib_ext dylib_prefix target_verus_dir
  local builtin_rlib builtin_macros_dylib sm_macros_dylib vstd_rlib vstd_vir
  set +e
  (
    cd "$suite_json_dir"
    if [ "$suite" = "rust-verify-generated" ]; then
      case "$(uname -s)" in
        Darwin) dylib_prefix="lib"; dylib_ext="dylib" ;;
        Linux) dylib_prefix="lib"; dylib_ext="so" ;;
        MINGW*|MSYS*|CYGWIN*) dylib_prefix=""; dylib_ext="dll" ;;
        *)
          echo "Unsupported platform for rust-verify-generated suite: $(uname -s)" >&2
          exit 1
          ;;
      esac
      target_verus_dir="$VERUS_SRC/target-verus/release"
      builtin_rlib="$target_verus_dir/libverus_builtin.rlib"
      builtin_macros_dylib="$target_verus_dir/${dylib_prefix}verus_builtin_macros.${dylib_ext}"
      sm_macros_dylib="$target_verus_dir/${dylib_prefix}verus_state_machines_macros.${dylib_ext}"
      vstd_rlib="$target_verus_dir/libvstd.rlib"
      vstd_vir="$target_verus_dir/vstd.vir"
      # Generated rust_verify_test inputs rely on the same internal-test harness
      # extern setup used by Verus' own rust_verify_test harness.
      run_logged "$log_export" "$VERUS_BIN" \
        --internal-test-mode \
        --crate-name "$base" \
        --crate-type=lib \
        --cfg vstd_todo \
        --extern "builtin=$builtin_rlib" \
        --extern "verus_builtin=$builtin_rlib" \
        --extern "builtin_macros=$builtin_macros_dylib" \
        --extern "verus_builtin_macros=$builtin_macros_dylib" \
        --extern "state_machines_macros=$sm_macros_dylib" \
        --extern "verus_state_machines_macros=$sm_macros_dylib" \
        --extern "vstd=$vstd_rlib" \
        --import "vstd=$vstd_vir" \
        -L "dependency=$target_verus_dir" \
        --export-lean-all "$example"
    else
      # Some Verus examples are library-style (no `main`), so export in lib mode.
      run_logged "$log_export" "$VERUS_BIN" --export-lean-all "$example" --crate-type=lib
    fi
  )
  verus_rc=$?
  set -e
}

select_json_artifact() {
  json_fresh="no"
  if [ -f "$gen_json" ]; then
    if [ "$gen_json" != "$json" ]; then
      mv -f "$gen_json" "$json"
    fi
    json_fresh="yes"
  elif [ -n "$gen_json_alt1" ] && [ -f "$gen_json_alt1" ]; then
    if [ "$gen_json_alt1" != "$json" ]; then
      mv -f "$gen_json_alt1" "$json"
    fi
    json_fresh="yes"
  elif [ -n "$gen_json_alt2" ] && [ -f "$gen_json_alt2" ]; then
    if [ "$gen_json_alt2" != "$json" ]; then
      mv -f "$gen_json_alt2" "$json"
    fi
    json_fresh="yes"
  elif [ -f "$gen_json_alt3" ]; then
    if [ "$gen_json_alt3" != "$json" ]; then
      mv -f "$gen_json_alt3" "$json"
    fi
    json_fresh="yes"
  fi

  if [ "$json_fresh" = "yes" ]; then
    if [ -f "$old_gen_json" ]; then
      rm -f "$old_gen_json"
    fi
    if [ -n "$old_gen_json_alt1" ] && [ -f "$old_gen_json_alt1" ]; then
      rm -f "$old_gen_json_alt1"
    fi
    if [ -n "$old_gen_json_alt2" ] && [ -f "$old_gen_json_alt2" ]; then
      rm -f "$old_gen_json_alt2"
    fi
    if [ -f "$old_gen_json_alt3" ]; then
      rm -f "$old_gen_json_alt3"
    fi
  else
    if $had_old_gen_json; then
      # Restore prior artifact so local state is preserved for manual inspection.
      mv -f "$old_gen_json" "$gen_json"
    fi
    if $had_old_gen_json_alt1 && [ -n "$old_gen_json_alt1" ]; then
      mv -f "$old_gen_json_alt1" "$gen_json_alt1"
    fi
    if $had_old_gen_json_alt2 && [ -n "$old_gen_json_alt2" ]; then
      mv -f "$old_gen_json_alt2" "$gen_json_alt2"
    fi
    if $had_old_gen_json_alt3; then
      mv -f "$old_gen_json_alt3" "$gen_json_alt3"
    fi
  fi
}

run_translate() {
  tmp_core="$suite_core_dir/.${base}.core.st.tmp.$$"
  translated_ok="no"
  set +e
  run_logged "$log_translate" "$VERUS_LEAN" boogie "$json" "$tmp_core"
  core_rc=$?
  set -e

  if [ "$core_rc" -eq 0 ] && [ -f "$tmp_core" ]; then
    mv -f "$tmp_core" "$core"
    translated_ok="yes"
  else
    if [ "$core_rc" -eq 0 ] && [ ! -f "$tmp_core" ]; then
      core_rc="missing"
    fi
    if [ -f "$tmp_core" ]; then
      rm -f "$tmp_core"
    fi
  fi
}

run_verify() {
  set +e
  (
    cd "$STRATA_DIR"
    run_logged "$log_verify" lake exe strata verify ${STRATA_VERIFY_ARGS[@]-} "$core"
  )
  verify_rc=$?
  set -e
}

classify_case() {
  classification=""
  if [ "$json_fresh" != "yes" ]; then
    if $expected_empty_export; then
      expected_empty_exports+=("$case_name")
      classification="export-empty-expected"
    else
      export_failures+=("$case_name")
      classification="export-missing"
    fi
    return
  fi

  if [ "$translated_ok" != "yes" ]; then
    translation_failures+=("$case_name")
    classification="translate-failed"
    return
  fi

  if [ "$verify_rc" -ne 0 ]; then
    if is_strata_parse_failure_log "$log_verify"; then
      strata_parse_failures+=("$case_name")
      classification="strata-parse-failed"
    elif is_strata_type_failure_log "$log_verify"; then
      strata_type_failures+=("$case_name")
      classification="strata-type-failed"
    elif grep -q "Successfully parsed\\." "$log_verify"; then
      verify_failures+=("$case_name")
      classification="verify-failed"
    else
      strata_parse_failures+=("$case_name")
      classification="strata-parse-failed"
    fi
  else
    classification="ok"
  fi

  if [ "$classification" = "ok" ] || [ "$classification" = "verify-failed" ]; then
    if [ "$verus_rc" -eq 0 ] && [ "$verify_rc" -ne 0 ]; then
      mismatch_verus_pass_strata_fail+=("$case_name")
    elif [ "$verus_rc" -ne 0 ] && [ "$verify_rc" -eq 0 ]; then
      if is_expected_mismatch_verus_fail_strata_pass "$case_name"; then
        classification="expected-mismatch"
        expected_mismatches+=("$case_name")
      else
        mismatch_verus_fail_strata_pass+=("$case_name")
      fi
    fi
  fi

  if [ "$classification" = "ok" ]; then
    ok_cases+=("$case_name")
  fi
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
    --rvt-list)
      if [ $# -lt 2 ]; then
        echo "Missing value for --rvt-list"
        usage
        exit 1
      fi
      RVT_CURATED_LIST="$2"
      shift 2
      ;;
    --rvt-list=*)
      RVT_CURATED_LIST="${1#*=}"
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
if [ ! -d "$VERUS_TESTS_DIR" ]; then
  echo "Missing Verus tests dir: $VERUS_TESTS_DIR" >&2
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
  echo "No cases selected."
  echo "Provide .rs paths, or use --suite/--all-suites."
  usage
  exit 1
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
declare -a strata_type_failures=()
declare -a verify_failures=()
declare -a ok_cases=()
declare -a expected_mismatches=()
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
  json="$suite_json_dir/${base}.json"
  core="$suite_core_dir/${case_key}.core.st"
  log_safe="${suite//-/_}__${case_key}"

  log_export="$run_log_dir/${log_safe}.verus.log"
  log_translate="$run_log_dir/${log_safe}.translate.log"
  log_verify="$run_log_dir/${log_safe}.verify.log"

  # Keep a per-file backup to distinguish:
  # 1) stale JSON from a previous run (treat as export-missing), and
  # 2) JSON produced during this run, even when Verus exits non-zero.
  json_base_norm="${base//-/_}"
  gen_json="$suite_json_dir/${base}.json"
  gen_json_alt1=""
  if [ "$json_base_norm" != "$base" ]; then
    gen_json_alt1="$suite_json_dir/${json_base_norm}.json"
  fi
  gen_json_alt2=""
  if [ "$base" = "recursion" ]; then
    gen_json_alt2="$suite_json_dir/recursion_M.json"
  fi
  gen_json_alt3="$suite_json_dir/${json_base_norm}_lib.json"

  old_gen_json="$suite_json_dir/.${base}.json.prev.$$"
  had_old_gen_json=false
  if [ -f "$gen_json" ]; then
    had_old_gen_json=true
    mv -f "$gen_json" "$old_gen_json"
  fi

  old_gen_json_alt1=""
  had_old_gen_json_alt1=false
  if [ -n "$gen_json_alt1" ]; then
    old_gen_json_alt1="$suite_json_dir/.${base//-/_}.json.prev.$$"
    if [ -f "$gen_json_alt1" ]; then
      had_old_gen_json_alt1=true
      mv -f "$gen_json_alt1" "$old_gen_json_alt1"
    fi
  fi

  old_gen_json_alt2=""
  had_old_gen_json_alt2=false
  if [ -n "$gen_json_alt2" ]; then
    old_gen_json_alt2="$suite_json_dir/.recursion_M.json.prev.$$"
    if [ -f "$gen_json_alt2" ]; then
      had_old_gen_json_alt2=true
      mv -f "$gen_json_alt2" "$old_gen_json_alt2"
    fi
  fi

  old_gen_json_alt3="$suite_json_dir/.${json_base_norm}_lib.json.prev.$$"
  had_old_gen_json_alt3=false
  if [ -f "$gen_json_alt3" ]; then
    had_old_gen_json_alt3=true
    mv -f "$gen_json_alt3" "$old_gen_json_alt3"
  fi

  run_export
  select_json_artifact

  core_rc="-"
  verify_rc="-"
  classification=""
  translated_ok="no"
  expected_empty_export=false
  if [[ "$example" == */examples/guide/opaque.rs ]]; then
    expected_empty_export=true
  fi

  if [ "$json_fresh" = "yes" ]; then
    run_translate
    if [ "$translated_ok" = "yes" ]; then
      run_verify
    fi
  fi
  classify_case

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
echo "  strata type failures: ${#strata_type_failures[@]}"
echo "  verify failures: ${#verify_failures[@]}"
echo "  expected mismatches: ${#expected_mismatches[@]}"
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
if [ ${#strata_type_failures[@]} -gt 0 ]; then
  echo "  strata type failures list: ${strata_type_failures[*]}"
  echo ""
fi
if [ ${#verify_failures[@]} -gt 0 ]; then
  echo "  verify failures list: ${verify_failures[*]}"
  echo ""
fi
if [ ${#expected_mismatches[@]} -gt 0 ]; then
  echo "  expected mismatches list: ${expected_mismatches[*]}"
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
