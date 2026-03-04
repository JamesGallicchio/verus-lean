#!/bin/bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERUS_DIR="$(cd "$ROOT_DIR/../verus" && pwd -P)"
VERUS_SRC="$VERUS_DIR/source"
VERUS_EXAMPLES_DIR="$VERUS_DIR/examples"
VERUS_TESTS_DIR="$VERUS_DIR/tests"
VERUS_RUST_VERIFY_TESTS_DIR="$VERUS_SRC/rust_verify_test/tests"
VERUS_RVT_INPUTS_DIR="${VERUS_RVT_INPUTS_DIR:-$VERUS_SRC/target/debug/test_inputs}"
VLIR_TESTS_DIR="$ROOT_DIR/tests/VerusFiles"
VERUS_BIN="$VERUS_SRC/target-verus/release/verus"
VERUS_LEAN="$ROOT_DIR/.lake/build/bin/verus-lean"
STRATA_DIR="$(cd "$ROOT_DIR/../Strata" && pwd -P)"

JSON_BOOGIE_DIR="${JSON_BOOGIE_DIR:-$ROOT_DIR/tests/JSONFilesBoogie}"
CORE_DIR="${CORE_DIR:-$ROOT_DIR/tests/BoogieFiles}"
REGRESSION_LOGS_DIR="${REGRESSION_LOGS_DIR:-$ROOT_DIR/tests/RegressionLogs}"

verbose=false
run_all_suites=false
declare -a selected_suites=()
declare -a requested_examples=()
STRATA_SOLVER="cvc5"
STRATA_SOLVER_TIMEOUT=""
declare -a rvt_expected_err_keys=()
declare -a rvt_expected_rust_compile_error_keys=()
# Bash 3 on macOS has no associative arrays; store deduped keys in temp files
# for fast membership checks via `grep -Fx`.
rvt_expected_err_keys_index=""
rvt_expected_rust_compile_error_keys_index=""
have_rvt_expected_rust_compile_errors=false
skipped_expected_err_cases=0
skipped_rust_compile_error_cases=0

cleanup_regress_temp_files() {
  if [ -n "${rvt_expected_err_keys_index:-}" ] && [ -f "$rvt_expected_err_keys_index" ]; then
    rm -f "$rvt_expected_err_keys_index"
  fi
  if [ -n "${rvt_expected_rust_compile_error_keys_index:-}" ] && [ -f "$rvt_expected_rust_compile_error_keys_index" ]; then
    rm -f "$rvt_expected_rust_compile_error_keys_index"
  fi
}
trap cleanup_regress_temp_files EXIT

usage() {
  cat <<'EOF'
Usage: tests/regress_examples.sh [options] [target.rs ...]

Runs regression across 3 stages for each Verus example:
  1) Verus export (--export-lean-all)
  2) Verus-Lean JSON -> Core translation
  3) StrataVerify on generated Core file

Options:
  --verbose         Stream command output while also saving logs
  --all-suites      Run vlir-tests + verus-examples + rust-verify-tests
  --suite <name>    Add a suite: vlir-tests | verus-examples | rust-verify-tests
  --solver <name>   StrataVerify solver (default: cvc5)
  --solver-timeout <sec>
                    StrataVerify timeout in seconds
  -h, --help        Show this help

Examples:
  tests/regress_examples.sh /abs/path/to/verus/examples/assertions.rs
  tests/regress_examples.sh tests/VerusFiles/FindMax.rs
  tests/regress_examples.sh ../verus/source/target/debug/test_inputs/basic-*/test.rs
  tests/regress_examples.sh --suite verus-examples
  tests/regress_examples.sh --suite vlir-tests
  tests/regress_examples.sh --suite rust-verify-tests
  tests/regress_examples.sh --all-suites

EOF
}

is_known_suite() {
  case "$1" in
    vlir-tests|verus-examples|rust-verify-tests) return 0 ;;
    *) return 1 ;;
  esac
}

suite_dir_of() {
  case "$1" in
    vlir-tests) (cd "$VLIR_TESTS_DIR" && pwd -P) ;;
    verus-examples) (cd "$VERUS_EXAMPLES_DIR" && pwd -P) ;;
    rust-verify-tests)
      if [ -d "$VERUS_RVT_INPUTS_DIR" ]; then
        (cd "$VERUS_RVT_INPUTS_DIR" && pwd -P)
      else
        echo "$VERUS_RVT_INPUTS_DIR"
      fi
      ;;
    *) return 1 ;;
  esac
}

add_selected_suite() {
  local suite="$1"
  if ! is_known_suite "$suite"; then
    echo "Unknown suite: $suite" >&2
    echo "Valid suites: vlir-tests, verus-examples, rust-verify-tests" >&2
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
  local vlir_root examples_root tests_root rvt_inputs_root
  abs_dir="$(cd "$(dirname "$path")" && pwd -P)"
  abs_path="$abs_dir/$(basename "$path")"
  vlir_root="$(suite_dir_of vlir-tests)"
  examples_root="$(suite_dir_of verus-examples)"
  tests_root="$(cd "$VERUS_TESTS_DIR" && pwd -P)"
  rvt_inputs_root="$(suite_dir_of rust-verify-tests)"
  case "$abs_path" in
    "$vlir_root"/*) echo "vlir-tests" ;;
    "$examples_root"/*) echo "verus-examples" ;;
    "$tests_root"/*) echo "vlir-tests" ;;
    "$rvt_inputs_root"/*) echo "rust-verify-tests" ;;
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
  local rvt_tests_root
  abs_dir="$(cd "$(dirname "$arg")" && pwd -P)"
  abs_path="$abs_dir/$(basename "$arg")"
  rvt_tests_root="$(cd "$VERUS_RUST_VERIFY_TESTS_DIR" && pwd -P)"
  if [[ "$abs_path" == "$rvt_tests_root/"* ]]; then
    echo "rust-verify-tests-source|$abs_path"
    return 0
  fi

  local suite
  suite="$(infer_suite_from_path "$abs_path")"
  if [ "$suite" = "external" ]; then
    echo "ERROR: file must be under tests/VerusFiles, verus/examples, verus/tests," \
      "or verus/source/target/debug/test_inputs: $abs_path" >&2
    exit 1
  fi
  echo "$suite|$abs_path"
}

collect_rust_verify_expected_rust_compile_errors() {
  if $have_rvt_expected_rust_compile_errors; then
    return
  fi
  # rust_verify_test contains many intentional negative tests (`=> Err(...)`).
  # Exclude those from translation-differential stats. Also record the subset
  # that explicitly expects Rust compile errors (`assert_rust_error_msg`).
  local file file_base test_name pending_test in_matches_syntax_err_macro
  while IFS= read -r file; do
    file_base="$(basename "$file" .rs)"
    pending_test=""
    in_matches_syntax_err_macro=false
    while IFS= read -r line; do
      if [[ "$line" == *"test_matches_syntax_err! {"* ]]; then
        in_matches_syntax_err_macro=true
      fi
      if [[ "$line" =~ \#\[test\][[:space:]]+([A-Za-z0-9_]+) ]]; then
        pending_test="${BASH_REMATCH[1]}"
        if $in_matches_syntax_err_macro; then
          local macro_err_key="$file_base:$pending_test"
          rvt_expected_err_keys+=("$macro_err_key")
        fi
        continue
      fi
      if [ -n "$pending_test" ] && [[ "$line" == *"=> Err("* ]]; then
        local err_key="$file_base:$pending_test"
        rvt_expected_err_keys+=("$err_key")
      fi
      if [ -n "$pending_test" ] && [[ "$line" == *"assert_rust_error_msg"* ]]; then
        local key="$file_base:$pending_test"
        rvt_expected_rust_compile_error_keys+=("$key")
        pending_test=""
      fi
      if $in_matches_syntax_err_macro && [[ "$line" == *"}"* ]]; then
        in_matches_syntax_err_macro=false
      fi
    done < "$file"
  done < <(find "$VERUS_RUST_VERIFY_TESTS_DIR" -maxdepth 1 -type f -name '*.rs' | sort)
  # Bash 3 on macOS has no associative arrays; use sorted lookup indexes.
  if [ -n "$rvt_expected_err_keys_index" ] && [ -f "$rvt_expected_err_keys_index" ]; then
    rm -f "$rvt_expected_err_keys_index"
  fi
  if [ -n "$rvt_expected_rust_compile_error_keys_index" ] && [ -f "$rvt_expected_rust_compile_error_keys_index" ]; then
    rm -f "$rvt_expected_rust_compile_error_keys_index"
  fi
  rvt_expected_err_keys_index="$(mktemp "${TMPDIR:-/tmp}/rvt_expected_err_keys.XXXXXX")"
  rvt_expected_rust_compile_error_keys_index="$(mktemp "${TMPDIR:-/tmp}/rvt_expected_rust_compile_error_keys.XXXXXX")"
  if [ ${#rvt_expected_err_keys[@]} -gt 0 ]; then
    printf '%s\n' "${rvt_expected_err_keys[@]}" | sort -u > "$rvt_expected_err_keys_index"
  else
    : > "$rvt_expected_err_keys_index"
  fi
  if [ ${#rvt_expected_rust_compile_error_keys[@]} -gt 0 ]; then
    printf '%s\n' "${rvt_expected_rust_compile_error_keys[@]}" | sort -u > "$rvt_expected_rust_compile_error_keys_index"
  else
    : > "$rvt_expected_rust_compile_error_keys_index"
  fi
  have_rvt_expected_rust_compile_errors=true
}

rvt_expected_err_case() {
  local key="$1"
  [ -n "$rvt_expected_err_keys_index" ] || return 1
  [ -f "$rvt_expected_err_keys_index" ] || return 1
  grep -Fxq -- "$key" "$rvt_expected_err_keys_index"
}

rvt_expected_rust_compile_error_case() {
  local key="$1"
  [ -n "$rvt_expected_rust_compile_error_keys_index" ] || return 1
  [ -f "$rvt_expected_rust_compile_error_keys_index" ] || return 1
  grep -Fxq -- "$key" "$rvt_expected_rust_compile_error_keys_index"
}

add_rust_verify_generated_cases_for_test_name() {
  local test_name="$1"
  local latest_entry latest_dir dir_base rest hash dir case_suffix
  collect_rust_verify_expected_rust_compile_errors
  latest_entry="$(
    find "$VERUS_RVT_INPUTS_DIR" -maxdepth 1 -type d -name "${test_name}-*-*" | while IFS= read -r dir; do
      mtime="$(stat -f %m "$dir" 2>/dev/null || stat -c %Y "$dir" 2>/dev/null || echo 0)"
      printf "%s %s\n" "$mtime" "$dir"
    done | sort -nr | head -n 1
  )"
  if [ -z "$latest_entry" ]; then
    return
  fi
  latest_dir="${latest_entry#* }"
  dir_base="$(basename "$latest_dir")"
  rest="${dir_base#${test_name}-}"
  hash="${rest%%-*}"
  while IFS= read -r dir; do
    if [ -f "$dir/test.rs" ]; then
      case_suffix="$(basename "$dir")"
      case_suffix="${case_suffix#${test_name}-${hash}-}"
      case_suffix="${case_suffix%__test}"
      if rvt_expected_err_case "$test_name:$case_suffix"; then
        skipped_expected_err_cases=$((skipped_expected_err_cases + 1))
        if rvt_expected_rust_compile_error_case "$test_name:$case_suffix"; then
          skipped_rust_compile_error_cases=$((skipped_rust_compile_error_cases + 1))
        fi
        continue
      fi
      if rvt_expected_rust_compile_error_case "$test_name:$case_suffix"; then
        # Keep this as a fallback in case source parsing misses a surrounding
        # `=> Err(...)` marker.
        skipped_rust_compile_error_cases=$((skipped_rust_compile_error_cases + 1))
        continue
      fi
      add_case "rust-verify-tests" "$dir/test.rs"
    fi
  done < <(find "$VERUS_RVT_INPUTS_DIR" -maxdepth 1 -type d -name "${test_name}-${hash}-*" | sort)
}

add_rust_verify_generated_cases_all() {
  local test_file test_name
  while IFS= read -r test_file; do
    test_name="$(basename "$test_file" .rs)"
    add_rust_verify_generated_cases_for_test_name "$test_name"
  done < <(find "$VERUS_RUST_VERIFY_TESTS_DIR" -maxdepth 1 -type f -name '*.rs' | sort)
}

materialize_rust_verify_inputs() {
  local rc
  echo "Materializing rust_verify_test inputs under $VERUS_RVT_INPUTS_DIR ..."
  set +e
  (
    cd "$VERUS_SRC"
    # shellcheck disable=SC1091
    source ../tools/activate
    if $verbose; then
      vargo test -p rust_verify_test --tests -- --nocapture
    else
      vargo test -p rust_verify_test --tests -- --nocapture > /dev/null 2>&1
    fi
  )
  rc=$?
  set -e
  if [ "$rc" -ne 0 ]; then
    echo "warning: rust_verify_test reported failures while generating inputs; continuing"
  fi
}

add_suite_files() {
  local suite="$1"
  local dir
  local file
  local base
  local before after
  dir="$(suite_dir_of "$suite")"
  if [ "$suite" != "rust-verify-tests" ] && [ ! -d "$dir" ]; then
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
  elif [ "$suite" = "rust-verify-tests" ]; then
    before=${#cases[@]}
    add_rust_verify_generated_cases_all
    after=${#cases[@]}
    if [ "$after" -eq "$before" ]; then
      materialize_rust_verify_inputs
      add_rust_verify_generated_cases_all
      after=${#cases[@]}
    fi
    if [ "$after" -eq "$before" ]; then
      echo "No rust_verify_test generated inputs found under $VERUS_RVT_INPUTS_DIR" >&2
      echo "Try running: (cd $VERUS_SRC && source ../tools/activate && vargo test -p rust_verify_test --tests -- --nocapture)" >&2
      exit 1
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
  set +e
  (
    cd "$suite_json_dir"
    # Some Verus examples are library-style (no `main`), so export in lib mode.
    run_logged "$log_export" "$VERUS_BIN" --export-lean-all "$example" --crate-type=lib
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
    run_logged "$log_verify" lake exe StrataVerify ${STRATA_VERIFY_ARGS[@]-} "$core"
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
  add_selected_suite "rust-verify-tests"
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
if [ ! -d "$VERUS_RUST_VERIFY_TESTS_DIR" ]; then
  echo "Missing rust_verify_test dir: $VERUS_RUST_VERIFY_TESTS_DIR" >&2
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
    if [[ "$resolved" == rust-verify-tests-source\|* ]]; then
      test_source="${resolved#*|}"
      test_name="$(basename "$test_source" .rs)"
      before=${#cases[@]}
      add_rust_verify_generated_cases_for_test_name "$test_name"
      after=${#cases[@]}
      if [ "$after" -eq "$before" ]; then
        materialize_rust_verify_inputs
        add_rust_verify_generated_cases_for_test_name "$test_name"
        after=${#cases[@]}
      fi
      if [ "$after" -eq "$before" ]; then
        echo "No generated inputs found for rust_verify_test '$test_name' under $VERUS_RVT_INPUTS_DIR" >&2
        exit 1
      fi
    else
      add_case "${resolved%%|*}" "${resolved#*|}"
    fi
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
if [ "$skipped_expected_err_cases" -gt 0 ]; then
  echo "  skipped expected rust_verify_test Err-cases: $skipped_expected_err_cases"
fi
if [ "$skipped_rust_compile_error_cases" -gt 0 ]; then
  echo "  skipped expected Rust compile-error cases: $skipped_rust_compile_error_cases"
fi

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
