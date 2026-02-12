#!/bin/bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERUSFILES_DIR="$ROOT_DIR/tests/VerusFiles"
JSON_LEAN_DIR="${JSON_LEAN_DIR:-$ROOT_DIR/tests/JSONFilesLean}"
JSON_BOOGIE_DIR="${JSON_BOOGIE_DIR:-$ROOT_DIR/tests/JSONFilesBoogie}"
BOOGIE_DIR="${BOOGIE_DIR:-$ROOT_DIR/tests/BoogieFiles}"
LEAN_DIR="${LEAN_DIR:-$ROOT_DIR/tests/LeanFiles}"
VERUS_DIR="$ROOT_DIR/../verus"
VERUS_SRC="$VERUS_DIR/source"
VERUS_BIN="$VERUS_SRC/target-verus/release/verus"
STRATA_DIR="$ROOT_DIR/../Strata"
VERUS_LEAN="$ROOT_DIR/.lake/build/bin/verus-lean"

verbose=false
STRATA_SOLVER="cvc5"
STRATA_SOLVER_TIMEOUT=""

usage() {
  cat <<'EOF'
Usage: tests/run_tests.sh [options] [target]

Stages:
  --verus          Run Verus on tests/VerusFiles to generate JSONFilesLean/JSONFilesBoogie
  --boogie         Run verus-lean on JSONFilesBoogie to generate Core files
  --lean           Run verus-lean on JSONFilesLean to generate LeanFiles
  --verify         Run StrataVerify on Core files
  --solver <name>  StrataVerify solver (default: cvc5)
  --solver-timeout <sec>
                   StrataVerify timeout in seconds
  --verbose        Show full CLI output for external commands

Convenience:
  --all            Run all stages (1-3)
  --verus-boogie   Run Verus and Boogie stages
  --boogie-verify  Run Boogie and Verify stages
  -h, --help       Show this help

Target:
  Optional base name or a concrete file path to run a single test, e.g.
    LoopSimple
    /path/to/LoopSimple.rs
    /path/to/serialized_LoopSimple.json
    /path/to/serialized_LoopSimple.core.st

EOF
}

map_output_base() {
  case "$1" in
    recursion) echo "recursion_M" ;;
    *) echo "$1" ;;
  esac
}

map_input_base() {
  case "$1" in
    recursion_M) echo "recursion" ;;
    *) echo "$1" ;;
  esac
}

normalize_target_base() {
  local b
  b=$(basename "$1")
  b=${b#serialized_}
  b=${b%.boogie.st}
  b=${b%.core.st}
  b=${b%.json}
  b=${b%.rs}
  echo "$b"
}

run_cmd_quiet() {
  if $verbose; then
    "$@"
  else
    "$@" >/dev/null 2>&1
  fi
}

run_cmd_quiet_in_dir() {
  local dir="$1"
  shift
  if $verbose; then
    (cd "$dir" && "$@")
  else
    (cd "$dir" && "$@") >/dev/null 2>&1
  fi
}

run_verus_export() {
  local mode="$1"
  local file="$2"
  local base="$3"
  local out_base="$4"
  local rc
  local out_json
  local out_dir
  local label
  local -a flags=()

  if [ "$mode" = "boogie" ]; then
    flags+=(--export-lean-all)
    out_dir="$JSON_BOOGIE_DIR"
    label="boogie"
  else
    out_dir="$JSON_LEAN_DIR"
    label="lean"
  fi

  out_json="$out_dir/serialized_${base}.json"
  set +e
  run_cmd_quiet_in_dir "$out_dir" "$VERUS_BIN" "${flags[@]}" "$file"
  rc=$?
  set -e
  if [ $rc -ne 0 ]; then
    failures+=("$base ($label)")
  fi
  if [ -f "$out_json" ]; then
    if [ "$out_base" != "$base" ]; then
      mv -f "$out_json" "$out_dir/serialized_${out_base}.json"
    fi
  else
    if [ "$mode" = "boogie" ]; then
      failures+=("$base (core json missing)")
    fi
  fi
}

run_verus_lean_jsons() {
  local mode="$1"
  local json_dir="$2"
  local out_dir="$3"
  local label="$4"
  local out_ext="$5"
  local failures=()
  local json_files=()
  local base
  local f
  local rc
  local cmd=("$VERUS_LEAN")

  if [ "$mode" = "boogie" ]; then
    cmd+=("boogie")
  fi

  if [ -n "$target_json_path" ]; then
    case "$target_json_path" in
      *.json) json_files=("$target_json_path") ;;
      *) echo "Target is not a .json file: $target_json_path"; exit 1 ;;
    esac
  elif [ -n "$target_base" ]; then
    out_base=$(map_output_base "$target_base")
    json="$json_dir/serialized_${out_base}.json"
    if [ ! -f "$json" ]; then
      echo "Missing JSON input: $json"
      exit 1
    fi
    json_files=("$json")
  else
    json_files=("$json_dir"/serialized_*.json)
  fi

  for f in "${json_files[@]}"; do
    if [ ! -f "$f" ]; then
      echo "No JSON files found in $json_dir"
      break
    fi
    base=$(basename "$f" .json)
    echo "$label: $base"
    set +e
    run_cmd_quiet "${cmd[@]}" "$f" "$out_dir/${base}.${out_ext}"
    rc=$?
    set -e
    if [ $rc -ne 0 ]; then
      failures+=("$base")
    fi
  done

  if [ "$mode" = "lean" ]; then
    echo ""
    echo "LeanFiles:"
    ls -1 "$out_dir"/*.lean 2>/dev/null | wc -l | xargs echo "  Count:"
    if [ ${#failures[@]} -gt 0 ]; then
      echo "Lean generation issues: ${failures[*]}"
    fi
  else
    if [ ${#failures[@]} -gt 0 ]; then
      echo "Core generation issues: ${failures[*]}"
    fi
  fi
}

run_verus=false
run_boogie=false
run_lean=false
run_verify=false
target_base=""
target_rs_path=""
target_json_path=""
target_core_path=""

if [ $# -eq 0 ]; then
  usage
  exit 0
fi

positional=()
while [ $# -gt 0 ]; do
  case "$1" in
    --verus) run_verus=true; shift ;;
    --boogie) run_boogie=true; shift ;;
    --lean) run_lean=true; shift ;;
    --verify) run_verify=true; shift ;;
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
    --verbose) verbose=true; shift ;;
    --all) run_verus=true; run_boogie=true; run_verify=true; shift ;;
    --verus-boogie) run_verus=true; run_boogie=true; shift ;;
    --boogie-verify) run_boogie=true; run_verify=true; shift ;;
    -h|--help) usage; exit 0 ;;
    --) shift; while [ $# -gt 0 ]; do positional+=("$1"); shift; done ;;
    --*) echo "Unknown option: $1"; usage; exit 1 ;;
    *) positional+=("$1"); shift ;;
  esac
done

declare -a STRATA_VERIFY_ARGS=()
if [ -n "$STRATA_SOLVER" ]; then
  STRATA_VERIFY_ARGS+=(--solver "$STRATA_SOLVER")
fi
if [ -n "$STRATA_SOLVER_TIMEOUT" ]; then
  STRATA_VERIFY_ARGS+=(--solver-timeout "$STRATA_SOLVER_TIMEOUT")
fi

if [ ${#positional[@]} -gt 1 ]; then
  echo "Too many targets provided."
  usage
  exit 1
fi

if [ ${#positional[@]} -eq 1 ]; then
  if [ -f "${positional[0]}" ]; then
    candidate="${positional[0]}"
    target_base=$(normalize_target_base "$candidate")
    case "$candidate" in
      *.rs) target_rs_path="$candidate" ;;
      *.json) target_json_path="$candidate" ;;
      *.core.st|*.boogie.st) target_core_path="$candidate" ;;
      *)
        echo "Unsupported target file type: $candidate"
        echo "Expected .rs, .json, or .core.st/.boogie.st"
        exit 1
        ;;
    esac
  else
    target_base=$(normalize_target_base "${positional[0]}")
  fi
fi

if ! $run_verus && ! $run_boogie && ! $run_lean && ! $run_verify; then
  usage
  exit 1
fi

mkdir -p "$JSON_LEAN_DIR" "$JSON_BOOGIE_DIR" "$BOOGIE_DIR" "$LEAN_DIR"

if $run_verus; then
  echo "=== Step 1: Verus -> JSON ==="
  if [ ! -d "$VERUS_SRC" ]; then
    echo "Missing verus repo at $VERUS_DIR"
    exit 1
  fi
  if [ ! -d "$VERUSFILES_DIR" ]; then
    echo "Missing VerusFiles at $VERUSFILES_DIR"
    exit 1
  fi

  gen_lean_json=false
  gen_boogie_json=false
  if $run_lean; then
    gen_lean_json=true
  fi
  if $run_boogie || $run_verify; then
    gen_boogie_json=true
  fi
  if ! $gen_lean_json && ! $gen_boogie_json; then
    gen_lean_json=true
    gen_boogie_json=true
  fi

  need_verus_build=false
  if [ ! -x "$VERUS_BIN" ] || [ "${VERUS_FORCE_BUILD:-0}" = "1" ]; then
    need_verus_build=true
  fi

  (
    cd "$VERUS_SRC"
    # Avoid rebuilding Verus on every test run. This prevents frequent stalls on
    # stale cargo/vargo locks while keeping an override for explicit rebuilds.
    if $need_verus_build; then
      source ../tools/activate
      vargo build --release --features lean
    else
      if $verbose; then
        echo "Using existing Verus binary: $VERUS_BIN"
      fi
    fi

    if [ -n "$target_rs_path" ]; then
      case "$target_rs_path" in
        *.rs) files=("$target_rs_path") ;;
        *) echo "Target is not a .rs file: $target_rs_path"; exit 1 ;;
      esac
    elif [ -n "$target_base" ]; then
      in_base=$(map_input_base "$target_base")
      file="$VERUSFILES_DIR/$in_base.rs"
      if [ ! -f "$file" ]; then
        echo "Missing Verus input: $file"
        exit 1
      fi
      files=("$file")
    else
      files=("$VERUSFILES_DIR"/*.rs)
    fi
    if [ ! -e "${files[0]}" ]; then
      echo "No Verus test files found in $VERUSFILES_DIR"
      exit 1
    fi

    failures=()
    for file in "${files[@]}"; do
      base=$(basename "$file" .rs)
      out_base=$(map_output_base "$base")
      echo "Verus: $base"
      if $gen_lean_json; then
        run_verus_export "lean" "$file" "$base" "$out_base"
      fi
      if $gen_boogie_json; then
        run_verus_export "boogie" "$file" "$base" "$out_base"
      fi
    done

    if [ ${#failures[@]} -gt 0 ]; then
      echo "Verus export issues: ${failures[*]}"
    fi
  )
fi

if $run_boogie || $run_lean; then
  echo ""
  echo "=== Step 2: JSON -> Strata Core ==="
  if [ ! -x "$VERUS_LEAN" ]; then
    echo "Missing verus-lean binary at $VERUS_LEAN (run lake build)"
    exit 1
  fi
  if $run_lean; then
    run_verus_lean_jsons "lean" "$JSON_LEAN_DIR" "$LEAN_DIR" "Lean" "lean"
  fi
  if $run_boogie; then
    run_verus_lean_jsons "boogie" "$JSON_BOOGIE_DIR" "$BOOGIE_DIR" "Core" "core.st"
  fi
fi

if $run_verify; then
  echo ""
  echo "=== Step 3: StrataVerify ==="
  if [ ! -d "$STRATA_DIR" ]; then
    echo "Missing Strata repo at $STRATA_DIR"
    exit 1
  fi
  if [ -n "$target_core_path" ]; then
    case "$target_core_path" in
      *.core.st) verify_path="$target_core_path" ;;
      *) echo "Target is not a .core.st file: $target_core_path"; exit 1 ;;
    esac
    (cd "$STRATA_DIR" && lake exe StrataVerify ${STRATA_VERIFY_ARGS[@]-} "$verify_path")
  elif [ -n "$target_base" ]; then
    out_base=$(map_output_base "$target_base")
    file="$BOOGIE_DIR/serialized_${out_base}.core.st"
    if [ ! -f "$file" ]; then
      echo "Missing Core input: $file"
      exit 1
    fi
    case "$file" in
      /*) verify_path="$file" ;;
      *) verify_path="$ROOT_DIR/$file" ;;
    esac
    (cd "$STRATA_DIR" && lake exe StrataVerify ${STRATA_VERIFY_ARGS[@]-} "$verify_path")
  else
    any=false
    for file in "$BOOGIE_DIR"/serialized_*.core.st; do
      if [ ! -f "$file" ]; then
        break
      fi
      any=true
      (cd "$STRATA_DIR" && lake exe StrataVerify ${STRATA_VERIFY_ARGS[@]-} "$file")
    done
    if ! $any; then
      echo "No Core files found in $BOOGIE_DIR"
      exit 1
    fi
  fi
fi
