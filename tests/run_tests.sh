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
STRATA_DIR="$ROOT_DIR/../Strata"
VERUS_LEAN="$ROOT_DIR/.lake/build/bin/verus-lean"

verbose=false

usage() {
  cat <<'EOF'
Usage: tests/run_tests.sh [options] [target]

Stages:
  --verus          Run Verus on tests/VerusFiles to generate JSONFilesLean/JSONFilesBoogie
  --boogie         Run verus-lean on JSONFilesBoogie to generate Core files
  --lean           Run verus-lean on JSONFilesLean to generate LeanFiles
  --verify         Run StrataVerify on Core files
  --verbose        Show full CLI output for external commands

Convenience:
  --all            Run all stages (1-3)
  --verus-boogie   Run Verus and Boogie stages
  --boogie-verify  Run Boogie and Verify stages
  -h, --help       Show this help

Target:
  Optional base name or file name to run a single test, e.g.
    LoopSimple
    LoopSimple.rs
    serialized_LoopSimple.json
    serialized_LoopSimple.core.st
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
  local flags=""
  local verus_bin

  if [ "$mode" = "boogie" ]; then
    flags="--export-lean-all"
    out_dir="$JSON_BOOGIE_DIR"
    label="boogie"
  else
    out_dir="$JSON_LEAN_DIR"
    label="lean"
  fi

  verus_bin="$VERUS_SRC/target-verus/release/verus"
  out_json="$out_dir/serialized_${base}.json"
  rm -f "$out_json"
  set +e
  if [ -n "$flags" ]; then
    run_cmd_quiet_in_dir "$out_dir" "$verus_bin" $flags "$file"
  else
    run_cmd_quiet_in_dir "$out_dir" "$verus_bin" "$file"
  fi
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

  if [ -n "$target_base" ]; then
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

if [ $# -eq 0 ]; then
  usage
  exit 0
fi

positional=()
for arg in "$@"; do
  case "$arg" in
    --verus) run_verus=true ;;
    --boogie) run_boogie=true ;;
    --lean) run_lean=true ;;
    --verify) run_verify=true ;;
    --verbose) verbose=true ;;
    --all) run_verus=true; run_boogie=true; run_verify=true ;;
    --verus-boogie) run_verus=true; run_boogie=true ;;
    --boogie-verify) run_boogie=true; run_verify=true ;;
    -h|--help) usage; exit 0 ;;
    --*) echo "Unknown option: $arg"; usage; exit 1 ;;
    *) positional+=("$arg") ;;
  esac
done

if [ ${#positional[@]} -gt 1 ]; then
  echo "Too many targets provided."
  usage
  exit 1
fi

if [ ${#positional[@]} -eq 1 ]; then
  target_base=$(normalize_target_base "${positional[0]}")
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

  if $gen_lean_json; then
    rm -f "$JSON_LEAN_DIR"/serialized_*.json
  fi
  if $gen_boogie_json; then
    rm -f "$JSON_BOOGIE_DIR"/serialized_*.json
  fi

  (
    cd "$VERUS_SRC"
    source ../tools/activate
    vargo build --release --features lean

    if [ -n "$target_base" ]; then
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
  if [ -n "$target_base" ]; then
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
    (cd "$STRATA_DIR" && lake exe StrataVerify "$verify_path")
  else
    any=false
    for file in "$BOOGIE_DIR"/serialized_*.core.st; do
      if [ ! -f "$file" ]; then
        break
      fi
      any=true
      (cd "$STRATA_DIR" && lake exe StrataVerify "$file")
    done
    if ! $any; then
      echo "No Boogie files found in $BOOGIE_DIR"
      exit 1
    fi
  fi
fi
