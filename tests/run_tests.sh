#!/bin/bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERUSFILES_DIR="$ROOT_DIR/tests/VerusFiles"
JSON_LEAN_DIR="${JSON_LEAN_DIR:-$ROOT_DIR/tests/JSONFilesLean}"
JSON_BOOGIE_DIR="${JSON_BOOGIE_DIR:-$ROOT_DIR/tests/JSONFilesBoogie}"
BOOGIE_DIR="${BOOGIE_DIR:-$ROOT_DIR/tests/BoogieFiles}"
LEAN_DIR="${LEAN_DIR:-$ROOT_DIR/tests/LeanFiles}"
VERUS_DIR="${VERUS_DIR:-$ROOT_DIR/../verus}"
VERUS_SRC="${VERUS_SRC:-$VERUS_DIR/source}"
VERUS_BIN="${VERUS_BIN:-$VERUS_SRC/target-verus/release/verus}"
STRATA_DIR="${STRATA_DIR:-$ROOT_DIR/../Strata}"
VERUS_LEAN="${VERUS_LEAN:-$ROOT_DIR/.lake/build/bin/verus-lean}"

if [ -z "${BOOLE_DIR:-}" ]; then
  if [ -d "$ROOT_DIR/../cslib/Cslib/Languages/Boole" ]; then
    BOOLE_DIR="$ROOT_DIR/../cslib/Cslib/Languages/Boole/tests"
  else
    BOOLE_DIR="$ROOT_DIR/tests/BooleFiles"
  fi
fi

JSON_BOOGIE_EXAMPLES_DIR="$JSON_BOOGIE_DIR/verus-examples"
JSON_BOOGIE_VLIR_DIR="$JSON_BOOGIE_DIR/vlir-tests"
CORE_EXAMPLES_DIR="$BOOGIE_DIR/verus-examples"
CORE_VLIR_DIR="$BOOGIE_DIR/vlir-tests"

verbose=false
STRATA_SOLVER="cvc5"
STRATA_SOLVER_TIMEOUT=""

usage() {
  cat <<'EOF'
Usage: tests/run_tests.sh [options] [target]

Stages:
  --verus          Run Verus export on .rs input(s) to generate JSON files
  --boogie         Run verus-lean on JSONFilesBoogie to generate Core files
  --boole          Generate Boole files (.rs -> JSON -> Core -> Boole, as needed)
  --lean           Run verus-lean on JSONFilesLean to generate LeanFiles
  --verify         Run StrataVerify on Core files
  --all            Run Verus + Boogie + Verify
  --solver <name>  StrataVerify solver (default: cvc5)
  --solver-timeout <sec>
                   StrataVerify timeout in seconds
  --out <path>     Output file path for single-target runs
                   (applies to one stage: --lean, --boogie, or --boole)
  --verbose        Show full CLI output for external commands
  -h, --help       Show this help

Target:
  Optional and single-case only.
  Use a file path target: *.rs, *.json, *.core.st, *.boogie.st
  With --boole:
    *.rs      runs Verus export + Core translation + Boole wrapping
    *.json    runs Core translation + Boole wrapping
    *.core.st runs Boole wrapping only
    (no target) wraps existing Core files under tests/BoogieFiles/*

Environment variables:
  VERUS_LEAN_OFFICIAL=1
    Use Strata's official pretty-printer (Core.formatProgram) instead of
    the local one when generating Core files.

EOF
}

map_output_base() {
  case "$1" in
    recursion) echo "recursion_M" ;;
    *) echo "$1" ;;
  esac
}

case_key_from_rs_path() {
  local p="$1"
  local p_real
  p_real="$(cd "$(dirname "$p")" && pwd -P)/$(basename "$p")"
  local vlir_root examples_root
  vlir_root="$(cd "$VERUSFILES_DIR" && pwd -P)"
  examples_root="$(cd "$VERUS_DIR/examples" && pwd -P)"
  local rel
  case "$p_real" in
    "$vlir_root"/*) rel="${p_real#$vlir_root/}" ;;
    "$examples_root"/*) rel="${p_real#$examples_root/}" ;;
    *) rel="$(basename "$p_real")" ;;
  esac
  rel="${rel%.rs}"
  rel="${rel//\//__}"
  rel="${rel// /_}"
  echo "$rel"
}

boogie_json_case_dir_for_rs_path() {
  local p="$1"
  local suite case_key
  suite="$(infer_suite_from_rs_path "$p")"
  case_key="$(case_key_from_rs_path "$p")"
  echo "$(boogie_json_dir_for_suite "$suite")/$case_key"
}

case_key_from_json_path() {
  local p="$1"
  local rel
  case "$p" in
    "$JSON_BOOGIE_VLIR_DIR"/*)
      rel="${p#$JSON_BOOGIE_VLIR_DIR/}"
      ;;
    "$JSON_BOOGIE_EXAMPLES_DIR"/*)
      rel="${p#$JSON_BOOGIE_EXAMPLES_DIR/}"
      ;;
    *)
      echo "$(basename "$p" .json)"
      return 0
      ;;
  esac
  local first="${rel%%/*}"
  if [ "$first" = "$rel" ]; then
    echo "$(basename "$p" .json)"
  else
    echo "$first"
  fi
}

module_shard_root() {
  local stem="$1"
  if [[ "$stem" =~ ^(.+)_M[[:alnum:]_]+$ ]]; then
    echo "${BASH_REMATCH[1]}"
    return 0
  fi
  return 1
}

infer_suite_from_rs_path() {
  local p="$1"
  local p_real
  p_real="$(cd "$(dirname "$p")" && pwd -P)/$(basename "$p")"
  local vlir_root examples_root
  vlir_root="$(cd "$VERUSFILES_DIR" && pwd -P)"
  examples_root="$(cd "$VERUS_DIR/examples" && pwd -P)"
  case "$p_real" in
    "$vlir_root"/*) echo "vlir-tests" ;;
    "$examples_root"/*) echo "verus-examples" ;;
    *) echo "verus-examples" ;;
  esac
}

boogie_json_dir_for_suite() {
  case "$1" in
    vlir-tests) echo "$JSON_BOOGIE_VLIR_DIR" ;;
    *) echo "$JSON_BOOGIE_EXAMPLES_DIR" ;;
  esac
}

boogie_core_dir_for_suite() {
  case "$1" in
    vlir-tests) echo "$CORE_VLIR_DIR" ;;
    *) echo "$CORE_EXAMPLES_DIR" ;;
  esac
}

infer_suite_from_json_path() {
  local p="$1"
  case "$p" in
    "$JSON_BOOGIE_VLIR_DIR"/*) echo "vlir-tests" ;;
    "$JSON_BOOGIE_EXAMPLES_DIR"/*) echo "verus-examples" ;;
    *)
      local b in_base
      b=$(basename "$p" .json)
      case "$b" in
        recursion_M) in_base="recursion" ;;
        *) in_base="$b" ;;
      esac
      if [ -f "$VERUSFILES_DIR/$in_base.rs" ]; then
        echo "vlir-tests"
      else
        echo "verus-examples"
      fi
      ;;
  esac
}

resolve_core_file_for_case() {
  local suite="$1"
  local case_key="$2"
  local candidate
  candidate="$(boogie_core_dir_for_suite "$suite")/${case_key}.core.st"
  if [ -f "$candidate" ]; then
    echo "$candidate"
    return 0
  fi
  return 1
}

lean_ident_from_base() {
  local raw="$1"
  local ident
  ident="$(printf '%s' "$raw" | sed -E 's/[^A-Za-z0-9_]/_/g')"
  if [[ ! "$ident" =~ ^[A-Za-z_] ]]; then
    ident="_$ident"
  fi
  echo "$ident"
}

write_boole_wrapper() {
  local core_file="$1"
  local out_file="$2"
  local base ident
  base="$(basename "$core_file" .core.st)"
  ident="$(lean_ident_from_base "$base")"
  mkdir -p "$(dirname "$out_file")"
  {
    echo "import Strata.MetaVerifier"
    echo "import Smt"
    echo
    echo "open Strata"
    echo
    echo "def ${ident} : Strata.Program :="
    echo "#strata"
    echo "program Boole; // Specify that this is a Boole program."
    sed '1{/^[[:space:]]*program Core;[[:space:]]*$/d;}' "$core_file"
    echo "#end"
    echo
    echo "-- Approach 1: Using an SMT solver to verify the VCs."
    echo "#eval Strata.Boole.verify \"cvc5\" ${ident}"
    echo
    echo "-- Approach 2: Using Lean tactics to verify the VCs."
    echo "theorem ${ident}_smtVCsCorrect : Strata.smtVCsCorrect ${ident} := by"
    echo "  gen_smt_vcs"
    echo "  all_goals smt"
  } >"$out_file"
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
  local out_json_final
  local out_json_tmp
  local out_json_alt_tmp
  local out_dir
  local tmp_dir
  local shard
  local label
  local -a flags=()

  if [ "$mode" = "boogie" ]; then
    local out_case_dir
    flags+=(--export-lean-all)
    out_case_dir="$(boogie_json_case_dir_for_rs_path "$file")"
    out_dir="$out_case_dir"
    label="boogie"
  else
    out_dir="$JSON_LEAN_DIR"
    label="lean"
  fi

  mkdir -p "$out_dir"
  tmp_dir="$(mktemp -d "$out_dir/.export_${base}.XXXXXX")"
  out_json_final="$out_dir/${out_base}.json"
  out_json_tmp="$tmp_dir/${base}.json"
  out_json_alt_tmp="$tmp_dir/${out_base}.json"
  set +e
  run_cmd_quiet_in_dir "$tmp_dir" "$VERUS_BIN" "${flags[@]-}" "$file"
  rc=$?
  set -e
  if [ $rc -ne 0 ] && $verbose; then
    echo "Verus exited non-zero for $base ($label); continuing if JSON was produced."
  fi
  if [ -f "$out_json_alt_tmp" ]; then
    mv -f "$out_json_alt_tmp" "$out_json_final"
  elif [ -f "$out_json_tmp" ]; then
    mv -f "$out_json_tmp" "$out_json_final"
  else
    if [ "$mode" = "boogie" ]; then
      failures+=("$base (core json missing)")
    fi
  fi
  for shard in "$tmp_dir/${base}_"*.json "$tmp_dir/${out_base}_"*.json; do
    [ -f "$shard" ] || continue
    mv -f "$shard" "$out_dir/"
  done
  rm -rf "$tmp_dir"
}

run_verus_lean_jsons() {
  local mode="$1"
  local json_dir="$2"
  local out_dir="$3"
  local label="$4"
  local out_ext="$5"
  local failures=()
  local json_files=()
  local json_candidates=()
  local base
  local f
  local rc
  local suite
  local d
  local out_file
  local any_json=false
  local cmd=("$VERUS_LEAN")

  if [ "$mode" = "boogie" ]; then
    if [ "${VERUS_LEAN_OFFICIAL:-}" = "1" ]; then
      cmd+=("core" "--official")
    else
      cmd+=("boogie")
    fi
  fi

  if [ -n "$target_json_path" ]; then
    case "$target_json_path" in
      *.json) json_files=("$target_json_path") ;;
      *) echo "Target is not a .json file: $target_json_path"; exit 1 ;;
    esac
  elif [ -n "$target_rs_path" ]; then
    target_rs_base="$(basename "$target_rs_path" .rs)"
    out_base=$(map_output_base "$target_rs_base")
    if [ "$mode" = "boogie" ]; then
      json_candidates+=("$(boogie_json_case_dir_for_rs_path "$target_rs_path")/${out_base}.json")
      for json in "${json_candidates[@]}"; do
        if [ -f "$json" ]; then
          json_files=("$json")
          break
        fi
      done
    else
      json="$json_dir/${out_base}.json"
      if [ -f "$json" ]; then
        json_files=("$json")
      fi
    fi
    if [ ${#json_files[@]} -eq 0 ]; then
      echo "Missing JSON input for target: $target_rs_path"
      exit 1
    fi
  else
    if [ "$mode" = "boogie" ]; then
      for d in "$JSON_BOOGIE_VLIR_DIR" "$JSON_BOOGIE_EXAMPLES_DIR"; do
        [ -d "$d" ] || continue
        while IFS= read -r f; do
          [ -f "$f" ] || continue
          json_files+=("$f")
        done < <(find "$d" -mindepth 2 -maxdepth 2 -type f -name '*.json' | sort)
      done
    else
      json_files=("$json_dir"/*.json)
    fi
  fi

  for f in "${json_files[@]}"; do
    if [ ! -f "$f" ]; then
      break
    fi
    base=$(basename "$f" .json)
    if [ "$mode" = "boogie" ] && [ -z "$target_json_path" ] && [ -z "$target_rs_path" ]; then
      local shard_root
      if shard_root="$(module_shard_root "$base")"; then
        local parent
        parent="$(cd "$(dirname "$f")" && pwd -P)"
        if [ -f "$parent/${shard_root}.json" ]; then
          # Translate the primary JSON once; `Main.genCoreFromFile` will load
          # sibling shards (`base_*.json`) automatically.
          continue
        fi
      fi
    fi
    any_json=true
    echo "$label: $base"
    if [ "$custom_out_mode" = "$mode" ]; then
      out_file="$custom_out_path"
    elif [ "$mode" = "boogie" ]; then
      suite="$(infer_suite_from_json_path "$f")"
      case_key="$(case_key_from_json_path "$f")"
      out_dir_file="$(boogie_core_dir_for_suite "$suite")"
      mkdir -p "$out_dir_file"
      out_file="$out_dir_file/${case_key}.${out_ext}"
    else
      out_file="$out_dir/${base}.${out_ext}"
    fi
    set +e
    # Avoid stale-tail artifacts if the translator writes shorter output than
    # an existing file and does not truncate in place.
    mkdir -p "$(dirname "$out_file")"
    rm -f "$out_file"
    run_cmd_quiet "${cmd[@]}" "$f" "$out_file"
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
    if ! $any_json; then
      if [ "$mode" = "boogie" ]; then
        echo "No JSON files found in $JSON_BOOGIE_VLIR_DIR or $JSON_BOOGIE_EXAMPLES_DIR"
      else
        echo "No JSON files found in $json_dir"
      fi
    fi
  fi
}

run_verus=false
run_boogie=false
run_boole=false
run_lean=false
run_verify=false
target_rs_path=""
target_json_path=""
target_core_path=""
custom_out_path=""
custom_out_mode=""

if [ $# -eq 0 ]; then
  usage
  exit 0
fi

positional=()
while [ $# -gt 0 ]; do
  case "$1" in
    --verus) run_verus=true; shift ;;
    --boogie) run_boogie=true; shift ;;
    --boole) run_boole=true; shift ;;
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
    --out)
      if [ $# -lt 2 ]; then
        echo "Missing value for --out"
        usage
        exit 1
      fi
      custom_out_path="$2"
      shift 2
      ;;
    --out=*)
      custom_out_path="${1#*=}"
      if [ -z "$custom_out_path" ]; then
        echo "Missing value for --out"
        usage
        exit 1
      fi
      shift
      ;;
    --verbose) verbose=true; shift ;;
    --all) run_verus=true; run_boogie=true; run_verify=true; shift ;;
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
  candidate="${positional[0]}"
  if [ ! -f "$candidate" ]; then
    echo "Target must be an existing file path: $candidate"
    exit 1
  fi
  candidate_dir="$(cd "$(dirname "$candidate")" && pwd -P)"
  candidate_abs="$candidate_dir/$(basename "$candidate")"
  case "$candidate_abs" in
    *.rs) target_rs_path="$candidate_abs" ;;
    *.json) target_json_path="$candidate_abs" ;;
    *.core.st|*.boogie.st) target_core_path="$candidate_abs" ;;
    *)
      echo "Unsupported target file type: $candidate"
      echo "Expected .rs, .json, or .core.st/.boogie.st"
      exit 1
      ;;
  esac
fi

# `--boole` is an end-to-end target. Infer prerequisite stages from the input:
#   .rs      => Verus export + Core translation + Boole wrapping
#   .json    => Core translation + Boole wrapping
#   .core.st => Boole wrapping only
if $run_boole; then
  if [ -n "$target_rs_path" ]; then
    run_verus=true
    run_boogie=true
  elif [ -n "$target_json_path" ]; then
    run_boogie=true
  fi
fi

if [ -n "$custom_out_path" ]; then
  if [ ${#positional[@]} -ne 1 ]; then
    echo "--out requires a single target path."
    exit 1
  fi
  if [[ "$custom_out_path" != /* ]]; then
    custom_out_path="$(pwd -P)/$custom_out_path"
  fi
  if $run_boole; then
    custom_out_mode="boole"
  elif $run_lean && ! $run_boogie; then
    custom_out_mode="lean"
  elif $run_boogie && ! $run_lean; then
    custom_out_mode="boogie"
  else
    echo "--out is supported for exactly one output stage: --lean, --boogie, or --boole."
    exit 1
  fi
fi

if ! $run_verus && ! $run_boogie && ! $run_boole && ! $run_lean && ! $run_verify; then
  usage
  exit 1
fi

mkdir -p "$JSON_LEAN_DIR" "$JSON_BOOGIE_DIR" "$JSON_BOOGIE_EXAMPLES_DIR" "$JSON_BOOGIE_VLIR_DIR" \
  "$BOOGIE_DIR" "$CORE_EXAMPLES_DIR" "$CORE_VLIR_DIR" "$BOOLE_DIR" "$LEAN_DIR"

if $run_verus; then
  echo "=== Step 1: Verus -> JSON ==="
  if [ -n "$target_json_path" ] || [ -n "$target_core_path" ]; then
    echo "--verus requires an .rs target path (or no target)."
    exit 1
  fi
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
  if $run_boogie || $run_boole || $run_verify; then
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
      echo "Verus export failures (missing JSON): ${failures[*]}"
    fi
  )
fi

if $run_boogie || $run_lean; then
  echo ""
  echo "=== Step 2: JSON -> Strata Core ==="
  if [ -n "$target_core_path" ]; then
    echo "--boogie/--lean target must be .rs or .json (not .core.st)."
    exit 1
  fi
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

if $run_boole; then
  echo ""
  echo "=== Step 2b: Core -> Boole ==="
  core_files=()
  if [ -n "$target_core_path" ]; then
    case "$target_core_path" in
      *.core.st|*.boogie.st)
        case "$target_core_path" in
          /*) core_files=("$target_core_path") ;;
          *) core_files=("$ROOT_DIR/$target_core_path") ;;
        esac
        ;;
      *) echo "Target is not a .core.st/.boogie.st file: $target_core_path"; exit 1 ;;
    esac
  elif [ -n "$target_rs_path" ] || [ -n "$target_json_path" ]; then
    if [ -n "$target_rs_path" ]; then
      suite="$(infer_suite_from_rs_path "$target_rs_path")"
      case_key="$(case_key_from_rs_path "$target_rs_path")"
      file="$(resolve_core_file_for_case "$suite" "$case_key" || true)"
    else
      suite="$(infer_suite_from_json_path "$target_json_path")"
      case_key="$(case_key_from_json_path "$target_json_path")"
      file="$(resolve_core_file_for_case "$suite" "$case_key" || true)"
    fi
    if [ -z "$file" ]; then
      echo "Missing Core input for target path."
      exit 1
    fi
    case "$file" in
      /*) core_files=("$file") ;;
      *) core_files=("$ROOT_DIR/$file") ;;
    esac
  else
    for scan_dir in "$CORE_VLIR_DIR" "$CORE_EXAMPLES_DIR"; do
      [ -d "$scan_dir" ] || continue
      while IFS= read -r f; do
        core_files+=("$f")
      done < <(find "$scan_dir" -maxdepth 1 -type f -name '*.core.st' | sort)
    done
  fi

  any=false
  for core in "${core_files[@]}"; do
    [ -f "$core" ] || continue
    base="$(basename "$core" .core.st)"
    if [ -z "$target_core_path" ] && [ -z "$target_rs_path" ] && [ -z "$target_json_path" ]; then
      if shard_root="$(module_shard_root "$base")"; then
        parent="$(cd "$(dirname "$core")" && pwd -P)"
        if [ -f "$parent/${shard_root}.core.st" ]; then
          continue
        fi
      fi
    fi
    any=true
    if [ "$custom_out_mode" = "boole" ]; then
      out_file="$custom_out_path"
    else
      case "$core" in
        "$CORE_VLIR_DIR"/*) out_file="$BOOLE_DIR/vlir-tests/${base}.lean" ;;
        *) out_file="$BOOLE_DIR/verus-examples/${base}.lean" ;;
      esac
    fi
    echo "Boole: $base"
    write_boole_wrapper "$core" "$out_file"
  done
  if ! $any; then
    echo "No Core files found to wrap."
    exit 1
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
      *.core.st|*.boogie.st)
        case "$target_core_path" in
          /*) verify_path="$target_core_path" ;;
          *) verify_path="$ROOT_DIR/$target_core_path" ;;
        esac
        ;;
      *) echo "Target is not a .core.st/.boogie.st file: $target_core_path"; exit 1 ;;
    esac
    (cd "$STRATA_DIR" && lake exe StrataVerify ${STRATA_VERIFY_ARGS[@]-} "$verify_path")
  elif [ -n "$target_rs_path" ] || [ -n "$target_json_path" ]; then
    if [ -n "$target_rs_path" ]; then
      suite="$(infer_suite_from_rs_path "$target_rs_path")"
      case_key="$(case_key_from_rs_path "$target_rs_path")"
      file="$(resolve_core_file_for_case "$suite" "$case_key" || true)"
    else
      suite="$(infer_suite_from_json_path "$target_json_path")"
      case_key="$(case_key_from_json_path "$target_json_path")"
      file="$(resolve_core_file_for_case "$suite" "$case_key" || true)"
    fi
    if [ -z "$file" ]; then
      echo "Missing Core input for target path."
      exit 1
    fi
    case "$file" in
      /*) verify_path="$file" ;;
      *) verify_path="$ROOT_DIR/$file" ;;
    esac
    (cd "$STRATA_DIR" && lake exe StrataVerify ${STRATA_VERIFY_ARGS[@]-} "$verify_path")
  else
    any=false
    for scan_dir in "$CORE_VLIR_DIR" "$CORE_EXAMPLES_DIR"; do
      [ -d "$scan_dir" ] || continue
      for file in "$scan_dir"/*.core.st; do
        if [ ! -f "$file" ]; then
          break
        fi
        if [ -z "$target_core_path" ] && [ -z "$target_rs_path" ] && [ -z "$target_json_path" ]; then
          base="$(basename "$file" .core.st)"
          if shard_root="$(module_shard_root "$base")"; then
            parent="$(cd "$(dirname "$file")" && pwd -P)"
            if [ -f "$parent/${shard_root}.core.st" ]; then
              continue
            fi
          fi
        fi
        any=true
        (cd "$STRATA_DIR" && lake exe StrataVerify ${STRATA_VERIFY_ARGS[@]-} "$file")
      done
    done
    if ! $any; then
      echo "No Core files found in $BOOGIE_DIR"
      exit 1
    fi
  fi
fi
