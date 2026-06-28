#!/bin/bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERUSFILES_DIR="$ROOT_DIR/tests/VerusFiles"
ADOPTED_RVT_DIR="$ROOT_DIR/tests/adopted_rust_verify_test"
JSON_BOOGIE_DIR="${JSON_BOOGIE_DIR:-$ROOT_DIR/tests/JSONFilesBoogie}"
VERUS_DIR="${VERUS_DIR:-$ROOT_DIR/../verus}"
VERUS_SRC="${VERUS_SRC:-$VERUS_DIR/source}"
VERUS_BIN="${VERUS_BIN:-$VERUS_SRC/target-verus/release/verus}"
STRATA_DIR="${STRATA_DIR:-$ROOT_DIR/../Strata}"
VERUS_LEAN="${VERUS_LEAN:-$ROOT_DIR/.lake/build/bin/verus-lean}"
BOOLE_DIR="${BOOLE_DIR:-$ROOT_DIR/tests/BooleFiles}"
BOOLE_PROGRAMS_DIR="${BOOLE_PROGRAMS_DIR:-$ROOT_DIR/tests/BoolePrograms}"

JSON_BOOGIE_EXAMPLES_DIR="$JSON_BOOGIE_DIR/verus-examples"
JSON_BOOGIE_VLIR_DIR="$JSON_BOOGIE_DIR/vlir-tests"

verbose=false
# SMT solver for the `--verify` stage's `#eval Strata.Boole.verify` wrapper.
# Defaults to any pre-set env value so an exported SOLVER still works without
# the flag.
solver="${SOLVER:-cvc5}"
# Tracks whether `--solver` was passed explicitly. When it is, `--verify` rewrites
# the solver in an already-generated wrapper, so `--verify --solver X` takes
# effect without also re-running `--boole`.
solver_explicit=false
# Comma-separated synthesized verification aids to disable, forwarded to
# `verus-lean` via the BOOLE_SYNTH_DISABLE env var. Defaults to any pre-set
# value so an exported env var still works without the flag.
synth_disable="${BOOLE_SYNTH_DISABLE:-}"

usage() {
  cat <<'EOF'
Usage: tests/run_tests.sh [options] [target]

Stages (pipeline: .rs -> JSON -> .boole.st -> .lean wrapper -> verify):
  --verus          Run Verus export on .rs input(s) to generate JSON files
  --boole          Generate Boole files (.rs -> JSON -> Boole, as needed)
  --verify         Run Strata Boole verification (lake env lean) on the
                   generated .lean wrapper for a target
  --all            Run Verus + Boole + Verify across all suites
  --out <path>     Output .boole.st path for single-target --boole runs
  --verbose        Show full output: every proof obligation during --verify
                   (default prints only a tally + non-passing obligations) and
                   full CLI output for the Verus/Boole steps
  --solver <name>  SMT solver for the --verify stage (e.g. cvc5, z3); default cvc5
  --synth-disable <names>
                   Comma-separated synthesized verification aids to turn OFF
                   during Boole generation (sets BOOLE_SYNTH_DISABLE). Valid
                   names: fixedArrayLengths, loopLowerBound, seqMapPrecond.
                   Default: all aids on. Only affects stages that regenerate
                   Boole (--boole / --all).
  -h, --help       Show this help

Target:
  Optional and single-case only.
  Use a file path target: *.rs, *.json, *.lean
  With --boole:
    *.rs      runs Verus export + Boole generation
    *.json    runs Boole generation
    (no target) uses generated JSON cases under tests/JSONFilesBoogie/*
  With --verify:
    *.rs / *.json  resolves to the corresponding Boole .lean wrapper
    *.lean         verifies the wrapper directly

EOF
}

map_output_base() {
  case "$1" in
    recursion) echo "recursion_M" ;;
    *) echo "$1" ;;
  esac
}

abs_file_path() {
  local p="$1"
  echo "$(cd "$(dirname "$p")" && pwd -P)/$(basename "$p")"
}

case_key_from_rs_path() {
  local p="$1"
  local p_real
  p_real="$(abs_file_path "$p")"
  local vlir_root adopted_rvt_root verus_root examples_root
  vlir_root="$(cd "$VERUSFILES_DIR" && pwd -P)"
  adopted_rvt_root="$(cd "$ADOPTED_RVT_DIR" 2>/dev/null && pwd -P || true)"
  verus_root="$(cd "$VERUS_DIR" && pwd -P)"
  examples_root="$(cd "$VERUS_DIR/examples" && pwd -P)"
  local rel
  case "$p_real" in
    "$vlir_root"/*) rel="${p_real#$vlir_root/}" ;;
    "$adopted_rvt_root"/*) rel="tests__adopted_rust_verify_test__$(basename "$p_real")" ;;
    "$verus_root/tests"/*) rel="${p_real#$verus_root/}" ;;
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
  # Given a stem like "quants_M" or "broadcast_proof_m1", return the root
  # stem ("quants" or "broadcast_proof") by stripping the last `_segment`.
  # The caller (has_primary_module_artifact) will verify the primary exists.
  local stem="$1"
  if [[ "$stem" =~ ^(.+)_[^_]+$ ]]; then
    echo "${BASH_REMATCH[1]}"
    return 0
  fi
  return 1
}

infer_suite_from_rs_path() {
  local p="$1"
  local p_real
  p_real="$(abs_file_path "$p")"
  local vlir_root adopted_rvt_root verus_tests_root examples_root
  vlir_root="$(cd "$VERUSFILES_DIR" && pwd -P)"
  adopted_rvt_root="$(cd "$ADOPTED_RVT_DIR" 2>/dev/null && pwd -P || true)"
  verus_tests_root="$(cd "$VERUS_DIR/tests" && pwd -P)"
  examples_root="$(cd "$VERUS_DIR/examples" && pwd -P)"
  case "$p_real" in
    "$vlir_root"/*) echo "vlir-tests" ;;
    "$adopted_rvt_root"/*) echo "vlir-tests" ;;
    "$verus_tests_root"/*) echo "vlir-tests" ;;
    "$examples_root"/*) echo "verus-examples" ;;
    *) echo "verus-examples" ;;
  esac
}

collect_local_vlir_rs_files() {
  local file
  for dir in "$VERUSFILES_DIR" "$ADOPTED_RVT_DIR"; do
    [ -d "$dir" ] || continue
    while IFS= read -r file; do
      printf '%s\n' "$file"
    done < <(find "$dir" -maxdepth 1 -type f -name '*.rs' | sort)
  done
}

collect_all_suite_rs_files() {
  local file
  local base

  # Match the suite coverage used by regress_examples.sh.
  while IFS= read -r file; do
    printf '%s\n' "$file"
  done < <(collect_local_vlir_rs_files)

  while IFS= read -r file; do
    base="$(basename "$file")"
    if [ -f "$VERUSFILES_DIR/$base" ]; then
      continue
    fi
    if [ -f "$ADOPTED_RVT_DIR/$base" ]; then
      continue
    fi
    printf '%s\n' "$file"
  done < <(find "$VERUS_DIR/tests" -maxdepth 1 -type f -name '*.rs' | sort)

  while IFS= read -r file; do
    base="$(basename "$file" .rs)"
    if [ "$base" = "verified_vec" ]; then
      continue
    fi
    printf '%s\n' "$file"
  done < <(find "$VERUS_DIR/examples" -maxdepth 1 -type f -name '*.rs' | sort)

  if [ -d "$VERUS_DIR/examples/guide" ]; then
    while IFS= read -r file; do
      printf '%s\n' "$file"
    done < <(find "$VERUS_DIR/examples/guide" -type f -name '*.rs' | sort)
  fi
}

json_file_for_rs_path() {
  local rs_path="$1"
  local out_base
  out_base="$(map_output_base "$(basename "$rs_path" .rs)")"
  echo "$(boogie_json_case_dir_for_rs_path "$rs_path")/${out_base}.json"
}

boogie_json_dir_for_suite() {
  case "$1" in
    vlir-tests) echo "$JSON_BOOGIE_VLIR_DIR" ;;
    *) echo "$JSON_BOOGIE_EXAMPLES_DIR" ;;
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
      if [ -f "$VERUSFILES_DIR/$in_base.rs" ] || [ -f "$ADOPTED_RVT_DIR/$in_base.rs" ]; then
        echo "vlir-tests"
      else
        echo "verus-examples"
      fi
      ;;
  esac
}

boole_wrapper_dir_for_suite() {
  case "$1" in
    vlir-tests) echo "$BOOLE_PROGRAMS_DIR/vlir-tests" ;;
    *) echo "$BOOLE_PROGRAMS_DIR/verus-examples" ;;
  esac
}

resolve_boole_wrapper_for_rs_path() {
  local p="$1"
  local suite case_key
  suite="$(infer_suite_from_rs_path "$p")"
  case_key="$(case_key_from_rs_path "$p")"
  echo "$(boole_wrapper_dir_for_suite "$suite")/${case_key}.lean"
}

resolve_boole_wrapper_for_json_path() {
  local p="$1"
  local suite case_key
  suite="$(infer_suite_from_json_path "$p")"
  case_key="$(case_key_from_json_path "$p")"
  echo "$(boole_wrapper_dir_for_suite "$suite")/${case_key}.lean"
}

has_primary_module_artifact() {
  local artifact_path="$1"
  local suffix="$2"
  local stem parent candidate
  stem="$(basename "$artifact_path" "$suffix")"
  parent="$(cd "$(dirname "$artifact_path")" && pwd -P)"
  # Try progressively shorter prefixes by stripping trailing `_segment`
  # components until we find a sibling primary artifact.
  candidate="$stem"
  while candidate="$(module_shard_root "$candidate")"; do
    if [ -f "$parent/${candidate}${suffix}" ]; then
      return 0
    fi
  done
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
  local program_file="$1"
  local out_file="$2"
  local requested_base="${3:-}"
  local base ident
  if [ -n "$requested_base" ]; then
    base="$requested_base"
  else
    base="$(basename "$program_file")"
    base="${base%.core.st}"
    base="${base%.boole.st}"
  fi
  ident="$(lean_ident_from_base "$base")"
  mkdir -p "$(dirname "$out_file")"
  {
    # The Boole language lives in the downstream `StrataBoole` package: its
    # MetaVerifier registers the `Boole` dialect and provides `Strata.Boole.verify`.
    echo "import StrataBoole.MetaVerifier"
    echo
    echo "open Strata"
    echo
    # Large generated Boole programs (e.g. field arithmetic) elaborate deeply
    # through the `#strata` macro; Lean's default `maxRecDepth` (512) overflows
    # with "maximum recursion depth has been reached".  This only raises the
    # ceiling, so smaller programs are unaffected.
    echo "set_option maxRecDepth 100000"
    echo
    echo "private def ${ident}_program : StrataDDM.Program :="
    echo "#strata"
    echo "program Boole;"
    sed '1{/^[[:space:]]*program [A-Za-z][A-Za-z]*;.*$/d;}' "$program_file"
    echo "#end"
    echo
    echo "#eval Strata.Boole.verify \"$solver\" ${ident}_program (options := .quiet)"
  } >"$out_file"
}

# When --solver was passed explicitly, rewrite the solver in an already-generated
# wrapper so `--verify --solver X` (without re-running --boole) uses X. The
# wrapper is a regenerable artifact, so the in-place rewrite is safe.
rewrite_wrapper_solver() {
  local wrapper="$1"
  if $solver_explicit && [ -f "$wrapper" ]; then
    local tmp="$wrapper.solver.tmp"
    if sed "s/Strata\\.Boole\\.verify \"[A-Za-z0-9_]*\"/Strata.Boole.verify \"$solver\"/" "$wrapper" >"$tmp"; then
      mv "$tmp" "$wrapper"
    else
      rm -f "$tmp"
    fi
  fi
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

# Shared Strata Boole verify helpers (run_boole_verify, classify_boole_verify_log).
# Keeps the pass/skip/fail classification consistent between this script and
# check_working_tests.sh.
# shellcheck source=tests/lib/boole_verify.sh
source "$ROOT_DIR/tests/lib/boole_verify.sh"

run_verus_export() {
  local file="$1"
  local base="$2"
  local out_base="$3"
  local rc
  local out_json_final
  local out_json_tmp
  local out_json_alt_tmp
  local out_dir
  local tmp_dir
  local shard

  out_dir="$(boogie_json_case_dir_for_rs_path "$file")"
  mkdir -p "$out_dir"
  tmp_dir="$(mktemp -d "$out_dir/.export_${base}.XXXXXX")"
  out_json_final="$out_dir/${out_base}.json"
  out_json_tmp="$tmp_dir/${base}.json"
  out_json_alt_tmp="$tmp_dir/${out_base}.json"
  # Rust crate names disallow `-`, so Verus normalizes hyphens in the
  # source-file stem to underscores when picking the JSON output name
  # (e.g. `proposal-rw2022.rs` → `proposal_rw2022.json`).  Look for the
  # underscored name as a third candidate so hyphenated sources don't
  # spuriously classify as "json missing".
  out_json_norm_tmp="$tmp_dir/${base//-/_}.json"
  out_json_norm_alt_tmp="$tmp_dir/${out_base//-/_}.json"
  set +e
  if $verbose; then
    run_cmd_quiet_in_dir "$tmp_dir" "$VERUS_BIN" --export-lean-all "$file"
    rc=$?
  else
    # Quiet mode: suppress Verus chatter but still surface its
    # "verification results:: N verified, M errors" summary line.
    verus_out="$( (cd "$tmp_dir" && "$VERUS_BIN" --export-lean-all "$file") 2>&1 )"
    rc=$?
    printf '%s\n' "$verus_out" | grep -E 'verification results::' || true
  fi
  set -e
  if [ $rc -ne 0 ] && $verbose; then
    echo "Verus exited non-zero for $base; continuing if JSON was produced."
  fi
  if [ -f "$out_json_alt_tmp" ]; then
    mv -f "$out_json_alt_tmp" "$out_json_final"
  elif [ -f "$out_json_tmp" ]; then
    mv -f "$out_json_tmp" "$out_json_final"
  elif [ -f "$out_json_norm_alt_tmp" ]; then
    mv -f "$out_json_norm_alt_tmp" "$out_json_final"
  elif [ -f "$out_json_norm_tmp" ]; then
    mv -f "$out_json_norm_tmp" "$out_json_final"
  else
    failures+=("$base (json missing)")
  fi
  for shard in "$tmp_dir/${base}_"*.json "$tmp_dir/${out_base}_"*.json "$tmp_dir/${base//-/_}_"*.json "$tmp_dir/${out_base//-/_}_"*.json; do
    [ -f "$shard" ] || continue
    mv -f "$shard" "$out_dir/"
  done
  rm -rf "$tmp_dir"
}

run_verus=false
run_boole=false
run_verify=false
run_all_flag=false
target_rs_path=""
target_json_path=""
target_lean_path=""
custom_out_path=""
declare -a all_suite_rs_files=()

if [ $# -eq 0 ]; then
  usage
  exit 0
fi

positional=()
while [ $# -gt 0 ]; do
  case "$1" in
    --verus) run_verus=true; shift ;;
    --boole) run_boole=true; shift ;;
    --verify) run_verify=true; shift ;;
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
    --solver)
      if [ $# -lt 2 ]; then
        echo "Missing value for --solver"
        usage
        exit 1
      fi
      solver="$2"
      solver_explicit=true
      shift 2
      ;;
    --solver=*)
      solver="${1#*=}"
      solver_explicit=true
      shift
      ;;
    --synth-disable)
      if [ $# -lt 2 ]; then
        echo "Missing value for --synth-disable"
        usage
        exit 1
      fi
      synth_disable="$2"
      shift 2
      ;;
    --synth-disable=*)
      synth_disable="${1#*=}"
      shift
      ;;
    --all) run_verus=true; run_boole=true; run_verify=true; run_all_flag=true; shift ;;
    -h|--help) usage; exit 0 ;;
    --) shift; while [ $# -gt 0 ]; do positional+=("$1"); shift; done ;;
    --*) echo "Unknown option: $1"; usage; exit 1 ;;
    *) positional+=("$1"); shift ;;
  esac
done

# Forward the synthesized-aid toggle to `verus-lean` (read by Main.lean's
# `synthConfigFromEnv` during Boole generation). Empty = all aids on.
export BOOLE_SYNTH_DISABLE="$synth_disable"

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
  candidate_abs="$(abs_file_path "$candidate")"
  case "$candidate_abs" in
    *.rs) target_rs_path="$candidate_abs" ;;
    *.json) target_json_path="$candidate_abs" ;;
    *.lean) target_lean_path="$candidate_abs" ;;
    *)
      echo "Unsupported target file type: $candidate"
      echo "Expected .rs, .json, or .lean"
      exit 1
      ;;
  esac
fi

# `--boole` is an end-to-end target. Infer prerequisite stages from the input:
#   .rs      => Verus export + Boole generation (JSON → Boole directly)
#   .json    => Boole generation directly
if $run_boole; then
  if [ -n "$target_rs_path" ]; then
    run_verus=true
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
  if ! $run_boole; then
    echo "--out is only supported with --boole."
    exit 1
  fi
fi

if ! $run_verus && ! $run_boole && ! $run_verify; then
  usage
  exit 1
fi

if $run_all_flag && [ -z "$target_rs_path" ] && [ -z "$target_json_path" ] && [ -z "$target_lean_path" ]; then
  while IFS= read -r file; do
    [ -n "$file" ] || continue
    all_suite_rs_files+=("$file")
  done < <(collect_all_suite_rs_files)
fi

mkdir -p "$JSON_BOOGIE_DIR" "$JSON_BOOGIE_EXAMPLES_DIR" "$JSON_BOOGIE_VLIR_DIR" \
  "$BOOLE_DIR" "$BOOLE_PROGRAMS_DIR"

if $run_verus; then
  echo "=== Step 1: Verus -> JSON ==="
  if [ -n "$target_json_path" ] || [ -n "$target_lean_path" ]; then
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
    fi

    if [ -n "$target_rs_path" ]; then
      files=("$target_rs_path")
    elif $run_all_flag; then
      files=("${all_suite_rs_files[@]}")
    else
      while IFS= read -r file; do
        files+=("$file")
      done < <(collect_local_vlir_rs_files)
    fi
    if [ ! -e "${files[0]}" ]; then
      if $run_all_flag; then
        echo "No Verus test files found in the selected suites."
      else
        echo "No Verus test files found in $VERUSFILES_DIR or $ADOPTED_RVT_DIR"
      fi
      exit 1
    fi

    failures=()
    for file in "${files[@]}"; do
      base=$(basename "$file" .rs)
      out_base=$(map_output_base "$base")
      echo "Verus: $base"
      run_verus_export "$file" "$base" "$out_base"
    done

    if [ ${#failures[@]} -gt 0 ]; then
      echo "Verus export failures (missing JSON): ${failures[*]}"
    fi
  )
fi

if $run_boole; then
  echo ""
  echo "=== Step 2: JSON -> Boole ==="
  if [ -n "$target_lean_path" ]; then
    echo "--boole target must be .rs or .json (not .lean)."
    exit 1
  fi
  if [ ! -x "$VERUS_LEAN" ]; then
    echo "Missing verus-lean binary at $VERUS_LEAN (run lake build)"
    exit 1
  fi

  # Find JSON source
  json_source=""
  if [ -n "$target_json_path" ]; then
    json_source="$target_json_path"
  elif [ -n "$target_rs_path" ]; then
    json_source="$(json_file_for_rs_path "$target_rs_path" || true)"
  fi

  if [ -n "$json_source" ] && [ -f "$json_source" ]; then
    # Single-target mode
    case_key="$(case_key_from_json_path "$json_source")"
    suite="$(infer_suite_from_json_path "$json_source")"
    base="$case_key"
    echo "Boole: $base"
    boole_st_file=""
    lean_file=""
    if [ -n "$custom_out_path" ]; then
      boole_st_file="$custom_out_path"
    else
      boole_st_file="$BOOLE_DIR/${suite}/${base}.boole.st"
      lean_file="$BOOLE_PROGRAMS_DIR/${suite}/${base}.lean"
    fi
    mkdir -p "$(dirname "$boole_st_file")"
    set +e
    run_cmd_quiet "$VERUS_LEAN" boole "$json_source" "$boole_st_file"
    boole_rc=$?
    set -e
    if [ $boole_rc -ne 0 ]; then
      echo "Boole generation failed for $base"
    fi
    if [ -n "$lean_file" ] && [ -f "$boole_st_file" ]; then
      write_boole_wrapper "$boole_st_file" "$lean_file" "$base"
    fi
  elif [ -z "$target_rs_path" ] && [ -z "$target_json_path" ]; then
    # Batch mode: iterate over all JSON directories
    any=false
    for scan_dir in "$JSON_BOOGIE_VLIR_DIR" "$JSON_BOOGIE_EXAMPLES_DIR"; do
      [ -d "$scan_dir" ] || continue
      while IFS= read -r d; do
        [ -d "$d" ] || continue
        local_name="$(basename "$d")"
        local_json="$d/${local_name}.json"
        [ -f "$local_json" ] || continue
        any=true
        suite="$(infer_suite_from_json_path "$local_json")"
        echo "Boole: $local_name"
        out="$BOOLE_DIR/${suite}/${local_name}.boole.st"
        lean_out="$BOOLE_PROGRAMS_DIR/${suite}/${local_name}.lean"
        mkdir -p "$(dirname "$out")"
        set +e
        run_cmd_quiet "$VERUS_LEAN" boole "$local_json" "$out"
        set -e
        if [ -f "$out" ]; then
          write_boole_wrapper "$out" "$lean_out" "$local_name"
        fi
      done < <(find "$scan_dir" -mindepth 1 -maxdepth 1 -type d | sort)
    done
    if ! $any; then
      echo "No JSON inputs found for Boole generation."
      exit 1
    fi
  else
    echo "json missing for target"
    exit 1
  fi
fi


if $run_verify; then
  echo ""
  echo "=== Step 3: Strata Boole verify ==="
  if [ ! -d "$STRATA_DIR" ]; then
    echo "Missing Strata repo at $STRATA_DIR"
    exit 1
  fi
  if [ -n "$target_lean_path" ]; then
    case "$target_lean_path" in
      /*) verify_path="$target_lean_path" ;;
      *) verify_path="$ROOT_DIR/$target_lean_path" ;;
    esac
    echo "Verify: $(basename "$verify_path")"
    rewrite_wrapper_solver "$verify_path"
    run_boole_verify "$verify_path" "full" "$verbose"
  elif [ -n "$target_rs_path" ] || [ -n "$target_json_path" ]; then
    if [ -n "$target_rs_path" ]; then
      verify_path="$(resolve_boole_wrapper_for_rs_path "$target_rs_path")"
    else
      verify_path="$(resolve_boole_wrapper_for_json_path "$target_json_path")"
    fi
    if [ -z "$verify_path" ] || [ ! -f "$verify_path" ]; then
      echo "Missing Boole .lean wrapper for target: ${target_rs_path:-$target_json_path}"
      echo "Run with --boole first (or use --boole --verify together)."
      exit 1
    fi
    echo "Verify: $(basename "$verify_path")"
    rewrite_wrapper_solver "$verify_path"
    run_boole_verify "$verify_path" "full" "$verbose"
  else
    any=false
    verify_rc=0
    if $run_all_flag; then
      for rs_path in "${all_suite_rs_files[@]}"; do
        verify_path="$(resolve_boole_wrapper_for_rs_path "$rs_path")"
        case_key="$(case_key_from_rs_path "$rs_path")"
        any=true
        if [ -z "$verify_path" ] || [ ! -f "$verify_path" ]; then
          echo "${case_key}.lean: missing"
          verify_rc=1
          continue
        fi
        set +e
        run_boole_verify "$verify_path" "concise" "$verbose"
        rc=$?
        set -e
        if [ $rc -ne 0 ]; then
          verify_rc=1
        fi
      done
    else
      for scan_dir in "$BOOLE_PROGRAMS_DIR/vlir-tests" "$BOOLE_PROGRAMS_DIR/verus-examples"; do
        [ -d "$scan_dir" ] || continue
        for file in "$scan_dir"/*.lean; do
          if [ ! -f "$file" ]; then
            break
          fi
          if has_primary_module_artifact "$file" ".lean"; then
            continue
          fi
          any=true
          set +e
          run_boole_verify "$file" "concise" "$verbose"
          rc=$?
          set -e
          if [ $rc -ne 0 ]; then
            verify_rc=1
          fi
        done
      done
    fi
    if ! $any; then
      echo "No Boole .lean wrappers found in $BOOLE_PROGRAMS_DIR"
      exit 1
    fi
    if [ $verify_rc -ne 0 ]; then
      exit $verify_rc
    fi
  fi
fi
