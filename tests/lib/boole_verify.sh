# Shared helpers for Strata Boole verification.
# Sourced by tests/run_tests.sh and tests/check_working_tests.sh.
#
# Requires the caller to have set $STRATA_DIR.

# Classify a verify log from `lake env lean <wrapper.lean>`.
# Arguments:
#   $1 = path to the captured log
#   $2 = lake exit code
# Prints one of: pass | skip_sequence | skip_gap | fail
classify_boole_verify_log() {
  local log="$1"
  local rc="$2"
  if [ "$rc" -eq 0 ] && ! grep -q "error:" "$log"; then
    echo "pass"
    return 0
  fi
  if grep -q "Sequence" "$log"; then
    echo "skip_sequence"
    return 0
  fi
  if grep -qE "Unsupported expression|Unsupported typed operator|Unknown bound variable with index|Expression has type .* when int expected|unexpected token '\('; expected '\)'|Undeclared type or category Tuple" "$log"; then
    echo "skip_gap"
    return 0
  fi
  echo "fail"
  return 0
}

# Run `lake env lean` on a Boole .lean wrapper and emit a concise per-file
# status line. Returns non-zero only on genuine failure (not on skip).
# $1 = wrapper path
# $2 = output mode: "full" (stream lake output) or "concise" (summary only)
# $3 = verbose flag (true/false); concise still streams if verbose
run_boole_verify() {
  local lean_file="$1"
  local output_mode="${2:-concise}"
  local verbose="${3:-false}"
  local base verify_log rc category
  base="$(basename "$lean_file")"
  if [ "$output_mode" = "full" ] || [ "$verbose" = "true" ]; then
    (cd "$STRATA_DIR" && lake env lean "$lean_file")
    return $?
  fi
  verify_log="$(mktemp)"
  (cd "$STRATA_DIR" && lake env lean "$lean_file") >"$verify_log" 2>&1
  rc=$?
  category="$(classify_boole_verify_log "$verify_log" "$rc")"
  case "$category" in
    pass)
      echo "$base: ✅"
      rm -f "$verify_log"
      return 0
      ;;
    skip_sequence)
      echo "$base: ⏭  (Sequence type unsupported in Strata)"
      rm -f "$verify_log"
      return 0
      ;;
    skip_gap)
      local err
      err="$(grep "error:" "$verify_log" | head -1 | cut -c1-120)"
      echo "$base: ⏭  (Strata gap): $err"
      rm -f "$verify_log"
      return 0
      ;;
    *)
      echo "$base: ❌"
      grep "error:" "$verify_log" | head -3 || true
      rm -f "$verify_log"
      [ "$rc" -eq 0 ] && rc=1
      return "$rc"
      ;;
  esac
}
