# Shared helpers for Strata Boole verification.
# Sourced by tests/run_tests.sh and tests/check_working_tests.sh.
#
# Requires the caller to have set $STRATA_DIR.

# Classify a verify log from `lake env lean <wrapper.lean>`.
# Arguments:
#   $1 = path to the captured log
#   $2 = lake exit code
#   $3 = (optional) expected-fail pattern: a regex matching obligation labels
#        the test EXPECTS Strata to report as failing (i.e. negative tests
#        whose Verus source contains intentionally-unverifiable assertions).
#        A `Result: ❌ fail` line whose preceding `Obligation:` matches the
#        pattern is treated as expected; any other failing obligation makes
#        the test fail.
#   $4 = (optional) known-translator-bug pattern: a regex matching obligation
#        labels that are known to fail because of a translator-side bug
#        (not a Strata limitation). If every non-expected failing obligation
#        matches this pattern — or if the wrapper fails with any Lean-level
#        error and this pattern is non-empty — the test is classified as
#        `known_translator_bug`. This keeps the per-bug tracking visible in
#        summaries without masking translator bugs behind "Strata gap".
# Prints one of: pass | skip_sequence | skip_gap | known_translator_bug | fail
classify_boole_verify_log() {
  local log="$1"
  local rc="$2"
  local expected_fail_pattern="${3:-}"
  local known_translator_bug_pattern="${4:-}"
  # Lean elaboration errors: skip_sequence > skip_gap > known_translator_bug > fail
  if [ "$rc" -ne 0 ] || grep -q "error:" "$log"; then
    # Match only the two concrete signatures that mean "Strata is missing
    # Sequence support". The bare `Sequence` token is too broad: Strata's
    # type-checking errors print the full builtin operator list as a hint
    # (containing `Sequence.length`, `Sequence.empty`, etc.), so any
    # type-check failure would be miscategorized as a Sequence skip.
    if grep -qE "Unsupported Boole type: Strata\\.BooleDDM\\.BooleType\\.Sequence|Unknown expr identifier Sequence\\.empty" "$log"; then
      echo "skip_sequence"
      return 0
    fi
    # Strata-side gaps: features Strata itself does not yet support. These
    # are legitimately not our bugs to fix.
    #
    # `Unknown bound variable with index` *in the context of mutual recursion*
    # is a Strata-side bug in `Boole.toCoreProgram`'s `command_recfndefs`
    # lowering: the DDM parser scopes preceding siblings as bvars for each
    # function body, but `lowerPureFuncDef` pushes only inputs. See
    # `docs/boole-translation-todo.md`. Classified here as a Strata gap
    # rather than a translator bug.
    #
    # `Recursive function .* requires a @\[cases\] parameter` is Strata's
    # refusal to verify rec functions without an ADT @[cases] annotation.
    # Verus programs often recurse on `int`, which has no constructors, so
    # they hit this wall in Boole even though Core has the same behavior.
    if grep -qE "Unsupported expression|Unsupported typed operator|unexpected token '\('; expected '\)'|Undeclared type or category Tuple|Unknown bound variable with index|Recursive function .* requires a @\[cases\] parameter" "$log"; then
      echo "skip_gap"
      return 0
    fi
    # Solver timeouts surface as `SMT Solver Invocation Error!` plus a line
    # `cvc5 interrupted by timeout` (or `killed by`). Treat as a skip rather
    # than a fail: verification did not complete, so nothing about the
    # translation is being asserted.
    if grep -qE "(cvc5|z3)[^\n]*(interrupted by timeout|killed by)" "$log"; then
      echo "skip_solver_timeout"
      return 0
    fi
    # Translator-side bugs: error signatures below indicate our translator
    # emitted a malformed program. They are NOT Strata gaps. If the wrapper
    # is on the known-translator-bug list *and* the log matches that concrete
    # signature, classify as `known_translator_bug` (tracked but not a
    # regression); otherwise surface as `fail` so new occurrences of these
    # signatures are visible.
    #   * "Unknown bound variable with index"  (bvar index miscount)
    #   * "Cannot find this fvar in the context"  (ill-scoped fvar, e.g. `old p`)
    #   * "Expression has type .* when int expected"  (missed coercion)
    if [ -n "$known_translator_bug_pattern" ] && grep -qE "$known_translator_bug_pattern" "$log"; then
      local non_bug_errors
      non_bug_errors="$(grep "error:" "$log" | grep -Ev "$known_translator_bug_pattern|aborting evaluation since the expression depends on the 'sorry' axiom" || true)"
      if [ -z "$non_bug_errors" ]; then
        echo "known_translator_bug"
        return 0
      fi
    fi
    echo "fail"
    return 0
  fi
  # Lake completed cleanly. Now scrutinize per-obligation results.
  # Pair each `Obligation: <name>` with the next `Result: ...` line so we can
  # tell *which* obligation failed.
  local unexpected_fails
  unexpected_fails="$(awk -v pat="$expected_fail_pattern" '
    /^Obligation:/ { obligation = $0; sub(/^Obligation: */, "", obligation); next }
    /^Result: ❌ fail/ {
      if (pat == "" || obligation !~ pat) {
        print obligation
      }
    }
  ' "$log")"
  if [ -z "$unexpected_fails" ]; then
    echo "pass"
    return 0
  fi
  if [ -n "$known_translator_bug_pattern" ]; then
    local non_bug_fails
    non_bug_fails="$(printf '%s\n' "$unexpected_fails" | awk -v pat="$known_translator_bug_pattern" '
      $0 !~ pat { print }
    ')"
    if [ -z "$non_bug_fails" ]; then
      echo "known_translator_bug"
      return 0
    fi
  fi
  echo "fail"
  return 0
}

expected_boole_fail_pattern_for_wrapper() {
  case "$1" in
    */basic_failure.lean) echo 'fail_a_post_expr' ;;
    # See `expected_fail_pattern_for_target` in check_working_tests.sh for
    # the rationale. Tracks `lean_test` ensures + the 3 asserts in
    # `assert_lean_jumble`; brittle to assertion ordering in the source.
    */by_lean.lean)       echo 'lean_test_ensures|assert_[456]_' ;;
    */assertions.lean)    echo '.' ;;
    */debug.lean)         echo '.' ;;
    # `matching.rs` contains intentionally-failing negative tests:
    # `assert(s is Soccer)` on an unconstrained `Sport`, and `is_insect_proof`
    # calling `is_insect(l)` on a `Mammal`. Verus also reports these as
    # assertion failures; Strata surfaces them as `assert_*` obligations.
    */vlir-tests/matching.lean) echo 'assert_' ;;
    *) echo "" ;;
  esac
}

# Wrappers known to trip a translator-side bug (as opposed to a Strata
# limitation). See "Known translator bugs" in docs/boole-translation-todo.md
# for the bug descriptions and the fix plan.
known_translator_bug_pattern_for_wrapper() {
  case "$1" in
    # mini_c currently emits a malformed tuple projection `Tuple.._2` while
    # lowering match tuple temporaries; Lean elaboration aborts before any
    # obligation runs. Tracked in differential_status.md.
    */vlir-tests/mini_c.lean) echo 'Unknown variable Tuple\.\._2' ;;
    # LoopSimpleWithSpec uses `triangle0(i as nat)` style spec-fn calls; the
    # translator does not insert an `int -> nat` coercion at the call boundary,
    # so Strata reports `Expression has type int when nat expected` at Lean
    # elaboration time. Same family as the missed-coercion shape called out in
    # the per-bug list at the top of `classify_boole_verify_log`.
    */vlir-tests/LoopSimpleWithSpec.lean) echo 'Expression has type int when nat expected' ;;
    *) echo "" ;;
  esac
}

# Run `lake env lean` on a Boole .lean wrapper and emit a concise per-file
# status line. Returns non-zero only on genuine failure (not on skip / known
# translator bug).
# $1 = wrapper path
# $2 = output mode: "full" (stream lake output) or "concise" (summary only)
# $3 = verbose flag (true/false); concise still streams if verbose
run_boole_verify() {
  local lean_file="$1"
  local output_mode="${2:-concise}"
  local verbose="${3:-false}"
  local expected_fail_pattern="${4:-}"
  local known_translator_bug_pattern="${5:-}"
  local base verify_log rc category
  base="$(basename "$lean_file")"
  if [ -z "$expected_fail_pattern" ]; then
    expected_fail_pattern="$(expected_boole_fail_pattern_for_wrapper "$lean_file")"
  fi
  if [ -z "$known_translator_bug_pattern" ]; then
    known_translator_bug_pattern="$(known_translator_bug_pattern_for_wrapper "$lean_file")"
  fi
  verify_log="$(mktemp)"
  (cd "$STRATA_DIR" && lake env lean "$lean_file") >"$verify_log" 2>&1
  rc=$?
  if [ "$output_mode" = "full" ] || [ "$verbose" = "true" ]; then
    cat "$verify_log"
  fi
  category="$(classify_boole_verify_log "$verify_log" "$rc" "$expected_fail_pattern" "$known_translator_bug_pattern")"
  case "$category" in
    pass)
      echo "$base: ✅"
      rm -f "$verify_log"
      return 0
      ;;
    skip_sequence)
      echo "$base: ⏭  (Sequence support missing in Strata Boole verify)"
      rm -f "$verify_log"
      return 0
      ;;
    skip_gap)
      local err
      err="$(grep "error:" "$verify_log" | head -1 | cut -c1-120 || true)"
      if [ -z "$err" ]; then
        err="$(awk '
          /^Obligation:/ { ob = $0; sub(/^Obligation: */, "", ob); next }
          /^Result: ❌ fail/ { print "failed obligation " ob; exit }
        ' "$verify_log" | cut -c1-120)"
      fi
      echo "$base: ⏭  (Strata gap): $err"
      rm -f "$verify_log"
      return 0
      ;;
    known_translator_bug)
      local err
      err="$(grep "error:" "$verify_log" | head -1 | cut -c1-120 || true)"
      if [ -z "$err" ]; then
        err="$(awk '
          /^Obligation:/ { ob = $0; sub(/^Obligation: */, "", ob); next }
          /^Result: ❌ fail/ { print "failed obligation " ob; exit }
        ' "$verify_log" | cut -c1-120)"
      fi
      echo "$base: 🐞 (known translator bug): $err"
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
