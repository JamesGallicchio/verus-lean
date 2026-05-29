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
    # `[rR]ecursive function .* requires .* @\[cases\]` is Strata's refusal
    # to verify rec functions without an ADT @[cases] annotation.  Verus
    # programs often recurse on `int`, which has no constructors, so they
    # hit this wall in Boole even though Core has the same behavior.  The
    # `.*` between "requires" and "@[cases]" tolerates Strata's newer
    # wording that adds `a 'decreases' clause or` before `@[cases]`
    # (kondylidou/pr/benchmarks after #1092 termination-checking landed).
    if grep -qE "Unsupported expression|Unsupported typed operator|unexpected token '\('; expected '\)'|Undeclared type or category Tuple|Unknown bound variable with index|[rR]ecursive function .* requires .*@\[cases\]" "$log"; then
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
  #
  # Three per-obligation results count as non-passing — a transition from
  # `pass` to any of them is a real loss of proof power and must be flagged,
  # not tolerated:
  #   * `❌ fail`               — cvc5 found a counterexample;
  #   * `❓ unknown`            — cvc5 gave up;
  #   * `🚨 SMT Encoding Error` — the obligation never even reached the solver
  #     (e.g. an unused polymorphic decl's unmonomorphizable type var).  This
  #     is a *hard* failure and was previously invisible, silently hiding
  #     dozens of broken obligations behind a "pass".
  # Obligations documented in the per-wrapper `expected_fail_pattern` are
  # exempt (known-hard goals / known Strata gaps).
  #
  # Per-obligation `🚨 Solver Timeout` is deliberately NOT matched — timeouts
  # are nondeterministic, and a whole-run timeout is already handled above as
  # `skip_solver_timeout`.
  local unexpected_fails
  unexpected_fails="$(awk -v pat="$expected_fail_pattern" '
    /^Obligation:/ { obligation = $0; sub(/^Obligation: */, "", obligation); next }
    /^Result: ❌ fail/ || /^Result: ❓ unknown/ || /^Result: 🚨 SMT Encoding Error/ {
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

# Single source of truth for expected-fail obligation patterns, used by
# `classify_boole_verify_log` here AND by `check_working_tests.sh::
# expected_fail_pattern_for_target` (which now delegates to this fn via
# `lean_wrapper_for_target`).
#
# Obligation labels have the shape `<stable-prefix>_<idx>_<serial>` (e.g.
# `assert_15_1719`, `bitvector_query`, `triangle0_terminates_0`).  The
# trailing `_<serial>` is a Provenance positional counter that *renumbers*
# whenever upstream Strata's metadata changes (the 2026-05-18 int-
# termination pull is one such event).  Anchor patterns on the stable
# prefix (semantic name, or `<name>_<idx>_`) and never on the volatile
# serial, so a pin bump does not spuriously re-flag these as regressions.
# A genuinely new failing obligation has a different prefix and still
# surfaces.
expected_boole_fail_pattern_for_wrapper() {
  case "$1" in
    # ── negative tests (intentional source-level failures) ──────────────
    */vlir-tests/basic_failure.lean) echo 'fail_a_post_expr' ;;
    # `by_lean.rs`: `lean_test` ensures fails + asserts in
    # `assert_lean_jumble`. Brittle to assertion ordering in source.
    */vlir-tests/by_lean.lean)       echo 'lean_test_ensures|assert_[4-9]_' ;;
    # `matching.rs` intentionally fails on `assert(s is Soccer)` (an
    # unconstrained enum) and `is_insect(mammal) == 6` (calls a `->`
    # accessor with the wrong variant precondition).
    */vlir-tests/matching.lean)      echo 'assert_' ;;
    # verus/examples/*.rs with `expect-failures` header comment
    */verus-examples/assertions.lean) echo '.' ;;
    */verus-examples/debug.lean)      echo '.' ;;

    # ── pre-documented not-faithful translations (see differential_status
    #    "not faithful translation"): fail (or return ❓ unknown) on specific
    #    obligations for known, unrelated reasons (hard bv/quantifier/
    #    int-recursion goals, generic type-var SMT encoding, intentional
    #    type_fail/bvslt baselines).
    #
    #    NOTE: the classifier counts ❓ unknown the same as ❌ fail (a
    #    `pass -> unknown` transition is a real loss of proof power and must
    #    be flagged).  Most obligations below are ❓ unknown, not ❌ fail.
    #    These were verified NOT to be regressions from the nat-prelude /
    #    nat-arithmetic migration: the always-loaded nat axioms are inert
    #    without ground `nat.toInt` terms in the goal (confirmed by stripping
    #    the Nat prelude from `bitvector_equivalence` — unknown count
    #    unchanged), and only `quantifiers` uses `nat` in its body (where the
    #    `nat.toInt(i) >= 0` sub-goal actually became *more* provable).
    #    Obligation indices shifted (`assert_15` -> `assert_20`, etc.) because
    #    the always-loaded Nat prelude adds declarations ahead of them; anchor
    #    on the semantic prefix where possible. ─

    # `[TRANS-coercion-uninterpreted]`: `∀ i:nat :: nat.toInt(i) >= 0 &&
    # tr(nat.toInt(i))` — the `>= 0` half is now provable via `nat_nonneg`,
    # but the uninterpreted `tr(...)` half keeps the obligation unknown.
    */verus-examples/quantifiers.lean)           echo 'assert_20_' ;;
    # `[TRANS-coercion-uninterpreted]`: `b1 == i*2` loop entry-invariant
    # over uninterpreted `bv8_to_bv64_u`, plus the loop's maintain-invariant
    # and a dependent assert.
    */verus-examples/statements.lean)            echo 'entry_invariant_|arbitrary_iter_maintain_invariant_|assert_13_' ;;
    # `[TRANS-coercion-uninterpreted]`: `bitvector_query`/`compute`
    # obligations depending on uninterpreted `bv8_to_*` coercions.
    */verus-examples/bitvector_basic.lean)       echo 'bitvector_query|compute|assert_32_' ;;
    # `[VERIFY-generic-typevar-ddm]`: SMT encoding error on type-var
    # obligations (`id_exec_ensures_`, `assert_7`); dependent asserts
    # (`assert_8`/`assert_9`) also go unknown.  This is a Strata DDM
    # limitation on verifying generic functions abstractly, not a translation
    # defect — kept documented now that `🚨 SMT Encoding Error` is counted.
    */verus-examples/generics.lean)              echo 'id_exec_ensures_|assert_[789]_' ;;
    # `[VERIFY-bv-equivalence]`: the curve25519-style bit-equivalence
    # induction over 32 `equivalence_proof_bv` call-elim preconditions is
    # beyond cvc5's bv reasoning here (confirmed pre-existing: independent of
    # the nat prelude).
    */verus-examples/bitvector_equivalence.lean) echo 'callElimAssert_equivalence_proof_' ;;
    # `[VERIFY-funext]`: function-extensionality ensures + dependent asserts
    # cvc5 cannot discharge without an extensionality axiom.
    */verus-examples/fun_ext.lean)               echo 'test_funext_specific_|assert_(5|8|11)_' ;;
    # `[TRANS-coercion-uninterpreted]`: `s >= n` precondition becomes
    # `s >= bv64_to_int_u(n)` with `bv64_to_int_u` uninterpreted.
    */verus-examples/external.lean)              echo 'callElimAssert_test_requires_' ;;
    # Intentional baseline: `type_fail` + cvc5 `wide_mul` timeout +
    # nonlinear `*_ensures_*` cvc5 cannot discharge.
    */vlir-tests/tests__adopted_rust_verify_test__integer_ring.lean) echo '_ensures_' ;;
    # Intentional bvslt/bvsle verify-mismatch baseline (strata-bv-lowering
    # issue) plus int-termination `triangle0_terminates_*` measure
    # obligations on the same uninterpreted signed-compare path.  The loop's
    # entry/maintain invariants, the `triangle0_is_monotonic` lemma (both its
    # requires call-elim and its ensures), and a dependent assert are all
    # cvc5-unknown — confirmed pre-existing (unchanged by the nat.sub fold;
    # the nat.sub precondition obligations themselves all discharge).
    */vlir-tests/LoopSimpleWithSpec.lean) echo 'entry_invariant_|arbitrary_iter_maintain_invariant_|triangle0_is_monotonic_ensures_|triangle0_is_monotonic_requires_|triangle0_terminates_|assert_4_' ;;

    # ── intended int-termination reclassification (2026-05-18 pull, see
    #    differential_status.md [CORE-decreases]). Translation is faithful;
    #    failing obligations are documented Strata-side limitations, not
    #    translator defects. ───────────────────────────────────────────────

    # int-recursive fns are pure UFs with no definitional axiom, so cvc5
    # cannot prove the inductive `is_even(i) <==> i%2==0` ensures.
    */vlir-tests/mutual_recursion.lean) echo 'even_odd_mod2_ensures_' ;;
    # Verus proves these via a *lexicographic* measure
    # (`decreases abs(i), 0int`); the translator collapses lex-decreases
    # to the head term, so the same-arg `M_is_odd(i) → M_is_even(i)`
    # edge has no strict decrease. Waits on Strata tuple-measure support.
    # Same int-recursive-UF limitation as `mutual_recursion` for the
    # `M_even_odd_mod2_ensures_` goals + the two dependent asserts.
    */vlir-tests/recursion.lean)        echo 'M_is_odd_terminates|M_even_odd_mod2_ensures_|assert_[46]_' ;;
    */verus-examples/guide__recursion.lean) echo 'M_is_odd_terminates|M_even_odd_mod2_ensures_|assert_[46]_' ;;

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
    # guide/datatypes and matching both flip pass/fail run-to-run because Verus'
    # Lean exporter (vir/src/sst_to_lean.rs::lctx.dts: HashSet<Dt>) iterates
    # non-deterministically. When a candidate datatype lands at position 0,
    # Strata's Boole.toCoreProgram lowering references its ctors / testers as
    # free variables on auto-generated call-elim obligations. Filed against
    # Strata as [VERIFY-datatype-tester-ordering]; no translator workaround
    # possible.
    #
    # Each pattern is an alternation over every line of the diagnostic so the
    # script's `grep -Ev <pattern>` residual-error check (which requires every
    # `error:` line to match) accepts the whole multi-line message. The Type
    # checking error line is the wrapper-scoped catch-all; the Free Variables
    # line is the bug-specific signature that must appear for the whitelist to
    # actually trigger.
    */verus-examples/guide__datatypes.lean)
      echo 'Type checking error\.|No free variables are allowed here|Free Variables: \[shape\.\.isshape_' ;;
    */vlir-tests/matching.lean)
      echo 'Type checking error\.|No free variables are allowed here|Free Variables: \[life_' ;;
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
  set +e
  (cd "$STRATA_DIR" && lake env lean "$lean_file") >"$verify_log" 2>&1
  rc=$?
  set -e
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

# -----------------------------------------------------------------------------
# Ignored tests — shared between check_working_tests.sh and regress_examples.sh
# -----------------------------------------------------------------------------
# Returns 0 iff the given test path matches an active (non-comment) entry in
# `tests/ignored_tests.txt` — the single source of truth for tests that are
# not suitable or valuable to run regression on (upstream-marked `ignore`,
# empty-export, known-hang).  Each line in the list is a shell `case` glob
# pattern (e.g. `*/examples/verified_vec.rs`); trailing `# comment` text is
# stripped.  Requires `$ROOT_DIR` to be set by the caller.
is_ignored_test() {
  local target="$1"
  local list="$ROOT_DIR/tests/ignored_tests.txt"
  [ -f "$list" ] || return 1
  local line pat
  while IFS= read -r line; do
    pat="${line%%#*}"
    # Note: use [^...] (bash-specific) not [!...] for the POSIX-style
    # negation; bash with extglob/history off can mis-parse [![:space:]]
    # as matching whitespace (the `!` is read literally).
    pat="${pat#"${pat%%[^[:space:]]*}"}"
    pat="${pat%"${pat##*[^[:space:]]}"}"
    [ -z "$pat" ] && continue
    # shellcheck disable=SC2254  # intentional unquoted glob
    case "$target" in
      $pat) return 0 ;;
    esac
  done < "$list"
  return 1
}
