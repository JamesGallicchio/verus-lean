# Differential Status

This file tracks three things separately:
- raw Core regression outcomes from `regress_examples.sh`
- Boole smoke/elaboration status for selected cases
- manual faithfulness judgments for reviewed cases

Solver success is **not** used to classify faithfulness.

## Data Sources
- Full run (`./tests/regress_examples.sh --all-suites`):
  - run id: `20260430_204358` (historical baseline; per-test classifications below are anchored to this run unless explicitly updated)
  - solver: `cvc5`
- **2026-06-01 — Strata pin advanced (`kondylidou/pr/casts-boole @ e3c2806fd`,
  fast-forward; now current with `upstream/main2 @ 41cf05e4c`); native casts
  (#1217); generics reclassified.**  The pull landed PR **#1217** (`Bv{n}.ToUInt`
  / `Bv{n}.ToInt` / `Int.ToBv{n}` cast operators) and **#1214** (empty-seq
  literal typing).  Upstream dropped the verus-boogie reference test
  `StrataTest/Languages/Boole/b2_minimal.lean`
  ("deleted the big test to put it in another pr"); it is preserved locally
  (restored on top of the branch, untracked, with its `gen_smt_vcs` experiment).
  - **#1217 — native interpreted casts (`Cast.lean::applyCast`).** The remaining
    uninterpreted cast kinds — `.intToBv`, `.bvWiden`, `.bvToNat` — now emit
    Strata's native postfix ops: `e as_bv<w>`, `(e as_int) as_bv<w>`, and
    `nat.fromInt(e as_int)` (bv→int / nat↔int were already native).  cvc5 now
    reasons through them (SMT `int_to_bv` / `ubv_to_int`) instead of opaque UFs.
    **This RESOLVES `[TRANS-coercion-uninterpreted]` for bv-cast coercions**
    (`bv8_to_bv64_u`, `bv8_to_*`, `bv64_to_int_u`, …): `verus-examples:statements`
    (23✅), `bitvector_basic` (42✅; only the genuinely cvc5-hard `bitvector_query`
    still times out), `external` (5✅) now verify.  Their `boole_verify.sh`
    expected-fail patterns were removed (statements, external) / narrowed to
    `bitvector_query` (bitvector_basic) — the gate now *requires* these
    coercions to discharge.  Other bv-coercion entries below
    (`guide/integers`, `guide/references`, `nonlinear`, `LoopSimple`, …) likely
    benefit too, pending a full all-suites re-run to recompute the
    faithful/different/not-faithful counts.
  - **generics → Strata gap.**  With native casts, a cast on a *non-
    monomorphized* generic result (`g(u):A as u16` → `g(u) as_int`) reaches
    Strata with an abstract type, which `as_int` *correctly* rejects
    (`'as int' requires a bitvector source type, got: …tvar`).  This is the
    existing `[VERIFY-generic-typevar-ddm]` limitation surfacing as an
    elaboration error rather than an SMT encoding error; the faithful native
    emission is kept (no opaque fallback) and `verus-examples:generics` is now
    classified `skip_gap` in `boole_verify.sh`.  Proper fix is Strata-side
    generic monomorphization.
  - **#1214 — no translator change needed.**  We already emit typed empty-seq
    literals (`seqEmptyExpr`), which pulled-#1214 now types correctly; the
    `Seq::map`-result (`Sequence nat`) base case keeps the uninterpreted
    `Seq_map_empty` constant + length-0 axiom (Boole has no `Sequence.empty_nat`
    token, and the reference uses the same workaround).
  - **Gate (`check_working_tests.sh`):** **39 passed · 1 skipped (Strata gap =
    generics) · 7 failed**, no BooleDDM API drift (verus-boogie rebuilds clean).
    The 7 are unchanged: `FindMax` + `demo` + `demo_for` + `demo_while` +
    `demo_while_loop_isolation` (the Strata-side `∃ j :: bound && …select…`
    OOB-guard gap — `collectWFObligations` guards `==>`/`ite` but not `&&`),
    and `crypto_noref` + `mini_c` (pre-existing parse bugs).
- **2026-05-19 all-suites refresh (final)** (Strata pin
  `upstream/main2 @ c4dbccfea`, *with* the small `seq_empty_bool` patch
  plus translator/harness fixes detailed below):
  `45 verify passed · 4 skipped (Sequence) · 1 skipped (Strata gap) ·
  1 known translator bug · 69 verify failures · 0 missing JSON ·
  4 ignored (skipped per `tests/ignored_tests.txt`) ·
  0 generation failures`.  Total accounted: 124 tests.
  - **Missing JSON is now 0.** The earlier "8 missing JSON" set
    resolved into three buckets: (a) **6 unblocked by appending
    `fn main(){}`** to upstream Verus sources lacking one
    (`verus/examples/{basic_failure,broadcast_proof,exec_termination_example,guide/exec_attr,guide/strings,guide/opaque}.rs`
    — uncommitted local edits to the upstream repo; rustc was rejecting
    these with `E0601: 'main' function not found in crate` before Verus
    could analyze them); (b) **1 unblocked by a harness fix** in
    `tests/run_tests.sh::run_verus_export` that now also looks up the
    underscore-normalized JSON filename (Verus writes
    `proposal_rw2022.json` for `proposal-rw2022.rs` because Rust crate
    names disallow `-`); (c) **2 silenced into the ignored list**
    (`verified_vec.rs`, upstream-marked `ignore` due to deprecated
    `vstd::ptr`; `guide/opaque.rs`, no Verus-mode declarations to
    export).  Plus `trigger_loops.rs` and `broadcast_proof.rs` are now
    also in `tests/ignored_tests.txt` (the former previously caused
    silent all-suites truncations).
  - **`tests/ignored_tests.txt` is now the single source of truth** for
    tests not suitable or valuable to run regression on
    (`UPSTREAM-IGNORE`, `EMPTY-EXPORT`, `HANG` categories).  Active
    entries: `verified_vec`, `trigger_loops`, `guide/opaque`,
    `broadcast_proof`.  The list is consulted by `is_ignored_test` in
    `tests/lib/boole_verify.sh` (shared between
    `check_working_tests.sh` and `regress_examples.sh`).  The legacy
    `is_expected_empty_export_target` was retired.
  - **One small local Strata patch is back** (the "patch-free" claim
    above is now nuanced): `seq_empty_bool` was added 2026-05-19 to
    Strata `Grammar.lean` (1 line: `fn seq_empty_bool () : Sequence
    bool => "Sequence.empty_bool";`) and `Verify.lean` (1-token
    addition to the `.seq_empty_*` arm).  Paired with
    `VerusLean/VLIR/Boole/Inference.lean::seqEmptyTokenName` gaining
    `| .Bool => "Sequence.empty_bool"`.  This typed 6 of 11 untyped
    `Sequence.empty` references in `verus-examples:assert_by_compute`
    and flipped `adopted_rust_verify_test:seqs` from `skip_sequence`
    into a real `FAIL` exposing the polymorphic-`T` issue tracked under
    `[VERIFY-sequence-empty-polymorphic]`.
  - **The 69 verify failures** are largely the previously-documented
    "not faithful" set (`[TRANS-coercion-uninterpreted]`,
    `[VERIFY-lambda-encoding]`, `[VERIFY-generic-typevar-ddm]`,
    `[VERIFY-sequence-empty-polymorphic]`, ghost/tracked scaffolding,
    parametric-datatype tester SMT bug, lex-decreases collapse, etc.)
    plus the 4 previously-export-blocked tests that now reach Stage 3
    and surface their real (pre-existing) verification failures — see
    per-test entries below.
- Upstream Strata HEAD: `2e055ab09` (`strata-org/Strata` main as of 2026-04-30).
  Local Strata working tree adds the for-loop `measure` clause, mutual-recursion
  sibling-bvar fix, and datatype-decl symbol registration on top.
- **2026-05-07 update — Strata pin advanced** to `kondylidou/pr/benchmarks`
  head `c33cfbe25` (= `boole-pr1075-rebased` after fast-forward).
  The PR branch supersedes the original three local patches:
  `for_to_by_statement` / `for_down_to_by_statement` now carry
  `decr : Option Measure` upstream (the for-loop measure patch is
  landed); the mutual-recursion sibling-bvar and datatype-symbol patches
  need re-verification before being re-applied.  Three new local patches
  are maintained on top of the new tip: (a) `body:0` precedence on the
  three for-loop body productions in `Boole/Grammar.lean`;
  (b) `bvDefaultOpName` consolidation in `Boole/Verify.lean` extending
  the BV-unsigned-default rewrite to `Mod`/`Div` (was comparison-only)
  and applying it from `toCoreTypedUn` as well as `toCoreTypedBin`;
  (c) `bvsdiv` / `bvsmod` arms in `toCoreExpr`.  See
  `docs/boole-translation-todo.md` (local) for full diff details.
  **Superseded 2026-05-18 (see below):** patches (b) and (c) are now
  in upstream HEAD (the int-termination / `main2` merge absorbed
  equivalent `Div`/`Mod`→`UDiv`/`UMod` in `toBvCmpOp` and the
  `bvsdiv`/`bvsmod`→`SDiv`/`SMod` arms).  The local `Verify.lean`
  diff has been dropped as redundant — only the no-op `toCoreTypedUn`
  unary-path routing was unique to it, and `toCoreTypedUn` is only
  ever called with `"Neg"` (which `toBvCmpOp` passes through
  unchanged), so the working tree is now pristine upstream with
  identical translation behavior.
- **2026-05-18 update — Strata pin advanced** to `kondylidou/pr/benchmarks`
  head `4f3b68d64` (= `boole-pr1075-rebased` after fast-forward).  This
  tip incorporates merged upstream PR #1167 *"Add int-valued recursion
  with termination checking"* (`strata-org/Strata`, commit `25f254373`)
  plus `a4056242a` ("changes after int-termination merged") and an
  `upstream/main2` merge.  **int-valued termination checking is now live
  on the Strata side**: `decreases <int expr>` is accepted as an
  alternative to `@[cases]` (the refusal wording is now "requires a
  'decreases' clause **or** a '@[cases]' parameter"), int-recursive
  functions become pure UFs with non-negativity + strict-decrease
  obligations per call site, and compound single measures (`decreases m
  + n`) are supported.  Mixed structural/int-valued mutual blocks are
  rejected upstream; lexicographic *tuple* measures are still
  unsupported.  Pristine upstream Strata (no local `Verify.lean`
  patch — see the 2026-05-07 supersession note above) rebuilds
  cleanly (`lake build`, 584 jobs).
  - **Translator gap CLOSED.** Root cause was *not* the parser:
    `SpecFn.fromJson` parses `SpecFn.decreases` correctly, but
    mutually-recursive spec fns arrive inside a Verus `DeclType:
    "Mutual"` block and take the `.mutualBlock` arm of
    `VerusLean/VLIR/Boole/Translate.lean`, which **hardcoded `(ann
    none)`** for the measure slot (the solo-fn `specFnToBoole` path
    threaded it; the mutual path did not).  Fix: thread `decrAnn` via
    `decreasesToMeasureAnn` inside the mutual loop's input-bound scope,
    mirroring `specFnToBoole`.  Regenerated Boole now emits `rec
    function is_odd … decreases abs(i)` and Strata generates + checks
    `*_terminates_*` obligations.
  - **Pull-induced build break fixed.** Upstream `dc7a029ae` removed
    unlabeled `exit` from the Boole DDM; `Builder.lean::exitStmt` lost
    its dead `none` branch and now takes a non-optional label (the only
    caller already rejected the unlabeled case).
  - **Per-case outcomes (int-termination enforced):**
    - `vlir-tests:mutual_recursion` — **termination-clean**: all
      `is_even_terminates_*` pass.  Residual `even_odd_mod2_ensures_*`
      failures are *expected*: PR #1167 models int-recursive fns as
      pure UFs with no definitional axiom, so the solver cannot
      discharge the inductive `is_even(i) <==> i%2==0` ensures.  Strata
      encoding tradeoff, not a translator defect; translation is
      source-close.
    - `vlir-tests:recursion`, `verus-examples:guide__recursion` —
      decreases now emitted, but `M_is_odd_terminates_1` fails: source
      uses a *lexicographic* measure (`decreases abs(i), 0int`) to
      break the same-argument `M_is_odd(i) → M_is_even(i)` edge; the
      translator collapses lex-decreases to the head term, so that
      edge has no strict decrease and #1167's per-call-site
      strict-decrease obligation fails.  Pre-existing lex-collapse
      limitation, *exposed* (not caused) by enforced int-termination;
      full fix waits on Strata tuple-measure support.
  - **Collateral pull regressions (NOT from the two edits above; NOT
    from int-termination).**  `check_working_tests.sh` on the new pin
    reports 13 verify regressions.  3 are the recursion family above
    (intended reclassification: were `skip_gap`, now generate real
    obligations).  The rest trace to **two local Strata patches the
    pull dropped** (the pin note flagged both as "need re-verification
    before being re-applied" but they were not carried forward):
    `datatype-symbol-registration` and `mutual-rec sibling-bvar`.
    Confirmed: `verus-examples:structural` /
    `verus-examples:adts_eq` fail Strata typecheck with `No free
    variables are allowed here! Free Variables: [car_ctor]` — the
    exact signature documented in
    `strata-datatype-symbol-registration-pr-draft.md`
    (`registerCommandSymbols` emits one symbol per datatype decl
    instead of one per constructor/tester/destructor).  The remaining
    broad cases (`quantifiers`, `external`, `generics`,
    `bitvector_basic`, `statements`, `syntax_attr`, `integer_ring`,
    `LoopSimpleWithSpec`) are solver/obligation-level shifts from the
    pull (Provenance/metadata migration, int-recursion UF encoding,
    obligation-ID renumbering) and need separate triage.
  - **2026-05-18 — `datatype-symbol-registration` patch re-applied**
    (local Strata, `Verify.lean::registerCommandSymbols` +
    `registerDatatypeDecl` helper; verbatim from
    `fix-datatype-symbol-registration @ 5d10b290d`, adapted past the
    new `boole_procedure` arm; Strata rebuilds clean, 584 jobs).
    Result (gate re-run, confirmed): **30→35 passed, known
    translator bugs 3→1, regressions 13→10, zero new breakage** (the
    10 are a strict subset of the original 13).
    `verus-examples:structural` ✅ and `verus-examples:adts_eq` ✅
    fully recovered (the two the draft predicted); 2 further
    datatype-using cases flipped out of the "known translator bug"
    bucket to pass; `verus-examples:syntax_attr` dropped off the
    regression list (its remaining SMT `Parse Error: matching failed
    for tester argument of parameterized datatype` on `*_terminates_*`
    obligations is a *separate, independent* parameterized-datatype
    tester SMT-encoding bug, unmasked — not caused — by the fix, and
    classified by the gate as non-regression).  The
    `mutual-rec sibling-bvar` patch was **not** needed for any of the
    13 — no case showed `Unknown bound variable with index`.
  - **Per-obligation triage of the 7 remaining (b) cases — COMPLETE.
    Verdict: zero genuine new functional regressions from the pull.**
    Each fails on exactly the obligation(s) its *pre-existing*
    `differential_status` entry already documents, with an unchanged
    Boole translation:
    - `quantifiers` — `assert_15/17`, the `nat_to_int` universal
      (`[TRANS-coercion-uninterpreted]`, this file's entry).
    - `statements` — `entry_invariant_0_0`, the `bv8_to_bv64_u`
      loop invariant (`[TRANS-coercion-uninterpreted]`).
    - `bitvector_basic` — `bitvector_query`/`compute`
      (`[TRANS-coercion-uninterpreted]` on `bv8_to_*`).
    - `generics` — `🚨 SMT Encoding Error! Unimplemented encoding for
      type var $__ty*` (`[VERIFY-generic-typevar-ddm]`).
    - `external`, `integer_ring`, `LoopSimpleWithSpec` — pre-
      documented intentional / not-faithful baselines
      (`bv64_to_int_u` uninterpreted; intentional `type_fail` +
      cvc5 `wide_mul` timeout; `bvslt`/`bvsle` dispatch baseline).
    These surface as gate "regressions" only because the
    Provenance-migration obligation-ID renumbering breaks
    `boole_verify.sh`'s brittle expected-fail matching and the
    classifier now counts the documented coercion-fail as `fail`
    rather than tolerating it.  Final tally of the original 13:
    3 intended int-termination reclassification · 3 recovered by the
    datatype patch (+`syntax_attr` partial) · 7 gate-accounting on
    pre-documented not-faithful baselines · 0 genuine new functional
    regressions.
  - **2026-05-18 — test-harness hygiene applied.**
    `check_working_tests.sh::expected_fail_pattern_for_target` now
    whitelists the documented failing obligations for the 10
    expected-fail cases (7 pre-documented not-faithful + 3 intended
    int-termination reclassification), keyed on **stable obligation
    prefixes** (semantic name or `<name>_<idx>_`), never the volatile
    Provenance `_<serial>` that pin bumps renumber.  A header note in
    `working_tests.txt` records why these stay in the curated list
    (generation + Boole-shape coverage).  This makes the gate a
    meaningful zero-noise signal again while still surfacing any
    genuinely new failing obligation (different prefix).
- **2026-05-19 update — Strata pin switched to `upstream/main2`**;
  left the `kondylidou/pr/benchmarks` line entirely.  HEAD now at
  `c4dbccfea Boole language extensions for dalek-lite benchmarks
  (#1075)` (strata-org/Strata `main2`).  This trunk now contains every
  feature we'd been integrating piecemeal: PR #1075 (Boole language
  extensions), int-valued termination checking (#1167), and
  `fix/datatype-tester-freevar`'s `getFVarIsOp` rework that supersedes
  our `registerCommandSymbols` patch.  **Consequence — zero local
  Strata patches required at that moment.**  The datatype-symbol-
  registration patch is content-superseded (different mechanism, same
  effect, plus a `getFVarIsOp_spec` theorem).  The earlier BV patch
  was already dropped as redundant.  **(Later that day, 2026-05-19, a
  small new local patch — `seq_empty_bool` in `Grammar.lean` +
  `Verify.lean` — was added; see the 2026-05-19 all-suites refresh
  entry at the top of this file.)**  Regression gate against `main2`
  clean:
  **45 passed, 0 failed, 1 Sequence-skip, 1 known-bug** — identical
  to the previous 45/0 baselines on `boole-pr1075-rebased + datatype
  patch` and on `pr/casts-pre-nat`, but without any local Strata
  changes.  Local Strata branches consolidated 12 → 4:
  `main2` (current trunk), `pr/casts` (post-nat-synonym tracker, gate
  drops to 14/11), `pr/casts-pre-nat @ 832eeab09` (frozen snapshot
  before the regression-causing nat-synonym pull), and
  `add-bv-operator-lowering` (status unclear, keep-pending-review).
  All obsolete branches reflog-recoverable for ~30 days
  (`fix-datatype-symbol-registration @ 5d10b290d`,
  `boole-pr1075 @ 7de89b75b`, `boole-pr1075-rebased @ 4f3b68d64`,
  `add-for-loop-measure-clause @ 270aa0eb4`,
  `fix-recursive-function-bvar @ f43d1f51d`,
  `local-boole-patches @ 9145e84d1`,
  `fix-constructor-binding-parens @ 5119b1da8`,
  `fix-decllist-binding-parens @ 13cd14193`).
  `strata-datatype-symbol-registration-pr-draft.md` deleted (moot).
- Boole output (primary):
  - `verus-lean` emits Boole as the primary output. The intended artifact to
    inspect for any test is `tests/BoolePrograms/.../*.lean`; raw
    `tests/BoogieFiles/.../*.core.st` is kept for Core-pipeline regression
    tracking only.
  - Boole `for` loops are reconstructed for simple range-iterator patterns
    (e.g. `vlir-tests:demo_for`).
  - current Verus range-loop support is unit-step only:
    `for ... step_by(...)` is rejected before JSON export, so recovered Boole
    `for` loops are emitted as plain `for ... to ...` loops with implicit step 1.
  - `vlir-tests:demo_for` elaborates cleanly in Strata as Boole output.
  - targeted `for`-loop cases still blocked by non-`for` issues:
    `verus-examples:recursion` (`int`/`bv64` mismatch),
    `verus-examples:set_from_vec`, `verus-examples:mergesort`,
    `verus-examples:guide/exec_attr` (`Unit` / loop-helper artifacts in the
    current Core-shaped lowering),
    `verus-examples:vectors` (`datatype Vec` path is now source-close; the
    remaining issues are `[VERIFY-lambda-encoding]`,
    `[TRANS-extensional-eq]`, plus `Unit` / loop-helper artifacts in the
    reverse examples),
    `verus-examples:exec_termination_example` (residual iterator/ghost state),
    `verus-examples:guide/invariants` (`bv64` where `int` expected)
  - the raw summary below is still based on Core output plus `strata verify`

## Boole Regression Summary (base full run `20260430_204358` plus mirrored tests)
Tests in regression and classified in this doc: **122**.
`regress_examples.sh --all-suites` scans `tests/VerusFiles/`,
`tests/adopted_rust_verify_test/`, `verus/examples/`, and
`verus/examples/guide/` at `find -maxdepth 1`.

Bucket totals: 16 (faithful and same) + 48 (faithful but different) +
58 (not faithful) = **122**, matching the regression test count.

Classification rule (faithfulness-first): a test is placed in a bucket by
asking, in order, (1) is the emitted Boole faithful to the source — i.e. it
does not drop or change important semantics — and only if yes, (2) does
the Strata verification outcome agree with the Verus outcome. A test with a
faithfulness gap stays in bucket 3 even when Strata happens to verify it
(e.g. `verus-examples:modules`, where `[TRANS-closed-visibility]` makes the
translation unfaithful regardless of solver result).

Personal scratch tests under `tests/scratch/` (e.g. `crypto*.rs`) live in
`.git/info/exclude` and are intentionally not part of the regression count
or this doc.

Primary verify statuses from the **base regression run `20260430_204358`**
(historical) plus the two mirrored `vlir-tests` entries above (sum to 122).
**See the 2026-05-19 all-suites refresh at the top of "Data Sources" for
current `main2`-pin numbers (45/4/1/1/69/0-missing/4-ignored on 124 tests)**;
the breakdown below is kept for the historical baseline only:
- generation failures: 0
- missing json: 8
- verify passed: 17
- verify skipped (Sequence): 18
- verify skipped (Strata gap): 24
- known translator bugs: 2
- verify failures: 53

Notes:
- "Generation failures" is now 0: every test in the suite produces emitted Boole.
  Faithfulness review of the emitted output is therefore the relevant audit
  axis (rather than translate-stage failures).
- "Verify failures" includes obligation-level failures, which mix solver
  incompleteness with downstream gaps. Faithfulness audit is independent of
  these counts.

## Translation Quality Labels
- `faithful and same as Verus output`: translation is faithful and Strata verification outcome matches Verus.
- `faithful but different from Verus output`: translation is faithful, but Verus/Strata outcomes differ or Strata lacks support.
- `not faithful translation`: translation currently drops/changes important semantics compared to source-level intent.
- Manual labels below are **Boole-first**: the primary artifact for review is
  `tests/BoolePrograms/.../*.lean`. Raw Core (`tests/BoogieFiles/.../*.core.st`)
  is kept as a regression artifact but no longer the canonical output for
  judging translation quality.
- Repeated issues are keyed by gap IDs from the `Gap Index` section below.
  Some gaps are tagged `(Core-only)` when they describe a Core-pipeline-only
  issue that the Boole pipeline already resolves; those are kept for raw-Core
  regression tracking but should not affect the Boole-side judgment.

## Translation Conventions
General translator-side conventions that affect every test's emitted output.
Each is semantically faithful (preserves verification meaning) but may differ
syntactically from the source — listed here so per-test entries don't have
to repeat them.

- **`let` vs `let mut`**: Boole has no immutable-binding form, so Rust's
  `let` vs `let mut` distinction collapses to a uniformly mutable `var`
  declaration in all Boole output.
- **Statement-position vs expression-position `let`**: statement-position
  `let x = e; ...` lowers structurally to `var x; x := e; ...`, but
  expression-position `let x = e; body` (e.g. `assert({ let x = ...; cond })`)
  is inlined via substitution rather than preserved as a binding form. The
  Boole `let_in_expr` AST exists but its current lowering substitutes the value
  into the body. If Strata Boole later grows expression-level `let` syntax with
  a non-substituting lowering, the translator could be retargeted at the
  dispatch site in `Verify.lean:toCoreExpr`.
- **Negative integer literals** are encoded as `0 - n` (Boole has no
  negative-integer literal syntax).
- **Repeated quantifier binders** with the same names across sibling
  quantifiers are alpha-renamed (`i, j` → `i_0, j_0`).
- **`#[verifier::external_body]` procedures** are emitted with their spec
  preserved and a body of `assume false;` (not strictly an empty body). This
  makes the procedure verify vacuously, modeling "trust the spec, skip body
  verification." Tests exhibiting this pattern include `assorted_demo:gcd`,
  `guide__overflow:Num_checked_add`,
  `guide__requires_ensures:print_two_digit_number`, and `bitvector_basic:main`.
- **Struct/enum naming**: type names are lowercased in the emitted datatype
  identifier (`Point` → `point`, `Sport` → `sport`); constructor names are
  prefixed with the type name (`Soccer` → `sport_Soccer`).
- **Field/variant accessor syntax**: field accessors use `tyname..field(obj)`;
  constructor-test predicates use `tyname..is<ctor>(obj)`.

## Best Available Output Notes
- `vlir-tests:demo`, `vlir-tests:demo_for`: best current output is Boole, which
  elaborates cleanly in Strata and recovers the source-level `for` loop shape.
  The raw Core run still fails earlier on lingering `Tuple_ctor_0` / `Unit`
  artifacts.
- `vlir-tests:mutual_recursion`, `vlir-tests:recursion`: best current output is
  Boole, which elaborates cleanly. The raw Core run is still blocked by
  Strata's current `@[cases]` requirement for recursion over datatypes.
- `verus-examples:recursion`, `verus-examples:guide/recursion`: Boole now
  recovers the loop structure where relevant, but the overall best current
  condition is still not faithful because `[TRANS-reveal-with-fuel]` still
  changes the source-level behavior.

## faithful and same as Verus output (16)
- `verus-examples:adts_eq`
- `verus-examples:assertions` (fail as expected)
- `verus-examples:debug` (fail as expected)
- `verus-examples:fun_ext`
- `verus-examples:guide/calc`
- `verus-examples:guide/datatypes`
- `verus-examples:guide/equality`
- `verus-examples:guide/getting_started`
- `verus-examples:imo_1988_6`
- `verus-examples:structural`
- `vlir-tests:basic_failure` (fail as expected)
- `vlir-tests:binder_cast_regressions`
- `vlir-tests:by_lean` (fail as expected)
- `vlir-tests:matching`
- `vlir-tests:test_opaque_reveal` (opaque function declaration-only + reveal as assume)
- `vlir-tests:test_specfn`

## faithful but different from Verus output (48)
- `verus-examples:adts` (datatypes, variant checks, structural equality; `matches` clauses correctly desugar to `..is<ctor>(o) && ..field(o) == val` form)
- `verus-examples:assorted_demo` (`#[verifier::external]` fn dropped from translation entirely; `external_body` follows the standard `assume false;` convention)
- `verus-examples:basic_failure` (translation is source-close; the test's `external_span(s: Seq<nat>)` proof procedure lowers to `procedure external_span (s : Sequence nat)` and is blocked by Strata's current Sequence frontend/indexing support. **2026-05-19:** previously missing-JSON because the upstream `.rs` lacks `fn main()`; the local `fn main(){}` source edit (uncommitted, in `verus/examples/basic_failure.rs`) unblocks Verus export so the file now reaches Stage 3 and surfaces this pre-existing Sequence-frontend failure rather than hiding behind `E0601`)
- `verus-examples:bitvector_basic` (`[TRANS-coercion-uninterpreted]` blocks several `bitvector_query` / `compute` obligations that depend on `bv8_to_bv16_u`, `bv8_to_bv32_s`, `bv8_to_int_u`, `bv8_to_int_s`. **2026-06-01:** #1217 native casts make these interpreted — `compute`/`assert_32` now verify; only `bitvector_query` remains (cvc5-hard, times out): 42✅/1⌛)
- `verus-examples:bitvector_equivalence` (bitvector proofs with triggers and decreases; cvc5 times out on the `equivalence_proof_bv` ensures — large bit-blasted query)
- `verus-examples:broadcast_proof` (translation uses Sequence prelude faithfully. **2026-05-19:** moved to `tests/ignored_tests.txt` as `EMPTY-EXPORT` — the source is `broadcast use`-only with no top-level Verus-mode declarations, so Verus reports `verified` but emits no JSON. Skipped silently rather than counted as missing-JSON. The historical Sequence-frontend blocker is moot because Stage 1 never produces output)
- `verus-examples:calc` (`calc!` steps lower to explicit assertion chains; the remaining mismatch is Strata's current `Sequence` frontend/indexing support plus nat/bv64 typing in the sequence-extensionality steps)
- `verus-examples:cells` (translation is source-close; the current difference is the missing `Cell` model type in Strata)
- `verus-examples:generics` (`[TRANS-generic-reveal]`; `[VERIFY-generic-typevar-ddm]` raises SMT encoding errors on type-var-using obligations, and downstream asserts depending on those obligations also fail. **2026-06-01:** post-#1217 the type-var cast surfaces as a Strata *elaboration* error (`as_int` on a `tvar`) rather than an SMT encoding error; reclassified `skip_gap` — non-monomorphized generics, the fix is Strata-side monomorphization)
- `verus-examples:guide/integers` (`[TRANS-coercion-uninterpreted]`: widening casts emit uninterpreted coercions like `bv8_to_bv16_u`, `bv16_to_int_u`, `int_to_bv8_u`; cvc5 cannot reason through these)
- `verus-examples:guide/interior_mutability` (translation is source-close; the current difference is the missing `Cell` model type in Strata)
- `verus-examples:guide/modes` (`Tuple` type declared by translator when referenced; `[TRANS-coercion-uninterpreted]` in mixed `nat`/`bv8`/`int` arithmetic — uninterpreted `nat_to_int` and `bv8_to_int_u` block obligations like `bv8_to_int_u(u) < i && i < nat_to_int(n)`)
- `verus-examples:guide/nonlinear_bitvec` (translation faithful: `[bitvector_query]`/`[nonlinear_query]`/`[compute]` proof-mode labels emitted; `[TRANS-trigger-annotation]` strips `#[trigger]` annotations on De-Morgan quantifiers but preserves logical content. Verify SKIP — Strata-side dispatch for the proof-mode labels is incomplete on this case)
- `verus-examples:guide/opaque` (faithful empty Boole export: source `pub open spec fn` opaque-with-`reveal_with_fuel` declarations have no exec procedures to verify. **2026-05-19:** moved to `tests/ignored_tests.txt` as `EMPTY-EXPORT`. Even after appending `fn main(){}` to the source, Verus reports `0 verified, 0 errors` and emits no JSON because there are no Verus-mode declarations to serialize — consistent with the historical "nothing for Strata to discharge" classification)
- `verus-examples:guide/overflow` (`[MODEL-missing-types]`: `Arithmetic_overflow` not modelled in Strata; `Num_checked_add` lowers to a procedure with `assume false;` body per the external-body convention)
- `verus-examples:guide/references` (`[TRANS-coercion-uninterpreted]` in the loop's `decreases bv32_to_int_u(b_out)` — Strata cannot discharge the decrement because `bv32_to_int_u` has no body; immutable/mutable references erase to plain values, which is verification-equivalent)
- `verus-examples:guide/requires_ensures_edit` (source `i8` with signed comparisons `-16 <= x1 < 16` lowers to `<=s`/`<s` (`bvsle`/`bvslt`) Boole AST — blocked by Strata Verify lacking dispatch arms for these signed-bv-comparison constructors; tracked in the strata-bv-lowering issue draft)
- `verus-examples:guide/requires_ensures` (same signed-bv-comparison gap as `requires_ensures_edit`; `print_two_digit_number` is `external_body` and follows the `assume false;` convention)
- `verus-examples:guide/strings` (translation is source-close; the current difference is the missing `String_string` / string-library model support in Strata. **2026-05-19:** previously missing-JSON because the upstream `.rs` lacks `fn main()`; the local `fn main(){}` source edit (uncommitted, in `verus/examples/guide/strings.rs`) unblocks Verus export — Stage 1 now reports `5 verified, 0 errors` — and Stage 3 surfaces the documented `Expression has type String_string when string expected` failure)
- `verus-examples:impl_basic` (structs, methods, generics, ensures clauses preserved)
- `verus-examples:nevd_script` (`[TRANS-coercion-uninterpreted]`: `nat`-typed parameters and `nat_to_int`-coerced bodies (e.g. `rec function fibo (n : nat) : nat` with `if nat_to_int(n) == 0 then 0 else ...`); int literals in the body trigger `int`-where-`nat`-expected typecheck errors)
- `verus-examples:overflow` (`[MODEL-missing-types]`: `Arithmetic_overflow` not modelled in Strata; the translator preserves source-level checked-overflow operations like `checked_u64_constants`/`checked_u64_calculations` and emits `var w : Arithmetic_overflow` parameters that Strata cannot resolve)
- `verus-examples:power_of_2` (Strata type error: `int` literals where `nat` expected)
- `verus-examples:prelude` (`seq!` now lowers through `Sequence.empty`/`Sequence.build`; the remaining mismatch is Strata's current `Sequence` frontend/indexing support)
- `verus-examples:proposal-rw2022` (`[TRANS-coercion-uninterpreted]` in `rec function fibo (n : nat) : nat` body and the `bv64_to_int_u(result) == nat_to_int(fibo(bv64_to_nat_u(n)))` ensures clause; termination-check artifacts (`decrease%init*`, `CheckDecrease*`) correctly stripped from translation. **2026-05-19:** previously misclassified as missing-JSON due to a harness path bug — Verus writes `proposal_rw2022.json` (underscored crate name, since Rust forbids `-`), but the harness's `${base}.json` lookup retained the hyphen. Fixed in `run_tests.sh::run_verus_export` by also trying the underscore-normalized filename; the test now reaches Stage 3 and surfaces the documented coercion gap)
- `verus-examples:quantifiers` (typing now flows through via `nat_to_int` coercion; the universal `∀ i : nat :: nat_to_int(i) >= 0 && ...` fails because `nat_to_int` is declared without a body, so cvc5 cannot prove `nat_to_int(i) >= 0` — `[TRANS-coercion-uninterpreted]`)
- `verus-examples:recursive_types` (translation appears source-close; Strata-side blocker is nested datatype shape unsupported in current Strata typechecker)
- `verus-examples:rw2022_script` (`[TRANS-coercion-uninterpreted]`: `is_prime` and `fibo` use `nat` arithmetic via uninterpreted `nat_to_int`; prime-testing quantifier/trigger structure preserved, `rec function fibo` with implicit decreases preserved)
- `verus-examples:statements` (mixed-width bitvector arithmetic with explicit width extension; `[TRANS-coercion-uninterpreted]` causes the `b1 == i * 2` loop entry-invariant to fail — `bv8_to_bv64_u(b1)` is uninterpreted so cvc5 can't establish the relation. **2026-06-01:** RESOLVED by #1217 — native `as_int`/`as_bv` make the widening interpreted, the loop invariant discharges; 23✅ (only ⌛ `measure_decrease_0`, a hard nonlinear measure))
- `verus-examples:test` (translation faithful: small bv64 procedure `foo` with `requires a < bv{64}(100)` and `_pct_return := a + bv{64}(1)`, plus a `main` that exercises it. Verify SKIP — Strata-side dispatch gap on this shape, no translator defect)
- `verus-examples:trigger_loops` (uninterpreted fns + multi-trigger quantifier patterns preserved; `[TRANS-choose]`: source `choose|z| g(z)` in `choose_example`/`quantifier_example` is parsed as `Bind.Lambda [z]` with the predicate erased. **2026-05-19:** moved to `tests/ignored_tests.txt` as `UPSTREAM-IGNORE + HANG` — file is upstream-marked `ignore`, was previously the cause of silent all-suites run truncations; now skipped silently)
- `vlir-tests:crypto_noref` (translation uses `Sequence.empty`/`Sequence.build`. **2026-05-19:** still verify SKIP — the bool fix that added typed `Sequence.empty_bool` did not help here because the remaining bare `Sequence.empty` is polymorphic-`T`. Now classified under `[VERIFY-sequence-empty-polymorphic]` (Strata has no `Sequence.empty[A]` for type-variable element types). Also affected by `[VERIFY-lambda-encoding]` for lambdas in `Seq::new`-style spec functions. **2026-06-05:** `[VERIFY-sequence-empty-polymorphic]` resolved — the polymorphic seed now emits as `Sequence.empty<T>()` via the Core `seq_empty<A>()` production (`Bld.seqEmpty` / `seqEmptyExpr` fall back to it for non-concrete element types), and the `Sequence.empty` parse error is gone. crypto_noref still FAILs verify, now solely on the generic tuple selectors: `Tuple.._0/._1` type as the uninstantiated `T0`/`T1`, so `Tuple.._0(kv) ^ Tuple.._1(kv)` in `encrypt_spec`/`decrypt_spec` is rejected (`crypto_noref.lean:68: Expression has type T1 when T0 expected`) — the malformed-tuple-projection issue also seen at `vlir-tests:mini_c`)
- `vlir-tests:datatypes` (current difference is only that Strata still type-fails later in the pipeline)
- `vlir-tests:demo_for` (verify SKIP (Sequence): Boole output recovers the source-level `for` loop shape; blocked by Strata's Sequence frontend/indexing support)
- `vlir-tests:demo_while_loop_isolation` (`Vec<u64>` find-max with explicit `loop_isolation` enabled; loop-index uses now lower through `[TRANS-loop-counter-int]`, so indexing is expressed directly over `Sequence.length`/`Sequence.select`; structurally identical to `demo_while`)
- `vlir-tests:demo_while` (`Vec<u64>` find-max with `#[verifier::loop_isolation(false)]`; loop-index uses now lower through `[TRANS-loop-counter-int]`, so indexing is expressed directly over `Sequence.length`/`Sequence.select`)
- `vlir-tests:demo` (verify SKIP (Sequence): Boole output is source-close and elaborates cleanly; blocked by Strata's Sequence frontend/indexing support)
- `vlir-tests:FindMax` (`Vec<i32>` find-max via `Sequence bv32`; loop-index uses now lower through `[TRANS-loop-counter-int]`; value comparisons remain signed bv32 comparisons such as `>=s`)
- `vlir-tests:integer_ring` (Strata type error on intentionally-failing `type_fail`; cvc5 also times out on `wide_mul` ensures — non-linear bv64 multiplication beyond solver default budget)
- `vlir-tests:LoopSimple` (`i32` summation loop; `[TRANS-coercion-uninterpreted]` in `decreases bv32_to_int_s(n - i)`; signed comparisons `<s`/`<=s` use `bvslt`/`bvsle` Boole AST nodes that lack dispatch arms in Strata Verify (per the strata-bv-lowering issue draft); intentionally fails as a stable verify-mismatch baseline)
- `vlir-tests:mutual_recursion` (Boole output is a source-close `rec function is_odd ... function is_even ...` block. **2026-05-18 (resolved):** the `.mutualBlock` Boole-translation arm now threads the source `decreases abs(i)` measure (was hardcoded `(ann none)`); regenerated Boole emits `rec function is_odd … decreases abs(i)` and Strata's int-termination checker passes all `is_even_terminates_*` obligations.  Translation faithful and termination-clean.  The only residual `even_odd_mod2_ensures_*` failures are an *expected Strata encoding limitation*: int-recursive fns are pure UFs with no definitional axiom, so the solver cannot prove the inductive `is_even(i) <==> i%2==0` ensures — not a translator defect)
- `vlir-tests:nonlinear` (`[TRANS-coercion-uninterpreted]`: `nat`-typed nonlinear obligations like `bv32_to_int_u(x) * bv32_to_int_u(z) <= nat_to_int(65535 * 65535)` and `nat_to_int(x * x + x) == nat_to_int(x * (x + 1))` go through uninterpreted `nat_to_int`/`bv32_to_int_u` that cvc5 cannot reason through; same flavor as `nevd_script`)
- `vlir-tests:proof_fn` (translation faithful: `function p (u : bv64) : bool` and `function min (x : int, y : int) : int` declared with bodies, lemma-style procedures lower to spec-only `procedure ... ensures ... { exit ... }` shape. Verify SKIP — Strata-side dispatch gap, no translator defect)
- `vlir-tests:quant` (mixed `int`/`nat` quantifier patterns like `∀ x : int, y : nat :: x + y == y + x` produce direct `+` on mismatched types that Strata's typechecker rejects; also affected by `[TRANS-trigger-annotation]` (source `#[trigger]` annotations stripped) and `[TRANS-assert-label]` (source `as a1`/`a2`/`a3` labels dropped))
- `vlir-tests:recursion` (Boole-side translation faithful.  **2026-05-18:** the mutual-block decreases fix lands here too — `rec function M_is_odd … decreases M_abs(i)` is now emitted and most `*_terminates_*` obligations pass.  Residual `M_is_odd_terminates_1` fails: source uses a *lexicographic* measure (`decreases abs(i), 0int`) to break the same-argument `M_is_odd(i) → M_is_even(i)` edge, but the translator collapses lex-decreases to the head term, leaving that edge with no strict decrease under #1167's per-call-site obligation.  Pre-existing lex-collapse limitation exposed by enforced int-termination; full fix waits on Strata tuple-measure support.  Same applies to `verus-examples:guide__recursion`)
- `vlir-tests:rec_adt_structural` (nat emitted as abstract type via `[MODEL-missing-types]`; waiting for Strata native nat support)
- `vlir-tests:test_requires` (translation faithful: `[bitvector_query]` and `[nonlinear_query]` proof-mode labels preserved on the `test_success` and `bound_check` assertions. Verify SKIP — Strata-side dispatch for these proof-mode labels is incomplete on this case, mirroring `guide/nonlinear_bitvec`)
- `vlir-tests:vec_ops` (verify SKIP (Sequence): Vec operations lower through Sequence prelude; blocked by Strata's Sequence frontend/indexing support)

## not faithful translation (58)
- `verus-examples:assert_by_compute` (`[VERIFY-lambda-encoding]` for lambdas in `Seq::new`-style spec functions; `[TRANS-coercion-uninterpreted]` for `nat_to_int(Fib_fib(...))` and friends; `assert(...) by (compute_only)` lowers to `assume <pre-computed-result>;` directly. `Compute_all_spec` stubs surface in `guide__assert_by_compute`, not here. **2026-05-19:** 6 of 11 originally-untyped `Sequence.empty` references now correctly emit `Sequence.empty_bool` (the `bits_of_int` family) after the bool patch; the remaining 5 are polymorphic-`T` in `Sequences_reverse<T>` / `Sequences_compute_seq_symbolic<T>` and still skip under `[VERIFY-sequence-empty-polymorphic]`)
- `verus-examples:atomics` (`[TRANS-atomic-ghost-scaffolding]`: `struct_with_invariants!` / `atomic_with_ghost!` still lower to low-level `Invariant_*`, `Atomic_*`, and `assume` scaffolding; `[MODEL-missing-types]` (`Atomic_ghost`))
- `verus-examples:basic_lock1` (`[TRANS-atomic-ghost-scaffolding]`: `InvariantPredicate` impl + `open_local_invariant!` lower to `Invariant_*`/`Atomic_*`/`Cell_*` helper scaffolding; `[MODEL-missing-types]` — `Atomic`, `Cell`, `Invariant`)
- `verus-examples:basic_lock2` (`[TRANS-atomic-ghost-scaffolding]`: `struct_with_invariants!` flattens to `Atomic_ghost_*`/`Cell_*` helpers; `[MODEL-missing-types]` — `Atomic_ghost`, `PCell`)
- `verus-examples:bitmap` (`[VERIFY-lambda-encoding]` in `u64_view`; `[TRANS-extensional-eq]` still expands source `=~=` and `assert_seqs_equal!`. The `BitMap` API (`view`, `from`, `get_bit`, `set_bit`, `or`) is now emitted as `Impl__0_view`/`Impl__0_from`/`Impl__0_get_bit`/`Impl__0_set_bit`/`Impl__0_or` procedures — the older claim that it was missing is no longer true after recent translator work.)
- `verus-examples:bitvector_garbage_collection` (`[VERIFY-lambda-encoding]` in `bucket_view`; `[TRANS-extensional-eq]` still expands source `=~=` away to explicit formulas; raw Core also currently hits nat/int typing around `Seq_new`)
- `verus-examples:datatypes` (`Box::new(t)` lowers to `call v := Boxed_new(t)` — an external-body identity wrapper procedure (`ensures v == t; { assume false; }`), so semantically identity but syntactically a procedure call rather than literal erasure; `[TRANS-reveal-with-fuel]` discards source `reveal_with_fuel(f, n)` annotations; loop/match lowering not yet source-close enough)
- `verus-examples:debug_expand` (`[TRANS-hide]`, `[TRANS-closed-visibility]`)
- `verus-examples:doubly_linked_xor` (pointer-heavy XOR linked list; `[MODEL-missing-types]` — `Simple_pptr`; `[TRANS-ghost-tracked-erasure]` for `Tracked`/`Ghost` wrappers; `external_body` proof with `unimplemented!()` in source)
- `verus-examples:doubly_linked` (`[MODEL-missing-types]` — `Simple_pptr`, `Raw_ptr`, plus `Doubly_linked_list_node`/`ghostState`/`doublyLinkedList`/`iterator` datatypes; `[TRANS-ghost-tracked-erasure]` for `Tracked`/`Ghost` wrappers; pointer arithmetic and `next`/`prev` chasing not yet source-close)
- `verus-examples:even_cell` (`[TRANS-atomic-ghost-scaffolding]`: `open_local_invariant!` flattened to `Invariant_create_open_invariant_credit`/etc. helpers; `[MODEL-missing-types]` — `Cell`, `LocalInvariant`)
- `verus-examples:exec_termination_example` (source has basic recursive `exec` fns and while loops with `decreases` clauses on bare `int`. **2026-05-18:** verify previously failed on iterator/range desugaring artifacts (`error: Undeclared type or category Ops_Range_range`, `Unknown expr identifier VERUS_iter`) from the `exec_for_loop` arms — orthogonal to `[CORE-decreases]`. **2026-05-19:** also previously missing-JSON because the upstream `.rs` lacks `fn main()`; the local `fn main(){}` source edit (uncommitted, in `verus/examples/exec_termination_example.rs`) unblocks Verus export — Stage 1 now reports `14 verified, 0 errors` — and Stage 3 surfaces the same iterator-lowering gap rather than hiding behind `E0601`)
- `verus-examples:extensionality` (`[TRANS-extensional-eq]` expands `assert_seqs_equal!`, `assert_maps_equal!`, and `assert_sets_equal!` into low-level proof scaffolding and explicit formulas; `[VERIFY-lambda-encoding]` and `[TRANS-higher-order-collection-stubs]` still affect `Map::total`, `Map::new`, and `Set::new`; raw Core also currently hits a Strata-side `Sequence` indexing type error in `are_equal`)
- `verus-examples:external` (`Ghost<int>` erased to plain `int`; `println!` in `external_body` fn not translated; the `s >= n` precondition becomes `s >= bv64_to_int_u(n)` which cvc5 can't prove because `bv64_to_int_u` is uninterpreted — `[TRANS-coercion-uninterpreted]`. **2026-06-01:** RESOLVED by #1217 — `bv64_to_int_u` is now native `e as_int`; verifies, 5✅)
- `verus-examples:float` (`[TRANS-float-unsupported]`: source `f64`/`f32` literals lower to `Unsupported.Float64` placeholders in emitted Boole; floating-point types/operations not yet translated)
- `verus-examples:guide/assert_by_compute` (`range_property` still uses uninterpreted `Compute_all_spec` plus `[VERIFY-lambda-encoding]`; nat/int literal typing still leaks into recursive nat functions such as `pow`. **2026-05-19:** also affected by `[VERIFY-sequence-empty-polymorphic]` — 1 untyped `Sequence.empty` from a polymorphic-`T` context the bool fix can't handle)
- `verus-examples:guide/bst_map_generic` (BST-as-map with generic key/value; emits `Map_empty`, `Map_lib_union_prefer_right`, `Map_insert` cleanly — `[TRANS-fuel-parameter-leakage]` no longer applies here. Remaining gap: classification holds via solver-side reasoning about generic recursive datatypes — `[VERIFY-generic-typevar-ddm]`-adjacent issues likely)
- `verus-examples:guide/bst_map_type_invariant` (BST-as-map with type-invariant constraint; same Map operations emitted cleanly — Fuel-leakage claim was stale; remaining gap is solver-side reasoning about the type invariant under recursive operations)
- `verus-examples:guide/bst_map` (concrete BST-as-map for `u64 -> bool`; emits `Map_empty`, `Map_lib_union_prefer_right`, `Map_insert` and `Impl__0_as_map`/`Impl__0_optional_as_map` accessors cleanly — `[TRANS-fuel-parameter-leakage]` no longer applies. Remaining gap is solver-side reasoning about recursive structural properties)
- `verus-examples:guide/const` (`Layout::size_of` lowers to `Layout_size_of` symbol that is undeclared in the emitted Boole; `[MODEL-missing-types]` for `Layout`; output also relies on the `sorry` axiom, indicating an `assume false`-style fallback)
- `verus-examples:guide/exec_attr` (`test_for_loop` still has `[VERIFY-lambda-encoding]` in the loop invariant; `proof_decl!` / `proof_with!` / `Ghost` / `Tracked` wrappers are flattened under `[TRANS-ghost-tracked-erasure]`. **2026-05-19:** previously missing-JSON because the upstream `.rs` lacks `fn main()`; the local `fn main(){}` source edit (uncommitted, in `verus/examples/guide/exec_attr.rs`) unblocks Verus export — Stage 1 now reports `8 verified, 0 errors`)
- `verus-examples:guide/exec_spec_unverified` (`[TRANS-exec-spec-helper-leakage]`: the `exec_spec_unverified!` example lowers through internal `View_deep_view` / `exec_*` helper stubs and a distorted `Map int execPoint` representation rather than preserving the source macro structure)
- `verus-examples:guide/exec_spec_verified` (`[TRANS-exec-spec-helper-leakage]`: the `exec_spec_verified!` example leaks internal `View_deep_view`, `View_V`, `Contrib_Exec_spec_*`, and slice/array helper stubs instead of source-like `deep_view` / `as_slice` reasoning)
- `verus-examples:guide/external_trait_specs` (`[TRANS-trait-unsupported]`; raw Core also currently hits a bv64/int comparison mismatch in `test_hasher`)
- `verus-examples:guide/ext_equal` (`[VERIFY-lambda-encoding]`; direct `Seq`/`Set`/struct extensionality now lowers to explicit formulas, but raw Core still expands away source `=~=`/`=~~=` syntax. **2026-05-19:** the legacy `[SURFACE-sequence-empty]` reference here is the same issue now tracked as `[VERIFY-sequence-empty-polymorphic]` — 5 polymorphic-`T` `Sequence.empty` references the bool fix can't handle)
- `verus-examples:guide/higher_order_fns` (`[TRANS-exec-closure-scaffolding]`; `[SURFACE-sequence-empty]` in the captured-closure example)
- `verus-examples:guide/invariants` (`[TRANS-extensional-eq]`: source `assert(operations@.take(i as int) =~= ...)` is expanded to plain `==`; `[TRANS-coercion-uninterpreted]` in fib-loop invariants like `bv64_to_int_u(prev) == nat_to_int(fib(i - bv{64}(1)))`)
- `verus-examples:guide/lib_examples` (`[VERIFY-lambda-encoding]` in returned/captured function values and collection constructors; `[SURFACE-sequence-empty]`; the current Vec translation itself is now the datatype-based path)
- `verus-examples:guide/pervasive_example` (current output uses `Sequence.length(s) == 5` cleanly — the older `[TRANS-seq-len-literal-typing]` nat/bv64 mismatch claim no longer applies after recent translator work. Remaining gap is Strata's current `Sequence` frontend/indexing support)
- `verus-examples:guide/quants` (`[TRANS-reveal-with-fuel]`; `[SURFACE-sequence-empty]`. **2026-06-11:** the multi-binder choose-let (`quants.rs:325`) and choose-in-argument (`quants.rs:452`) shapes now emit faithfully — see `[TRANS-choose]` — and the file runs end-to-end: cvc5 129 ✅ / 26 ⌛ / 0 ❌, previously failed elaboration on the unbound choose binders)
- `verus-examples:guide/recursion` (`[TRANS-reveal-with-fuel]`: `M_test_even`/`M_test_odd` lower their `reveal(M_is_even)`/`reveal(M_is_odd)` calls to globally-scoped `assume ∀ i :: M_is_even(i) == ...` — fuel amount discarded; older "test_triangle_*" procedure names are stale)
- `verus-examples:integers` (`[TRANS-coercion-uninterpreted]`: heavy use of `bv8_to_int_u`, `bv8_to_nat_u`, `bv8_to_bv16_u`, `nat_to_int` coercions in call arguments and assertions like `nat_to_int(add1_nat(bv8_to_nat_u(u))) == bv8_to_int_u(u + bv{8}(1))`; cvc5 cannot reason through the uninterpreted coercions)
- `verus-examples:invariants` (`[TRANS-atomic-ghost-scaffolding]`: `open_atomic_invariant!` flattened to helper-call scaffolding; `[MODEL-missing-types]` — `AtomicInvariant`)
- `verus-examples:mergesort` (source `=~=` proof steps are flattened under `[TRANS-extensional-eq]`; the final `lemma_sorted_unique(..., |a, b| a <= b)` call still hits `[VERIFY-lambda-encoding]`)
- `verus-examples:modules` (`[TRANS-closed-visibility]`)
- `verus-examples:multiset` (`broadcast use group_to_multiset_ensures` ignored; multiset extensionality still lowers to plain equality; `[VERIFY-lambda-encoding]` still affects the `sort_by` comparator)
- `verus-examples:playground` (translator-side ill-scoped variable: synthetic temp symbol referenced before it is in the bvar/fvar context; produces a Strata typecheck error from a malformed program rather than a Strata-side limitation)
- `verus-examples:recommends` (`[TRANS-reveal-with-fuel]`: `seq_max_int`'s local reveal lowers to `assume ∀ s : (Sequence int) :: seq_max_int(s) == ...` global reveal; source `spec_affirm(...)` steps in `some_predicate` are erased. Sequence-length expressions use clean `Sequence.length(s)` now — older `[TRANS-seq-len-literal-typing]` claim no longer applies)
- `verus-examples:recursion` (`[TRANS-reveal-with-fuel]`; Boole output now recovers the `for` loop shape, but the source-level fuel behavior is still not preserved)
- `verus-examples:rfmig_script` (`[MODEL-missing-types]` still blocks `Simple_pptr`; the current Vec pieces now use the datatype-based path directly)
- `verus-examples:rwlock_vstd` (`[VERIFY-lambda-encoding]` in the `Ghost(|v| ...)` lock invariant; raw Core also currently collapses `RwLock`/handle operations to undeclared model types under `[MODEL-missing-types]`)
- `verus-examples:set_from_vec` (`set` extensionality still expands away under `[TRANS-extensional-eq]`)
- `verus-examples:statics` (`[TRANS-atomic-ghost-scaffolding]`: the `Lazy` / `atomic_with_ghost!` encoding still lowers to low-level `Atomic_ghost_*`, `Invariant_*`, `Cell_*`, and `assume` scaffolding rather than source-like lazy-static structure; `[MODEL-missing-types]` (`Cell`, `Atomic_ghost`))
- `verus-examples:syntax_attr` (`#[verus_spec(with ...)]`, `proof!`, and tracked/ghost wrapper syntax are still flattened under `[TRANS-ghost-tracked-erasure]`; raw Core also currently hits Strata's polymorphic tuple-helper DDM panic)
- `verus-examples:syntax` (`[TRANS-choose]` in `test_choose`; `[TRANS-ghost-tracked-erasure]`; `test_views` now uses the datatype-based Vec path directly; `[TRANS-broadcast-use]`)
- `verus-examples:test_expand_errors` (`[TRANS-hide]`, `[TRANS-reveal-with-fuel]`)
- `verus-examples:thread` (`[TRANS-exec-closure-scaffolding]`; `[MODEL-missing-types]` (`Thread`) through the closure requirement encoding)
- `verus-examples:traits` (`[TRANS-trait-unsupported]`: trait method bodies dropped, dispatch uninterpreted; commented out of `working_tests.txt` as a known issue)
- `verus-examples:trait_for_fn` (`[TRANS-trait-unsupported]`: the `impl IntFn for spec_fn(int) -> int` body `self(x)` is dropped; `[VERIFY-lambda-encoding]` then blocks the call site `f.call_int(2)`)
- `verus-examples:vectors` (`datatype Vec` path is now source-close; `pusher` still hits `[VERIFY-lambda-encoding]` and `[TRANS-extensional-eq]`)
- `verus-examples:verified_vec` (**2026-05-19:** cause confirmed and test moved to `tests/ignored_tests.txt` as `UPSTREAM-IGNORE`. Verus errors with `E0432: unresolved import vstd::ptr` — upstream Verus marked this example `ignore` (line 1 of the source: *"intending to deprecate PPtr, should update this to raw_ptr"*) because vstd no longer exposes `vstd::ptr`; the example uses the deprecated `PPtr` API. Either port to `vstd::simple_pptr` or wait for upstream port to `vstd::raw_ptr`)
- `vlir-tests:LoopSimpleWithSpec` (mirrored from `verus/tests/LoopSimpleWithSpec.rs` into `tests/VerusFiles/`; generates clean Boole but Strata-side verify reports `Expression has type int when nat expected` — a translator-side missed-coercion bug rather than a Strata gap, classified by the runner as translator-bug-shape rather than `[TRANS-coercion-uninterpreted]`)
- `vlir-tests:maps` (`[VERIFY-lambda-encoding]` in `mk_map` lambdas; `[TRANS-higher-order-collection-stubs]` currently distorts `Set_mk_map`; raw Core map equalities are still emitted as plain `==` rather than source-like map extensional equality)
- `vlir-tests:mini_c` (mirrored from `verus/tests/mini_c.rs` into `tests/VerusFiles/`; generates Boole but emits malformed tuple projection `Tuple.._2` while lowering match tuple temporaries — translator-side malformed-output bug)
- `vlir-tests:seqs` (`[VERIFY-lambda-encoding]` in `Seq::new`, `Seq::map`, `Seq::filter`, and `seq![x; n]`; `[TRANS-extensional-eq]` still expands source `===` away to raw Core equality; raw Core also currently hits `[SURFACE-sequence-empty]` and nat/int mismatches`)
- `vlir-tests:sets` (`[VERIFY-lambda-encoding]` in `Set::new`, `Set::filter`, `Set::map`, `set_map`, and `fold`; `[TRANS-higher-order-collection-stubs]` distorts `Set_new`, `Set_filter`, `Set_lib_map`, and `Set_Fold_fold`; `[TRANS-extensional-eq]` still expands source `===` away to raw Core equality; `s.choose()` is currently just uninterpreted `Set_choose` without witness semantics`)
- `vlir-tests:test_vstd` (`[VERIFY-lambda-encoding]` in `Set_new(fun i => ...)`, `Map_new(fun i => ..., fun i => ...)`, `Seq_new(5, fun i => ...)`; fixed-size array literals now lower to concrete `Sequence.empty`/`Sequence.build` chains)

## Gap Index

### `[TRANS-generic-reveal]` Generic `reveal` support
- Non-generic opaque spec functions are emitted declaration-only.
  `reveal(f)` becomes `assume forall params :: f(params) == body;`.
- Generic `reveal(g)` is still dropped because Verus erases type arguments from
  `Fuel` at SST level.
- Affects: `verus-examples:generics`

### `[TRANS-hide]` `hide` not supported
- `hide(f)` is not emitted, so the function body remains visible to the solver.
- Affects: `verus-examples:test_expand_errors`, `verus-examples:debug_expand`

### `[TRANS-reveal-with-fuel]` `reveal_with_fuel` loses fuel/locality
- `reveal_with_fuel(f, n)` is currently lowered to the same kind of global
  definitional `assume forall` used for `reveal(f)`, discarding the fuel amount
  `n` and strengthening what was source-level local proof context.
- Affects: `verus-examples:test_expand_errors`, `verus-examples:recursion`,
  `verus-examples:guide/quants`, `verus-examples:datatypes`,
  `verus-examples:recommends`

### `[TRANS-fuel-parameter-leakage]` Source `Map` operations leaked synthetic `Fuel` parameters (RESOLVED)
- Historical: some library `Map` operations used to lower to helper symbols
  whose signatures exposed internal `Fuel` arguments, even though the Verus
  source only mentioned ordinary `Map::empty`, `union_prefer_right`, and
  `insert` calls.
- **Resolved**: current emitted Boole shows clean `Map_empty`,
  `Map_lib_union_prefer_right`, `Map_insert` signatures with no `Fuel`
  parameter leakage. Verified against `guide/bst_map`,
  `guide/bst_map_generic`, `guide/bst_map_type_invariant` outputs in this
  audit.
- Kept in the Gap Index for historical context; remove if you'd prefer to
  drop resolved gaps entirely.

### `[TRANS-closed-visibility]` `closed` spec fn visibility not enforced
- `pub closed spec fn` is translated with its body visible to callers in other
  modules.
- Affects: `verus-examples:modules`, `verus-examples:debug_expand`

### `[CORE-decreases]` `decreases` preservation
- **Loop-level**: emitted in concrete `while ... decreases ...` /
  `for ... decreases ...` syntax in both Core and Boole.  Core's
  `Stmt.loop`'s `measure : Option P.Expr` is populated faithfully.
  **2026-05-07 update — for-loop measure now ships on the Boole side.**
  After the Strata pin advanced to `kondylidou/pr/benchmarks`,
  `for_to_by_statement` / `for_down_to_by_statement` carry
  `decr : Option Measure` upstream, and our translator's for-loop
  recovery branch threads the source `decreases` head term into
  the slot via `decreasesToMeasureAnn` (verus-boogie commit
  `7cf1f7d`).  Verus' auto-synthesized `Pervasive_ghost_decrease(iter)`
  shape is filtered via the new `expContainsGhostPervasiveCall`
  walker so it doesn't leak as an unresolved fvar.  Verified on
  `tests/VerusFiles/demo_for.rs` (`for i in 1..v.len() decreases
  v.len() - i`).
- **Function/procedure-level `decreases`**: **2026-05-07 update —
  shipped on the Boole side** (verus-boogie commit `4ed9b72`).
  The translator preserves Verus' `local_decls_decreases_init`
  through JSON parsing onto `ProofFn.decreases` / `ExecFn.decreases`,
  then lowers the head term into Boole's `Option Measure` slot on
  `boole_procedure`.  Verus-internal artifacts (`decrease%init*`,
  `CheckDecrease*`) continue to be stripped from bodies.
  Lex-decreases (multiple terms) collapse to the head; full
  lexicographic support waits on Strata accepting a tuple measure.
- **2026-05-18 update — Strata side closed; gap now translator-side
  for recursive *spec* fns.**  Merged upstream PR #1167 (now on the
  `kondylidou/pr/benchmarks` pin `4f3b68d64`) makes Strata actually
  check int-valued termination: `decreases <int expr>` generates
  non-negativity + strict-decrease obligations instead of being
  ignored.  So procedure-level / loop-level measures the translator
  already emits are now *enforced*, not just AST-present.  The
  remaining hole is the recursive **spec-fn** path: the emitter at
  `VerusLean/VLIR/Boole/Translate.lean:1755-1771` *does* thread
  `f.decreases` into `recfn_decl`'s measure slot, but `SpecFn.fromJson`
  (`VerusLean/VLIR/Parser.lean:1573-1645`) leaves
  `SpecFn.decreases = none` for mutually-recursive spec fns, so
  `rec function` is emitted bare and Strata rejects it with
  *"requires a 'decreases' clause or a '@[cases]' parameter"*.
  Source `decreases abs(i)` is present (`tests/VerusFiles/
  mutual_recursion.rs`) and the ProofFn path carries it correctly, so
  this is a focused parser-extraction fix on `SpecFn.fromJson`'s
  `spec_axioms.termination_check` handling.  Affects
  `vlir-tests:recursion`, `vlir-tests:mutual_recursion`,
  `verus-examples:guide__recursion`.

### `[TRANS-return-comment]` Early return rendered as comment (Core-only)
- This was a Core-pipeline-only workaround: Verus SST encodes `return expr;`
  as `ret_var := expr; assume false;`, and the Core printer rendered the pair
  back as `// return expr;` because Strata Core had no native return.
- **Resolved for Boole**: Strata Boole has native `exit <ProcedureName>;`,
  which the translator emits directly (see e.g.
  `tests/BoolePrograms/verus-examples/imo_1988_6.lean`'s many
  `exit is_perfect_square;` sites). No `// return` comments appear in any
  Boole output today.
- Still tracked here only as a raw-Core legacy note. For the previously
  affected tests (`vlir-tests:basic_failure`,
  `verus-examples:guide/requires_ensures{,_edit}`,
  `verus-examples:imo_1988_6`, `verus-examples:guide/invariants`,
  `verus-examples:set_from_vec`), the Boole output is faithful.

### `[TRANS-hastype-overflow]` `HasType` overflow guards dropped
- Verus `HasType(U32, e)` assertions silently skipped in Core output.
- Affects: many exec-mode integer arithmetic tests

### `[TRANS-extensional-eq]` Extensional / deep-equality surface syntax not preserved
- Source-level extensionality syntax such as `===`, `=~=`, `=~~=`, and
  `assert_seqs_equal!` / `assert_maps_equal!` / `assert_sets_equal!` is still
  expanded away in emitted Core/Boole output.
- Supported `Seq`, `Set`, `Map`, `spec_fn`, and `#[verifier::ext_equal]`
  struct cases now lower to explicit extensional formulas rather than
  collapsing to plain spec equality, but the original surface notation is not
  preserved as future Strata syntax. Unsupported higher-order cases can still
  fall back to raw Core `==`.
- Affects: `verus-examples:bitmap`,
  `verus-examples:bitvector_garbage_collection`,
  `verus-examples:guide/ext_equal`, `verus-examples:extensionality`,
  `verus-examples:guide/invariants`, `verus-examples:mergesort`,
  `verus-examples:multiset`, `verus-examples:set_from_vec`,
  `vlir-tests:maps`, `vlir-tests:seqs`, `vlir-tests:sets`

### `[TRANS-air-revealstring]` `RevealString` / `Air` statements erased
- `RevealString` and `Air` statements parsed as empty blocks.
- `Fuel` statements parsed into `Stm.Reveal` and lowered to `assume` equations
  for non-generic spec functions. Generic `Fuel` still dropped.

### `[TRANS-widening-casts]` Widening casts partially inserted
- Verus erases widening casts (`nat as int`, `u16 as int`) at SST level.
- Type-directed coercion insertion now adds `bv*_to_nat_u`/`bv*_to_int_u`
  at function/procedure call sites.
- Type-directed coercion insertion now also preserves source-typed quantifier
  binders and inserts `int_to_bv64_u` at plain variable use sites when the
  current `usize`/indexing context expects `bv64`.
- **Remaining gaps**: richer non-call contexts beyond plain variables
  (for example larger arithmetic expressions, projections, and other composite
  terms that still need result-side coercion insertion).

### `[TRANS-coercion-uninterpreted]` Coercion functions emitted without semantics
- Coercion helpers such as `bv64_to_int_u`, `bv8_to_bv64_u`, `bv16_to_int_u`,
  `nat_to_int`, `int_to_nat`, and `int_to_bv64_u` are emitted as
  declaration-only Boole functions (e.g. `function bv64_to_int_u (x : bv64) : int;`).
  No body, no axiom set.
- Consequence: cvc5 treats each as an arbitrary function, so any obligation
  whose proof needs the coercion's value (`bv8_to_bv64_u(20) == 20`,
  `bv64_to_int_u(15) == 15`, `bv16_to_int_u(i) >= 0`) is unprovable from the
  declaration alone, even when the source-level reasoning is trivial.
- Most visible after upstream Strata fixed earlier-pipeline typing/elaboration
  errors: tests that previously stopped at a Strata-side type error now reach
  the solver, where uninterpreted coercions become the binding constraint.
- Two viable fixes:
  - Translator-side: emit axioms alongside each declaration
    (`assume forall x : bv64. 0 <= bv64_to_int_u(x) && bv64_to_int_u(x) < 2^64`,
    `assume forall x : bv8. bv8_to_bv64_u(x) == ...`, etc.).
  - Strata-side: add native bv↔int / nat↔int conversions with built-in
    semantics so the translator can target them directly.
- Affects: `verus-examples:bitvector_basic`, `verus-examples:external`,
  `verus-examples:quantifiers`, `verus-examples:statements`,
  and any test where the solver must reason about a value that flows
  through a width-changing coercion.

### `[VERIFY-generic-typevar-ddm]` Strata still rejects some generic typed operations
- The translator now emits faithful generic helper bodies such as
  `Vec_len<T>` / `Vec_index<T>` in the Vec prelude, rather than monomorphic
  wrappers.
- Some Vec-heavy or otherwise generic examples then hit current Strata
  DDM/SMT encoding limits on type variables, even though the translation shape
  is now more source-faithful.
- Affects: `vlir-tests:FindMax`, `vlir-tests:demo_while`,
  `vlir-tests:demo_while_loop_isolation`, `verus-examples:generics`

### `[VERIFY-sequence-empty-polymorphic]` No polymorphic `Sequence.empty[A]` in Strata Boole
- Strata's Boole grammar (`Strata/Languages/Boole/Grammar.lean`) exposes
  the typed empty-sequence constants `seq_empty_bv8`/`bv16`/`bv32`/`bv64`/
  `int`/`bool` (the last added 2026-05-19), each printing as
  `Sequence.empty_<elem>`.  There is **no 0-ary polymorphic
  `Sequence.empty[A]`**; the matching translator helper
  (`VerusLean/VLIR/Boole/Inference.lean::seqEmptyTokenName`) can only pick
  a token when the element type is statically concrete.
- In generic spec functions such as
  `rec function Sequences_reverse<T> (s : Sequence T) : Sequence T` or
  `procedure Sequences_compute_seq_symbolic<T> (a : T, b : T, ...)`, the
  element type is a *type variable* and the translator falls through to
  the bare `Sequence.empty` literal, which Strata's DDM rejects with
  `Unknown expr identifier Sequence.empty`.
- Related: even when the empty-constant resolves, generic spec-fn bodies
  can still trip Strata's typed-operator dispatch with `Expected bitvector
  type, got: ... tvar "T"` on other sequence operations (see e.g.
  `adopted_rust_verify_test:seqs` after the bool fix).  This sits at the
  boundary of `[VERIFY-generic-typevar-ddm]`; tracked here as the
  specifically-Sequence-shaped manifestation.
- **Waiting on upstream**: Strata DDM growing 0-ary polymorphic
  resolution (Grammar.lean's own TODO references tracking issue #1157).
  Translator-side monomorphization is a possible workaround but doesn't
  cover truly generic call sites with unknown instantiations.
- Affects (current `main2` pin, after the 2026-05-19 bool fix):
  `verus-examples:assert_by_compute` (5 of 11 `Sequence.empty` references
  are polymorphic-`T`; 6 of 11 now correctly emit `_bool`),
  `verus-examples:guide__assert_by_compute`,
  `verus-examples:guide__ext_equal`,
  `vlir-tests:crypto_noref`,
  `vlir-tests:tests__adopted_rust_verify_test__seqs` (no longer
  Sequence.empty-blocked but exposes the related tvar-bitvector issue
  noted above).

### `[VERIFY-lambda-encoding]` Strata SMT encoder rejects lambdas
- Per Strata PR #1049, the Boole/Core grammar accepts `fun x : T => body`
  and `(f)(x)` syntax, but the SMT encoder does not yet encode lambda
  abstractions in function bodies, lambda-typed parameters, or bare
  lambda expressions: it emits `Unsupported expression:
  Strata.BooleDDM.Expr.lambda` instead.
- This is a Strata-side gap, not a translator defect; it caps the
  verifier outcome of every test that flows a closure into a spec-fn
  body or higher-order combinator.
- Affects: `verus-examples:assert_by_compute`, `verus-examples:bitmap`,
  `verus-examples:bitvector_garbage_collection`,
  `verus-examples:extensionality`, `verus-examples:guide/assert_by_compute`,
  `verus-examples:guide/exec_attr`, `verus-examples:guide/ext_equal`,
  `verus-examples:guide/lib_examples`, `verus-examples:mergesort`,
  `verus-examples:multiset`, `verus-examples:rwlock_vstd`,
  `verus-examples:trait_for_fn`, `verus-examples:vectors`,
  `vlir-tests:crypto_noref`, `vlir-tests:maps`, `vlir-tests:seqs`,
  `vlir-tests:sets`, `vlir-tests:test_vstd`.

### `[TRANS-exec-spec-helper-leakage]` `exec_spec_*` examples still lower through internal helper stubs
- `exec_spec_unverified!` and `exec_spec_verified!` examples currently expose
  internal helper symbols such as `View_deep_view`, `View_V`,
  `Contrib_Exec_spec_*`, and array/slice glue procedures rather than a
  source-like surface encoding of `deep_view`, `as_slice`, and the exec/spec
  wrapper itself.
- Affects: `verus-examples:guide/exec_spec_unverified`,
  `verus-examples:guide/exec_spec_verified`

### `[TRANS-seq-len-literal-typing]` Sequence-length expressions used to mix `nat` and `bv` (RESOLVED)
- Historical: some `Seq.len()` / `Seq_len(...)` contexts emitted `bv64` literals
  where the surrounding Core type was `nat`, producing mismatches such as
  `Seq_len(s) == bv{64}(5)`.
- **Resolved**: current emitted Boole uses `Sequence.length(s) == 5` (built-in
  `Sequence.length` returns `int`), no nat/bv mismatch. Verified against
  `guide/pervasive_example` and `recommends` outputs in this audit.
- Kept in the Gap Index for historical context.

### `[TRANS-higher-order-collection-stubs]` Higher-order collection APIs lowered to distorted first-order stubs
- Some collection constructors and operators that should take predicates or
  function values are currently emitted as first-order stubs with distorted
  signatures in order to accommodate `Unsupported.lambda`.
- Examples include `Set_new`, `Set_filter`, `Set_lib_map`, `Set_Fold_fold`,
  `Set_mk_map`, `Map_new`, and `Map_total`.
- Affects: `verus-examples:extensionality`, `vlir-tests:maps`,
  `vlir-tests:sets`

### `[TRANS-exec-closure-scaffolding]` Exec closures lowered to first-order scaffolding
- Exec higher-order code currently lowers closures to synthetic datatypes and
  contracts such as `anonymous_closure_*`, `ClosureReq`, `ClosureEns`, and
  helper calls like `Pervasive_exec_nonstatic_call`.
- This is distinct from plain lambda placeholders: the emitted shape already
  commits to a first-order closure encoding rather than a future source-like
  closure syntax.
- Affects: `verus-examples:guide/higher_order_fns`, `verus-examples:thread`

### `[TRANS-trait-unsupported]` Traits not faithfully translated
- The translator does not yet support user-defined `trait`s in any
  source-faithful way. Concrete losses observable today:
  - **Trait method bodies dropped.** A `spec fn`/`proof fn` body inside an
    `impl Trait for T` is discarded; the translated method is emitted as
    a bodyless function. Example: in
    [`tests/BoolePrograms/verus-examples/trait_for_fn.lean`](BoolePrograms/verus-examples/trait_for_fn.lean),
    the `IntFn for spec_fn(int) -> int` impl body `self(x)` is lost —
    `IntFn_call_int<Self_>` is declared without semantics.
  - **Dispatch is uninterpreted.** Calls like `f.call_int(2)` lower to
    `IntFn_call_int(f, 2)` but the function has no body, so cvc5 cannot
    relate it to any specific impl.
  - **External trait specs degrade across modules.** Uses of
    `#[verifier::external_trait_specification]` produce low-level helper
    names and mismatched coercion shapes when crossed across module
    boundaries (the case previously tracked separately).
- Treat any test that defines a `trait` or relies on trait-method
  dispatch as currently unfaithful, regardless of which specific
  manifestation surfaces in its output.
- Affects: `verus-examples:trait_for_fn`,
  `verus-examples:guide/external_trait_specs`, `verus-examples:traits`
  (commented out of `working_tests.txt` as a known issue), and any test
  whose source uses user-defined traits incidentally.

### `[TRANS-ghost-tracked-erasure]` Ghost/tracked/proof wrapper syntax flattened away
- Verus surface constructs such as `proof!`, `proof_decl!`, `proof_with!`,
  `Ghost(...)`, `Tracked(...)`, and their wrapper syntax are flattened to
  ordinary locals, parameters, tuple returns, and bare assertions/calls in
  emitted Core.
- Affects: `verus-examples:guide/exec_attr`, `verus-examples:syntax`,
  `verus-examples:syntax_attr`

### `[TRANS-atomic-ghost-scaffolding]` `atomic_with_ghost!` / invariant machinery lowered to helper scaffolding
- Source-level `struct_with_invariants!`, `atomic_with_ghost!`, and related
  ghost-invariant reasoning currently lower to low-level `Invariant_*`,
  `Atomic_*`, `Atomic_ghost_*`, `Cell_*`, and raw `assume` scaffolding rather
  than a source-like future Strata surface form.
- Affects: `verus-examples:atomics`, `verus-examples:statics`

### `[TRANS-assert-label]` Source `as <name>` assertion labels not preserved
- Verus syntax `assert(P) by (lean_proof as a1)` carries an explicit label
  `a1` that the source uses to name the obligation. Boole has matching surface
  syntax (`assert [a1]: P;` per `Strata/Languages/Core/DDMTransform/Grammar.lean:251`
  with the `Label` category at `:239,242`), but the translator currently emits
  `assert P;` without the label. Semantic content is preserved; the named
  obligation is lost.
- The translator *does* emit synthetic labels for some proof-mode contexts:
  `by (bit_vector)` produces `assert [bitvector_query]: ...`,
  `by (nonlinear_arith)` produces `assert [nonlinear_query]: ...`, and
  computation-mode asserts produce `assert [compute]: ...`. So label-emission
  is wired up; only the user-supplied `as <name>` is dropped.
- The `by (lean_proof)` proof-tactic specifier itself is not tracked as a
  separate gap because every Boole obligation is downstream-proven by Lean
  anyway, so the source choice of prover is irrelevant.
- Affects: `vlir-tests:test_specfn`, plus any test using `by (lean_proof as ...)`
  or other user-labeled `assert` syntax.

### `[TRANS-trigger-annotation]` `#[trigger]` annotations on quantifier sub-expressions stripped
- Verus quantifiers can carry `#[trigger]` (or `#![auto]`) annotations that hint
  the SMT solver about which sub-expressions to use as instantiation patterns.
  E.g. `forall|a: u32, b: u32| #[trigger] (!(a & b)) == !a | !b` marks
  `(!(a & b))` as the trigger.
- The translator currently strips these annotations: the same source quantifier
  becomes `∀ a : bv32, b : bv32 :: ~(a & b) == ~a | ~b;` with no trigger marker.
- Boole's grammar has trigger infrastructure (`Triggers.empty`,
  `Triggers.addGroup`, `TriggerGroup.empty`, `TriggerGroup.addTrigger` —
  registered Core operators), so explicit trigger preservation is supported in
  principle.
- Logical content of the assertion is preserved; only the SMT instantiation
  hint is lost. May affect verification performance or completeness for
  trigger-sensitive proofs.
- Affects: `verus-examples:guide/nonlinear_bitvec`, `verus-examples:quantifiers`,
  and any test using explicit `#[trigger]` / `#![auto]` annotations.

### `[TRANS-choose]` `choose` operator partially translated
- **2026-05-07 update — statement-level single-binder `choose` now
  ships faithfully.**  `Bind.Choose (vars) (pred)` was restored as
  a first-class VLIR constructor (was previously dropped to
  `Bind.Lambda [z]` with the predicate erased); `Parser.lean`'s
  `Choose` arm now reads the predicate from the JSON's `arr[2]`;
  every `Bind` walker (`Pp`, `Elab`, `Normalize`, `ForLoop`,
  `Pruning`, `Prelude`, `Inference`) handles the new constructor;
  `stmToBoole`'s `.Assign` arm detects `Bind (Choose [(v, ty)] pred)
  (Var v)` after `peelCallWrappers` and emits Boole's
  `choose_assign : Statement`
  (`lhs := choose v : T :: pred;`), which Strata lowers to
  `havoc lhs; assume pred[v ↦ lhs];`.
- Verified on `tests/scratch/choose_min.rs` (1/1 obligation passes).
  Cross-checked against the 9 statement-level single-binder
  occurrences across `trigger_loops.rs` (lines 25, 33),
  `syntax.rs:279`, `quants.rs` (lines 295, 312, 313),
  `chapter-1-22.rs` (lines 188, 224) — all emit clean
  `choose_assign` form.
- **2026-06-11 — the two remaining statement-reachable shapes ship:**
  - **Multi-binder choose-let** (`let (x, y) = choose|i, j| pred(i, j)`,
    arriving as the tuple temporary's assignment with the binder tuple as
    the chosen value): `normalizeChooseProduct` rewrites it to a
    single-binder choose over the right-nested pair type
    (`choose p : (T1, …, Tn) :: pred[vk ↦ p.k]`), which the existing
    statement and spec-fn paths then handle.  `quants.rs:325` now emits
    `tmp_ren0 := choose i_j_choose : (Tuple2 int int) ::
    less_than(Tuple2.._0(i_j_choose), Tuple2.._1(i_j_choose));`.
  - **Choose in call-argument position** (`lemma(i, choose|j| pred(j))`):
    `hoistChooseArg` hoists each such argument to a fresh temporary bound
    by `choose_assign` ahead of the call — `quants.rs:452` now emits
    `j_choose_arg1 := choose j : int :: g(i, j); call
    lemma_g_proves_f(i, j_choose_arg1);` and its ensures passes.  The
    temporary's inline `var` introduces a binding level, so the hoist
    registers it in scope before any of the call's expressions translate
    (two passes over the arguments).
  - A spec fn whose whole body is a choose emits Boole's native
    `command_choosefndef` (`function f(args) : R := choose v : T :: pred;`,
    Strata #1365), which Strata lowers to an uninterpreted `f` plus a choice
    axiom (see `specFnToBoole`); with `normalizeChooseProduct` this covers
    multi-binder spec-fn chooses too.
  - Still erased: choose in non-argument expression positions (e.g.
    nested inside arithmetic), the `expToBoole` `.Choose` fallback.
    Remaining Verus examples: `state_machines/refinement.rs:81`,
    `state_machines/refinement_labels.rs:91`,
    `summer_school/chapter-6-1.rs:117` (all argument-adjacent shapes that
    should route through the hoist when those suites are exercised).
  - **Known semantic divergence of the statement lowering** (visible in
    `quants.rs`'s `test_choose_same`, ⌛ not ❌): Verus's choose is a
    function of the predicate — two chooses of the same predicate are
    equal, and an unsatisfiable predicate yields an arbitrary value with
    no obligation.  `choose_assign` havocs per occurrence (so `x == y`
    across two chooses is not derivable) and asserts the existential at
    each site (an obligation Verus does not have).  Spec-fn chooses get
    the functional semantics exactly via the choice axiom; choose-lets
    whose witnesses must coincide would need the same function-level
    encoding.

### `[TRANS-float-unsupported]` Floating-point types/operations not yet translated
- Source `f64`/`f32` literals lower to `Unsupported.Float64`/`Unsupported.Float32`
  placeholders in emitted Boole rather than concrete bv64/bv32-bit-pattern
  encodings or a Strata-native float type.
- Float operations (`+`/`*`/etc.) and float-related axioms (e.g. `vstd::float::*`)
  similarly lower to `Unsupported.*` placeholders or get dropped.
- Strata has no native floating-point type today; a translator-side workaround
  would have to choose an encoding (bit-pattern bv, uninterpreted, or
  axiomatic) before this gap can be closed.
- Affects: `verus-examples:float`.

### `[TRANS-broadcast-use]` `broadcast use` flattened to raw assumptions
- Source-level `broadcast use ...` proof steps are currently flattened to
  direct `assert` / `assume forall` scaffolding rather than a dedicated proof
  construct or future Strata surface syntax.
- Affects: `verus-examples:multiset`, `verus-examples:syntax`

- Affects: `verus-examples:guide/lib_examples`, `verus-examples:rfmig_script`,
  `verus-examples:syntax`, `verus-examples:vectors`

### `[TRANS-for-loop-empty-range]` For-loop `to` bound underflows on empty ranges
- The translator (and `synthesizeVecFromElemBody`) lowers Verus's exclusive
  range `0..n` to Boole's inclusive `for i := 0 to n-1`. The subtraction is
  done in `bv64` (e.g. `int_to_bv64_u(Sequence.length(text)) - bv{64}(1)`),
  which underflows to `2^64 - 1` when `n == 0`.
- Boole's `for ... to limit` is inclusive, so a limit of `bv{64}(2^64 - 1)`
  would attempt up to `2^64` iterations — silently divergent rather than
  the empty iteration the source intends.
- Today this is masked because callers typically `requires len > 0` or the
  surrounding spec guarantees non-empty input, so the `len == 0` path is
  unreachable in practice. There is no test that exercises the empty-range
  case end-to-end.
- Three viable fixes, in order of cheapness:
  - **Use an exclusive-bound for-loop syntax** if Strata Boole exposes one
    (`for i := 0 < limit` style); cheapest, deterministic.
  - **Guard the loop**: emit `if n > 0 { for i := 0 to n - 1 { ... } }` at
    every for-loop reconstruction site (and in `synthesizeVecFromElemBody`).
  - **Axiomatize the coercion**: orthogonal — doesn't fix the divergence,
    just makes it provably stuck rather than silently wrong.
- Choice between `int_to_bv64_u(n) - bv{64}(1)` (current) and
  `int_to_bv64_u(n - 1)` is solver-side: bv subtraction is more concrete
  for cvc5; int subtraction goes through an extra uninterpreted-coercion
  layer. Current form is preferred until the empty-range guard is in place.
- Affects: every test that uses a for-loop reconstruction or
  `Vec_from_elem`. Concrete instance: `vlir-tests:crypto_noref`'s
  `encrypt`/`decrypt` loops at `for i : bv64 := bv{64}(0) to
  int_to_bv64_u(Sequence.length(text)) - bv{64}(1)`.

### `[VERIFY-datatype-tester-ordering]` Strata: datatype tester resolves as free variable when its datatype is declared first
- **Filed against Strata.**  Trigger conditions bisected: program
  has ≥4 datatype declarations AND the position-0 datatype's
  testers (`<dt>..is<ctor>`) are referenced by a later function
  or procedure body.  Type-check fails with `Free Variables:
  [<dt>..is<ctor>]` on an auto-generated obligation that includes
  the same tester twice — once recognised as an op (`~`-prefixed),
  once as a free variable.
- Localised to `Boole.toCoreProgram`'s lowering (the LContext
  function-table construction path).  The same program written
  directly in Core verifies cleanly, so the bug is Boole-side
  rather than Core-side.  No translator workaround possible from
  our side.
- **Causes flake on tests/working_tests.txt**: Verus' Lean
  exporter (`vir/src/sst_to_lean.rs::lctx.dts: HashSet<Dt>`)
  iterates non-deterministically, so `verus-examples:guide/datatypes`
  intermittently triggers the position-0 condition and flips
  pass/fail between runs of the same source.  Awaiting Strata
  maintainer fix.
- Affects: `verus-examples:guide/datatypes` (run-to-run flake),
  any future test with ≥4 datatypes where one has match-cased
  testers.
- **Script-side workaround**: `tests/lib/boole_verify.sh` now
  classifies the matching errors (`Free Variables:
  [shape..isshape_…]` on `guide__datatypes.lean`, `Free Variables:
  [life_…]` on `vlir-tests/matching.lean`) as `known_translator_bug`
  rather than as a regression, so `tests/check_working_tests.sh`
  reports a consistent count regardless of which side of the dice
  roll the current run landed on.  The underlying bug is unchanged.
- Affects (run-to-run flake, same root cause): also
  `vlir-tests:matching` (`Life` enum referenced from a procedure
  body; same ≥4-datatype condition as `guide/datatypes`).

### `[TRANS-nat-quantifier-arith]` `nat` binders in quantifier arithmetic context
- Verus source: `requires forall|x: nat, y: nat| f(x + 1, 2 * y)
  && …`.  The translator emits the binders with type `nat` and
  the arithmetic with type `int`, producing
  `∀ x : nat, y : nat :: f(x + 1, 2 * y) && …` which Strata
  rejects with *Expression has type int when nat expected*.
- Surfaced while sweeping `choose|x|` test sites (priority-8
  validation pass).  The test's choose statements lower
  correctly; the surrounding `requires` clause's nat-quantifier
  hits this pre-existing bug instead.
- Likely fix: either coerce binders to `int` for arithmetic
  contexts (matching how scalars are handled elsewhere in the
  pipeline) or wrap each use of the binder in `nat_to_int(...)`.
- Affects: `verus-examples:trigger_loops` (line 36's
  `bad_loop` requires).  Adjacent to `[TRANS-coercion-uninterpreted]`
  but the failure is at type-check rather than at solver time.

### `[SURFACE-sequence-empty]` typed `Sequence.empty_<T>` resolved
- **2026-05-07 — typed dispatch in `expected?`-known contexts**
  (verus-boogie commit `8048d3a`).  Boole's grammar exposes
  `Sequence.empty_bv8 / _bv16 / _bv32 / _bv64 / _int` (the DDM
  parser cannot resolve a polymorphic `Sequence.empty` without
  arguments).  The translator picks the right token via the new
  `seqEmptyTokenName` helper at every `resolveFreeVar
  "Sequence.empty"` site, threaded through `seqEmptyExpr` /
  `seqLiteralExpr` / `seqRepeatExpr`.  Eliminated the manual edits
  the SHA-256 wrapper required.
- **2026-05-08 — equality-position gap closed.**  When a sequence
  literal appears in `assert v == Sequence.append(…, Sequence.build(…,
  Sequence.empty, …), …)`, the inner `Sequence.empty` was previously
  emitted untyped because `expected? = some .Bool` carried no
  element-type hint and `Seq_*` arms looked up the polymorphic
  static signature instead of using the call's `expected?`.  Two
  changes: (a) `comparisonPrelude` now uses `inferComparableTyp?`
  to propagate one side's concrete type as `expected?` to the other
  side when neither side has bv info; (b) every `Seq_*` arm in
  `expToBoole`'s Call branch now prefers a concrete `Sequence T`
  `expected?` over the polymorphic `lookupFnParamTypeFull` value via
  the new `seqArgExpected?` helper — letting nested
  `Sequence.append`/`Sequence.build` chains thread the element type
  down to `Sequence.empty_<T>` literals at the leaves.
- **Validation**: `verus-examples:guide/lib_examples`,
  `verus-examples:guide/quants`, and `vlir-tests:test_vstd` now
  emit zero untyped `Sequence.empty` tokens.  Each test still fails
  for a different (pre-existing) reason — `lib_examples` on
  int-vs-nat coercion in `Seq_new(5, fun i: int => …)`,
  `quants` on the multi-binder / expression-level `[TRANS-choose]`
  gaps, `test_vstd` on `Unknown variable Map_new` — but the
  `Sequence.empty` typed-dispatch issue itself is resolved across
  all reachable contexts.

### `[SURFACE-sequence-literal]` typed `Sequence.of_<T>[…]` literal emission
- **2026-05-14 — adopt upstream `seq_of_*` syntax** (Strata
  `kondylidou/pr/benchmarks` commit `edd12d7f8`, "sequence
  initilization").  Boole's grammar now exposes
  `Sequence.of_bv8 / _bv16 / _bv32 / _bv64 / _int` typed-literal tokens
  with the surface syntax `Sequence.of_<T>[v0, v1, …]`.  Strata's
  `toCoreExpr` lowers each one to the same left-fold of `Sequence.build`
  over `Sequence.empty` that the translator was emitting by hand, so
  verification semantics are unchanged.
- **Translator change**: `seqLiteralCtor?` in `Translate.lean` maps an
  element type to the dedicated `BooleDDM.Expr.seq_of_<T>` AST
  constructor (the brackets-with-comma surface form must be emitted as
  the specific AST node — a generic `Bld.appN` to a `Sequence.of_bv32`
  free variable prints with parens and is rejected by the DDM frontend
  as `Unknown variable Sequence.of_bv32`).  Both `seqLiteralExpr` and
  `seqRepeatExpr` route through it; polymorphic element types
  (`TypParam`, `Struct`, unrecognised) fall back to the older
  `Sequence.build` chain over `Sequence.empty_<T>`.
- **Validation**: `sha256_compact_indexed`'s `K32` constant emits as a
  single `Sequence.of_bv32[bv{32}(0x428a2f98), bv{32}(0x71374491), …]`
  literal instead of a 64-deep nested `Sequence.build(Sequence.build(…
  Sequence.empty_bv32, v0), v1)` chain.  Output size for that one
  literal drops from ~3 KB to ~700 bytes.  The `[0u32; 16]` init in
  `to_u32s` similarly compacts.  Obligation count goes 24 → 26 for the
  SHA test (two additional well-formedness obligations the typed-literal
  node generates), all passing; full
  `tests/check_working_tests.sh` regression is unchanged (31 pass /
  9 fail).
- Affects (emission shape only, no verification-outcome changes):
  every test that previously emitted a `Sequence.build(…)` chain on a
  bv8/16/32/64/int element type.  Visible in
  `vlir-tests:sha256_compact_indexed`, `vlir-tests:test_vstd`,
  `verus-examples:assert_by_compute`, `multiset`,
  `doubly_linked_xor`/`doubly_linked`, `guide/ext_equal`,
  `guide/lib_examples`, `mergesort`, `vec_ops`, and
  `vlir-tests:seqs` (where polymorphic element types still fall
  back to the build chain).

### `[TRANS-loop-counter-int]` `usize`/`isize` counters use `int` when used as sequence indices
- **Background**: Verus types `for i in 0..N { … }` (and `let mut k:
  usize = 0; while k < blocks.len() { … }`) with `i, k : usize`, which
  the canonical type lowering maps to `bv64`.  When the body uses the
  counter as a sequence index (`s[i]`) or compares it against
  `Sequence.length(_)`, the translator emits `bv64_to_int_u(_)` casts
  on every use.  The cast is uninterpreted from the solver's point of
  view, so the SHA-256 compress loop's invariants did not discharge:
  cvc5 could not relate `bv64_to_int_u(i)` to `i`'s known range or the
  sequence's length.
- **2026-05-08 fix — `IntPromotion` pass.**  A new module
  `VerusLean/VLIR/Boole/IntPromotion.lean` runs once per procedure
  body and decides which `usize`/`isize` locals (and recovered
  for-loop binders) can safely be retyped as `Int`.  The rule:
    - **Candidates**: every `usize`/`isize` local in `f.locals`, plus
      every `usize`/`isize` for-loop binder discovered through
      `recoverForLoop?`.  Procedure inputs and `&mut` outputs are not
      candidates (they cross call boundaries).
    - **Promote** iff every use site is in a position the classifier
      considers safe (sequence-index slot of a `Vec`/`Array`/`Slice`
      indexer or `Std_specs_Core_index_set` call, true index/count
      slot of `Seq_*` ops, length comparison, pure int arithmetic,
      for-loop bound, `Unary[Box _]` / `Unary[Unbox _]` /
      `Unary[Clip _ _]` wrapper) **and** at
      least one use is *qualifying* (sequence-index or length
      comparison).  The for-loop bound being a length call qualifies
      the binder.
    - **Reject** if any use is in a bitwise op, an explicit
      `bv*_to_*` / `int_to_bv*_*` cast, an opaque `Stm.Call` arg slot,
      a struct/enum/tuple ctor field, an assignment into a bv-typed
      non-candidate target, or an assignment dependency connected to a
      rejected candidate (propagated to fixpoint in both directions).
  The result is a `HashSet String` of names to promote.  Once
  computed, the procedure-lowering site rewrites `Assign.lhsTy` on
  every assignment to a promoted name to `Int`, retypes the
  corresponding `LocalDeclInfo`, and stashes the set in
  `BuildCtx.promotedLocals`; `tryForLoopRecovery` reads the set there
  to decide whether to retype the loop binder.  The expression walker is
  scope-aware, so quantifier/lambda/choose/let binders shadow same-named
  locals during inference.  The rest of the translator picks up
  `expected = some Int` automatically through the env and the
  assignment's lhsTy.
- **Companion changes that landed alongside.**
  - `Unary[Box _]` and `Unary[Clip _ _]` in `expToBoole`, plus the
    existing `Unary[Unbox _]` pass-through behavior, preserve
    `expected? = some Int`, so Verus' overflow-check + type-erasure
    wrappers don't drop the int context.
  - `arithFootprint` treats `Clip` as transparent so a Clip-wrapped
    int subtree no longer trips `inferBitInfo` into deciding the
    expression is bv.
  - The four sequence-index lowering arms in `expToBoole`
    (`isArrayIndexGetName`, `isSliceIndexGetName`,
    `isVecIndexSpecName` / `isVecIndexExecName`, plus the `index_set`
    write side) all now pass `expected = some .Int` to the index
    translator directly, instead of translating with `expected = none`
    and post-coercing.  The post-coerce path didn't fold a bv-typed
    `Const` literal into `intConst`, so an old `state[0]` was emitting
    `Sequence.select(state_out, bv64_to_int_u(bv{64}(0)))` even though
    the matching write side already printed `Sequence.update(…, 0,
    …)`.  After unification both sides print as `Sequence.select(…,
    0)` / `Sequence.update(…, 0, …)`.
- **Validation**: `tests/VerusFiles/sha256_compact_indexed.rs` is now
  fully green: 24/24 obligations pass, including the two `compress`
  while-loop invariants (`entry_invariant_0_0`,
  `arbitrary_iter_maintain_invariant_0_0`) that were previously
  unknown.  Generated Boole prints `var k : int; while (k <
  Sequence.length(blocks)) { … }`, `for i : int := 0 to N - 1 { …
  Sequence.select(s, i) … }`, with no `bv64_to_int_u` casts at the
  index positions.  The working-suite regression case intentionally
  stays on this source-close while-loop variant, rather than replacing
  the SHA code with a state-threaded rewrite, so the test continues to
  check translation faithfulness for the original control-flow and
  mutation shape.  Full `tests/check_working_tests.sh` runs on this
  checkout report the same 9 existing non-green verification failures
  and no SHA regression; the pass / known-translator-bug split varies
  between runs because of `[VERIFY-datatype-tester-ordering]`.
- **Scope notes**.
  - This is *not* a global "treat all `usize` as `int`" change.
    `usize` outside a candidate slot, and any local with a bitwise op
    or bv-typed callee in its use sites, stays bv-typed.
  - The pass is conservative on opaque Stm.Call args (rejects every
    candidate appearing in a generic procedure call), with a
    deliberate exception for `Std_specs_Core_index_set`'s index slot.
    Extending the per-callee whitelist (e.g. for known-int procedure
    parameters) is future work.

### `[MODEL-unit]` Missing Strata `Unit` (Core-only)
- Raw Core still leaks `Tuple_ctor_0(): Unit` in places where the Verus source
  did not mention a user-visible unit value.
- **Resolved for Boole**: `Tuple_ctor_0` does not appear in any current Boole
  output. The translator either drops the unit value entirely (procedure
  return is `()` modeled as no return slot) or rewrites the synthetic
  `Tuple_ctor_0` away during normalization.
- Still tracked as a raw-Core legacy note for the previously affected tests:
  `verus-examples:guide/exec_attr`, `verus-examples:mergesort`,
  `verus-examples:set_from_vec`, `verus-examples:syntax`,
  `verus-examples:guide/invariants`.

### `[TRANS-loop-helper-leakage]` Loop helper symbols leak into raw Core (Core-only)
- Iterator-lowered loops still expose helper symbols such as
  `Pervasive_ghost_*`, `Pervasive_exec_invariant`, and `Pervasive_arbitrary`
  in raw Core output, even though they are translator scaffolding rather than
  source-level Verus syntax.
- **Resolved for Boole**: the translator filters these via
  `isGhostPervasiveCallName` and the for-loop preamble live-set scan; no
  `Pervasive_ghost_*` / `Pervasive_arbitrary` / `Pervasive_exec_invariant`
  symbols appear in any current Boole output.
- Still tracked as a raw-Core legacy note for the previously affected tests:
  `verus-examples:guide/exec_attr`, `verus-examples:mergesort`,
  `verus-examples:set_from_vec`, `verus-examples:guide/invariants`,
  `verus-examples:guide/higher_order_fns`.

### `[MODEL-missing-types]` Missing Strata types
- `nat` emitted as abstract type. Coercion functions declared as uninterpreted.
- Collection types: `Set`, `Verus_Map`, `Multiset`.
  `Set` and `Multiset` are still declared by the translator when referenced.
  `Map` stays prefixed because Strata Core already has a built-in `Map`.
  `Tuple`, `Std_specs_range` are also declared when referenced.
- Verus `Seq<T>` now lowers to Strata's built-in `Sequence T`. Free type
  variables (`A`, `T`, etc.) are auto-declared as abstract types.
- Still missing in Strata: `Cell`, `Atomic`, `Atomic_ghost`, `Simple_pptr`,
  `Unit`, `Arithmetic_overflow`, `Rwlock`, `Thread`, `String_string`,
  `Invariant` (keyword clash with Strata's `invariant`), `LocalInvariant`,
  `AtomicInvariant`. Floating-point types `f32`/`f64` lower to
  `Unsupported.Float*` placeholders (see `[TRANS-float-unsupported]`).
- Concrete tests exemplifying each missing type:
  - `Atomic`/`Atomic_ghost`: `verus-examples:atomics`, `verus-examples:basic_lock1`,
    `verus-examples:basic_lock2`
  - `Cell`/`PCell`: `verus-examples:cells`, `verus-examples:guide/interior_mutability`,
    `verus-examples:basic_lock1`, `verus-examples:basic_lock2`,
    `verus-examples:even_cell`
  - `LocalInvariant`/`AtomicInvariant`/`Invariant`: `verus-examples:even_cell`,
    `verus-examples:invariants`, `verus-examples:basic_lock1`
  - `Simple_pptr`: `verus-examples:rfmig_script`, `verus-examples:doubly_linked_xor`
  - `Arithmetic_overflow`: `verus-examples:overflow`
  - `Rwlock`: `verus-examples:rwlock_vstd`
  - `Thread`: `verus-examples:thread`
  - `String_string`: `verus-examples:guide/strings`
  - `Unit` (Core-only): `vlir-tests:demo_for` (Boole-side resolves to no-return,
    only the raw Core path leaks `Tuple_ctor_0`)
  - Floating-point: `verus-examples:float`
