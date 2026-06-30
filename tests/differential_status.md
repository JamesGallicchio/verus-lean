# Differential Status

This file tracks three things separately:
- automated Boole pipeline outcomes from `regress_examples.sh`
- targeted Boole smoke/elaboration/verification diagnostics
- manual faithfulness judgments for reviewed cases

Solver success is **not** used to classify faithfulness.

## Data Sources
- **trait-dispatch targeted smoke** (`resolved_method` parser
  dispatch):
  - `lake build`: success (443 jobs; warnings only).
  - Targeted Boole generation succeeded for `trait_for_fn`, `traits`,
    `guide/external_trait_specs`, and `b5_minimal`.
  - Generated call-site evidence: expression call `f.call_int(2)` emits
    `Impl__0_call_int(f, 2)`; concrete statement calls emit `Impl__0_f`,
    `Impl__0_summary`, and `Impl__13_mul` respectively.
  - Targeted verification still fails for non-dispatch reasons:
    `trait_for_fn` has a higher-order SMT encoding error on
    `Impl__0_call_int(self : int -> int, ...)`; `traits` has existing
    bv64/int type mismatches around the generic trait path;
    `guide/external_trait_specs` has a type-var SMT encoding error on the
    abstract `Summarizer_summary` obligation plus cvc5 timeouts.
    `b5_minimal` targeted verify was interrupted after several silent solver
    minutes, so no obligation count is recorded.
- **automated refresh** (`verus-boogie @ f959ae7` plus the
  associated-type-resolution working-tree changes; `Strata`
  `pr/casts-boole @ fff49d4e3` plus its current working-tree fixes; solver:
  `cvc5`):
  - `lake build`: success (443 jobs; warnings only).
  - `./tests/check_working_tests.sh` (rerun 2026-06-22 after the tuple refresh):
    **generation all working tests passed**; Strata verify: **30 passed ·
    0 skipped (Sequence) · 3 skipped (Strata gap: `crypto_noref`, `generics`,
    `guide/overflow`) · 0 skipped (solver timeout) · 16 skipped (solver
    unknown) · 0 known translator bugs · 0 failed**.
  - `./tests/check_regression_gate.sh` / `regress_examples.sh --all-suites`:
    **67 verify passed · 0 skipped (Sequence) · 6 skipped (Strata gap) ·
    1 known translator bug · 53 verify failures · 0 generation failures ·
    0 missing JSON · 4 ignored**. Total accounted: **131 tests**.
    The gate exits nonzero because it requires zero verify failures, while the
    broad differential set currently has 53 failing cases (many already
    documented as unsupported/unfaithful); use `check_working_tests.sh` as the
    stable regression gate.
  - The all-suites scan includes the Dalek B1-B5 files present under
    `tests/VerusFiles/`. `b1_full` fails at Lean elaboration (stack
    overflow). `b5_minimal` emits the concrete resolved trait impl call
    (`call tmp1 := Impl__13_mul(self, s)`) instead of the abstract
    `Ops_Arith_Mul_mul` call.
  - `guide/quants`:
    **149 obligations: 129 passed · 7 SMT encoding errors · 13 timeouts**.
    The encoding errors are the `assert_81` / `assume_82`
    `Sequence.update`/`Sequence.select` obligations.
- **targeted mini_c tuple/unit refresh** (2026-06-22):
  `./tests/run_tests.sh --boole --verbose tests/VerusFiles/mini_c.rs`
  emits valid binary tuple selectors (`Tuple2.._0`/`Tuple2.._1`), no
  `Tuple.._2` / `Tuple2_ctor_0`, and includes the needed `Unit` and `Set`
  support declarations. `./tests/run_tests.sh --verify --verbose
  tests/VerusFiles/mini_c.rs` now classifies as a Strata gap on unsupported
  string literals (`Strata.BooleDDM.Expr.strLit`), not a translator bug.
- **targeted crypto_noref tuple-projection refresh** (2026-06-22):
  `./tests/run_tests.sh --boole --verbose tests/VerusFiles/crypto_noref.rs`
  emits monomorphic `Tuple2_proj_*` helpers for the `|kv: (u8, u8)| kv.0 ^
  kv.1` closures, avoiding Strata's direct `Tuple2.._0/_1` type-variable
  mismatch in bitvector XOR. `./tests/run_tests.sh --verify --verbose
  tests/VerusFiles/crypto_noref.rs` now classifies as a Strata gap on
  unsupported polymorphic `Sequence.empty<T>()`, not a translator bug.
- **unit-test demonstration suite for `FEATURE_SUPPORT_MATRIX.md`** (2026-06-22):
  added `tests/VerusFiles/unit_tests/*.rs` — one minimal, clearly-marked example
  (header: "UNIT TEST … NOT adopted from the Verus repo") per all-green matrix
  row. **27 verify end-to-end** (Verus `0 errors` + every Strata obligation ✅)
  and are listed in `working_tests.txt`. A5 "Structural recursion (over
  datatypes)" / B5 "decreases — function (structural `@[cases]`)" now verify
  end-to-end (`unit_tests/structural_recursion.rs`, 9/9): Translate emits
  `@[cases]` on the decreasing datatype parameter. A5 "Mutual recursion (over
  datatypes)" (#599) also verifies (`unit_tests/mutual_recursion_datatypes.rs`,
  13/13): the mutually-recursive datatype SCC emits as one `command_datatypes`
  block, so `tree ↔ forest` resolve under two-phase name pre-registration. One
  row the matrix marks all-green still does **not** verify in the minimal case
  and is recorded in `waiting_for_strata.txt`:
  - A1 "Bitwise ops on bvN" `>>s` — `unit_tests/bitwise_ops.rs`: the six unsigned ops
    verify, but signed/arithmetic right shift lowers to `Bv32.SShr` (undeclared
    in Strata Core) / malformed Boole on negative literals.
  Authoring notes (solver-budget, not translation defects): symbolic bv→int
  arithmetic bridges (`r == x + y`, `decreases i` on a bv var, full-range
  overflow guards) time out at cvc5's default budget, so the green examples use
  concrete or tightly-bounded operands; array `.len()` times out via the
  uninterpreted `Array_spec_array_as_slice` wrapper (concrete-index access is
  fine); loop-indexing stays in the `for`-over-local-array form (sha256's green
  shape); and concrete bitwise asserts use `by (lean)` because Verus's default
  solver treats integer bitwise ops as opaque while Strata/cvc5 discharges them.
- Full run (`./tests/regress_examples.sh --all-suites`):
  - solver: `cvc5`
## Automated Boole Regression Summary
`regress_examples.sh --all-suites` currently scans 131 tests:
- generation failures: 0
- missing json: 0
- verify passed: 67
- verify skipped (Sequence): 0
- verify skipped (Strata gap): 6
- known translator bugs: 1
- verify failures: 53
- ignored: 4

These are automated pipeline outcomes, not faithfulness judgments. The manual
classification below covers all 131 currently scanned tests, including the
Dalek cases.

## Manual Differential Classification
Tests in regression and classified in this doc: **131**.
`regress_examples.sh --all-suites` scans `tests/VerusFiles/`,
`tests/adopted_rust_verify_test/`, `verus/examples/`, and
`verus/examples/guide/` at `find -maxdepth 1`.

Bucket totals: 21 (faithful and same) + 54 (faithful but different) +
56 (not faithful) = **131**, matching the current regression test count.

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

Notes:
- "Generation failures" is 0: every test in the suite produces emitted Boole.
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
  is kept as a regression artifact but is not the canonical output for
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
  Boole `let_in_expr` AST exists but its lowering substitutes the value
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
  Strata's `@[cases]` requirement for recursion over datatypes.
- `verus-examples:recursion`, `verus-examples:guide/recursion`: Boole
  recovers the loop structure where relevant, but the overall best current
  condition is still not faithful because `[TRANS-reveal-with-fuel]` changes
  the source-level behavior.

The manual pass review retains the following currently passing
tests in `not faithful translation`: `verus-examples:modules`,
`verus-examples:recommends`, `verus-examples:recursion`,
`verus-examples:syntax_attr`, `verus-examples:test_expand_errors`,
`verus-examples:guide/const`, and `verus-examples:guide/recursion`. Passing
does not repair their documented visibility, reveal/fuel, hide, wrapper
erasure, or name-collision semantics.
## faithful and same as Verus output (21)
- `verus-examples:adts_eq`
- `verus-examples:assertions` (fail as expected)
- `verus-examples:debug` (fail as expected)
- `verus-examples:external` (`external_body` follows the standard trusted-spec convention; erased `Ghost<int>` and `println!` body do not change verification meaning; native `as_int` preserves and discharges the mixed `u64`/`int` precondition)
- `verus-examples:fun_ext`
- `verus-examples:guide/calc`
- `verus-examples:guide/datatypes`
- `verus-examples:guide/equality`
- `verus-examples:guide/getting_started`
- `verus-examples:guide/pervasive_example` (sequence literal, length, and indexing lower directly through the native `Sequence` model; 12/12 obligations pass)
- `verus-examples:imo_1988_6`
- `verus-examples:integers` (native integer/bitvector casts preserve the source assertions; 35/35 obligations pass)
- `verus-examples:structural`
- `vlir-tests:basic_failure` (fail as expected)
- `vlir-tests:binder_cast_regressions`
- `vlir-tests:by_lean` (fail as expected)
- `vlir-tests:matching`
- `vlir-tests:sha256_compact_indexed` (indexed loops, `Sequence` accesses, wrapping bitvector additions, and mutable-reference state output are preserved)
- `vlir-tests:test_array` (array literals and inequality lower directly to concrete `Sequence` construction and equality; 6/6 obligations pass)
- `vlir-tests:test_opaque_reveal` (opaque function declaration-only + reveal as assume)
- `vlir-tests:test_specfn`

## faithful but different from Verus output (54)
- `verus-examples:adts` (datatypes, variant checks, structural equality; `matches` clauses correctly desugar to `..is<ctor>(o) && ..field(o) == val` form)
- `verus-examples:assorted_demo` (`#[verifier::external]` fn dropped from translation entirely; `external_body` follows the standard `assume false;` convention)
- `verus-examples:basic_failure` (translation is source-close; the test's `external_span(s: Seq<nat>)` proof procedure lowers to `procedure external_span (s : Sequence nat)` and is blocked by Strata's current Sequence frontend/indexing support. The local `fn main(){}` source edit (uncommitted, in `verus/examples/basic_failure.rs`) unblocks Verus export so the file reaches Stage 3 and surfaces this pre-existing Sequence-frontend failure rather than hiding behind `E0601`)
- `verus-examples:bitvector_basic` (width-changing and bv↔int casts use native interpreted `as_bv` / `as_int` / `as_sint`; `compute`/`assert_32` verify, and only the genuinely cvc5-hard `bitvector_query` remains: 42✅/1⌛)
- `verus-examples:bitvector_equivalence` (bitvector proofs with triggers and decreases; cvc5 times out on the `equivalence_proof_bv` ensures — large bit-blasted query)
- `verus-examples:broadcast_proof` (translation uses Sequence prelude faithfully. In `tests/ignored_tests.txt` as `EMPTY-EXPORT` — the source is `broadcast use`-only with no top-level Verus-mode declarations, so Verus reports `verified` but emits no JSON. Skipped silently rather than counted as missing-JSON. The Sequence-frontend blocker is moot because Stage 1 never produces output)
- `verus-examples:calc` (`calc!` steps lower to explicit assertion chains; the remaining mismatch is Strata's current `Sequence` frontend/indexing support plus nat/bv64 typing in the sequence-extensionality steps)
- `verus-examples:cells` (translation is source-close; the current difference is the missing `Cell` model type in Strata)
- `verus-examples:generics` (`[TRANS-generic-reveal]`; `[VERIFY-generic-typevar-ddm]` raises SMT encoding errors on type-var-using obligations, and downstream asserts depending on those obligations also fail. The type-var cast surfaces as a Strata *elaboration* error (`as_int` on a `tvar`); classified `skip_gap` — non-monomorphized generics, the fix is Strata-side monomorphization)
- `verus-examples:guide/integers` (integer-domain crossings lower to native interpreted `as_bv` / `as_int` casts and the modeled nat API; the output is semantically faithful but expands source casts and range checks)
- `verus-examples:guide/interior_mutability` (translation is source-close; the current difference is the missing `Cell` model type in Strata)
- `verus-examples:guide/modes` (`Tuple2` support is declared when referenced; mixed `nat`/`bv8`/`int` arithmetic lowers through modeled `nat.toInt` / `nat.fromInt` and native `as_int` casts)
- `verus-examples:guide/nonlinear_bitvec` (translation faithful: `[bitvector_query]`/`[nonlinear_query]`/`[compute]` proof-mode labels emitted; `[TRANS-trigger-annotation]` strips `#[trigger]` annotations on De-Morgan quantifiers but preserves logical content. Verify SKIP — Strata-side dispatch for the proof-mode labels is incomplete on this case)
- `verus-examples:guide/opaque` (faithful empty Boole export: source `pub open spec fn` opaque-with-`reveal_with_fuel` declarations have no exec procedures to verify. In `tests/ignored_tests.txt` as `EMPTY-EXPORT`. Even after appending `fn main(){}` to the source, Verus reports `0 verified, 0 errors` and emits no JSON because there are no Verus-mode declarations to serialize — consistent with the "nothing for Strata to discharge" classification)
- `verus-examples:guide/overflow` (`[MODEL-missing-types]`: `Arithmetic_overflow` not modelled in Strata; `Num_checked_add` lowers to a procedure with `assume false;` body per the external-body convention. Classified `skip_gap` in elaboration because native `as_int` is applied to an unmonomorphized type variable `V`; this is the same Strata generic-monomorphization gap as `verus-examples:generics`)
- `verus-examples:guide/references` (the loop decrease and overflow guards use native interpreted `as_int`; immutable/mutable references erase to plain values, which is verification-equivalent)
- `verus-examples:guide/requires_ensures_edit` (source `i8` signed comparisons `-16 <= x1 < 16` lower to `<=s`/`<s` and now **verify end-to-end: 12/12 ✅ (2026-06-22)** — the earlier signed-bv-comparison lowering gap is resolved; Strata Core handles the signed-bv comparison ops)
- `verus-examples:guide/requires_ensures` (the signed-bv-comparison gap is resolved, see `requires_ensures_edit`; `print_two_digit_number` is `external_body` and follows the `assume false;` convention)
- `verus-examples:guide/strings` (translation is source-close; the current difference is the missing `String_string` / string-library model support in Strata. The local `fn main(){}` source edit (uncommitted, in `verus/examples/guide/strings.rs`) unblocks Verus export — Stage 1 reports `5 verified, 0 errors` — and Stage 3 surfaces the documented `Expression has type String_string when string expected` failure)
- `verus-examples:impl_basic` (structs, methods, generics, ensures clauses preserved)
- `verus-examples:nevd_script` (`nat`-typed recursive functions, measures, and call boundaries lower through the modeled `nat.toInt` / `nat.fromInt` / `nat.*` API; scalar crossings use native `as_int`)
- `verus-examples:overflow` (`[MODEL-missing-types]`: `Arithmetic_overflow` not modelled in Strata; the translator preserves source-level checked-overflow operations like `checked_u64_constants`/`checked_u64_calculations` and emits `var w : Arithmetic_overflow` parameters that Strata cannot resolve)
- `verus-examples:power_of_2` (Strata type error: `int` literals where `nat` expected)
- `verus-examples:prelude` (`seq!` lowers through `Sequence.empty`/`Sequence.build`; the remaining mismatch is Strata's current `Sequence` frontend/indexing support)
- `verus-examples:proposal-rw2022` (`fibo` and its scalar call boundaries use the modeled nat API plus native `as_int`; termination-check artifacts (`decrease%init*`, `CheckDecrease*`) are correctly stripped. Verus writes `proposal_rw2022.json` (underscored crate name, since Rust forbids `-`); `run_tests.sh::run_verus_export` also tries the underscore-normalized filename)
- `verus-examples:quantifiers` (typing flows through modeled `nat.toInt` and native `as_int`; `nat_nonneg` proves the non-negativity half of the universal assertion, while the remaining `tr(nat.toInt(i))` predicate stays uninterpreted and cvc5-hard)
- `verus-examples:recursive_types` (translation appears source-close; Strata-side blocker is nested datatype shape unsupported in current Strata typechecker)
- `verus-examples:rw2022_script` (`is_prime` and `fibo` use the modeled nat API; prime-testing quantifier/trigger structure and `rec function fibo` with its decreases clause are preserved)
- `verus-examples:statements` (mixed-width bitvector arithmetic uses native interpreted `as_int`/`as_bv`, so the widened loop invariant discharges; 23✅ with only the hard nonlinear `measure_decrease_0` timing out)
- `verus-examples:test` (translation faithful: small bv64 procedure `foo` with `requires a < bv{64}(100)` and `_pct_return := a + bv{64}(1)`, plus a `main` that exercises it. Verify SKIP — Strata-side dispatch gap on this shape, no translator defect)
- `verus-examples:trigger_loops` (uninterpreted fns + multi-trigger quantifier patterns preserved; `[TRANS-choose]`: source `choose|z| g(z)` in `choose_example`/`quantifier_example` is parsed as `Bind.Lambda [z]` with the predicate erased. In `tests/ignored_tests.txt` as `UPSTREAM-IGNORE + HANG` — file is upstream-marked `ignore`; skipped silently)
- `vlir-tests:crypto_noref` (concrete and polymorphic empty sequences emit typed forms, including `Sequence.empty<T>()`. Tuple projections inside the `map_values` XOR closures now route through monomorphic `Tuple2_proj_*` helpers, so the prior direct-selector `T1 when T0 expected` failure is gone. Verification is currently blocked downstream by Strata's unsupported polymorphic `Sequence.empty<T>()` expression in `Vec_from_elem`)
- `vlir-tests:datatypes` (current difference is only that Strata still type-fails later in the pipeline)
- `vlir-tests:demo_for` (verify SKIP (Sequence): Boole output recovers the source-level `for` loop shape; blocked by Strata's Sequence frontend/indexing support)
- `vlir-tests:demo_while_loop_isolation` (`Vec<u64>` find-max with explicit `loop_isolation` enabled; loop-index uses lower through `[TRANS-loop-counter-int]`, so indexing is expressed directly over `Sequence.length`/`Sequence.select`; structurally identical to `demo_while`)
- `vlir-tests:demo_while` (`Vec<u64>` find-max with `#[verifier::loop_isolation(false)]`; loop-index uses lower through `[TRANS-loop-counter-int]`, so indexing is expressed directly over `Sequence.length`/`Sequence.select`)
- `vlir-tests:demo` (verify SKIP (Sequence): Boole output is source-close and elaborates cleanly; blocked by Strata's Sequence frontend/indexing support)
- `vlir-tests:FindMax` (`Vec<i32>` find-max via `Sequence bv32`; loop-index uses lower through `[TRANS-loop-counter-int]`; value comparisons remain signed bv32 comparisons such as `>=s`)
- `vlir-tests:integer_ring` (Strata type error on intentionally-failing `type_fail`; cvc5 also times out on `wide_mul` ensures — non-linear bv64 multiplication beyond solver default budget)
- `vlir-tests:LoopSimple` (`i32` summation loop; decreases and invariant arithmetic use native interpreted `as_sint`; signed comparisons `<s`/`<=s` lower to Strata Core signed-bv ops and **verify: 9/13 ✅ (2026-06-22)**; the residual 4 failures are nonlinear-arith cvc5 timeouts (`measure_decrease_0`), not a lowering gap)
- `vlir-tests:LoopSimpleWithSpec` (source-close nat recursive specification, loop invariant/decreases, overflow assertions, and proof procedure; Strata still times out on hard obligations, so its outcome differs from Verus)
- `vlir-tests:b1_boundary_proved` (source-close Dalek boundary variant, including its trusted source assumptions; Strata leaves obligations open while Verus passes)
- `vlir-tests:b1_full` (emission is source-close, but the generated Lean/Strata program currently hits a stack overflow before verification completes)
- `vlir-tests:b1_minimal` (source-close Dalek B1 reduction, including source `admit`/trusted assumptions; Strata leaves obligations open while Verus passes)
- `vlir-tests:b2_minimal` (source-close Dalek B2 reduction, including source trusted assumptions; Strata leaves obligations open while Verus passes)
- `vlir-tests:b2_minimal_upstream` (source-close upstream-style Dalek B2 reduction; Strata leaves obligations open while Verus passes)
- `vlir-tests:mutual_recursion` (Boole output is a source-close `rec function is_odd ... function is_even ...` block. The `.mutualBlock` Boole-translation arm threads the source `decreases abs(i)` measure; Boole emits `rec function is_odd … decreases abs(i)` and Strata's int-termination checker passes all `is_even_terminates_*` obligations. Translation faithful and termination-clean. The only residual `even_odd_mod2_ensures_*` failures are an *expected Strata encoding limitation*: int-recursive fns are pure UFs with no definitional axiom, so the solver cannot prove the inductive `is_even(i) <==> i%2==0` ensures — not a translator defect)
- `vlir-tests:nonlinear` (bv operands use native interpreted `as_int`, while nat obligations use the modeled nat API; remaining open obligations are nonlinear solver-hard rather than blocked by opaque coercions)
- `vlir-tests:proof_fn` (translation faithful: `function p (u : bv64) : bool` and `function min (x : int, y : int) : int` declared with bodies, lemma-style procedures lower to spec-only `procedure ... ensures ... { exit ... }` shape. Verify SKIP — Strata-side dispatch gap, no translator defect)
- `vlir-tests:quant` (mixed `int`/`nat` quantifier patterns like `∀ x : int, y : nat :: x + y == y + x` produce direct `+` on mismatched types that Strata's typechecker rejects; also affected by `[TRANS-trigger-annotation]` (source `#[trigger]` annotations stripped); the source `as a1`/`a2`/`a3` labels are now preserved)
- `vlir-tests:recursion` (Boole-side translation faithful. The mutual-block decreases applies here — `rec function M_is_odd … decreases M_abs(i)` is emitted and most `*_terminates_*` obligations pass. Residual `M_is_odd_terminates_1` fails: source uses a *lexicographic* measure (`decreases abs(i), 0int`) to break the same-argument `M_is_odd(i) → M_is_even(i)` edge, but the translator collapses lex-decreases to the head term, leaving that edge with no strict decrease under #1167's per-call-site obligation. Lex-collapse limitation exposed by enforced int-termination; full fix waits on Strata tuple-measure support. Same applies to `verus-examples:guide__recursion`)
- `vlir-tests:rec_adt_structural` (nat emitted as abstract type via `[MODEL-missing-types]`; waiting for Strata native nat support)
- `vlir-tests:test_requires` (translation faithful: `[bitvector_query]` and `[nonlinear_query]` proof-mode labels preserved on the `test_success` and `bound_check` assertions. Verify SKIP — Strata-side dispatch for these proof-mode labels is incomplete on this case, mirroring `guide/nonlinear_bitvec`)
- `vlir-tests:vec_ops` (verify SKIP (Sequence): Vec operations lower through Sequence prelude; blocked by Strata's Sequence frontend/indexing support)

## not faithful translation (56)
- `verus-examples:assert_by_compute` (`[VERIFY-lambda-encoding]` for lambdas in `Seq::new`-style spec functions; `assert(...) by (compute_only)` lowers to `assume <pre-computed-result>;` directly. Nat expressions use the modeled nat API, and concrete and polymorphic empty sequences emit typed forms)
- `verus-examples:atomics` (`[TRANS-atomic-ghost-scaffolding]`: `struct_with_invariants!` / `atomic_with_ghost!` still lower to low-level `Invariant_*`, `Atomic_*`, and `assume` scaffolding; `[MODEL-missing-types]` (`Atomic_ghost`))
- `verus-examples:basic_lock1` (`[TRANS-atomic-ghost-scaffolding]`: `InvariantPredicate` impl + `open_local_invariant!` lower to `Invariant_*`/`Atomic_*`/`Cell_*` helper scaffolding; `[MODEL-missing-types]` — `Atomic`, `Cell`, `Invariant`)
- `verus-examples:basic_lock2` (`[TRANS-atomic-ghost-scaffolding]`: `struct_with_invariants!` flattens to `Atomic_ghost_*`/`Cell_*` helpers; `[MODEL-missing-types]` — `Atomic_ghost`, `PCell`)
- `verus-examples:bitmap` (`[VERIFY-lambda-encoding]` in `u64_view`; `[TRANS-extensional-eq]` still expands source `=~=` and `assert_seqs_equal!`. The `BitMap` API (`view`, `from`, `get_bit`, `set_bit`, `or`) is emitted as `Impl__0_view`/`Impl__0_from`/`Impl__0_get_bit`/`Impl__0_set_bit`/`Impl__0_or` procedures.)
- `verus-examples:bitvector_garbage_collection` (`[VERIFY-lambda-encoding]` in `bucket_view`; `[TRANS-extensional-eq]` still expands source `=~=` away to explicit formulas; raw Core also currently hits nat/int typing around `Seq_new`)
- `verus-examples:datatypes` (`Box::new(t)` lowers to `call v := Boxed_new(t)` — an external-body identity wrapper procedure (`ensures v == t; { assume false; }`), so semantically identity but syntactically a procedure call rather than literal erasure; `[TRANS-reveal-with-fuel]` discards source `reveal_with_fuel(f, n)` annotations; loop/match lowering not yet source-close enough)
- `verus-examples:debug_expand` (`[TRANS-hide]`, `[TRANS-closed-visibility]`)
- `verus-examples:doubly_linked_xor` (pointer-heavy XOR linked list; `[MODEL-missing-types]` — `Simple_pptr`; `[TRANS-ghost-tracked-erasure]` for `Tracked`/`Ghost` wrappers; `external_body` proof with `unimplemented!()` in source)
- `verus-examples:doubly_linked` (`[MODEL-missing-types]` — `Simple_pptr`, `Raw_ptr`, plus `Doubly_linked_list_node`/`ghostState`/`doublyLinkedList`/`iterator` datatypes; `[TRANS-ghost-tracked-erasure]` for `Tracked`/`Ghost` wrappers; pointer arithmetic and `next`/`prev` chasing not yet source-close)
- `verus-examples:even_cell` (`[TRANS-atomic-ghost-scaffolding]`: `open_local_invariant!` flattened to `Invariant_create_open_invariant_credit`/etc. helpers; `[MODEL-missing-types]` — `Cell`, `LocalInvariant`)
- `verus-examples:exec_termination_example` (source has basic recursive `exec` fns and while loops with `decreases` clauses on bare `int`. Verify fails on iterator/range desugaring artifacts (`error: Undeclared type or category Ops_Range_range`, `Unknown expr identifier VERUS_iter`) from the `exec_for_loop` arms — orthogonal to `[CORE-decreases]`. The local `fn main(){}` source edit (uncommitted, in `verus/examples/exec_termination_example.rs`) unblocks Verus export — Stage 1 reports `14 verified, 0 errors` — and Stage 3 surfaces the same iterator-lowering gap rather than hiding behind `E0601`)
- `verus-examples:extensionality` (`[TRANS-extensional-eq]` expands `assert_seqs_equal!`, `assert_maps_equal!`, and `assert_sets_equal!` into low-level proof scaffolding and explicit formulas; `[VERIFY-lambda-encoding]` and `[TRANS-higher-order-collection-stubs]` still affect `Map::total`, `Map::new`, and `Set::new`; raw Core also currently hits a Strata-side `Sequence` indexing type error in `are_equal`)
- `verus-examples:float` (`[TRANS-float-unsupported]`: source `f64`/`f32` literals lower to `Unsupported.Float64` placeholders in emitted Boole; floating-point types/operations not yet translated)
- `verus-examples:guide/assert_by_compute` (`range_property` still uses uninterpreted `Compute_all_spec` plus `[VERIFY-lambda-encoding]`; recursive nat functions use the modeled nat API, and the polymorphic-empty-sequence blocker is resolved)
- `verus-examples:guide/bst_map_generic` (BST-as-map with generic key/value; emits `Map_empty`, `Map_lib_union_prefer_right`, `Map_insert` cleanly — `[TRANS-fuel-parameter-leakage]` does not apply here. Remaining gap: classification holds via solver-side reasoning about generic recursive datatypes — `[VERIFY-generic-typevar-ddm]`-adjacent issues likely)
- `verus-examples:guide/bst_map_type_invariant` (BST-as-map with type-invariant constraint; same Map operations emitted cleanly; remaining gap is solver-side reasoning about the type invariant under recursive operations)
- `verus-examples:guide/bst_map` (concrete BST-as-map for `u64 -> bool`; emits `Map_empty`, `Map_lib_union_prefer_right`, `Map_insert` and `Impl__0_as_map`/`Impl__0_optional_as_map` accessors cleanly — `[TRANS-fuel-parameter-leakage]` does not apply. Remaining gap is solver-side reasoning about recursive structural properties)
- `verus-examples:guide/const` (the source exec constant `E` calls `const fn e()`, but both lower to the same Boole procedure name `e`; the emitted wrapper recursively calls itself instead of the source const function, so the passing output is not faithful)
- `verus-examples:guide/exec_attr` (`test_for_loop` still has `[VERIFY-lambda-encoding]` in the loop invariant; `proof_decl!` / `proof_with!` / `Ghost` / `Tracked` wrappers are flattened under `[TRANS-ghost-tracked-erasure]`. The local `fn main(){}` source edit (uncommitted, in `verus/examples/guide/exec_attr.rs`) unblocks Verus export — Stage 1 reports `8 verified, 0 errors`)
- `verus-examples:guide/exec_spec_unverified` (`[TRANS-exec-spec-helper-leakage]`: the `exec_spec_unverified!` example lowers through internal `View_deep_view` / `exec_*` helper stubs and a distorted `Map int execPoint` representation rather than preserving the source macro structure)
- `verus-examples:guide/exec_spec_verified` (`[TRANS-exec-spec-helper-leakage]`: the `exec_spec_verified!` example leaks internal `View_deep_view`, `View_V`, `Contrib_Exec_spec_*`, and slice/array helper stubs instead of source-like `deep_view` / `as_slice` reasoning)
- `verus-examples:guide/external_trait_specs` (`[TRANS-trait-unsupported]`:
  the concrete `summary` call dispatches to `Impl__0_summary`, but the
  abstract `Summarizer_summary` obligation still hits a type-var SMT encoding
  error; the impl/assert obligations also include cvc5 timeouts. Raw Core also
  currently hits a bv64/int comparison mismatch in `test_hasher`)
- `verus-examples:guide/ext_equal` (`[VERIFY-lambda-encoding]`; direct `Seq`/`Set`/struct extensionality lowers to explicit formulas, but raw Core still expands away source `=~=`/`=~~=` syntax; polymorphic empty sequences emit `Sequence.empty<T>()`)
- `verus-examples:guide/higher_order_fns` (`[TRANS-exec-closure-scaffolding]`; the polymorphic-empty-sequence blocker in the captured-closure example is resolved)
- `verus-examples:guide/invariants` (`[TRANS-extensional-eq]`: source `assert(operations@.take(i as int) =~= ...)` is expanded to plain `==`; fib-loop invariants use native scalar casts and the modeled nat API)
- `verus-examples:guide/lib_examples` (`[VERIFY-lambda-encoding]` in returned/captured function values and collection constructors; the current Vec translation is the datatype-based path, and empty sequences emit typed forms)
- `verus-examples:guide/quants` (`[TRANS-reveal-with-fuel]`; the multi-binder choose-let and choose-in-argument shapes emit faithfully. 149 obligations: 129 ✅ / 7 SMT encoding errors / 13 ⌛; the encoding errors are the `assert_81` / `assume_82` `Sequence.update`/`Sequence.select` obligations)
- `verus-examples:guide/recursion` (`[TRANS-reveal-with-fuel]`: `M_test_even`/`M_test_odd` lower their `reveal(M_is_even)`/`reveal(M_is_odd)` calls to globally-scoped `assume ∀ i :: M_is_even(i) == ...` — fuel amount discarded)
- `verus-examples:invariants` (`[TRANS-atomic-ghost-scaffolding]`: `open_atomic_invariant!` flattened to helper-call scaffolding; `[MODEL-missing-types]` — `AtomicInvariant`)
- `verus-examples:mergesort` (source `=~=` proof steps are flattened under `[TRANS-extensional-eq]`; the final `lemma_sorted_unique(..., |a, b| a <= b)` call still hits `[VERIFY-lambda-encoding]`)
- `verus-examples:modules` (`[TRANS-closed-visibility]`)
- `verus-examples:multiset` (`broadcast use group_to_multiset_ensures` ignored; multiset extensionality still lowers to plain equality; `[VERIFY-lambda-encoding]` still affects the `sort_by` comparator)
- `verus-examples:playground` (translator-side ill-scoped variable: synthetic temp symbol referenced before it is in the bvar/fvar context; produces a Strata typecheck error from a malformed program rather than a Strata-side limitation)
- `verus-examples:recommends` (`[TRANS-reveal-with-fuel]`: `seq_max_int`'s local reveal lowers to `assume ∀ s : (Sequence int) :: seq_max_int(s) == ...` global reveal; source `spec_affirm(...)` steps in `some_predicate` are erased. Sequence-length expressions use clean `Sequence.length(s)`)
- `verus-examples:recursion` (`[TRANS-reveal-with-fuel]`; Boole output recovers the `for` loop shape, but the source-level fuel behavior is still not preserved)
- `verus-examples:rfmig_script` (`[MODEL-missing-types]` still blocks `Simple_pptr`; the current Vec pieces use the datatype-based path directly)
- `verus-examples:rwlock_vstd` (`[VERIFY-lambda-encoding]` in the `Ghost(|v| ...)` lock invariant; raw Core also currently collapses `RwLock`/handle operations to undeclared model types under `[MODEL-missing-types]`)
- `verus-examples:set_from_vec` (`set` extensionality still expands away under `[TRANS-extensional-eq]`)
- `verus-examples:statics` (`[TRANS-atomic-ghost-scaffolding]`: the `Lazy` / `atomic_with_ghost!` encoding still lowers to low-level `Atomic_ghost_*`, `Invariant_*`, `Cell_*`, and `assume` scaffolding rather than source-like lazy-static structure; `[MODEL-missing-types]` (`Cell`, `Atomic_ghost`))
- `verus-examples:syntax_attr` (`#[verus_spec(with ...)]`, `proof!`, and tracked/ghost wrapper syntax are still flattened under `[TRANS-ghost-tracked-erasure]`; raw Core also currently hits Strata's polymorphic tuple-helper DDM panic)
- `verus-examples:syntax` (`[TRANS-choose]` in `test_choose`; `[TRANS-ghost-tracked-erasure]`; `test_views` uses the datatype-based Vec path directly; `[TRANS-broadcast-use]`)
- `verus-examples:test_expand_errors` (`[TRANS-hide]`, `[TRANS-reveal-with-fuel]`)
- `verus-examples:thread` (`[TRANS-exec-closure-scaffolding]`; `[MODEL-missing-types]` (`Thread`) through the closure requirement encoding)
- `verus-examples:traits` (`[TRANS-trait-unsupported]`: concrete calls
  dispatch to `Impl__0_f`, but generic trait calls still target abstract `T_f`
  and the wrapper still type-checks with bv64/int mismatches; commented out of
  `working_tests.txt` as a known issue)
- `verus-examples:trait_for_fn` (`[TRANS-trait-unsupported]`: the
  `impl IntFn for spec_fn(int) -> int` body `self(x)` is preserved and
  `f.call_int(2)` dispatches to `Impl__0_call_int(f, 2)`, but Strata cannot SMT
  encode `Impl__0_call_int` because its `self` parameter has function type)
- `verus-examples:vectors` (`datatype Vec` path is source-close; `pusher` still hits `[VERIFY-lambda-encoding]` and `[TRANS-extensional-eq]`)
- `verus-examples:verified_vec` (In `tests/ignored_tests.txt` as `UPSTREAM-IGNORE`. Verus errors with `E0432: unresolved import vstd::ptr` — upstream Verus marked this example `ignore` (line 1 of the source: *"intending to deprecate PPtr, should update this to raw_ptr"*) because vstd no longer exposes `vstd::ptr`; the example uses the deprecated `PPtr` API. Either port to `vstd::simple_pptr` or wait for upstream port to `vstd::raw_ptr`)
- `vlir-tests:b3_minimal` (currently verifies, but source `pub closed spec fn edwards_{x,y,z,t}` bodies are emitted globally visible; `[TRANS-closed-visibility]`)
- `vlir-tests:b4_minimal` (currently verifies and preserves native `choose`, but source `pub closed spec fn edwards_{x,y,z,t}` bodies are emitted globally visible; `[TRANS-closed-visibility]`)
- `vlir-tests:b5_minimal` (the associated output type resolves to
  `montgomeryPoint`, and the exec call targets VLIR's resolved
  `Impl__13_mul`; verification status is still solver-heavy)
- `vlir-tests:maps` (`[VERIFY-lambda-encoding]` in `mk_map` lambdas; `[TRANS-higher-order-collection-stubs]` currently distorts `Set_mk_map`; raw Core map equalities are still emitted as plain `==` rather than source-like map extensional equality)
- `vlir-tests:mini_c` (Boole now emits valid `Tuple2` selectors, drops unit-valued match temporaries / declares `Unit` when needed, and declares `Set` for `Map_dom`; verification is blocked downstream by Strata's unsupported `strLit` expression for string literals)
- `vlir-tests:seqs` (`[VERIFY-lambda-encoding]` in `Seq::new`, `Seq::map`, `Seq::filter`, and `seq![x; n]`; `[TRANS-extensional-eq]` still expands source `===` away to raw Core equality; empty sequences emit typed forms, while other generic/nat typing gaps remain)
- `vlir-tests:sets` (`[VERIFY-lambda-encoding]` in `Set::new`, `Set::filter`, `Set::map`, `set_map`, and `fold`; `[TRANS-higher-order-collection-stubs]` distorts `Set_new`, `Set_filter`, `Set_lib_map`, and `Set_Fold_fold`; `[TRANS-extensional-eq]` still expands source `===` away to raw Core equality; `s.choose()` is currently just uninterpreted `Set_choose` without witness semantics`)
- `vlir-tests:test_vstd` (`[VERIFY-lambda-encoding]` in `Set_new(fun i => ...)`, `Map_new(fun i => ..., fun i => ...)`, `Seq_new(5, fun i => ...)`; fixed-size array literals lower to concrete `Sequence.empty`/`Sequence.build` chains)
## Gap Index

### `[TRANS-generic-reveal]` Generic `reveal` support
- Non-generic opaque spec functions are emitted declaration-only.
  `reveal(f)` becomes `assume forall params :: f(params) == body;`.
- Generic `reveal(g)` is dropped because Verus erases type arguments from
  `Fuel` at SST level.
- Affects: `verus-examples:generics`

### `[TRANS-hide]` `hide` not supported
- `hide(f)` is not emitted, so the function body remains visible to the solver.
- Affects: `verus-examples:test_expand_errors`, `verus-examples:debug_expand`

### `[TRANS-reveal-with-fuel]` `reveal_with_fuel` loses fuel/locality
- `reveal_with_fuel(f, n)` is lowered to the same kind of global
  definitional `assume forall` used for `reveal(f)`, discarding the fuel amount
  `n` and strengthening what was source-level local proof context.
- Affects: `verus-examples:test_expand_errors`, `verus-examples:recursion`,
  `verus-examples:guide/quants`, `verus-examples:datatypes`,
  `verus-examples:recommends`

### `[TRANS-fuel-parameter-leakage]` Source `Map` operations leaked synthetic `Fuel` parameters (RESOLVED)
- **Resolved**: emitted Boole shows clean `Map_empty`,
  `Map_lib_union_prefer_right`, `Map_insert` signatures with no `Fuel`
  parameter leakage. Verified against `guide/bst_map`,
  `guide/bst_map_generic`, `guide/bst_map_type_invariant` outputs.

### `[TRANS-closed-visibility]` `closed` spec fn visibility not enforced
- `pub closed spec fn` is translated with its body visible to callers in other
  modules.
- Affects: `verus-examples:modules`, `verus-examples:debug_expand`

### `[CORE-decreases]` `decreases` preservation
- **Loop-level**: emitted in concrete `while ... decreases ...` /
  `for ... decreases ...` syntax in both Core and Boole.  Core's
  `Stmt.loop`'s `measure : Option P.Expr` is populated faithfully.
  For-loop measure ships on the Boole side.
  `for_to_by_statement` / `for_down_to_by_statement` carry
  `decr : Option Measure` upstream, and our translator's for-loop
  recovery branch threads the source `decreases` head term into
  the slot via `decreasesToMeasureAnn`.  Verus' auto-synthesized
  `Pervasive_ghost_decrease(iter)`
  shape is filtered via the `expContainsGhostPervasiveCall`
  walker so it doesn't leak as an unresolved fvar.  Verified on
  `tests/VerusFiles/demo_for.rs` (`for i in 1..v.len() decreases
  v.len() - i`).
- **Function/procedure-level `decreases`**: shipped on the Boole side.
  The translator preserves Verus' `local_decls_decreases_init`
  through JSON parsing onto `ProofFn.decreases` / `ExecFn.decreases`,
  then lowers the head term into Boole's `Option Measure` slot on
  `boole_procedure`.  Verus-internal artifacts (`decrease%init*`,
  `CheckDecrease*`) are stripped from bodies.
  Lex-decreases (multiple terms) collapse to the head; full
  lexicographic support waits on Strata accepting a tuple measure.
- Strata side closed; gap is translator-side
  for recursive *spec* fns.  Strata checks int-valued termination:
  `decreases <int expr>` generates
  non-negativity + strict-decrease obligations instead of being
  ignored.  So procedure-level / loop-level measures the translator
  emits are *enforced*, not just AST-present.  The
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
- **Structural (datatype-measured) `decreases` — resolved (2026-06-24).** When the
  measure is a parameter of user-datatype type, Strata classifies it as
  structural recursion and requires the decreasing parameter to carry `@[cases]`
  (int measures do not). `specFnToBoole` and the mutual-rec path now read the
  parser's `recursiveCasesIdxHint` (the decreasing-parameter index, with
  `Box`/`HasType` wrappers already peeled), gate it on the parameter being a
  `Struct`/`Enum`, and emit that binding as `casesBinding` — dropping the
  datatype `decreases`, since `@[cases]` carries termination via Strata's
  `adtRank` and generates the per-constructor unfolding axioms.
  `unit_tests/structural_recursion.rs` verifies 9/9 (termination + `len` values).
  `mutual_recursion_datatypes.rs` (mutual datatypes) now also verifies 13/13:
  emitting the datatype SCC as one `command_datatypes` block (`mergeDatatypeCommands`
  in `Translate.lean`) resolves the `tree ↔ forest` forward reference, separate
  from the termination markers.

### `[TRANS-return-comment]` Early return rendered as comment (Core-only)
- This is a Core-pipeline-only workaround: Verus SST encodes `return expr;`
  as `ret_var := expr; assume false;`, and the Core printer renders the pair
  back as `// return expr;` because Strata Core has no native return.
- **Resolved for Boole**: Strata Boole has native `exit <ProcedureName>;`,
  which the translator emits directly (see e.g.
  `tests/BoolePrograms/verus-examples/imo_1988_6.lean`'s many
  `exit is_perfect_square;` sites). No `// return` comments appear in any
  Boole output.
- Tracked here only as a raw-Core legacy note. For the
  affected tests (`vlir-tests:basic_failure`,
  `verus-examples:guide/requires_ensures{,_edit}`,
  `verus-examples:imo_1988_6`, `verus-examples:guide/invariants`,
  `verus-examples:set_from_vec`), the Boole output is faithful.

### `[TRANS-hastype-overflow]` Numeric `HasType` overflow guards (RESOLVED)
- Resolved: `hasTypeRangeCond` lowers numeric `HasType` to explicit int-domain
  range predicates for both asserts and assumes, preserving overflow VCs and
  the checked-range facts used by later obligations.
- Non-numeric `HasType` remains omitted as a typing tautology.
- Validated on `b1_full`; see `docs/numeric-domains.html`.

### `[TRANS-extensional-eq]` Extensional / deep-equality surface syntax not preserved
- Source-level extensionality syntax such as `===`, `=~=`, `=~~=`, and
  `assert_seqs_equal!` / `assert_maps_equal!` / `assert_sets_equal!` is
  expanded away in emitted Core/Boole output.
- Supported `Seq`, `Set`, `Map`, `spec_fn`, and `#[verifier::ext_equal]`
  struct cases lower to explicit extensional formulas rather than
  collapsing to plain spec equality, but the original surface notation is not
  preserved as future Strata syntax. Unsupported higher-order cases can
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
  for non-generic spec functions. Generic `Fuel` dropped.

### `[TRANS-widening-casts]` Widening casts inserted at call, variable, and composite sites
- Verus erases widening casts (`nat as int`, `u16 as int`) at SST level.
- Type-directed coercion insertion adds interpreted bv→nat/int conversions
  at function/procedure call sites.
- Type-directed coercion insertion also preserves source-typed quantifier
  binders and inserts native `as_bv64` casts at plain variable use sites when the
  current `usize`/indexing context expects `bv64`.
- Composite result sites coerce too: struct/enum field projections and tuple
  projections compare the field's numeric kind against the expected kind and
  insert a result-side cast when they differ (e.g. `p.a as int` on `p.a : u16`
  emits `as_uint(pair..a(p))`). Arithmetic built from such projections then
  widens through the operand path, so `p.a as int + p.b as int` stays in `int`
  with no `bv16` wrap. The bv→int step is idempotent (`bexprIsKnownInt`
  recognizes native `as_uint`/`as_sint`), so an operand a caller already widened
  is not double-cast. Closed bitvector tuple fields go through the monomorphic
  `Tuple2_proj_*` helper (see the tuple-selector note in the projection commit).
- Tuple literals decompose a known tuple `expected?` into per-element types and
  push each onto the corresponding element, so a widened element with no
  `Box{Int}` wrapper (a bare projection/variable) is coerced to the slot type:
  `(p.a as u32, p.b as u32)` emits `Tuple2_ctor_2(as_bv32(as_uint(pair..a(p))),
  …)` typed `Tuple2 bv32 bv32`, instead of leaving `bv16` values in `bv32`
  fields. Mirrors the `StructCtor` / `ArrayLiteral` element-type propagation.
- Lambda applications (`CallLambda`) recover the applied function's parameter
  types from its `SpecFn` type and push each onto the corresponding argument, so
  a widened argument coerces to the parameter type: `f(a as int)` with
  `f : spec_fn(int) -> int` and `a : u16` emits `f(as_uint(a))` instead of
  passing a `bv16` to an `int` parameter. The result side already coerces through
  the surrounding `Box`/`Unbox` cast wrapper.
- Exercised by `verus-examples:guide/integers`, `verus-examples:quantifiers`,
  `verus-examples:statements`; minimal repro at
  `tests/VerusFiles/repros/widening_composite.rs`.
- **Remaining gaps**:
  - A concrete bitvector field inside a type-parameterized tuple keeps a
    type-variable selector (it escapes the monomorphic helper), so a width cast
    on it is deferred rather than emitted — tracked with the generic
    type-variable casts under `[VERIFY-generic-typevar-ddm]`. Likewise, an
    `int`/`nat` tuple field's polymorphic selector is not yet monomorphized, so
    *consuming* such a field (e.g. `(x as int, …).0`) hits the same Strata
    selector-typing limit even though the tuple's *construction* is well-typed.
  - Cast insertion across a spec-level lambda application is complete (arguments
    coerce to the parameter type, results through the cast wrapper), so the
    emitted Boole type-checks; what remains is downstream — *proving* properties
    through the application is limited by Strata's lambda encoding
    (`[VERIFY-lambda-encoding]`), as an obligation that depends on beta-reducing
    the applied lambda still fails.

### `[TRANS-coercion-uninterpreted]` Legacy uninterpreted coercions (RESOLVED)
- Resolved: bv↔int and bv-width casts use Strata's interpreted `as_int`,
  `as_sint`, and `as_bv<w>` constructs. Nat↔int uses the modeled
  `nat.toInt` / `nat.fromInt` prelude functions and round-trip axioms.
- Remaining coercion work is type-directed insertion in composite contexts and
  generic type-variable casts, tracked under `[TRANS-widening-casts]` and
  `[VERIFY-generic-typevar-ddm]`.

### `[VERIFY-generic-typevar-ddm]` Strata still rejects some generic typed operations
- The translator emits faithful generic helper bodies such as
  `Vec_len<T>` / `Vec_index<T>` in the Vec prelude, rather than monomorphic
  wrappers.
- Some Vec-heavy or otherwise generic examples then hit current Strata
  DDM/SMT encoding limits on type variables, even though the translation shape
  is more source-faithful.
- Affects: `vlir-tests:FindMax`, `vlir-tests:demo_while`,
  `vlir-tests:demo_while_loop_isolation`, `verus-examples:generics`

### `[VERIFY-sequence-empty-polymorphic]` Polymorphic `Sequence.empty<A>` (surface resolved; SMT-encode open)
- **Surface/translation resolved:** `Bld.seqEmpty` / `seqEmptyExpr` fall back to
  Core's polymorphic `seq_empty<A>()` production, printing
  `Sequence.empty<T>()` for generic element types, so it is valid Boole rather
  than a translation-time error.
- **SMT encoding still open:** the Strata SMT encoder does not encode the
  polymorphic `seq_empty<T>` constant — it emits `Unsupported expression:
  Strata.BooleDDM.Expr.seq_empty` (the same grammar-accepts / encoder-rejects
  shape as `[VERIFY-lambda-encoding]`). This blocks `vlir-tests:crypto_noref`
  in the generic `Vec_from_elem<T>` helper once the tuple-selector typing is
  fixed. A translation-side workaround would monomorphize the concrete
  instantiation to a typed `Sequence.empty_bv8` (mirroring the `Tuple2_proj_*`
  helper).

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
- `exec_spec_unverified!` and `exec_spec_verified!` examples expose
  internal helper symbols such as `View_deep_view`, `View_V`,
  `Contrib_Exec_spec_*`, and array/slice glue procedures rather than a
  source-like surface encoding of `deep_view`, `as_slice`, and the exec/spec
  wrapper itself.
- Affects: `verus-examples:guide/exec_spec_unverified`,
  `verus-examples:guide/exec_spec_verified`

### `[TRANS-seq-len-literal-typing]` Sequence-length expressions used to mix `nat` and `bv` (RESOLVED)
- **Resolved**: emitted Boole uses `Sequence.length(s) == 5` (built-in
  `Sequence.length` returns `int`), no nat/bv mismatch. Verified against
  `guide/pervasive_example` and `recommends` outputs.

### `[TRANS-higher-order-collection-stubs]` Higher-order collection APIs lowered to distorted first-order stubs
- Some collection constructors and operators that should take predicates or
  function values are emitted as first-order stubs with distorted
  signatures in order to accommodate `Unsupported.lambda`.
- Examples include `Set_new`, `Set_filter`, `Set_lib_map`, `Set_Fold_fold`,
  `Set_mk_map`, `Map_new`, and `Map_total`.
- Affects: `verus-examples:extensionality`, `vlir-tests:maps`,
  `vlir-tests:sets`

### `[TRANS-exec-closure-scaffolding]` Exec closures lowered to first-order scaffolding
- Exec higher-order code lowers closures to synthetic datatypes and
  contracts such as `anonymous_closure_*`, `ClosureReq`, `ClosureEns`, and
  helper calls like `Pervasive_exec_nonstatic_call`.
- This is distinct from plain lambda placeholders: the emitted shape already
  commits to a first-order closure encoding rather than a future source-like
  closure syntax.
- Affects: `verus-examples:guide/higher_order_fns`, `verus-examples:thread`

### `[TRANS-trait-unsupported]` Traits not faithfully translated
- The translator has partial `resolved_method` support: statement and
  expression calls dispatch to an already-parsed in-crate impl selected by
  Verus trait resolution. This fixes concrete call sites such as
  `trait_for_fn`'s `f.call_int(2)`, `traits`' direct `Impl__0_f` call,
  `guide/external_trait_specs`' `Impl__0_summary` call, and B5's
  `Impl__13_mul` call.
- Traits are still not fully source-faithful. Concrete losses observable:
  - **Generic trait dispatch remains abstract.** Calls through type parameters
    still target the abstract trait procedure/function, e.g. `T_f` in
    `verus-examples:traits`.
  - **Higher-order impl methods expose SMT gaps.** `trait_for_fn` preserves
    `Impl__0_call_int(self, x) { self(x) }`, but Strata cannot encode a
    non-inline function with a function-typed `self` parameter.
  - **Abstract trait obligations remain problematic.** Even when a concrete
    call dispatches to the impl, abstract trait declarations/obligations can
    still be emitted and may hit type-var SMT encoding errors, as in
    `guide/external_trait_specs`.
  - **Resolved dispatch is single-pass.** A resolved impl is selected only if
    its declaration has already been parsed; calls to later impl declarations
    still remain abstract until declaration indexing becomes two-pass.
  - **External trait specs degrade across modules.** Uses of
    `#[verifier::external_trait_specification]` still produce low-level helper
    names and mismatched coercion shapes when crossed across module
    boundaries.
- Treat any test that defines a `trait` or relies on trait-method
  dispatch as requiring manual review unless it has a specific passing audit.
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

### `[TRANS-assert-label]` Source `as <name>` assertion labels (RESOLVED)
- Verus syntax `assert(P) by (lean_proof as a1)` carries an explicit label
  `a1` that names the obligation; Boole has matching surface syntax
  (`assert [a1]: P;`).
- **Resolved:** the `AssertLean` parser reads the label from the JSON
  `mode: {"Proof": <name>}` and preserves it as a named query
  (`.AssertQuery (.Other <name>) (.AssertLean …)`); `assertQueryModeLabel`
  returns the `.Other` name, so the emitter produces `assert [a1]: P;`.
  Verified on `vlir-tests:test_specfn` (source `as a1`/`a2`/`a3` now emit
  `assert [a1]:` / `[a2]:` / `[a3]:`).
- This joins the synthetic proof-mode labels the translator already emitted —
  `by (bit_vector)` → `[bitvector_query]`, `by (nonlinear_arith)` →
  `[nonlinear_query]`, compute-mode → `[compute]`.
- Affects: `vlir-tests:test_specfn`, plus any test using `by (lean_proof as ...)`.

### `[TRANS-trigger-annotation]` `#[trigger]` annotations on quantifier sub-expressions stripped
- Verus quantifiers can carry `#[trigger]` (or `#![auto]`) annotations that hint
  the SMT solver about which sub-expressions to use as instantiation patterns.
  E.g. `forall|a: u32, b: u32| #[trigger] (!(a & b)) == !a | !b` marks
  `(!(a & b))` as the trigger.
- The translator currently strips these annotations: the same source quantifier
  becomes `∀ a : bv32, b : bv32 :: ~(a & b) == ~a | ~b;` with no trigger marker.
- Boole's grammar has a trigger-carrying quantifier (`forall_unicodeT` /
  `exists_unicodeT`), so the construct exists. **But this is not a
  translation-only fix:** StrataBoole's Boole→Core lowering discards the
  triggers (`Verify.lean`'s `forall_unicodeT _ ds _ body` / `exists_unicodeT _
  ds _ body` ignore the trigger slot), so even an emitted trigger would not
  reach the Core quantifier. Preserving triggers end-to-end needs both a
  translator change (emit `forall_unicodeT` with the VLIR `Quant` groups)
  **and** a Strata-Boole change (thread them through `toCoreExpr`) — a Strata
  PR, not verus-boogie alone.
- Logical content of the assertion is preserved; only the SMT instantiation
  hint is lost. May affect verification performance or completeness for
  trigger-sensitive proofs.
- Affects: `verus-examples:guide/nonlinear_bitvec`, `verus-examples:quantifiers`,
  and any test using explicit `#[trigger]` / `#![auto]` annotations.

### `[TRANS-choose]` `choose` operator partially translated
- Statement-level single-binder `choose` ships faithfully.
  `Bind.Choose (vars) (pred)` is a first-class VLIR constructor;
  `Parser.lean`'s `Choose` arm reads the predicate from the JSON's `arr[2]`;
  every `Bind` walker (`Pp`, `Elab`, `Normalize`, `ForLoop`,
  `Pruning`, `Prelude`, `Inference`) handles the constructor;
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
- The two remaining statement-reachable shapes ship:
  - **Multi-binder choose-let** (`let (x, y) = choose|i, j| pred(i, j)`,
    arriving as the tuple temporary's assignment with the binder tuple as
    the chosen value): `normalizeChooseProduct` rewrites it to a
    single-binder choose over the right-nested pair type
    (`choose p : (T1, …, Tn) :: pred[vk ↦ p.k]`), which the existing
    statement and spec-fn paths then handle.  `quants.rs:325` emits
    `tmp_ren0 := choose i_j_choose : (Tuple2 int int) ::
    less_than(Tuple2.._0(i_j_choose), Tuple2.._1(i_j_choose));`.
  - **Choose in call-argument position** (`lemma(i, choose|j| pred(j))`):
    `hoistChooseArg` hoists each such argument to a fresh temporary bound
    by `choose_assign` ahead of the call — `quants.rs:452` emits
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

### `[TRANS-for-loop-empty-range]` Bv-domain exclusive ranges (RESOLVED)
- Lowering Rust's exclusive `start..end` to Boole's inclusive
  `for i := start to end - 1` allowed `end - 1` to wrap in the bitvector
  domain. Empty ranges such as `0..0` could therefore become a loop ending at
  `2^64 - 1`; mathematical-`int` loops already represented emptiness faithfully
  with a negative inclusive limit.
- **Resolved:** every recovered bv-domain range is wrapped in a
  signedness-aware `if start < end` guard before the inclusive loop. The same
  helper guards the synthesized `Vec_from_elem` loop with `if bv{64}(0) < n`.
  This handles both zero-bound and reversed ranges without changing int-domain
  loop output.
- Regression coverage:
  - `vlir-tests:crypto_noref` emits the corresponding guard around synthesized
    `Vec_from_elem`.

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
- **Script-side workaround**: `tests/lib/boole_verify.sh`
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
  pipeline) or wrap each use of the binder in `nat.toInt(...)`.
- Affects: `verus-examples:trigger_loops` (line 36's
  `bad_loop` requires). Adjacent to `[TRANS-widening-casts]`
  but the failure is at type-check rather than at solver time.

### `[SURFACE-sequence-empty]` typed `Sequence.empty_<T>` resolved
- Typed dispatch in `expected?`-known contexts.  Boole's grammar exposes
  `Sequence.empty_bv8 / _bv16 / _bv32 / _bv64 / _int` (the DDM
  parser cannot resolve a polymorphic `Sequence.empty` without
  arguments).  The translator picks the right token via the
  `seqEmptyTokenName` helper at every `resolveFreeVar
  "Sequence.empty"` site, threaded through `seqEmptyExpr` /
  `seqLiteralExpr` / `seqRepeatExpr`.
- Equality-position gap closed.  When a sequence
  literal appears in `assert v == Sequence.append(…, Sequence.build(…,
  Sequence.empty, …), …)`, the inner `Sequence.empty` is emitted typed.
  Two changes: (a) `comparisonPrelude` uses `inferComparableTyp?`
  to propagate one side's concrete type as `expected?` to the other
  side when neither side has bv info; (b) every `Seq_*` arm in
  `expToBoole`'s Call branch prefers a concrete `Sequence T`
  `expected?` over the polymorphic `lookupFnParamTypeFull` value via
  the `seqArgExpected?` helper — letting nested
  `Sequence.append`/`Sequence.build` chains thread the element type
  down to `Sequence.empty_<T>` literals at the leaves.
- **Validation**: `verus-examples:guide/lib_examples`,
  `verus-examples:guide/quants`, and `vlir-tests:test_vstd`
  emit zero untyped `Sequence.empty` tokens.
- Polymorphic fallback resolved. For an element type variable,
  `Bld.seqEmpty` / `seqEmptyExpr` use Core's `seq_empty<A>()` production and
  print `Sequence.empty<T>()`. The generic empty-sequence parse errors
  in `crypto_noref`, `assert_by_compute`, and related tests are gone.

### `[SURFACE-sequence-literal]` typed `Sequence.of_<T>[…]` literal emission
- Adopts upstream `seq_of_*` syntax.  Boole's grammar exposes
  `Sequence.of_bv8 / _bv16 / _bv32 / _bv64 / _int` typed-literal tokens
  with the surface syntax `Sequence.of_<T>[v0, v1, …]`.  Strata's
  `toCoreExpr` lowers each one to the same left-fold of `Sequence.build`
  over `Sequence.empty` that the translator emits by hand, so
  verification semantics are unchanged.
- **Translator change**: `seqLiteralCtor?` in `Translate.lean` maps an
  element type to the dedicated `BooleDDM.Expr.seq_of_<T>` AST
  constructor (the brackets-with-comma surface form must be emitted as
  the specific AST node — a generic `Bld.appN` to a `Sequence.of_bv32`
  free variable prints with parens and is rejected by the DDM frontend
  as `Unknown variable Sequence.of_bv32`).  Both `seqLiteralExpr` and
  `seqRepeatExpr` route through it; polymorphic element types
  (`TypParam`, `Struct`, unrecognised) fall back to the older
  `Sequence.build` chain over typed `Sequence.empty<T>()`.
- **Validation**: `sha256_compact_indexed`'s `K32` constant emits as a
  single `Sequence.of_bv32[bv{32}(0x428a2f98), bv{32}(0x71374491), …]`
  literal instead of a 64-deep nested `Sequence.build(Sequence.build(…
  Sequence.empty_bv32, v0), v1)` chain.  Output size for that one
  literal drops from ~3 KB to ~700 bytes.  The `[0u32; 16]` init in
  `to_u32s` similarly compacts.  Obligation count is 26 for the
  SHA test (two additional well-formedness obligations the typed-literal
  node generates), all passing; the current working-suite gate remains
  46 pass / 2 skips / 1 fail.
- Affects (emission shape only, no verification-outcome changes):
  every test that emits a `Sequence.build(…)` chain on a
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
- **`IntPromotion` pass.**  The module
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
- **Companion changes.**
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
    write side) all pass `expected = some .Int` to the index
    translator directly, instead of translating with `expected = none`
    and post-coercing.  The post-coerce path didn't fold a bv-typed
    `Const` literal into `intConst`, so `state[0]` emitted
    `Sequence.select(state_out, bv64_to_int_u(bv{64}(0)))` even though
    the matching write side already printed `Sequence.update(…, 0,
    …)`.  After unification both sides print as `Sequence.select(…,
    0)` / `Sequence.update(…, 0, …)`.
- **Validation**: `tests/VerusFiles/sha256_compact_indexed.rs` is
  fully green: 24/24 obligations pass, including the two `compress`
  while-loop invariants (`entry_invariant_0_0`,
  `arbitrary_iter_maintain_invariant_0_0`).  Generated Boole prints
  `var k : int; while (k <
  Sequence.length(blocks)) { … }`, `for i : int := 0 to N - 1 { …
  Sequence.select(s, i) … }`, with no `bv64_to_int_u` casts at the
  index positions.  The working-suite regression case stays on this
  source-close while-loop variant, rather than replacing
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
- **Resolved for Boole**: unit lowers through a singleton support datatype
  `datatype Unit { Unit_unit() }`, and unit-valued match temporaries are
  dropped after preserving their branch side effects. Normal Boole wrapper
  verification now covers stale malformed tuple/unit spellings such as
  `Tuple.._2` and `Tuple2_ctor_0`.
- Still tracked as a raw-Core legacy note for the affected tests:
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
- Still tracked as a raw-Core legacy note for the affected tests:
  `verus-examples:guide/exec_attr`, `verus-examples:mergesort`,
  `verus-examples:set_from_vec`, `verus-examples:guide/invariants`,
  `verus-examples:guide/higher_order_fns`.

### `[MODEL-missing-types]` Missing Strata types
- `nat` emitted as abstract type. Coercion functions declared as uninterpreted.
- Collection types: `Set`, `Verus_Map`, `Multiset`.
  `Set` and `Multiset` are still declared by the translator when referenced.
  `Map` stays prefixed because Strata Core already has a built-in `Map`.
  `Tuple`, `Std_specs_range` are also declared when referenced.
- Verus `Seq<T>` lowers to Strata's built-in `Sequence T`. Free type
  variables (`A`, `T`, etc.) are auto-declared as abstract types.
- Still missing in Strata: `Cell`, `Atomic`, `Atomic_ghost`, `Simple_pptr`,
  `Arithmetic_overflow`, `Rwlock`, `Thread`, `String_string`,
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
  - Floating-point: `verus-examples:float`
