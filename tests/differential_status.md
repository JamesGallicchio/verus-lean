# Differential Status

This file tracks three things separately:
- raw Core regression outcomes from `regress_examples.sh`
- Boole smoke/elaboration status for selected cases
- manual faithfulness judgments for reviewed cases

Solver success is **not** used to classify faithfulness.

## Data Sources
- Full run (`./tests/regress_examples.sh --all-suites`):
  - run id: `20260430_204358`
  - solver: `cvc5`
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

Primary verify statuses from the base regression run plus the two mirrored
`vlir-tests` entries above (sum to 122):
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
- `verus-examples:basic_failure` (translation is source-close; the test's `external_span(s: Seq<nat>)` proof procedure lowers to `procedure external_span (s : Sequence nat)` and is blocked by Strata's current Sequence frontend/indexing support)
- `verus-examples:bitvector_basic` (`[TRANS-coercion-uninterpreted]` blocks several `bitvector_query` / `compute` obligations that depend on `bv8_to_bv16_u`, `bv8_to_bv32_s`, `bv8_to_int_u`, `bv8_to_int_s`)
- `verus-examples:bitvector_equivalence` (bitvector proofs with triggers and decreases; cvc5 times out on the `equivalence_proof_bv` ensures — large bit-blasted query)
- `verus-examples:broadcast_proof` (verify SKIP (Sequence): translation uses Sequence prelude faithfully; blocked by Strata's current Sequence frontend/indexing support)
- `verus-examples:calc` (`calc!` steps lower to explicit assertion chains; the remaining mismatch is Strata's current `Sequence` frontend/indexing support plus nat/bv64 typing in the sequence-extensionality steps)
- `verus-examples:cells` (translation is source-close; the current difference is the missing `Cell` model type in Strata)
- `verus-examples:generics` (`[TRANS-generic-reveal]`; `[VERIFY-generic-typevar-ddm]` raises SMT encoding errors on type-var-using obligations, and downstream asserts depending on those obligations also fail)
- `verus-examples:guide/integers` (`[TRANS-coercion-uninterpreted]`: widening casts emit uninterpreted coercions like `bv8_to_bv16_u`, `bv16_to_int_u`, `int_to_bv8_u`; cvc5 cannot reason through these)
- `verus-examples:guide/interior_mutability` (translation is source-close; the current difference is the missing `Cell` model type in Strata)
- `verus-examples:guide/modes` (`Tuple` type declared by translator when referenced; `[TRANS-coercion-uninterpreted]` in mixed `nat`/`bv8`/`int` arithmetic — uninterpreted `nat_to_int` and `bv8_to_int_u` block obligations like `bv8_to_int_u(u) < i && i < nat_to_int(n)`)
- `verus-examples:guide/nonlinear_bitvec` (translation faithful: `[bitvector_query]`/`[nonlinear_query]`/`[compute]` proof-mode labels emitted; `[TRANS-trigger-annotation]` strips `#[trigger]` annotations on De-Morgan quantifiers but preserves logical content. Verify SKIP — Strata-side dispatch for the proof-mode labels is incomplete on this case)
- `verus-examples:guide/opaque` (faithful empty Boole export: source `pub open spec fn` opaque-with-`reveal_with_fuel` declarations have no exec procedures to verify, so no `.lean` file is produced. Treated as faithful but different because there is nothing for Strata to discharge against the Verus-side outcome)
- `verus-examples:guide/overflow` (`[MODEL-missing-types]`: `Arithmetic_overflow` not modelled in Strata; `Num_checked_add` lowers to a procedure with `assume false;` body per the external-body convention)
- `verus-examples:guide/references` (`[TRANS-coercion-uninterpreted]` in the loop's `decreases bv32_to_int_u(b_out)` — Strata cannot discharge the decrement because `bv32_to_int_u` has no body; immutable/mutable references erase to plain values, which is verification-equivalent)
- `verus-examples:guide/requires_ensures_edit` (source `i8` with signed comparisons `-16 <= x1 < 16` lowers to `<=s`/`<s` (`bvsle`/`bvslt`) Boole AST — blocked by Strata Verify lacking dispatch arms for these signed-bv-comparison constructors; tracked in the strata-bv-lowering issue draft)
- `verus-examples:guide/requires_ensures` (same signed-bv-comparison gap as `requires_ensures_edit`; `print_two_digit_number` is `external_body` and follows the `assume false;` convention)
- `verus-examples:guide/strings` (translation is source-close; the current difference is the missing `String_string` / string-library model support in Strata)
- `verus-examples:impl_basic` (structs, methods, generics, ensures clauses preserved)
- `verus-examples:nevd_script` (`[TRANS-coercion-uninterpreted]`: `nat`-typed parameters and `nat_to_int`-coerced bodies (e.g. `rec function fibo (n : nat) : nat` with `if nat_to_int(n) == 0 then 0 else ...`); int literals in the body trigger `int`-where-`nat`-expected typecheck errors)
- `verus-examples:overflow` (`[MODEL-missing-types]`: `Arithmetic_overflow` not modelled in Strata; the translator preserves source-level checked-overflow operations like `checked_u64_constants`/`checked_u64_calculations` and emits `var w : Arithmetic_overflow` parameters that Strata cannot resolve)
- `verus-examples:power_of_2` (Strata type error: `int` literals where `nat` expected)
- `verus-examples:prelude` (`seq!` now lowers through `Sequence.empty`/`Sequence.build`; the remaining mismatch is Strata's current `Sequence` frontend/indexing support)
- `verus-examples:proposal-rw2022` (`[TRANS-coercion-uninterpreted]` in `rec function fibo (n : nat) : nat` body and the `bv64_to_int_u(result) == nat_to_int(fibo(bv64_to_nat_u(n)))` ensures clause; termination-check artifacts (`decrease%init*`, `CheckDecrease*`) correctly stripped from translation)
- `verus-examples:quantifiers` (typing now flows through via `nat_to_int` coercion; the universal `∀ i : nat :: nat_to_int(i) >= 0 && ...` fails because `nat_to_int` is declared without a body, so cvc5 cannot prove `nat_to_int(i) >= 0` — `[TRANS-coercion-uninterpreted]`)
- `verus-examples:recursive_types` (translation appears source-close; Strata-side blocker is nested datatype shape unsupported in current Strata typechecker)
- `verus-examples:rw2022_script` (`[TRANS-coercion-uninterpreted]`: `is_prime` and `fibo` use `nat` arithmetic via uninterpreted `nat_to_int`; prime-testing quantifier/trigger structure preserved, `rec function fibo` with implicit decreases preserved)
- `verus-examples:statements` (mixed-width bitvector arithmetic with explicit width extension; `[TRANS-coercion-uninterpreted]` causes the `b1 == i * 2` loop entry-invariant to fail — `bv8_to_bv64_u(b1)` is uninterpreted so cvc5 can't establish the relation)
- `verus-examples:test` (translation faithful: small bv64 procedure `foo` with `requires a < bv{64}(100)` and `_pct_return := a + bv{64}(1)`, plus a `main` that exercises it. Verify SKIP — Strata-side dispatch gap on this shape, no translator defect)
- `verus-examples:trigger_loops` (uninterpreted fns + multi-trigger quantifier patterns preserved; `[TRANS-choose]`: source `choose|z| g(z)` in `choose_example`/`quantifier_example` is parsed as `Bind.Lambda [z]` with the predicate erased)
- `vlir-tests:crypto_noref` (verify SKIP (Sequence): translation uses `Sequence.empty`/`Sequence.build`; blocked by Strata's Sequence frontend; also affected by `[VERIFY-lambda-encoding]` for lambdas in `Seq::new`-style spec functions)
- `vlir-tests:datatypes` (current difference is only that Strata still type-fails later in the pipeline)
- `vlir-tests:demo_for` (verify SKIP (Sequence): Boole output recovers the source-level `for` loop shape; blocked by Strata's Sequence frontend/indexing support)
- `vlir-tests:demo_while_loop_isolation` (`Vec<u64>` find-max with explicit `loop_isolation` enabled; `[TRANS-coercion-uninterpreted]` in `bv64_to_int_u(i)` indexing through `Sequence.length`/`Sequence.select`; structurally identical to `demo_while`)
- `vlir-tests:demo_while` (`Vec<u64>` find-max with `#[verifier::loop_isolation(false)]`; `[TRANS-coercion-uninterpreted]` in `bv64_to_int_u(i)` indexing through `Sequence.length`/`Sequence.select`)
- `vlir-tests:demo` (verify SKIP (Sequence): Boole output is source-close and elaborates cleanly; blocked by Strata's Sequence frontend/indexing support)
- `vlir-tests:FindMax` (`Vec<i32>` find-max via `Sequence bv32`; `[TRANS-coercion-uninterpreted]` for `bv64_to_int_u` in indexing and `>=s` signed comparisons; cvc5 default returns unknown on at least one VC even when the translation is well-formed)
- `vlir-tests:integer_ring` (Strata type error on intentionally-failing `type_fail`; cvc5 also times out on `wide_mul` ensures — non-linear bv64 multiplication beyond solver default budget)
- `vlir-tests:LoopSimple` (`i32` summation loop; `[TRANS-coercion-uninterpreted]` in `decreases bv32_to_int_s(n - i)`; signed comparisons `<s`/`<=s` use `bvslt`/`bvsle` Boole AST nodes that lack dispatch arms in Strata Verify (per the strata-bv-lowering issue draft); intentionally fails as a stable verify-mismatch baseline)
- `vlir-tests:mutual_recursion` (Boole output elaborates as a `rec function is_odd ... function is_even ...` block and is source-close; raw Core path still hits `[CORE-decreases]`'s `@[cases]`-on-`int` requirement for spec-fn recursion)
- `vlir-tests:nonlinear` (`[TRANS-coercion-uninterpreted]`: `nat`-typed nonlinear obligations like `bv32_to_int_u(x) * bv32_to_int_u(z) <= nat_to_int(65535 * 65535)` and `nat_to_int(x * x + x) == nat_to_int(x * (x + 1))` go through uninterpreted `nat_to_int`/`bv32_to_int_u` that cvc5 cannot reason through; same flavor as `nevd_script`)
- `vlir-tests:proof_fn` (translation faithful: `function p (u : bv64) : bool` and `function min (x : int, y : int) : int` declared with bodies, lemma-style procedures lower to spec-only `procedure ... ensures ... { exit ... }` shape. Verify SKIP — Strata-side dispatch gap, no translator defect)
- `vlir-tests:quant` (mixed `int`/`nat` quantifier patterns like `∀ x : int, y : nat :: x + y == y + x` produce direct `+` on mismatched types that Strata's typechecker rejects; also affected by `[TRANS-trigger-annotation]` (source `#[trigger]` annotations stripped) and `[TRANS-assert-label]` (source `as a1`/`a2`/`a3` labels dropped))
- `vlir-tests:recursion` (Boole output now elaborates as a `rec function` block; raw Core path is still blocked by `[CORE-decreases]` `@[cases]`-on-`int` requirement, but Boole-side translation is faithful)
- `vlir-tests:rec_adt_structural` (nat emitted as abstract type via `[MODEL-missing-types]`; waiting for Strata native nat support)
- `vlir-tests:test_requires` (translation faithful: `[bitvector_query]` and `[nonlinear_query]` proof-mode labels preserved on the `test_success` and `bound_check` assertions. Verify SKIP — Strata-side dispatch for these proof-mode labels is incomplete on this case, mirroring `guide/nonlinear_bitvec`)
- `vlir-tests:vec_ops` (verify SKIP (Sequence): Vec operations lower through Sequence prelude; blocked by Strata's Sequence frontend/indexing support)

## not faithful translation (58)
- `verus-examples:assert_by_compute` (`[VERIFY-lambda-encoding]` for lambdas in `Seq::new`-style spec functions; `[TRANS-coercion-uninterpreted]` for `nat_to_int(Fib_fib(...))` and friends; `assert(...) by (compute_only)` lowers to `assume <pre-computed-result>;` directly. `Compute_all_spec` stubs surface in `guide__assert_by_compute`, not here)
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
- `verus-examples:exec_termination_example` (source has basic recursive `exec` fns and while loops with `decreases` clauses on bare `int`; the claim about iterator/ghost state was inaccurate — no `iter()` in source. Actual gap: function-level `decreases` is dropped per `[CORE-decreases]` (which only supports loop-level), so the recursive procedures verify only as far as Strata's recursion handling permits)
- `verus-examples:extensionality` (`[TRANS-extensional-eq]` expands `assert_seqs_equal!`, `assert_maps_equal!`, and `assert_sets_equal!` into low-level proof scaffolding and explicit formulas; `[VERIFY-lambda-encoding]` and `[TRANS-higher-order-collection-stubs]` still affect `Map::total`, `Map::new`, and `Set::new`; raw Core also currently hits a Strata-side `Sequence` indexing type error in `are_equal`)
- `verus-examples:external` (`Ghost<int>` erased to plain `int`; `println!` in `external_body` fn not translated; the `s >= n` precondition becomes `s >= bv64_to_int_u(n)` which cvc5 can't prove because `bv64_to_int_u` is uninterpreted — `[TRANS-coercion-uninterpreted]`)
- `verus-examples:float` (`[TRANS-float-unsupported]`: source `f64`/`f32` literals lower to `Unsupported.Float64` placeholders in emitted Boole; floating-point types/operations not yet translated)
- `verus-examples:guide/assert_by_compute` (`range_property` still uses uninterpreted `Compute_all_spec` plus `[VERIFY-lambda-encoding]`; nat/int literal typing still leaks into recursive nat functions such as `pow`)
- `verus-examples:guide/bst_map_generic` (BST-as-map with generic key/value; emits `Map_empty`, `Map_lib_union_prefer_right`, `Map_insert` cleanly — `[TRANS-fuel-parameter-leakage]` no longer applies here. Remaining gap: classification holds via solver-side reasoning about generic recursive datatypes — `[VERIFY-generic-typevar-ddm]`-adjacent issues likely)
- `verus-examples:guide/bst_map_type_invariant` (BST-as-map with type-invariant constraint; same Map operations emitted cleanly — Fuel-leakage claim was stale; remaining gap is solver-side reasoning about the type invariant under recursive operations)
- `verus-examples:guide/bst_map` (concrete BST-as-map for `u64 -> bool`; emits `Map_empty`, `Map_lib_union_prefer_right`, `Map_insert` and `Impl__0_as_map`/`Impl__0_optional_as_map` accessors cleanly — `[TRANS-fuel-parameter-leakage]` no longer applies. Remaining gap is solver-side reasoning about recursive structural properties)
- `verus-examples:guide/const` (`Layout::size_of` lowers to `Layout_size_of` symbol that is undeclared in the emitted Boole; `[MODEL-missing-types]` for `Layout`; output also relies on the `sorry` axiom, indicating an `assume false`-style fallback)
- `verus-examples:guide/exec_attr` (`test_for_loop` still has `[VERIFY-lambda-encoding]` in the loop invariant; `proof_decl!` / `proof_with!` / `Ghost` / `Tracked` wrappers are flattened under `[TRANS-ghost-tracked-erasure]`)
- `verus-examples:guide/exec_spec_unverified` (`[TRANS-exec-spec-helper-leakage]`: the `exec_spec_unverified!` example lowers through internal `View_deep_view` / `exec_*` helper stubs and a distorted `Map int execPoint` representation rather than preserving the source macro structure)
- `verus-examples:guide/exec_spec_verified` (`[TRANS-exec-spec-helper-leakage]`: the `exec_spec_verified!` example leaks internal `View_deep_view`, `View_V`, `Contrib_Exec_spec_*`, and slice/array helper stubs instead of source-like `deep_view` / `as_slice` reasoning)
- `verus-examples:guide/external_trait_specs` (`[TRANS-trait-unsupported]`; raw Core also currently hits a bv64/int comparison mismatch in `test_hasher`)
- `verus-examples:guide/ext_equal` (`[VERIFY-lambda-encoding]`; direct `Seq`/`Set`/struct extensionality now lowers to explicit formulas, but raw Core still expands away source `=~=`/`=~~=` syntax and currently hits `[SURFACE-sequence-empty]`)
- `verus-examples:guide/higher_order_fns` (`[TRANS-exec-closure-scaffolding]`; `[SURFACE-sequence-empty]` in the captured-closure example)
- `verus-examples:guide/invariants` (`[TRANS-extensional-eq]`: source `assert(operations@.take(i as int) =~= ...)` is expanded to plain `==`; `[TRANS-coercion-uninterpreted]` in fib-loop invariants like `bv64_to_int_u(prev) == nat_to_int(fib(i - bv{64}(1)))`)
- `verus-examples:guide/lib_examples` (`[VERIFY-lambda-encoding]` in returned/captured function values and collection constructors; `[SURFACE-sequence-empty]`; the current Vec translation itself is now the datatype-based path)
- `verus-examples:guide/pervasive_example` (current output uses `Sequence.length(s) == 5` cleanly — the older `[TRANS-seq-len-literal-typing]` nat/bv64 mismatch claim no longer applies after recent translator work. Remaining gap is Strata's current `Sequence` frontend/indexing support)
- `verus-examples:guide/quants` (`[TRANS-reveal-with-fuel]`; `[SURFACE-sequence-empty]`)
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
- `verus-examples:verified_vec` (no Boole `.lean` output produced — generation step fails silently for this test; cause TBD, likely a translator-side abort on Vec lowering)
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
  `boole_procedure`.  Strata still ignores the slot today (no SMT
  termination check at the procedure level), but the AST is in
  place.  Verus-internal artifacts (`decrease%init*`,
  `CheckDecrease*`) continue to be stripped from bodies.
  Lex-decreases (multiple terms) collapse to the head; full
  lexicographic support waits on Strata accepting a tuple measure.

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
- **Two shapes remain unfaithful:**
  - **Multi-binder choose-let** (`let (x, y) = choose|i, j| pred(i, j)`):
    Verus desugars to a tuple destructure, so the `Stm.Assign` arm
    doesn't match.  Surfaces as `Tuple_ctor_2(i, j)` with `i, j`
    unbound — Strata catches it as `Unknown expr identifier`,
    not a silent miscompile.  Verus examples:
    `syntax.rs:284`, `quants.rs:325`.
  - **Expression-level choose** (`f(choose|j| pred(j))` in argument
    or other sub-expression position):
    `expToBoole`'s `.Choose` arm translates the body and silently
    drops the predicate.  Verus examples:
    `quants.rs:452`, `state_machines/refinement.rs:81`,
    `state_machines/refinement_labels.rs:91`,
    `summer_school/chapter-6-1.rs:117`.  Fix sketch: pre-pass in
    `Boole/Normalize.lean` that hoists choose-bearing sub-
    expressions to fresh-temp `Stm.Assign`s, exposing the
    statement-level path.

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

### `[SURFACE-sequence-empty]` typed `Sequence.empty_<T>` mostly resolved
- **2026-05-07 update — typed dispatch ships in `expected?`-known
  contexts** (verus-boogie commit `8048d3a`).  Boole's grammar
  exposes `Sequence.empty_bv8 / _bv16 / _bv32 / _bv64 / _int` (the
  DDM parser cannot resolve a polymorphic `Sequence.empty` without
  arguments).  The translator now picks the right token via the new
  `seqEmptyTokenName` helper at every `resolveFreeVar
  "Sequence.empty"` site (`Translate.lean` lines 279, 797, 1120,
  1619), threaded through `seqEmptyExpr`/`seqLiteralExpr`/
  `seqRepeatExpr`.  Verified on `sha256_compact_indexed.lean` —
  emits `Sequence.empty_bv32` automatically; eliminated the previous
  manual edits the wrapper required.
- **Remaining gap** (open in `boole-translation-todo.md`): when a
  sequence literal appears in **equality / comparison position
  inside a bool-typed context** (e.g. `assert v == Sequence.build(…,
  Sequence.empty, …)`), `expected? = some .Bool` and the element
  type isn't reachable through `firstStructParamFromExpected?`.
  Surfaces in `tests/BoolePrograms/verus-examples/guide__lib_examples.lean`
  with `Unknown expr identifier Sequence.empty` errors on
  comparison RHS literals.  Fix likely needs the comparison-prelude
  to thread the inferred operand type into the literal side's
  `expected?`.
- Affects: `verus-examples:guide/lib_examples` (still hits the
  equality-position gap), `verus-examples:guide/quants`,
  `vlir-tests:test_vstd`, and other sequence-heavy tests where
  literals appear in bool-typed comparisons.

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
