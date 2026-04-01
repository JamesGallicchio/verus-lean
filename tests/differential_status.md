# Differential Status

This file tracks three things separately:
- raw Core regression outcomes from `regress_examples.sh`
- Boole smoke/elaboration status for selected cases
- manual faithfulness judgments for reviewed cases

Solver success is **not** used to classify faithfulness.

## Data Sources
- Full run:
  - command: `./tests/regress_examples.sh --all-suites`
  - run id: `20260330_010858`
  - solver: `cvc5`
- Boole output:
  - `verus-lean` now accepts `core --dialect boole ...`
  - current Boole mode reuses the local printer and reconstructs simple
    range-iterator loops as Boole `for` loops (for example `vlir-tests:demo_for`)
  - current Verus range-loop support is unit-step only:
    `for ... step_by(...)` is rejected before JSON export, so recovered Boole
    `for` loops are emitted as plain `for ... to ...` loops with implicit step 1
  - `vlir-tests:demo_for` now elaborates cleanly in Strata as Boole output
  - Boole-primary tests for manual review:
    `vlir-tests:demo`, `vlir-tests:demo_for`, `vlir-tests:mutual_recursion`,
    `vlir-tests:recursion`, `verus-examples:guide/recursion`
  - for those Boole-primary tests, the intended artifact to inspect is
    `tests/BooleFiles/.../*.lean`; raw `tests/BoogieFiles/.../*.core.st`
    failures are only background/Core-pipeline notes
  - other generated Boole files are still useful smoke tests, but they do not
    replace Core as the primary artifact unless called out explicitly below
  - targeted `for`-loop cases still blocked by non-`for` issues:
    `verus-examples:recursion` (`int`/`bv64` mismatch),
    `verus-examples:set_from_vec`, `verus-examples:mergesort`,
    `verus-examples:guide/exec_attr` (`Unit` / loop-helper artifacts in the
    current Core-shaped lowering),
    `verus-examples:vectors` (`[TRANS-vec-representation-gap]`, plus `Unit` /
    loop-helper artifacts in the reverse examples),
    `verus-examples:exec_termination_example` (residual iterator/ghost state),
    `verus-examples:guide/invariants` (`bv64` where `int` expected)
  - the raw summary below is still based on Core output plus `strata verify`

## Raw Core Regression Summary (Full Run)
Total cases: **118**

Primary statuses (sum to 118):
- export failures: 0
- expected empty exports: 1
- translate failures: 0
- strata parse failures: 0
- strata type failures: 80
- verify failures: 25
- verify success: 12
- expected mismatches: 0

Additional counters (do not affect total):
- mismatch (Verus pass, Strata fail): 18
- mismatch (Verus fail, Strata pass): 0

## Translation Quality Labels
- `faithful and same as Verus output`: translation is faithful and Strata verification outcome matches Verus.
- `faithful but different from Verus output`: translation is faithful, but Verus/Strata outcomes differ or Strata lacks support.
- `not faithful translation`: translation currently drops/changes important semantics compared to source-level intent.
- Manual labels below are Core-first by default.
- Repeated issues are keyed by gap IDs from the `Gap Index` section below.
- Exception: for the Boole-primary tests listed above, judge translation quality
  from the Boole file in `tests/BooleFiles`, not from the raw Core file in
  `tests/BoogieFiles`.
- If a non-Boole-primary test is better in Boole for some specific reason, that
  exception is called out explicitly in its note.

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
- `vlir-tests:basic_failure`, `verus-examples:guide/requires_ensures`,
  `verus-examples:guide/requires_ensures_edit`, `verus-examples:imo_1988_6`:
  the local Core output now renders `return` as comments again. We still note
  `[TRANS-return-comment]` under `Gap Index`, but we classify these as faithful
  when that is the only issue.

## faithful and same as Verus output (16)
- `vlir-tests:basic_failure` (fail as expected)
- `vlir-tests:proof_fn`
- `vlir-tests:test_requires`
- `vlir-tests:test_specfn`
- `vlir-tests:test_opaque_reveal` (opaque function declaration-only + reveal as assume)
- `vlir-tests:by_lean` (fail as expected)
- `verus-examples:adts_eq`
- `verus-examples:assertions` (fail as expected)
- `verus-examples:debug` (fail as expected)
- `verus-examples:structural`
- `verus-examples:test`
- `verus-examples:guide/calc`
- `verus-examples:guide/equality`
- `verus-examples:guide/getting_started`
- `verus-examples:guide/nonlinear_bitvec`
- `verus-examples:guide/opaque` (expected empty export)

## faithful but different from Verus output (39)
- `vlir-tests:FindMax` (cvc5 default gives one VC unknown)
- `vlir-tests:LoopSimple` (mismatch as expected)
- `vlir-tests:datatypes` (current difference is only that Strata still type-fails later in the pipeline)
- `vlir-tests:matching` (Strata currently fails on nat assertions)
- `vlir-tests:demo_while` (same as FindMax)
- `vlir-tests:demo_while_loop_isolation` (same as FindMax)
- `vlir-tests:quant` (current blocker is Strata-side typing)
- `vlir-tests:rec_adt_structural` (nat emitted as a datatype; waiting for Strata native nat support)
- `vlir-tests:mutual_recursion` (current Boole output elaborates and is source-close; raw Core still has the `@[cases]`-on-`int` limitation only)
- `verus-examples:bitvector_basic` (Strata SMT encoding issue on indexed bitvector literal)
- `verus-examples:fun_ext` (blocked by higher-order/extensional support)
- `verus-examples:generics` (`[TRANS-generic-reveal]`)
- `verus-examples:guide/modes` (Tuple type now declared; blocked by other Strata issues)
- `verus-examples:guide/datatypes` (current difference is only that datatype-constructor/selector VCs fail in Strata)
- `verus-examples:guide/interior_mutability` (translation is source-close; the current difference is the missing `Cell` model type in Strata)
- `verus-examples:guide/overflow` (blocked by missing arithmetic-overflow/cast support in Strata)
- `verus-examples:guide/references` (current mismatch is Strata loop-measure reasoning)
- `verus-examples:guide/strings` (translation is source-close; the current difference is the missing `String_string` / string-library model support in Strata)
- `verus-examples:guide/requires_ensures` (`[TRANS-return-comment]` only)
- `verus-examples:guide/requires_ensures_edit` (`[TRANS-return-comment]` only)
- `verus-examples:prelude` (`seq!` now lowers through `Sequence.empty`/`Sequence.build`; the remaining mismatch is Strata's current `Sequence` frontend/indexing support)
- `verus-examples:statements` (mixed-width bitvector arithmetic with explicit width extension)
- `verus-examples:quantifiers` (Strata type error: `tr(i)` where `i: nat` but `tr` expects `int`)
- `verus-examples:assorted_demo` (`#[verifier::external]` fn dropped, `#[verifier::external_body]` fn emitted with specs and empty body)
- `verus-examples:cells` (translation is source-close; the current difference is the missing `Cell` model type in Strata)
- `verus-examples:overflow` (checked-overflow operations are preserved through the current arithmetic-overflow helper model; the remaining blocker is the missing `Arithmetic_overflow` type in Strata)
- `verus-examples:guide/integers` (missing `bv8_to_nat` coercion — Verus widening cast erasure)
- `verus-examples:impl_basic` (structs, methods, generics, ensures clauses preserved)
- `vlir-tests:integer_ring` (Strata type error only on intentionally-failing `type_fail`)
- `verus-examples:proposal-rw2022` (coercions at call sites, termination-check artifacts stripped)
- `verus-examples:bitvector_equivalence` (bitvector proofs with triggers and decreases)
- `verus-examples:adts` (datatypes, variant checks, structural equality; TODO: `matches` clause)
- `verus-examples:basic_failure` (translation is source-close; the current difference is Strata's `Sequence` indexing/frontend support in `external_span`)
- `verus-examples:calc` (`calc!` steps lower to explicit assertion chains; the remaining mismatch is Strata's current `Sequence` frontend/indexing support plus nat/bv64 typing in the sequence-extensionality steps)
- `verus-examples:rw2022_script` (prime testing with quantifiers/triggers, fibo with decreases)
- `verus-examples:trigger_loops` (uninterpreted fns, multi-triggers, coercions; TODO: `choose`)
- `vlir-tests:tests/LoopSimpleWithSpec` (loop with spec, recursive spec fn, coercions at call sites)
- `verus-examples:imo_1988_6` (`[TRANS-return-comment]` only)
- `verus-examples:power_of_2` (Strata type error: `int` literals where `nat` expected)

## not faithful translation (45)
- `verus-examples:datatypes` (`Box` erased to identity, `[TRANS-reveal-with-fuel]`, and loop/match lowering still not source-close enough)
- `verus-examples:doubly_linked` (pointer-heavy translation not source-faithful yet)
- `verus-examples:external` (`Ghost<int>` erased to plain `int`; `println!` in `external_body` fn not translated)
- `verus-examples:integers` (remaining non-faithful call-argument coercion shape)
- `verus-examples:assert_by_compute` (`[TRANS-lambda-placeholder]` and `Compute_all_spec` stubs still affect sequence/range examples; nat/int literal typing still leaks into recursive nat functions such as `fib`)
- `verus-examples:atomics` (`[TRANS-atomic-ghost-scaffolding]`: `struct_with_invariants!` / `atomic_with_ghost!` still lower to low-level `Invariant_*`, `Atomic_*`, and `assume` scaffolding; raw Core also currently hits `[MODEL-missing-types]` (`Atomic_ghost`, `Unit`))
- `verus-examples:multiset` (`broadcast use group_to_multiset_ensures` ignored; multiset extensionality still lowers to plain equality; `[TRANS-lambda-placeholder]` still affects the `sort_by` comparator)
- `verus-examples:bitmap` (`[TRANS-lambda-placeholder]` in `u64_view`; `[TRANS-extensional-eq]` still expands source `=~=` and `assert_seqs_equal!`; and most of the `BitMap` API (`view`, `from`, `get_bit`, `set_bit`, `or`) is currently missing from emitted Core)
- `verus-examples:bitvector_garbage_collection` (`[TRANS-lambda-placeholder]` in `bucket_view`; `[TRANS-extensional-eq]` still expands source `=~=` away to explicit formulas; raw Core also currently hits nat/int typing around `Seq_new`)
- `vlir-tests:test_vstd` (`[TRANS-lambda-placeholder]` in `Set::new`, `Map::new`, and `Seq::new`)
- `vlir-tests:maps` (`[TRANS-lambda-placeholder]` in `mk_map` lambdas; `[TRANS-higher-order-collection-stubs]` currently distorts `Set_mk_map`; raw Core map equalities are still emitted as plain `==` rather than source-like map extensional equality)
- `vlir-tests:seqs` (`[TRANS-lambda-placeholder]` in `Seq::new`, `Seq::map`, `Seq::filter`, and `seq![x; n]`; `[TRANS-extensional-eq]` still expands source `===` away to raw Core equality; raw Core also currently hits `[SURFACE-sequence-empty]` and nat/int mismatches`)
- `vlir-tests:sets` (`[TRANS-lambda-placeholder]` in `Set::new`, `Set::filter`, `Set::map`, `set_map`, and `fold`; `[TRANS-higher-order-collection-stubs]` distorts `Set_new`, `Set_filter`, `Set_lib_map`, and `Set_Fold_fold`; `[TRANS-extensional-eq]` still expands source `===` away to raw Core equality; `s.choose()` is currently just uninterpreted `Set_choose` without witness semantics`)
- `verus-examples:guide/ext_equal` (`[TRANS-lambda-placeholder]`; direct `Seq`/`Set`/struct extensionality now lowers to explicit formulas, but raw Core still expands away source `=~=`/`=~~=` syntax and currently hits `[SURFACE-sequence-empty]`)
- `verus-examples:extensionality` (`[TRANS-extensional-eq]` expands `assert_seqs_equal!`, `assert_maps_equal!`, and `assert_sets_equal!` into low-level proof scaffolding and explicit formulas; `[TRANS-lambda-placeholder]` and `[TRANS-higher-order-collection-stubs]` still affect `Map::total`, `Map::new`, and `Set::new`; raw Core also currently hits a Strata-side `Sequence` indexing type error in `are_equal`)
- `verus-examples:guide/assert_by_compute` (`range_property` still uses uninterpreted `Compute_all_spec` plus `[TRANS-lambda-placeholder]`; nat/int literal typing still leaks into recursive nat functions such as `pow`)
- `verus-examples:guide/bst_map` (`[TRANS-fuel-parameter-leakage]`: source `Map::empty`, `union_prefer_right`, and `insert` still lower to helper signatures with synthetic `Fuel` parameters)
- `verus-examples:guide/bst_map_generic` (`[TRANS-fuel-parameter-leakage]`: source `Map::empty`, `union_prefer_right`, and `insert` still lower to helper signatures with synthetic `Fuel` parameters)
- `verus-examples:guide/bst_map_type_invariant` (`[TRANS-fuel-parameter-leakage]`: source `Map::empty`, `union_prefer_right`, and `insert` still lower to helper signatures with synthetic `Fuel` parameters)
- `verus-examples:guide/exec_attr` (`test_for_loop` still has `[TRANS-loop-helper-leakage]`, `[MODEL-unit]`, and `[TRANS-lambda-placeholder]` in the loop invariant; `proof_decl!` / `proof_with!` / `Ghost` / `Tracked` wrappers are flattened under `[TRANS-ghost-tracked-erasure]`)
- `verus-examples:guide/exec_spec_unverified` (`[TRANS-exec-spec-helper-leakage]`: the `exec_spec_unverified!` example lowers through internal `View_deep_view` / `exec_*` helper stubs and a distorted `Map int execPoint` representation rather than preserving the source macro structure)
- `verus-examples:guide/exec_spec_verified` (`[TRANS-exec-spec-helper-leakage]`: the `exec_spec_verified!` example leaks internal `View_deep_view`, `View_V`, `Contrib_Exec_spec_*`, and slice/array helper stubs instead of source-like `deep_view` / `as_slice` reasoning)
- `verus-examples:guide/external_trait_specs` (`[TRANS-trait-spec-resolution]`; raw Core also currently hits a bv64/int comparison mismatch in `test_hasher`)
- `verus-examples:guide/higher_order_fns` (`[TRANS-exec-closure-scaffolding]`; raw Core also currently hits `[SURFACE-sequence-empty]` and `[MODEL-unit]` in the captured-closure example)
- `verus-examples:guide/invariants` (`non_negative` still lowers its source `for` loop to raw iterator scaffolding with `[TRANS-loop-helper-leakage]` and `[MODEL-unit]`; the source `=~=` assertion is expanded away under `[TRANS-extensional-eq]`; raw Core also still renders `return false` under `[TRANS-return-comment]`)
- `verus-examples:guide/lib_examples` (`[TRANS-lambda-placeholder]` in returned/captured function values and collection constructors; raw Core also currently hits `[SURFACE-sequence-empty]`, helper leakage such as `Pervasive_set`, and `[TRANS-vec-representation-gap]`)
- `verus-examples:guide/pervasive_example` (`s.len() == 5` still lowers under `[TRANS-seq-len-literal-typing]` to a nat/bv64 mismatch; raw Core otherwise looks source-close and then runs into current `Sequence` frontend/indexing support)
- `verus-examples:guide/recursion` (`[TRANS-reveal-with-fuel]` in `test_triangle_reveal` / `test_triangle_assert_by`; raw Core also currently exposes `[TRANS-loop-helper-leakage]`, `[MODEL-unit]`, and `[TRANS-return-comment]` in the loop and early-return examples)
- `verus-examples:mergesort` (`extend_from_idx` still has `[TRANS-loop-helper-leakage]` and `[MODEL-unit]`; source `=~=` proof steps are flattened under `[TRANS-extensional-eq]`; the final `lemma_sorted_unique(..., |a, b| a <= b)` call still hits `[TRANS-lambda-placeholder]`)
- `verus-examples:guide/quants` (`[TRANS-reveal-with-fuel]`; raw Core also currently hits `[SURFACE-sequence-empty]`)
- `verus-examples:modules` (`[TRANS-closed-visibility]`)
- `verus-examples:recommends` (`[TRANS-reveal-with-fuel]` still strengthens the local proof step for `seq_max_int`; the recursive body also has `[TRANS-seq-len-literal-typing]`, and source `spec_affirm(...)` steps are erased from `some_predicate`)
- `verus-examples:rfmig_script` (`[MODEL-missing-types]` still blocks `Simple_pptr`; function `g` also still hits `[TRANS-vec-representation-gap]`)
- `verus-examples:rwlock_vstd` (`[TRANS-lambda-placeholder]` in the `Ghost(|v| ...)` lock invariant; raw Core also currently collapses `RwLock`/handle operations to undeclared model types under `[MODEL-missing-types]`)
- `verus-examples:set_from_vec` (`set` extensionality still expands away under `[TRANS-extensional-eq]`; `contains` still lowers its labeled `for i in iter: ...` loop to raw iterator scaffolding with `[TRANS-loop-helper-leakage]` and `[MODEL-unit]`)
- `verus-examples:statics` (`[TRANS-atomic-ghost-scaffolding]`: the `Lazy` / `atomic_with_ghost!` encoding still lowers to low-level `Atomic_ghost_*`, `Invariant_*`, `Cell_*`, and `assume` scaffolding rather than source-like lazy-static structure; raw Core also currently hits `[MODEL-missing-types]` (`Cell`, `Atomic_ghost`, `Unit`))
- `verus-examples:syntax` (`[TRANS-choose]` in `test_choose`; `[TRANS-ghost-tracked-erasure]`; `[TRANS-vec-representation-gap]` in `test_views`; `[TRANS-broadcast-use]`; raw Core also currently hits `[MODEL-unit]`)
- `verus-examples:syntax_attr` (`#[verus_spec(with ...)]`, `proof!`, and tracked/ghost wrapper syntax are still flattened under `[TRANS-ghost-tracked-erasure]`; raw Core also currently hits Strata's polymorphic tuple-helper DDM panic)
- `verus-examples:trait_for_fn` (`[TRANS-lambda-placeholder]`)
- `verus-examples:test_expand_errors` (`[TRANS-hide]`, `[TRANS-reveal-with-fuel]`)
- `verus-examples:thread` (`[TRANS-exec-closure-scaffolding]`; raw Core also currently hits `[MODEL-missing-types]` (`Thread`) and `[MODEL-unit]` through the closure requirement encoding)
- `verus-examples:debug_expand` (`[TRANS-hide]`, `[TRANS-closed-visibility]`)
- `verus-examples:recursion` (`[TRANS-reveal-with-fuel]`; Boole output now recovers the `for` loop shape, but the source-level fuel behavior is still not preserved)
- `verus-examples:vectors` (`[TRANS-vec-representation-gap]`; `pusher` also still hits `[TRANS-lambda-placeholder]` and `[TRANS-extensional-eq]`, while `reverse` / `reverse_no_spinoff` still expose `[TRANS-loop-helper-leakage]` and `[MODEL-unit]`)
- `vlir-tests:tests/mini_c` (`[TRANS-map-helper-typing]`: `Store = Map<Variable, Value>` still lowers `Map_insert` with a `state` receiver type; proof helper procedures also currently hit `[MODEL-unit]`)

## others (18) [WIP]

### missing Strata categories/model types (7)
- Missing types: `Unit`, `Atomic`, `Atomic_ghost`, `Cell`, `Simple_pptr`,
  `Arithmetic_overflow`, `Rwlock`, `Thread`, `String_string`. `Invariant`
  clashes with Strata's `invariant` keyword.
- Concrete example tests for each missing type:
  - `Unit`: raw Core example `vlir-tests:demo_for` (this test is Boole-primary,
    so use it here only as evidence of the missing Core `Unit` type, not as the
    primary artifact for manual translation review)
  - `Atomic`: `verus-examples:atomics` (also classified above because it has additional non-model translation issues)
  - `Atomic_ghost`: `verus-examples:atomics` (also classified above because it has additional non-model translation issues)
  - `Cell`: `verus-examples:cells` (also classified above because it is otherwise source-close)
  - `Simple_pptr`: `verus-examples:rfmig_script` (also classified above because it has additional non-model translation issues)
  - `Arithmetic_overflow`: `verus-examples:overflow` (also classified above because it is otherwise source-close)
  - `Rwlock`: `verus-examples:rwlock_vstd` (also classified above because it has additional non-model translation issues)
  - `Thread`: `verus-examples:thread` (also classified above because it has additional non-model translation issues)
  - `String_string`: `verus-examples:guide/strings` (also classified above because it is otherwise source-close)
  - `Invariant`: `verus-examples:invariants`
- Verus `Seq<T>` now lowers to Strata's built-in `Sequence T`.
  `Tuple`, `Std_specs_range`, `Set`, `Verus_Map`, and `Multiset` are
  declared when referenced. Free type variables (`A`, `T`, etc.) are
  auto-declared as abstract types.
- Tests: `verus-examples:basic_lock1`, `verus-examples:basic_lock2`, `verus-examples:doubly_linked_xor`, `verus-examples:even_cell`, `verus-examples:float`, `verus-examples:invariants`, `verus-examples:exec_termination_example`

### lambda / function-value placeholder gap (11)
- `Unsupported.lambda` is the current placeholder for actual lambda
  abstractions and function-valued terms.
- This is separate from `choose`; `choose` is tracked in its own gap below.
- Tests: `verus-examples:assert_by_compute`,
  `verus-examples:bitmap`, `verus-examples:bitvector_garbage_collection`,
  `verus-examples:extensionality`, `verus-examples:guide/assert_by_compute`,
  `verus-examples:multiset`, `verus-examples:rwlock_vstd`,
  `verus-examples:vectors`, `vlir-tests:maps`, `vlir-tests:seqs`,
  `vlir-tests:sets`

### `[TRANS-choose]` `choose` operator not faithfully translated
- Verus's `choose|z| g(z)` (Hilbert's epsilon) is parsed as `Bind.Lambda [z]`,
  erasing the predicate. The faithful encoding would be
  `havoc z; assume (exists z' :: g(z')) ==> g(z);`.
- Affects: `verus-examples:syntax`,
  `verus-examples:trigger_loops` (`choose_example`, `quantifier_example`)

### Raw Core-only mutual recursion over `int` still blocked by `@[cases]` requirements (1)
- Core mutual-recursive spec functions are now emitted as `rec` blocks, and the
  old `Procedure ... not found!` forward-reference failure is gone.
- The remaining Core blocker is Strata's current recursive-function
  requirement that the recursive parameter marked `@[cases]` have a datatype
  type. These Verus examples recurse over `int`, so the Core path still stops
  at `Recursive function ... requires a @[cases] parameter`.
- The current Boole output already elaborates for these tests, so this is a
  Core-only gap rather than the best available condition.
- Tests: `vlir-tests:recursion`

### complex type-check failures (2)
- `verus-examples:playground`: synthetic temp symbol not in context.
- `verus-examples:recursive_types`: nested datatype shape unsupported in Strata.

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

### `[TRANS-fuel-parameter-leakage]` Source `Map` operations still leak synthetic `Fuel` parameters
- Some library `Map` operations currently lower to helper symbols whose
  signatures still expose internal `Fuel` arguments, even though the Verus
  source only mentioned ordinary `Map::empty`, `union_prefer_right`, and
  `insert` calls.
- Affects: `verus-examples:guide/bst_map`,
  `verus-examples:guide/bst_map_generic`,
  `verus-examples:guide/bst_map_type_invariant`

### `[TRANS-closed-visibility]` `closed` spec fn visibility not enforced
- `pub closed spec fn` is translated with its body visible to callers in other
  modules.
- Affects: `verus-examples:modules`, `verus-examples:debug_expand`

### `[CORE-decreases]` `decreases` preservation
- Loop measures are emitted in concrete `while ... decreases ...` syntax. The
  Core AST `Stmt.loop` `measure : Option P.Expr` is populated faithfully.
- Function/procedure-level `decreases` is not part of the semantic Core AST.
  Verus-internal artifacts (`decrease%init*`, `CheckDecrease*`) are stripped
  from bodies instead of being reintroduced as Core-only printer comments.

### `[TRANS-return-comment]` Early return rendered as comment
- Verus SST encodes `return expr;` as `ret_var := expr; assume false;`.
- We still encode return internally as
  `ret_var := expr; assume [__return__]: false;`, but the local printer renders
  it back as `// return expr;` (or `// return;`) for readability until Strata
  grows native `return` support.
- We currently treat this as faithful when it is the only remaining issue.
- Affects: `vlir-tests:basic_failure`,
  `verus-examples:guide/requires_ensures`,
  `verus-examples:guide/requires_ensures_edit`,
  `verus-examples:imo_1988_6`, `verus-examples:guide/invariants`, and
  `verus-examples:set_from_vec`.

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
  current `usize`/`Vec` fallback expects `bv64`.
- **Remaining gaps**: richer non-call contexts beyond plain variables
  (for example larger arithmetic expressions, projections, and other composite
  terms that still need result-side coercion insertion).

### `[TRANS-lambda-placeholder]` Lambda / function-value placeholder
- `Unsupported.lambda` is the current fallback for real lambda abstractions and
  function-valued terms in the lowered Core AST.
- This is broader than collection constructors: it also affects plain
  `spec_fn` values, comparators passed to library functions, ghost predicates,
  and function values stored in structs/sequences.
- `choose` placeholders are tracked separately below and are not counted here.
- Affects: `verus-examples:assert_by_compute`,
  `verus-examples:bitmap`, `verus-examples:bitvector_garbage_collection`,
  `verus-examples:extensionality`, `verus-examples:guide/assert_by_compute`,
  `verus-examples:guide/exec_attr`, `verus-examples:guide/ext_equal`,
  `verus-examples:guide/lib_examples`, `verus-examples:mergesort`,
  `verus-examples:multiset`, `verus-examples:rwlock_vstd`,
  `verus-examples:trait_for_fn`, `verus-examples:vectors`,
  `vlir-tests:maps`, `vlir-tests:seqs`, `vlir-tests:sets`,
  `vlir-tests:test_vstd`

### `[TRANS-exec-spec-helper-leakage]` `exec_spec_*` examples still lower through internal helper stubs
- `exec_spec_unverified!` and `exec_spec_verified!` examples currently expose
  internal helper symbols such as `View_deep_view`, `View_V`,
  `Contrib_Exec_spec_*`, and array/slice glue procedures rather than a
  source-like surface encoding of `deep_view`, `as_slice`, and the exec/spec
  wrapper itself.
- Affects: `verus-examples:guide/exec_spec_unverified`,
  `verus-examples:guide/exec_spec_verified`

### `[TRANS-seq-len-literal-typing]` Sequence-length expressions still mix `nat` and `bv`
- Some `Seq.len()` / `Seq_len(...)` contexts still emit `bv64` literals and
  arithmetic where the surrounding Core type is `nat`, producing raw Core
  mismatches such as `Seq_len(s) == bv{64}(5)`.
- Affects: `verus-examples:guide/pervasive_example`,
  `verus-examples:recommends`

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

### `[TRANS-trait-spec-resolution]` External trait-spec symbols not preserved cleanly across modules
- External trait specifications and their helper symbols are not resolved
  cleanly across module boundaries yet, so uses of those specs can degrade into
  low-level helper names and mismatched coercion shapes.
- Affects: `verus-examples:guide/external_trait_specs`

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

### `[TRANS-broadcast-use]` `broadcast use` flattened to raw assumptions
- Source-level `broadcast use ...` proof steps are currently flattened to
  direct `assert` / `assume forall` scaffolding rather than a dedicated proof
  construct or future Strata surface syntax.
- Affects: `verus-examples:multiset`, `verus-examples:syntax`

### `[TRANS-vec-representation-gap]` `Vec` still lowers through a temporary mixed representation
- The long-term target is first-class `Vec` support in Strata/Boole, but the
  current Core fallback still models `Vec<T>` through helper APIs over a
  backing `Map bv64 T` plus an explicit length (`Vec_view`,
  `Vec_Impl__0_new`, `Vec_Impl__1_push`, `Vec_Impl__1_pop`).
- Some lowered call sites still look source-like and only thread the backing
  map, while later assertions/spec uses refer to the helper-level length. That
  mixed representation is a temporary fallback, not the intended final surface
  design.
- Affects: `verus-examples:guide/lib_examples`, `verus-examples:rfmig_script`,
  `verus-examples:syntax`, `verus-examples:vectors`

### `[TRANS-map-helper-typing]` Map helper signatures not source-faithful
- Some current Core helper declarations for map operations are emitted with the
  wrong receiver type, so source-level `Map` / store operations are no longer
  represented as well-typed map helpers in the output.
- Affects: `vlir-tests:tests/mini_c`

### `[SURFACE-sequence-empty]` `Sequence.empty` as intended future syntax
- `Sequence.empty` is now emitted intentionally as future-facing Strata syntax.
- This is treated as faithful translation and a current Strata frontend gap,
  not as a translation defect.
- Affects: `verus-examples:guide/lib_examples`,
  `verus-examples:guide/quants`, `vlir-tests:test_vstd`, and other
  sequence-heavy tests that otherwise look source-close.

### `[MODEL-unit]` Missing Strata `Unit`
- Raw Core still leaks `Tuple_ctor_0(): Unit` in places where the Verus source
  did not mention a user-visible unit value.
- Some occurrences are pure helper artifacts and should eventually be pruned;
  other occurrences need future Strata surface/model support for unit.
- Affects: `verus-examples:guide/exec_attr`, `verus-examples:mergesort`,
  `verus-examples:set_from_vec`, `verus-examples:syntax`,
  `vlir-tests:tests/mini_c`, `verus-examples:guide/invariants`

### `[TRANS-loop-helper-leakage]` Loop helper symbols leak into raw Core
- Iterator-lowered loops still expose helper symbols such as
  `Pervasive_ghost_*`, `Pervasive_exec_invariant`, and `Pervasive_arbitrary`
  in raw Core output, even though they are translator scaffolding rather than
  source-level Verus syntax.
- Affects: `verus-examples:guide/exec_attr`, `verus-examples:mergesort`,
  `verus-examples:set_from_vec`, `verus-examples:guide/invariants`,
  `verus-examples:guide/higher_order_fns`

### `[MODEL-missing-types]` Missing Strata types
- `nat` emitted as abstract type. Coercion functions declared as uninterpreted.
- Collection types: `Set`, `Verus_Map`, `Multiset`.
  `Set` and `Multiset` are still declared by the translator when referenced.
  `Map` stays prefixed because Strata Core already has a built-in `Map`.
  `Tuple`, `Std_specs_range` are also declared when referenced.
- Still missing in Strata: `Cell`, `Atomic`, `Simple_pptr`, `Unit`,
  `Arithmetic_overflow`, `Rwlock`, `Thread`, `Invariant` (keyword clash).
