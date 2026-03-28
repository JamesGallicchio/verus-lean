# Differential Status

This file tracks three things separately:
- raw Core regression outcomes from `regress_examples.sh`
- Boole smoke/elaboration status for selected cases
- manual faithfulness judgments for reviewed cases

Solver success is **not** used to classify faithfulness.

## Data Sources
- Full run:
  - command: `./tests/regress_examples.sh --all-suites`
  - run id: `20260327_174841`
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
    `verus-examples:guide/exec_attr` (`Sequence.empty` text-mode gap),
    `verus-examples:vectors` (generic `V`/`T` mismatch),
    `verus-examples:exec_termination_example` (residual iterator/ghost state),
    `verus-examples:guide/invariants` (`bv64` where `int` expected)
  - the raw summary below is still based on Core output plus `StrataVerify`

## Raw Core Regression Summary (Full Run)
Total cases: **118**

Primary statuses (sum to 118):
- export failures: 0
- expected empty exports: 1
- translate failures: 0
- strata parse failures: 0
- strata type failures: 79
- verify failures: 26
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
- `vlir-tests:mutual_recursion`, `vlir-tests:recursion`,
  `verus-examples:guide/recursion`: best current output is Boole, which
  elaborates cleanly. The raw Core run is still blocked by Strata's current
  `@[cases]` requirement for recursion over datatypes.
- `verus-examples:recursion`: Boole now recovers the `for` loop structure, but
  the overall best current condition is still not faithful because
  `reveal_with_fuel` loses the fuel amount.
- `vlir-tests:basic_failure`, `verus-examples:guide/requires_ensures`,
  `verus-examples:guide/requires_ensures_edit`, `verus-examples:imo_1988_6`:
  the local Core output now renders `return` as comments again. We still note
  that caveat under Gaps, but we classify these as faithful when the return
  comment is the only issue.

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

## faithful but different from Verus output (31)
- `vlir-tests:FindMax` (cvc5 default gives one VC unknown)
- `vlir-tests:LoopSimple` (mismatch as expected)
- `vlir-tests:datatypes` (Strata still type-fails later in the pipeline)
- `vlir-tests:matching` (Strata currently fails on nat assertions)
- `vlir-tests:demo_while` (same as FindMax)
- `vlir-tests:demo_while_loop_isolation` (same as FindMax)
- `vlir-tests:quant` (current blocker is Strata-side typing)
- `vlir-tests:rec_adt_structural` (nat emitted as a datatype; waiting for Strata native nat support)
- `verus-examples:bitvector_basic` (Strata SMT encoding issue on indexed bitvector literal)
- `verus-examples:fun_ext` (blocked by higher-order/extensional support)
- `verus-examples:generics` (generic `reveal(g)` dropped — see Gaps)
- `verus-examples:guide/modes` (Tuple type now declared; blocked by other Strata issues)
- `verus-examples:guide/datatypes` (datatype-constructor/selector VCs fail in Strata)
- `verus-examples:guide/overflow` (blocked by missing arithmetic-overflow/cast support in Strata)
- `verus-examples:guide/references` (current mismatch is Strata loop-measure reasoning)
- `verus-examples:guide/requires_ensures` (only the early-return comment caveat remains)
- `verus-examples:guide/requires_ensures_edit` (same early-return comment caveat as `guide/requires_ensures`)
- `verus-examples:statements` (mixed-width bitvector arithmetic with explicit width extension)
- `verus-examples:quantifiers` (Strata type error: `tr(i)` where `i: nat` but `tr` expects `int`)
- `verus-examples:assorted_demo` (`#[verifier::external]` fn dropped, `#[verifier::external_body]` fn emitted with specs and empty body)
- `verus-examples:guide/integers` (missing `bv8_to_nat` coercion — Verus widening cast erasure)
- `verus-examples:impl_basic` (structs, methods, generics, ensures clauses preserved)
- `vlir-tests:integer_ring` (Strata type error only on intentionally-failing `type_fail`)
- `verus-examples:proposal-rw2022` (coercions at call sites, termination-check artifacts stripped)
- `verus-examples:bitvector_equivalence` (bitvector proofs with triggers and decreases)
- `verus-examples:adts` (datatypes, variant checks, structural equality; TODO: `matches` clause)
- `verus-examples:rw2022_script` (prime testing with quantifiers/triggers, fibo with decreases)
- `verus-examples:trigger_loops` (uninterpreted fns, multi-triggers, coercions; TODO: `choose`)
- `vlir-tests:tests/LoopSimpleWithSpec` (loop with spec, recursive spec fn, coercions at call sites)
- `verus-examples:imo_1988_6` (only the printed return-comment caveat remains)
- `verus-examples:power_of_2` (Strata type error: `int` literals where `nat` expected)

## not faithful translation (8)
- `verus-examples:datatypes` (decrease/recursion artifacts not source-close enough yet)
- `verus-examples:doubly_linked` (pointer-heavy translation not source-faithful yet)
- `verus-examples:external` (`Ghost<int>` erased to plain `int`; `println!` in `external_body` fn not translated)
- `verus-examples:integers` (remaining non-faithful call-argument coercion shape)
- `verus-examples:modules` (`closed` visibility not preserved — see Gaps)
- `verus-examples:test_expand_errors` (`hide` not emitted, `reveal_with_fuel` fuel amount lost — see Gaps)
- `verus-examples:debug_expand` (`hide` not emitted; `closed` spec fn body visible — see Gaps)
- `verus-examples:recursion` (`reveal_with_fuel` loses fuel amount; Boole output now recovers the `for` loop shape, but the source-level fuel behavior is still not preserved)

## others (63) [WIP]

### missing Strata categories/model types (16)
- Missing types: `Unit`, `Atomic`, `Cell`, `Simple_pptr`, `Arithmetic_overflow`,
  `Rwlock`, `Thread`. `Invariant` clashes with Strata's `invariant` keyword.
- Concrete example tests for each missing type:
  - `Unit`: `vlir-tests:demo_for` (current Core loop lowering still leaves `Tuple_ctor_0`)
  - `Atomic`: `verus-examples:atomics`
  - `Cell`: `verus-examples:cells`
  - `Simple_pptr`: `verus-examples:rfmig_script`
  - `Arithmetic_overflow`: `verus-examples:overflow`
  - `Rwlock`: `verus-examples:rwlock_vstd`
  - `Thread`: `verus-examples:thread`
  - `Invariant`: `verus-examples:invariants`
- Verus `Seq<T>` now lowers to Strata's built-in `Sequence T`.
  `Tuple`, `Std_specs_range`, `Set`, `Verus_Map`, and `Multiset` are
  declared when referenced. Free type variables (`A`, `T`, etc.) are
  auto-declared as abstract types.
- Tests: `verus-examples:atomics`, `verus-examples:basic_lock1`, `verus-examples:basic_lock2`, `verus-examples:cells`, `verus-examples:doubly_linked_xor`, `verus-examples:even_cell`, `verus-examples:float`, `verus-examples:guide/interior_mutability`, `verus-examples:guide/strings`, `verus-examples:invariants`, `verus-examples:overflow`, `verus-examples:rwlock_vstd`, `verus-examples:statics`, `verus-examples:thread`, `vlir-tests:sets`, `verus-examples:exec_termination_example`

### polymorphic tuple helper panic in StrataVerify (1)
- The emitted polymorphic tuple helper declarations (`Tuple_ctor_2`, `Tuple_2_0`, `Tuple_2_1`) trigger a DDM/Core
  translation panic (`translateExpr unexpected type for ... add_expr`) when
  instantiated at `bv32`.
- Tests: `verus-examples:syntax_attr`

### missing stdlib/pervasive symbols (19)
- Auto-stub pass emits uninterpreted **function and procedure stubs** for
  referenced-but-undeclared symbols using **typed signatures from JSON
  call-site annotations** (e.g. `Seq_len(x0: Sequence int): nat`).
- Stubs and type declarations are only emitted when referenced.
- Multi-shard test script bug fixed: tests with module shards (e.g.
  `broadcast_proof`, `guide/quants`) now correctly load all shards.
- Current per-test blockers:
  - Incomplete `Vec_view` bridge between exec `Vec` (`Map bv64 T` + `len`) and spec `Sequence T`: `broadcast_proof`, `guide/exec_attr`, `guide/lib_examples`, `guide/quants`, `mergesort`, `nevd_script`, `set_from_vec`, `syntax`
  - `Undeclared type impl_*`: `guide/higher_order_fns`
  - `Undeclared type Simple_pptr`: `rfmig_script`
  - Type mismatch (`nat`/`bv64`/`int`): `guide/const`, `nonlinear`, `seqs`, `test_array`
  - `Undeclared type or category Unit` from lingering `Tuple_ctor_0` in Core loop lowering: `demo`, `demo_for` (Core-only; current Boole output elaborates cleanly)
  - `Unsupported.lambda`: `maps`
  - Other: `tests/mini_c`, `test_vstd`, `traits` (body type mismatch), `guide/invariants`

### generic/category typing mismatch (18)
- Verus `Seq<T>` now lowers to Strata's built-in `Sequence T`.
  The optional minimal prelude now only supplies typed shim declarations for
  `Seq_len`, higher-order `Seq_lib_*`, `Vec_view`, `Seq_lib_to_set`, and
  `Set_finite`. Simple sequence helpers such as first/last/subrange/remove
  are lowered directly to `Sequence.select`, `Sequence.take`,
  `Sequence.drop`, and `Sequence.append`. Sequence literals now start from
  built-in `Sequence.empty`.
- The remaining failures in these files are later blockers:
  current Strata text-mode support for `Sequence.empty`, `Unsupported.lambda`,
  `nat`/`int`/`bv` mismatches, missing
  `Set`/`Multiset` semantics, and unresolved higher-order sequence operators.
- Manual review found none are faithful yet. Key blockers per test:
  - `basic_failure`: no heap model for references (`&mut` parameter)
  - `prelude`: `seq!` now lowers through `Sequence.empty`/`Sequence.build`, but
    higher-order `Seq_new` is still a stub
  - `recommends`: same `Sequence`/set-model issue; `spec_affirm` lost in translation
  - `guide/pervasive_example`: `Sequence`/set support still incomplete
  - `guide/exec_spec_unverified`: `exec_spec_unverified!` macro needs more
    thought; `Sequence`/set support still incomplete
  - `guide/assert_by_compute`: nat literal inference needed (is `exp - 1`
    `int` or `nat`?); `all_spec` semantics not captured (see Verus guide on
    assert_by_compute); closure support needed for `let prop = |x| p(x as
    usize);`
  - `extensionality`: `Sequence`/set extensionality still incomplete; needs closer review later
  - `multiset`: `Sequence` lowers cleanly now, but `broadcast use` is ignored and `Multiset` semantics are still missing
  - `bitmap`: `Sequence` plus closure support still needed
  - `bitvector_garbage_collection`: closure support needed
  - `calc`: bv8/int type mismatch in calc chain
  - `guide/bst_map`, `guide/bst_map_generic`, `guide/bst_map_type_invariant`:
    undeclared `Fuel` type
  - `guide/exec_spec_verified`: undeclared `View_V` type
  - `guide/ext_equal`: `Sequence`/extensional-equality support needed
  - `vectors`: undeclared type `T`
- Tests: `verus-examples:assert_by_compute`, `verus-examples:basic_failure`, `verus-examples:bitmap`, `verus-examples:bitvector_garbage_collection`, `verus-examples:calc`, `verus-examples:extensionality`, `verus-examples:guide/assert_by_compute`, `verus-examples:guide/bst_map`, `verus-examples:guide/bst_map_generic`, `verus-examples:guide/bst_map_type_invariant`, `verus-examples:guide/exec_spec_unverified`, `verus-examples:guide/exec_spec_verified`, `verus-examples:guide/ext_equal`, `verus-examples:guide/pervasive_example`, `verus-examples:multiset`, `verus-examples:prelude`, `verus-examples:recommends`, `verus-examples:vectors`

### higher-order/lambda support gap (1)
- `Unsupported.lambda` placeholder for lambda/closure/choose expressions.
- Tests: `verus-examples:trait_for_fn`

### `choose` operator not faithfully translated
- Verus's `choose|z| g(z)` (Hilbert's epsilon) is parsed as `Bind.Lambda [z]`,
  erasing the predicate. The faithful encoding would be
  `havoc z; assume (exists z' :: g(z')) ==> g(z);`.
- Affects: `verus-examples:trigger_loops` (`choose_example`, `quantifier_example`)

### Raw Core-only mutual recursion over `int` still blocked by `@[cases]` requirements (3)
- Core mutual-recursive spec functions are now emitted as `rec` blocks, and the
  old `Procedure ... not found!` forward-reference failure is gone.
- The remaining Core blocker is Strata's current recursive-function
  requirement that the recursive parameter marked `@[cases]` have a datatype
  type. These Verus examples recurse over `int`, so the Core path still stops
  at `Recursive function ... requires a @[cases] parameter`.
- The current Boole output already elaborates for these tests, so this is a
  Core-only gap rather than the best available condition.
- Tests: `verus-examples:guide/recursion`, `vlir-tests:mutual_recursion`, `vlir-tests:recursion`

### trait-spec symbol resolution gap (1)
- Trait-spec symbols not preserved across module boundaries.
- Tests: `verus-examples:guide/external_trait_specs`

### complex type-check failures (2)
- `verus-examples:playground`: synthetic temp symbol not in context.
- `verus-examples:recursive_types`: nested datatype shape unsupported in Strata.

## Gaps

### `opaque` / `reveal` partial support
- Non-generic opaque spec functions emitted **declaration-only**. `reveal(f)`
  emitted as `assume forall params :: f(params) == body;`.
- **Generic reveals dropped**: `reveal(g)` where `g` has type parameters is
  silently skipped (Verus erases type args from `Fuel` at SST level).
- Affects: `verus-examples:generics`

### `hide` not supported
- `hide(f)` not emitted — function body remains visible to the solver.
- Affects: `verus-examples:test_expand_errors`, `verus-examples:debug_expand`

### `reveal_with_fuel` loses fuel amount
- `reveal_with_fuel(f, n)` lowered to same `assume forall` as `reveal(f)`,
  discarding fuel amount `n`.
- Affects: `verus-examples:test_expand_errors`, `verus-examples:recursion`

### `closed` spec fn visibility not enforced
- `pub closed spec fn` translated with body visible. Callers in other modules
  should not see it.
- Affects: `verus-examples:modules`, `verus-examples:debug_expand`

### `decreases` preservation
- Loop measures are emitted in concrete `while ... decreases ...` syntax. The
  Core AST `Stmt.loop` `measure : Option P.Expr` is populated faithfully.
- Function/procedure-level `decreases` is not part of the semantic Core AST.
  Verus-internal artifacts (`decrease%init*`, `CheckDecrease*`) are stripped
  from bodies instead of being reintroduced as Core-only printer comments.

### Early return
- Verus SST encodes `return expr;` as `ret_var := expr; assume false;`.
- We still encode return internally as
  `ret_var := expr; assume [__return__]: false;`, but the local printer renders
  it back as `// return expr;` (or `// return;`) for readability until Strata
  grows native `return` support.
- This is no longer semantically faithful in the emitted Core for
  return-sensitive procedures such as `vlir-tests:basic_failure`,
  `verus-examples:guide/requires_ensures`,
  `verus-examples:guide/requires_ensures_edit`, and
  `verus-examples:imo_1988_6`.

### `HasType` overflow guards dropped
- Verus `HasType(U32, e)` assertions silently skipped in Core output.
- Affects: many exec-mode integer arithmetic tests

### Extensional equality lowered to spec equality
- `=~=` (`ExtEq`) lowered to `==` (`Eq Spec`), losing extensional semantics
  for collection types.
- Affects: `verus-examples:guide/ext_equal`

### `RevealString` / `Air` statements erased
- `RevealString` and `Air` statements parsed as empty blocks.
- `Fuel` statements parsed into `Stm.Reveal` and lowered to `assume` equations
  for non-generic spec functions. Generic `Fuel` still dropped.

### Widening casts partially inserted
- Verus erases widening casts (`nat as int`, `u16 as int`) at SST level.
- Type-directed coercion insertion now adds `bv*_to_nat_u`/`bv*_to_int_u`
  at function/procedure call sites.
- **Remaining gaps**: non-call contexts (comparisons, quantifier bodies).

### Missing Strata types
- `nat` emitted as abstract type. Coercion functions declared as uninterpreted.
- Collection types: `Sequence` (built-in), `Set`, `Verus_Map`, `Multiset`.
  Verus `Seq<T>` now lowers to Strata's built-in `Sequence T`; `Set` and
  `Multiset` are still declared by the translator when referenced.
  `Map` stays prefixed because Strata Core already has a built-in `Map`.
  `Tuple`, `Std_specs_range` are also declared when referenced.
- Still missing in Strata: `Cell`, `Atomic`, `Simple_pptr`, `Unit`,
  `Arithmetic_overflow`, `Rwlock`, `Thread`, `Invariant` (keyword clash).
