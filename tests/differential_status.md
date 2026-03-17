# Differential Status

This file tracks two things separately:
- raw regression outcomes from `regress_examples.sh`
- manual faithfulness judgments for reviewed cases

Solver success is **not** used to classify faithfulness.

## Data Sources
- Full run:
  - command: `./tests/regress_examples.sh --all-suites`
  - run id: `20260311_005016`
  - solver: `cvc5`

## Raw Regression Summary (Full Run)
Total cases: **117**

Primary statuses (sum to 117):
- export failures: 0
- expected empty exports: 1
- translate failures: 0
- strata parse failures: 0
- strata type failures: 83
- verify failures: 16
- verify success: 16
- expected mismatches: 1

Additional counters (do not affect total):
- mismatch (Verus pass, Strata fail): 11
- mismatch (Verus fail, Strata pass): 0

## Translation Quality Labels
- `faithful and same as Verus output`: translation is faithful and Strata verification outcome matches Verus.
- `faithful but different from Verus output`: translation is faithful, but Verus/Strata outcomes differ or Strata lacks support.
- `not faithful translation`: translation currently drops/changes important semantics compared to source-level intent.

## faithful and same as Verus output (21)
- `vlir-tests:datatypes`
- `vlir-tests:proof_fn`
- `vlir-tests:quant`
- `vlir-tests:test_requires`
- `vlir-tests:test_specfn`
- `vlir-tests:test_opaque_reveal` (opaque function declaration-only + reveal as assume)
- `vlir-tests:basic_failure` (fail as expected)
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
- `verus-examples:guide/references`
- `verus-examples:guide/requires_ensures`
- `verus-examples:guide/requires_ensures_edit`

## faithful but different from Verus output (26)
- `vlir-tests:FindMax` (cvc5 default gives one VC unknown)
- `vlir-tests:LoopSimple` (mismatch as expected)
- `vlir-tests:matching` (Strata currently fails on nat assertions)
- `vlir-tests:demo_while` (same as FindMax)
- `vlir-tests:demo_while_loop_isolation` (same as FindMax)
- `vlir-tests:rec_adt_structural` (nat emitted as a datatype; waiting for Strata native nat support)
- `verus-examples:bitvector_basic` (Strata SMT encoding issue on indexed bitvector literal)
- `verus-examples:fun_ext` (blocked by higher-order/extensional support)
- `verus-examples:generics` (generic `reveal(g)` dropped — see Gaps)
- `verus-examples:guide/modes` (Tuple type now declared; blocked by other Strata issues)
- `verus-examples:guide/datatypes` (datatype-constructor/selector VCs fail in Strata despite faithful emission)
- `verus-examples:guide/overflow` (blocked by missing arithmetic-overflow/cast support in Strata)
- `verus-examples:statements` (mixed-width bitvector arithmetic with explicit width extension)
- `verus-examples:quantifiers` (Strata type error: `tr(i)` where `i: nat` but `tr` expects `int`)
- `verus-examples:assorted_demo` (`#[verifier::external]` fn dropped, `#[verifier::external_body]` fn emitted with specs and empty body)
- `verus-examples:guide/integers` (missing `bv8_to_nat` coercion — Verus widening cast erasure)
- `verus-examples:impl_basic` (structs, methods, generics, ensures clauses preserved)
- `vlir-tests:integer_ring` (Strata type error only on intentionally-failing `type_fail`)
- `verus-examples:proposal-rw2022` (coercions at call sites, `// decreases` preserved, termination-check artifacts stripped)
- `verus-examples:bitvector_equivalence` (bitvector proofs with triggers and decreases)
- `verus-examples:adts` (datatypes, variant checks, structural equality; TODO: `matches` clause)
- `verus-examples:rw2022_script` (prime testing with quantifiers/triggers, fibo with decreases)
- `verus-examples:trigger_loops` (uninterpreted fns, multi-triggers, coercions; TODO: `choose`)
- `vlir-tests:tests/LoopSimpleWithSpec` (loop with spec, recursive spec fn, coercions at call sites)
- `verus-examples:imo_1988_6` (parses and type-checks; nonlinear arithmetic proofs)
- `verus-examples:power_of_2` (Strata type error: `int` literals where `nat` expected)

## not faithful translation (8)
- `verus-examples:datatypes` (decrease/recursion artifacts not source-close enough yet)
- `verus-examples:doubly_linked` (pointer-heavy translation not source-faithful yet)
- `verus-examples:external` (`Ghost<int>` erased to plain `int`; `println!` in `external_body` fn not translated)
- `verus-examples:integers` (remaining non-faithful call-argument coercion shape)
- `verus-examples:modules` (`closed` visibility not preserved — see Gaps)
- `verus-examples:test_expand_errors` (`hide` not emitted, `reveal_with_fuel` fuel amount lost — see Gaps)
- `verus-examples:debug_expand` (`hide` not emitted; `closed` spec fn body visible — see Gaps)
- `verus-examples:recursion` (`reveal_with_fuel` loses fuel amount; for-loop ghost iterator complexity)

## others (62) [WIP]

### missing Strata categories/model types (17)
- Missing types: `Unit`, `Atomic`, `Cell`, `Simple_pptr`, `Arithmetic_overflow`,
  `Rwlock`, `Thread`. `Invariant` clashes with Strata's `invariant` keyword.
- `Tuple`, `Std_specs_range`, `Verus_Seq`, `Verus_Set`, `Verus_Map`,
  `Verus_Multiset` are now declared. Free type variables (`A`, `T`, etc.)
  are auto-declared as abstract types.
- Tests: `verus-examples:atomics`, `verus-examples:basic_lock1`, `verus-examples:basic_lock2`, `verus-examples:cells`, `verus-examples:doubly_linked_xor`, `verus-examples:even_cell`, `verus-examples:float`, `verus-examples:guide/interior_mutability`, `verus-examples:guide/strings`, `verus-examples:invariants`, `verus-examples:overflow`, `verus-examples:rwlock_vstd`, `verus-examples:statics`, `verus-examples:thread`, `vlir-tests:sets`, `verus-examples:exec_termination_example`, `verus-examples:syntax_attr`

### missing stdlib/pervasive symbols (19)
- Auto-stub pass emits uninterpreted **function and procedure stubs** for
  referenced-but-undeclared symbols using **typed signatures from JSON
  call-site annotations** (e.g. `Seq_len(x0: Verus_Seq int): nat`).
- Stubs and type declarations are only emitted when referenced.
- Multi-shard test script bug fixed: tests with module shards (e.g.
  `broadcast_proof`, `guide/quants`) now correctly load all shards.
- Current per-test blockers:
  - `Verus_Seq T` vs `Map T bv64` mismatch: `broadcast_proof`, `guide/exec_attr`, `guide/lib_examples`, `guide/quants`, `mergesort`, `nevd_script`, `set_from_vec`, `syntax`
  - `Undeclared type impl_*`: `guide/higher_order_fns`
  - `Undeclared type Simple_pptr`: `rfmig_script`
  - Type mismatch (`nat`/`bv64`/`int`): `guide/const`, `nonlinear`, `seqs`, `test_array`
  - `Unknown expr identifier VERUS_ghost_iter`: `demo`, `demo_for`
  - `Unsupported.lambda`: `maps`
  - Other: `tests/mini_c`, `test_vstd`, `traits` (body type mismatch), `guide/invariants`

### generic/category typing mismatch (18)
- Reviewed by agent: 11 assessed as faithful translations blocked by Strata
  type-checker issues, 7 partially faithful.
- Observed blockers: `Undeclared type Fuel/View_V/T`, `Verus_Seq` vs `Map`
  mismatch, type width mismatches, `Unsupported.lambda`.
- Tests: `verus-examples:assert_by_compute`, `verus-examples:basic_failure`, `verus-examples:bitmap`, `verus-examples:bitvector_garbage_collection`, `verus-examples:calc`, `verus-examples:extensionality`, `verus-examples:guide/assert_by_compute`, `verus-examples:guide/bst_map`, `verus-examples:guide/bst_map_generic`, `verus-examples:guide/bst_map_type_invariant`, `verus-examples:guide/exec_spec_unverified`, `verus-examples:guide/exec_spec_verified`, `verus-examples:guide/ext_equal`, `verus-examples:guide/pervasive_example`, `verus-examples:multiset`, `verus-examples:prelude`, `verus-examples:recommends`, `verus-examples:vectors`

### higher-order/lambda support gap (1)
- `Unsupported.lambda` placeholder for lambda/closure/choose expressions.
- Tests: `verus-examples:trait_for_fn`

### `choose` operator not faithfully translated
- Verus's `choose|z| g(z)` (Hilbert's epsilon) is parsed as `Bind.Lambda [z]`,
  erasing the predicate. The faithful encoding would be
  `havoc z; assume (exists z' :: g(z')) ==> g(z);`.
- Affects: `verus-examples:trigger_loops` (`choose_example`, `quantifier_example`)

### mutual recursion / forward-reference gap (3)
- Strata cannot resolve the second function when type-checking the first
  in a mutually recursive pair.
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
- Loop measures emitted as `// decreases (expr)` comments. The Core AST
  `Stmt.loop` has `measure : Option P.Expr` which is populated faithfully.
- Spec function `decreases` emitted as `// decreases (expr)` comments via
  a side map (not stored in semantic `Func.axioms`).
- Procedure `decreases` emitted in spec block. Verus-internal artifacts
  (`decrease%init*`, `CheckDecrease*`) stripped from bodies.

### Early return
- Verus SST encodes `return expr;` as `ret_var := expr; assume false;`.
- We emit `// return expr;` — a comment-only sentinel (encoded as
  `assert [__return__]: true` in the AST). When Strata adds native
  `return` support, the comment can become a real statement.

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
- Collection types: `Verus_Seq`, `Verus_Set`, `Verus_Map`, `Verus_Multiset`
  (prefixed to avoid Strata reserved name clashes). `Tuple`, `Std_specs_range`
  also declared. Type declarations only emitted when referenced.
- Still missing in Strata: `Cell`, `Atomic`, `Simple_pptr`, `Unit`,
  `Arithmetic_overflow`, `Rwlock`, `Thread`, `Invariant` (keyword clash).
