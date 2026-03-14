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
- `passing`: behavior aligns with expectation and translation is faithful.
- `faithful but different from Verus output`: translation is faithful, but Verus/Strata outcomes differ or Strata lacks support.
- `not faithful translation`: translation currently drops/changes important semantics compared to source-level intent.

## passing (21)
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

## faithful but different from Verus output (13)
- `vlir-tests:FindMax` (cvc5 default gives one VC unknown)
- `vlir-tests:LoopSimple` (expected mismatch bucket)
- `vlir-tests:matching` (Strata currently fails on nat assertions)
- `vlir-tests:demo_while` (same as FindMax)
- `vlir-tests:demo_while_loop_isolation` (same as FindMax)
- `vlir-tests:rec_adt_structural` (emit nat as a dataype; waiting for Strata native support for nat)
- `verus-examples:bitvector_basic` (Core translation is semantically faithful but Strata SMT encoding panics on indexed bitvector literal `(_ bv0 32)` while discharging `bit_and32_auto_ensures_3`)
- `verus-examples:fun_ext` (blocked by higher-order/extensional support)
- `verus-examples:generics` (2 goals hit Strata "Unimplemented encoding for type var"; generic `reveal(g)` dropped — see Gaps)
- `verus-examples:guide/modes` (blocked by missing `Tuple`/`Tuple_ctor_2` support)
- `verus-examples:guide/datatypes` (datatype-constructor/selector VCs currently fail in Strata despite faithful emission)
- `verus-examples:guide/overflow` (blocked by missing arithmetic-overflow/cast support in Strata)
- `verus-examples:statements` (mixed-width bitvector arithmetic lowered with explicit width extension, e.g. `bv8_to_bv64_u`)

## not faithful translation (5)
- `verus-examples:datatypes` (decrease/recursion artifacts are not source-close enough yet)
- `verus-examples:doubly_linked` (pointer-heavy translation not source-faithful yet)
- `verus-examples:external` (`Ghost<int>` erased to plain `int`; `println!` in `external_body` fn not translated)
- `verus-examples:integers` (remaining non-faithful call-argument coercion shape)
- `verus-examples:modules` (`closed` visibility not preserved: other modules cannot see the function's body)

## others (79) [WIP]
- manual review of generated `.core.st` (logs are secondary and may only show the first downstream error)

### missing Strata categories/model types (14)
- Potential roadblock/todo: add missing category/model support in Strata/Boole and keep translation faithful in the meantime.
- Observed blocker patterns include: `Undeclared type or category Unit/Atomic/Cell/Simple_pptr/Ops_Arith_add_Output/String_string/Arithmetic_overflow/Rwlock/Thread/Set`.
- Tests: `verus-examples:atomics`, `verus-examples:basic_lock1`, `verus-examples:basic_lock2`, `verus-examples:cells`, `verus-examples:doubly_linked_xor`, `verus-examples:even_cell`, `verus-examples:float`, `verus-examples:guide/interior_mutability`, `verus-examples:guide/strings`, `verus-examples:overflow`, `verus-examples:rwlock_vstd`, `verus-examples:statics`, `verus-examples:thread`, `vlir-tests:sets`

### missing stdlib/pervasive symbols (21)
- Potential roadblock/todo: add/prelude-bind missing symbols and preserve them in translation (`Seq_*`, `Map_*`, `Set_*`, `Pervasive_*`, tuple selectors, etc.).
- Observed blocker patterns include: `Unknown expr identifier Seq_empty/Layout_size_of/Pervasive_arbitrary/sqrt` and `Unknown variable Seq_len/Seq_push/Map_index/Set_contains/Tuple_2_0/Pervasive_exec_invariant`.
- Tests: `verus-examples:broadcast_proof`, `verus-examples:guide/const`, `verus-examples:guide/exec_attr`, `verus-examples:guide/higher_order_fns`, `verus-examples:guide/invariants`, `verus-examples:guide/lib_examples`, `verus-examples:guide/quants`, `verus-examples:imo_1988_6`, `verus-examples:mergesort`, `verus-examples:nevd_script`, `verus-examples:rfmig_script`, `verus-examples:set_from_vec`, `verus-examples:syntax`, `vlir-tests:demo`, `vlir-tests:demo_for`, `vlir-tests:maps`, `vlir-tests:nonlinear`, `vlir-tests:seqs`, `vlir-tests:test_array`, `vlir-tests:test_vstd`, `vlir-tests:tests/mini_c`

### generic/category typing mismatch (18)
- Potential roadblock/todo: align category/type-arg handling across parser/lowering and Strata typing, especially around projection/generic category expectations.
- Observed blocker patterns include: `Expected category`, `Expression has type V when T expected`, `Expression has type Map T bv64 when Map T int expected`.
- Tests: `verus-examples:assert_by_compute`, `verus-examples:basic_failure`, `verus-examples:bitmap`, `verus-examples:bitvector_garbage_collection`, `verus-examples:calc`, `verus-examples:extensionality`, `verus-examples:guide/assert_by_compute`, `verus-examples:guide/bst_map`, `verus-examples:guide/bst_map_generic`, `verus-examples:guide/bst_map_type_invariant`, `verus-examples:guide/exec_spec_unverified`, `verus-examples:guide/exec_spec_verified`, `verus-examples:guide/ext_equal`, `verus-examples:guide/pervasive_example`, `verus-examples:multiset`, `verus-examples:prelude`, `verus-examples:recommends`, `verus-examples:vectors`

### bitvector/int typing mismatch (11)
- Potential roadblock/todo: keep faithful cast emission but reduce avoidable bv->int mixing; add typing-safe width harmonization where possible without semantic weakening.
- Observed blocker patterns include: `Encountered bv* expression when int/bool expected`, `Expression has type int when bv* expected`, `Expression has type bv8 when bv16 expected`.
- Tests: `verus-examples:adts`, `verus-examples:assorted_demo`, `verus-examples:debug_expand`, `verus-examples:guide/integers`, `verus-examples:impl_basic`, `verus-examples:proposal-rw2022`, `verus-examples:quantifiers`, `verus-examples:recursion`, `verus-examples:rw2022_script`, `vlir-tests:integer_ring`, `vlir-tests:tests/LoopSimpleWithSpec`

### missing decrease helpers (4)
- Potential roadblock/todo: Strata side probably needs support for decrease checks used by Verus exports.
- Observed blocker pattern: `Unknown variable CheckDecreaseInt`.
- Tests: `verus-examples:bitvector_equivalence`, `verus-examples:exec_termination_example`, `verus-examples:power_of_2`, `verus-examples:syntax_attr`

### higher-order/lambda support gap (1)
- Potential roadblock/todo: add Strata support for lambda/arrow constructs (or equivalent encoding accepted by Strata verifier).
- Observed blocker pattern: `Unknown expr identifier Unsupported.lambda`.
- Tests: `verus-examples:trait_for_fn`

### mutual recursion / forward-reference gap (3)
- Potential roadblock/todo: add Strata support for mutually recursive function declarations. Current emitted Core contains both functions, but the first function body cannot resolve the second at type-check time.
- Observed blocker patterns: `Unknown variable is_even`, `Unknown variable M_is_even`.
- Tests: `verus-examples:guide/recursion`, `vlir-tests:mutual_recursion`, `vlir-tests:recursion`

### trait-spec symbol resolution gap (1)
- Potential roadblock/todo: preserve trait-spec symbols and referenced spec bodies across module/import boundaries in Core emission.
- Observed blocker pattern: `Unknown variable SummarizerSpec_spec_summary`.
- Tests: `verus-examples:guide/external_trait_specs`

### unresolved local/spec symbols in emitted Core (3)
- Potential roadblock/todo: investigate symbol-drop bugs in translation/emission (`e`, `g`, `T_req`/`T_ens`) and ensure required declarations are emitted.
- Observed blocker patterns: `Unknown variable e`, `Unknown variable g`, `Unknown variable T_req`.
- Tests: `verus-examples:test_expand_errors`, `verus-examples:traits`, `verus-examples:trigger_loops`

### invariant form mismatch (1)
- Potential roadblock/todo: align emitted invariant shape with current Strata `Invariant` argument expectations.
- Observed blocker pattern: `Unexpected argument to Invariant`.
- Tests: `verus-examples:invariants`

### complex type-check failures (needs focused triage) (2)
- Potential roadblock/todo: inspect full logs and generated Core for these two outliers, then split into a concrete bucket after diagnosis.
- Specific notes: `verus-examples:playground` modifies clause references a huge synthetic temp symbol not present in context; `verus-examples:recursive_types` uses nested datatype shape (`groundedList` inside `dataOption`) currently unsupported in Strata Core.
- Tests: `verus-examples:playground`, `verus-examples:recursive_types`

## Gaps

### `opaque` / `reveal` partial support
- Non-generic opaque spec functions are now emitted **declaration-only** (no body)
  in Core. `reveal(f)` is emitted as
  `assume forall params :: f(params) == body;` which faithfully models Verus's
  reveal semantics.
- **Generic reveals are currently dropped**: `reveal(g)` where `g` has type
  parameters is silently skipped. The Fuel JSON currently contains only the
  function path and fuel amount, with no type arguments (Verus erases the
  `<u8>` from `reveal(g::<u8>)` at the SST level). To emit the correct Core
  (`procedure test_g1<A>(...) { assume forall a: A :: g(a) == a; ... }`)
  we need to (1) recover the type parameter `A` for the enclosing procedure
  signature, and (2) thread it into the assume. Two paths forward:
  - **Modify Verus export**: add type arguments to the `Fuel` SST variant and
    serialize them in the JSON, giving the translator direct access.
  - **Infer from call sites**: VLIR `Call` nodes carry `typs : List Typ`, so
    we can scan the procedure body for calls to the revealed function and
    extract the type instantiation from there.
- Affects: `verus-examples:generics` (generic `g` reveal dropped)

### `closed` spec fn visibility not enforced
- `pub closed spec fn` is translated with the body visible. Callers in other modules
  should not see it.
- Affects: `verus-examples:modules`

### `decreases` gaps
- Loop measures are emitted as `// decreases (expr)` comments because 
  Strata has no parser support for `decreases` yet. The AST is faithful.
- Recursive-function `decreases` (`SpecFn.decreases`) are dropped in
  `specFnToCore` because Strata Core currently has no function-level
  termination measure syntax.
- Self-recursive `SpecFn` bodies are currently emitted declaration-only
  (no body) to avoid Strata recursive-function resolution failures.
- Affects: all loop tests, `verus-examples:modules` (recursive spec fns)

### `HasType` overflow guards dropped
- Verus emits `HasType(U32, e)` assertions before arithmetic to check that the
  result fits in the target width. These are silently skipped in Core output,
  meaning overflow checks are lost.
- Affects: many test JSONs with exec-mode integer arithmetic (e.g.
  `verus-examples:guide/references`, `vlir-tests:FindMax`,
  `vlir-tests:LoopSimple`)

### Extensional equality lowered to spec equality
- `=~=` (`ExtEq`) is silently lowered to ordinary `==` (`Eq Spec`). For
  collection types this loses the extensional semantics.
- Affects: `verus-examples:guide/ext_equal`, tests using `=~=` on sequences/sets

### `RevealString` / `Air` statements erased
- `RevealString` (string-keyed reveal) and `Air` (backend-specific directives)
  statements are parsed as empty blocks.
- `Fuel` statements are now parsed into `Stm.Reveal` and lowered to `assume`
  equations for non-generic spec functions (see opaque/reveal section above).
  Generic-function Fuel statements are still dropped.
- Affects: `verus-examples:guide/strings` (RevealString)

### Missing Strata Core/Boole types and primitives
- Native `Nat` typing/arithmetic support is still incomplete in Strata/Boole.
  The translator now emits nat as a datatype (without conversion from/to int), 
  which is more faithful to the Verus source but wouldn't be parsed by Strata.
- No cast/coercion primitives or semantics for `bv*_to_int_{u,s}`.
- Missing model types: `Tuple`, `Cell`, `Atomic`, `Set`, `arrow`, `Unit`, etc.
- Missing stdlib/pervasive symbols used by Verus exports: `Seq_*`, `Map_*`, `Pervasive_*`, etc.
