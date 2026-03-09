# Differential Status

This file tracks two things separately:
- raw regression outcomes from `regress_examples.sh`
- manual faithfulness judgments for reviewed cases

Solver success is **not** used to classify faithfulness.

## Data Sources
- Full run:
  - command: `./tests/regress_examples.sh --all-suites`
  - run id: `20260309_102607`
  - solver: `cvc5`

## Raw Regression Summary (Full Run)
Total cases: **117**

Primary statuses (sum to 117):
- export failures: 1
- expected empty exports: 1
- translate failures: 0
- strata parse failures: 0
- strata type failures: 83
- verify failures: 15
- verify success: 16
- expected mismatches: 1

Additional counters (do not affect total):
- mismatch (Verus pass, Strata fail): 10
- mismatch (Verus fail, Strata pass): 0

Current export failures in the full run:
- `rust-verify-tests:basic-fe9539cec5a28303-test_ret/test`

## Translation Quality Labels
- `passing`: behavior aligns with expectation and translation is faithful.
- `faithful but different from Verus output`: translation is faithful, but Verus/Strata outcomes differ or Strata lacks support.
- `not faithful translation`: translation currently drops/changes important semantics compared to source-level intent.

## passing (20)
- `vlir-tests:datatypes`
- `vlir-tests:proof_fn`
- `vlir-tests:quant`
- `vlir-tests:test_requires`
- `vlir-tests:test_specfn`
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

## faithful but different from Verus output (11)
- `vlir-tests:FindMax` (cvc5 default gives one VC unknown)
- `vlir-tests:LoopSimple` (expected mismatch bucket)
- `vlir-tests:demo_while` (same as FindMax)
- `vlir-tests:demo_while_loop_isolation` (same as FindMax)
- `verus-examples:bitvector_basic` (Core translation is semantically faithful but Strata SMT encoding panics on indexed bitvector literal `(_ bv0 32)` while discharging `bit_and32_auto_ensures_3`)
- `verus-examples:fun_ext` (blocked by higher-order/extensional support)
- `verus-examples:generics` (2 goals hit Strata "Unimplemented encoding for type var"; 1 goal needs `reveal`)
- `verus-examples:guide/modes` (blocked by missing `Tuple`/`Tuple_ctor_2` support)
- `verus-examples:guide/datatypes` (datatype-constructor/selector VCs currently fail in Strata despite faithful emission)
- `verus-examples:guide/overflow` (blocked by missing arithmetic-overflow/cast support in Strata)
- `verus-examples:statements` (mixed-width bitvector arithmetic lowered with explicit width extension, e.g. `bv8_to_bv64_u`)

## not faithful translation (6)
- `vlir-tests:matching` (`nat` lowered as `int`, losing non-negativity semantics)
- `verus-examples:datatypes` (decrease/recursion artifacts are not source-close enough yet)
- `verus-examples:doubly_linked` (pointer-heavy translation not source-faithful yet)
- `verus-examples:external` (`Ghost<int>` erased to plain `int`; `println!` in `external_body` fn not translated)
- `verus-examples:integers` (`nat`/cast semantics not source-faithful yet)
- `verus-examples:modules` (`closed` visibility not preserved: other modules cannot see the function's body)

## Gaps

### `opaque` / `reveal` not supported
- Functions marked `#[verifier::opaque]` have their bodies **fully visible** in Core.
  `reveal(f)` calls are silently dropped. A downstream verifier can prove facts that
  Verus would reject because the body should be hidden until explicitly revealed.
- Affects: `verus-examples:generics` (`g` is opaque but body is emitted; `reveal(g)` dropped)

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

### `Fuel` / `RevealString` / `Air` statements erased
- `Fuel` (controlling recursive function unrolling), `RevealString` (string-keyed
  reveal), and `Air` (backend-specific directives) statements are all parsed as
  empty blocks. Related to but distinct from the opaque/reveal gap above.
- Affects: `verus-examples:generics` (fuel), `verus-examples:guide/strings`
  (RevealString)

### Missing Strata Core/Boole types and primitives
- No native `.Nat` type.
- No cast/coercion primitives or semantics for `bv*_to_int_{u,s}`.
- Missing model types: `Tuple`, `Cell`, `Atomic`, `Set`, `arrow`, `Unit`, etc.
- Missing stdlib/pervasive symbols used by Verus exports: `Seq_*`, `Map_*`, `Pervasive_*`, etc.
