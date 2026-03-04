# Differential Status

This file tracks two things separately:
- raw regression outcomes from `regress_examples.sh`
- manual faithfulness judgments for reviewed cases

Solver success is **not** used to classify faithfulness.

## Data Sources
- Full run:
  - command: `./tests/regress_examples.sh --all-suites`
  - run id: `20260303_182610`
  - solver: `cvc5`

## Raw Regression Summary (Full Run)
Total cases: **112**

Primary statuses (sum to 112):
- expected empty exports: 1
- translate failures: 0
- strata parse failures: 0
- strata type failures: 80
- verify failures: 13
- verify success: 17
- expected mismatches: 1

Additional counters (do not affect total):
- export failures: 0
- mismatch (Verus pass, Strata fail): 8
- mismatch (Verus fail, Strata pass): 0

## Fidelity Labels
- `passing`: behavior aligns with expectation and translation is faithful.
- `faithful but different from Verus output`: translation is faithful, but Verus/Strata outcomes differ or Strata lacks support.
- `not faithful translation`: translation currently drops/changes important semantics compared to source-level intent.

## passing (21)
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
- `verus-examples:guide/datatypes`
- `verus-examples:guide/equality`
- `verus-examples:guide/getting_started`
- `verus-examples:guide/nonlinear_bitvec`
- `verus-examples:guide/opaque` (expected empty export)
- `verus-examples:guide/references`
- `verus-examples:guide/requires_ensures`
- `verus-examples:guide/requires_ensures_edit`

## faithful but different from Verus output (10)
- `vlir-tests:FindMax` (cvc5 default gives one VC unknown)
- `vlir-tests:LoopSimple` (expected mismatch bucket)
- `vlir-tests:demo_while` (same as FindMax)
- `vlir-tests:demo_while_loop_isolation` (same as FindMax)
- `verus-examples:bitvector_basic` (remaining VC failures are cast semantics/modeling)
- `verus-examples:external` (blocked by cast function semantics/modeling)
- `verus-examples:fun_ext` (blocked by higher-order/extensional support)
- `verus-examples:generics` (blocked by Strata/Cslib type/model gaps)
- `verus-examples:guide/modes` (blocked by missing `Tuple`/`Tuple_ctor_2` support)
- `verus-examples:statements` (mixed-width integer comparison lowered via `bv*_to_int_u`)

## not faithful translation (5)
- `vlir-tests:matching` (`nat` lowered as `int`, losing non-negativity semantics)
- `verus-examples:datatypes` (decrease/recursion artifacts are not source-close enough yet)
- `verus-examples:doubly_linked` (pointer-heavy translation not source-faithful yet)
- `verus-examples:integers` (`nat`/cast semantics not source-faithful yet)
- `verus-examples:modules` (`closed` visibility/body-hiding behavior not preserved yet)

## Coverage
Reviewed fidelity labels cover **36 / 112** cases.
- passing: 21
- faithful but different from Verus output: 10
- not faithful translation: 5

Unreviewed or not yet labeled: **76 / 112** (mostly `strata-type-failed`).
