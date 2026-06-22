# Handoff: model `u128`/`i128` as native `bv128` in Boole (remove the int workarounds)

## The task / decision
The Boole developer has confirmed Boole/Strata **supports 128-bit bitvectors**. So
the translator should model `u128`/`i128` as a **normal `bv128`** with **normal bv
operations** — NOT widen to `int`. Remove the int-modeling workarounds that exist
only because `bv128` used to be rejected (`bvTy: unsupported width 128`).

This affects the **EXEC** path for `u128`/`i128` (wrapping, fixed-width). It does
**NOT** change the faithful-arithmetic rule: **spec-mode** `+ - * / %` stays
mathematical `int`/`nat` (committed `c03d79e`, the `parentIntNatClip` rule). The
spec vs exec split is decided by the arith op's **result type** in VLIR — int/nat
result = mathematical (unchanged); `uN` result = bv (this is what flips u128 from
int to bv128). So: **exec `u128` → native `bv128`; spec `u128` → `int` (unchanged).**

## The core change (one list, then a cascade)
`VerusLean/VLIR/Boole/Coercions.lean:20`
```lean
def supportedBvWidths : List Nat := [1, 8, 16, 32, 64]   -- add 128
```
Adding `128` makes `isSupportedBvWidth 128 = true`, which cascades through everything
that gates on it: `bitWidthOfTyp`/`bitInfoOfTyp` (Coercions.lean:25,31),
`numKindOfTyp?` (Coercions.lean:90 — `.UInt 128` now → `.bv 128 false` instead of
`.int`), and all the inference sites in `Inference.lean:326,367–381,432–504`.
Once `numKindOfTyp? u128 = bv`, the int workarounds below simply stop firing for
u128 — but several panic or assume `1|8|16|32|64`, so they must be extended too.

## Bv builders that hard-code `1|8|16|32|64` — extend to 128
`VerusLean/VLIR/Boole/Builder.lean`
- `:44` `bvTy` — `panic! "bvTy: unsupported bitvector width {w} (expected 1|8|16|32|64)"`. Add the 128 case.
- `:101` `bitvecConstNat` — same panic; add 128.
- `:82` `cast_to_bv128` **already exists** — partial support is there.
- Check the bv op constructors (shl/shr/add/mul/and/or/cast) emit a valid 128-bit
  form in the Strata Boole dialect (the dev says they're supported — verify the
  exact constructor names / that `bv{128}` literals parse).

## The int workarounds that should become dead / be cleaned
These exist ONLY for int-modeled `u128`. After the flip they should not fire for
u128; confirm they're dead for u128 (and decide whether to delete or leave inert):
- **Rule ④ shift-via-pow2**: `intShiftViaPow2` (`Translate.lean:~798`),
  `shiftValueIntModeled?` (`Translate.lean:~649`), the `int_pow2` prelude function
  (`prelude/Nat.boole.st`). `x >> k` / `x << k` on u128 should now be native
  `bvShr`/`bvShl`, not `x div int_pow2(k)` / `x * int_pow2(k)`.
- **Narrowing gate**: `clipWrapIntModeled` + `fixedWidthInfoOfTyp`
  (`Translate.lean:~631`, `Coercions.lean:~42`). `(x: u128) as u64` should be a
  native bv truncation/cast, not `x mod 2^64`.
- **ArithFootprint `hasMathInt`** for unsupported-width ints
  (`Inference.lean:480,495–504`) — the `u128 → hasMathInt` contributions were to
  detect int/bv mixes; with u128 native bv they're unnecessary for u128.
- The exec-overflow `HasType` range-predicate handling stays (that's general), but
  for u128 the overflow is now native bv wrapping + the range obligation.

## Primary validation target
**Benchmark B1 — `FieldElement51::mul`** is the u128 stress test: it has `u128`
intermediate products and variable-amount shifts. Current state (gaps doc): "u128
intermediate products → Modelled as `int`". Regenerate and verify:
- `tests/VerusFiles/b1_minimal.rs`, `b1_boundary_proved.rs`, `b1_full.rs`
- Expect the emitted Boole to use `bv128` ops (not `int_pow2`/`mod 2^k`/int arith)
  for the exec u128 path, and the nonlinear `mul` obligations to be pure-bv.
- `b1_full` currently fails at Lean `#strata` elaboration (stack overflow on the
  ~1300-line program) — independent of this change; don't be alarmed.

## Build / test workflow (verus-boogie)
- `source ../tools/activate` once; build with `lake build` (NOT cargo). ~443 jobs.
- After building, ALWAYS run the gate: `bash tests/check_working_tests.sh`
  (baseline: **46 passed / 2 skipped (Strata gap) / 1 failed (`crypto_noref`)**;
  exit-1 is expected because crypto_noref fails). `SKIP_STRATA_VERIFY=1` for
  generation-only. The gate's Strata verify runs `lake env lean` in
  `../Strata/StrataBoole` — if you see `incompatible header`, rebuild Strata
  (`cd ../Strata/StrataBoole && lake build`) and avoid concurrent builds.
- Regenerate one test: `./tests/run_tests.sh --boole <file.rs>` (or `--all` to
  include verify). Emitted output: `tests/BoolePrograms/vlir-tests/<name>.lean`.
- Strata dep is the local `../Strata/StrataBoole` (pr/casts-boole) per
  `lake-manifest.json`.

## Files
- `VerusLean/VLIR/Boole/Coercions.lean` — `supportedBvWidths`, the width gates, `numKindOfTyp?`.
- `VerusLean/VLIR/Boole/Builder.lean` — `bvTy`, `bitvecConstNat`, bv op/cast constructors.
- `VerusLean/VLIR/Boole/Inference.lean` — `arithFootprint`, the bit-info inference.
- `VerusLean/VLIR/Boole/Translate.lean` — `intShiftViaPow2`, `clipWrapIntModeled`, `shiftValueIntModeled?`, the arith lowering.
- `prelude/Nat.boole.st` — `int_pow2` (may become unused for u128).

## Risks / gotchas
- Don't regress the **spec** path: spec-mode `u128` arith must still emit `int`/`nat`
  (faithful, never-wraps) via the result-type rule. Only the `uN`-result (exec) path
  flips to bv128. Add/keep a test that exercises both.
- `usize`/`isize` map to `usizeBitWidth` (64) — unaffected.
- Watch for places that assumed "u128 ⇒ int" as a shortcut (grep the codebase for
  `128`, `u128`, `unsupported width`). The gaps doc `docs/dalek-benchmark-gaps.md`
  fixed-bugs table documents every int-modeling rule that was added for u128.
- The change is mostly *removing* special-casing; the cleanest first step is
  `supportedBvWidths += 128` + the two builder panics, then regenerate B1 and read
  the diff to see which workarounds are now dead.
