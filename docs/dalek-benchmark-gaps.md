# Dalek benchmarks B1–B5 — translation bugs & StrataBoole gaps

Status of the five dalek-lite benchmark targets (see `Strata/docs/BooleBenchmarks.md`)
through the Verus → VLIR → verus-lean → Boole → Strata pipeline, as of 2026-06-09.

Target files: `tests/VerusFiles/{B1_mul_minimal, B1_mul_boundary_proved,
B1_mul, B2_from_bytes_minimal, B3_decompress_minimal,
B4_compress_minimal, B5_mul_clamped_minimal}.rs` — all verify under our Verus fork
with 0 errors. `B1_mul` is fully proved (zero admits — its whole
lemma closure is vendored from dalek-lite); the other targets keep
heavy/curve lemmas admitted as `/// TRUSTED AXIOM` stubs, per file headers.

## Pipeline status at a glance

| B | Target | Verus | Boole export | Strata type-check | Verify |
|---|--------|-------|--------------|-------------------|--------|
| 1 | `B1_mul_minimal` (2 admits) | ✅ | ✅ | ✅ | cvc5 157/282 (125 ⌛); cslib Lean backend 61/70 (9 nonlinear open) |
| 1 | `B1_mul_boundary_proved` (1 admit) | ✅ 22/0 | ✅ | ✅ (after u128/shift inference fixes) | ⌛ nonlinear (no obligation closes in 220s) |
| 1 | `B1_mul` (fully proved, 0 admits) | ✅ 36/0 | ✅ 114 KB (variable-amount shifts via `int_pow2`; narrowing-gate `mod`s; exec overflow VCs as range asserts) | ❌ Lean stack overflow elaborating the ~1400-line program (see open gaps) | not attempted (same nonlinear wall expected) |
| 2 | `B2_from_bytes_minimal` (typesyn) | ✅ | ✅ | ✅ | gen_smt_vcs + `grind\|omega\|smt` closes all VCs; `Boole.verify` 330/366 (2 benign ⌛) |
| 3 | `B3_decompress_minimal` | ✅ 17/0 | ✅ | ❌ tuple selectors + struct field access | — |
| 4 | `B4_compress_minimal` | ✅ 31/0 | ✅ | ❌ `choose`-defined spec fn body | — |
| 5 | `B5_mul_clamped_minimal` | ✅ 16/0 | ✅ | ❌ trait associated type | — |

## Translator (verus-lean) bugs found and fixed

All fixed in `VerusLean/VLIR/Boole/{Translate,Inference}.lean`; full suite held
at the 40 ✅ / 5 ❌ baseline after each fix.

| Bug | Surfaced by | Fix |
|-----|-------------|-----|
| u128 emitted as `bv128` → Strata `bvTy: unsupported width 128` panic | B1 | Rule ①: `numKindOfTyp?` total — unsupported-width ints classify (and emit) as `int` |
| Numeric casts (widen/narrow/as-int) handled by scattered patches | B1 | Rule ③: one unified `Clip` rule |
| Int-modeled `x >> k` / `x << k` has no bv form | B1 | Rule ④: lower to `x div 2^k` / `x * 2^k` (constant `k`, value operand int-modeled) |
| Shift-amount width mismatch (`bv64 << bv32` rejected by Strata) | B1 | Pin amount width from the value operand's type |
| Rule ④ gate missed nested/literal shifts (`(x<<51)>>51`, `1u128<<108`) | B1 boundary | `shiftValueIntModeled?` — recurses through arith/bitwise binaries, reads literal types; kept separate from the coercion path |
| u128 *variable* not classified int ⇒ `u128 + bv64` mix undetected ⇒ bv64 const left uncoerced in int context | B1 boundary | `inferNumKind` routes through `numKindOfTyp?` |
| u128-typed / ≥2⁶⁴-valued literals contributed nothing to the arith footprint | B1 boundary | `arithFootprint` `.Const`: unsupported-width type or value ≥ 2⁶⁴ → `hasMathInt` |
| Bitwise binaries opaque to the arith footprint (un-lowered `u128 << k` hid the mix) | B1 boundary | `arithFootprint` recurses into `.Binary (.Bitwise …)` like `.Arith` |
| Single-field array struct lowered to opaque datatype + global `∀ length == N` axiom — **unsound** (asserts every `Sequence T` has length N) | B1/B2 | Wrapper-datatype trick: transparent `type <dt> := Sequence T` + identity ctor with `requires length == N` + identity destructor |
| `nat % nat` previously routed via precondition-free `nat.fromIntAux` — underspecified `mod 0` | B1 | `nat.mod` mirrors `nat.div` (guarded nonzero-divisor definition in `prelude/Nat.boole.st`); EuclideanMod fires on nat operand types |
| Comparison result inherited operand bv width ⇒ `(u == 1u8) == choice_is_true(c)` mis-coerced bool to int | B3 | `inferBitInfo`: `.Eq`/`.Ne`/`.Inequality` → `none` (a comparison is `bool`) |
| nat-arith results (`nat.mod` etc.) returned uncoerced ⇒ `(n % 2) as u8` and `n % 2 == 0` type-error | B3, B4 | Coerce the nat-domain result to the caller's expected kind (`nat.toInt` wrap) |
| Bare polymorphic `Sequence.empty` unparseable for type-variable element types | crypto_noref | `Bld.seqEmpty` fallback: emit `Sequence.empty<T>()` via Core `seq_empty` |
| Variable-amount shift on int-modeled u128 (`x >> shift` with `shift` a parameter, vstd `lemma_u128_shr_is_div`) → `bvTy: unsupported width 128` PANIC in `bvUShr`; recovered emission left `x >> shift` on `int` operands — invalid Boole | B1_mul | Rule ④ variable-amount arm: `x >> e` → `x div int_pow2(e)`, `x << e` → `x * int_pow2(e)` (`intShiftViaPow2`); `int_pow2` + guarded axioms live in `prelude/Nat.boole.st` |
| Arith op reaching the bv-inference path with no inferred width lowers in the int domain but translated operands with `expected = none` ⇒ nat-returning call fed bare to int `div` (`x div pow2(…)` with `x : u128`) | B1_mul | Operands of a no-bv-width arith op translate at `Int`, so nat leaves coerce via `nat.toInt` |
| Comparison between two arith trees got no numeric-kind signal (`inferComparableTyp?` has no `.Binary` case) ⇒ sides picked domains independently: `nat.mod(...) == (...) mod nat.toInt(p)` — nat vs int under `==` | B1_mul (`lemma_u64_5_as_nat_product` ensures); repro: `tests/VerusFiles/repros/eq_clip_nat_mod_repro.rs` | `inferComparisonNumKind` joins an arith tree's operand kinds (nat⊔nat = nat, int involvement = int, bv defers to bit-info), so `comparisonPrelude` reconciles both sides to int |
| Rule ③ elided *narrowing* casts in int-modeled contexts — `(x : u128) as u64` emitted as bare `x` — collapsing vstd `lemma_cast_then_mod_51`'s ensures to the tautology `x mod c == x mod c`; same class silently mis-read `u64→u32` and `u64→i64` casts under int contexts | B1_mul faithfulness review; probe: `tests/VerusFiles/repros/clip_gate_probe.rs` | Narrowing gate (`clipWrapIntModeled` + `fixedWidthInfoOfTyp`/`fitsFixedWidth`): a Clip to fixed width `w` in the int domain emits `mod 2^w` (signed targets: centered `(x + 2^(w-1)) mod 2^w − 2^(w-1)`) unless the inner's source type syntactically fits the target; widening stays elided; bv-context cast paths unchanged (native `as_bv<w>` already truncates) |
| Exec overflow VCs dropped: Verus materializes them as `assert HasType(τ, e)` ("possible arithmetic underflow/overflow", 31 in B1_mul's exec body), and the Assert/Assume arms blanket-dropped every `HasType` expression — Boole-verified exec code carried no overflow obligations (bv ops wrap silently) | B1_mul faithfulness review (soundness item S1) | `hasTypeRangeCond`: numeric `HasType(τ, e)` lowers to the range predicate `lo_τ ≤ e ≤ hi_τ` over the int model, for asserts (the overflow obligation) and assumes (the checked-range fact, also emitted by Verus for call results — partially restoring rule ①'s dropped range invariants); non-numeric `HasType` stays dropped as a typing tautology |
| `assert X; assume X` pairs from Verus's SST had the assume dropped as an "echo" (`isAssertAssumeEcho`) — but Strata's `assert` defers the obligation *without* extending path conditions (`Imperative/CmdEval`), so the echo assume is what carries the checked fact to later obligations | B1_mul faithfulness audit (assert-fact persistence) | Echo suppression removed; Verus's Hoare-style pairs translate whole |

## Open translator gaps (current B1/B3/B4/B5 blockers)

These are feature gaps, not coercion bugs — each needs a designed encoding.

| B | First error | Root cause |
|---|-------------|------------|
| 1 | `lake env lean` on `B1_mul.lean` (wrapper minus the `#eval`): `Stack overflow detected. Aborting.` — survives `ulimit -s 65520` | The fully-proved program is ~1300 lines with the giant `lemma_mul_value` / `lemma_u64_5_as_nat_product` assert terms (hundred-node nested sums); Lean's `#strata` elaboration recurses past the OS stack. Emission itself is fine (the same translator output type-checks for `B1_mul_boundary_proved`). Needs elaborator-side relief: chunked elaboration, iterative AST walk in StrataDDM, or splitting the program. |
| 1 | Definition-level obligations unprovable: `p_body_calls_nat.sub` (needs `19 ≤ pow2(255)`), `field_canonical_body_calls_nat.mod` (needs `toInt(p) ≠ 0`), `l51_bit_mask_lt` first ensures (needs the `low_bits_mask(51)` value), and `Sequence.select` in-bounds preconditions in `u64_5_as_nat`/`u64_5_bounded` (no length fact on the wrapper-sequence param) — 9 failing obligations in the trimmed B1 prefix | Two causes: `pow2`/`low_bits_mask` are uninterpreted with values living only in *lemma ensures* (unreachable from function-definition obligations), and the wrapper-datatype length invariant is ctor-enforced but never assumed at use sites. **Fix prototyped and validated** in `tests/BoolePrograms/scratch/defn_obligations_experiment.lean`: (a) ground value axioms per literal exponent (`axiom [pow2_255_val]: toInt(pow2(255)) == 2^255`, likewise `low_bits_mask(51)`) — mechanically emittable by scanning the crate's literal exponents; (b) `requires Sequence.length(x) == 5` on the wrapper-sequence spec-fn chain, which cascades cleanly. Result: 234 ✅ / 9 🚨 → **246 ✅ / 0 🚨**. Translator emission of both is the follow-up. |
| 3 | `B3_decompress_minimal.lean:213` `Unknown variable Tuple_4_2` | Translator references flat N-tuple selectors (`Tuple_4_0..3`) but the type is the nested-pair `Tuple choice (Tuple fe51 (Tuple fe51 fe51))`; no flat selectors exist for N>2. Needs nested-pair projection chains (`Tuple.._0/_1` composition) or declared N-tuple selectors. |
| 3 | `B3_decompress_minimal.lean:213` `Unknown variable compressedEdwardsY..compressedEdwardsY_CompressedEdwardsY_0` | Struct field access on a non-array-wrapper struct (gap #13). The wrapper-datatype trick covers only the single-field fixed-array shape; tuple-struct field 0 of `CompressedEdwardsY([u8;32])` isn't emitted. |
| 4 | `B4_compress_minimal.lean:238` `Unknown expr identifier b` | `u8_32_from_nat` (nat → 32-byte inverse) is `choose`-defined in the source; the `choose` binder is erased (`[TRANS-choose]`, same class as `trigger_loops`), leaving a free `b`. Needs a choose/epsilon encoding or an axiomatized uninterpreted function. |
| 5 | `B5_mul_clamped_minimal.lean:87` `Undeclared type or category Ops_Arith_mul_Output` | Trait associated type `<&MontgomeryPoint as Mul<&Scalar>>::Output` from the `MulSpecImpl` machinery is referenced generically but never resolved/declared. Needs associated-type resolution to the concrete impl type (here `MontgomeryPoint`). |

Maps to `BooleBenchmarks.md` gaps: #13 (struct fields, B3/B4), #14 (`Option` —
modeled through the tuple return, B3), #15 (byte arrays, B2/B5), pair returns +
field-op axioms (B4), Montgomery ladder axioms (B5). Gaps #10 (abstract `nat`)
and #11 (recursive spec fns) are handled by the nat model + admitted axioms.

## Strata / StrataBoole bugs found (upstream handoffs)

| Issue | Where | Status |
|-------|-------|--------|
| Polymorphic `mod` leaks the as-int cast's type var (`modt_expr` fvar) — surfaces at `Verify.lean` bvWidth | `BooleDDM` mod type inference | Written up in `…/project/strata-boole-mod-fvar-issue.md` for the Boole developer |
| Generic tuple selector `Tuple.._1(kv)` elaborates at `T1` where `T0` expected (`crypto_noref.lean`: `fun kv : (Tuple bv8 bv8) => Tuple.._0(kv) ^ Tuple.._1(kv)`) — fails the working-suite `crypto_noref` type-check | StrataDDM/StrataBoole generic-selector type instantiation | Reproduces with an unmodified translator (verified by stash-rebuild-regen), so the regression is dependency-side, not verus-lean; surfaced 2026-06-09 alongside the Strata rebuild |
| `gen_smt_vcs` drops the bitvector width in `ubv_to_int`/`sbv_to_int` (`BitVec.toNat` applied without the width) | `Strata/DL/SMT/Translate.lean` | Fixed in cslib's vendored Strata copy (recover width via `getBitVecWidth`); dev repo + upstream still unfixed — PR-worthy |
| `gen_smt_vcs` crashes on opaque `datatype` wrappers (`withTypeDecls` declares the sort, `translateSort` can't find it) | `Strata/DL/SMT/Translate.lean` | Known; deferred to Strata devs. Forces the synonym encoding, which in turn makes cvc5 unfold recursive spec fns and time out — the two backends pull on opposite encodings |
| `String.IsSuffix` defined in the global `String` namespace collides with Mathlib (`Mathlib.Data.String.Defs`) — blocks importing `nlinarith` alongside Strata | `Strata/DL/Util/StringGen.lean` | Found; rename is PR-worthy (used only inside `StringGen.lean`) |
| `gen_smt_vcs` is slow on large programs (~8 min on B2): `nativeDecide` over the whole VC set as one giant literal, recompiled every elaboration | `MetaVerifier.lean` | Documented; mitigations: `#exit` while editing, shrink program terms |

## Verification-level wall (B1 family)

With translation clean, B1's bottleneck is **nonlinear integer arithmetic**
(25 limb products, carry-chain bounds), not pow2 modeling (uninterpreted
`pow2` + imported value/monotonicity lemmas is correct and not the limiter):

- cvc5 (`Boole.verify`): 157/282 on the sound synonym encoding; the 125
  timeouts are transparent-synonym unfolding + nonlinear grinding.
- cslib Lean backend (`gen_smt_vcs; grind|omega|smt`): 61/70; the 9 open VCs
  are products-of-bounded-limbs goals (`nlinarith`-shaped; blocked from trying
  `nlinarith` by the `String.IsSuffix` clash above).
- Levers, in rough order: make the heavy spec fns opaque for cvc5; fix the
  `gen_smt_vcs` datatype crash (enables the cvc5-friendly opaque encoding in
  both backends); prove the 9 residuals with nonlinear tactics once Mathlib
  can be imported.
