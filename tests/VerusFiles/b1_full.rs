// =============================================================================
// Benchmark B1 — `FieldElement51::mul`  (VARIANT: fully proved, zero admits)
// =============================================================================
//
// FULL variant of b1_minimal.rs: every lemma in the transitive closure
// of the `mul` correctness proof carries its real proof body — no `admit()`
// or `assume(false)` anywhere in this file.  Companion files:
//   b1_minimal.rs         — lemma_mul_boundary + lemma_mul_value admitted
//   b1_boundary_proved.rs — only lemma_mul_value admitted
//   b1_full.rs                 — (this file) everything proved
//
// Field multiplication in GF(p), p = 2^255 - 19, the prime field underlying
// Curve25519/Ed25519.  A `FieldElement51` is an integer in radix 2^51, stored
// as five u64 limbs (limbs[i] < 2^54 between reductions).  `mul` computes the
// schoolbook product of two such elements, folding the 2^255 overflow back in
// with the constant 19 (since 2^255 ≡ 19 mod p), and carry-propagates the 25
// u64×u64 → u128 partial products down to five 52-bit limbs.
//
// This is THE arithmetic foundation of the whole library: every higher-level
// curve operation (point addition, doubling, scalar multiplication, field
// inversion) bottoms out in repeated calls to `mul`.
//
// Postconditions:
//   (1) Correctness   — fe51_as_canonical_nat(&output)
//                          == field_mul(fe51_as_canonical_nat(self),
//                                       fe51_as_canonical_nat(_rhs))
//                       The output's canonical value mod p equals the product
//                       of the inputs' canonical values mod p.
//
//   (2) Boundedness   — fe51_limbs_bounded(&output, 52)  (and, weaker, 54)
//                       Every output limb is < 2^52, so the result can be fed
//                       straight back into another `mul`/`add`/`sub` without a
//                       separate reduction step — this is what makes the limb
//                       representation composable.
//
// Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
// Pinned commit: 3f3443e
//
// Assembled from:
//   curve25519-dalek/src/backend/serial/u64/field.rs        (target `mul`, `m`, mask)
//   curve25519-dalek/src/specs/field_specs.rs               (fe51_* / field_mul specs)
//   curve25519-dalek/src/specs/field_specs_u64.rs           (p, u64_5_as_nat, pow255_gt_19, l51_bit_mask_lt)
//   curve25519-dalek/src/lemmas/field_lemmas/mul_lemmas.rs  (mul_return, lemma_mul_boundary, lemma_mul_value)
//   curve25519-dalek/src/lemmas/common_lemmas/mul_lemmas.rs (lemma_mul_lt, lemma_m, distributive/reorder lemmas) [§7a, §7b]
//   curve25519-dalek/src/lemmas/common_lemmas/div_mod_lemmas.rs (lemma_mod_sum_factor, lemma_mod_diff_factor)   [§7b]
//   curve25519-dalek/src/lemmas/field_lemmas/pow2_51_lemmas.rs  (shift/mask/cast lemmas)                        [§7a, §7b]
//   curve25519-dalek/src/lemmas/field_lemmas/u64_5_as_nat_lemmas.rs (lemma_u64_5_as_nat_product)                [§7b]
//
// Local deviations from upstream (statements identical, bodies re-proved):
//   - `lemma_masked_lt_51` / `lemma_shr_51_le`: upstream routes through
//     vstd::bits lemmas absent from this vstd (`lemma_u64_masked_lt`,
//     `lemma_div_is_ordered` chain); re-proved directly `by (bit_vector)`
//     over the concrete mask51 constant and the fixed 51-bit shift.
//   - `lemma_u64_div_and_mod_51`: upstream instantiates the generic
//     `lemma_div_and_mod!` macro at u64 and specializes to k = 51; the
//     specialization is inlined here (same proof steps, k fixed to 51).
//
// Verification targets: the full proof chain
//   lemma_mul_boundary (§7a) → exec carry chain (no overflow) →
//   lemma_mul_value (§7c, via §7b support) → lemma_mul_mod_noop_general
// discharging both postconditions of `mul` with no trusted gaps.
// =============================================================================

#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;   // lemma_mul_mod_noop_general, lemma_fundamental_div_mod, mod-noop lemmas
use vstd::arithmetic::mul::*;       // lemma_mul_is_* family, lemma_mul_upper_bound
use vstd::arithmetic::power2::*;    // pow2, lemma2_to64, lemma2_to64_rest, lemma_pow2_adds
use vstd::bits::*;                  // low_bits_mask, lemma_u64_shr_is_div, lemma_u128_shr_is_div, lemma_u64_low_bits_mask_is_mod
use vstd::prelude::*;

verus! {

// ============================================================
// § 1  Limb-evaluation spec  (specs/field_specs_u64.rs)
// ============================================================

// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
#[verusfmt::skip]
pub open spec fn u64_5_as_nat(limbs: [u64; 5]) -> nat {
                (limbs[0] as nat) +
    pow2( 51) * (limbs[1] as nat) +
    pow2(102) * (limbs[2] as nat) +
    pow2(153) * (limbs[3] as nat) +
    pow2(204) * (limbs[4] as nat)
}

// ============================================================
// § 2  Field specs mod p  (specs/field_specs_u64.rs, field_specs.rs)
// ============================================================

/// p = 2^255 - 19
pub open spec fn p() -> nat {
    (pow2(255) - 19) as nat
}

pub open spec fn field_canonical(n: nat) -> nat {
    n % p()
}

pub open spec fn u64_5_as_field_canonical(limbs: [u64; 5]) -> nat {
    field_canonical(u64_5_as_nat(limbs))
}

/// Spec predicate: all limbs are bounded by a given bit limit
pub open spec fn u64_5_bounded(limbs: [u64; 5], bit_limit: u64) -> bool {
    forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] < (1u64 << bit_limit)
}

/// Spec predicate: all limbs are bounded by a given bit limit
pub open spec fn fe51_limbs_bounded(fe: &FieldElement51, bit_limit: u64) -> bool {
    u64_5_bounded(fe.limbs, bit_limit)
}

/// Returns the canonical mathematical value of a field element in [0, p)
pub open spec fn fe51_as_canonical_nat(fe: &FieldElement51) -> nat {
    u64_5_as_field_canonical(fe.limbs)
}

/// Math-level field multiplication
pub open spec fn field_mul(a: nat, b: nat) -> nat {
    field_canonical(a * b)
}

// ============================================================
// § 3  Type  (backend/serial/u64/field.rs)
// ============================================================

/// An element of the field ℤ / p
#[derive(Copy, Clone)]
pub struct FieldElement51 {
    pub limbs: [u64; 5],
}

// ============================================================
// § 4  Constants & the 64×64 → 128 helper  (backend/serial/u64/field.rs, specs/field_specs_u64.rs)
// ============================================================

/// 2^51 - 1, the low-51-bit mask (exec side), originally u64 = (1u64 << 51) -1
pub const LOW_51_BIT_MASK: u64 = 2251799813685247u64;

/// 2^51 - 1, the low-51-bit mask (spec side), equal in value to LOW_51_BIT_MASK).
pub open spec const mask51: u64 = 2251799813685247u64;

/// Multiply two u64s into a u128
#[inline(always)]
fn m(x: u64, y: u64) -> (r: u128)
    ensures
        (r as nat) == (x as nat) * (y as nat),
        r <= u128::MAX,
{
    proof {
        // x ≤ u64::MAX ∧ y ≤ u64::MAX ⇒ x·y ≤ u64::MAX² ≤ u128::MAX, so no overflow.
        lemma_mul_upper_bound(x as int, u64::MAX as int, y as int, u64::MAX as int);
        assert((u64::MAX as int) * (u64::MAX as int) <= u128::MAX as int) by (compute);
    }
    (x as u128) * (y as u128)
}

// ============================================================
// § 5  Coefficient & output specs  (lemmas/field_lemmas/mul_lemmas.rs)
//
//      These mirror, term-for-term, the exec carry chain in `mul`.  They are
//      needed to state the boundary/value lemmas below and to phrase the
//      `out =~= mul_return(a, b)` step inside the target proof.
// ============================================================

// Initial coefficient values before carry propagation.
// These match the exec code in mul:
//   c0 = m(a[0],b[0]) + m(a[4],b1_19) + m(a[3],b2_19) + m(a[2],b3_19) + m(a[1],b4_19)
// where bN_19 = b[N] * 19

// Initial 128-bit coefficients (before carry propagation).  bN_19 = b[N]*19,
// so a[i]*(19*b[j]) is the schoolbook term folded by 2^255 ≡ 19 (mod p).
pub open spec fn mul_c0_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[0] * b[0] + a[4] * (19 * b[1]) + a[3] * (19 * b[2]) + a[2] * (19 * b[3]) + a[1] * (19
        * b[4])) as u128
}

pub open spec fn mul_c1_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[1] * b[0] + a[0] * b[1] + a[4] * (19 * b[2]) + a[3] * (19 * b[3]) + a[2] * (19
        * b[4])) as u128
}

pub open spec fn mul_c2_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[2] * b[0] + a[1] * b[1] + a[0] * b[2] + a[4] * (19 * b[3]) + a[3] * (19 * b[4])) as u128
}

pub open spec fn mul_c3_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[3] * b[0] + a[2] * b[1] + a[1] * b[2] + a[0] * b[3] + a[4] * (19 * b[4])) as u128
}

pub open spec fn mul_c4_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[4] * b[0] + a[3] * b[1] + a[2] * b[2] + a[1] * b[3] + a[0] * b[4]) as u128
}

// Accumulated coefficients after the carry chain c1 += c0>>51, c2 += c1>>51, …
pub open spec fn mul_c0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    mul_c0_0_val(a, b)
}

pub open spec fn mul_c1_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (mul_c1_0_val(a, b) + ((mul_c0_val(a, b) >> 51) as u64) as u128) as u128
}

pub open spec fn mul_c2_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (mul_c2_0_val(a, b) + ((mul_c1_val(a, b) >> 51) as u64) as u128) as u128
}

pub open spec fn mul_c3_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (mul_c3_0_val(a, b) + ((mul_c2_val(a, b) >> 51) as u64) as u128) as u128
}

pub open spec fn mul_c4_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (mul_c4_0_val(a, b) + ((mul_c3_val(a, b) >> 51) as u64) as u128) as u128
}

/// The final 5-limb output, mirroring the exec carry chain in `mul`.
pub open spec fn mul_return(a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
    let c0 = mul_c0_val(a, b);
    let c1 = mul_c1_val(a, b);
    let c2 = mul_c2_val(a, b);
    let c3 = mul_c3_val(a, b);
    let c4 = mul_c4_val(a, b);
    let out0: u64 = (c0 as u64) & mask51;
    let out1: u64 = (c1 as u64) & mask51;
    let out2: u64 = (c2 as u64) & mask51;
    let out3: u64 = (c3 as u64) & mask51;
    let out4: u64 = (c4 as u64) & mask51;
    let carry: u64 = (c4 >> 51) as u64;
    let out0: u64 = (out0 + carry * 19) as u64;
    let out1: u64 = (out1 + (out0 >> 51)) as u64;
    let out0: u64 = out0 & mask51;
    [out0, out1, out2, out3, out4]
}

// ============================================================
// § 6  Boundary spec  (lemmas/field_lemmas/mul_lemmas.rs)
//
//      `mul_boundary_spec` packages every no-overflow / limb-bound fact the
//      exec body of `mul` needs.  It is the postcondition of
//      `lemma_mul_boundary`.
// ============================================================

pub open spec fn mul_term_product_bounds_spec(a: [u64; 5], b: [u64; 5], bound: u64) -> bool {
    // All plain products a[i]*b[j] < bound*bound
    &&& forall|i: int, j: int|
        0 <= i < 5 && 0 <= j < 5 ==> (a[i] as u128) * (b[j] as u128) < bound * bound
    // All scaled products a[i]*(19*b[j]) < 19*bound*bound
    &&& forall|i: int, j: int|
        0 <= i < 5 && 0 <= j < 5 ==> (a[i] as u128) * ((19 * b[j]) as u128) < 19 * (bound * bound)
}

pub open spec fn mul_ci_0_val_boundaries(a: [u64; 5], b: [u64; 5], bound: u64) -> bool {
    &&& mul_c0_0_val(a, b) < 77 * (bound * bound)
    &&& mul_c1_0_val(a, b) < 59 * (bound * bound)
    &&& mul_c2_0_val(a, b) < 41 * (bound * bound)
    &&& mul_c3_0_val(a, b) < 23 * (bound * bound)
    &&& mul_c4_0_val(a, b) < 5 * (bound * bound)
}

pub open spec fn mul_ci_val_boundaries(a: [u64; 5], b: [u64; 5]) -> bool {
    &&& (mul_c0_val(a, b) >> 51) <= (u64::MAX as u128)
    &&& (mul_c1_val(a, b) >> 51) <= (u64::MAX as u128)
    &&& (mul_c2_val(a, b) >> 51) <= (u64::MAX as u128)
    &&& (mul_c3_val(a, b) >> 51) <= (u64::MAX as u128)
    &&& (mul_c4_val(a, b) >> 51) <= (u64::MAX as u128)
}

pub open spec fn mul_out_val_boundaries(a: [u64; 5], b: [u64; 5]) -> bool {
    let c0 = mul_c0_val(a, b);
    let c1 = mul_c1_val(a, b);
    let c2 = mul_c2_val(a, b);
    let c3 = mul_c3_val(a, b);
    let c4 = mul_c4_val(a, b);
    let out0: u64 = (c0 as u64) & mask51;
    let out1: u64 = (c1 as u64) & mask51;
    let carry: u64 = (c4 >> 51) as u64;
    let out0_1: u64 = (out0 + carry * 19) as u64;
    &&& out0 < 1u64 << 51
    &&& out1 < 1u64 << 51
    &&& ((c2 as u64) & mask51) < 1u64 << 51
    &&& ((c3 as u64) & mask51) < 1u64 << 51
    &&& ((c4 as u64) & mask51) < 1u64 << 51
    &&& carry < 724618875532318195u64
    &&& out0 + carry * 19 < u64::MAX
    &&& out1 + (out0_1 >> 51) < 1u64 << 52
    &&& (out0_1 & mask51) < 1u64 << 51
}

pub open spec fn mul_boundary_spec(a: [u64; 5], b: [u64; 5]) -> bool {
    &&& 19 * (1u64 << 54) <= u64::MAX
    &&& 77 * ((1u64 << 54) * (1u64 << 54)) <= u128::MAX
    &&& mul_term_product_bounds_spec(a, b, 1u64 << 54)
    &&& mul_ci_0_val_boundaries(a, b, 1u64 << 54)
    &&& mul_ci_val_boundaries(a, b)
    &&& mul_out_val_boundaries(a, b)
    &&& mul_return(a, b)[0] < 1u64 << 52
    &&& mul_return(a, b)[1] < 1u64 << 52
    &&& mul_return(a, b)[2] < 1u64 << 52
    &&& mul_return(a, b)[3] < 1u64 << 52
    &&& mul_return(a, b)[4] < 1u64 << 52
    &&& (1u64 << 52) < (1u64 << 54)
}

// ============================================================
// § 7  Lemmas  (specs/field_specs_u64.rs, lemmas/field_lemmas/mul_lemmas.rs)
// ============================================================

/// Proof that 2^255 > 19
pub proof fn pow255_gt_19()
    ensures
        pow2(255) > 19,
{
    lemma2_to64();  // 2^5 = 32
    lemma_pow2_strictly_increases(5, 255);
}

// ------------------------------------------------------------
// § 7a  Boundary-proof support lemmas (vendored from dalek-lite)
//
//   The transitive closure of `lemma_mul_boundary`'s proof.  `lemma_mul_lt`,
//   `lemma_m`, and the three `mul_*_bounded` lemmas are verbatim from
//   dalek-lite (lemmas/{common_lemmas,field_lemmas}/mul_lemmas.rs).
//
//   `lemma_masked_lt_51` and `lemma_shr_51_le` upstream route through the
//   vstd::bits lemmas `lemma_u64_masked_lt` / `lemma_div_is_ordered`, which
//   THIS Verus's vstd does not provide.  Their statements are kept identical
//   but the bodies are re-proved directly with `by (bit_vector)` over the
//   concrete `mask51` constant and the fixed 51-bit shift — so every caller
//   in the closure is unaffected.
// ------------------------------------------------------------

/// Strict product monotonicity for nats:  a1<b1 ∧ a2<b2 ⇒ a1·a2 < b1·b2.
pub proof fn lemma_mul_lt(a1: nat, b1: nat, a2: nat, b2: nat)
    requires
        a1 < b1,
        a2 < b2,
    ensures
        a1 * a2 < b1 * b2,
{
    if a2 == 0 {
        assert(b1 * b2 > 0) by {
            lemma_mul_nonzero(b1 as int, b2 as int);
        }
    } else {
        lemma_mul_strict_inequality(a1 as int, b1 as int, a2 as int);
        lemma_mul_strict_inequality(a2 as int, b2 as int, b1 as int);
    }
}

/// `m(x,y)` is bounded by the product of the individual bounds.
/// (Param `b_y` is upstream `by`, renamed to avoid the `by` token.)
pub proof fn lemma_m(x: u64, y: u64, bx: u64, b_y: u64)
    requires
        x < bx,
        y < b_y,
    ensures
        (x as u128) * (y as u128) < (bx as u128) * (b_y as u128),
{
    lemma_mul_lt(x as nat, bx as nat, y as nat, b_y as nat);
}

/// All plain products a[i]·b[j] and scaled products a[i]·(19·b[j]) are bounded.
pub proof fn lemma_mul_term_product_bounds(a: [u64; 5], b: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        forall|i: int| 0 <= i < 5 ==> a[i] < bound,
        forall|i: int| 0 <= i < 5 ==> b[i] < bound,
    ensures
        mul_term_product_bounds_spec(a, b, bound),
{
    let bound19 = (19 * bound) as u64;
    assert(bound * (19 * bound) == 19 * (bound * bound)) by {
        lemma_mul_is_associative(19, bound as int, bound as int);
    }
    assert forall|i: int, j: int| 0 <= i < 5 && 0 <= j < 5 implies (a[i] as u128) * (b[j] as u128)
        < bound * bound && (a[i] as u128) * ((19 * b[j]) as u128) < 19 * (bound * bound) by {
        lemma_m(a[i], b[j], bound, bound);
        lemma_m(a[i], (19 * b[j]) as u64, bound, bound19);
    }
}

/// Initial coefficients c_i_0 are bounded by {77,59,41,23,5}·bound².
pub proof fn lemma_mul_c_i_0_bounded(a: [u64; 5], b: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        forall|i: int| 0 <= i < 5 ==> a[i] < bound,
        forall|i: int| 0 <= i < 5 ==> b[i] < bound,
    ensures
        mul_ci_0_val_boundaries(a, b, bound),
{
    lemma_mul_term_product_bounds(a, b, bound);
}

/// Each carry (c_i >> 51) fits in a u64.
pub proof fn lemma_mul_c_i_shift_bounded(a: [u64; 5], b: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        77 * (bound * bound) + u64::MAX <= ((u64::MAX as u128) << 51),
        mul_ci_0_val_boundaries(a, b, bound),
    ensures
        mul_ci_val_boundaries(a, b),
{
    lemma_shr_51_fits_u64(mul_c0_val(a, b));
    lemma_shr_51_fits_u64(mul_c1_val(a, b));
    lemma_shr_51_fits_u64(mul_c2_val(a, b));
    lemma_shr_51_fits_u64(mul_c3_val(a, b));
    lemma_shr_51_fits_u64(mul_c4_val(a, b));
}

/// `>>51` is monotone on u128.  (Re-proved via bit_vector; dalek-lite routes
/// through `lemma_u128_shr_is_div` + `lemma_div_is_ordered`.)
pub proof fn lemma_shr_51_le(a: u128, b: u128)
    requires
        a <= b,
    ensures
        (a >> 51) <= (b >> 51),
{
    assert((a >> 51) <= (b >> 51)) by (bit_vector)
        requires a <= b;
}

/// If a ≤ u64::MAX·2^51 then a>>51 fits in a u64.
pub proof fn lemma_shr_51_fits_u64(a: u128)
    requires
        a <= (u64::MAX as u128) << 51,
    ensures
        (a >> 51) <= (u64::MAX as u128),
{
    assert(((u64::MAX as u128) << 51) >> 51 == (u64::MAX as u128)) by (compute);
    lemma_shr_51_le(a, (u64::MAX as u128) << 51);
}

/// Masking with mask51 (= 2^51 − 1) yields a value < 2^51.  (Re-proved via
/// bit_vector; dalek-lite routes through the missing `lemma_u64_masked_lt`.)
pub proof fn lemma_masked_lt_51(v: u64)
    ensures
        v & mask51 < (1u64 << 51),
{
    assert(v & 2251799813685247u64 < (1u64 << 51)) by (bit_vector);
}

/// PROVEN (full body, vendored from lemmas/field_lemmas/mul_lemmas.rs).
/// Establishes every no-overflow / limb-bound fact the exec carry chain needs.
pub proof fn lemma_mul_boundary(a: [u64; 5], b: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> a[i] < 1u64 << 54,
        forall|i: int| 0 <= i < 5 ==> b[i] < 1u64 << 54,
    ensures
        mul_boundary_spec(a, b),
{
    let bound = 1u64 << 54;
    let bound19 = (19 * bound) as u64;
    let bound_sq = 1u128 << 108;

    assert(bound * bound == bound_sq) by {
        assert(((1u64 << 54) as u128) * ((1u64 << 54) as u128) == (1u128 << 108)) by (bit_vector);
    }

    assert(bound * bound19 == 19 * bound_sq) by {
        assert((1u64 << 54) * ((19 * (1u64 << 54)) as u64) == 19 * (1u128 << 108)) by (bit_vector);
    }

    assert(19 * bound <= u64::MAX) by {
        assert(19 * (1u64 << 54) <= u64::MAX) by (compute);
    }

    assert(mul_term_product_bounds_spec(a, b, bound)) by {
        lemma_mul_term_product_bounds(a, b, bound);
    }

    assert(mul_ci_0_val_boundaries(a, b, bound)) by {
        lemma_mul_c_i_0_bounded(a, b, bound);
    }

    assert(77 * bound_sq + u64::MAX <= ((u64::MAX as u128) << 51)) by {
        assert(77 * (1u128 << 108) + u64::MAX <= ((u64::MAX as u128) << 51)) by (compute);
    }

    assert(mul_ci_val_boundaries(a, b)) by {
        lemma_mul_c_i_shift_bounded(a, b, bound);
    }

    assert(mul_out_val_boundaries(a, b)) by {
        let c0 = mul_c0_val(a, b);
        let c1 = mul_c1_val(a, b);
        let c2 = mul_c2_val(a, b);
        let c3 = mul_c3_val(a, b);
        let c4 = mul_c4_val(a, b);
        let out0: u64 = (c0 as u64) & mask51;
        let out1: u64 = (c1 as u64) & mask51;
        let carry: u64 = (c4 >> 51) as u64;
        let out0_1: u64 = (out0 + carry * 19) as u64;

        assert(out0 < 1u64 << 51 && out1 < 1u64 << 51 && ((c2 as u64) & mask51) < 1u64 << 51 && ((
        c3 as u64) & mask51) < 1u64 << 51 && ((c4 as u64) & mask51) < 1u64 << 51) by {
            lemma_masked_lt_51(c0 as u64);
            lemma_masked_lt_51(c1 as u64);
            lemma_masked_lt_51(c2 as u64);
            lemma_masked_lt_51(c3 as u64);
            lemma_masked_lt_51(c4 as u64);
        }

        let pow2_5933 = 724618875532318195u64;
        assert(carry < pow2_5933) by {
            assert(c4 >> 51 <= (5 * bound_sq + (u64::MAX as u128)) as u128 >> 51) by {
                lemma_shr_51_le(c4, (5 * bound_sq + (u64::MAX as u128)) as u128);
            }
            assert((5 * (1u128 << 108) + (u64::MAX as u128)) as u128 >> 51 < (
            724618875532318195u64 as u128)) by (compute);
        }

        assert(out0 + carry * 19 < u64::MAX) by {
            assert((1u64 << 51) + 19 * 724618875532318195u64 <= u64::MAX) by (compute);
        }

        assert(out1 + (out0_1 >> 51) < 1u64 << 52) by {
            assert(out0_1 as u128 >> 51 <= u64::MAX as u128 >> 51) by {
                lemma_shr_51_le(out0_1 as u128, u64::MAX as u128);
            }
            assert(((u64::MAX as u128) >> 51) < (1u64 << 13)) by (compute);
            assert((1u64 << 51) + (1u64 << 13) < (1u64 << 52)) by (compute);
        }

        assert((out0_1 & mask51) < 1u64 << 51) by {
            lemma_masked_lt_51(out0_1 as u64);
        }
    }

    assert((1u64 << 51) < (1u64 << 52) < (1u64 << 54)) by (bit_vector);
}

// ------------------------------------------------------------
// § 7b  Value-proof support lemmas (vendored from dalek-lite)
//
//   The transitive closure of `lemma_mul_value`'s proof, with full bodies:
//     lemma_mul_distributive_{3,4,5}_terms, lemma_mul_quad_prod,
//     lemma_mul_w0_and_reorder, lemma_mul_si_vi_and_reorder
//                                  — common_lemmas/mul_lemmas.rs
//     lemma_mod_sum_factor, lemma_mod_diff_factor
//                                  — common_lemmas/div_mod_lemmas.rs
//     l51_bit_mask_lt              — specs/field_specs_u64.rs
//     lemma_cast_then_mod_51, lemma_mul_sub, lemma_u64_div_and_mod_51
//                                  — field_lemmas/pow2_51_lemmas.rs
//     lemma_u64_5_as_nat_product   — field_lemmas/u64_5_as_nat_lemmas.rs
//
//   `lemma_u64_div_and_mod_51` upstream calls the `lemma_div_and_mod!` macro
//   instantiation `lemma_u64_div_and_mod` at k = 51; that specialization is
//   inlined here (same proof steps over the vstd::bits div/mod lemmas).
// ------------------------------------------------------------

pub proof fn lemma_mul_distributive_3_terms(n: int, x1: int, x2: int, x3: int)
    ensures
        n * (x1 + x2 + x3) == (x1 + x2 + x3) * n == n * x1 + n * x2 + n * x3,
{
    assert(n * (x1 + x2 + x3) == (x1 + x2 + x3) * n) by {
        lemma_mul_is_commutative(n, x1 + x2 + x3);
    }

    assert(n * (x1 + x2 + x3) == n * (x1 + x2) + n * x3) by {
        lemma_mul_is_distributive_add(n, x1 + x2, x3);
    }

    assert(n * (x1 + x2) == n * x1 + n * x2) by {
        lemma_mul_is_distributive_add(n, x1, x2);
    }
}

pub proof fn lemma_mul_distributive_4_terms(n: int, x1: int, x2: int, x3: int, x4: int)
    ensures
        n * (x1 + x2 + x3 + x4) == (x1 + x2 + x3 + x4) * n == n * x1 + n * x2 + n * x3 + n * x4,
{
    assert(n * (x1 + x2 + x3 + x4) == (x1 + x2 + x3 + x4) * n) by {
        lemma_mul_is_commutative(n, x1 + x2 + x3 + x4);
    }

    assert(n * (x1 + x2 + x3 + x4) == n * (x1 + x2 + x3) + n * x4) by {
        lemma_mul_is_distributive_add(n, x1 + x2 + x3, x4);
    }

    assert(n * (x1 + x2 + x3) == n * x1 + n * x2 + n * x3) by {
        lemma_mul_distributive_3_terms(n, x1, x2, x3);
    }
}

pub proof fn lemma_mul_distributive_5_terms(n: int, x1: int, x2: int, x3: int, x4: int, x5: int)
    ensures
        n * (x1 + x2 + x3 + x4 + x5) == (x1 + x2 + x3 + x4 + x5) * n == n * x1 + n * x2 + n * x3 + n
            * x4 + n * x5,
{
    assert(n * (x1 + x2 + x3 + x4 + x5) == (x1 + x2 + x3 + x4 + x5) * n) by {
        lemma_mul_is_commutative(n, x1 + x2 + x3 + x4 + x5);
    }

    assert(n * (x1 + x2 + x3 + x4 + x5) == n * (x1 + x2 + x3 + x4) + n * x5) by {
        lemma_mul_is_distributive_add(n, x1 + x2 + x3 + x4, x5);
    }

    assert(n * (x1 + x2 + x3 + x4) == n * x1 + n * x2 + n * x3 + n * x4) by {
        lemma_mul_distributive_4_terms(n, x1, x2, x3, x4);
    }
}

/// Product-of-pairs reassociation: (a1·b1)·(a2·b2) == (a1·a2)·(b1·b2).
pub proof fn lemma_mul_quad_prod(a1: int, b1: int, a2: int, b2: int)
    ensures
        (a1 * b1) * (a2 * b2) == (a1 * a2) * (b1 * b2),
{
    // commutativity is baked-in
    // (a1 * b1) * (a2 * b2) =  ((a1 * b1) * a2) * b2
    lemma_mul_is_associative(a1 * b1, a2, b2);
    // (a1 * b1) * a2 = a2 * (a1 * b1) = (a2 * a1) * b1
    lemma_mul_is_associative(a2, a1, b1);
    // ((a2 * a1) * b1) * b2 = (a2 * a1) * (b1 * b2)
    lemma_mul_is_associative(a2 * a1, b1, b2);
}

/// Row expansion for the radix-2^51 product: scalar row w0 times the 5-limb
/// value of b, reordered into power-grouped form.
pub proof fn lemma_mul_w0_and_reorder(
    w0: int,
    v0: int,
    s1: int,
    v1: int,
    s2: int,
    v2: int,
    s3: int,
    v3: int,
    s4: int,
    v4: int,
)
    ensures
        w0 * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4) == s4 * (w0 * v4) + s3 * (w0 * v3) + s2
            * (w0 * v2) + s1 * (w0 * v1) + (w0 * v0),
{
    lemma_mul_distributive_5_terms(w0, v0, s1 * v1, s2 * v2, s3 * v3, s4 * v4);

    lemma_mul_is_associative(w0, v1, s1);
    lemma_mul_is_associative(w0, v2, s2);
    lemma_mul_is_associative(w0, v3, s3);
    lemma_mul_is_associative(w0, v4, s4);
}

/// Row expansion for the radix-2^51 product: scaled row (si·vi) times the
/// 5-limb value of b, reordered into power-grouped form.
pub proof fn lemma_mul_si_vi_and_reorder(
    si: int,
    vi: int,
    v0: int,
    s1: int,
    v1: int,
    s2: int,
    v2: int,
    s3: int,
    v3: int,
    s4: int,
    v4: int,
)
    ensures
        (si * vi) * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4) == (si) * (vi * v0) + (si * s1) * (
        vi * v1) + (si * s2) * (vi * v2) + (si * s3) * (vi * v3) + (si * s4) * (vi * v4),
{
    lemma_mul_distributive_5_terms(si * vi, v0, s1 * v1, s2 * v2, s3 * v3, s4 * v4);

    assert((si * vi) * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4) == (si * vi) * v0 + (si * vi)
        * (s1 * v1) + (si * vi) * (s2 * v2) + (si * vi) * (s3 * v3) + (si * vi) * (s4 * v4));

    lemma_mul_is_associative(si, vi, v0);
    lemma_mul_quad_prod(si, vi, s1, v1);
    lemma_mul_quad_prod(si, vi, s2, v2);
    lemma_mul_quad_prod(si, vi, s3, v3);
    lemma_mul_quad_prod(si, vi, s4, v4);
}

/// (a·m + b) % m == b % m.
pub proof fn lemma_mod_sum_factor(a: int, b: int, m: int)
    requires
        m > 0,
    ensures
        (a * m + b) % m == b % m,
{
    // (a * m + b) % m == ((a * m) % m + b % m) % m
    lemma_add_mod_noop(a * m, b, m);
    // (a * m) % m == 0
    lemma_mod_multiples_basic(a, m);
    // b % m % m = b % m
    lemma_mod_twice(b, m);
}

/// (b − a·m) % m == b % m.
pub proof fn lemma_mod_diff_factor(a: int, b: int, m: int)
    requires
        m > 0,
    ensures
        (b - a * m) % m == b % m,
{
    // (b - a * m) % m == (b % m - (a * m) % m) % m
    lemma_sub_mod_noop(b, a * m, m);
    // (a * m) % m == 0
    lemma_mod_multiples_basic(a, m);
    // b % m % m = b % m
    lemma_mod_twice(b, m);
}

/// mask51 equals vstd's low_bits_mask(51) and is below 2^51.
pub proof fn l51_bit_mask_lt()
    ensures
        mask51 == low_bits_mask(51),
        mask51 < (1u64 << 51) as nat,
{
    lemma2_to64_rest();  // pow2(51) value, so low_bits_mask(51) = pow2(51) - 1 computes
    assert(mask51 < (1u64 << 51) as nat) by (compute);
}

/// Shift/mask decomposition at 51 bits: v>>51 and v&mask51 are exactly the
/// div/mod of v by 2^51.  (Inlined specialization of upstream's generic
/// `lemma_u64_div_and_mod` macro instantiation at k = 51.)
pub proof fn lemma_u64_div_and_mod_51(ai: u64, bi: u64, v: u64)
    requires
        ai == v >> 51,
        bi == v & mask51,
    ensures
        ai == v / (pow2(51) as u64),
        bi == v % (pow2(51) as u64),
        v == ai * pow2(51) + bi,
{
    l51_bit_mask_lt();  // mask51 == low_bits_mask(51)

    assert(0 < pow2(51) <= u64::MAX) by {
        lemma_pow2_pos(51);
        lemma2_to64_rest();  // pow2(51) == 0x8000000000000
    }

    assert(ai == v / (pow2(51) as u64)) by {
        lemma_u64_shr_is_div(v, 51);
    }

    // v & low_bits_mask(51) = v % pow2(51)
    assert(bi == v % (pow2(51) as u64)) by {
        lemma_u64_low_bits_mask_is_mod(v, 51);
    }

    assert(v == pow2(51) * (v as nat / pow2(51)) + v as nat % pow2(51)) by {
        lemma_fundamental_div_mod(v as int, pow2(51) as int);
    }

    lemma_mul_is_commutative(ai as int, pow2(51) as int);
}

/// Truncating a u128 to u64 commutes with mod 2^51.
/// (x as u64) = x % 2^64, so x = 2^64·(x/2^64) + (x as u64); since
/// 2^51 | 2^64·(…), both sides agree mod 2^51.
pub proof fn lemma_cast_then_mod_51(x: u128)
    ensures
        (x as u64) % (pow2(51) as u64) == x % (pow2(51) as u128),
{
    lemma2_to64_rest();  // pow2(51 | 64)
    assert((x as u64) % 0x8000000000000 == x % 0x8000000000000) by (bit_vector);
}

/// 2^k·(ci − 2^51·(cj − cj_0)) == 2^k·ci − 2^(k+51)·cj + 2^(k+51)·cj_0.
pub proof fn lemma_mul_sub(ci: int, cj: int, cj_0: int, k: nat)
    ensures
        pow2(k) * (ci - pow2(51) * (cj - cj_0)) == pow2(k) * ci - pow2(k + 51) * cj + pow2(k + 51)
            * cj_0,
{
    // 2^k (ci - X) = 2^k ci - 2^k X
    lemma_mul_is_distributive_sub(pow2(k) as int, ci, pow2(51) * (cj - cj_0));
    // 2^k (2^51 * Y) = (2^k * 2^51) * Y
    lemma_mul_is_associative(pow2(k) as int, pow2(51) as int, cj - cj_0);
    // 2^k * 2^51 = 2^(k + 51)
    lemma_pow2_adds(k, 51);
    // 2^(k + 51) * (cj - cj_0) = 2^(k + 51) * cj - 2^(k + 51) * cj_0
    lemma_mul_is_distributive_sub(pow2(k + 51) as int, cj, cj_0);
}

/// PROVEN (full body, vendored from lemmas/field_lemmas/u64_5_as_nat_lemmas.rs).
/// The schoolbook expansion of the 5-limb product, and its reduction mod p
/// using pow2(5·51) = p + 19.
#[verusfmt::skip]
pub proof fn lemma_u64_5_as_nat_product(a: [u64; 5], b: [u64; 5])
    ensures
        // Full polynomial expansion
        u64_5_as_nat(a) * u64_5_as_nat(b) ==
            pow2(8 * 51) * (a[4] * b[4]) +
            pow2(7 * 51) * (a[3] * b[4] + a[4] * b[3]) +
            pow2(6 * 51) * (a[2] * b[4] + a[3] * b[3] + a[4] * b[2]) +
            pow2(5 * 51) * (a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1]) +
            pow2(4 * 51) * (a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0]) +
            pow2(3 * 51) * (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0]) +
            pow2(2 * 51) * (a[0] * b[2] + a[1] * b[1] + a[2] * b[0]) +
            pow2(1 * 51) * (a[0] * b[1] + a[1] * b[0]) +
                           (a[0] * b[0]),
        // Mod-p reduction (using pow2(5*51) = p + 19)
        (u64_5_as_nat(a) * u64_5_as_nat(b)) % p() ==
            (
                pow2(4 * 51) * (a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0]) +
                pow2(3 * 51) * (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0] + 19 * (a[4] * b[4])) +
                pow2(2 * 51) * (a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + 19 * (a[3] * b[4] + a[4] * b[3])) +
                pow2(1 * 51) * (a[0] * b[1] + a[1] * b[0] + 19 * (a[2] * b[4] + a[3] * b[3] + a[4] * b[2])) +
                               (a[0] * b[0] + 19 * (a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1]))
            ) as nat % p(),
{
    let a0 = a[0]; let a1 = a[1]; let a2 = a[2]; let a3 = a[3]; let a4 = a[4];
    let b0 = b[0]; let b1 = b[1]; let b2 = b[2]; let b3 = b[3]; let b4 = b[4];

    let s1 = pow2(1 * 51);
    let s2 = pow2(2 * 51);
    let s3 = pow2(3 * 51);
    let s4 = pow2(4 * 51);
    let s5 = pow2(5 * 51);
    let s6 = pow2(6 * 51);
    let s7 = pow2(7 * 51);
    let s8 = pow2(8 * 51);

    assert(s1 * s1 == s2) by { lemma_pow2_adds(51, 51) }
    assert(s1 * s2 == s2 * s1 == s3) by { lemma_pow2_adds(51, 102) }
    assert(s1 * s3 == s3 * s1 == s4) by { lemma_pow2_adds(51, 153) }
    assert(s1 * s4 == s4 * s1 == s5) by { lemma_pow2_adds(51, 204) }
    assert(s2 * s2 == s4) by { lemma_pow2_adds(102, 102) }
    assert(s2 * s3 == s3 * s2 == s5) by { lemma_pow2_adds(102, 153) }
    assert(s2 * s4 == s4 * s2 == s6) by { lemma_pow2_adds(102, 204) }
    assert(s3 * s3 == s6) by { lemma_pow2_adds(153, 153) }
    assert(s3 * s4 == s4 * s3 == s7) by { lemma_pow2_adds(153, 204) }
    assert(s4 * s4 == s8) by { lemma_pow2_adds(204, 204) }

    // Step 1: Distribute u64_5_as_nat(a) * u64_5_as_nat(b) into 5 rows
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == a0 * u64_5_as_nat(b) + (s1 * a1)
        * u64_5_as_nat(b) + (s2 * a2) * u64_5_as_nat(b) + (s3 * a3) * u64_5_as_nat(b) + (s4
        * a4) * u64_5_as_nat(b)) by {
        lemma_mul_distributive_5_terms(
            u64_5_as_nat(b) as int,
            a0 as int,
            s1 * a1,
            s2 * a2,
            s3 * a3,
            s4 * a4,
        );
    }

    // Step 2: Expand each row
    assert(a0 * u64_5_as_nat(b) == s4 * (a0 * b4) + s3 * (a0 * b3) + s2 * (a0 * b2) + s1 * (a0
        * b1) + a0 * b0) by {
        lemma_mul_w0_and_reorder(
            a0 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s1 * a1) * u64_5_as_nat(b) == s5 * (a1 * b4) + s4 * (a1 * b3) + s3 * (a1 * b2) + s2
        * (a1 * b1) + s1 * (a1 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s1 as int,
            a1 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s2 * a2) * u64_5_as_nat(b) == s6 * (a2 * b4) + s5 * (a2 * b3) + s4 * (a2 * b2) + s3
        * (a2 * b1) + s2 * (a2 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s2 as int,
            a2 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s3 * a3) * u64_5_as_nat(b) == s7 * (a3 * b4) + s6 * (a3 * b3) + s5 * (a3 * b2) + s4
        * (a3 * b1) + s3 * (a3 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s3 as int,
            a3 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s4 * a4) * u64_5_as_nat(b) == s8 * (a4 * b4) + s7 * (a4 * b3) + s6 * (a4 * b2) + s5
        * (a4 * b1) + s4 * (a4 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s4 as int,
            a4 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    // Step 3: Group by power
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == s8 * (a4 * b4) + s7 * (a3 * b4 + a4 * b3) + s6
        * (a2 * b4 + a3 * b3 + a4 * b2) + s5 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) + s4
        * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) + s3 * (a0 * b3 + a1 * b2 + a2 * b1
        + a3 * b0) + s2 * (a0 * b2 + a1 * b1 + a2 * b0) + s1 * (a0 * b1 + a1 * b0) + (a0 * b0))
        by {
        // s1 terms
        assert(s1 * (a0 * b1) + s1 * (a1 * b0) == s1 * (a0 * b1 + a1 * b0)) by {
            lemma_mul_is_distributive_add(s1 as int, a0 * b1, a1 * b0);
        }
        // s2 terms
        assert(s2 * (a0 * b2) + s2 * (a1 * b1) + s2 * (a2 * b0) == s2 * (a0 * b2 + a1 * b1 + a2
            * b0)) by {
            lemma_mul_distributive_3_terms(s2 as int, a0 * b2, a1 * b1, a2 * b0);
        }
        // s3 terms
        assert(s3 * (a0 * b3) + s3 * (a1 * b2) + s3 * (a2 * b1) + s3 * (a3 * b0) == s3 * (a0
            * b3 + a1 * b2 + a2 * b1 + a3 * b0)) by {
            lemma_mul_distributive_4_terms(s3 as int, a0 * b3, a1 * b2, a2 * b1, a3 * b0);
        }
        // s4 terms
        assert(s4 * (a0 * b4) + s4 * (a1 * b3) + s4 * (a2 * b2) + s4 * (a3 * b1) + s4 * (a4
            * b0) == s4 * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0)) by {
            lemma_mul_distributive_5_terms(s4 as int, a0 * b4, a1 * b3, a2 * b2, a3 * b1, a4 * b0);
        }
        // s5 terms
        assert(s5 * (a1 * b4) + s5 * (a2 * b3) + s5 * (a3 * b2) + s5 * (a4 * b1) == s5 * (a1
            * b4 + a2 * b3 + a3 * b2 + a4 * b1)) by {
            lemma_mul_distributive_4_terms(s5 as int, a1 * b4, a2 * b3, a3 * b2, a4 * b1);
        }
        // s6 terms
        assert(s6 * (a2 * b4) + s6 * (a3 * b3) + s6 * (a4 * b2) == s6 * (a2 * b4 + a3 * b3 + a4
            * b2)) by {
            lemma_mul_distributive_3_terms(s6 as int, a2 * b4, a3 * b3, a4 * b2);
        }
        // s7 terms
        assert(s7 * (a3 * b4) + s7 * (a4 * b3) == s7 * (a3 * b4 + a4 * b3)) by {
            lemma_mul_is_distributive_add(s7 as int, a3 * b4, a4 * b3);
        }
    }

    // Step 4: Factor out s5 = p + 19 for high-order terms
    pow255_gt_19();
    assert(s5 == (p() + 19));

    let c0_x19 = a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1];
    let c1_x19 = a[2] * b[4] + a[3] * b[3] + a[4] * b[2];
    let c2_x19 = a[3] * b[4] + a[4] * b[3];
    let c3_x19 = a[4] * b[4];

    let c0_base = a[0] * b[0];
    let c1_base = a[0] * b[1] + a[1] * b[0];
    let c2_base = a[0] * b[2] + a[1] * b[1] + a[2] * b[0];
    let c3_base = a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0];
    let c4 = a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0];

    let c0 = c0_base + 19 * c0_x19;
    let c1 = c1_base + 19 * c1_x19;
    let c2 = c2_base + 19 * c2_x19;
    let c3 = c3_base + 19 * c3_x19;

    // Group in preparation for the s5 = p+19 substitution
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == s4 * c4 + s3 * (s5 * c3_x19 + c3_base) + s2
        * (s5 * c2_x19 + c2_base) + s1 * (s5 * c1_x19 + c1_base) + (s5 * c0_x19 + c0_base)) by {
        assert(s8 * c3_x19 + s3 * c3_base == s3 * (s5 * c3_x19 + c3_base)) by {
            assert(s8 == (s3 * s5)) by {
                lemma_pow2_adds(3 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s3 as int, s5 as int, c3_x19);
            lemma_mul_is_distributive_add(s3 as int, s5 * c3_x19, c3_base);
        }

        assert(s7 * c2_x19 + s2 * c2_base == s2 * (s5 * c2_x19 + c2_base)) by {
            assert(s7 == (s2 * s5)) by {
                lemma_pow2_adds(2 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s2 as int, s5 as int, c2_x19);
            lemma_mul_is_distributive_add(s2 as int, s5 * c2_x19, c2_base);
        }

        assert(s6 * c1_x19 + s1 * c1_base == s1 * (s5 * c1_x19 + c1_base)) by {
            assert(s6 == (s1 * s5)) by {
                lemma_pow2_adds(1 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s1 as int, s5 as int, c1_x19);
            lemma_mul_is_distributive_add(s1 as int, s5 * c1_x19, c1_base);
        }
    }

    // Step 5: Substitute s5 = p + 19
    assert(s5 * c3_x19 + c3_base == p() * c3_x19 + c3) by {
        lemma_mul_is_distributive_add(c3_x19 as int, p() as int, 19);
    }

    assert(s5 * c2_x19 + c2_base == p() * c2_x19 + c2) by {
        lemma_mul_is_distributive_add(c2_x19 as int, p() as int, 19);
    }

    assert(s5 * c1_x19 + c1_base == p() * c1_x19 + c1) by {
        lemma_mul_is_distributive_add(c1_x19 as int, p() as int, 19);
    }

    assert(s5 * c0_x19 + c0_base == p() * c0_x19 + c0) by {
        lemma_mul_is_distributive_add(c0_x19 as int, p() as int, 19);
    }

    // Regroup: X * p() + Y
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == p() * (s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19
        + c0_x19) + (s4 * c4 + s3 * c3 + s2 * c2 + s1 * c1 + c0)) by {
        lemma_mul_is_distributive_add(s3 as int, p() * c3_x19, c3 as int);
        lemma_mul_is_distributive_add(s2 as int, p() * c2_x19, c2 as int);
        lemma_mul_is_distributive_add(s1 as int, p() * c1_x19, c1 as int);

        assert(s3 * (p() * c3_x19) + s2 * (p() * c2_x19) + s1 * (p() * c1_x19) + p() * c0_x19
            == p() * (s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19 + c0_x19)) by {
            lemma_mul_is_associative(s3 as int, c3_x19 as int, p() as int);
            lemma_mul_is_associative(s2 as int, c2_x19 as int, p() as int);
            lemma_mul_is_associative(s1 as int, c1_x19 as int, p() as int);

            lemma_mul_is_distributive_add(p() as int, s3 * c3_x19, s2 * c2_x19);
            lemma_mul_is_distributive_add(p() as int, s3 * c3_x19 + s2 * c2_x19, s1 * c1_x19);
            lemma_mul_is_distributive_add(
                p() as int,
                s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19,
                c0_x19 as int,
            );
        }
    }

    // Step 6: Take mod p
    let k = (s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19 + c0_x19);
    let sum = (s4 * c4 + s3 * c3 + s2 * c2 + s1 * c1 + c0);

    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == k * p() + sum);
    assert(k * p() + sum == (k as nat) * p() + (sum as nat));

    assert((u64_5_as_nat(a) * u64_5_as_nat(b)) % p() == ((k as nat) * p() + (sum as nat)) % p());
    assert(((k as nat) * p() + (sum as nat)) % p() == (sum as nat) % p()) by {
        lemma_mod_sum_factor(k as int, sum as int, p() as int);
    }
}

// ------------------------------------------------------------
// § 7c  Value lemma  (lemmas/field_lemmas/mul_lemmas.rs)
// ------------------------------------------------------------

/// PROVEN (full body, vendored from lemmas/field_lemmas/mul_lemmas.rs).
/// The mathematical heart: the carry-chain output reduces (mod p) to the
/// schoolbook product of the inputs — a telescoping div/mod argument plus
/// lemma_u64_5_as_nat_product.
pub proof fn lemma_mul_value(a: [u64; 5], b: [u64; 5])
    requires
        mul_boundary_spec(a, b),
    ensures
        u64_5_as_nat(mul_return(a, b)) % p() == (u64_5_as_nat(a) * u64_5_as_nat(b)) % p(),
{
    lemma2_to64_rest();
    assert(p() > 0) by {
        pow255_gt_19();
    }

    assert(mask51 == low_bits_mask(51)) by {
        l51_bit_mask_lt();
    }

    let out_hat = mul_return(a, b);

    let c0_0 = mul_c0_0_val(a, b);
    let c1_0 = mul_c1_0_val(a, b);
    let c2_0 = mul_c2_0_val(a, b);
    let c3_0 = mul_c3_0_val(a, b);
    let c4_0 = mul_c4_0_val(a, b);
    let c1 = mul_c1_val(a, b);
    let c2 = mul_c2_val(a, b);
    let c3 = mul_c3_val(a, b);
    let c4 = mul_c4_val(a, b);
    let carry: u64 = (c4 >> 51) as u64;
    let out0_0: u64 = (c0_0 as u64) & mask51;
    let out1_0: u64 = (c1 as u64) & mask51;
    let out2: u64 = (c2 as u64) & mask51;
    let out3: u64 = (c3 as u64) & mask51;
    let out4: u64 = (c4 as u64) & mask51;
    let out0_1: u64 = (out0_0 + carry * 19) as u64;
    let out1_1: u64 = (out1_0 + (out0_1 >> 51)) as u64;
    let out0_2: u64 = out0_1 & mask51;

    assert(u64_5_as_nat(out_hat) == out0_1 + pow2(51) * out1_0 + pow2(102) * out2 + pow2(153) * out3
        + pow2(204) * out4) by {
        assert(out0_2 + pow2(51) * out1_1 == out0_1 + pow2(51) * out1_0) by {
            assert(out0_2 == out0_1 % (pow2(51) as u64)) by {
                lemma_u64_low_bits_mask_is_mod(out0_1, 51);
            }
            assert(out0_1 >> 51 == out0_1 / (pow2(51) as u64)) by {
                lemma_u64_shr_is_div(out0_1, 51);
            }
            lemma_u64_div_and_mod_51((out0_1 >> 51), out0_2, out0_1);
        }
    }

    assert(u64_5_as_nat(out_hat) == ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry + pow2(51) * ((
    c1 as u64) % (pow2(51) as u64)) + pow2(102) * ((c2 as u64) % (pow2(51) as u64)) + pow2(153) * ((
    c3 as u64) % (pow2(51) as u64)) + pow2(204) * ((c4 as u64) % (pow2(51) as u64))) by {
        l51_bit_mask_lt();

        assert((pow2(51) as u64) == (pow2(51) as u128));

        assert(out0_1 == ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry) by {
            lemma_u64_low_bits_mask_is_mod(c0_0 as u64, 51);
        }

        assert(out1_0 == (c1 as u64) % (pow2(51) as u64)) by {
            lemma_u64_low_bits_mask_is_mod(c1 as u64, 51);
        }

        assert(out2 == (c2 as u64) % (pow2(51) as u64)) by {
            lemma_u64_low_bits_mask_is_mod(c2 as u64, 51);
        }

        assert(out3 == (c3 as u64) % (pow2(51) as u64)) by {
            lemma_u64_low_bits_mask_is_mod(c3 as u64, 51);
        }

        assert(out4 == (c4 as u64) % (pow2(51) as u64)) by {
            lemma_u64_low_bits_mask_is_mod(c4 as u64, 51);
        }
    }

    assert(u64_5_as_nat(out_hat) == (c0_0 % (pow2(51) as u128)) + 19 * carry + pow2(51) * (c1 % (
    pow2(51) as u128)) + pow2(102) * (c2 % (pow2(51) as u128)) + pow2(153) * (c3 % (pow2(
        51,
    ) as u128)) + pow2(204) * (c4 % (pow2(51) as u128))) by {
        lemma_cast_then_mod_51(c0_0);
        lemma_cast_then_mod_51(c1);
        lemma_cast_then_mod_51(c2);
        lemma_cast_then_mod_51(c3);
        lemma_cast_then_mod_51(c4);
    }

    assert(u64_5_as_nat(out_hat) == (c0_0 - pow2(51) * (c0_0 / (pow2(51) as u128))) + 19 * carry
        + pow2(51) * (c1 - pow2(51) * (c1 / (pow2(51) as u128))) + pow2(102) * (c2 - pow2(51) * (c2
        / (pow2(51) as u128))) + pow2(153) * (c3 - pow2(51) * (c3 / (pow2(51) as u128))) + pow2(204)
        * (c4 - pow2(51) * (c4 / (pow2(51) as u128)))) by {
        lemma_fundamental_div_mod(c0_0 as int, pow2(51) as int);
        lemma_fundamental_div_mod(c1 as int, pow2(51) as int);
        lemma_fundamental_div_mod(c2 as int, pow2(51) as int);
        lemma_fundamental_div_mod(c3 as int, pow2(51) as int);
        lemma_fundamental_div_mod(c4 as int, pow2(51) as int);
    }

    // carry = c4/s, c0_0/s = c1 - c1_0, c1/s = c2 - c2_0, etc.
    assert(u64_5_as_nat(out_hat) == (c0_0 - pow2(51) * (c1 - c1_0)) + 19 * carry + pow2(51) * (c1
        - pow2(51) * (c2 - c2_0)) + pow2(102) * (c2 - pow2(51) * (c3 - c3_0)) + pow2(153) * (c3
        - pow2(51) * (c4 - c4_0)) + pow2(204) * (c4 - pow2(51) * carry)) by {
        lemma_u128_shr_is_div(c0_0, 51);
        lemma_u128_shr_is_div(c1, 51);
        lemma_u128_shr_is_div(c2, 51);
        lemma_u128_shr_is_div(c3, 51);
        lemma_u128_shr_is_div(c4, 51);
    }

    // Telescoping: distribute and cancel, leaving only ci_0 terms minus p()*carry
    assert(u64_5_as_nat(out_hat) == c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0
        + pow2(204) * c4_0 - p() * carry) by {
        assert(c0_0 - pow2(51) * (c1 - c1_0) == c0_0 - pow2(51) * c1 + pow2(51) * c1_0) by {
            lemma_mul_is_distributive_sub(pow2(51) as int, c1 as int, c1_0 as int);
        }

        assert(pow2(51) * (c1 - pow2(51) * (c2 - c2_0)) == pow2(51) * c1 - pow2(102) * c2 + pow2(
            102,
        ) * c2_0) by {
            lemma_mul_sub(c1 as int, c2 as int, c2_0 as int, 51);
        }

        assert(pow2(102) * (c2 - pow2(51) * (c3 - c3_0)) == pow2(102) * c2 - pow2(153) * c3 + pow2(
            153,
        ) * c3_0) by {
            lemma_mul_sub(c2 as int, c3 as int, c3_0 as int, 102);
        }

        assert(pow2(153) * (c3 - pow2(51) * (c4 - c4_0)) == pow2(153) * c3 - pow2(204) * c4 + pow2(
            204,
        ) * c4_0) by {
            lemma_mul_sub(c3 as int, c4 as int, c4_0 as int, 153);
        }

        assert(pow2(204) * (c4 - pow2(51) * carry) == pow2(204) * c4 - pow2(255) * carry) by {
            lemma_mul_is_distributive_sub(pow2(204) as int, c4 as int, pow2(51) * carry);
            lemma_mul_is_associative(pow2(204) as int, pow2(51) as int, carry as int);
            lemma_pow2_adds(204, 51);
        }

        assert(c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0 + pow2(204) * c4_0 + 19
            * carry - pow2(255) * carry == c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153)
            * c3_0 + pow2(204) * c4_0 - p() * carry) by {
            pow255_gt_19();
            lemma_mul_is_distributive_sub_other_way(carry as int, pow2(255) as int, 19);
        }
    }

    let c_arr_as_nat = (c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0 + pow2(204)
        * c4_0);

    assert(u64_5_as_nat(out_hat) % p() == c_arr_as_nat as nat % p()) by {
        lemma_mod_diff_factor(carry as int, c_arr_as_nat as int, p() as int);
    }

    // Connect c_i_0 sums to the polynomial product via lemma_u64_5_as_nat_product
    lemma_u64_5_as_nat_product(a, b);

    let s1 = pow2(51);
    let s4 = pow2(204);

    // Rewrite c_i_0 from a[i]*(19*b[j]) form to 19*(a[i]*b[j]) form
    // to match the ensures of lemma_u64_5_as_nat_product
    assert(c0_0 == (a[0] * b[0] + 19 * (a[4] * b[1] + a[3] * b[2] + a[2] * b[3] + a[1] * b[4])))
        by {
        lemma_mul_is_associative(a[4] as int, b[1] as int, 19);
        lemma_mul_is_associative(a[3] as int, b[2] as int, 19);
        lemma_mul_is_associative(a[2] as int, b[3] as int, 19);
        lemma_mul_is_associative(a[1] as int, b[4] as int, 19);
        lemma_mul_distributive_4_terms(19, a[4] * b[1], a[3] * b[2], a[2] * b[3], a[1] * b[4]);
    }

    assert(c1_0 == (a[1] * b[0] + a[0] * b[1] + 19 * (a[4] * b[2] + a[3] * b[3] + a[2] * b[4])))
        by {
        lemma_mul_is_associative(a[4] as int, b[2] as int, 19);
        lemma_mul_is_associative(a[3] as int, b[3] as int, 19);
        lemma_mul_is_associative(a[2] as int, b[4] as int, 19);
        lemma_mul_distributive_3_terms(19, a[4] * b[2], a[3] * b[3], a[2] * b[4]);
    }

    assert(c2_0 == (a[2] * b[0] + a[1] * b[1] + a[0] * b[2] + 19 * (a[4] * b[3] + a[3] * b[4])))
        by {
        lemma_mul_is_associative(a[4] as int, b[3] as int, 19);
        lemma_mul_is_associative(a[3] as int, b[4] as int, 19);
        lemma_mul_is_distributive_add(19, a[4] * b[3], a[3] * b[4]);
    }

    assert(c3_0 == (a[3] * b[0] + a[2] * b[1] + a[1] * b[2] + a[0] * b[3] + 19 * (a[4] * b[4])))
        by {
        lemma_mul_is_associative(a[4] as int, b[4] as int, 19);
    }

    // c4_0 already matches the product lemma form directly
    // c4_0 == a[4]*b[0] + a[3]*b[1] + a[2]*b[2] + a[1]*b[3] + a[0]*b[4]

    // Now chain: c_arr_as_nat matches the reduced product form
    let reduced_sum = (s4 * (a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0])
        + pow2(153) * (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0] + 19 * (a[4] * b[4]))
        + pow2(102) * (a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + 19 * (a[3] * b[4] + a[4] * b[3]))
        + s1 * (a[0] * b[1] + a[1] * b[0] + 19 * (a[2] * b[4] + a[3] * b[3] + a[4] * b[2])) + (a[0]
        * b[0] + 19 * (a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1])));

    assert(c_arr_as_nat == reduced_sum);
    assert((u64_5_as_nat(a) * u64_5_as_nat(b)) % p() == reduced_sum as nat % p());
    assert(c_arr_as_nat as nat % p() == (u64_5_as_nat(a) * u64_5_as_nat(b)) % p());
}

// ============================================================
// § 8  Target function  (backend/serial/u64/field.rs:486–632)
//
//      The benchmark target.  Modelled as an inherent method (the upstream
//      `impl Mul<&FieldElement51> for &FieldElement51` carries its `requires`
//      via the `MulSpecImpl` trait; here it is stated directly).  The body and
//      proof block are the upstream ones verbatim.
// ============================================================

impl FieldElement51 {
    #[rustfmt::skip]  // keep alignment of c* calculations
    pub fn mul(&self, _rhs: &FieldElement51) -> (output: FieldElement51)
        requires
            fe51_limbs_bounded(self, 54),
            fe51_limbs_bounded(_rhs, 54),
        ensures
            fe51_as_canonical_nat(&output) == field_mul(
                fe51_as_canonical_nat(self),
                fe51_as_canonical_nat(_rhs),
            ),
            fe51_limbs_bounded(&output, 52),
            fe51_limbs_bounded(&output, 54),
    {
        // Alias self, _rhs for more readable formulas.
        let a: &[u64; 5] = &self.limbs;
        let b: &[u64; 5] = &_rhs.limbs;

        proof {
            lemma_mul_boundary(*a, *b);
        }

        // 64-bit precomputations to avoid 128-bit multiplications.
        let b1_19 = b[1] * 19;
        let b2_19 = b[2] * 19;
        let b3_19 = b[3] * 19;
        let b4_19 = b[4] * 19;

        // Multiply to get 128-bit coefficients of output
        // Each term a[i]*(19*b[j]) folds the 2^255 wraparound back in (2^255 ≡ 19 mod p).
        let c0: u128 = m(a[0], b[0]) + m(a[4], b1_19) + m(a[3], b2_19) + m(a[2], b3_19) + m(a[1], b4_19);
        let mut c1: u128 = m(a[1], b[0]) + m(a[0], b[1]) + m(a[4], b2_19) + m(a[3], b3_19) + m(a[2], b4_19);
        let mut c2: u128 = m(a[2], b[0]) + m(a[1], b[1]) + m(a[0], b[2]) + m(a[4], b3_19) + m(a[3], b4_19);
        let mut c3: u128 = m(a[3], b[0]) + m(a[2], b[1]) + m(a[1], b[2]) + m(a[0], b[3]) + m(a[4], b4_19);
        let mut c4: u128 = m(a[4], b[0]) + m(a[3], b[1]) + m(a[2], b[2]) + m(a[1], b[3]) + m(a[0], b[4]);

        // Casting to u64 and back tells the compiler the carry is bounded by
        // 2^64, so each addition is u128 + u64 rather than u128 + u128.
        let mut out = [0u64; 5];

        c1 += ((c0 >> 51) as u64) as u128;
        out[0] = (c0 as u64) & LOW_51_BIT_MASK;

        c2 += ((c1 >> 51) as u64) as u128;
        out[1] = (c1 as u64) & LOW_51_BIT_MASK;

        c3 += ((c2 >> 51) as u64) as u128;
        out[2] = (c2 as u64) & LOW_51_BIT_MASK;

        c4 += ((c3 >> 51) as u64) as u128;
        out[3] = (c3 as u64) & LOW_51_BIT_MASK;

        let carry: u64 = (c4 >> 51) as u64;
        out[4] = (c4 as u64) & LOW_51_BIT_MASK;

        // out[0] + carry*19 < 2^51 + 19*2^59.33 < 2^63.58, so no overflow.
        out[0] += carry * 19;

        // Now out[1] < 2^51 + 2^13 < 2^(51 + ε).
        out[1] += out[0] >> 51;
        out[0] &= LOW_51_BIT_MASK;

        proof {
            lemma_mul_value(*a, *b);
            assert(out =~= mul_return(*a, *b));
            assert(u64_5_as_nat(out) % p() == (u64_5_as_nat(*a) * u64_5_as_nat(*b)) % p());

            assert(fe51_as_canonical_nat(&FieldElement51 { limbs: out }) == field_mul(
                fe51_as_canonical_nat(self),
                fe51_as_canonical_nat(_rhs),
            )) by {
                pow255_gt_19();
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(*a) as int,
                    u64_5_as_nat(*b) as int,
                    p() as int,
                );
            }

            assert(1u64 << 52 <= 1u64 << 54) by (bit_vector);
            assert(fe51_limbs_bounded(&FieldElement51 { limbs: out }, 52));
            assert(fe51_limbs_bounded(&FieldElement51 { limbs: out }, 54));
        }

        // Now out[i] < 2^(51 + epsilon) for all i.
        FieldElement51 { limbs: out }
    }
}

} // verus!

fn main() {}
