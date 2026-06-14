// =============================================================================
// Benchmark B1 — `FieldElement51::mul`
// =============================================================================
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
//   curve25519-dalek/src/backend/serial/u64/field.rs       (target `mul`, `m`, mask)
//   curve25519-dalek/src/specs/field_specs.rs              (fe51_* / field_mul specs)
//   curve25519-dalek/src/specs/field_specs_u64.rs          (p, u64_5_as_nat, pow255_gt_19)
//   curve25519-dalek/src/lemmas/field_lemmas/mul_lemmas.rs (mul_return, boundary/value lemmas)
//
// MINIMAL: only the specs, constants, helper, and lemmas reachable from the
// `mul` correctness proof are kept.  The two heavy lemmas
//   `lemma_mul_boundary`  (≈90 lines: u128 no-overflow / limb-bound facts)
//   `lemma_mul_value`     (≈210 lines: the carry-chain ≡ schoolbook-product
//                          mod p telescoping argument)
// have their bodies replaced with `admit()` — their postconditions are trusted
// as axioms, exactly as B2 trusts `from_bytes_wide`/`pack` via `assume(false)`.
// Their *statements* and every spec function they mention are kept verbatim, so
// the only real verification target is the `mul` body itself (bottom of file):
// the exec carry chain plus the proof block that chains
// `lemma_mul_boundary` → exec arithmetic (no overflow) →
// `lemma_mul_value` → `lemma_mul_mod_noop_general` to derive the two
// postconditions above.
// =============================================================================

#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;   // lemma_mul_mod_noop_general
use vstd::arithmetic::mul::*;       // lemma_mul_upper_bound (used in `m`)
use vstd::arithmetic::power2::*;    // pow2, lemma2_to64, lemma_pow2_strictly_increases
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
//      needed only to *state* the trusted lemmas below and to phrase the
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
//      exec body of `mul` needs.  It is the postcondition of the trusted
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

/// TRUSTED AXIOM (body `admit()`).  Establishes every no-overflow / limb-bound
/// fact the exec carry chain needs.  Real proof: ~90 lines in
/// lemmas/field_lemmas/mul_lemmas.rs (lemma_mul_boundary), via product/shift/
/// mask sublemmas.
pub proof fn lemma_mul_boundary(a: [u64; 5], b: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> a[i] < 1u64 << 54,
        forall|i: int| 0 <= i < 5 ==> b[i] < 1u64 << 54,
    ensures
        mul_boundary_spec(a, b),
{
    admit();
}

/// TRUSTED AXIOM (body `admit()`).  The mathematical heart: the carry-chain
/// output reduces (mod p) to the schoolbook product of the inputs.  Real proof:
/// ~210 lines in lemmas/field_lemmas/mul_lemmas.rs (lemma_mul_value), a
/// telescoping div/mod argument plus lemma_u64_5_as_nat_product.
pub proof fn lemma_mul_value(a: [u64; 5], b: [u64; 5])
    requires
        mul_boundary_spec(a, b),
    ensures
        u64_5_as_nat(mul_return(a, b)) % p() == (u64_5_as_nat(a) * u64_5_as_nat(b)) % p(),
{
    admit();
}

// ============================================================
// § 8  Target function  (backend/serial/u64/field.rs:486–632)
//
//      The benchmark target.  Modelled as an inherent method (the upstream
//      `impl Mul<&FieldElement51> for &FieldElement51` carries its `requires`
//      via the `MulSpecImpl` trait; here it is stated directly).  The body and
//      proof block are the upstream ones verbatim — this is the sole real
//      verification target in the file.
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
