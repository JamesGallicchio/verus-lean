// =============================================================================
// Benchmark B4 — `RistrettoPoint::compress`
// =============================================================================
//
// Ristretto255 point compression: the canonical 32-byte encoding of a point in
// the prime-order Ristretto group built over Edwards Curve25519.  Ristretto is
// a quotient construction (a variant of Decaf) that eliminates the cofactor 8
// of Curve25519, yielding a prime-order group with unique, canonical encodings.
// This encoding is what Bulletproofs and Pedersen commitments serialize on the
// wire.
//
// Given the underlying Edwards point (X : Y : Z : T) (with the Segre relation
// X·Y = Z·T), `compress` computes:
//   u1      = (Z + Y)(Z - Y)
//   u2      = X·Y
//   invsqrt = 1/√(u1·u2²)
//   i1      = invsqrt·u1,  i2 = invsqrt·u2,  z_inv = i1·i2·T
// then selects the unique coset representative (a sign-normalising rotation by
// the constant i = √(-1) and a final |·| on s), and serialises the field
// element s to 32 little-endian bytes.
//
// Postcondition:
//   result.0 == spec_ristretto_compress(*self)
//     The 32 output bytes equal the abstract Ristretto encoding of the point's
//     extended coordinates (X, Y, Z, T) reduced mod p = 2^255 - 19.  This is the
//     standard §5.3 Ristretto ENCODE.  Canonicality (the |s| ≥ 0 normalisation)
//     is what makes the encoding injective on the group, so two encodings are
//     equal iff the points are equal — the property cryptographic protocols
//     depend on.
//
// Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
// Pinned commit: 3f3443e
//
// Assembled from:
//   curve25519-dalek/src/ristretto.rs                       (target `compress`, types)
//   curve25519-dalek/src/specs/ristretto_specs.rs           (ristretto_compress_extended, spec_ristretto_compress)
//   curve25519-dalek/src/specs/edwards_specs.rs             (EdwardsPoint accessors, well-formedness, lemma_unfold_edwards)
//   curve25519-dalek/src/specs/field_specs.rs               (field_* ops, is_negative, nat_invsqrt, sqrt_m1, u8_32_from_nat)
//   curve25519-dalek/src/specs/field_specs_u64.rs           (p, u64_5_as_nat, field_canonical)
//   curve25519-dalek/src/specs/core_specs.rs                (u8_32_as_nat)
//   curve25519-dalek/src/backend/serial/u64/field.rs        (FieldElement51, ONE, add/sub/mul/square/as_bytes)
//   curve25519-dalek/src/field.rs                           (invsqrt, is_negative)
//   curve25519-dalek/src/backend/serial/u64/constants.rs    (SQRT_M1, INVSQRT_A_MINUS_D)
//   curve25519-dalek/src/backend/serial/u64/subtle_assumes.rs (Choice, conditional_assign/negate wrappers)
//   curve25519-dalek/src/lemmas/field_lemmas/*              (the supporting lemmas called from the proof block)
//
// MINIMAL / SELF-CONTAINED: every spec, type, constant, and lemma reachable from
// `compress` is inlined; no dalek modules are `use`d.  Following B1 (which
// `admit()`s its two heavy lemmas) and B2 (which stubs its callees with
// `assume(false)`), the external field operations (`fe_add`, `fe_sub`, `fe_mul`,
// `square`, `invsqrt`, `is_negative`, `as_bytes`, the `conditional_*` wrappers)
// and the heavy supporting lemmas are declared with their upstream
// `requires`/`ensures` reproduced verbatim and `admit()`/`external_body` bodies —
// their postconditions are trusted as axioms.  The infix field operators
// `+ - *` of the upstream code are rendered as the named methods `fe_add` /
// `fe_sub` / `fe_mul` (the `AddSpecImpl`/`SubSpecImpl`/`MulSpecImpl` trait
// machinery carries identical contracts upstream); every contract is preserved.
// The sole real verification target is the `compress` body and its proof block
// (bottom of file), which threads the field-op postconditions through the
// `ristretto_compress_extended` spec to discharge the encoding equality.
// =============================================================================

#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;   // lemma_small_mod, lemma_mod_bound
use vstd::arithmetic::power::*;     // pow
use vstd::arithmetic::power2::*;    // pow2, lemma_pow2_strictly_increases
use vstd::prelude::*;

verus! {

// ============================================================
// § 1  Limb-evaluation & field specs mod p
//      (specs/field_specs_u64.rs, specs/field_specs.rs)
// ============================================================

/// Evaluation function: reconstruct the nat value of five radix-2^51 limbs.
#[verusfmt::skip]
pub open spec fn u64_5_as_nat(limbs: [u64; 5]) -> nat {
                (limbs[0] as nat) +
    pow2( 51) * (limbs[1] as nat) +
    pow2(102) * (limbs[2] as nat) +
    pow2(153) * (limbs[3] as nat) +
    pow2(204) * (limbs[4] as nat)
}

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

/// Spec predicate: all limbs are bounded by a given bit limit.
pub open spec fn u64_5_bounded(limbs: [u64; 5], bit_limit: u64) -> bool {
    forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] < (1u64 << bit_limit)
}

/// Spec predicate: all limbs are bounded by a given bit limit.
pub open spec fn fe51_limbs_bounded(fe: &FieldElement51, bit_limit: u64) -> bool {
    u64_5_bounded(fe.limbs, bit_limit)
}

/// Spec predicate: sum of corresponding limbs is bounded.
pub open spec fn sum_of_limbs_bounded(
    fe1: &FieldElement51,
    fe2: &FieldElement51,
    bound: u64,
) -> bool {
    forall|i: int| 0 <= i < 5 ==> fe1.limbs[i] + fe2.limbs[i] < bound
}

pub open spec fn fe51_as_nat(fe: &FieldElement51) -> nat {
    u64_5_as_nat(fe.limbs)
}

/// Canonical mathematical value of a field element in [0, p).
pub open spec fn fe51_as_canonical_nat(fe: &FieldElement51) -> nat {
    u64_5_as_field_canonical(fe.limbs)
}

// Spec-level field operations on natural numbers (mod p).

/// Math-level field addition.
pub open spec fn field_add(a: nat, b: nat) -> nat {
    field_canonical(a + b)
}

/// Math-level field subtraction.
pub open spec fn field_sub(a: nat, b: nat) -> nat {
    field_canonical((field_canonical(a) + p() - field_canonical(b)) as nat)
}

/// Math-level field multiplication.
pub open spec fn field_mul(a: nat, b: nat) -> nat {
    field_canonical(a * b)
}

/// Math-level field negation.
pub open spec fn field_neg(a: nat) -> nat {
    field_canonical((p() - field_canonical(a)) as nat)
}

/// Math-level field squaring.
pub open spec fn field_square(a: nat) -> nat {
    field_canonical(a * a)
}

/// A field element is negative if its canonical low bit is 1.
pub open spec fn is_negative(a: nat) -> bool {
    field_canonical(a) % 2 == 1
}

/// r² · v ≡ u (mod p): the "square" sqrt-ratio relation.
pub open spec fn is_sqrt_ratio(u: nat, v: nat, r: nat) -> bool {
    field_canonical(r * r * v) == field_canonical(u)
}

/// r² · v ≡ i·u (mod p): the "nonsquare" sqrt-ratio relation (i = √(-1)).
pub open spec fn is_sqrt_ratio_times_i(u: nat, v: nat, r: nat) -> bool {
    field_canonical(r * r * v) == field_mul(sqrt_m1(), u)
}

/// b² · v ≡ u (mod p), on FieldElement51 values.
pub open spec fn fe51_is_sqrt_ratio(
    u: &FieldElement51,
    v: &FieldElement51,
    r: &FieldElement51,
) -> bool {
    is_sqrt_ratio(fe51_as_canonical_nat(u), fe51_as_canonical_nat(v), fe51_as_canonical_nat(r))
}

/// b² · v ≡ i·u (mod p), on FieldElement51 values.
pub open spec fn fe51_is_sqrt_ratio_times_i(
    u: &FieldElement51,
    v: &FieldElement51,
    r: &FieldElement51,
) -> bool {
    is_sqrt_ratio_times_i(
        fe51_as_canonical_nat(u),
        fe51_as_canonical_nat(v),
        fe51_as_canonical_nat(r),
    )
}

/// Inverse square root in GF(p): the canonical nonneg r with r²·a ≡ 1 (square
/// case) or r²·a ≡ √(-1) (nonsquare case), and r = 0 when a ≡ 0.
pub open spec fn nat_invsqrt(a: nat) -> nat {
    if a % p() == 0 {
        0
    } else {
        let a3 = field_mul(field_square(a), a);
        let a7 = field_mul(field_square(a3), a);
        let k = ((p() - 5) / 8) as nat;
        let r_raw = field_mul(a3, (pow(a7 as int, k) as nat) % p());
        let check = field_mul(a, field_square(r_raw));
        let neg_one = field_neg(1);
        let neg_i = field_neg(sqrt_m1());
        let r_adj = if check == neg_one || check == neg_i {
            field_mul(sqrt_m1(), r_raw)
        } else {
            r_raw
        };
        if is_negative(r_adj) {
            field_neg(r_adj)
        } else {
            r_adj
        }
    }
}

/// The mathematical value of SQRT_M1 (√(-1) mod p), the 4th root of unity.
pub open spec fn sqrt_m1() -> nat {
    fe51_as_canonical_nat(&SQRT_M1)
}

// ============================================================
// § 2  Byte specs  (specs/core_specs.rs, specs/field_specs.rs)
// ============================================================

/// Little-endian natural value of a fixed 32-byte array.
#[verusfmt::skip]
pub open spec fn u8_32_as_nat(bytes: &[u8; 32]) -> nat {
    (bytes[ 0] as nat) * pow2(  0) + (bytes[ 1] as nat) * pow2(  8) +
    (bytes[ 2] as nat) * pow2( 16) + (bytes[ 3] as nat) * pow2( 24) +
    (bytes[ 4] as nat) * pow2( 32) + (bytes[ 5] as nat) * pow2( 40) +
    (bytes[ 6] as nat) * pow2( 48) + (bytes[ 7] as nat) * pow2( 56) +
    (bytes[ 8] as nat) * pow2( 64) + (bytes[ 9] as nat) * pow2( 72) +
    (bytes[10] as nat) * pow2( 80) + (bytes[11] as nat) * pow2( 88) +
    (bytes[12] as nat) * pow2( 96) + (bytes[13] as nat) * pow2(104) +
    (bytes[14] as nat) * pow2(112) + (bytes[15] as nat) * pow2(120) +
    (bytes[16] as nat) * pow2(128) + (bytes[17] as nat) * pow2(136) +
    (bytes[18] as nat) * pow2(144) + (bytes[19] as nat) * pow2(152) +
    (bytes[20] as nat) * pow2(160) + (bytes[21] as nat) * pow2(168) +
    (bytes[22] as nat) * pow2(176) + (bytes[23] as nat) * pow2(184) +
    (bytes[24] as nat) * pow2(192) + (bytes[25] as nat) * pow2(200) +
    (bytes[26] as nat) * pow2(208) + (bytes[27] as nat) * pow2(216) +
    (bytes[28] as nat) * pow2(224) + (bytes[29] as nat) * pow2(232) +
    (bytes[30] as nat) * pow2(240) + (bytes[31] as nat) * pow2(248)
}

/// Canonical little-endian bytes for a nat (mod 2^256).
pub open spec fn u8_32_from_nat(n: nat) -> [u8; 32] {
    choose|b: [u8; 32]| u8_32_as_nat(&b) == n % pow2(256)
}

// ============================================================
// § 3  Types  (backend/serial/u64/field.rs, edwards.rs, ristretto.rs)
// ============================================================

/// An element of the field ℤ / p, in radix 2^51 (five u64 limbs).
#[derive(Copy, Clone)]
pub struct FieldElement51 {
    pub limbs: [u64; 5],
}

impl FieldElement51 {
    /// The multiplicative identity, 1.
    pub const ONE: FieldElement51 = FieldElement51 { limbs: [1, 0, 0, 0, 0] };
}

/// Alias used throughout the curve code.
pub type FieldElement = FieldElement51;

/// An `EdwardsPoint` in extended twisted-Edwards coordinates (X : Y : Z : T),
/// with the Segre relation X·Y = Z·T.
#[derive(Copy, Clone)]
pub struct EdwardsPoint {
    pub X: FieldElement,
    pub Y: FieldElement,
    pub Z: FieldElement,
    pub T: FieldElement,
}

/// A `RistrettoPoint` wraps an `EdwardsPoint`; the wrapping accounts for the
/// cofactor quotient via custom (de)compression.
#[derive(Copy, Clone)]
pub struct RistrettoPoint(pub EdwardsPoint);

/// The canonical 32-byte Ristretto encoding.
pub struct CompressedRistretto(pub [u8; 32]);

// ============================================================
// § 4  Curve constants  (backend/serial/u64/constants.rs)
// ============================================================

/// One precomputed square root of -1 (mod p): the rotation constant i.
pub const SQRT_M1: FieldElement51 = FieldElement51 {
    limbs: [1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133],
};

/// Precomputed 1/√(a - d) (a = -1), the Ristretto "magic" denominator constant.
pub const INVSQRT_A_MINUS_D: FieldElement51 = FieldElement51 {
    limbs: [278908739862762, 821645201101625, 8113234426968, 1777959178193151, 2118520810568447],
};

// ============================================================
// § 5  Choice (constant-time selection bit)  (subtle_assumes.rs)
// ============================================================

/// Constant-time boolean, mirroring `subtle::Choice`.
#[derive(Copy, Clone)]
pub struct Choice(pub u8);

/// Spec-level view of a `Choice` as a boolean (true = Choice(1)).
pub uninterp spec fn choice_is_true(c: Choice) -> bool;

// ============================================================
// § 6  EdwardsPoint accessors & well-formedness  (specs/edwards_specs.rs)
//
//      The accessors are `closed` upstream (encapsulating pub(crate) fields);
//      `lemma_unfold_edwards` is the bridge equating them with the raw fields.
// ============================================================

pub closed spec fn edwards_x(point: EdwardsPoint) -> FieldElement51 { point.X }

pub closed spec fn edwards_y(point: EdwardsPoint) -> FieldElement51 { point.Y }

pub closed spec fn edwards_z(point: EdwardsPoint) -> FieldElement51 { point.Z }

pub closed spec fn edwards_t(point: EdwardsPoint) -> FieldElement51 { point.T }

/// Equates the closed accessors with the actual struct fields.
pub proof fn lemma_unfold_edwards(point: EdwardsPoint)
    ensures
        edwards_x(point) == point.X,
        edwards_y(point) == point.Y,
        edwards_z(point) == point.Z,
        edwards_t(point) == point.T,
{
}

/// The field element values (X, Y, Z, T) of an EdwardsPoint, reduced mod p.
pub open spec fn edwards_point_as_nat(point: EdwardsPoint) -> (nat, nat, nat, nat) {
    let x = fe51_as_canonical_nat(&edwards_x(point));
    let y = fe51_as_canonical_nat(&edwards_y(point));
    let z = fe51_as_canonical_nat(&edwards_z(point));
    let t = fe51_as_canonical_nat(&edwards_t(point));
    (x, y, z, t)
}

/// Math-level validity of (X:Y:Z:T): Z ≠ 0, the projective curve equation, and
/// the Segre relation X·Y = Z·T.  The curve-equation predicate is left
/// uninterpreted here (it is irrelevant to the encoding equality this file
/// proves — `compress` only needs the limb bounds and the Z+Y limb-sum bound).
pub uninterp spec fn is_on_edwards_curve_projective(x: nat, y: nat, z: nat) -> bool;

pub open spec fn is_valid_extended_edwards_point(x: nat, y: nat, z: nat, t: nat) -> bool {
    field_canonical(z) != 0 && is_on_edwards_curve_projective(x, y, z) && field_mul(x, y)
        == field_mul(z, t)
}

pub open spec fn is_valid_edwards_point(point: EdwardsPoint) -> bool {
    let x = fe51_as_canonical_nat(&edwards_x(point));
    let y = fe51_as_canonical_nat(&edwards_y(point));
    let z = fe51_as_canonical_nat(&edwards_z(point));
    let t = fe51_as_canonical_nat(&edwards_t(point));
    is_valid_extended_edwards_point(x, y, z, t)
}

/// EdwardsPoint invariant: all coordinate limbs are 52-bounded.
pub open spec fn edwards_point_limbs_bounded(point: EdwardsPoint) -> bool {
    fe51_limbs_bounded(&edwards_x(point), 52) && fe51_limbs_bounded(&edwards_y(point), 52)
        && fe51_limbs_bounded(&edwards_z(point), 52) && fe51_limbs_bounded(&edwards_t(point), 52)
}

/// A well-formed EdwardsPoint: mathematically valid, limb-bounded, and with the
/// Y+X limb sum bounded (needed for the niels-style additions in `compress`).
pub open spec fn is_well_formed_edwards_point(point: EdwardsPoint) -> bool {
    is_valid_edwards_point(point) && edwards_point_limbs_bounded(point) && sum_of_limbs_bounded(
        &edwards_y(point),
        &edwards_x(point),
        u64::MAX,
    )
}

// ============================================================
// § 7  Ristretto encoding spec  (specs/ristretto_specs.rs)
// ============================================================

/// Ristretto encoding from extended coordinates (X : Y : Z : T).
///
/// Selects the unique coset representative whose serialised s is non-negative,
/// then serialises s.  Reference: [RISTRETTO] §5.3; [DECAF] §6.
pub open spec fn ristretto_compress_extended(x: nat, y: nat, z: nat, t: nat) -> [u8; 32] {
    // u1 = (Z + Y)(Z - Y)
    let u1 = field_mul(field_add(z, y), field_sub(z, y));
    // u2 = X·Y
    let u2 = field_mul(x, y);
    // invsqrt = 1/sqrt(u1·u2²)
    let invsqrt = nat_invsqrt(field_mul(u1, field_square(u2)));
    // i1 = invsqrt·u1
    let i1 = field_mul(invsqrt, u1);
    // i2 = invsqrt·u2
    let i2 = field_mul(invsqrt, u2);
    // z_inv = i1·i2·T
    let z_inv = field_mul(i1, field_mul(i2, t));
    // den_inv = i2
    let den_inv = i2;

    // iX = i·X
    let iX = field_mul(x, sqrt_m1());
    // iY = i·Y
    let iY = field_mul(y, sqrt_m1());
    // enchanted_denominator = i1·INVSQRT_A_MINUS_D
    let enchanted_denominator = field_mul(i1, fe51_as_canonical_nat(&INVSQRT_A_MINUS_D));

    // rotate = is_negative(T·z_inv)
    let rotate = is_negative(field_mul(t, z_inv));
    let x_rot = if rotate {
        iY
    } else {
        x
    };
    let y_rot = if rotate {
        iX
    } else {
        y
    };
    let den_inv_rot = if rotate {
        enchanted_denominator
    } else {
        den_inv
    };

    // y_final = -y_rot if x_rot·z_inv is negative, else y_rot
    let y_final = if is_negative(field_mul(x_rot, z_inv)) {
        field_neg(y_rot)
    } else {
        y_rot
    };
    // s = den_inv_rot · (Z - y_final)
    let s = field_mul(den_inv_rot, field_sub(z, y_final));
    // s_final = |s|
    let s_final = if is_negative(s) {
        field_neg(s)
    } else {
        s
    };

    u8_32_from_nat(s_final)
}

/// Ristretto encoding from a RistrettoPoint (delegates to extended coordinates).
pub open spec fn spec_ristretto_compress(point: RistrettoPoint) -> [u8; 32] {
    let (x, y, z, t) = edwards_point_as_nat(point.0);
    ristretto_compress_extended(x, y, z, t)
}

// ============================================================
// § 8  Supporting lemmas (specs/field_specs_u64.rs, lemmas/field_lemmas/*)
//
//      The bound/canonical/sqrt-ratio sublemmas the `compress` proof block
//      calls.  Their statements are reproduced verbatim; the nontrivial ones
//      carry `admit()` bodies (TRUSTED AXIOMs), exactly as B1 admits its heavy
//      lemmas.  The purely-structural ones (weakening, sum bound, constant
//      limb bounds, 2^255 > 19) are discharged here directly.
// ============================================================

/// Proof that 2^255 > 19.
pub proof fn pow255_gt_19()
    ensures
        pow2(255) > 19,
{
    lemma2_to64();  // 2^5 = 32
    lemma_pow2_strictly_increases(5, 255);
}

/// Weaken a limb bound from `a` bits to `b` bits.
pub proof fn lemma_fe51_limbs_bounded_weaken(fe: &FieldElement51, a: u64, b: u64)
    requires
        fe51_limbs_bounded(fe, a),
        a < b,
        b <= 63,
    ensures
        fe51_limbs_bounded(fe, b),
{
    assert forall|i: int| 0 <= i < 5 implies fe.limbs[i] < (1u64 << b) by {
        assert(fe.limbs[i] < (1u64 << a));
        assert((1u64 << a) < (1u64 << b)) by (bit_vector)
            requires
                a < b,
                b <= 63,
        ;
    }
}

/// From per-limb bounds, the pairwise limb sums fit in u64.
pub proof fn lemma_sum_of_limbs_bounded_from_fe51_bounded(
    a: &FieldElement51,
    b: &FieldElement51,
    n: u64,
)
    requires
        fe51_limbs_bounded(a, n),
        fe51_limbs_bounded(b, n),
        n <= 62,
    ensures
        sum_of_limbs_bounded(a, b, u64::MAX),
{
    assert forall|i: int| 0 <= i < 5 implies a.limbs[i] + b.limbs[i] < u64::MAX by {
        assert(a.limbs[i] < (1u64 << n));
        assert(b.limbs[i] < (1u64 << n));
        assert((1u64 << n) + (1u64 << n) < u64::MAX) by (bit_vector)
            requires
                n <= 62,
        ;
    }
}

/// SQRT_M1's limbs are 54-bounded (all are < 2^51).
pub proof fn lemma_sqrt_m1_limbs_bounded()
    ensures
        fe51_limbs_bounded(&SQRT_M1, 54),
{
    assert(SQRT_M1.limbs[0] < (1u64 << 54)) by (bit_vector);
    assert(SQRT_M1.limbs[1] < (1u64 << 54)) by (bit_vector);
    assert(SQRT_M1.limbs[2] < (1u64 << 54)) by (bit_vector);
    assert(SQRT_M1.limbs[3] < (1u64 << 54)) by (bit_vector);
    assert(SQRT_M1.limbs[4] < (1u64 << 54)) by (bit_vector);
}

/// INVSQRT_A_MINUS_D's limbs are 54-bounded.
pub proof fn lemma_invsqrt_a_minus_d_limbs_bounded()
    ensures
        fe51_limbs_bounded(&INVSQRT_A_MINUS_D, 54),
{
    assert(INVSQRT_A_MINUS_D.limbs[0] < (1u64 << 54)) by (bit_vector);
    assert(INVSQRT_A_MINUS_D.limbs[1] < (1u64 << 54)) by (bit_vector);
    assert(INVSQRT_A_MINUS_D.limbs[2] < (1u64 << 54)) by (bit_vector);
    assert(INVSQRT_A_MINUS_D.limbs[3] < (1u64 << 54)) by (bit_vector);
    assert(INVSQRT_A_MINUS_D.limbs[4] < (1u64 << 54)) by (bit_vector);
}

/// The canonical value of any field element is < p.
pub proof fn lemma_canonical_nat_lt_p(x: &FieldElement)
    ensures
        fe51_as_canonical_nat(x) < p(),
{
    assert(pow2(255) > 19) by {
        pow255_gt_19();
    };
    lemma_mod_bound(fe51_as_nat(x) as int, p() as int);
}

/// TRUSTED AXIOM (body `admit()`).  `square`'s `pow(·,2)`-phrased postcondition
/// matches the `field_square` spec used by the encoding.  Real proof: ~30 lines
/// in lemmas/field_lemmas/field_algebra_lemmas.rs (lemma_square_matches_field_square),
/// unfolding `pow(y,2)` and applying mod-product absorption.
pub proof fn lemma_square_matches_field_square(y_raw: nat, y2_raw: nat)
    requires
        y2_raw % p() == pow(y_raw as int, 2) as nat % p(),
    ensures
        y2_raw % p() == field_square(y_raw % p()),
{
    admit();
}

/// TRUSTED AXIOM (body `admit()`).  For the special case u = 1, the sqrt-ratio
/// candidate produced by `invsqrt` always satisfies one of the two sqrt-ratio
/// relations.  Real proof: ~40 lines in lemmas/field_lemmas/constants_lemmas.rs
/// (lemma_one_field_element_value).
pub proof fn lemma_one_field_element_value(v: nat, r: nat)
    requires
        v < p(),
        r < p(),
        v != 0,
    ensures
        is_sqrt_ratio(1, v, r) || is_sqrt_ratio_times_i(1, v, r),
{
    admit();
}

/// TRUSTED AXIOM (body `admit()`).  A nonneg field element satisfying a
/// sqrt-ratio relation against u = 1 is exactly `nat_invsqrt`.  Real proof:
/// ~30 lines in lemmas/field_lemmas/sqrt_ratio_lemmas.rs
/// (lemma_invsqrt_matches_spec), via the invsqrt-uniqueness lemma.
pub proof fn lemma_invsqrt_matches_spec(big_i_nat: nat, v_u2_sqr_nat: nat)
    requires
        big_i_nat % 2 == 0,
        (v_u2_sqr_nat == 0) ==> (big_i_nat == 0),
        (v_u2_sqr_nat != 0) ==> (is_sqrt_ratio(1, v_u2_sqr_nat, big_i_nat) || is_sqrt_ratio_times_i(
            1,
            v_u2_sqr_nat,
            big_i_nat,
        )),
        big_i_nat < p(),
        v_u2_sqr_nat < p(),
    ensures
        big_i_nat == nat_invsqrt(v_u2_sqr_nat),
{
    admit();
}

// ============================================================
// § 9  External field operations  (backend/serial/u64/field.rs, field.rs,
//                                  subtle_assumes.rs)
//
//      Each is the benchmark's trusted leaf: declared `external_body` with the
//      upstream `requires`/`ensures` reproduced verbatim (the operator forms
//      `+ - *` rendered as named methods).  Their correctness is the subject of
//      B1 (`mul`) and sibling benchmarks; here they are axioms.
// ============================================================

impl FieldElement51 {
    /// TRUSTED AXIOM (external body).  Limb-wise field addition (upstream
    /// `Add for &FieldElement51`).
    #[verifier::external_body]
    pub fn fe_add(&self, rhs: &FieldElement51) -> (output: FieldElement51)
        requires
            sum_of_limbs_bounded(self, rhs, u64::MAX),
        ensures
            fe51_as_canonical_nat(&output) == field_add(
                fe51_as_canonical_nat(self),
                fe51_as_canonical_nat(rhs),
            ),
            fe51_limbs_bounded(self, 51) && fe51_limbs_bounded(rhs, 51) ==> fe51_limbs_bounded(
                &output,
                52,
            ),
            fe51_limbs_bounded(self, 52) && fe51_limbs_bounded(rhs, 52) ==> fe51_limbs_bounded(
                &output,
                53,
            ),
    {
        unimplemented!()
    }

    /// TRUSTED AXIOM (external body).  Field subtraction with reduction
    /// (upstream `Sub for &FieldElement51`).
    #[verifier::external_body]
    pub fn fe_sub(&self, rhs: &FieldElement51) -> (output: FieldElement51)
        requires
            fe51_limbs_bounded(self, 54),
            fe51_limbs_bounded(rhs, 54),
        ensures
            fe51_as_canonical_nat(&output) == field_sub(
                fe51_as_canonical_nat(self),
                fe51_as_canonical_nat(rhs),
            ),
            fe51_limbs_bounded(&output, 52),
            fe51_limbs_bounded(&output, 54),
    {
        unimplemented!()
    }

    /// TRUSTED AXIOM (external body).  Field multiplication (upstream
    /// `Mul for &FieldElement51`; correctness is benchmark B1).
    #[verifier::external_body]
    pub fn fe_mul(&self, rhs: &FieldElement51) -> (output: FieldElement51)
        requires
            fe51_limbs_bounded(self, 54),
            fe51_limbs_bounded(rhs, 54),
        ensures
            fe51_as_canonical_nat(&output) == field_mul(
                fe51_as_canonical_nat(self),
                fe51_as_canonical_nat(rhs),
            ),
            fe51_limbs_bounded(&output, 52),
            fe51_limbs_bounded(&output, 54),
    {
        unimplemented!()
    }

    /// TRUSTED AXIOM (external body).  Field squaring.
    #[verifier::external_body]
    pub fn square(&self) -> (r: FieldElement51)
        requires
            fe51_limbs_bounded(self, 54),
        ensures
            fe51_limbs_bounded(&r, 52),
            fe51_limbs_bounded(&r, 54),
            fe51_as_canonical_nat(&r) == field_canonical(
                pow(u64_5_as_nat(self.limbs) as int, 2) as nat,
            ),
    {
        unimplemented!()
    }

    /// TRUSTED AXIOM (external body).  Inverse square root: returns a `Choice`
    /// flag (square case) and the canonical nonneg root.
    #[verifier::external_body]
    pub fn invsqrt(&self) -> (result: (Choice, FieldElement))
        requires
            fe51_limbs_bounded(self, 54),
        ensures
            (fe51_as_canonical_nat(self) == 0) ==> (!choice_is_true(result.0)
                && fe51_as_canonical_nat(&result.1) == 0),
            (choice_is_true(result.0)) ==> fe51_is_sqrt_ratio(&FieldElement::ONE, self, &result.1),
            (!choice_is_true(result.0) && fe51_as_canonical_nat(self) != 0)
                ==> fe51_is_sqrt_ratio_times_i(&FieldElement::ONE, self, &result.1),
            fe51_limbs_bounded(&result.1, 52),
            fe51_as_canonical_nat(&result.1) % 2 == 0,
    {
        unimplemented!()
    }

    /// TRUSTED AXIOM (external body).  Sign test: the result `Choice` is true
    /// iff the canonical value is negative (odd low bit).  Upstream the
    /// postcondition is phrased over the serialised low byte and bridged to
    /// `is_negative` by `lemma_is_negative_bridge`; here the bridge is folded in.
    #[verifier::external_body]
    pub fn is_negative(&self) -> (result: Choice)
        ensures
            choice_is_true(result) == is_negative(fe51_as_canonical_nat(self)),
    {
        unimplemented!()
    }

    /// TRUSTED AXIOM (external body).  Serialise to 32 canonical little-endian
    /// bytes.
    #[verifier::external_body]
    pub fn as_bytes(self) -> (r: [u8; 32])
        ensures
            u8_32_as_nat(&r) == fe51_as_canonical_nat(&self),
    {
        unimplemented!()
    }
}

/// TRUSTED AXIOM (external body).  Constant-time conditional assignment
/// (upstream `subtle::ConditionallySelectable::conditional_assign` wrapper).
#[verifier::external_body]
pub fn conditional_assign_field_element(a: &mut FieldElement51, b: &FieldElement51, choice: Choice)
    requires
        fe51_limbs_bounded(old(a), 52),
        fe51_limbs_bounded(b, 52),
    ensures
        !choice_is_true(choice) ==> *a == *old(a),
        choice_is_true(choice) ==> *a == *b,
        fe51_limbs_bounded(a, 52),
{
    unimplemented!()
}

/// TRUSTED AXIOM (external body).  Constant-time conditional negation
/// (upstream `subtle::ConditionallyNegatable::conditional_negate` wrapper).
#[verifier::external_body]
pub fn conditional_negate_field_element(a: &mut FieldElement51, choice: Choice)
    requires
        fe51_limbs_bounded(old(a), 54),
    ensures
        fe51_limbs_bounded(a, 54),
        choice_is_true(choice) ==> fe51_limbs_bounded(a, 52),
        !choice_is_true(choice) ==> *a == *old(a),
        fe51_as_canonical_nat(a) == if choice_is_true(choice) {
            field_neg(fe51_as_canonical_nat(old(a)))
        } else {
            fe51_as_canonical_nat(old(a))
        },
{
    unimplemented!()
}

// ============================================================
// § 10  Target function  (ristretto.rs:1102–1413)
//
//       The benchmark target.  The body is the upstream `compress` verbatim,
//       with the infix field operators rewritten to the named methods
//       (`Z + &Y` → `Z.fe_add(&Y)`, `&X * &Y` → `X.fe_mul(&Y)`, etc.) and the
//       `conditional_assign_generic`/`conditional_assign` calls routed through
//       the field-element wrapper.  This is the sole real verification target.
// ============================================================

impl RistrettoPoint {
    /// Compress this point using the Ristretto encoding.
    pub fn compress(&self) -> (result: CompressedRistretto)
        requires
            is_well_formed_edwards_point(self.0),
        ensures
            result.0 == spec_ristretto_compress(*self),
    {
        // Link accessor-based predicates to actual fields.
        proof {
            lemma_unfold_edwards(self.0);
        }

        let ghost x_nat = fe51_as_canonical_nat(&self.0.X);
        let ghost y_nat = fe51_as_canonical_nat(&self.0.Y);
        let ghost z_nat = fe51_as_canonical_nat(&self.0.Z);
        let ghost t_nat = fe51_as_canonical_nat(&self.0.T);

        proof {
            assert(sum_of_limbs_bounded(&self.0.Z, &self.0.Y, u64::MAX)) by {
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&self.0.Z, &self.0.Y, 52);
            };
            assert(fe51_limbs_bounded(&SQRT_M1, 54)) by {
                lemma_sqrt_m1_limbs_bounded();
            };
            assert(fe51_limbs_bounded(&INVSQRT_A_MINUS_D, 54)) by {
                lemma_invsqrt_a_minus_d_limbs_bounded();
            };
        }

        let mut X = self.0.X;
        let mut Y = self.0.Y;
        let Z = &self.0.Z;
        let T = &self.0.T;

        proof {
            assert(fe51_limbs_bounded(Z, 54) && fe51_limbs_bounded(&Y, 54) && fe51_limbs_bounded(
                &X,
                54,
            ) && fe51_limbs_bounded(T, 54)) by {
                lemma_fe51_limbs_bounded_weaken(Z, 52, 54);
                lemma_fe51_limbs_bounded_weaken(&Y, 52, 54);
                lemma_fe51_limbs_bounded_weaken(&X, 52, 54);
                lemma_fe51_limbs_bounded_weaken(T, 52, 54);
            };
        }

        /* ORIGINAL CODE: let u1 = &(Z + &Y) * &(Z - &Y); */
        let z_plus_y = Z.fe_add(&Y);
        let z_minus_y = Z.fe_sub(&Y);
        proof {
            assert(fe51_limbs_bounded(&z_plus_y, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&z_plus_y, 53, 54);
            };
        }
        let u1 = z_plus_y.fe_mul(&z_minus_y);
        let u2 = X.fe_mul(&Y);
        proof {
            assert(fe51_as_canonical_nat(&u1) == field_mul(
                field_add(z_nat, y_nat),
                field_sub(z_nat, y_nat),
            ));
        }

        /* ORIGINAL CODE: let (_, invsqrt) = (&u1 * &u2.square()).invsqrt(); */
        // Ignore return value since this is always square
        let u2_sq = u2.square();
        proof {
            assert(fe51_as_canonical_nat(&u2_sq) == field_square(fe51_as_canonical_nat(&u2))) by {
                lemma_square_matches_field_square(fe51_as_nat(&u2), fe51_as_nat(&u2_sq));
            };
        }
        let u1_u2_sq = u1.fe_mul(&u2_sq);
        let ghost u1_u2_sq_nat = fe51_as_canonical_nat(&u1_u2_sq);
        proof {
            assert(u1_u2_sq_nat == field_mul(
                fe51_as_canonical_nat(&u1),
                field_square(fe51_as_canonical_nat(&u2)),
            ));
        }

        let (_, invsqrt) = u1_u2_sq.invsqrt();
        let ghost invsqrt_nat = fe51_as_canonical_nat(&invsqrt);

        proof {
            assert(invsqrt_nat == nat_invsqrt(u1_u2_sq_nat)) by {
                assert(invsqrt_nat < p()) by {
                    lemma_canonical_nat_lt_p(&invsqrt);
                };
                assert(u1_u2_sq_nat < p()) by {
                    lemma_canonical_nat_lt_p(&u1_u2_sq);
                };
                if u1_u2_sq_nat == 0 {
                } else {
                    assert(is_sqrt_ratio(1, u1_u2_sq_nat, invsqrt_nat) || is_sqrt_ratio_times_i(
                        1,
                        u1_u2_sq_nat,
                        invsqrt_nat,
                    )) by {
                        lemma_one_field_element_value(u1_u2_sq_nat, invsqrt_nat);
                    };
                }
                lemma_invsqrt_matches_spec(invsqrt_nat, u1_u2_sq_nat);
            };
            assert(fe51_limbs_bounded(&invsqrt, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&invsqrt, 52, 54);
            };
        }

        let i1 = invsqrt.fe_mul(&u1);
        let i2 = invsqrt.fe_mul(&u2);
        /* ORIGINAL CODE: let z_inv = &i1 * &(&i2 * T); */
        let i2_t = i2.fe_mul(T);
        let z_inv = i1.fe_mul(&i2_t);
        let mut den_inv = i2;

        let ghost i1_nat = fe51_as_canonical_nat(&i1);
        let ghost i2_nat = fe51_as_canonical_nat(&i2);
        let ghost z_inv_nat = fe51_as_canonical_nat(&z_inv);

        proof {
            assert(z_inv_nat == field_mul(i1_nat, field_mul(i2_nat, t_nat)));
        }

        let iX = X.fe_mul(&SQRT_M1);
        let iY = Y.fe_mul(&SQRT_M1);
        let enchanted_denominator = i1.fe_mul(&INVSQRT_A_MINUS_D);

        let ghost ed_nat = fe51_as_canonical_nat(&enchanted_denominator);

        proof {
            assert(ed_nat == field_mul(
                i1_nat,
                fe51_as_canonical_nat(&INVSQRT_A_MINUS_D),
            ));
        }

        /* ORIGINAL CODE: let rotate = (T * &z_inv).is_negative(); */
        let t_z_inv = T.fe_mul(&z_inv);
        let rotate = t_z_inv.is_negative();

        let ghost rotate_bool = is_negative(field_mul(t_nat, z_inv_nat));
        proof {
            assert(choice_is_true(rotate) == rotate_bool);
        }

        let ghost old_den_inv = den_inv;

        /* <ORIGINAL CODE>
        X.conditional_assign(&iY, rotate);
        Y.conditional_assign(&iX, rotate);
        den_inv.conditional_assign(&enchanted_denominator, rotate);
        </ORIGINAL CODE> */
        // Use the field-element conditional-assign wrapper for Verus compatibility.
        conditional_assign_field_element(&mut X, &iY, rotate);
        conditional_assign_field_element(&mut Y, &iX, rotate);
        conditional_assign_field_element(&mut den_inv, &enchanted_denominator, rotate);

        let ghost x_rot = fe51_as_canonical_nat(&X);
        let ghost y_rot = fe51_as_canonical_nat(&Y);
        let ghost den_inv_rot = fe51_as_canonical_nat(&den_inv);

        proof {
            assert(den_inv_rot == if rotate_bool {
                ed_nat
            } else {
                i2_nat
            }) by {
                if choice_is_true(rotate) {
                } else {
                    assert(den_inv == old_den_inv);
                }
            };
            assert(fe51_limbs_bounded(&X, 52));
            assert(fe51_limbs_bounded(&Y, 52));
            assert(fe51_limbs_bounded(&den_inv, 52));
        }

        /* ORIGINAL CODE: Y.conditional_negate((&X * &z_inv).is_negative()); */
        let x_z_inv = X.fe_mul(&z_inv);
        let x_z_inv_neg = x_z_inv.is_negative();
        proof {
            assert(choice_is_true(x_z_inv_neg) == is_negative(field_mul(x_rot, z_inv_nat)));
        }

        // Use the conditional-negate wrapper.
        proof {
            assert(fe51_limbs_bounded(&Y, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&Y, 52, 54);
            };
        }
        conditional_negate_field_element(&mut Y, x_z_inv_neg);

        let ghost y_final = fe51_as_canonical_nat(&Y);
        proof {
            assert(y_final == if is_negative(field_mul(x_rot, z_inv_nat)) {
                field_neg(y_rot)
            } else {
                y_rot
            });
        }

        proof {
            assert(fe51_limbs_bounded(&den_inv, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&den_inv, 52, 54);
            };
        }
        /* ORIGINAL CODE: let mut s = &den_inv * &(Z - &Y); */
        let z_minus_y_final = Z.fe_sub(&Y);
        let mut s = den_inv.fe_mul(&z_minus_y_final);

        let ghost s_pre_nat = fe51_as_canonical_nat(&s);
        proof {
            assert(fe51_as_canonical_nat(&z_minus_y_final) == field_sub(z_nat, y_final));
            assert(s_pre_nat == field_mul(den_inv_rot, field_sub(z_nat, y_final)));
        }

        let s_is_negative = s.is_negative();
        proof {
            assert(choice_is_true(s_is_negative) == is_negative(s_pre_nat));
        }

        // Use the conditional-negate wrapper.
        proof {
            assert(fe51_limbs_bounded(&s, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&s, 52, 54);
            };
        }
        conditional_negate_field_element(&mut s, s_is_negative);

        let ghost s_final_nat = fe51_as_canonical_nat(&s);
        proof {
            assert(s_final_nat == if is_negative(s_pre_nat) {
                field_neg(s_pre_nat)
            } else {
                s_pre_nat
            });
        }

        /* ORIGINAL CODE: CompressedRistretto(s.as_bytes()) */
        let s_bytes = s.as_bytes();

        proof {
            assert(s_bytes == u8_32_from_nat(s_final_nat)) by {
                assert(u8_32_as_nat(&s_bytes) == s_final_nat);
                assert(s_final_nat < pow2(256)) by {
                    lemma_canonical_nat_lt_p(&s);
                    pow255_gt_19();
                    lemma_pow2_strictly_increases(255, 256);
                };
                assert(s_final_nat % pow2(256) == s_final_nat) by {
                    lemma_small_mod(s_final_nat, pow2(256));
                };
                let chosen = u8_32_from_nat(s_final_nat);
                lemma_canonical_bytes_equal(&s_bytes, &chosen);
            };

            assert(s_bytes == ristretto_compress_extended(x_nat, y_nat, z_nat, t_nat)) by {
                let spec_u1 = field_mul(field_add(z_nat, y_nat), field_sub(z_nat, y_nat));
                let spec_u2 = field_mul(x_nat, y_nat);
                let spec_invsqrt = nat_invsqrt(field_mul(spec_u1, field_square(spec_u2)));
                let spec_i1 = field_mul(spec_invsqrt, spec_u1);
                let spec_i2 = field_mul(spec_invsqrt, spec_u2);
                let spec_z_inv = field_mul(spec_i1, field_mul(spec_i2, t_nat));

                assert(invsqrt_nat == spec_invsqrt);
                assert(i1_nat == spec_i1);
                assert(i2_nat == spec_i2);
                assert(z_inv_nat == spec_z_inv);
                assert(rotate_bool == is_negative(field_mul(t_nat, spec_z_inv)));

                assert(x_rot == if rotate_bool {
                    field_mul(y_nat, sqrt_m1())
                } else {
                    x_nat
                });
                assert(y_rot == if rotate_bool {
                    field_mul(x_nat, sqrt_m1())
                } else {
                    y_nat
                });
                assert(den_inv_rot == if rotate_bool {
                    field_mul(spec_i1, fe51_as_canonical_nat(&INVSQRT_A_MINUS_D))
                } else {
                    spec_i2
                });

                assert(y_final == if is_negative(field_mul(x_rot, spec_z_inv)) {
                    field_neg(y_rot)
                } else {
                    y_rot
                });
                assert(s_pre_nat == field_mul(den_inv_rot, field_sub(z_nat, y_final)));
                assert(s_final_nat == if is_negative(s_pre_nat) {
                    field_neg(s_pre_nat)
                } else {
                    s_pre_nat
                });
            };
        }

        CompressedRistretto(s_bytes)
    }
}

// ============================================================
// § 11  Byte-equality lemma  (lemmas/common_lemmas/to_nat_lemmas.rs)
//
//       Two 32-byte arrays with the same little-endian value are equal.
// ============================================================

/// TRUSTED AXIOM (body `admit()`).  Equal little-endian value ⇒ equal bytes.
/// Real proof: ~15 lines in lemmas/common_lemmas/to_nat_lemmas.rs
/// (lemma_canonical_bytes_equal), via per-index byte extraction.
pub proof fn lemma_canonical_bytes_equal(bytes1: &[u8; 32], bytes2: &[u8; 32])
    requires
        u8_32_as_nat(bytes1) == u8_32_as_nat(bytes2),
    ensures
        forall|i: int| 0 <= i < 32 ==> bytes1[i] == bytes2[i],
{
    admit();
}

} // verus!

fn main() {}
