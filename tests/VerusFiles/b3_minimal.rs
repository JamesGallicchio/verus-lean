// =============================================================================
// Benchmark B3 — `CompressedEdwardsY::decompress`
// =============================================================================
//
// Edwards-point decompression for Ed25519.  A `CompressedEdwardsY` is a 32-byte
// little-endian encoding of an affine y-coordinate (with the x sign bit stored
// in the high bit of byte 31).  `decompress` recovers the full extended
// `EdwardsPoint` (X:Y:Z:T):
//   1. decode y, set Z = 1, compute  u = y² − 1  and  v = d·y² + 1
//   2. x = sqrt(u/v) via `sqrt_ratio_i` — succeeds iff y is a valid coordinate
//   3. conditionally negate x to match the compressed sign bit, set T = X·Y.
//
// This runs in EVERY Ed25519 signature verification (SSH, TLS 1.3, code
// signing) and is the entry point of the Ristretto255 decode path.
//
// Postconditions:
//   (1) Validity ⇔ success — is_valid_edwards_y_coordinate(field_element_from_bytes(&self.0))
//                            <==> result.is_some()
//                            Decompression succeeds exactly when y lies on the
//                            curve, i.e. u/v is a square.
//
//   (2) On success (result.is_some()):
//       (a) edwards_y_nat(result.unwrap()) == field_element_from_bytes(&self.0)
//           The decoded Y equals the y encoded in the compressed bytes.
//       (b) edwards_z_nat(result.unwrap()) == 1
//           Z is normalised to 1 (the affine representative).
//       (c) is_well_formed_edwards_point(result.unwrap())
//           The point satisfies the extended-coordinate curve invariant and is
//           limb-bounded (feedable to point arithmetic without reduction).
//       (d) field_square(field_element_from_bytes(&self.0)) != 1
//               ==> edwards_x_sign_bit(result.unwrap()) == (self.0[31] >> 7)
//           The recovered x has the requested sign — except when y² = 1, where
//           x = 0, negation is a no-op, and the sign bit is forced to 0.
//
// Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
// Pinned commit: 3f3443e
//
// Assembled from:
//   curve25519-dalek/src/edwards.rs                              (target `decompress`, `step_1`, `step_2`, types)
//   curve25519-dalek/src/backend/serial/u64/field.rs             (FieldElement51, ONE)
//   curve25519-dalek/src/backend/serial/u64/constants.rs         (EDWARDS_D)
//   curve25519-dalek/src/backend/serial/u64/subtle_assumes.rs    (Choice / choice_is_true / choice_into)
//   curve25519-dalek/src/specs/core_specs.rs                     (u8_32_as_nat)
//   curve25519-dalek/src/specs/field_specs_u64.rs                (p, field_canonical, u64_5_as_nat, pow255_gt_19)
//   curve25519-dalek/src/specs/field_specs.rs                    (field_* ops, fe51_* specs, field_element_from_bytes)
//   curve25519-dalek/src/specs/edwards_specs.rs                  (curve / point predicates, accessors)
//   curve25519-dalek/src/lemmas/field_lemmas/add_lemmas.rs       (limb-bound weakening / sum-bound lemmas)
//   curve25519-dalek/src/lemmas/edwards_lemmas/decompress_lemmas.rs (lemma_decompress_valid_branch)
//
// MINIMAL: only the specs, constants, types and lemmas reachable from the
// `decompress` spec + body proof are kept; the field-algebra, sqrt, and curve
// sublemmas are pruned.  Following B1/B2, the heavy callees and the heavy
// curve lemma are TRUSTED:
//   * `step_1` / `step_2`            — the real field-operation pipelines, bodies
//                                       `assume(false)`, postconditions verbatim.
//   * `lemma_decompress_valid_branch` — ~70-line curve argument, body `admit()`.
// Their *statements* (and every spec they mention) are kept verbatim, so the
// sole real verification target is the `decompress` body (bottom of file): the
// branch on `is_valid_y_coord` plus the proof block that chains
// `lemma_decompress_valid_branch` → limb-bound weakening → well-formedness.
// =============================================================================

#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;   // lemma_mod_bound
use vstd::arithmetic::power2::*;    // pow2, lemma2_to64, lemma_pow2_strictly_increases
use vstd::prelude::*;

verus! {

// ============================================================
// § 1  Byte-to-nat spec  (specs/core_specs.rs)
// ============================================================

/// Little-endian natural value of a fixed 32-byte array (explicit 32-term form).
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

// ============================================================
// § 2  Field foundations mod p  (specs/field_specs_u64.rs)
// ============================================================

/// p = 2^255 - 19, the prime of GF(p) underlying Curve25519/Ed25519.
pub open spec fn p() -> nat {
    (pow2(255) - 19) as nat
}

pub open spec fn field_canonical(n: nat) -> nat {
    n % p()
}

pub open spec fn u64_5_as_field_canonical(limbs: [u64; 5]) -> nat {
    field_canonical(u64_5_as_nat(limbs))
}

/// Evaluation function: reconstruct the nat value a 5-limb (radix 2^51) element represents.
#[verusfmt::skip]
pub open spec fn u64_5_as_nat(limbs: [u64; 5]) -> nat {
                (limbs[0] as nat) +
    pow2( 51) * (limbs[1] as nat) +
    pow2(102) * (limbs[2] as nat) +
    pow2(153) * (limbs[3] as nat) +
    pow2(204) * (limbs[4] as nat)
}

// ============================================================
// § 3  Field element specs & math operations  (specs/field_specs.rs)
// ============================================================

/// Spec predicate: all limbs are bounded by a given bit limit.
pub open spec fn u64_5_bounded(limbs: [u64; 5], bit_limit: u64) -> bool {
    forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] < (1u64 << bit_limit)
}

/// Spec predicate: all limbs are bounded by a given bit limit.
pub open spec fn fe51_limbs_bounded(fe: &FieldElement51, bit_limit: u64) -> bool {
    u64_5_bounded(fe.limbs, bit_limit)
}

/// Spec predicate: sum of corresponding limbs is bounded (overflow-freedom for additions).
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

/// Returns the canonical mathematical value of a field element in [0, p).
pub open spec fn fe51_as_canonical_nat(fe: &FieldElement51) -> nat {
    u64_5_as_field_canonical(fe.limbs)
}

/// The canonical mathematical value when creating a field element from bytes.
/// The bytes are a little-endian integer with the high bit of byte[31] ignored,
/// then reduced into [0, p).
pub open spec fn field_element_from_bytes(bytes: &[u8; 32]) -> nat {
    field_canonical(u8_32_as_nat(bytes) % pow2(255))
}

/// Sign bit of a field element: the LSB of its canonical representation.
pub open spec fn fe51_as_canonical_nat_sign_bit(fe: &FieldElement51) -> u8 {
    ((fe51_as_canonical_nat(fe)) % 2) as u8
}

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

// ============================================================
// § 4  Types  (backend/serial/u64/field.rs, edwards.rs, subtle)
// ============================================================

/// An element of the field ℤ / p, in radix 2^51 (five u64 limbs).
#[derive(Copy, Clone)]
pub struct FieldElement51 {
    pub limbs: [u64; 5],
}

/// `field.rs` aliases `FieldElement` to the u64 backend representation.
pub type FieldElement = FieldElement51;

impl FieldElement51 {
    /// The multiplicative identity (1, represented as limbs [1,0,0,0,0]).
    pub const ONE: FieldElement51 = FieldElement51 { limbs: [1, 0, 0, 0, 0] };
}

/// Edwards `d` value, equal to `-121665/121666 mod p`.
/// (backend/serial/u64/constants.rs)
pub const EDWARDS_D: FieldElement51 = FieldElement51 {
    limbs: [929955233495203u64, 466365720129213u64, 1662059464998953u64, 2033849074728123u64, 1442794654840575u64],
};

/// A point on the Edwards form of Curve25519, in extended coordinates (X:Y:Z:T).
#[derive(Copy, Clone)]
pub struct EdwardsPoint {
    pub X: FieldElement,
    pub Y: FieldElement,
    pub Z: FieldElement,
    pub T: FieldElement,
}

/// A compressed Edwards y-coordinate: 32 little-endian bytes (x sign in bit 255).
pub struct CompressedEdwardsY(pub [u8; 32]);

/// Opaque constant-time boolean (`subtle::Choice`).  Modelled here as a local
/// trusted type; its observers are `external_body`, exactly as the upstream
/// `subtle_assumes.rs` wrappers are.
#[derive(Copy, Clone)]
pub struct Choice {
    v: u8,
}

// ============================================================
// § 5  Curve & point specifications  (specs/edwards_specs.rs)
// ============================================================

/// Twisted Edwards curve membership (a = -1):  -x² + y² = 1 + d·x²·y²  (mod p).
pub open spec fn is_on_edwards_curve(x: nat, y: nat) -> bool {
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let x2 = field_square(x);
    let y2 = field_square(y);
    let x2y2 = field_mul(x2, y2);
    let lhs = field_sub(y2, x2);
    let rhs = field_add(1, field_mul(d, x2y2));
    lhs == rhs
}

/// Homogenised projective curve equation: (Y² − X²)·Z² = Z⁴ + d·X²·Y².
pub open spec fn is_on_edwards_curve_projective(x: nat, y: nat, z: nat) -> bool {
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let x2 = field_square(x);
    let y2 = field_square(y);
    let z2 = field_square(z);
    let z4 = field_square(z2);
    let lhs = field_mul(field_sub(y2, x2), z2);
    let rhs = field_add(z4, field_mul(d, field_mul(x2, y2)));
    lhs == rhs
}

/// A y-coordinate is valid iff u/v is a square, where u = y²−1, v = d·y²+1.
/// Mirrors the `sqrt_ratio_i(&u, &v)` decision computed in `decompress`.
pub open spec fn is_valid_edwards_y_coordinate(y: nat) -> bool {
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let y2 = field_square(y);
    let u = field_sub(y2, 1);
    let v = field_add(field_mul(d, y2), 1);
    if u % p() == 0 {
        true
    } else if v % p() == 0 {
        false
    } else {
        exists|r: nat|
            r < p() && (#[trigger] field_mul(field_square(r), v) == u % p() || #[trigger] field_mul(
                field_square(r),
                v,
            ) == field_neg(u))
    }
}

// ---- EdwardsPoint field accessors (closed — encapsulate field access) ----

pub closed spec fn edwards_x(point: EdwardsPoint) -> FieldElement51 {
    point.X
}

pub closed spec fn edwards_y(point: EdwardsPoint) -> FieldElement51 {
    point.Y
}

pub closed spec fn edwards_z(point: EdwardsPoint) -> FieldElement51 {
    point.Z
}

pub closed spec fn edwards_t(point: EdwardsPoint) -> FieldElement51 {
    point.T
}

/// Equates the closed accessors with the raw struct fields.  Needed because
/// spec predicates use the closed accessors (for encapsulation) while proof
/// code after construction knows facts about the raw fields.
pub proof fn lemma_unfold_edwards(point: EdwardsPoint)
    ensures
        edwards_x(point) == point.X,
        edwards_y(point) == point.Y,
        edwards_z(point) == point.Z,
        edwards_t(point) == point.T,
{
}

// ---- EdwardsPoint predicates (open — bodies visible everywhere) ----

/// Math-level validity for an extended-coordinate tuple (X:Y:Z:T):
/// Z ≠ 0, the projective curve equation holds, and the Segre relation X·Y = Z·T.
pub open spec fn is_valid_extended_edwards_point(x: nat, y: nat, z: nat, t: nat) -> bool {
    field_canonical(z) != 0 && is_on_edwards_curve_projective(x, y, z) && field_mul(x, y)
        == field_mul(z, t)
}

/// An EdwardsPoint in extended coordinates is valid (curve + Segre + Z≠0).
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

/// A well-formed EdwardsPoint: mathematically valid and properly bounded.
pub open spec fn is_well_formed_edwards_point(point: EdwardsPoint) -> bool {
    is_valid_edwards_point(point) && edwards_point_limbs_bounded(point) && sum_of_limbs_bounded(
        &edwards_y(point),
        &edwards_x(point),
        u64::MAX,
    )
}

/// Canonical nat value of the Y coordinate.
pub open spec fn edwards_y_nat(point: EdwardsPoint) -> nat {
    fe51_as_canonical_nat(&edwards_y(point))
}

/// Canonical nat value of the Z coordinate.
pub open spec fn edwards_z_nat(point: EdwardsPoint) -> nat {
    fe51_as_canonical_nat(&edwards_z(point))
}

/// Sign bit of the X coordinate (LSB of the canonical value).
pub open spec fn edwards_x_sign_bit(point: EdwardsPoint) -> u8 {
    fe51_as_canonical_nat_sign_bit(&edwards_x(point))
}

// ============================================================
// § 6  Choice helpers  (backend/serial/u64/subtle_assumes.rs)
//
//      Trusted observers of the opaque `Choice`, mirroring the upstream
//      `subtle` wrappers (each `external_body`).
// ============================================================

/// Spec-level view of Choice as a boolean (true = Choice(1), false = Choice(0)).
pub uninterp spec fn choice_is_true(c: Choice) -> bool;

impl Choice {
    /// `subtle::Choice::from(u8)`.
    #[verifier::external_body]
    pub fn from(u: u8) -> (c: Choice)
        ensures
            (u == 1) == choice_is_true(c),
    {
        Choice { v: u }
    }
}

/// `subtle::Choice::into::<bool>`.
#[verifier::external_body]
pub fn choice_into(c: Choice) -> (b: bool)
    ensures
        b == choice_is_true(c),
{
    c.v == 1
}

// ============================================================
// § 7  Reachable proof lemmas  (specs/field_specs_u64.rs, lemmas/field_lemmas/add_lemmas.rs)
//
//      Small, self-contained; kept with their real bodies.
// ============================================================

/// 2^255 > 19 (so p() > 0).
pub proof fn pow255_gt_19()
    ensures
        pow2(255) > 19,
{
    lemma2_to64();  // 2^5 = 32
    lemma_pow2_strictly_increases(5, 255);
}

/// p() > 2.
pub proof fn p_gt_2()
    ensures
        p() > 2,
        (p() - 2) > 0,
{
    lemma2_to64();
    lemma_pow2_strictly_increases(5, 255);
}

/// Bound weakening: a-bit-bounded limbs are also b-bit-bounded when a < b ≤ 63.
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

/// If both inputs are n-bounded (n ≤ 62), their limb sums fit in u64.
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

// ============================================================
// § 8  Trusted curve lemma  (lemmas/edwards_lemmas/decompress_lemmas.rs)
// ============================================================

/// TRUSTED AXIOM (body `admit()`).  Main decompress valid-branch lemma: from the
/// step_1/step_2 postconditions, derives point validity, Y-preservation, and
/// sign-bit correctness (when y² ≠ 1).  Real proof: ~70 lines in
/// lemmas/edwards_lemmas/decompress_lemmas.rs (lemma_decompress_valid_branch),
/// via lemma_negation_preserves_curve / lemma_affine_to_extended_valid /
/// lemma_x_zero_implies_y_squared_one and the sign-bit sublemmas.
pub proof fn lemma_decompress_valid_branch(
    repr_bytes: &[u8; 32],
    x_orig: nat,
    point: &EdwardsPoint,
)
    requires
    // step_1 postconditions
        fe51_as_canonical_nat(&point.Y) == field_element_from_bytes(repr_bytes),
        is_on_edwards_curve(x_orig, fe51_as_canonical_nat(&point.Y)),
        x_orig % 2 == 0,
        x_orig < p(),
        // step_2 postconditions
        fe51_as_canonical_nat(&point.X) == (if (repr_bytes[31] >> 7) == 1 {
            field_neg(x_orig)
        } else {
            x_orig
        }),
        fe51_as_canonical_nat(&point.Z) == 1,
        fe51_as_canonical_nat(&point.T) == field_mul(
            fe51_as_canonical_nat(&point.X),
            fe51_as_canonical_nat(&point.Y),
        ),
    ensures
        is_valid_edwards_point(*point),
        fe51_as_canonical_nat(&point.Y) == field_element_from_bytes(repr_bytes),
        // Sign bit correctness when y² ≠ 1 (i.e., x ≠ 0).  When y² == 1, x = 0
        // and negation is the identity, so the sign bit is always 0.
        field_square(field_element_from_bytes(repr_bytes)) != 1 ==> fe51_as_canonical_nat_sign_bit(
            &point.X,
        ) == (repr_bytes[31] >> 7),
{
    admit();
}

// ============================================================
// § 9  Stubbed callees: step_1, step_2  (edwards.rs)
//
//      The real field-operation pipelines (from_bytes, square, sub/mul/add,
//      sqrt_ratio_i, conditional_negate).  Bodies `assume(false)`;
//      postconditions trusted as axioms, exactly as B2 stubs from_bytes_wide/pack.
// ============================================================

mod decompress {
    use super::*;

    /// PHASE 1–3 of decompression: decode Y, set Z = 1, compute u = y²−1 and
    /// v = d·y²+1, then `sqrt_ratio_i(&u,&v)` to obtain validity and candidate X.
    /// Body stubbed — real proof is ~110 lines in edwards.rs.
    pub(super) fn step_1(repr: &CompressedEdwardsY) -> (result: (
        Choice,
        FieldElement,
        FieldElement,
        FieldElement,
    ))  // Result components: (is_valid, X, Y, Z)
        ensures
            ({
                let (is_valid, X, Y, Z) = result;
                fe51_as_canonical_nat(&Y) == field_element_from_bytes(&repr.0)
                    &&
                fe51_as_canonical_nat(&Z) == 1
                    &&
                (choice_is_true(is_valid) <==> is_valid_edwards_y_coordinate(
                    fe51_as_canonical_nat(&Y),
                )) && (choice_is_true(is_valid) ==> is_on_edwards_curve(
                    fe51_as_canonical_nat(&X),
                    fe51_as_canonical_nat(&Y),
                )) &&
                // Limb bounds for step_2: X is 52-bit (from sqrt_ratio_i), Y, Z are 51-bit.
                fe51_limbs_bounded(&X, 52) && fe51_limbs_bounded(&Y, 51) && fe51_limbs_bounded(
                    &Z,
                    51,
                )
                    &&
                // X is the non-negative root (LSB = 0) - from sqrt_ratio_i.
                fe51_as_canonical_nat(&X) % 2 == 0
            }),
    {
        assume(false);
        (Choice { v: 0 }, FieldElement51 { limbs: [0u64; 5] }, FieldElement51 { limbs: [0u64; 5] },
            FieldElement51 { limbs: [0u64; 5] })
    }

    /// PHASE 4 of decompression: conditionally negate X to the compressed sign
    /// bit, set T = X·Y, and assemble the EdwardsPoint.
    /// Body stubbed — real proof is ~80 lines in edwards.rs.
    pub(super) fn step_2(
        repr: &CompressedEdwardsY,
        X: FieldElement,
        Y: FieldElement,
        Z: FieldElement,
    ) -> (result: EdwardsPoint)
        requires
            fe51_limbs_bounded(&X, 52),
            fe51_limbs_bounded(&Y, 51),
            fe51_limbs_bounded(&Z, 51),
            is_on_edwards_curve(fe51_as_canonical_nat(&X), fe51_as_canonical_nat(&Y)),
            fe51_as_canonical_nat(&Z) == 1,
        ensures
            fe51_as_canonical_nat(&result.X)
                ==
            if (repr.0[31] >> 7) == 1 {
                field_neg(fe51_as_canonical_nat(&X))
            } else {
                fe51_as_canonical_nat(&X)
            },
            &result.Y == &Y && &result.Z == &Z
                &&
            fe51_as_canonical_nat(&result.T) == field_mul(
                fe51_as_canonical_nat(&result.X),
                fe51_as_canonical_nat(&result.Y),
            ),
            fe51_limbs_bounded(&result.X, 52),
            fe51_limbs_bounded(&result.T, 52),
    {
        assume(false);
        EdwardsPoint { X, Y, Z, T: FieldElement51 { limbs: [0u64; 5] } }
    }
}

// ============================================================
// § 10  Target function  (edwards.rs:279–354)
//
//       The benchmark target.  The body and proof block are the upstream ones
//       verbatim — the sole real verification target in the file.
// ============================================================

impl CompressedEdwardsY {
    /// Attempt to decompress to an `EdwardsPoint`.
    ///
    /// Returns `None` if the input is not the y-coordinate of a curve point.
    pub fn decompress(&self) -> (result: Option<EdwardsPoint>)
        ensures
    // Decompression succeeds iff the y-coordinate is valid.
            is_valid_edwards_y_coordinate(field_element_from_bytes(&self.0)) <==> result.is_some(),
            // When successful, the result has these properties:
            result.is_some() ==> (
            // The Y coordinate matches the one from the compressed representation.
            edwards_y_nat(result.unwrap()) == field_element_from_bytes(
                &self.0,
            )
            // Z is 1 in the decompressed representation.
             && edwards_z_nat(result.unwrap())
                == 1
            // The point is well-formed on the Edwards curve.
             && is_well_formed_edwards_point(
                result.unwrap(),
            )
            // The X coordinate sign bit matches the compressed sign bit when y² ≠ 1.
            // When y² == 1, x = 0 so negation is the identity and the sign bit is always 0.
             && (field_square(field_element_from_bytes(&self.0)) != 1 ==> edwards_x_sign_bit(
                result.unwrap(),
            ) == (self.0[31] >> 7))),
    {
        let (is_valid_y_coord, X, Y, Z) = decompress::step_1(self);

        proof {
            assert(choice_is_true(is_valid_y_coord) ==> is_valid_edwards_y_coordinate(
                field_element_from_bytes(&self.0),
            ));
            assert(choice_is_true(is_valid_y_coord) ==> is_on_edwards_curve(
                fe51_as_canonical_nat(&X),
                fe51_as_canonical_nat(&Y),
            ));
        }
        if choice_into(is_valid_y_coord) {
            let point = decompress::step_2(self, X, Y, Z);
            let result = Some(point);
            proof {
                lemma_unfold_edwards(point);
                // Extract values for lemma
                let x_orig = fe51_as_canonical_nat(&X);

                // Establish step_2 postconditions needed by lemma.
                // step_2 ensures Y and Z are preserved by reference equality.
                assert(&point.Y == &Y);
                assert(&point.Z == &Z);
                assert(fe51_as_canonical_nat(&point.Y) == field_element_from_bytes(&self.0));
                assert(fe51_as_canonical_nat(&point.Z) == 1);

                // x_orig < p() is trivially true since x_orig = fe51_as_canonical_nat(&X) = ...%p()
                pow255_gt_19();
                assert(x_orig < p()) by {
                    lemma_mod_bound(fe51_as_nat(&X) as int, p() as int);
                };

                // Use the unified lemma to prove all postconditions.
                lemma_decompress_valid_branch(&self.0, x_orig, &point);

                // Strengthen to well-formedness: bounds + sum bounds.
                assert(fe51_limbs_bounded(&point.Y, 51));
                assert(fe51_limbs_bounded(&point.Z, 51));
                assert((1u64 << 51) < (1u64 << 52)) by (bit_vector);
                lemma_fe51_limbs_bounded_weaken(&point.Y, 51, 52);
                lemma_fe51_limbs_bounded_weaken(&point.Z, 51, 52);

                assert(edwards_point_limbs_bounded(point));
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&point.Y, &point.X, 52);
                assert(is_well_formed_edwards_point(point));
            }
            result
        } else {
            let result = None;
            result
        }
    }
}

} // verus!

fn main() {}
