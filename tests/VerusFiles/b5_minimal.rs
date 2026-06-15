// =============================================================================
// Benchmark B5 — `MontgomeryPoint::mul_clamped`
// =============================================================================
//
// Core scalar multiplication of X25519 (the Diffie-Hellman function used in
// TLS 1.3, Signal, WireGuard and SSH).  A `MontgomeryPoint` holds the affine
// u-coordinate u₀(P) of a point P on the Montgomery form of Curve25519 (or its
// twist).  `mul_clamped` _clamps_ the 32 input bytes — clears the low 3 bits,
// clears bit 255, sets bit 254 — to a value n ∈ 2^254 + 8·{0, …, 2^251−1}, then
// returns the u-coordinate of [n]P.  Clamping is what every Curve25519 protocol
// actually uses: it forces the scalar into the prime-order coset and pins its
// bit-length, defeating small-subgroup and timing attacks.
//
// `mul_clamped` itself is ~25 lines: it builds an (intentionally unreduced)
// `Scalar` from the clamped bytes and delegates to the `*` operator, which
// drives the Montgomery ladder `mul_bits_be` (Algorithm 8 of Costello-Smith
// 2017, ~400 lines with a loop invariant and differential add-and-double
// axioms).
//
// Postcondition (the benchmark target):
//   Correctness — let P = canonical_montgomery_lift(montgomery_point_as_nat(self)),
//                     n = u8_32_as_nat(spec_clamp_integer(bytes)),
//                     R = montgomery_scalar_mul(P, n)
//                 in  montgomery_point_as_nat(result) == u_coordinate(R)
//                 The output's u-coordinate is the u-coordinate of [n]·P, where
//                 n is the *clamped* integer (NOT reduced mod the group order —
//                 clamped values sit in [2^254, 2^255), above ℓ ≈ 2^252).
//
// Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
// Pinned commit: 3f3443e
//
// Assembled from:
//   curve25519-dalek/src/montgomery.rs                 (mul_clamped, mul_bits_be, the `Mul` operator)
//   curve25519-dalek/src/scalar.rs                     (clamp_integer, the `Scalar` type)
//   curve25519-dalek/src/specs/montgomery_specs.rs     (MontgomeryAffine + the montgomery_* specs)
//   curve25519-dalek/src/specs/scalar_specs.rs         (scalar_as_nat, spec_clamp_integer, is_clamped_integer)
//   curve25519-dalek/src/specs/field_specs.rs          (field_* / field_element_from_bytes / is_square)
//   curve25519-dalek/src/specs/field_specs_u64.rs      (p, field_canonical, u64_5_* helpers)
//   curve25519-dalek/src/specs/core_specs.rs           (u8_32_as_nat, bits_be_as_nat)
//   curve25519-dalek/src/backend/serial/u64/constants.rs (MONTGOMERY_A)
//
// MINIMAL: only the specs, constants and types reachable from the `mul_clamped`
// correctness proof are kept; the Edwards machinery, Elligator2, hashing,
// equality and every unrelated curve operation are removed.
//
// What is ADMITTED, and why (all heavy CURVE/LADDER facts, never `mul_clamped`):
//   * `mul_bits_be`  — the ~400-line Montgomery ladder (constant-time
//                      differential add-and-double with a loop invariant and the
//                      Costello-Smith differential-addition correctness axioms).
//                      Declared with its `requires`/`ensures` reproduced verbatim
//                      and body `assume(false)`; its postcondition is trusted as
//                      an axiom.  Far too heavy to reproduce at "reasonable
//                      scale", exactly the case the B5 spec flags.
//   * `<&MontgomeryPoint as Mul<&Scalar>>::mul` — the `*` operator `mul_clamped`
//                      delegates to.  Its real body converts the scalar to a
//                      big-endian bit slice (a second loop plus a battery of
//                      bit-to-nat lemmas) and calls `mul_bits_be`.  Stubbed with
//                      its `ensures` verbatim and body `assume(false)`, trusted
//                      as an axiom — this is precisely the callee-stubbing
//                      pattern B2 uses for `from_bytes_wide`/`pack`.
//   * `spec_mod_inverse` — left UNINTERPRETED.  `field_inv` names it, but no
//                      reachable proof constrains an inverse's value, so the
//                      gcd / extended-Euclid chain is irrelevant here.
//
// As in B1/B2, the *statements* of the admitted items and every spec function
// they mention are kept verbatim, so the only real verification target is the
// body + proof block of `mul_clamped` (bottom of file): it chains
// `clamp_integer.ensures` (clamped == spec_clamp_integer(bytes)) with the `*`
// operator's `ensures` to discharge the correctness postcondition.
// `clamp_integer` itself is kept faithful and verifies (a short bit_vector proof).
// =============================================================================

#![allow(unused_imports)]
#![allow(non_snake_case)]
use vstd::arithmetic::power2::*;    // pow2, lemma2_to64, lemma_pow2_strictly_increases
use vstd::prelude::*;

verus! {

// ============================================================
// § 1  Field value specs mod p  (specs/field_specs_u64.rs, specs/core_specs.rs)
// ============================================================

/// p = 2^255 - 19, the prime of the Curve25519 base field.
pub open spec fn p() -> nat {
    (pow2(255) - 19) as nat
}

pub open spec fn field_canonical(n: nat) -> nat {
    n % p()
}

// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
#[verusfmt::skip]
pub open spec fn u64_5_as_nat(limbs: [u64; 5]) -> nat {
                (limbs[0] as nat) +
    pow2( 51) * (limbs[1] as nat) +
    pow2(102) * (limbs[2] as nat) +
    pow2(153) * (limbs[3] as nat) +
    pow2(204) * (limbs[4] as nat)
}

pub open spec fn u64_5_as_field_canonical(limbs: [u64; 5]) -> nat {
    field_canonical(u64_5_as_nat(limbs))
}

/// Little-endian natural value of a fixed 32-byte array (explicit 32-term form for SMT).
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

/// Big-endian natural value of a bit slice (bits[0] is most significant).
/// `mul_bits_be` interprets its argument with this; reproduced because the
/// ladder's `ensures` mentions it.
pub open spec fn bits_be_as_nat(bits: &[bool], len: int) -> nat
    recommends
        0 <= len <= bits.len(),
    decreases len,
{
    if len <= 0 {
        0
    } else {
        let bit_value = if bits[len - 1] { 1nat } else { 0nat };
        bit_value + 2 * bits_be_as_nat(bits, len - 1)
    }
}

// ============================================================
// § 2  Field element type & per-element specs  (backend/serial/u64/field.rs, specs/field_specs.rs)
// ============================================================

/// An element of the field ℤ / p, in radix 2^51 as five u64 limbs.
#[derive(Copy, Clone)]
pub struct FieldElement51 {
    pub limbs: [u64; 5],
}

pub open spec fn fe51_as_nat(fe: &FieldElement51) -> nat {
    u64_5_as_nat(fe.limbs)
}

/// Returns the canonical mathematical value of a field element in [0, p).
pub open spec fn fe51_as_canonical_nat(fe: &FieldElement51) -> nat {
    u64_5_as_field_canonical(fe.limbs)
}

/// Canonical value of a 32-byte little-endian encoding, with bit 255 ignored.
pub open spec fn field_element_from_bytes(bytes: &[u8; 32]) -> nat {
    field_canonical(u8_32_as_nat(bytes) % pow2(255))
}

// ============================================================
// § 3  Math-level field operations mod p  (specs/field_specs.rs)
//
//      Reproduced verbatim because the Montgomery curve specs below
//      (`montgomery_rhs`, `montgomery_add`, `canonical_sqrt`) are phrased in
//      terms of them.  Only `is_square` / `field_sqrt` are exercised by the
//      reachable postcondition; the arithmetic operators appear inside spec
//      bodies that the stubbed callees never force open.
// ============================================================

pub open spec fn field_add(a: nat, b: nat) -> nat {
    field_canonical(a + b)
}

pub open spec fn field_sub(a: nat, b: nat) -> nat {
    field_canonical((field_canonical(a) + p() - field_canonical(b)) as nat)
}

pub open spec fn field_mul(a: nat, b: nat) -> nat {
    field_canonical(a * b)
}

pub open spec fn field_neg(a: nat) -> nat {
    field_canonical((p() - field_canonical(a)) as nat)
}

pub open spec fn field_square(a: nat) -> nat {
    field_canonical(a * a)
}

/// Uninterpreted modular inverse.  Upstream `field_inv` computes this via
/// extended Euclid; no reachable `mul_clamped` proof constrains an inverse's
/// value, so the value is left abstract here.
pub uninterp spec fn spec_mod_inverse(a: nat, m: nat) -> nat;

/// Math-level field inversion: w such that (a · w) % p == 1 (and 0 ↦ 0).
pub open spec fn field_inv(a: nat) -> nat {
    if a % p() == 0 {
        0
    } else {
        spec_mod_inverse(a, p())
    }
}

/// Quadratic-residue test modulo p.
pub open spec fn is_square(a: nat) -> bool {
    exists|y: nat| (#[trigger] field_mul(y, y)) == field_canonical(a)
}

/// Some square root of `a` modulo p (unspecified if `a` is a non-residue).
pub open spec fn field_sqrt(a: nat) -> nat
    recommends
        is_square(a),
{
    choose|y: nat| y < p() && #[trigger] field_mul(y, y) == field_canonical(a)
}

// ============================================================
// § 4  Curve constant  (backend/serial/u64/constants.rs)
// ============================================================

/// Montgomery curve coefficient A = 486662 for Curve25519 (B·v² = u³ + A·u² + u).
pub const MONTGOMERY_A: FieldElement51 = FieldElement51 { limbs: [486662, 0, 0, 0, 0] };

// ============================================================
// § 5  Montgomery point types & curve specs
//      Types `MontgomeryPoint` / `ProjectivePoint`: montgomery.rs.
//      `MontgomeryAffine` + the montgomery_* specs: specs/montgomery_specs.rs.
// ============================================================

/// Holds the u-coordinate of a point on the Montgomery form of Curve25519 or its twist.
#[derive(Copy, Clone, Debug)]
pub struct MontgomeryPoint(pub [u8; 32]);

/// Projective x-only point (U:W); affine u = U/W, infinity when W = 0.
/// Upstream montgomery.rs types these fields as `FieldElement`, the u64 backend's
/// alias for `FieldElement51` (field.rs: `type FieldElement = … FieldElement51`);
/// the concrete type is named here. `ProjectivePoint` is not reached by the
/// `mul_clamped` proof.
pub struct ProjectivePoint {
    pub U: FieldElement51,
    pub W: FieldElement51,
}

/// Affine Montgomery point: either infinity or a finite point (u, v).
pub enum MontgomeryAffine {
    /// Point at infinity (identity element of the group).
    Infinity,
    /// Finite point with u-coordinate and v-coordinate.
    Finite { u: nat, v: nat },
}

/// The u-coordinate of a Montgomery point as a canonical field element.
pub open spec fn montgomery_point_as_nat(point: MontgomeryPoint) -> nat {
    field_element_from_bytes(&point.0)
}

/// f(u) = u³ + A·u² + u over the field.
pub open spec fn montgomery_rhs(u: nat) -> nat {
    let A = fe51_as_canonical_nat(&MONTGOMERY_A);
    let u2 = field_mul(u, u);
    let u3 = field_mul(u2, u);
    let Au2 = field_mul(A, u2);
    field_add(field_add(u3, Au2), u)
}

/// A u-coordinate is valid iff f(u) is a quadratic residue (so a v exists).
pub open spec fn is_valid_u_coordinate(u: nat) -> bool {
    is_square(montgomery_rhs(u))
}

/// A MontgomeryPoint is valid iff its u-coordinate admits a canonical lift.
pub open spec fn is_valid_montgomery_point(point: MontgomeryPoint) -> bool {
    let u = montgomery_point_as_nat(point);
    is_valid_u_coordinate(u)
}

/// Canonical square root: the root whose least-significant bit is 0.
pub open spec fn canonical_sqrt(r: nat) -> nat
    recommends
        is_square(r),
{
    let s1 = field_sqrt(r);
    let s2 = field_neg(s1);
    if (s1 % 2 == 0) { s1 } else { s2 }
}

/// Unique affine lift of a (non-torsion) u-coordinate, with v = canonical_sqrt(f(u)).
pub open spec fn canonical_montgomery_lift(u: nat) -> MontgomeryAffine
    recommends
        is_valid_u_coordinate(u),
{
    let v = canonical_sqrt(montgomery_rhs(u));
    MontgomeryAffine::Finite { u: u % p(), v }
}

/// Negation on the Montgomery curve: (u, v) ↦ (u, -v); ∞ ↦ ∞.
pub open spec fn montgomery_neg(P: MontgomeryAffine) -> MontgomeryAffine {
    match P {
        MontgomeryAffine::Infinity => MontgomeryAffine::Infinity,
        MontgomeryAffine::Finite { u, v } => { MontgomeryAffine::Finite { u, v: field_neg(v) } },
    }
}

/// Addition on the Montgomery curve via the chord-tangent method.
pub open spec fn montgomery_add(P: MontgomeryAffine, Q: MontgomeryAffine) -> MontgomeryAffine {
    match (P, Q) {
        (MontgomeryAffine::Infinity, _) => Q,
        (_, MontgomeryAffine::Infinity) => P,
        (MontgomeryAffine::Finite { u: u1, v: v1 }, MontgomeryAffine::Finite { u: u2, v: v2 }) => {
            let A = fe51_as_canonical_nat(&MONTGOMERY_A);
            // P = -Q
            if u1 == u2 && field_add(v1, v2) == 0 {
                MontgomeryAffine::Infinity
            } else if u1 == u2 && v1 == v2 {
                // P = Q (doubling)
                let u1_sq = field_square(u1);
                let numerator = field_add(
                    field_add(field_mul(3, u1_sq), field_mul(field_mul(2, A), u1)),
                    1,
                );
                let denominator = field_mul(2, v1);
                let lambda = field_mul(numerator, field_inv(denominator));
                let lambda_sq = field_square(lambda);
                let u3 = field_sub(field_sub(lambda_sq, A), field_mul(2, u1));
                let v3 = field_sub(field_mul(lambda, field_sub(u1, u3)), v1);
                MontgomeryAffine::Finite { u: u3, v: v3 }
            } else {
                // P ≠ Q
                let numerator = field_sub(v2, v1);
                let denominator = field_sub(u2, u1);
                let lambda = field_mul(numerator, field_inv(denominator));
                let lambda_sq = field_square(lambda);
                let u3 = field_sub(field_sub(field_sub(lambda_sq, A), u1), u2);
                let v3 = field_sub(field_mul(lambda, field_sub(u1, u3)), v1);
                MontgomeryAffine::Finite { u: u3, v: v3 }
            }
        },
    }
}

/// Extract the u-coordinate from a MontgomeryAffine point (∞ ↦ 0).
pub open spec fn u_coordinate(point: MontgomeryAffine) -> nat {
    match point {
        MontgomeryAffine::Infinity => 0,
        MontgomeryAffine::Finite { u, v: _ } => u,
    }
}

/// Scalar multiplication [n]P on the Montgomery curve (abstract spec).
pub open spec fn montgomery_scalar_mul(P: MontgomeryAffine, n: nat) -> MontgomeryAffine
    decreases n,
{
    if n == 0 {
        MontgomeryAffine::Infinity
    } else {
        montgomery_add(P, montgomery_scalar_mul(P, (n - 1) as nat))
    }
}

// ============================================================
// § 6  Scalar type & specs  (scalar.rs, specs/scalar_specs.rs)
// ============================================================

/// An element of ℤ / ℓℤ as a little-endian 32-byte encoding.  `mul_clamped`
/// constructs one whose value is NOT reduced mod ℓ (only invariant #1, value
/// < 2^255, holds — guaranteed by clamping).
#[derive(Copy, Clone)]
pub struct Scalar {
    pub bytes: [u8; 32],
}

/// The (unreduced) integer value of a Scalar's bytes.
pub open spec fn scalar_as_nat(s: &Scalar) -> nat {
    u8_32_as_nat(&s.bytes)
}

/// A byte array is a clamped X25519 integer: low 3 bits clear, bit 255 clear,
/// bit 254 set (so the value lies in [2^254, 2^255) and is divisible by 8).
pub open spec fn is_clamped_integer(bytes: &[u8; 32]) -> bool {
    bytes[0] & 0b0000_0111 == 0
        && bytes[31] & 0b1000_0000 == 0
        && bytes[31] & 0b0100_0000 == 0b0100_0000
        && bytes[31] <= 127
}

/// Spec-level clamping: clear low 3 bits of byte 0, clear bit 7 of byte 31, set bit 6 of byte 31.
pub open spec fn spec_clamp_integer(bytes: [u8; 32]) -> [u8; 32] {
    [
        bytes[0] & 0b1111_1000,
        bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
        bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
        bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30],
        bytes[31] & 0b0111_1111 | 0b0100_0000,
    ]
}

// ============================================================
// § 7  clamp_integer  (scalar.rs:4952 — kept faithful, verifies)
//
//      A short `const fn` whose proof is a handful of `by (bit_vector)` facts.
//      `mul_clamped` calls it directly, so it is reproduced verbatim.
// ============================================================

/// _Clamps_ the little-endian representation of a 32-byte integer into
/// 2^254 + 8·{0, …, 2^251 − 1}.  See `MontgomeryPoint::mul_clamped`.
#[must_use]
pub const fn clamp_integer(bytes: [u8; 32]) -> (result: [u8; 32])
    ensures
        is_clamped_integer(&result),
        result == spec_clamp_integer(bytes),
        forall|i: int| 1 <= i < 31 ==> #[trigger] result[i] == bytes[i],
        result[0] & 0b1111_1000 == bytes[0] & 0b1111_1000,
        result[31] & 0b0011_1111 == bytes[31] & 0b0011_1111,
{
    let mut result = bytes;

    // Clear low 3 bits: result[0] = bytes[0] & 0b1111_1000
    result[0] &= 0b1111_1000;

    // Clear bit 7 (MSB): result[31] = result[31] & 0b0111_1111
    result[31] &= 0b0111_1111;

    // Set bit 6: result[31] = result[31] | 0b0100_0000
    result[31] |= 0b0100_0000;

    proof {
        let r0: u8 = result[0];
        let r31: u8 = result[31];
        let b0: u8 = bytes[0];
        let b31: u8 = bytes[31];

        // is_clamped_integer: low 3 bits of byte 0 are cleared
        assert(r0 & 0b0000_0111u8 == 0u8) by (bit_vector)
            requires
                r0 == b0 & 0b1111_1000u8,
        ;
        // is_clamped_integer: bit 7 of byte 31 is cleared
        assert(r31 & 0b1000_0000u8 == 0u8) by (bit_vector)
            requires
                r31 == (b31 & 0b0111_1111u8) | 0b0100_0000u8,
        ;
        // is_clamped_integer: bit 6 of byte 31 is set
        assert(r31 & 0b0100_0000u8 == 0b0100_0000u8) by (bit_vector)
            requires
                r31 == (b31 & 0b0111_1111u8) | 0b0100_0000u8,
        ;
        // is_clamped_integer: byte 31 <= 127
        assert(r31 <= 127u8) by (bit_vector)
            requires
                r31 == (b31 & 0b0111_1111u8) | 0b0100_0000u8,
        ;

        // Bit preservation: bits 3-7 of byte 0
        assert(r0 & 0b1111_1000u8 == b0 & 0b1111_1000u8) by (bit_vector)
            requires
                r0 == b0 & 0b1111_1000u8,
        ;
        // Bit preservation: bits 0-5 of byte 31
        assert(r31 & 0b0011_1111u8 == b31 & 0b0011_1111u8) by (bit_vector)
            requires
                r31 == (b31 & 0b0111_1111u8) | 0b0100_0000u8,
        ;
    }

    result
}

// ============================================================
// § 8  The Montgomery ladder  (montgomery.rs:519 — TRUSTED AXIOM)
//
//      `mul_bits_be` is Algorithm 8 of Costello-Smith 2017: a constant-time
//      x-only ladder of `differential_add_and_double` steps carrying a loop
//      invariant (`montgomery_ladder_invariant`) plus the differential-addition
//      correctness axioms.  The faithful proof is ~400 lines (see the cited
//      source).  Per the B5 scale guidance, it is declared here with its
//      `requires`/`ensures` reproduced verbatim and a trusted `assume(false)`
//      body — its postcondition is taken as an axiom, exactly as B2 trusts its
//      stubbed callees.
// ============================================================

impl MontgomeryPoint {
    /// Given `self` = u₀(P) and a big-endian bit slice for n, return u₀([n]P).
    /// TRUSTED AXIOM (body `assume(false)`).
    pub fn mul_bits_be(&self, bits: &[bool]) -> (result: MontgomeryPoint)
        requires
            bits.len() <= 255,
            is_valid_montgomery_point(*self),
        ensures
            ({
                // Let P be the canonical affine lift of the input u-coordinate.
                let P = canonical_montgomery_lift(montgomery_point_as_nat(*self));
                let n = bits_be_as_nat(bits, bits.len() as int);
                let R = montgomery_scalar_mul(P, n);
                // result encodes u([n]P)
                montgomery_point_as_nat(result) == u_coordinate(R)
            }),
    {
        assume(false);
        MontgomeryPoint([0u8; 32])
    }
}

// ============================================================
// § 9  The `*` operator  (montgomery.rs:2607, specs/arithm_trait_specs.rs:318 — TRUSTED AXIOM)
//
//      `&MontgomeryPoint * &Scalar` is what `mul_clamped` delegates to.  Its
//      real body reverses `scalar.bits_le()` into a 255-bit big-endian slice
//      (a second loop plus a battery of bit-to-nat lemmas) and calls
//      `mul_bits_be`.  Stubbed with its `ensures` verbatim and body
//      `assume(false)`; the postcondition — multiplication by the *unreduced*
//      scalar value — is trusted as an axiom and is precisely what
//      `mul_clamped` needs.
//
//      The accompanying `MulSpecImpl` (from arithm_trait_specs.rs) tells Verus
//      the operator's precondition: the point is valid and the scalar's MSB is
//      clear.  `obeys_mul_spec()` is `false`, so the operator's built-in
//      `ensures` is vacuous and the `fn mul` `ensures` above carries the real
//      postcondition.
// ============================================================

impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &MontgomeryPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        is_valid_montgomery_point(*self) && rhs.bytes[31] <= 127
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> MontgomeryPoint {
        arbitrary()
    }
}

impl core::ops::Mul<&Scalar> for &MontgomeryPoint {
    type Output = MontgomeryPoint;

    /// Given `self` = u₀(P) and a `Scalar` n, return u₀([n]P).
    /// TRUSTED AXIOM (body `assume(false)`).
    fn mul(self, scalar: &Scalar) -> (result: MontgomeryPoint)
        ensures
            ({
                // The canonical Montgomery lift P of this u-coordinate is
                // multiplied by the UNREDUCED scalar value.
                let P = canonical_montgomery_lift(montgomery_point_as_nat(*self));
                let n_unreduced = scalar_as_nat(scalar);
                let R = montgomery_scalar_mul(P, n_unreduced);
                montgomery_point_as_nat(result) == u_coordinate(R)
            }),
    {
        assume(false);
        MontgomeryPoint([0u8; 32])
    }
}

// ============================================================
// § 10  Target function — `mul_clamped`  (montgomery.rs:408–449)
//
//       The benchmark target, body and proof block reproduced verbatim.  This
//       is the sole real verification target in the file: it chains
//       `clamp_integer.ensures` with the `*` operator's `ensures` to discharge
//       the correctness postcondition.
// ============================================================

impl MontgomeryPoint {
    /// Multiply this point by `clamp_integer(bytes)`. For a description of clamping, see
    /// [`clamp_integer`].
    pub fn mul_clamped(self, bytes: [u8; 32]) -> (result: Self)
        requires
            is_valid_montgomery_point(self),
        ensures/* VERIFICATION NOTE: Result represents [n]self where n is the clamped integer value
      The corresponding scalar is not reduced modulo the group order. */

            ({
                let P = canonical_montgomery_lift(montgomery_point_as_nat(self));
                let clamped_bytes = spec_clamp_integer(bytes);
                let n = u8_32_as_nat(&clamped_bytes);
                let R = montgomery_scalar_mul(P, n);
                montgomery_point_as_nat(result) == u_coordinate(R)
            }),
    {
        // We have to construct a Scalar that is not reduced mod l, which breaks scalar invariant
        // #2. But #2 is not necessary for correctness of variable-base multiplication. All that
        // needs to hold is invariant #1, i.e., the scalar is less than 2^255. This is guaranteed
        // by clamping.
        // Further, we don't do any reduction or arithmetic with this clamped value, so there's no
        // issues arising from the fact that the curve point is not necessarily in the prime-order
        // subgroup.
        /* ORIGINAL CODE: let s = Scalar { bytes: clamp_integer(bytes) }; s * self
           Split to keep `clamped` for proof blocks; uses &self * &s for Verus postcondition. */
        let clamped = clamp_integer(bytes);
        let s = Scalar { bytes: clamped };
        let result = &self * &s;
        proof {
            // Prove the postcondition using:
            // - `clamp_integer` ensures `clamped == spec_clamp_integer(bytes)`
            // - `&MontgomeryPoint * &Scalar` ensures multiplication by `scalar_as_nat(&s)`
            assert(clamped == spec_clamp_integer(bytes));
            assert(scalar_as_nat(&s) == u8_32_as_nat(&spec_clamp_integer(bytes)));
            assert({
                let P = canonical_montgomery_lift(montgomery_point_as_nat(self));
                let clamped_bytes = spec_clamp_integer(bytes);
                let n = u8_32_as_nat(&clamped_bytes);
                let R = montgomery_scalar_mul(P, n);
                montgomery_point_as_nat(result) == u_coordinate(R)
            });
        }
        result
    }
}

} // verus!

fn main() {}
