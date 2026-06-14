// =============================================================================
// Benchmark B2 — `Scalar::from_bytes_mod_order_wide`  (VARIANT: upstream-faithful)
// =============================================================================
//
// VARIANT of b2_minimal.rs.  Same reachable set, but
// each retained spec/lemma/proof was converged toward the pinned dalek-lite
// commit (3f3443e) as closely as possible: upstream `scalar_as_nat` /
// `u8_32_as_group_canonical`, upstream `is_canonical_scalar`, `u8_32_as_nat`
// `pow2(i*8)` form, `is_uniform_bytes(&[u8])`, the `calc!`-based
// `lemma_scalar52_lt_pow2_256_if_canonical`, the verbatim
// `lemma_group_order_bound` body (minus the two `constants::L` bridge calls,
// inapplicable here), and the verbatim 4-call `from_bytes_mod_order_wide`
// proof block.  The sibling `b2_minimal.rs` is the
// plain "verus.rs minus unreachable functions" form (no convergence).
// Both verify (10 verified, 0 errors).
// =============================================================================
//
// Reduces a 64-byte (512-bit) little-endian integer modulo the Ed25519/Ristretto
// group order ℓ = 2^252 + 27742317777372353535851937790883648493, producing a
// canonical 32-byte scalar.  Used in EdDSA signing to reduce the SHA-512 hash
// H(R ‖ A ‖ M) to a nonce scalar r before computing the response s = r + H·a.
//
// Postconditions:
//   (1) Correctness  — scalar_as_canonical(&result) == group_canonical(bytes_seq_as_nat(input@))
//                      The output equals the input reduced mod ℓ.
//
//   (2) Canonicality — is_canonical_scalar(&result)
//                      The output is the unique representative in [0, ℓ) with
//                      high bit clear (bytes[31] ≤ 127).  Absent this, two
//                      distinct byte strings represent the same scalar, enabling
//                      signature malleability (CVE in OpenSSL and tinyssh,
//                      RFC 8032 §5.1.7).
//
//   (3) Uniformity   — is_uniform_bytes(input) ==> is_uniform_scalar(&result)
//                      A uniform 512-bit input produces a statistically uniform
//                      scalar; bias ≤ ℓ/2^512 ≈ 2^{-259}.  Required for nonce
//                      secrecy — a biased nonce leaks the private key
//                      (cf. ECDSA PS3 attack).
//
// Source: dalek-lite https://github.com/Beneficial-AI-Foundation/dalek-lite
//
// Assembled from:
//   curve25519-dalek/src/scalar.rs                          (target function, pack)
//   curve25519-dalek/src/backend/serial/u64/scalar.rs       (from_bytes_wide)
//   curve25519-dalek/src/specs/core_specs.rs                (byte-to-nat specs)
//   curve25519-dalek/src/specs/scalar52_specs.rs            (limb specs, group order)
//   curve25519-dalek/src/specs/scalar_specs.rs              (Scalar specs)
//   curve25519-dalek/src/specs/proba_specs.rs               (uniformity axiom)
//   curve25519-dalek/src/lemmas/scalar_lemmas.rs            (group_order lemmas)
//
// SCOPE: this file is the *minimal* standalone benchmark for translating the
// composition proof in `from_bytes_mod_order_wide`.  Only the specs, stubs and
// lemmas reachable from that proof's call graph are kept.  The two callees
// (`from_bytes_wide`, `pack`) are stubbed with `assume(false)` — their
// postconditions are trusted as axioms; their real bodies live in
// backend/serial/u64/scalar.rs.  The Montgomery-reduction machinery
// (mul_internal / montgomery_reduce / *_bounds specs) and the byte-loading
// specs (load8_at / word64_from_bytes) are deliberately omitted: nothing in the
// composition proof reaches them.
// =============================================================================

#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;   // lemma_small_mod, lemma_mod_bound
use vstd::arithmetic::power2::*;
use vstd::calc;                     // calc! macro (lemma_scalar52_lt_pow2_256_if_canonical)
use vstd::prelude::*;

verus! {

// ============================================================
// § 1  Core specs  (specs/core_specs.rs)
// ============================================================

/// Little-endian natural value of a byte sequence.
pub open spec fn bytes_seq_as_nat(bytes: Seq<u8>) -> nat
    decreases bytes.len(),
{
    if bytes.len() == 0 { 0 } else { (bytes[0] as nat) + pow2(8) * bytes_seq_as_nat(bytes.skip(1)) }
}

/// Little-endian natural value of a fixed 32-byte array (explicit 32-term form for SMT).
#[verusfmt::skip]
pub open spec fn u8_32_as_nat(bytes: &[u8; 32]) -> nat {
    (bytes[ 0] as nat) * pow2( 0 * 8) +
    (bytes[ 1] as nat) * pow2( 1 * 8) +
    (bytes[ 2] as nat) * pow2( 2 * 8) +
    (bytes[ 3] as nat) * pow2( 3 * 8) +
    (bytes[ 4] as nat) * pow2( 4 * 8) +
    (bytes[ 5] as nat) * pow2( 5 * 8) +
    (bytes[ 6] as nat) * pow2( 6 * 8) +
    (bytes[ 7] as nat) * pow2( 7 * 8) +
    (bytes[ 8] as nat) * pow2( 8 * 8) +
    (bytes[ 9] as nat) * pow2( 9 * 8) +
    (bytes[10] as nat) * pow2(10 * 8) +
    (bytes[11] as nat) * pow2(11 * 8) +
    (bytes[12] as nat) * pow2(12 * 8) +
    (bytes[13] as nat) * pow2(13 * 8) +
    (bytes[14] as nat) * pow2(14 * 8) +
    (bytes[15] as nat) * pow2(15 * 8) +
    (bytes[16] as nat) * pow2(16 * 8) +
    (bytes[17] as nat) * pow2(17 * 8) +
    (bytes[18] as nat) * pow2(18 * 8) +
    (bytes[19] as nat) * pow2(19 * 8) +
    (bytes[20] as nat) * pow2(20 * 8) +
    (bytes[21] as nat) * pow2(21 * 8) +
    (bytes[22] as nat) * pow2(22 * 8) +
    (bytes[23] as nat) * pow2(23 * 8) +
    (bytes[24] as nat) * pow2(24 * 8) +
    (bytes[25] as nat) * pow2(25 * 8) +
    (bytes[26] as nat) * pow2(26 * 8) +
    (bytes[27] as nat) * pow2(27 * 8) +
    (bytes[28] as nat) * pow2(28 * 8) +
    (bytes[29] as nat) * pow2(29 * 8) +
    (bytes[30] as nat) * pow2(30 * 8) +
    (bytes[31] as nat) * pow2(31 * 8)
}

// ============================================================
// § 2  Scalar52 specs  (specs/scalar52_specs.rs)
// ============================================================

/// Group order ℓ = 2^252 + 27742317777372353535851937790883648493
pub open spec fn group_order() -> nat {
    pow2(252) + 27742317777372353535851937790883648493nat
}

/// Canonical reduction mod ℓ.
pub open spec fn group_canonical(n: nat) -> nat { n % group_order() }

pub open spec fn limbs52_as_nat(limbs: &[u64]) -> nat {
    seq_as_nat_52(limbs@.map(|i, x| x as nat))
}

pub open spec fn seq_as_nat_52(limbs: Seq<nat>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 { 0 }
    else { limbs[0] + seq_as_nat_52(limbs.subrange(1, limbs.len() as int)) * pow2(52) }
}

pub open spec fn scalar52_as_nat(s: &Scalar52) -> nat { limbs52_as_nat(&s.limbs) }

/// All limbs < 2^52.
pub open spec fn limbs_bounded(s: &Scalar52) -> bool {
    forall|i: int| 0 <= i < 5 ==> s.limbs[i] < (1u64 << 52)
}

/// Limbs bounded and value < ℓ.
pub open spec fn is_canonical_scalar52(s: &Scalar52) -> bool {
    limbs_bounded(s) && scalar52_as_nat(s) < group_order()
}

// ============================================================
// § 3  Scalar / uniformity specs  (scalar.rs, proba_specs.rs)
// ============================================================

pub open spec fn scalar_as_nat(s: &Scalar) -> nat {
    u8_32_as_nat(&s.bytes)
}

pub open spec fn u8_32_as_group_canonical(bytes: [u8; 32]) -> nat {
    group_canonical(u8_32_as_nat(&bytes))
}

/// Returns the scalar value reduced modulo group order.
pub open spec fn scalar_as_canonical(s: &Scalar) -> nat {
    u8_32_as_group_canonical(s.bytes)
}

/// Checks if a Scalar satisfies the canonical representation invariants:
/// - Invariant #1: High bit (bit 255) is clear, ensuring s < 2^255
/// - Invariant #2: Scalar is reduced modulo group order, i.e., s < ℓ
pub open spec fn is_canonical_scalar(s: &Scalar) -> bool {
    // Invariant #2: Scalar is reduced (< group order)
    u8_32_as_nat(&s.bytes)
        < group_order()
    // Invariant #1: High bit is clear (< 2^255)
     && s.bytes[31] <= 127
}

/// Uniform distribution predicate for a byte slice.
pub uninterp spec fn is_uniform_bytes(bytes: &[u8]) -> bool;

/// Uniform distribution predicate for a scalar.
pub uninterp spec fn is_uniform_scalar(scalar: &Scalar) -> bool;

// ============================================================
// § 4  Types
// ============================================================

/// The `Scalar52` struct: element of ℤ/ℓℤ as 5 × 52-bit limbs.
#[derive(Copy, Clone)]
pub struct Scalar52 {
    pub limbs: [u64; 5],
}

/// The `Scalar` struct: canonical 32-byte little-endian encoding.
#[derive(Copy, Clone, Hash)]
pub struct Scalar {
    /// `bytes` is a little-endian byte encoding of an integer representing a scalar modulo the
    /// group order.
    ///
    /// # Invariant #1
    ///
    /// The integer representing this scalar is less than \\(2\^{255}\\). That is, the most
    /// significant bit of `bytes[31]` is 0.
    ///
    /// This is required for `EdwardsPoint` variable- and fixed-base multiplication, because most
    /// integers above 2^255 are unrepresentable in our radix-16 NAF (see [`Self::as_radix_16`]).
    /// The invariant is also required because our `MontgomeryPoint` multiplication assumes the MSB
    /// is 0 (see `MontgomeryPoint::mul`).
    ///
    /// # Invariant #2 (weak)
    ///
    /// The integer representing this scalar is less than \\(2\^{255} - 19 \\), i.e., it represents
    /// a canonical representative of an element of \\( \mathbb Z / \ell\mathbb Z \\). This is
    /// stronger than invariant #1. It also sometimes has to be broken.
    ///
    /// This invariant is deliberately broken in the implementation of `EdwardsPoint::{mul_clamped,
    /// mul_base_clamped}`, `MontgomeryPoint::{mul_clamped, mul_base_clamped}`, and
    /// `BasepointTable::mul_base_clamped`. This is not an issue though. As mentioned above,
    /// scalar-point multiplication is defined for any choice of `bytes` that satisfies invariant
    /// #1. Since clamping guarantees invariant #1 is satisfied, these operations are well defined.
    ///
    /// Note: Scalar-point mult is the _only_ thing you can do safely with an unreduced scalar.
    /// Scalar-scalar addition and subtraction are NOT correct when using unreduced scalars.
    /// Multiplication is correct, but this is only due to a quirk of our implementation, and not
    /// guaranteed to hold in general in the future.
    ///
    /// Note: It is not possible to construct an unreduced `Scalar` from the public API unless the
    /// `legacy_compatibility` is enabled (thus making `Scalar::from_bits` public). Thus, for all
    /// public non-legacy uses, invariant #2
    /// always holds.
    ///
    /* <VERIFICATION NOTE>
    Changed from pub(crate) to pub
    </VERIFICATION NOTE> */
    pub bytes: [u8; 32],/* <ORIGINAL CODE>
    pub(crate) bytes: [u8; 32],
    </ORIGINAL CODE> */
}

/// Type alias used in scalar.rs (scalar.rs:214).
type UnpackedScalar = Scalar52;

// ============================================================
// § 5  Stubbed callees  (backend/serial/u64/scalar.rs)
//      Bodies are `assume(false)`; postconditions trusted as axioms.
// ============================================================

impl Scalar52 {

    /// Reduce a 512-bit little-endian integer mod ℓ into a Scalar52.
    /// Body stubbed — real proof is ~300 lines in backend/serial/u64/scalar.rs.
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> (s: Scalar52)
        ensures
            is_canonical_scalar52(&s),
            scalar52_as_nat(&s) == group_canonical(bytes_seq_as_nat(bytes@)),
    { assume(false); Scalar52 { limbs: [0u64; 5] } }

} // impl Scalar52

impl UnpackedScalar {
    /// Pack the limbs of this `UnpackedScalar` into a `Scalar`.
    /// Body stubbed — real proof lives in `scalar.rs` (impl `UnpackedScalar`),
    /// using `self.as_bytes()` + `lemma_five_limbs_equals_to_nat`.
    fn pack(&self) -> (result: Scalar)
        requires
            limbs_bounded(self),
        ensures
            u8_32_as_nat(&result.bytes) == scalar52_as_nat(self) % pow2(256),
            scalar52_as_nat(self) < group_order() ==> is_canonical_scalar(&result),
    { assume(false); Scalar { bytes: [0u8; 32] } }
}

// ============================================================
// § 6  Proof lemmas about group_order  (lemmas/scalar_lemmas.rs)
//
//      lemma_small_mod / lemma_mod_bound come from vstd::arithmetic::div_mod
//      and are available via the `use` import above — no local definition needed.
// ============================================================

/// group_order() < 2^255
///
/// Note: the original repo opens with two bridging calls not needed here:
///   `lemma_l_equals_group_order()` — connects `constants::L` (a Scalar52 limb struct)
///                                    to the `group_order()` spec function.
///   `lemma_pow252()`              — establishes a concrete value for `pow2(252)`
///                                    relative to that same struct.
/// Both are unnecessary here because `group_order()` is defined directly as
/// `pow2(252) + constant` with no concrete struct to bridge.
pub proof fn lemma_group_order_bound()
    ensures
        group_order() < pow2(255),
{
    // group_order = 2^252 + 27742317777372353535851937790883648493
    // (upstream opens with `lemma_l_equals_group_order(); lemma_pow252();`
    //  here, omitted — no `constants::L` struct to bridge; see note above.)

    // First compare the constant to the concrete numeral for 2^126
    assert(27742317777372353535851937790883648493nat < 0x40000000000000000000000000000000)
        by (compute_only);

    // Establish pow2(126) == 0x4000...0000 so we can rewrite the bound
    assert(pow2(63) == 0x8000000000000000) by {
        lemma2_to64_rest();
    };
    lemma_pow2_adds(63, 63);
    assert(pow2(126) == 0x40000000000000000000000000000000);

    // Hence the constant < 2^126 < 2^252
    assert(27742317777372353535851937790883648493nat < pow2(126));
    lemma_pow2_strictly_increases(126, 252);
    assert(27742317777372353535851937790883648493nat < pow2(252));

    // Therefore group_order < 2^252 + 2^252 = 2^253
    assert(group_order() == pow2(252) + 27742317777372353535851937790883648493nat);
    assert(group_order() < pow2(252) + pow2(252));

    // 2^252 + 2^252 = 2^253
    assert(pow2(252) + pow2(252) == pow2(253)) by {
        lemma_pow2_adds(1, 252);
        lemma2_to64();
    }

    // 2^253 < 2^255
    lemma_pow2_strictly_increases(253, 255);
    assert(group_order() < pow2(255));
}

/// group_order() < 2^256
pub proof fn lemma_group_order_smaller_than_pow256()
    ensures group_order() < pow2(256),
{
    lemma_group_order_bound();
    lemma_pow2_strictly_increases(255, 256);
}

/// If an UnpackedScalar (Scalar52) is canonical (< group_order), then it is < 2^256.
pub proof fn lemma_scalar52_lt_pow2_256_if_canonical(a: &Scalar52)
    requires
        limbs_bounded(a),
        scalar52_as_nat(&a) < group_order(),
    ensures
        scalar52_as_nat(&a) < pow2(256),
{
    // group_order() < 2^255
    lemma_group_order_bound();

    // Chain: scalar52_as_nat(a) < group_order() < 2^255 < 2^256
    calc! {
        (<)
        scalar52_as_nat(&a); {  /* from precondition */
        }
        group_order(); {  /* from lemma_group_order_bound */
        }
        pow2(255); {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(255, 256);
        }
        pow2(256);
    }
}

// ============================================================
// § 7  Uniformity axiom  (proba_specs.rs)
// ============================================================

/// Reducing 512 uniform bits mod ℓ produces a nearly-uniform scalar.
/// Statistical distance ≤ ℓ/2^512 ≈ 2^{-259} (cryptographically negligible).
pub proof fn axiom_uniform_mod_reduction(input: &[u8; 64], result: &Scalar)
    requires
        scalar_as_nat(result) == bytes_seq_as_nat(input@) % group_order(),
    ensures
        is_uniform_bytes(input) ==> is_uniform_scalar(result),
{
    admit();
}

// ============================================================
// § 8  Target function  (scalar.rs:300–348)
// ============================================================

impl Scalar {
    /// Reduce a 512-bit little-endian integer mod ℓ into a canonical Scalar.
    ///
    /// Used in EdDSA signing to reduce the SHA-512 hash of (R ‖ A ‖ M) to a
    /// nonce scalar r.  Absent canonicality caused malleability bugs in OpenSSL
    /// and tinyssh (RFC 8032 §5.1.7).  The uniformity postcondition ensures
    /// nonces derived from uniform randomness cannot leak the private key.
    pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> (result: Scalar)
        ensures
            scalar_as_canonical(&result) == group_canonical(bytes_seq_as_nat(input@)),
            is_canonical_scalar(&result),
            is_uniform_bytes(input) ==> is_uniform_scalar(&result),
    {
        let unpacked = UnpackedScalar::from_bytes_wide(input);
        let result   = unpacked.pack();

        proof {
            // from_bytes_wide postconditions:
            // - limbs_bounded(&unpacked)
            // - scalar52_as_nat(&unpacked) == bytes_seq_as_nat(input@) % group_order()
            // - scalar52_as_nat(&unpacked) < group_order()
            // pack() postconditions:
            // - u8_32_as_nat(&result.bytes) == scalar52_as_nat(&unpacked) % pow2(256)
            // - scalar52_as_nat(&unpacked) < group_order() ==> is_canonical_scalar(&result)
            // Since scalar52_as_nat(&unpacked) < group_order() < pow2(256),
            // we have scalar52_as_nat(&unpacked) % pow2(256) == scalar52_as_nat(&unpacked)
            lemma_group_order_smaller_than_pow256();
            lemma_small_mod(scalar52_as_nat(&unpacked), pow2(256));

            // Therefore u8_32_as_nat(&result.bytes) == scalar52_as_nat(&unpacked)
            //                                        == bytes_seq_as_nat(input@) % group_order()
            // Since bytes_seq_as_nat(input@) % group_order() < group_order(),
            // u8_32_as_nat(&result.bytes) % group_order() == u8_32_as_nat(&result.bytes)
            //                                              == bytes_seq_as_nat(input@) % group_order()
            lemma_mod_bound(bytes_seq_as_nat(input@) as int, group_order() as int);
            lemma_small_mod(u8_32_as_nat(&result.bytes), group_order());

            // Uniformity: reducing 512 uniform bits mod L (≈2^253) produces nearly uniform scalar.
            // Bias: at most L/2^512 ≈ 2^-259 statistical distance (cryptographically negligible).
            axiom_uniform_mod_reduction(input, &result);
        }

        result
    }
}

} // verus!

fn main() {}
