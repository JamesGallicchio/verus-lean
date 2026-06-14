// =============================================================================
// Benchmark B2 — `Scalar::from_bytes_mod_order_wide`
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
//   curve25519-dalek/src/scalar.rs                          (target function)
//   curve25519-dalek/src/backend/serial/u64/scalar.rs       (from_bytes_wide, pack)
//   curve25519-dalek/src/specs/core_specs.rs                (byte-to-nat specs)
//   curve25519-dalek/src/specs/scalar52_specs.rs            (limb specs, group order)
//   curve25519-dalek/src/specs/proba_specs.rs               (uniformity axiom)
//
// MINIMAL: only the specs, stubs and lemmas reachable from the
// `from_bytes_mod_order_wide` composition proof are kept — the Montgomery
// machinery, byte-loading specs, and unused lemma stubs from the full
// benchmark are removed.  All callee bodies are stubbed with `assume(false)`
// — their postconditions are trusted as axioms.  The only real verification
// target is the proof chain in `from_bytes_mod_order_wide` (bottom of file),
// which derives the three postconditions above by chaining
// `from_bytes_wide.ensures` and `pack.ensures`.
// =============================================================================

#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;   // lemma_small_mod, lemma_mod_bound
use vstd::arithmetic::power2::*;
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
// § 2  Scalar52 specs  (specs/scalar52_specs.rs)
// ============================================================

/// Group order ℓ = 2^252 + 27742317777372353535851937790883648493
pub open spec fn group_order() -> nat {
    pow2(252) + 27742317777372353535851937790883648493nat
}

/// Canonical reduction mod ℓ.
pub open spec fn group_canonical(n: nat) -> nat { n % group_order() }

pub open spec fn limbs52_as_nat(limbs: &[u64]) -> nat {
    seq_as_nat_52(limbs@.map(|_i, x: u64| x as nat))
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

/// Bytes[31] ≤ 127 and value < ℓ.
pub open spec fn is_canonical_scalar(s: &Scalar) -> bool {
    u8_32_as_nat(&s.bytes) < group_order() && s.bytes[31] <= 127
}

pub open spec fn scalar_as_canonical(s: &Scalar) -> nat {
    group_canonical(u8_32_as_nat(&s.bytes))
}

/// Uninterpreted: input bytes are uniformly distributed.
pub uninterp spec fn is_uniform_bytes(bytes: &[u8; 64]) -> bool;

/// Uninterpreted: scalar is uniformly distributed over [0, ℓ).
pub uninterp spec fn is_uniform_scalar(s: &Scalar) -> bool;

// ============================================================
// § 4  Types
// ============================================================

/// The `Scalar52` struct: element of ℤ/ℓℤ as 5 × 52-bit limbs.
#[derive(Copy, Clone)]
pub struct Scalar52 {
    pub limbs: [u64; 5],
}

/// The `Scalar` struct: canonical 32-byte little-endian encoding.
pub struct Scalar {
    pub bytes: [u8; 32],
}

/// Type alias used in scalar.rs (scalar.rs:214).
type UnpackedScalar = Scalar52;

// ============================================================
// § 5  Stubbed callees: from_bytes_wide, pack
//      (backend/serial/u64/scalar.rs — bodies `assume(false)`,
//       postconditions trusted as axioms)
// ============================================================

impl Scalar52 {

    /// Reduce a 512-bit little-endian integer mod ℓ into a Scalar52.
    /// Body stubbed — real proof is ~300 lines in backend/serial/u64/scalar.rs.
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> (s: Scalar52)
        ensures
            is_canonical_scalar52(&s),
            scalar52_as_nat(&s) == group_canonical(bytes_seq_as_nat(bytes@)),
    { assume(false); Scalar52 { limbs: [0u64; 5] } }

    /// Convert a canonical Scalar52 into a Scalar.
    /// Body stubbed — real proof in backend/serial/u64/scalar.rs.
    pub fn pack(&self) -> (result: Scalar)
        requires limbs_bounded(self),
        ensures
            u8_32_as_nat(&result.bytes) == scalar52_as_nat(self) % pow2(256),
            scalar52_as_nat(self) < group_order() ==> is_canonical_scalar(&result),
    { assume(false); Scalar { bytes: [0u8; 32] } }

} // impl Scalar52

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
    ensures group_order() < pow2(255),
{
    assert(27742317777372353535851937790883648493nat < 0x40000000000000000000000000000000)
        by (compute_only);
    assert(pow2(63) == 0x8000000000000000) by { lemma2_to64_rest(); }
    lemma_pow2_adds(63, 63);
    assert(pow2(126) == 0x40000000000000000000000000000000);
    assert(27742317777372353535851937790883648493nat < pow2(126));
    lemma_pow2_strictly_increases(126, 252);
    assert(group_order() < pow2(252) + pow2(252));
    assert(pow2(252) + pow2(252) == pow2(253)) by {
        lemma_pow2_adds(1, 252); lemma2_to64();
    }
    lemma_pow2_strictly_increases(253, 255);
}

/// group_order() < 2^256
pub proof fn lemma_group_order_smaller_than_pow256()
    ensures group_order() < pow2(256),
{
    lemma_group_order_bound();
    lemma_pow2_strictly_increases(255, 256);
}

/// If scalar52_as_nat(a) < group_order() then scalar52_as_nat(a) < 2^256
pub proof fn lemma_scalar52_lt_pow2_256_if_canonical(a: &Scalar52)
    requires limbs_bounded(a), scalar52_as_nat(a) < group_order(),
    ensures  scalar52_as_nat(a) < pow2(256),
{
    lemma_group_order_bound();
    lemma_pow2_strictly_increases(255, 256);
    // scalar52_as_nat(a) < group_order() < 2^255 < 2^256
}

// ============================================================
// § 7  Uniformity axiom  (proba_specs.rs)
// ============================================================

/// Reducing 512 uniform bits mod ℓ produces a nearly-uniform scalar.
/// Statistical distance ≤ ℓ/2^512 ≈ 2^{-259} (cryptographically negligible).
pub proof fn axiom_uniform_mod_reduction(input: &[u8; 64], result: &Scalar)
    requires scalar_as_canonical(result) == bytes_seq_as_nat(input@) % group_order(),
    ensures  is_uniform_bytes(input) ==> is_uniform_scalar(result),
{ admit() }

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
            // Step 1: scalar52_as_nat(&unpacked) < pow2(256)
            //   from_bytes_wide gives is_canonical_scalar52 => value < group_order()
            //   group_order() < pow2(256) by lemma below
            lemma_group_order_smaller_than_pow256();
            lemma_scalar52_lt_pow2_256_if_canonical(&unpacked);

            // Step 2: pack's mod-2^256 is a no-op (value < pow2(256))
            //   => u8_32_as_nat(&result.bytes) == scalar52_as_nat(&unpacked)
            lemma_small_mod(scalar52_as_nat(&unpacked), pow2(256));

            // Step 3: bytes_seq_as_nat(input@) % group_order() < group_order()
            //   => scalar52_as_nat(&unpacked) < group_order()  (already known, but needed for lemma_small_mod below)
            lemma_mod_bound(bytes_seq_as_nat(input@) as int, group_order() as int);

            // Step 4: u8_32_as_nat(&result.bytes) < group_order()
            //   => scalar_as_canonical(&result) == u8_32_as_nat(&result.bytes) == group_canonical(input)
            lemma_small_mod(u8_32_as_nat(&result.bytes), group_order());

            // Step 5: uniformity
            axiom_uniform_mod_reduction(input, &result);
        }

        result
    }
}

} // verus!

fn main() {}
