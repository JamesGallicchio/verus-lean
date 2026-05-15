// SHA-256 inner compression function — variant of `sha256_compact.rs`
// that rewrites `compress` to use an indexed `for k in 0..blocks.len()`
// loop instead of the upstream `for block in blocks.iter()` form.
//
// Why this variant exists:
//   The upstream-faithful version (sha256_compact.rs) lowers
//   `for block in blocks.iter()` to a Verus iterator-protocol expansion.
//   That expansion currently leaves several symbols undefined in the
//   Boole output (e.g. `Iter_Traits_Iterator_Iterator_next`,
//   `Pervasive_ghost_decrease`, `Pervasive_ghost_invariant`,
//   `Std_specs_Slice_spec_slice_iter`, `Option_option..isOption_option_Some`),
//   plus undeclared loop locals (`VERUS_iter`, `VERUS_exec_iter`,
//   `VERUS_ghost_iter`, ...). Indexed `for k in 0..blocks.len()` lowers
//   cleanly through the for-range recovery path with the existing
//   array-as-Map model, so this variant exercises everything except the
//   iterator-protocol gap.
//
// Difference from sha256_compact.rs:
//   - `compress` body is rewritten from
//         for block in blocks.iter() {
//             compress_u32(state, to_u32s(block));
//         }
//     to the equivalent indexed form
//         for k in 0..blocks.len() {
//             compress_u32(state, to_u32s(&blocks[k]));
//         }
//     The two are semantically equivalent ("for every block index k, …");
//     the indexed form sidesteps the iterator-protocol scaffolding gap.

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;
use vstd::prelude::*;

verus! {

pub const K32: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

#[inline]
fn rotate_right(x: u32, n: u32) -> u32
    requires
        1 <= n < 32,
{
    (x >> n) | (x << (32 - n))
}

fn to_u32s(block: &[u8; 64]) -> [u32; 16] {
    let mut res: [u32; 16] = [0u32; 16];
    for i in 0..16 {
        let j = i * 4;
        res[i] = ((block[j] as u32) << 24)
            | ((block[j + 1] as u32) << 16)
            | ((block[j + 2] as u32) << 8)
            | (block[j + 3] as u32);
    }
    res
}

fn compress_u32(state: &mut [u32; 8], mut block: [u32; 16]) {
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    for i in 0..64 {
        let w = if i < 16 {
            block[i]
        } else {
            let w15 = block[(i - 15) % 16];
            let s0 = rotate_right(w15, 7) ^ rotate_right(w15, 18) ^ (w15 >> 3);
            let w2 = block[(i - 2) % 16];
            let s1 = rotate_right(w2, 17) ^ rotate_right(w2, 19) ^ (w2 >> 10);
            let new_w = block[(i - 16) % 16]
                .wrapping_add(s0)
                .wrapping_add(block[(i - 7) % 16])
                .wrapping_add(s1);
            block[i % 16] = new_w;
            new_w
        };

        let s1 = rotate_right(e, 6) ^ rotate_right(e, 11) ^ rotate_right(e, 25);
        let ch = (e & f) ^ ((!e) & g);
        let t1 = s1
            .wrapping_add(ch)
            .wrapping_add(K32[i])
            .wrapping_add(w)
            .wrapping_add(h);
        let s0 = rotate_right(a, 2) ^ rotate_right(a, 13) ^ rotate_right(a, 22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

pub fn compress(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
    for k in 0..blocks.len() {
        compress_u32(state, to_u32s(&blocks[k]));
    }
}

fn main() {}

} // verus!
