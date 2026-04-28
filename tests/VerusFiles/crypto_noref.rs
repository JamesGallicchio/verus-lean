// A variant of `crypto.rs` that avoids `&[u8]` references but keeps the
// closures `|kv: (u8, u8)| kv.0 ^ kv.1` inside `encrypt_spec` /
// `decrypt_spec`. Exec-side `encrypt` / `decrypt` take `Vec<u8>` by
// value instead of borrowing slices.
//
// This is the closure-bearing variant; `crypto_axiomatized.rs` replaces
// the closures with an uninterpreted axiomatized `xor_map`, and
// `crypto_rec.rs` replaces them with a concrete recursive definition.
use vstd::prelude::*;

verus! {

spec fn encrypt_spec(key: Seq<u8>, text: Seq<u8>) -> Seq<u8> {
    key.zip_with(text).map_values(|kv: (u8, u8)| kv.0 ^ kv.1)
}

spec fn decrypt_spec(key: Seq<u8>, cypher: Seq<u8>) -> Seq<u8> {
    key.zip_with(cypher).map_values(|kv: (u8, u8)| kv.0 ^ kv.1)
}

proof fn decrypt_encrypt(key: Seq<u8>, text: Seq<u8>)
    requires
        key.len() == text.len(),
    ensures
        decrypt_spec(key, encrypt_spec(key, text)) == text,
{
    // need the following fact about xor:
    assert(forall|a: u8, b: u8| a ^ (a ^ b) == b) by(bit_vector);
}

fn encrypt(key: Vec<u8>, text: Vec<u8>) -> (res: Vec<u8>)
    requires
        key.len() == text.len(),
    ensures
        encrypt_spec(key@, text@) == res@,
{
    let mut res = vec![0; text.len()];

    for i in 0..text.len()
        invariant
            0 <= i <= text.len(),
            text.len() == key.len(),
            text.len() == res.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == key[j] ^ text[j],
    {
        res[i] = key[i] ^ text[i];
    }

    res
}

fn decrypt(key: Vec<u8>, text: Vec<u8>) -> (res: Vec<u8>)
    requires
        key.len() == text.len(),
    ensures
        decrypt_spec(key@, text@) == res@,
{
    let mut res = vec![0; text.len()];

    for i in 0..text.len()
        invariant
            0 <= i <= text.len(),
            text.len() == key.len(),
            text.len() == res.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == key[j] ^ text[j],
    {
        res[i] = key[i] ^ text[i];
    }

    res
}

fn test() {
    let key = vec![1, 2, 3];
    let text = vec![4, 5, 6];

    let encrypt = encrypt(key.clone(), text);
    let decrypt = decrypt(key.clone(), encrypt);

    assert(decrypt@ == text@) by { decrypt_encrypt(key@, text@) };
}

fn main() {
}
} // verus!
