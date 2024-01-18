import VerusLean
import LeanSlides

#slides Intro /-!
# Lean Verus Interface

### What is Verus?

- Built on top of Rust
- Assertion-style verification
- SMT backend to discharge obligations
- Improves on prior work:
  - Rust already adopted in industry
  - Much smaller SMT queries
  - Nicer utilities + tooling in general?

### Verus "Semi-Automation"

- SMT solvers notoriously unstable
- Verus disables non-linear arithmetic (NLA)
  - Heuristic-based, very unstable
- Disabling substantially improves stability
- Users still need to prove NLA goals
- Verus provides a library of NLA lemmas users can explicitly call

### The Problem

- Verus provides a library of NLA lemmas
  - Need NLA enabled for SMT to discharge
  - NLA enabled for these lemmas STILL unstable
- Want a more reliable verification story

[github.com/ahuoguo/verus/pull/3]()
-/

/-
```rust
// This warning is funny:

/* WARNING: Think three times before adding to this file, as nonlinear
verification is highly unstable! */

verus! {

/* multiplying two positive integers will result in a positive integer */
#[verifier(nonlinear)]
pub proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
{}

/* Integral Domain */
/* multiplying two nonzero integers will never result in 0 as the poduct */
#[verifier(nonlinear)]
pub proof fn lemma_mul_nonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
{}

/* multiplication is associative */
#[verifier(nonlinear)]
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
{}

/* multiplying by a positive integer preserves inequality */
#[verifier(nonlinear)]
pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires
        x < y,
        z > 0
    ensures
        x * z < y * z
{}

#[verifier(nonlinear)]
pub proof fn lemma_fundamental_div_mod(x:int, d:int)
    requires d != 0
    ensures  x == d * (x / d) + (x % d)
{}
}

//--------------------------------------------------------------/
// Examples provable without NLA but Lean might still make sense
//--------------------------------------------------------------/

pub open spec fn div_auto(n: int) -> bool
    recommends n > 0
{
    &&& mod_auto(n)
    &&& (n / n == -((-n) / n) == 1)
    &&& forall |x: int| 0 <= x < n <==> #[trigger](x / n) == 0
    &&& (forall |x: int, y: int| #![trigger ((x + y) / n)]
         {let z = (x % n) + (y % n);
         (  (0 <= z < n && ((x + y) / n) == x / n + y / n)
             || (n <= z < n + n && ((x + y) / n) == x / n + y / n + 1))})
    &&& (forall |x: int, y: int| #![trigger ((x - y) / n)]
        {let z = (x % n) - (y % n);
        (  (0 <= z < n && ((x - y) / n) == x / n - y / n)
            || (-n <= z < 0  && ((x - y) / n) == x / n - y / n - 1))})
}

/// Ensures that div_auto is true
pub proof fn lemma_div_auto(n: int)
    requires n > 0
    ensures
        div_auto(n)
{ ... 80 lines of assertions ... }
```

-/

#slides Design /-!
### UX Design Ideas

**Import by name**

```rust
by(lean_import(name_of_lemma))
```

- Translate Lean->Verus, check goal equivalent
- Most simple to implement
- Can pull from precompiled oleans (fast-ish)
- User needs to know names of Lean lemmas
  - Workaround: maintain translated lemma library

### UX Design Ideas

**Import Lean file**

```rust
lean_import!(path_to_file)
```

- Auto-gen trusted Verus lemmas for every lemma in Lean file
- Simple to implement
- Less maintenance burden for core devs
- Generated Verus signatures not inspectable
  - Workaround: file translator rather than macro
    - Need to manually update file!
    - Bad workaround

### UX Design Ideas

**Export to file**

("Export to Lean" code action in Verus)

- Translate Verus->Lean, put goal in a Lean file
  - Can auto insert correct lean import
- Power users can prove lemmas as they need
- May require more involved lake project management

### UX Design Ideas

**Lean Automation**

```rust
by(lean_find)
```
- Translates goal from Verus->Lean and runs `#exact?`
  - or `simp` or `aesop` or ...
- Will be slow
- Might be frustrating if goals not stated in mathlib-style
- BUT: avoids need to know Lean lemma names

### Tangent: verifying Lean runtime?

- Verus seems like a great tool for system-level code
- Already have Rust bindings for Lean runtime(?)
- Cool project:
  - Re-implement Lean runtime in Rust
  - Verify it correct with Verus
-/
