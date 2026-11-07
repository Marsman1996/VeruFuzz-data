//! num-integer 0.1.47 (pin 765fd9b) x Verus -- the Roots signed-precheck
//! assertions
//! (corresponds to the `signed_roots!` macro expansion of the upstream
//!  code/src/roots.rs on i64/u64)
//!
//! Purpose: **the documented-panic control group**. roots.rs:15-29 / :60-67
//! write `# Panics` sections for `nth_root(0)`, even roots of negatives,
//! and `sqrt` of negatives; this file obligation-ifies the same panic
//! discipline: the L0 transcriptions (no preconditions) become the failing
//! assertion lines; the contracted versions with the documented preconditions
//! (`*_documented`) discharge all obligations -- the classification contrast
//! with the F1 of lib.rs (the div family has no `# Panics` at all).
//!
//! The unsigned nth_root algorithm proper (roots.rs:241-310: recursion +
//! fixpoint + karatsuba) is out of scope: replaced by external_body stubs
//! (no verified site).

use vstd::prelude::*;

verus! {

// =========================================================================
// Delegate stubs: unsigned nth_root / sqrt (roots.rs:237-422, out of scope)
// =========================================================================

/// The nth_root proper of the roots.rs unsigned_roots! macro (out-of-scope stub).
/// Carries only the result bound (the n-th root of x stays below 2^32 for all n >= 2),
/// no value-level obligations; the verified sites are the callers' precheck assertions.
#[verifier::external_body]
/// Upstream doc (roots.rs:8-29; superscript and root glyphs normalized to ASCII):
///   Returns the truncated principal `n`th root of an integer
///   -- `if x >= 0 { floor(nth_root(x)) } else { ceil(nth_root(x)) }`
///
///   This is solving for `r` in `r^n = x`, rounding toward zero.
///   If `x` is positive, the result will satisfy `r^n <= x < (r+1)^n`.
///   If `x` is negative and `n` is odd, then `(r-1)^n < x <= r^n`.
///
///   # Panics
///
///   Panics if `n` is zero:
///
///   ```should_panic
///   # use num_integer::Roots;
///   println!("can't compute 0th-root(x) : {}", 123.nth_root(0));
///   ```
///
///   or if `n` is even and `self` is negative:
///
///   ```should_panic
///   # use num_integer::Roots;
///   println!("no imaginary numbers... {}", (-1).nth_root(10));
///   ```
exec fn nth_root_unsigned_stub(a: u64, n: u32) -> (r: u64)
    ensures r < 4294967296u64,   // < 2^32 (the bound of all integer roots with n >= 2)
{
    0u64
}

/// The unsigned sqrt proper of roots.rs (out-of-scope stub).
#[verifier::external_body]
/// Upstream doc (roots.rs:55-67; superscript and root glyphs normalized to ASCII):
///   Returns the truncated principal square root of an integer -- floor(sqrt(x))
///
///   This is solving for `r` in `r^2 = x`, rounding toward zero.
///   The result will satisfy `r^2 <= x < (r+1)^2`.
///
///   # Panics
///
///   Panics if `self` is less than zero:
///
///   ```should_panic
///   # use num_integer::Roots;
///   println!("no imaginary numbers... {}", (-1).sqrt());
///   ```
exec fn sqrt_unsigned_stub(a: u64) -> (r: u64)
    ensures r < 4294967296u64,   // < 2^32
{
    0u64
}

// =========================================================================
// L0 transcriptions (no preconditions) -- the obligation-ification of the
//    documented panics
// =========================================================================

/// `nth_root` signed macro-expansion body (roots.rs:134-143), the precheck part verbatim.
/// Doc contract (roots.rs:13-29): x < 0 with even n => panic (explicitly declared in the `# Panics` section).
/// The L0 (no preconditions): the obligation-ified form of `assert!(n.is_odd(), ...)`
/// fails exactly at the roots.rs:140 assertion -- the only difference from F1: **here the doc declares it**.
/// Upstream doc (roots.rs:8-29; superscript and root glyphs normalized to ASCII):
///   Returns the truncated principal `n`th root of an integer
///   -- `if x >= 0 { floor(nth_root(x)) } else { ceil(nth_root(x)) }`
///
///   This is solving for `r` in `r^n = x`, rounding toward zero.
///   If `x` is positive, the result will satisfy `r^n <= x < (r+1)^n`.
///   If `x` is negative and `n` is odd, then `(r-1)^n < x <= r^n`.
///
///   # Panics
///
///   Panics if `n` is zero:
///
///   ```should_panic
///   # use num_integer::Roots;
///   println!("can't compute 0th-root(x) : {}", 123.nth_root(0));
///   ```
///
///   or if `n` is even and `self` is negative:
///
///   ```should_panic
///   # use num_integer::Roots;
///   println!("no imaginary numbers... {}", (-1).nth_root(10));
///   ```
pub exec fn nth_root_signed_precheck_upstream_i64(x: i64, n: u32) -> (r: i64) {
    // /// if *self >= 0 { (*self as $U).nth_root(n) as Self }
    // /// else {
    // ///     assert!(n.is_odd(), "even roots of a negative are imaginary");  // :140
    // ///     -((self.wrapping_neg() as $U).nth_root(n) as Self)
    // /// }
    if x >= 0 {
        nth_root_unsigned_stub(x as u64, n) as i64
    } else {
        assert(n % 2 != 0);   // roots.rs:140 <-- EXPECTED: assertion fails when n is even
        (0i64) - (nth_root_unsigned_stub(x as u64, n) as i64)
    }
}

/// `sqrt` signed macro-expansion body (roots.rs:146-149), verbatim transcription (precheck assertion + delegation).
/// Doc contract (roots.rs:55-67): `# Panics: Panics if self is less than zero`.
/// Upstream doc (roots.rs:55-67; superscript and root glyphs normalized to ASCII):
///   Returns the truncated principal square root of an integer -- floor(sqrt(x))
///
///   This is solving for `r` in `r^2 = x`, rounding toward zero.
///   The result will satisfy `r^2 <= x < (r+1)^2`.
///
///   # Panics
///
///   Panics if `self` is less than zero:
///
///   ```should_panic
///   # use num_integer::Roots;
///   println!("no imaginary numbers... {}", (-1).sqrt());
///   ```
pub exec fn sqrt_signed_precheck_upstream_i64(x: i64) -> (r: i64) {
    // /// assert!(*self >= 0, "the square root of a negative is imaginary");  // :147
    // /// (*self as $U).sqrt() as Self
    assert(x >= 0);           // roots.rs:147 <-- EXPECTED: assertion fails when x < 0
    sqrt_unsigned_stub(x as u64) as i64
}

// =========================================================================
// Documented contract versions (the preconditions declared in # Panics become requires)
// =========================================================================

/// The obligation-ified form of the roots.rs:60-67 doc: negative input is declared a panic
/// by the doc `# Panics`; with the precondition added the assertion obligation discharges and there is
/// no other panic face (the addition 0i64 - r stays within the r < 2^31 sqrt(2^63) bound -- the stub has no ensures, so only the precheck face is proven here).
/// Upstream doc (roots.rs:55-67; superscript and root glyphs normalized to ASCII):
///   Returns the truncated principal square root of an integer -- floor(sqrt(x))
///
///   This is solving for `r` in `r^2 = x`, rounding toward zero.
///   The result will satisfy `r^2 <= x < (r+1)^2`.
///
///   # Panics
///
///   Panics if `self` is less than zero:
///
///   ```should_panic
///   # use num_integer::Roots;
///   println!("no imaginary numbers... {}", (-1).sqrt());
///   ```
pub exec fn sqrt_signed_documented_i64(x: i64) -> (r: i64)
    requires x >= 0,        // FIX (Document): already declared at roots.rs:62-66 (the control-group point)
{
    sqrt_unsigned_stub(x as u64) as i64
}

/// The obligation-ified form of the roots.rs:13-29 doc: when x < 0, n must be odd (declared in `# Panics`).
/// Upstream doc (roots.rs:8-29; superscript and root glyphs normalized to ASCII):
///   Returns the truncated principal `n`th root of an integer
///   -- `if x >= 0 { floor(nth_root(x)) } else { ceil(nth_root(x)) }`
///
///   This is solving for `r` in `r^n = x`, rounding toward zero.
///   If `x` is positive, the result will satisfy `r^n <= x < (r+1)^n`.
///   If `x` is negative and `n` is odd, then `(r-1)^n < x <= r^n`.
///
///   # Panics
///
///   Panics if `n` is zero:
///
///   ```should_panic
///   # use num_integer::Roots;
///   println!("can't compute 0th-root(x) : {}", 123.nth_root(0));
///   ```
///
///   or if `n` is even and `self` is negative:
///
///   ```should_panic
///   # use num_integer::Roots;
///   println!("no imaginary numbers... {}", (-1).nth_root(10));
///   ```
pub exec fn nth_root_signed_documented_i64(x: i64, n: u32) -> (r: i64)
    requires x >= 0 || n % 2 != 0,   // FIX (Document): already declared at roots.rs:15-29
{
    if x >= 0 {
        nth_root_unsigned_stub(x as u64, n) as i64
    } else {
        assert(n % 2 != 0);   // already discharged by requires
        (0i64) - (nth_root_unsigned_stub(x as u64, n) as i64)
    }
}

// =========================================================================
// Proof lemmas -- the roots panic reachability witness
// =========================================================================

/// Reachability of the documented roots panic: even n (the witness n = 2) with x = -1 satisfies
/// the empty-precondition version entering the negative branch; `assert(2 % 2 == 0)` directly concretizes the counterexample.
proof fn roots_panic_witnesses() {
    let n: int = 2;
    let x: int = -1;
    assert(n % 2 == 0);          // even root
    assert(x < 0);               // negative radicand -- the roots.rs:140 assertion is false
    assert(x < 0);               // sqrt branch: the roots.rs:147 assertion is false
}

}

fn main() {}
