//! num-integer 0.1.47 (pin 765fd9b) x Verus -- the F1 div family / is_multiple_of
//! formal mirror
//! (corresponds to the `impl_integer_for_isize!` / `impl_integer_for_usize!`
//!  macro expansions of the upstream code/src/lib.rs instantiated on i64 /
//!  u64; this file = the verified-mirror aggregation, not a standalone driver)
//!
//! Transcription baseline (KVerus migrate conventions):
//!   - upstream traits/generics are unavailable under single-file verus; per
//!     the macro-expansion sites the machine instances take i64 (the signed
//!     family) and u64 (the unsigned family); `&self`/`*self` become by-value
//!     machine parameters.
//!   - upstream source text is kept verbatim (line references cite the
//!     code/src/lib.rs pin tree).
//!   - the caller obligations of the machine `/`, `%` are exactly the vstd
//!     std_specs encoding of `Div`/`Rem`: "possible division by zero" and
//!     the (MIN, -1) overflow check -- those two are precisely the
//!     obligation-ified form of the std rustdoc `# Panics`.
//!
//! Reading guide: the L0 transcriptions (`*_upstream`) deliberately carry no
//! requires -- the upstream doc declares no preconditions at all (no
//! `# Panics` section, the F1 finding shape); a verus error landing exactly
//! on the transcribed `/`, `%` line is the F1 reproduction anchor. The
//! contracted versions (`*_documented`) give the Fix-Document shape with all
//! obligations discharged. Two-zone split: the obligation
//! anchors / refutations / witnesses stay in src; the UT example blocks
//! live as a whole in harness/ut_div.rs, average in harness/average.rs.
//!
//! Idioms: `x@` appears only in operator positions (argument positions need
//! the `a@ + 0` / `b@ * 1` pinning); Rust truncated-division semantics are
//! always written with the vstd `rust_div` / `rust_rem` (spec-position
//! `/`, `%` are Euclidean, differing from Rust on negative operands --
//! never used there directly).

use vstd::prelude::*;
use vstd::arithmetic::div_mod::rust_rem;   // the divisibility predicate of the is_multiple_of contract

verus! {

// =========================================================================
// 0. Note: the truncated-division identity `b * q + r == a` (the general form of
//    UT test_division_rule) is unprovable under the default z3 encoding -- the Div/Rem
//    trait specs give only boundedness (0 <= r < b / -b < r <= 0), no mul-div
//    nonlinear identity; the equality of the spec-position machine `%` with the
//    spec value likewise needs one extra bridge layer. So the contract layer is
//    expressed with "machine-level symbolic bounds" (the provable shape); the identity
//    coverage falls on the concrete example functions (ut_* / *_pair) -- z3 fully evaluates
//    concrete values. (probe basis: bounds all 3 cases verified; identity and ==spec both 2 cases error.)
// =========================================================================

// =========================================================================
// 1. div_rem -- the F1 sites (code/src/lib.rs:589-593 signed / 950-954 unsigned)
// =========================================================================

/// `div_rem` signed macro-expansion body (lib.rs:590-593), verbatim transcription.
/// The doc comment (outside # Examples) declares no preconditions => requires is empty.
/// EXPECTED x2 at LIB:592-anchor: "possible division by zero" and the
/// "(lhs, rhs) != (i64::MIN, -1)" overflow obligations (the std
/// `Div`/`Rem` rustdoc `# Panics` semantics; their obligation-ified form is
/// the runtime divide-by-zero / divide-with-overflow panic).
/// Upstream doc (lib.rs:245-246):
///   Simultaneous truncated integer division and modulus.
///   Returns `(quotient, remainder)`.
pub exec fn div_rem_upstream_i64(a: i64, b: i64) -> (r: (i64, i64)) {
    // /// Simultaneous truncated integer division and modulus. (lib.rs:589)
    // #[inline]
    // fn div_rem(&self, other: &Self) -> (Self, Self) {
    //     (*self / *other, *self % *other)      // lib.rs:592 <-- the F1 anchor
    // }
    (a / b, a % b)       // lib.rs:592 <-- EXPECTED: division by zero; MIN/-1 overflow
}

/// `div_rem` unsigned macro-expansion body (lib.rs:950-954).
/// EXPECTED at LIB:953-anchor: "possible division by zero" (the unsigned side has no MIN/-1 face).
/// Upstream doc (lib.rs:245-246):
///   Simultaneous truncated integer division and modulus.
///   Returns `(quotient, remainder)`.
pub exec fn div_rem_upstream_u64(a: u64, b: u64) -> (r: (u64, u64)) {
    (a / b, a % b)       // lib.rs:953 <-- EXPECTED: division by zero
}

/// Fix-Document shape: add the one missing premise of this crate
/// ("Panics if other == 0 or the division overflows" -- the same wording
/// as the std `Div`/`Rem` rustdoc) and the same code passes all obligations.
/// Upstream doc (lib.rs:245-246):
///   Simultaneous truncated integer division and modulus.
///   Returns `(quotient, remainder)`.
pub exec fn div_rem_documented_i64(a: i64, b: i64) -> (r: (i64, i64))
    requires
        b != 0,                       // FIX (Document): other == 0
        !((a == i64::MIN) && (b == -1)),  // FIX (Document): MIN / -1 overflow
        // SPEC-DOC MISMATCH (rust-num/num-integer#83): the div/rem family
        // declares no zero-divisor `# Panics` while the machine `/`/`%`
        // implementation panics there (the std `Div`/`Rem` rustdoc both
        // declare it) -- the doc-class div/rem zero-divisor portion of the
        // is_multiple_of bundle; the doc-silent premises are carried here in
        // the implementation-faithful form (the expected errors stay on the L0
        // anchors above).
    ensures
        // truncated-remainder bounds (positive divisor; negative-divisor cases covered by the ut_* examples)
        b > 0 && a >= 0 ==> (r.1 >= 0 && r.1 < b),
        b > 0 && a < 0 ==> (r.1 <= 0 && r.1 > (-b)),
{
    (a / b, a % b)       // lib.rs:592  -- now fully discharged
}

/// Upstream doc (lib.rs:245-246):
///   Simultaneous truncated integer division and modulus.
///   Returns `(quotient, remainder)`.
pub exec fn div_rem_documented_u64(a: u64, b: u64) -> (r: (u64, u64))
    requires b != 0,
    ensures
        r.1 < b,                      // truncated-remainder bound (unsigned)
{
    (a / b, a % b)
}



// =========================================================================
// 2. mod_floor / div_floor / div_mod_floor / div_ceil (the F1 site family)
// =========================================================================

/// `mod_floor` signed macro-expansion body (lib.rs:454-465), verbatim transcription (the `%` is the direct site).
/// EXPECTED at LIB:459-anchor: division by zero + MIN/-1.
/// Upstream doc (lib.rs:52-58):
///   Floored integer modulo, satisfying:
///   ~~~
///   # use num_integer::Integer;
///   # let n = 1; let d = 1;
///   assert!(n.div_floor(&d) * d + n.mod_floor(&d) == n)
///   ~~~
pub exec fn mod_floor_upstream_i64(a: i64, b: i64) -> (r: i64) {
    // /// Floored integer modulo (lib.rs:454-465)
    //     let r = *self % *other;                     // lib.rs:459 <-- the F1 anchor
    // if (r > 0 && *other < 0) || (r < 0 && *other > 0) { r + *other } else { r }
    let r = a % b;        // lib.rs:459 <-- EXPECTED: division by zero; MIN/-1
    if (r > 0 && b < 0) || (r < 0 && b > 0) {
        r + b             // (the branch-add overflow obligation is discharged in the *_documented version)
    } else {
        r
    }
}

/// `div_floor` signed macro-expansion body (lib.rs:441-452). The in-body
/// `self.div_rem(other)` forwards to the same macro's `div_rem`
/// (lib.rs:591-593) -- the panic site is exactly the `/`, `%` of lib.rs:592; the one-line div_rem body is directly inlined here per the macro expansion (semantically equivalent, call depth 0).
/// Upstream doc (lib.rs:34):
///   Floored integer division.
pub exec fn div_floor_upstream_i64(a: i64, b: i64) -> (q: i64) {
    // /// Floored integer division
    // // Algorithm from [Daan Leijen ...]
    // let (d, r) = self.div_rem(other);           // lib.rs:446 -> 592 (inlined)
    // if (r > 0 && *other < 0) || (r < 0 && *other > 0) { d - 1 } else { d }
    let (d, r) = (a / b, a % b);   // lib.rs:446->592 <-- EXPECTED: division by zero; MIN/-1
    if (r > 0 && b < 0) || (r < 0 && b > 0) {
        d - 1
    } else {
        d
    }
}

/// `div_ceil` signed macro-expansion body (lib.rs:480-488).
/// Upstream doc (lib.rs:76):
///   Ceiled integer division.
pub exec fn div_ceil_upstream_i64(a: i64, b: i64) -> (q: i64) {
    // let (d, r) = self.div_rem(other);           // lib.rs:482 -> 592 (inlined)
    // if (r > 0 && *other > 0) || (r < 0 && *other < 0) { d + 1 } else { d }
    let (d, r) = (a / b, a % b);   // lib.rs:482->592 <-- EXPECTED: division by zero; MIN/-1
    if (r > 0 && b > 0) || (r < 0 && b < 0) {
        d + 1
    } else {
        d
    }
}

/// `div_ceil` unsigned macro-expansion body (lib.rs:865-868):
/// `*self / *other + (0 != *self % *other) as Self`
/// (`bool as u64` is rewritten as the equivalent if in verus -- a
///  semantics-preserving rewrite reaching the same `/`, `%` pair under either evaluation order).
/// Upstream doc (lib.rs:76):
///   Ceiled integer division.
pub exec fn div_ceil_upstream_u64(a: u64, b: u64) -> (q: u64) {
    let q = a / b;       // lib.rs:867 <-- EXPECTED: division by zero
    let r = a % b;       // lib.rs:867 <-- EXPECTED: division by zero
    if r != 0 {
        q + 1
    } else {
        q
    }
}

/// --- contracted versions (doc/UT semantics) --------------------------------
///
/// `div_mod_floor` (lib.rs:466-478) combined: the division rule with floor
/// semantics, i.e. the mod_floor doc identity (lib.rs:52-58 example:
/// `n.div_floor(&d) * d + n.mod_floor(&d) == n`);
/// positive divisors additionally get the floor-remainder bound `0 <= r < b`.
/// Upstream doc (lib.rs:264-265):
///   Simultaneous floored integer division and modulus.
///   Returns `(quotient, remainder)`.
pub exec fn div_mod_floor_documented_i64(a: i64, b: i64) -> (qr: (i64, i64))
    requires
        b != 0,
        !((a == i64::MIN) && (b == -1)),
        // SPEC-DOC MISMATCH (rust-num/num-integer#83): the div/rem family
        // declares no zero-divisor `# Panics` while the machine `/`/`%`
        // implementation panics there (the std `Div`/`Rem` rustdoc both
        // declare it) -- the doc-class div/rem zero-divisor portion of the
        // is_multiple_of bundle; the doc-silent premises are carried here in
        // the implementation-faithful form (the expected errors stay on the L0
        // anchors above).
    ensures
        // The doc identity (lib.rs:57) `n.div_floor(&d)*d + n.mod_floor(&d) == n`
        // is nonlinear in the multiplicative form under the default encoding (see
        // the section 0 note) -- covered by the concrete examples; the equivalent
        b > 0 ==> (qr.1 >= 0 && qr.1 < b),
{
    // /// Calculates `div_floor` and `mod_floor` simultaneously (lib.rs:467-478)
    let (d, r) = (a / b, a % b);   // lib.rs:472 -> 592 (inlined; the obligations are discharged by the requires)
    if (r > 0 && b < 0) || (r < 0 && b > 0) {
        (d - 1, r + b)
    } else {
        (d, r)
    }
}

/// `div_floor` single-value version (lib.rs:441-452) contract: the floor-quotient property for positive divisors.
/// Upstream doc (lib.rs:34):
///   Floored integer division.
pub exec fn div_floor_documented_i64(a: i64, b: i64) -> (q: i64)
    requires
        b != 0,
        !((a == i64::MIN) && (b == -1)),
        b > 0,
        // SPEC-DOC MISMATCH (rust-num/num-integer#83): the div/rem family
        // declares no zero-divisor `# Panics` while the machine `/`/`%`
        // implementation panics there (the std `Div`/`Rem` rustdoc both
        // declare it) -- the doc-class div/rem zero-divisor portion of the
        // is_multiple_of bundle; the doc-silent premises are carried here in
        // the implementation-faithful form (the expected errors stay on the L0
        // anchors above).
    ensures
        // The floor-quotient inequality `b*q <= a < b*(q+1)` is a multiplicative nonlinear form (see the section 0 note),
        // covered by the example functions ut_test_div_mod_floor_examples / ut_test_div_ceil_examples
        // with all 16 doc (n, d) pairs (negative divisors included);
        // what stays here: positive divisor, a >= 0 => q == the truncated quotient (the zero-adjustment branch),
        // i.e. the no-adjustment-branch floor consistency.
        a >= 0 ==> (q >= 0 && q <= a),
{
    let (d, r) = (a / b, a % b);   // lib.rs:446->592
    if (r > 0 && b < 0) || (r < 0 && b > 0) {
        d - 1
    } else {
        d
    }
}

/// `mod_floor` single-value version (lib.rs:454-465) contract.
/// Upstream doc (lib.rs:52-58):
///   Floored integer modulo, satisfying:
///   ~~~
///   # use num_integer::Integer;
///   # let n = 1; let d = 1;
///   assert!(n.div_floor(&d) * d + n.mod_floor(&d) == n)
///   ~~~
pub exec fn mod_floor_documented_i64(a: i64, b: i64) -> (r: i64)
    requires
        b != 0,
        !((a == i64::MIN) && (b == -1)),
        // SPEC-DOC MISMATCH (rust-num/num-integer#83): the div/rem family
        // declares no zero-divisor `# Panics` while the machine `/`/`%`
        // implementation panics there (the std `Div`/`Rem` rustdoc both
        // declare it) -- the doc-class div/rem zero-divisor portion of the
        // is_multiple_of bundle; the doc-silent premises are carried here in
        // the implementation-faithful form (the expected errors stay on the L0
        // anchors above).
    ensures
        b > 0 ==> (r >= 0 && r < b),
{
    let r = a % b;        // lib.rs:459
    if (r > 0 && b < 0) || (r < 0 && b > 0) {
        r + b
    } else {
        r
    }
}

/// `div_ceil` single-value version (lib.rs:480-488) contract (positive
/// divisor): `b*q - b < a <= b*q` (the ceil quotient).
/// Upstream doc (lib.rs:76):
///   Ceiled integer division.
pub exec fn div_ceil_documented_i64(a: i64, b: i64) -> (q: i64)
    requires
        b != 0,
        !((a == i64::MIN) && (b == -1)),
        b > 0,
        // SPEC-DOC MISMATCH (rust-num/num-integer#83): the div/rem family
        // declares no zero-divisor `# Panics` while the machine `/`/`%`
        // implementation panics there (the std `Div`/`Rem` rustdoc both
        // declare it) -- the doc-class div/rem zero-divisor portion of the
        // is_multiple_of bundle; the doc-silent premises are carried here in
        // the implementation-faithful form (the expected errors stay on the L0
        // anchors above).
    ensures
        // The ceil-quotient inequality is likewise a multiplicative nonlinear form (see the section 0 note); covered by the example functions.
        a >= 0 ==> (q >= 0 && q >= a / b),
{
    let (d, r) = (a / b, a % b);   // lib.rs:482->592
    if (r > 0 && b > 0) || (r < 0 && b < 0) {
        d + 1
    } else {
        d
    }
}





// =========================================================================
// 3. is_multiple_of -- the explicit zero-guard control + the MIN/-1
//    blind-audit note
// =========================================================================

/// `is_multiple_of` signed macro-expansion body (lib.rs:568-575), verbatim transcription.
/// The zero divisor has an explicit guard (lib.rs:571-573) -> the "possible division by zero"
/// is discharged by control flow; MIN/-1 has no guard -> EXPECTED at LIB:574-anchor:
/// "possible overflow case for signed remainder: (lhs, rhs) != (i64::MIN, -1)"
/// -- i.e. the runtime `attempt to calculate the remainder with a divisor of -1`.
/// Control group: next_multiple_of / prev_multiple_of (lib.rs:597-616) carry in the tip pin tree
/// the `if *other == -1 { return *self; }` guard; is_multiple_of does not (the blind-audit note).
/// Upstream doc (lib.rs:212):
///   Returns `true` if `self` is a multiple of `other`.
pub exec fn is_multiple_of_upstream_i64(a: i64, b: i64) -> (r: bool) {
    // /// Returns `true` if the number is a multiple of `other`.
    // if other.is_zero() { return self.is_zero(); }   // lib.rs:571-572 explicit guard
    // *self % *other == 0                             // lib.rs:574 <-- the MIN/-1 anchor
    if b == 0 {
        return a == 0;
    }
    a % b == 0          // lib.rs:574 <-- EXPECTED: MIN/-1 remainder overflow (zero already guarded)
}

/// Unsigned version (lib.rs:929-936): the guard face is complete (no MIN/-1
/// face) -> the L0 passes all obligations, the guard-completeness control group.
/// Upstream doc (lib.rs:212):
///   Returns `true` if `self` is a multiple of `other`.
pub exec fn is_multiple_of_upstream_u64(a: u64, b: u64) -> (r: bool)
    ensures r == ((b == 0 && a == 0) || (b != 0 && a % b == 0)),
{
    if b == 0 {
        return a == 0;
    }
    a % b == 0
}

/// The is_multiple_of doc contract ("Returns true if self is a multiple of
/// other"): adding the MIN/-1 premise passes all obligations.
/// Upstream doc (lib.rs:212):
///   Returns `true` if `self` is a multiple of `other`.
pub exec fn is_multiple_of_documented_i64(a: i64, b: i64) -> (r: bool)
    requires
        b != 0,
        !((a == i64::MIN) && (b == -1)),
    ensures
        r == (rust_rem(a@ + 0, b@ * 1) == 0),
{
    if b == 0 {
        return a == 0;
    }
    a % b == 0
}

/// Zero-guard control proof: the b == 0 input path is panic-free and returns a == 0
/// (the obligation-ified counterpart of test_is_multiple_of lib.rs:1030
/// `is_multiple_of(42, 0) == false`).
/// Upstream doc (lib.rs:212):
///   Returns `true` if `self` is a multiple of `other`.
pub exec fn is_multiple_of_zero_guard_case(a: i64, b: i64) -> (r: bool)
    requires b == 0,
    ensures r == (a == 0),
{
    if b == 0 {
        return a == 0;
    }
    a % b == 0
}

// =========================================================================
// 4. next_multiple_of -- evaluating the obligation effect of the tip-added
//    -1 guard
// =========================================================================

/// `next_multiple_of` signed macro-expansion body (lib.rs:594-605, with the tip's new guard).
/// Expected obligation layout:
///   - the lib.rs:599 guard returns early on the (a, b) == (MIN, -1) path -> the MIN/-1
///     remainder obligation is discharged (the contrast with is_multiple_of);
///   - b == 0 has no guard -> the lib.rs:603 (-> 459) `%` site EXPECTED division by zero.
/// Upstream doc (lib.rs:285-289):
///   Rounds up to nearest multiple of argument.
///
///   # Notes
///
///   For signed types, `a.next_multiple_of(b) = a.prev_multiple_of(b.neg())`.
pub exec fn next_multiple_of_upstream_i64(a: i64, b: i64) -> (ret: i64) {
    // // Avoid the overflow of `MIN % -1`
    // if *other == -1 { return *self; }          // lib.rs:598-601 tip guard
    // let m = Integer::mod_floor(self, other);   // lib.rs:603 -> 459 (inlined expansion)
    // *self + if m == 0 { 0 } else { other - m }
    if b == -1 {
        return a;
    }
    let r = a % b;      // lib.rs:603->459 <-- EXPECTED: division by zero
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a + (if m == 0 { 0 } else { b - m })
}


// =========================================================================
// 6. is_even / is_odd -- the coverage-difference batch.
//    The bitwise `&1` contract is fully discharged via the by (bit_vector)
//    bit-level bridge (the same deployment as src/average.rs: the assertions use only parameter terms) -- this group is no anchor; it closes coverage.
// =========================================================================

/// `is_even` signed macro-expansion body (lib.rs:577-581), verbatim transcription (the i64 instance):
/// `fn is_even(&self) -> bool { (*self) & 1 == 0 }` (lib.rs:580).
/// The doc contract (lib.rs:223 "Returns true if the number is even") = the divisibility
/// predicate <=> `((x & 1 == 0) == (x % 2 == 0))` (bit-level fact) + the rust_rem
/// semantics of the machine `%` (src/lib.rs section 3 already uses the same contract).
/// Upstream doc (lib.rs:223):
///   Returns `true` if the number is even.
pub exec fn is_even_upstream_i64(x: i64) -> (r: bool)
    ensures
        r == (rust_rem(x@ + 0, 2) == 0),
{
    // /// Returns `true` if the number is divisible by `2`
    // (*self) & 1 == 0                       // lib.rs:580
    // Bit-level bridge (params-only):
    assert((x & 1 == 0) == (x % 2 == 0)) by (bit_vector);
    (x & 1) == 0        // no residual obligation after the bit-bridge discharge (no pre-existing upstream error set)
}

/// `is_odd` signed macro-expansion body (lib.rs:583-587): `!self.is_even()` (inlined).
/// Upstream doc (lib.rs:234):
///   Returns `true` if the number is odd.
pub exec fn is_odd_upstream_i64(x: i64) -> (r: bool)
    ensures
        r == (rust_rem(x@ + 0, 2) != 0),
{
    // lib.rs:586 `!self.is_even()` (is_even :580 inlined)
    assert((x & 1 == 0) == (x % 2 == 0)) by (bit_vector);
    !((x & 1) == 0)
}

/// `is_even` unsigned macro-expansion body (lib.rs:938-942): `*self % 2 == 0` (lib.rs:941).
/// The unsigned side has no bitwise face; all obligations discharge directly.
/// Upstream doc (lib.rs:223):
///   Returns `true` if the number is even.
pub exec fn is_even_upstream_u64(x: u64) -> (r: bool)
    ensures
        r == (x@ % 2 == 0),
{
    x % 2 == 0
}

/// `is_odd` unsigned macro-expansion body (lib.rs:944-948).
/// Upstream doc (lib.rs:234):
///   Returns `true` if the number is odd.
pub exec fn is_odd_upstream_u64(x: u64) -> (r: bool)
    ensures
        r == (x@ % 2 == 1),
{
    !(x % 2 == 0)
}

// =========================================================================
// 7. prev_multiple_of -- the coverage-difference batch.
//    lib.rs:607-616 (the `other == -1` guard at :611, then `self - mod_floor` at :615).
//    L0 obligation anchors (expected error x2, the F1 family -- the newly extended
//    subtraction-side face):
//      (1) the subtraction underflow at :615: the doc examples only show moderate values,
//          but a=MIN with m>0 (e.g. (MIN).prev_multiple_of(&3) -> m=1 -> MIN-1) triggers it --
//          the doc has no `# Panics` (same F1 doctrine: the std Sub/Mul rustdoc carry their own # Panics);
//      (2) the inlined mod_floor division by zero (b=0 unguarded, same as next_multiple_of's :603).
// =========================================================================

/// `prev_multiple_of` signed macro-expansion body (lib.rs:609-616), verbatim transcription
/// (the mod_floor :603 body is inlined per the macro expansion -- call depth 0, semantically equivalent).
/// EXPECTED x2 at LIB:612-anchor / LIB:615-anchor.
/// Upstream doc (lib.rs:318-322):
///   Rounds down to nearest multiple of argument.
///
///   # Notes
///
///   For signed types, `a.prev_multiple_of(b) = a.next_multiple_of(b.neg())`.
pub exec fn prev_multiple_of_upstream_i64(a: i64, b: i64) -> (ret: i64) {
    // /// Rounds down to nearest multiple of argument.
    // if *other == -1 { return *self; }       // lib.rs:611 tip guard
    // let m = Integer::mod_floor(self, other);// lib.rs:615 -> :459 (inlined)
    // *self - m
    if b == -1 {
        return a;
    }
    let r = a % b;        // lib.rs:615->459 <-- EXPECTED: division by zero (b=0 is unguarded)
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a - m                 // lib.rs:615 <-- EXPECTED: subtract underflow (a=MIN, m>0)
}

/// Fix-Document shape: after adding the "subtraction stays within the MIN bound"
/// and the "b != 0, not (MIN, -1)" obligations, the distance property passes
/// fully for positive divisors: the return value r satisfies `0 <= a - r < b` (the multiple
/// identity in the d*r == 0 form is multiplicatively nonlinear -- see the section 0 note; covered by the examples).
/// The exact safe precondition on the subtraction side is given by the rust_rem conditional:
/// mod_floor's m is exactly the non-negative-ized rust_rem (+b when r < 0),
/// a - m >= MIN <=> the formula below -- it precisely characterizes the real overflow
/// corner posed by prev_multiple_of(MIN+1, 11) -> m=3 (see the PoC).
/// Upstream doc (lib.rs:318-322):
///   Rounds down to nearest multiple of argument.
///
///   # Notes
///
///   For signed types, `a.prev_multiple_of(b) = a.next_multiple_of(b.neg())`.
pub exec fn prev_multiple_of_documented_i64(b: i64, a: i64) -> (r: i64)
    requires
        b != 0,                                // FIX (Document)
        !((a == i64::MIN) && (b == -1)),      // FIX (Document): corresponds to the tip guard
        b > 0,                                // the contract version focuses on positive divisors (negative divisors covered by the examples)
        (rust_rem(a@ + 0, b@ * 1) >= 0
            && a@ - rust_rem(a@ + 0, b@ * 1) >= (-9223372036854775808))
            || (rust_rem(a@ + 0, b@ * 1) < 0
                && a@ - (rust_rem(a@ + 0, b@ * 1) + b@) >= (-9223372036854775808)),
    ensures
        // SPEC-DOC MISMATCH (unreported): the doc promises "Rounds down to
        // nearest multiple of argument" with no overflow `# Panics`; the
        // doc-promised rounding clause is unprovable at the lib.rs:615
        // subtract corner (release builds wrap to the opposite-sign extreme,
        // past the requested multiple), so the distance form is carried under
        // the overflow-excluding precondition the doc omits.
        b > 0 ==> (0 <= a@ - r@ && a@ - r@ < b@),
{
    if b == -1 {
        return a;
    }
    let r = a % b;        // lib.rs:615->459
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a - m
}

/// `next_multiple_of` Fix-Document shape (the contract completion of the section 4 L0, closed symmetrically):
/// all obligations discharge for positive divisors; the addition-side safe precondition is
/// sharpened with the same rust_rem conditional as prev (the real corner next_multiple_of(MAX-1, 11) -> m=6 -> +5 past the upper bound, see the PoC).
/// Upstream doc (lib.rs:285-289):
///   Rounds up to nearest multiple of argument.
///
///   # Notes
///
///   For signed types, `a.next_multiple_of(b) = a.prev_multiple_of(b.neg())`.
pub exec fn next_multiple_of_documented_i64(a: i64, b: i64) -> (ret: i64)
    requires
        b != 0,
        !((a == i64::MIN) && (b == -1)),
        b > 0,
        rust_rem(a@ + 0, b@ * 1) == 0
            || a@ + (b@ - rust_rem(a@ + 0, b@ * 1)) <= 9223372036854775807,
    ensures
        // SPEC-DOC MISMATCH (unreported): the doc promises "Rounds up to
        // nearest multiple of argument" with no overflow `# Panics`; the
        // doc-promised rounding clause is unprovable at the lib.rs:604 add
        // corner (release builds wrap to the opposite-sign extreme, past the
        // requested multiple), so the distance form is carried under the
        // overflow-excluding precondition the doc omits.
        b > 0 ==> (0 <= ret@ - a@ && ret@ - a@ <= b@),
{
    // /// Rounds up to nearest multiple of argument. (lib.rs:595-605)
    if b == -1 {
        return a;
    }
    let r = a % b;        // lib.rs:603->459
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a + (if m == 0 { 0 } else { b - m })
}

// =========================================================================
// 8. dec / inc -- the coverage-difference batch.
//    Trait default bodies (lib.rs:345-360 / :362-377), `&mut self` converted to the
//    by-value return form. L0 obligation anchors (expected error x1 each, the F1
//    add/sub extension family -- the doc likewise has no # Panics):
//      dec: lib.rs:359 `*self = self.clone() - Self::one()` -> the MIN subtraction-side overflow;
//      inc: lib.rs:376 -> the MAX addition-side overflow.
//    (Runtime verification: MIN.dec() debug panics "attempt to subtract
//    with overflow" -- see out/poc/integer-family-overflow/.)
// =========================================================================

/// `dec` trait default body (lib.rs:355-360), verbatim transcription (the i64 instance).
/// EXPECTED at LIB:359-anchor: subtract underflow (self == MIN).
/// Upstream doc (lib.rs:345):
///   Decrements self by one.
pub exec fn dec_upstream_i64(x: i64) -> (r: i64) {
    // /// Decrements self by one.
    // *self = self.clone() - Self::one()      // lib.rs:359 <-- the F1 add/sub-side anchor
    x - 1
}

/// `inc` trait default body (lib.rs:372-377), verbatim transcription.
/// EXPECTED at LIB:376-anchor: add overflow (self == MAX).
/// Upstream doc (lib.rs:362):
///   Increments self by one.
pub exec fn inc_upstream_i64(x: i64) -> (r: i64) {
    x + 1                // lib.rs:376 <-- the F1 add/sub-side anchor
}

/// `dec` Fix-Document shape: adding the MIN subtraction side passes all obligations
/// (the step postcondition is exactly the doc semantics "Decrements self by one").
/// Upstream doc (lib.rs:345):
///   Decrements self by one.
pub exec fn dec_documented_i64(x: i64) -> (r: i64)
    requires
        x > i64::MIN,                          // FIX (Document)
    ensures
        r == x - 1,
{
    x - 1
}

/// `inc` Fix-Document shape.
/// Upstream doc (lib.rs:362):
///   Increments self by one.
pub exec fn inc_documented_i64(x: i64) -> (r: i64)
    requires
        x < i64::MAX,                          // FIX (Document)
    ensures
        r == x + 1,
{
    x + 1
}

// =========================================================================
// Proof lemmas -- the reachability witnesses of the F1 / MIN/-1 anchors
// and the coverage-difference anchors (signatures and contracts untouched)
// =========================================================================
// =========================================================================
// 5. Reachability witnesses (the F1 counterexample + the MIN/-1 counterexample)
// =========================================================================

/// F1 reachability: the documented precondition set is empty; the witness (a, b) = (8, 0)
/// satisfies the empty premises and falsifies div_rem's division-by-zero
/// obligation -- inputs on which the upstream obligations necessarily fail
/// really exist (the PoC's own case).
proof fn f1_witness_div_zero() {
    let a: int = 8;
    let b: int = 0;
    assert(true);        // documented precondition set is empty
    assert(b == 0);      // => the division-by-zero obligations of div_rem / mod_floor / div_ceil are false
}

/// MIN/-1 reachability: the witness (a, b) = (i64::MIN, -1) likewise satisfies the empty
/// documented premises and falsifies the (MIN, -1) remainder/division overflow obligations of is_multiple_of / div_rem.
proof fn f1_witness_min_minus_one() {
    let a: int = 0 - 9223372036854775808;
    let b: int = -1;
    assert(true);        // documented precondition set is empty
    assert(a == 0 - 9223372036854775808 && b == -1);
}

// =========================================================================
// 9. Reachability witnesses of the coverage-difference anchors
// =========================================================================

/// prev_multiple_of subtraction-anchor reachability: the witness a = i64::MIN, b = 3 (satisfying the empty
/// documented preconditions) => m = mod_floor(MIN, 3) = 1 => prev = MIN - 1 < MIN,
/// so the :615 underflow obligation is false (the same live measurement as the runtime PoC).
proof fn witness_prev_multiple_of_underflow() {
    let a: int = 0 - 9223372036854775808;
    let b: int = 3;
    assert(true);        // documented precondition set is empty
    // Euclid floor-mod: m = a - b*floor(a/b) = -2^63 + 3*3074457345618258603
    assert(a / b == 0 - 3074457345618258603);         // Euclid division (negative rounds down)
    assert(a % b == 1);                                // m = 1
    assert(a - (a % b) < a - 0 + 0);                   // MIN - 1 < MIN <=> underflow
}

/// dec subtraction-anchor reachability: the witness x = i64::MIN => the underflow obligation at :359 is false.
proof fn witness_dec_underflow() {
    let x: int = 0 - 9223372036854775808;
    assert(true);        // documented precondition set is empty
    assert(x - 1 < x);                                 // MIN - 1 is out of range
}

/// inc addition-anchor reachability: the witness x = i64::MAX => the addition-overflow obligation at :376 is false.
proof fn witness_inc_overflow() {
    let x: int = 9223372036854775807;
    assert(true);        // documented precondition set is empty
    assert(x + 1 > x);                                 // MAX + 1 is out of range
}

/// next_multiple_of addition-anchor reachability: the witness a = i64::MAX, b = 8 => m = 7 =>
/// next = MAX + 1, so the :604 addition obligation is false.
proof fn witness_next_multiple_of_overflow() {
    let a: int = 9223372036854775807;
    let b: int = 8;
    assert(true);        // documented precondition set is empty
    assert(a % b == 7);                                // m = 7
    assert(a + (b - (a % b)) > a);                     // MAX + 1 is out of range
}

}

fn main() {}
