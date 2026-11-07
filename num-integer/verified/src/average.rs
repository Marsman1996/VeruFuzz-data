//! num-integer 0.1.47 (pin 765fd9b) x Verus -- the Average (Dietz bit-trick)
//! contracts
//! (corresponds to the `impl<I> Average for I` blanket implementation of the
//!  upstream code/src/average.rs instantiated on i8 / u8 / i64 / u64;
//!  `&self`/`*other` become by-value machine parameters)
//!
//! The bitwise `&`, `^`, `>>` are uninterpreted symbols under the default z3
//! encoding; this verus build carries the dedicated `assert(...) by
//! (bit_vector)` solving mode, which discharges them. Encoding essentials
//! (the basis of this file's deployment):
//!   - a bit_vector assertion **does not inherit ambient definitional facts**: an
//!     exec bitwise let (`andv = x & y`) is a free variable inside the assertion,
//!     the identity is necessarily false -- the expressions of a bit-level
//!     assertion may only use **parameter-cast terms** (`x as u128`, `(x & y) as
//!     u128` etc., builtin machine function applications + casts, directly
//!     evaluable by bit blasting);
//!   - the machine equalities produced this way become trivial in default mode
//!     once bridged: in-range machine add/mul/cast bridging to int is automatic,
//!     and the definitional axioms of the exec lets then connect
//!     these int facts to the exec sites, discharging the `+`/`-` overflow
//!     obligations together with the ensures.
//!
//! Hence average_floor / average_ceil's **doc contracts discharge every
//! obligation on the full input domain**. The property itself is neither a
//! bug nor a doc distortion (UT 0.1.47 all-green agrees with this
//! conclusion); there is nothing to file.
//!
//! Doc contracts (code/src/average.rs:6-7 / :25-26):
//!   average_ceil  = ceil((self + other)/2) <=> normalized spec: r == (x+y+1)/2
//!   average_floor = floor((self + other)/2) <=> normalized spec: r == (x+y)/2
//! (the spec `/` is Euclidean, negative sums round down; ceil(S/2) <=>
//!  floor((S+1)/2) is a full-domain equivalence.)
//!
//! Bit-level identities (Dietz, Hacker's Delight; the upstream implementations
//! code/src/average.rs:56-58/62-64):
//!   floor: 2*((x&y) + ((x^y)>>1)) + ((x^y)&1) == x + y
//!   ceil : 2*((x|y) - ((x^y)>>1)) - ((x^y)&1) == x + y
//! Inside the 128-bit mirror the identity never wraps (|and+half| < 2^63 in
//! magnitude), provable at the bit level; the machine disjunctive fact
//! ((x^y)&1) in {0,1} is likewise given by bit_vector; once int-ized it is the
//! carry flag p, letting the two ensures fall out of the constant division of
//! S = 2r +/- p.
//!
//! The exec bodies stay verbatim transcriptions (the three lets are the direct
//! decomposition of the upstream one-liner, the kverus-migrate
//! "semantics-preserving rewrite keeping the source structure" convention).
//! Two-zone split: this file is the **src zone**
//! (the library contracts proper + the bit-level bridge fact source);
//! tests/average.rs's 48 examples and the doc-example assertion theorems live
//! in harness/average.rs referencing this file via `#[path]`.

use vstd::prelude::*;

verus! {

// =========================================================================
// 1. average_floor -- the u64 / i64 / u8 / i8 machine instances (upstream body :57)
// =========================================================================

/// u64 instance. The doc floor((x+y)/2) (average.rs:25-26) holds on the full domain; no panic face.
/// Upstream doc (average.rs:25-26; bracket glyphs normalized to ASCII):
///   Returns the floor value of the average of `self` and `other`.
///   -- floor((self + other)/2)
pub exec fn average_floor_upstream_u64(x: u64, y: u64) -> (r: u64)
    ensures
        r@ == (x@ + y@) / 2,
{
    let andv = x & y;          // src/average.rs:57, term one
    let xorv = x ^ y;
    let halfv = xorv >> 1;    // term two
    // Bit-level bridge (bit_vector: only parameter-cast terms; no reference to the exec lets)
    assert((x as u128) & (y as u128) == (x & y) as u128) by (bit_vector);
    assert((x as u128) ^ (y as u128) == (x ^ y) as u128) by (bit_vector);
    assert((((x as u128) ^ (y as u128)) >> 1) == ((x ^ y) >> 1) as u128) by (bit_vector);
    assert((((x as u128) ^ (y as u128)) & 1u128) == ((x ^ y) & 1) as u128) by (bit_vector);
    assert(
        2u128 * (((x as u128) & (y as u128)) + (((x as u128) ^ (y as u128)) >> 1))
            + (((x as u128) ^ (y as u128)) & 1u128)
            == (x as u128) + (y as u128)
    ) by (bit_vector);
    assert((x ^ y) & 1 == 0 || (x ^ y) & 1 == 1) by (bit_vector);
    // Int-ization: S = 2*(and+half) + p, p in {0,1} => and+half = (S-p)/2 < 2^64
    assert(andv@ + halfv@ < 0x1_0000_0000_0000_0000);
    let r = andv + halfv;     // <-- the former overflow-obligation site, now discharged
    assert(r@ == (x@ + y@) / 2);
    r
}

/// i64 instance. For negative sums the Euclid `/` == floor, identical to the doc
/// floor((x+y)/2) on the full domain (the doc examples `(-2).average_floor(&-5) == -4`,
/// `MIN.average_floor(&MAX) == -1` are instances of this postcondition -- see harness/average.rs).
/// Upstream doc (average.rs:25-26; bracket glyphs normalized to ASCII):
///   Returns the floor value of the average of `self` and `other`.
///   -- floor((self + other)/2)
pub exec fn average_floor_upstream_i64(x: i64, y: i64) -> (r: i64)
    ensures
        r@ == (x@ + y@) / 2,
{
    let andv = x & y;
    let xorv = x ^ y;
    let halfv = xorv >> 1;    // arithmetic shift right; the bit-level identity covers the sign bit
    assert((x as i128) & (y as i128) == (x & y) as i128) by (bit_vector);
    assert((x as i128) ^ (y as i128) == (x ^ y) as i128) by (bit_vector);
    assert((((x as i128) ^ (y as i128)) >> 1) == ((x ^ y) >> 1) as i128) by (bit_vector);
    assert((((x as i128) ^ (y as i128)) & 1) == ((x ^ y) & 1) as i128) by (bit_vector);
    assert(
        2 * (((x as i128) & (y as i128)) + (((x as i128) ^ (y as i128)) >> 1))
            + (((x as i128) ^ (y as i128)) & 1)
            == (x as i128) + (y as i128)
    ) by (bit_vector);
    assert((x ^ y) & 1 == 0 || (x ^ y) & 1 == 1) by (bit_vector);
    // Int-ization: S in [-2^64, 2^64-2] => and+half in [-2^63, 2^63-1]
    assert(-9223372036854775808 <= andv@ + halfv@ <= 9223372036854775807);
    let r = andv + halfv;
    assert(r@ == (x@ + y@) / 2);
    r
}

/// u8 instance (the source width of the doc examples :37-39).
/// Upstream doc (average.rs:25-26; bracket glyphs normalized to ASCII):
///   Returns the floor value of the average of `self` and `other`.
///   -- floor((self + other)/2)
pub exec fn average_floor_upstream_u8(x: u8, y: u8) -> (r: u8)
    ensures
        r@ == (x@ + y@) / 2,
{
    let andv = x & y;
    let xorv = x ^ y;
    let halfv = xorv >> 1;
    assert((x as u128) & (y as u128) == (x & y) as u128) by (bit_vector);
    assert((x as u128) ^ (y as u128) == (x ^ y) as u128) by (bit_vector);
    assert((((x as u128) ^ (y as u128)) >> 1) == ((x ^ y) >> 1) as u128) by (bit_vector);
    assert((((x as u128) ^ (y as u128)) & 1u128) == ((x ^ y) & 1) as u128) by (bit_vector);
    assert(
        2u128 * (((x as u128) & (y as u128)) + (((x as u128) ^ (y as u128)) >> 1))
            + (((x as u128) ^ (y as u128)) & 1u128)
            == (x as u128) + (y as u128)
    ) by (bit_vector);
    assert((x ^ y) & 1 == 0 || (x ^ y) & 1 == 1) by (bit_vector);
    assert(andv@ + halfv@ < 256);
    let r = andv + halfv;
    assert(r@ == (x@ + y@) / 2);
    r
}

/// i8 instance (the source width of the doc examples :15-20 / :38-39).
/// Upstream doc (average.rs:25-26; bracket glyphs normalized to ASCII):
///   Returns the floor value of the average of `self` and `other`.
///   -- floor((self + other)/2)
pub exec fn average_floor_upstream_i8(x: i8, y: i8) -> (r: i8)
    ensures
        r@ == (x@ + y@) / 2,
{
    let andv = x & y;
    let xorv = x ^ y;
    let halfv = xorv >> 1;
    assert((x as i128) & (y as i128) == (x & y) as i128) by (bit_vector);
    assert((x as i128) ^ (y as i128) == (x ^ y) as i128) by (bit_vector);
    assert((((x as i128) ^ (y as i128)) >> 1) == ((x ^ y) >> 1) as i128) by (bit_vector);
    assert((((x as i128) ^ (y as i128)) & 1) == ((x ^ y) & 1) as i128) by (bit_vector);
    assert(
        2 * (((x as i128) & (y as i128)) + (((x as i128) ^ (y as i128)) >> 1))
            + (((x as i128) ^ (y as i128)) & 1)
            == (x as i128) + (y as i128)
    ) by (bit_vector);
    assert((x ^ y) & 1 == 0 || (x ^ y) & 1 == 1) by (bit_vector);
    assert(-128 <= andv@ + halfv@ <= 127);
    let r = andv + halfv;
    assert(r@ == (x@ + y@) / 2);
    r
}

// =========================================================================
// 2. average_ceil -- the u64 / i64 / u8 / i8 machine instances (upstream body :63)
// =========================================================================

/// u64 instance. The doc ceil((x+y)/2) <=> (x+y+1)/2 (S even: same as S/2; S odd: rounds up -- a full-domain equivalence).
/// Upstream doc (average.rs:6-7; bracket glyphs normalized to ASCII):
///   Returns the ceiling value of the average of `self` and `other`.
///   -- ceil((self + other)/2)
pub exec fn average_ceil_upstream_u64(x: u64, y: u64) -> (r: u64)
    ensures
        r@ == (x@ + y@ + 1) / 2,
{
    let orv = x | y;           // src/average.rs:63, term one
    let xorv = x ^ y;
    let halfv = xorv >> 1;    // term two
    // Bit-level bridge
    assert((x as u128) | (y as u128) == (x | y) as u128) by (bit_vector);
    assert((x as u128) ^ (y as u128) == (x ^ y) as u128) by (bit_vector);
    assert((((x as u128) ^ (y as u128)) >> 1) == ((x ^ y) >> 1) as u128) by (bit_vector);
    assert((((x as u128) ^ (y as u128)) & 1u128) == ((x ^ y) & 1) as u128) by (bit_vector);
    // minuend >= subtrahend (bit level) => the u64 subtraction has no underflow
    assert(((x as u128) | (y as u128)) >= (((x as u128) ^ (y as u128)) >> 1)) by (bit_vector);
    assert(
        2u128 * (((x as u128) | (y as u128)) - (((x as u128) ^ (y as u128)) >> 1))
            == (x as u128) + (y as u128) + (((x as u128) ^ (y as u128)) & 1u128)
    ) by (bit_vector);
    assert((x ^ y) & 1 == 0 || (x ^ y) & 1 == 1) by (bit_vector);
    let r = orv - halfv;      // <-- the former underflow-obligation site, now discharged
    assert(r@ == (x@ + y@ + 1) / 2);
    r
}

/// i64 instance.
/// Upstream doc (average.rs:6-7; bracket glyphs normalized to ASCII):
///   Returns the ceiling value of the average of `self` and `other`.
///   -- ceil((self + other)/2)
pub exec fn average_ceil_upstream_i64(x: i64, y: i64) -> (r: i64)
    ensures
        r@ == (x@ + y@ + 1) / 2,
{
    let orv = x | y;
    let xorv = x ^ y;
    let halfv = xorv >> 1;
    assert((x as i128) | (y as i128) == (x | y) as i128) by (bit_vector);
    assert((x as i128) ^ (y as i128) == (x ^ y) as i128) by (bit_vector);
    assert((((x as i128) ^ (y as i128)) >> 1) == ((x ^ y) >> 1) as i128) by (bit_vector);
    assert((((x as i128) ^ (y as i128)) & 1) == ((x ^ y) & 1) as i128) by (bit_vector);
    // On the signed side o >= h does not hold (e.g. x=y=-2: o=-2 < h=0) -- the underflow obligation is
    // discharged by the int bound of the identity (r = (S+p)/2 in [MIN, MAX]), not by minuend >= subtrahend.
    assert(
        2 * (((x as i128) | (y as i128)) - (((x as i128) ^ (y as i128)) >> 1))
            == (x as i128) + (y as i128) + (((x as i128) ^ (y as i128)) & 1)
    ) by (bit_vector);
    assert((x ^ y) & 1 == 0 || (x ^ y) & 1 == 1) by (bit_vector);
    assert(-9223372036854775808 <= orv@ - halfv@ <= 9223372036854775807);
    let r = orv - halfv;
    assert(r@ == (x@ + y@ + 1) / 2);
    r
}

/// u8 instance (the source of the MAX neighborhood of the doc example :18).
/// Upstream doc (average.rs:6-7; bracket glyphs normalized to ASCII):
///   Returns the ceiling value of the average of `self` and `other`.
///   -- ceil((self + other)/2)
pub exec fn average_ceil_upstream_u8(x: u8, y: u8) -> (r: u8)
    ensures
        r@ == (x@ + y@ + 1) / 2,
{
    let orv = x | y;
    let xorv = x ^ y;
    let halfv = xorv >> 1;
    assert((x as u128) | (y as u128) == (x | y) as u128) by (bit_vector);
    assert((x as u128) ^ (y as u128) == (x ^ y) as u128) by (bit_vector);
    assert((((x as u128) ^ (y as u128)) >> 1) == ((x ^ y) >> 1) as u128) by (bit_vector);
    assert((((x as u128) ^ (y as u128)) & 1u128) == ((x ^ y) & 1) as u128) by (bit_vector);
    assert(((x as u128) | (y as u128)) >= (((x as u128) ^ (y as u128)) >> 1)) by (bit_vector);
    assert(
        2u128 * (((x as u128) | (y as u128)) - (((x as u128) ^ (y as u128)) >> 1))
            == (x as u128) + (y as u128) + (((x as u128) ^ (y as u128)) & 1u128)
    ) by (bit_vector);
    assert((x ^ y) & 1 == 0 || (x ^ y) & 1 == 1) by (bit_vector);
    let r = orv - halfv;
    assert(r@ == (x@ + y@ + 1) / 2);
    r
}

/// i8 instance (the source of the MIN neighborhood of the doc examples :19-20).
/// Upstream doc (average.rs:6-7; bracket glyphs normalized to ASCII):
///   Returns the ceiling value of the average of `self` and `other`.
///   -- ceil((self + other)/2)
pub exec fn average_ceil_upstream_i8(x: i8, y: i8) -> (r: i8)
    ensures
        r@ == (x@ + y@ + 1) / 2,
{
    let orv = x | y;
    let xorv = x ^ y;
    let halfv = xorv >> 1;
    assert((x as i128) | (y as i128) == (x | y) as i128) by (bit_vector);
    assert((x as i128) ^ (y as i128) == (x ^ y) as i128) by (bit_vector);
    assert((((x as i128) ^ (y as i128)) >> 1) == ((x ^ y) >> 1) as i128) by (bit_vector);
    assert((((x as i128) ^ (y as i128)) & 1) == ((x ^ y) & 1) as i128) by (bit_vector);
    // Signed side, same note as i64: the underflow obligation is discharged by the identity int bound (o >= h does not hold).
    assert(
        2 * (((x as i128) | (y as i128)) - (((x as i128) ^ (y as i128)) >> 1))
            == (x as i128) + (y as i128) + (((x as i128) ^ (y as i128)) & 1)
    ) by (bit_vector);
    assert((x ^ y) & 1 == 0 || (x ^ y) & 1 == 1) by (bit_vector);
    assert(-128 <= orv@ - halfv@ <= 127);
    let r = orv - halfv;
    assert(r@ == (x@ + y@ + 1) / 2);
    r
}

}

fn main() {}
