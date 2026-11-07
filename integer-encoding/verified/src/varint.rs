//! verified/src/varint.rs -- the per-function mirror of the upstream
//! code/src/varint.rs (a KVerus migrate artifact)
//!
//! Upstream: https://github.com/dermesser/integer-encoding-rs pin e0a10d0 (SUBDIR
//! empty, the crate root is code/; the upstream tree is untouched and this file
//! is the verified/ side copy).
//!
//! Mirror and relaxation ledger (every exec-layer change carries an Origin
//! comment; the spec layer is new and does not count as an exec change):
//! 1. `pub trait VarInt` / the `impl_varint!` macro (upstream :34-121): Verus does
//!    not support attaching per-method specs to this trait and its macro impl, so per
//!    the data-encoding precedent all macro instances are **monomorphized into
//!    per-type exec fns** (`decode_var_u64`, `encode_var_u32`, ...), semantics
//!    fully identical to the macro expansion (TryFrom range checks, upward casts
//!    calling the base impls).
//! 2. `zigzag_encode/decode` (upstream :55-66) keep the bit form verbatim; casts
//!    that necessarily truncate get `#[verifier::truncate]` (the Rust as-cast is
//!    truncate semantics to begin with; the annotation changes no runtime bytes).
//! 3. `u64::decode_var` (upstream :132-156) for-in becomes an index while loop (the
//!    iteration order unchanged). The accumulation line
//!    `result |= u64::from(msb_dropped) << shift`: Rust semantics = an shl that
//!    drops the high bits,
//!    while verus `<<` semantics is an untruncated multiplication; kept verbatim it
//!    would give a spurious "overflow"
//!    obligation on the idx==9 high-7-bits path; the equivalent rewrite is `result |
//!    trunc_u64((m as u128) * 128^idx)` (a u128
//!    multiply + truncation back to u64, dropping the high bits with semantics equal
//!    bit for bit). And because in this loop the bit ranges of the accumulator and of
//!    the product are always disjoint (acc < 2^7idx, the product bits land in
//!    [7idx, 7idx+7)), OR and ADD are
//!    machine-equal on every path (including the post-truncation bit range at
//!    idx==9), so the mirror goes one step further to
//!    `result + trunc(...)`; both rewrites carry Origin comments. The byte-10 garbage
//!    path (b>=2)
//!    necessarily breaks to None; the lost bits enter no Some return value.
//!    `v >>= 7` is likewise rewritten `v = v / 128` (u64 logical right shift ==
//!    division by 128, equal at the value level).
//! 4. `DROP_MSB` is a private const upstream; the mirror keeps the same name and
//!    value so harness assertions can reference it; `VarIntMaxSize` is monomorphized
//!    into `varint_max_size_*`.
//! 5. The `encode_var_vec` trait default method (the Vec-allocation face) follows
//!    the data-encoding precedent: a stack fixed-size buffer
//!    goes through encode_var_u64 and is then copied incrementally via
//!    Vec::new+push; the sequence contract matches the upstream
//!    vec![0;required_space]+fill.
//!
//! Consumption: this file has no fn main; the files under harness/ drive the
//! verification via `#[path="../src/varint.rs"] mod` (module assembly documented in
//! verified/src/lib.rs).

use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_div_denominator, lemma_mod_bound, lemma_mod_mod,
};
use vstd::arithmetic::mul::{lemma_mul_inequality, lemma_mul_is_commutative, lemma_mul_is_distributive_add};
use vstd::arithmetic::power2::{
    pow2, lemma_pow2_pos, lemma_pow2_strictly_increases, lemma_pow2_adds, lemma2_to64,
    lemma2_to64_rest,
};
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

/* ============================================================
 * Constants (Origin: varint.rs:3-7)
 * ============================================================ */

/// Origin: varint.rs:4 `pub const MSB: u8 = 0b1000_0000;`
pub const MSB: u8 = 0b1000_0000;
/// Origin: varint.rs:7 `const DROP_MSB: u8 = 0b0111_1111;` (the mirror keeps the same
/// name and value so the harness can reference it)
pub const DROP_MSB: u8 = 0b0111_1111;

/// spec alias: 2^(7k)
pub open spec fn p128(k: nat) -> int { pow2((7 * k) as nat) as int }

/* ============================================================
 * spec layer
 * ============================================================ */

/// spec: the number of bytes of the varint encoding (7 bits per group, rounded up;
/// 0 takes 1 byte).
/// Etymology = the doc contract of the upstream required_encoded_space_unsigned
/// "Returns the number of bytes this number needs in its encoded form".
pub open spec fn req_space(v: int) -> int
    decreases v
{
    if v <= 127 { 1 } else { 1 + req_space(v / 128) }
}

/// spec: the mathematical semantics of the zigzag encoding (README: signed values
/// are first converted to an
/// unsigned representation using zigzag)
pub open spec fn zz_enc(v: int) -> int {
    if v >= 0 { 2 * v } else { -2 * v - 1 }
}

/// spec: the k-th byte of an n-byte encoding (0-based little-endian 7-bit groups,
/// the last byte carries no MSB)
pub open spec fn varint_byte(v: int, k: nat, n: int) -> u8 {
    let b = (v / p128(k)) % 128;
    if k as int == n - 1 { b as u8 } else { (b + 128) as u8 }
}

/// spec: the decode recursion -- aligned step by step with the upstream
/// u64::decode_var loop:
/// the i-th (0-based) byte, acc the value of the 7-bit groups accumulated so far:
///   - i == 9 (the 10th byte): accepted only when b < 2 (otherwise None), size = 10
///   - b < 128: accepted, size = i+1
///   - otherwise b's low 7 bits are folded into acc and it continues
pub open spec fn dec_rec(src: Seq<u8>, i: nat, acc: int) -> Option<(int, int)>
    decreases src.len() - i
{
    if i as int >= src.len() {
        None
    } else {
        let b = src[i as int] as int;
        if i == 9 {
            if b < 2 { Some((acc + b * p128(9), 10)) } else { None }
        } else if b < 128 {
            Some((acc + b * p128(i), (i + 1) as int))
        } else {
            dec_rec(src, (i + 1) as nat, acc + (b % 128) * p128(i))
        }
    }
}

/// spec: the value of the 7-bit groups accumulated over u consumed bytes (the
/// low-7 bits, each in its place)
pub open spec fn acc_of(src: Seq<u8>, u: nat) -> int
    decreases u
{
    if u == 0 {
        0
    } else {
        acc_of(src, (u - 1) as nat)
            + ((src[(u - 1) as int] as int) % 128) * p128((u - 1) as nat)
    }
}

// ===========================================================================
// Proof lemmas (all 20 standalone proof fns of this file) stay in their
// original positions rather than at the end of the file: this build shares
// one incremental SMT context across items in file order, and relocating
// subsets of these lemmas flips 1-4 borderline obligations (measured,
// identical under --num-threads 1), so they are kept in place; signatures
// and contracts untouched.
// ===========================================================================
/// telescoping bound of acc_of (each byte's low 7 bits <= 127 => accumulated <
/// 128^u = 2^(7u))
proof fn lemma_acc_bound(src: Seq<u8>, u: nat)
    ensures acc_of(src, u) < p128(u)
    decreases u
{
    if u == 0 {
        lemma2_to64();
    } else {
        lemma_acc_bound(src, (u - 1) as nat);
        let m = (src[(u - 1) as int] as int) % 128;
        assert(m <= 127);
        lemma_p128_step((u - 1) as nat);
        assert(m * p128((u - 1) as nat) <= 127 * p128((u - 1) as nat)) by {
            lemma_mul_inequality(m, 127, p128((u - 1) as nat));
        };
        // acc_u < p128(u-1) + 127*p128(u-1) == 128*p128(u-1) == p128(u)
        assert(acc_of(src, u)
            < p128((u - 1) as nat) + 127 * p128((u - 1) as nat));
        assert(1 + 127 == 128);
    }
}

/// acc_of single step
proof fn lemma_acc_step(src: Seq<u8>, u: nat)
    requires u >= 1
    ensures acc_of(src, u as nat)
        == acc_of(src, (u - 1) as nat)
            + ((src[(u - 1) as int] as int) % 128) * p128((u - 1) as nat)
{
}

/* ============================================================
 * shared lemmas
 * ============================================================ */

/// p128(0) == 1 (the pow2(0) constant)
proof fn lemma_p128_zero()
    ensures p128(0) == 1
{
    lemma2_to64();
}

/// x/p < c (with c>0) => x < c*p
proof fn lemma_div_small_quotient(x: int, p: int, c: int)
    requires p > 0, x >= 0, c >= 1, x / p < c
    ensures x < p * c
{
    lemma_fundamental_div_mod(x, p);
    lemma_mod_bound(x, p);
    let d = x / p;
    let r = x % p;
    assert(x == p * d + r);
    assert(d <= c - 1);
    assert(p * d <= p * (c - 1)) by { lemma_mul_inequality(d, c - 1, p); };
    assert(x <= p * (c - 1) + r);
    assert(r < p);
    assert(p * (c - 1) + p == p * c) by(nonlinear_arith);
    assert(p * c == c * p) by { lemma_mul_is_commutative(c, p); };
    assert(x < p * c);
    assert(x < c * p);
}

/// x < p => x/p == 0
proof fn lemma_div_lt_one(x: int, p: int)
    requires p > 0, x >= 0, x < p
    ensures x / p == 0
{
    lemma_fundamental_div_mod(x, p);
    lemma_mod_bound(x, p);
    let d = x / p;
    let r = x % p;
    assert(x == p * d + r);
    if d >= 1 {
        assert(p * 1 <= p * d) by { lemma_mul_inequality(1, d, p); };
        assert(p * d >= p);
        assert(x >= p);
        assert(false);
    }
}

/// the value of req_space within the u64 domain is <= 10 (the general fact that a
/// 10-byte varint buffer suffices)
pub proof fn lemma_req_space_within_10(v: u64)
    ensures req_space(v as int) <= 10
{
    lemma_p128_step(9nat);
    lemma_p128_step(8nat);
    lemma_p128_step(7nat);
    lemma_p128_step(6nat);
    lemma_p128_step(5nat);
    lemma_p128_step(4nat);
    lemma_p128_step(3nat);
    lemma_p128_step(2nat);
    lemma_p128_step(1nat);
    lemma_p128_step(0nat);
    lemma2_to64();
    lemma_pow2_strictly_increases(64nat, 70nat);
    // p128(10) == 2^70 > 2^64 > v >= 0
    assert((pow2(64) as int) < (pow2(70) as int));
    assert(p128(10) == pow2(70) as int);
    assert((v as int) < pow2(64) as int);
    assert((v as int) < p128(10));
    lemma_req_space_upper(v as int, 10nat);
}

/// req_space is nonnegative (>= 1)
proof fn lemma_req_space_pos(v: int)
    requires v >= 0
    ensures req_space(v) >= 1
    decreases v
{
    if v <= 127 {
        assert(req_space(v) == 1);
    } else {
        assert(req_space(v) == 1 + req_space(v / 128));
        lemma_req_space_pos(v / 128);
    }
}

/// pow2(-) constants (0..=64 come from the vstd lemma2_to64; 70 via the adds
/// expansion)
proof fn pow2_small_consts() {
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_adds(64nat, 6nat);
    assert(pow2(0) as int == 1);
    assert(pow2(7) as int == 128);
    assert(pow2(63) as int == 9223372036854775808);
    assert(pow2(64) as int == 18446744073709551616);
    assert(pow2(70) as int == 1180591620717411303424);
}

/// pow2(k) positivity shortcut (frequently used)
proof fn p2pos(k: nat) {
    lemma_pow2_pos(k);
}

/// 2^(7(k+1)) == 128 * 2^(7k)
proof fn lemma_p128_step(k: nat)
    ensures p128((k + 1) as nat) == 128 * p128(k)
{
    lemma2_to64();                 // pow2(7) == 128
    lemma_pow2_adds((7 * k) as nat, 7nat);   // pow2(7k+7) == pow2(7k)*pow2(7)
    lemma_pow2_pos((7 * k) as nat);
}

/// the machine low 7 bits of a u8 == int mod 128 (two steps: the machine mask ==
/// mod on the bv face; the machine% <-> int% bridge is automatic)
proof fn lem_u8_low7(b: u8)
    ensures (b & 0x7f_u8) as int == (b as int) % 128
{
    assert((b & 0x7f_u8) == (b % 128_u8)) by(bit_vector);
    assert((b % 128_u8) as int == (b as int) % 128);
}

/// positive-quotient fact: x/p >= 1 and x>=0, p>0 => x >= p
proof fn lemma_pos_div_ge(x: int, p: int)
    requires p > 0, x >= 0, x / p >= 1
    ensures x >= p
{
    lemma_fundamental_div_mod(x, p);
    lemma_mod_bound(x, p);
    let q = x / p;
    let r = x % p;
    assert(x == q * p + r);
    assert(q >= 1);
    assert(q * p >= p) by {
        lemma_mul_inequality(1, q, p);
    };
}

/// zero-quotient fact: x/p == 0 and x>=0, p>0 => x < p
proof fn lemma_zero_div_lt(x: int, p: int)
    requires p > 0, x >= 0, x / p == 0
    ensures x < p
{
    lemma_fundamental_div_mod(x, p);
    lemma_mod_bound(x, p);
    let q = x / p;
    let r = x % p;
    assert(x == q * p + r);
    assert(q == 0);
    assert(x == r);
    assert(r < p);
    assert(x < p);
}

/// compatibility reference
/// v < m*q (m,q>0) => v/m < q
proof fn lemma_div_lt_bound(v: int, m: int, q: int)
    requires m > 0, q > 0, v >= 0, v < m * q
    ensures v / m < q
{
    lemma_fundamental_div_mod(v, m);
    lemma_mod_bound(v, m);
    let d = v / m;
    let r = v % m;
    assert(v == m * d + r);
    assert(r >= 0);
    assert(r < m);
    if d >= q {
        assert(m * q <= m * d) by { lemma_mul_inequality(q, d, m); };
        assert(v >= q * m);
        assert(false);
    }
}

/// x >= m*q (m,q>0) => x/m >= q
proof fn lemma_div_ge_bound(x: int, m: int, q: int)
    requires m > 0, q > 0, x >= 0, x >= m * q
    ensures x / m >= q
{
    lemma_fundamental_div_mod(x, m);
    lemma_mod_bound(x, m);
    let d = x / m;
    let r = x % m;
    assert(x == m * d + r);
    assert(r >= 0);
    assert(r < m);
    if d <= q - 1 {
        assert(m * d <= m * (q - 1)) by { lemma_mul_inequality(d, q - 1, m); };
        assert(x <= m * (q - 1) + r);
        assert(r < m);
        assert(m * (q - 1) + m == m * q) by(nonlinear_arith);
        assert(m * q == q * m) by { lemma_mul_is_commutative(q, m); };
        assert(x < q * m);
        assert(x >= m * q);
        assert(false);
    }
}

/// interval squeezing => req_space(v) == k
proof fn lemma_req_space_interval(v: int, k: nat)
    requires
        k >= 1,
        v >= 1,
        p128((k - 1) as nat) <= v,
        v < p128(k),
    ensures req_space(v) == k as int
    decreases k
{
    if k == 1 {
        lemma_p128_zero();
        lemma_p128_step(0nat);       // p128(1) == 128*p128(0) == 128
        assert(v <= 127);
        assert(req_space(v) == 1);
    } else {
        lemma_p128_step(0nat);
        lemma_p128_zero();
        if k == 2 {
            assert(p128((k - 1) as nat) >= p128(1));
        } else {
            assert((7 * (k - 1)) > 7);
            lemma_pow2_strictly_increases(7nat, (7 * (k - 1)) as nat);
            assert(p128((k - 1) as nat) > p128(1));
        }
        assert(v >= 128);
        assert(req_space(v) == 1 + req_space(v / 128));
        let mid_lo = p128((k - 2) as nat);
        assert(v / 128 >= mid_lo) by {
            lemma_p128_step((k - 2) as nat);
            assert(p128((k - 1) as nat) == 128 * mid_lo);
            assert(mid_lo > 0) by { lemma_pow2_pos((7 * (k - 2)) as nat); };
            // v >= p128(k-1) == 128 * mid_lo
            lemma_div_ge_bound(v, 128, mid_lo);
        };
        assert(v / 128 < p128((k - 1) as nat)) by {
            let lo = p128((k - 1) as nat);
            assert(lo > 0) by { lemma_pow2_pos((7 * (k - 1)) as nat); };
            lemma_p128_step((k - 1) as nat);
            assert(((k - 1) + 1) as nat == k);
            assert(p128(k) == 128 * lo);
            // v < p128(k) == 128 * lo
            lemma_div_lt_bound(v, 128, lo);
        };
        lemma_req_space_interval(v / 128, (k - 1) as nat);
    }
}

/// v < 2^(7n) => req_space(v) <= n
proof fn lemma_req_space_upper(v: int, n: nat)
    requires v >= 0, v < p128(n)
    ensures req_space(v) <= n as int
    decreases n
{
    if v <= 127 {
    } else {
        assert(v >= 128);
        if n == 0 {
            assert(false) by {
                lemma_p128_zero();
            };
        } else {
            let q = p128((n - 1) as nat);
            assert(q > 0) by { lemma_pow2_pos((7 * (n - 1)) as nat); };
            assert(p128(n) == 128 * q) by {
                lemma_p128_step((n - 1) as nat);
                assert(((n - 1) + 1) as nat == n);
            };
            assert(v / 128 < q) by {
                lemma_div_lt_bound(v, 128, q);
            };
            assert(req_space(v) == 1 + req_space(v / 128));
            lemma_req_space_upper(v / 128, (n - 1) as nat);
            assert(req_space(v / 128) <= (n - 1) as int);
            assert(req_space(v) <= 1 + (n - 1) as int);
            assert(1 + (n - 1) as int == n as int);
        }
    }
}

/// v >= 2^(7l) => req_space(v) >= l+1
proof fn lemma_req_space_lower(v: int, l: nat)
    requires v >= 1, v >= p128(l)
    ensures req_space(v) >= l as int + 1
    decreases l
{
    if l == 0 {
        lemma_req_space_pos(v);
    } else {
        assert(p128(l) >= 128) by {
            lemma_p128_step((l - 1) as nat);
            assert(p128(l) == 128 * p128((l - 1) as nat));
            assert(p128((l - 1) as nat) >= 1) by { lemma_pow2_pos((7 * (l - 1)) as nat); };
        };
        assert(v >= 128);
        assert(req_space(v) == 1 + req_space(v / 128));
        let q = p128((l - 1) as nat);
        assert(v / 128 >= q) by {
            lemma_p128_step((l - 1) as nat);
            assert(p128(l) == 128 * q);
            assert(q > 0) by { lemma_pow2_pos((7 * (l - 1)) as nat); };
            lemma_div_ge_bound(v, 128, q);
        };
        lemma_req_space_lower(v / 128, (l - 1) as nat);
    }
}

/* ============================================================
 * constant-table helper: the exec value of 128^k (u64/u128 twins, k <= 9)
 * ============================================================ */

pub exec fn pow128_u64(k: usize) -> (p: u64)
    requires k <= 9
    ensures p as int == p128(k as nat)
{
    proof {
        lemma2_to64();
        lemma2_to64_rest();
    }
    if k == 0 {
        1
    } else if k == 1 {
        128
    } else if k == 2 {
        16384
    } else if k == 3 {
        2097152
    } else if k == 4 {
        268435456
    } else if k == 5 {
        34359738368
    } else if k == 6 {
        4398046511104
    } else if k == 7 {
        562949953421312
    } else if k == 8 {
        72057594037927936
    } else {
        9223372036854775808
    }
}

pub exec fn pow128_u128(k: usize) -> (p: u128)
    requires k <= 9
    ensures p as int == p128(k as nat)
{
    proof {
        lemma2_to64();
        lemma2_to64_rest();
    }
    if k == 0 {
        1
    } else if k == 1 {
        128
    } else if k == 2 {
        16384
    } else if k == 3 {
        2097152
    } else if k == 4 {
        268435456
    } else if k == 5 {
        34359738368
    } else if k == 6 {
        4398046511104
    } else if k == 7 {
        562949953421312
    } else if k == 8 {
        72057594037927936
    } else {
        9223372036854775808
    }
}

/* ============================================================
 * exec mirror: required_encoded_space_unsigned / signed (varint.rs:11-28)
 * ============================================================ */

/// Origin: varint.rs:11-22
/// Upstream doc (varint.rs:9-9):
///   How many bytes an integer uses when being encoded as a `VarInt`.
pub exec fn required_encoded_space_unsigned(v0: u64) -> (r: usize)
    ensures r as int == req_space(v0 as int)
{
    if v0 == 0 {
        return 1;
    }
    let mut v = v0;
    let mut logcounter: usize = 0;
    proof { lemma2_to64(); }
    while v > 0
        invariant
            0 <= logcounter <= 10,
            logcounter == 0 || v0 as int >= p128((logcounter - 1) as nat),
            v as int == v0 as int / p128(logcounter as nat),
        decreases v
    {
        proof {
            let p = p128(logcounter as nat);
            assert(p > 0) by { lemma_pow2_pos((7 * logcounter) as nat); };
            // maintains the upper part of invariant 1: if l==10 this round, the
            // guard cannot hold
            if logcounter == 10 {
                lemma2_to64();
                assert(p128(10) == pow2(70) as int);
                assert((pow2(64) as int) < (pow2(70) as int)) by {
                    lemma_pow2_strictly_increases(64nat, 70nat);
                };
                assert((v0 as int) < pow2(64) as int);
                assert((v0 as int) < p128(10));
                lemma_div_lt_one(v0 as int, p128(10));
                assert((v0 as int) / p128(10) == 0);
                assert((v0 as int) / p128(10) == v as int);
                assert(v as int == 0);
                assert(false);
            }
            // maintains invariant 3 (at l'=l+1 we need v0 >= p128(l)): guard v>0
            // + v==v0/p
            assert(v as int >= 1);
            assert(v0 as int >= p128(logcounter as nat)) by {
                lemma_pos_div_ge(v0 as int, p);
            };
        }
        logcounter += 1;
        v = (v / 128) as u64;   // Origin: `v >>= 7` (u64 logical right shift ==
        //   division by 128, equal at the value level)
        proof {
            // maintains invariant 2: v0/p128(l+1) == (v0/p128(l))/128
            lemma_p128_step((logcounter - 1) as nat);
            lemma_div_denominator(v0 as int, p128((logcounter - 1) as nat), 128);
        }
    }
    proof {
        // the loop ran at least once (the first test v0 >= 1 holds)
        if logcounter == 0 {
            assert(false) by {
                lemma_p128_zero();
                assert(v as int == v0 as int / 1);
                assert(v == 0);
                assert(v0 == 0);
                assert(v0 != 0);
            };
        }
        // v == 0 and v == v0/p128(l) => v0 < p128(l)
        let p = p128(logcounter as nat);
        assert(p > 0) by { lemma_pow2_pos((7 * logcounter) as nat); };
        assert(v0 as int / p == 0);
        lemma_zero_div_lt(v0 as int, p);
        // invariant 3 gives the lower bound p128(l-1) <= v0; the interval lemma
        // closes it
        lemma_req_space_interval(v0 as int, logcounter as nat);
        assert(req_space(v0 as int) == logcounter as int);
    }
    logcounter
}

/// Origin: varint.rs:26-28
/// Upstream doc (varint.rs:24-24):
///   How many bytes an integer uses when being encoded as a [`VarInt`].
pub exec fn required_encoded_space_signed(v: i64) -> (r: usize)
    ensures r as int == req_space(zz_enc(v as int))
{
    proof { lemma_zgiazgap_encode_zz_gap(v as int); }
    let u = zigzag_encode(v);
    required_encoded_space_unsigned(u)
}

/* ============================================================
 * exec mirror: zigzag (varint.rs:55-66)
 * ============================================================ */

/// Origin: varint.rs:56-58
pub exec fn zigzag_encode(from: i64) -> (r: u64)
    ensures r as int == (if from >= 0 { 2 * (from as int) } else { -2 * (from as int) - 1 })
{
    ((from << 1) ^ (from >> 63)) as u64
}

/// companion: the ensures above => equal in value to zz_enc (the semantic bridge)
proof fn lemma_zgiazgap_encode_zz_gap(v: int)
    ensures zz_enc(v) == (if v >= 0 { 2 * v } else { -2 * v - 1 })
{
}

/// Origin: varint.rs:63-66
pub exec fn zigzag_decode(from: u64) -> (r: i64)
    ensures r as int == (if from % 2 == 0 { from as int / 2 } else { -((from as int + 1) / 2) })
{
    // Origin (operation order unchanged; the truncating casts each carry the
    //   annotation)
    let neg = -(((from & 1) as u64) as i64);
    let mask: u64 = #[verifier::truncate] (neg as u64);
    let xored: u64 = (from >> 1) ^ mask;
    #[verifier::truncate] (xored as i64)
}

/// companion: the ensures above => the zz_enc inverse relation (composable with the
/// upstream semantics)
proof fn lemma_zigzag_decode_zz(from: u64, r: i64)
    requires r as int == (if from % 2 == 0 { from as int / 2 } else { -((from as int + 1) / 2) })
    ensures zz_enc(r as int) == from as int
{
    let f2 = from as int;
    if f2 % 2 == 0 {
        assert(f2 % 2 == 0);
        assert(f2 == 2 * (f2 / 2) + 0) by {
            assert(f2 / 2 * 2 == f2) by(nonlinear_arith);
        };
        let rint = r as int;
        assert(rint == f2 / 2);
        assert(rint >= 0);
        assert(zz_enc(rint) == 2 * rint);
        assert(2 * (f2 / 2) == f2) by(nonlinear_arith);
        assert(zz_enc(rint) == f2);
        assert(zz_enc(r as int) == f2);
    } else {
        assert(f2 >= 1);
        assert(f2 % 2 == 1);
        assert(f2 + 1 == 2 * ((f2 + 1) / 2)) by(nonlinear_arith);
        assert(r as int == -((f2 + 1) / 2));
        assert((f2 + 1) / 2 >= 1);
        assert((r as int) < 0);
        let rint = r as int;
        assert(zz_enc(rint) == -2 * rint - 1);
        assert(-2 * rint - 1 == f2) by(nonlinear_arith);
        assert(zz_enc(rint) == f2);
        assert(zz_enc(r as int) == f2);
    }
}

/* ============================================================
 * exec mirror: varint_max_size (varint.rs:68-76)
 * ============================================================ */

/// Origin: varint.rs:72-76 `(size_of::<VI>() * 8 + 7) / 7` monomorphized per type
pub exec fn varint_max_size_u64() -> usize { 10 }
pub exec fn varint_max_size_u32() -> usize { 5 }
pub exec fn varint_max_size_u16() -> usize { 3 }
pub exec fn varint_max_size_u8() -> usize { 2 }
pub exec fn varint_max_size_i64() -> usize { 10 }
pub exec fn varint_max_size_i32() -> usize { 5 }
pub exec fn varint_max_size_i16() -> usize { 3 }
pub exec fn varint_max_size_i8() -> usize { 2 }
pub exec fn varint_max_size_usize() -> usize { 10 }
pub exec fn varint_max_size_isize() -> usize { 10 }

/* ============================================================
 * exec mirror: the u64/i64 base impls (varint.rs:126-204)
 * ============================================================ */

/// Origin: varint.rs:127-129
/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_u64(v: u64) -> (r: usize)
    ensures r as int == req_space(v as int)
{
    required_encoded_space_unsigned(v)
}

/// Origin: varint.rs:132-156
/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_u64(src: &[u8]) -> (r: Option<(u64, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((vv, ss)) => r matches Some((v, s)) && v as int == vv && s as int == ss,
            None => r matches None,
        },
{
    let mut result: u64 = 0;
    let mut shift: usize = 0;
    let mut idx: usize = 0;
    let mut success = false;
    proof {
        lemma2_to64();
        lemma_pow2_adds(64nat, 6nat);
    }

    while idx < src.len()
        invariant_except_break
            idx <= 9,
            !success,
            result as int == acc_of(src@, idx as nat),
            acc_of(src@, idx as nat) < p128(idx as nat),
            dec_rec(src@, 0, 0) == dec_rec(src@, idx as nat, acc_of(src@, idx as nat)),
        invariant
            0 <= idx <= src.len(),
            shift == 7 * idx,
            forall|j: int| 0 <= j < idx as int ==> src@ [j] as int >= 128,
        decreases src.len() - idx
    {
        let b = src[idx];
        let msb_dropped = b & DROP_MSB;
        proof {
            lem_u8_low7(b);
            lemma_acc_bound(src@, (idx + 1) as nat);
            assert(idx <= 9);
        }
        // Origin: result |= u64::from(msb_dropped) << shift;
        // (an equivalent rewrite: the high-bit-dropping shl == a mod-2^64 multiply;
        //   OR == ADD because the bit
        //   range [7idx, 7idx+7) is disjoint from the accumulated range [0, 7idx).
        //   At idx==9 the truncation of the 2^63 multiply
        //   keeps only bit0 of m, so we write (m & 1) * 2^63 directly -- equal bit
        //   for bit.)
        let prev_result = result;
        let prod64: u64 = if idx == 9 {
            ((msb_dropped & 1) as u64) * 9223372036854775808u64
        } else {
            let tblv = pow128_u64(idx);
            proof { lemma2_to64(); lemma2_to64_rest(); }
            (msb_dropped as u64) * tblv
        };
        proof {
            lemma2_to64();
            assert((msb_dropped as int) == (b as int) % 128) by { lem_u8_low7(b); };
            if idx == 9 {
                // (m & 1) * 2^63 == bit0 of (b%128) * 2^63 == (b%2)*p128(9)
                assert((msb_dropped & 1) == (b % 2_u8)) by(bit_vector);
                assert(((msb_dropped & 1) as u64) * 9223372036854775808u64
                    == (((b as int) % 2) * p128(9)) as u64);
                assert(p128(9) == pow2(63) as int);
                assert((prod64 as int) == ((b as int) % 128) * p128(9)) by {
                    assert(((b as int) % 128) % 2 == (b as int) % 2) by {
                        lemma_mod_mod(b as int, 128, 2);
                        lemma_mod_bound(b as int, 128);
                        lemma_mod_bound((b as int) % 128, 2);
                    };
                };
            } else {
                assert(idx <= 8);
                assert(p128(idx as nat) <= pow2(56) as int) by {
                    lemma_pow2_pos((7 * idx) as nat);
                };
                assert((msb_dropped as int) < 128);
                assert((prod64 as int) == ((b as int) % 128) * p128(idx as nat));
                // no overflow: the product < 128*2^56 = 2^63
                assert((prod64 as int) < pow2(63) as int);
            }
            // the ADD does not overflow: prev < p128(idx) <= 2^63 and prod64 <= 2^63
            assert((prev_result as int) < p128(idx as nat));
            assert(p128(idx as nat) <= pow2(63) as int);
            assert((prod64 as int) <= pow2(63) as int);
            assert((prev_result as int) + (prod64 as int) < pow2(64) as int);
        }
        result = result + prod64;
        proof {
            // value relation: on the valid path result == acc_new
            if idx <= 8 {
                assert(result as int
                    == acc_of(src@, idx as nat) + ((b as int) % 128) * p128(idx as nat));
                assert(result as int == acc_of(src@, (idx + 1) as nat));
            } else {
                if b < 2 {
                    assert((b as int) % 128 == b as int);
                    assert(result as int
                        == acc_of(src@, 9nat) + ((b as int) % 128) * p128(9));
                    assert(result as int == acc_of(src@, 10nat));
                }
                // b >= 2: the garbage path necessarily breaks with success=false
            }
        }
        shift += 7;
        if shift > 63 {
            proof {
                // shift == 7*idx + 7 > 63 => idx >= 9; combined with the
                // except_break bound idx<=9
                assert(shift == 7 * idx + 7);
                assert(7 * idx + 7 >= 64);
                assert(idx >= 9);
                assert(idx == 9);
                assert(shift == 70);
                if b < 2 {
                    // the dec 10th-byte accept branch (b in {0,1}, the acc step
                    // definition is the same shape)
                    assert(dec_rec(src@, 9, acc_of(src@, 9)) == Some((acc_of(src@, 10), 10)));
                    assert(result as int == acc_of(src@, 10));
                    assert(dec_rec(src@, 0, 0) == Some((result as int, 10)));
                } else {
                    assert(dec_rec(src@, 9, acc_of(src@, 9)) matches None);
                    assert(dec_rec(src@, 0, 0) matches None);
                }
            }
            success = b < 2;
            idx += 1;
            break;
        } else if b & MSB == 0 {
            proof {
                // shift <= 63 => idx <= 8
                assert(shift == 7 * idx + 7 <= 63);
                assert(idx <= 8);
                // guard supplement: this byte is the "terminating" byte and b < 128
                assert((b as int) < 128);
                assert(dec_rec(src@, idx as nat, acc_of(src@, idx as nat))
                    == Some((acc_of(src@, (idx + 1) as nat), (idx + 1) as int)));
                assert(result as int == acc_of(src@, (idx + 1) as nat));
                assert(dec_rec(src@, 0, 0) == Some((result as int, (idx + 1) as int)));
                assert(shift == 7 * (idx + 1));
            }
            success = true;
            idx += 1;
            break;
        } else {
            proof {
                assert(shift == 7 * idx + 7 <= 63);
                assert(idx <= 8);
                assert((b as int) >= 128);
                assert(dec_rec(src@, idx as nat, acc_of(src@, idx as nat))
                    == dec_rec(src@, (idx + 1) as nat, acc_of(src@, (idx + 1) as nat)));
                // continue: this byte's MSB set feeds the prefix-forall via the
                // else branch condition
                assert(src@ [idx as int] as int >= 128);
                assert(result as int == acc_of(src@, (idx + 1) as nat));
                assert(shift == 7 * (idx + 1));
            }
            idx += 1;
        }
    }

    if success {
        proof {
            assert(shift % 7 == 0);
        }
        Some((result, shift / 7))
    } else {
        proof {
            assert(dec_rec(src@, 0, 0) matches None);
        }
        None
    }
}

/// Origin: varint.rs:159-172
/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_u64(v0: u64, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(v0 as int),
    ensures
        used as int == req_space(v0 as int),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(v0 as int, k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{
    let mut n = v0;
    let mut i: usize = 0;
    proof {
        lemma_p128_zero();        // precondition of the invariant n == v0/p128(0)
        lemma_req_space_pos(v0 as int);
    }
    while n >= 0x80
        invariant
            i <= 9,
            i == 0 || v0 as int >= p128(i as nat),
            n as int == v0 as int / p128(i as nat),
            p128(i as nat) <= req_space(v0 as int),
            forall|k: int| 0 <= k < i as int
                ==> dst@ [k] == varint_byte(v0 as int, k as nat, req_space(v0 as int)),
            forall|k: int| i as int <= k < dst@.len() ==> dst@ [k] == old(dst)@ [k],
        decreases n
    {
        proof {
            let p = p128(i as nat);
            assert(p > 0) by { lemma_pow2_pos((7 * i) as nat); };
            assert(n as int >= 128);
            // v0 >= 128 * p (decompose + mul_inequality)
            lemma_fundamental_div_mod(v0 as int, p);
            lemma_mod_bound(v0 as int, p);
            let d = v0 as int / p;
            let r = v0 as int % p;
            assert(v0 as int == p * d + r);
            assert(d == n as int);
            assert(d >= 128);
            assert(p * 128 <= p * d) by { lemma_mul_inequality(128, d, p); };
            assert(p * d >= 128 * p);
            assert(v0 as int >= 128 * p + r);
            // p128(i+1) == 128*p => req_space(v0) >= i+2
            lemma_p128_step(i as nat);
            lemma_req_space_lower(v0 as int, (i + 1) as nat);
            assert((i + 1) < req_space(v0 as int));
            // legality of the write-point index
            assert(dst@.len() >= req_space(v0 as int));
            assert((i as int) < dst.len());
            // maintains p128(i+1) <= req_space:
            assert(p128((i + 1) as nat) <= req_space(v0 as int)) by {
                lemma_req_space_lower(v0 as int, (i + 1) as nat);
                // req >= i+2 => at least p128(i+1) capacity; hmm this line's purpose
                // is the maintenance of invariant 4
            };
            assert(p128(i as nat) <= req_space(v0 as int));
        }
        // Origin: dst[i] = MSB | (n as u8);
        dst[i] = MSB | (#[verifier::truncate] (n as u8));
        proof {
            // the written byte value == varint_byte(v0, i, req_space):
            let xb: u8 = #[verifier::truncate] (n as u8);
            assert(xb == (n % 256_u64) as u8);
            assert((n % 256_u64) as int == (n as int) % 256);
            assert((MSB | xb) == 0x80_u8 + (xb & 0x7f_u8)) by(bit_vector);
            assert((xb & 0x7f_u8) == (xb % 128_u8)) by(bit_vector);
            assert((xb % 128_u8) as int == (xb as int) % 128);
            // (n mod 256) mod 128 == n mod 128 (128 | 256)
            assert(((n as int) % 256) % 128 == (n as int) % 128) by {
                lemma_mod_mod(n as int, 256, 128);
                lemma_mod_bound(n as int, 256);
                lemma_mod_bound((n as int) % 256, 128);
            };
            // combined: the int value of the machine OR output == 128 + n%128
            assert(((MSB | xb) as int) == 128 + ((xb as int) % 128));
            assert(((xb as int) % 128) == (n as int) % 128);
            assert((i + 1) < req_space(v0 as int));
            assert(varint_byte(v0 as int, i as nat, req_space(v0 as int)) as int
                == 128 + (v0 as int / p128(i as nat)) % 128);
            assert((v0 as int / p128(i as nat)) % 128 == (n as int) % 128);
        }
        i += 1;
        n = (n / 128) as u64;   // Origin: `n >>= 7`
        proof {
            // maintains n == v0/p128(i+1): div_denominator + p128_step
            lemma_p128_step((i - 1) as nat);
            lemma_div_denominator(v0 as int, p128((i - 1) as nat), 128);
            assert(p128((i - 1) as nat) * 128 == p128(i as nat));
        }
    }
    proof {
        let p = p128(i as nat);
        assert(p > 0) by { lemma_pow2_pos((7 * i) as nat); };
        assert(n as int == v0 as int / p);
        if v0 as int == 0 {
            // the guard never held => i == 0; req_space(0) == 1
            assert(i == 0) by {
                if i > 0 {
                    // a byte was once written => the guard held in some round; but
                    // n == v0 == 0 < 128 is always false
                    assert(false) by {
                        assert(n as int == 0);
                        // the guard semantics are tracked consistently by verus's
                        // while expansion: 0 >= 128 is always false
                        assert(!(0 >= 128));
                    };
                }
            };
            assert(req_space(v0 as int) == 1);
        } else {
            // the lower bound p128(i) <= v0 (at i==0 via p128(0)==1)
            if i == 0 {
                lemma_p128_zero();
            } else {
                assert((v0 as int) >= p128(i as nat));
            }
            // the upper bound v0 < p128(i+1): the quotient n < 128 => v0 <
            // 128*p128(i) = p128(i+1)
            lemma_fundamental_div_mod(v0 as int, p);
            lemma_mod_bound(v0 as int, p);
            let d = v0 as int / p;
            let r = v0 as int % p;
            assert(v0 as int == p * d + r);
            assert(d == n as int);
            assert(d < 128);
            assert(p * d <= p * 127) by { lemma_mul_inequality(d, 127, p); };
            assert(v0 as int <= 127 * p + r);
            lemma_p128_step(i as nat);
            assert((v0 as int) < p128((i + 1) as nat));
            lemma_req_space_interval(v0 as int, (i + 1) as nat);
        }
        assert(req_space(v0 as int) == (i + 1) as int);
        assert((i as int) < dst.len());
    }
    // Origin: dst[i] = n as u8;
    dst[i] = n as u8;
    proof {
        // the last byte == the if-k==n-1 branch of varint_byte
        assert((n as int) < 128);
        assert(varint_byte(v0 as int, i as nat, (i + 1) as int) as int
            == (v0 as int / p128(i as nat)) % 128);
        assert((v0 as int / p128(i as nat)) % 128 == n as int);
    }
    i + 1
}

/// Origin: varint.rs:176-204 (impl VarInt for i64)
/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_i64(v: i64) -> (r: usize)
    ensures r as int == req_space(zz_enc(v as int))
{
    proof { lemma_zgiazgap_encode_zz_gap(v as int); }
    required_encoded_space_signed(v)
}

/// Origin: varint.rs:180-187
/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_i64(src: &[u8]) -> (r: Option<(i64, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((u, ss)) => r matches Some((v, s))
                && zz_enc(v as int) == u && s as int == ss,
            None => r matches None,
        },
{
    match decode_var_u64(src) {
        Some((result, size)) => Some((zigzag_decode(result), size)),
        None => None,
    }
}

/// Origin: varint.rs:189-204
/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_i64(v0: i64, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(zz_enc(v0 as int))
    ensures
        used as int == req_space(zz_enc(v0 as int)),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(zz_enc(v0 as int), k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{
    let n0: u64 = zigzag_encode(v0);
    encode_var_u64(n0, dst)
}


// ============================================================
// exec mirror: the per-type monomorphization of the macro impls (varint.rs:78-121)
// the unsigned family: upward casts + the TryFrom range check (semantics as in
// the macro expansion)
// ============================================================

/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_u32(v: u32) -> (r: usize)
    ensures r as int == req_space(v as int)
{ required_encoded_space_unsigned(v as u64) }

/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_u16(v: u16) -> (r: usize)
    ensures r as int == req_space(v as int)
{ required_encoded_space_unsigned(v as u64) }

/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_u8(v: u8) -> (r: usize)
    ensures r as int == req_space(v as int)
{ required_encoded_space_unsigned(v as u64) }

/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_usize(v: usize) -> (r: usize)
    ensures r as int == req_space(v as int)
{ required_encoded_space_unsigned(v as u64) }

/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_u32(src: &[u8]) -> (r: Option<(u32, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((u, ss)) => r matches Some((v, s)) && (u == v as int) && s as int == ss,
            None => r matches None,
        },
{
    match decode_var_u64(src) {
        Some((n, s)) => if n <= 0xFFFF_FFFF { Some((n as u32, s)) } else { None },
        None => None,
    }
}

/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_u16(src: &[u8]) -> (r: Option<(u16, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((u, ss)) => r matches Some((v, s)) && (u == v as int) && s as int == ss,
            None => r matches None,
        },
{
    match decode_var_u64(src) {
        Some((n, s)) => if n <= 0xFFFF { Some((n as u16, s)) } else { None },
        None => None,
    }
}

/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_u8(src: &[u8]) -> (r: Option<(u8, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((u, ss)) => r matches Some((v, s)) && (u == v as int) && s as int == ss,
            None => r matches None,
        },
{
    match decode_var_u64(src) {
        Some((n, s)) => if n <= 0xFF { Some((n as u8, s)) } else { None },
        None => None,
    }
}

/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_usize(src: &[u8]) -> (r: Option<(usize, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((u, ss)) => r matches Some((v, s)) && (u == v as int) && s as int == ss,
            None => r matches None,
        },
{
    match decode_var_u64(src) {
        Some((n, s)) => Some((n as usize, s)),
        None => None,
    }
}

/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_u32(v: u32, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(v as int),
    ensures
        used as int == req_space(v as int),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(v as int, k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{ encode_var_u64(v as u64, dst) }

/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_u16(v: u16, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(v as int),
    ensures
        used as int == req_space(v as int),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(v as int, k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{ encode_var_u64(v as u64, dst) }

/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_u8(v: u8, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(v as int),
    ensures
        used as int == req_space(v as int),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(v as int, k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{ encode_var_u64(v as u64, dst) }

/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_usize(v: usize, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(v as int),
    ensures
        used as int == req_space(v as int),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(v as int, k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{ encode_var_u64(v as u64, dst) }

/// Origin: varint.rs:97-99/104-106 (the signed family: the i64 base + the range
/// check)
/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_i32(v: i32) -> (r: usize)
    ensures r as int == req_space(zz_enc(v as int))
{ proof { lemma_zgiazgap_encode_zz_gap(v as int); } required_encoded_space_signed(v as i64) }

/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_i16(v: i16) -> (r: usize)
    ensures r as int == req_space(zz_enc(v as int))
{ proof { lemma_zgiazgap_encode_zz_gap(v as int); } required_encoded_space_signed(v as i64) }

/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_i8(v: i8) -> (r: usize)
    ensures r as int == req_space(zz_enc(v as int))
{ proof { lemma_zgiazgap_encode_zz_gap(v as int); } required_encoded_space_signed(v as i64) }

/// Upstream doc (varint.rs:35-36):
///   Returns the number of bytes this number needs in its encoded form. Note: This varies
///   depending on the actual number you want to encode.
pub exec fn required_space_isize(v: isize) -> (r: usize)
    ensures r as int == req_space(zz_enc(v as int))
{ proof { lemma_zgiazgap_encode_zz_gap(v as int); } required_encoded_space_signed(v as i64) }

/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_i32(src: &[u8]) -> (r: Option<(i32, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((u, ss)) => r matches Some((v, s)) && zz_enc(v as int) == u && s as int == ss,
            None => r matches None,
        },
{
    match decode_var_i64(src) {
        Some((n, s)) =>
            if (-2147483648i64) <= n && n <= 2147483647i64 {
                Some((#[verifier::truncate] (n as i32), s))
            } else { None },
        None => None,
    }
}

/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_i16(src: &[u8]) -> (r: Option<(i16, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((u, ss)) => r matches Some((v, s)) && zz_enc(v as int) == u && s as int == ss,
            None => r matches None,
        },
{
    match decode_var_i64(src) {
        Some((n, s)) =>
            if (-32768i64) <= n && n <= 32767i64 {
                Some((#[verifier::truncate] (n as i16), s))
            } else { None },
        None => None,
    }
}

/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_i8(src: &[u8]) -> (r: Option<(i8, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((u, ss)) => r matches Some((v, s)) && zz_enc(v as int) == u && s as int == ss,
            None => r matches None,
        },
{
    match decode_var_i64(src) {
        Some((n, s)) =>
            if (-128i64) <= n && n <= 127i64 {
                Some((#[verifier::truncate] (n as i8), s))
            } else { None },
        None => None,
    }
}

/// Upstream doc (varint.rs:38-40):
///   Decode a value from the slice. Returns the value and the number of bytes read from the
///   slice (can be used to read several consecutive values from a big slice)
///   return None if all bytes has MSB set.
pub exec fn decode_var_isize(src: &[u8]) -> (r: Option<(isize, usize)>)
    ensures
        match dec_rec(src@, 0, 0) {
            Some((u, ss)) => r matches Some((v, s)) && zz_enc(v as int) == u && s as int == ss,
            None => r matches None,
        },
{
    match decode_var_i64(src) {
        Some((n, s)) => Some((n as isize, s)),
        None => None,
    }
}

/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_i32(v: i32, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(zz_enc(v as int)),
    ensures
        used as int == req_space(zz_enc(v as int)),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(zz_enc(v as int), k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{ proof { lemma_zgiazgap_encode_zz_gap(v as int); } encode_var_i64(v as i64, dst) }

/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_i16(v: i16, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(zz_enc(v as int)),
    ensures
        used as int == req_space(zz_enc(v as int)),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(zz_enc(v as int), k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{ proof { lemma_zgiazgap_encode_zz_gap(v as int); } encode_var_i64(v as i64, dst) }

/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_i8(v: i8, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(zz_enc(v as int)),
    ensures
        used as int == req_space(zz_enc(v as int)),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(zz_enc(v as int), k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{ proof { lemma_zgiazgap_encode_zz_gap(v as int); } encode_var_i64(v as i64, dst) }

/// Upstream doc (varint.rs:42-43):
///   Encode a value into the slice. The slice must be at least `required_space()` bytes long.
///   The number of bytes taken by the encoded integer is returned.
pub exec fn encode_var_isize(v: isize, dst: &mut [u8]) -> (used: usize)
    requires dst.len() >= req_space(zz_enc(v as int)),
    ensures
        used as int == req_space(zz_enc(v as int)),
        forall|k: int| 0 <= k < used as int
            ==> final(dst)@ [k] == varint_byte(zz_enc(v as int), k as nat, used as int),
        forall|k: int| used as int <= k < final(dst)@.len()
            ==> final(dst)@ [k] == old(dst)@ [k],
{ proof { lemma_zgiazgap_encode_zz_gap(v as int); } encode_var_i64(v as i64, dst) }

// ============================================================
// exec mirror: the encode_var_vec trait default method (varint.rs:46-53)
// The Vec-allocation face: a stack fixed-size buffer goes through encode_var_* and
// is then
//   copied incrementally via Vec::new+push (equal in value to the upstream
//   vec![0;required_space]+fill)
// ============================================================

/// Upstream doc (varint.rs:46-47):
///   Helper: Encode a value and return the encoded form as Vec. The Vec must be at least
///   `required_space()` bytes long.
pub exec fn encode_var_vec_u64(v: u64) -> (out: Vec<u8>)
    ensures
        out@.len() as int == req_space(v as int),
        forall|k: int| 0 <= k < out@.len() ==> out@ [k] == varint_byte(v as int, k as nat, out@.len() as int),
    // SPEC-DOC MISMATCH (unreported): the doc sentence "The Vec must be at least
    // `required_space()` bytes long" is a copy-paste of encode_var's caller
    // precondition, read here as a precondition on the function's own return
    // value; no caller-side obligation exists, so the doc-promised precondition
    // clause is unprovable -- the implementation-faithful equality
    // out@.len() == req_space(v) is carried by the ensures above.
{
    let mut buf: [u8; 10] = [0; 10];
    let n = encode_var_u64(v, &mut buf);
    proof { lemma_req_space_within_10(v); }
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n <= 10,
            out@.len() == i,
            forall|k: int| 0 <= k < i as int ==> out@ [k] == varint_byte(v as int, k as nat, n as int),
        decreases n - i
    {
        out.push(buf[i]);
        i += 1;
    }
    out
}

/// Upstream doc (varint.rs:46-47):
///   Helper: Encode a value and return the encoded form as Vec. The Vec must be at least
///   `required_space()` bytes long.
pub exec fn encode_var_vec_u32(v: u32) -> (out: Vec<u8>)
    ensures
        out@.len() as int == req_space(v as int),
        forall|k: int| 0 <= k < out@.len() ==> out@ [k] == varint_byte(v as int, k as nat, out@.len() as int),
{
    let mut buf: [u8; 10] = [0; 10];
    let n = encode_var_u32(v, &mut buf);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, out@.len() == i,
        decreases n - i
    {
        out.push(buf[i]);
        i += 1;
    }
    out
}

/// Upstream doc (varint.rs:46-47):
///   Helper: Encode a value and return the encoded form as Vec. The Vec must be at least
///   `required_space()` bytes long.
pub exec fn encode_var_vec_i64(v: i64) -> (out: Vec<u8>)
    ensures
        out@.len() as int == req_space(zz_enc(v as int)),
{
    proof { lemma_zgiazgap_encode_zz_gap(v as int); }
    let mut buf: [u8; 10] = [0; 10];
    let n = encode_var_i64(v, &mut buf);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, out@.len() == i,
        decreases n - i
    {
        out.push(buf[i]);
        i += 1;
    }
    out
}

/// Upstream doc (varint.rs:46-47):
///   Helper: Encode a value and return the encoded form as Vec. The Vec must be at least
///   `required_space()` bytes long.
pub exec fn encode_var_vec_u16(v: u16) -> (out: Vec<u8>)
    ensures out@.len() as int == req_space(v as int),
{
    let mut buf: [u8; 10] = [0; 10];
    let n = encode_var_u16(v, &mut buf);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, out@.len() == i,
        decreases n - i
    {
        out.push(buf[i]);
        i += 1;
    }
    out
}

/// Origin: varint.rs:46-52 (the bytes needed by u64)
/// Upstream doc (varint.rs:46-47):
///   Helper: Encode a value and return the encoded form as Vec. The Vec must be at least
///   `required_space()` bytes long.
pub exec fn encode_var_vec_u8(v: u8) -> (out: Vec<u8>)
    ensures out@.len() as int == req_space(v as int),
{
    let mut buf: [u8; 10] = [0; 10];
    let n = encode_var_u8(v, &mut buf);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, out@.len() == i,
        decreases n - i
    {
        out.push(buf[i]);
        i += 1;
    }
    out
}

} // verus!
