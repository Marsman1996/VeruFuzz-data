//! verified/src/model.rs -- machine-semantics models and the bridging lemma library for the bitwise/table implementations of crc.
//!
//! This file is not a mirror of an upstream source file; it is the spec-side shared fact source (shared models + shared lemmas):
//! - each width family provides reflected / non-reflected spec models of the "single register update"
//!   (machine uN semantics, truncating left shifts expressed as an explicit mod 2^W) and the 8-round run recursion;
//! - the exec loop invariants of `crcX` (util.rs), table generation (table.rs) and digest/update (crcX.rs)
//!   all reference this file's run/step, keeping the fact source unique;
//! - the bridging lemmas depend only on vstd (pow2 / lemma_uN_shr_is_div / lemma_uN_shl_is_mul)
//!   plus the single machine fact `by(bit_vector)`; each is independently provable and reusable for any width family.
//!
//! [Origin Rust: external dependency vstd -- no upstream source counterpart]

use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

/* Truncating left-shift model: shl1/mod 2^W (explicit mod form, machine uN semantics) */

pub open spec fn shl1_u8(v: u8) -> u8 { (((v as int) * 2) % 256) as u8 }
pub open spec fn shl1_u16(v: u16) -> u16 { (((v as int) * 2) % 65536) as u16 }
pub open spec fn shl1_u32(v: u32) -> u32 { (((v as int) * 2) % 4294967296) as u32 }
pub open spec fn shl1_u64(v: u64) -> u64 { (((v as int) * 2) % (18446744073709551616 as int)) as u64 }
pub open spec fn shl1_u128(v: u128) -> u128 { (((v as int) * 2) % (340282366920938463463374607431768211456 as int)) as u128 }

// Large-constant shift models (low-8-bits mask form: v<<k == (v%2^(W-k))*2^k mod 2^W)
pub open spec fn shl24_u32(v: u32) -> u32 { (((v as int) * 16777216) % 4294967296) as u32 }
pub open spec fn shl8_u16(v: u16) -> u16 { (((v as int) * 256) % 65536) as u16 }
pub open spec fn shl56_u64(v: u64) -> u64 { (((v as int) * 72057594037927936) % (18446744073709551616 as int)) as u64 }
pub open spec fn shl120_u128(v: u128) -> u128 { (((v as int) * 1329227995784915872903807060280344576) % (340282366920938463463374607431768211456 as int)) as u128 }


/* -- Symbolic shift models and per-case dispatch bridges (s < W ==> exec (v << s) == shls_uN(v, s)).
 * shls is defined via the shl1 chain (a pure machine term; the bv engine can fully evaluate it on a concrete s);
 * the W=128 big constants ride the shl1 chain with no literal pow2. */

pub open spec fn shls_u8(v: u8, s: nat) -> u8
    decreases s,
{
    if s == 0 { v } else { shl1_u8(shls_u8(v, (s - 1) as nat)) }
}
pub open spec fn shls_u16(v: u16, s: nat) -> u16
    decreases s,
{
    if s == 0 { v } else { shl1_u16(shls_u16(v, (s - 1) as nat)) }
}
pub open spec fn shls_u32(v: u32, s: nat) -> u32
    decreases s,
{
    if s == 0 { v } else { shl1_u32(shls_u32(v, (s - 1) as nat)) }
}
pub open spec fn shls_u64(v: u64, s: nat) -> u64
    decreases s,
{
    if s == 0 { v } else { shl1_u64(shls_u64(v, (s - 1) as nat)) }
}
pub open spec fn shls_u128(v: u128, s: nat) -> u128
    decreases s,
{
    if s == 0 { v } else { shl1_u128(shls_u128(v, (s - 1) as nat)) }
}


/* Byte-injection shift of the L=0 no-table path (crc << 8, one per family) */
pub open spec fn shl8_u32m(v: u32) -> u32 { shls_u32(v, 8) }
pub open spec fn shl8_u64m(v: u64) -> u64 { shls_u64(v, 8) }
pub open spec fn shl8_u128m(v: u128) -> u128 { shls_u128(v, 8) }

pub open spec fn revm8_acc(x: u8, k: nat) -> u8
    decreases k,
{
    if k == 0 { 0 } else {
        (shl1_u8(revm8_acc(x, (k - 1) as nat)) + ((x >> (((k - 1) % 8) as u8)) & 1)) as u8
    }
}
pub open spec fn revm8(x: u8) -> u8 { revm8_acc(x, 8) }
pub open spec fn revm16(x: u16) -> u16 {
    /* [Origin Rust: u16::reverse_bits = weighted byte-mirror composition] */
    (shls_u16((revm8((x % 256) as u8)) as u16, 8)) | (revm8((x / 256) as u8) as u16)
}
pub open spec fn revm32(x: u32) -> u32 {
    (shls_u32((revm16((x % 65536) as u16)) as u32, 16)) | (revm16((x / 65536) as u16) as u32)
}


/* Symbolic right-shift amount model and dispatch bridge (s < 8) */
pub open spec fn shrs_u8(v: u8, s: nat) -> u8
    decreases s,
{
    if s == 0 { v } else { shrs_u8(v, (s - 1) as nat) >> 1 }
}

/* Symbolic right-shift amount model and dispatch bridge (s < 16) */
pub open spec fn shrs_u16(v: u16, s: nat) -> u16
    decreases s,
{
    if s == 0 { v } else { shrs_u16(v, (s - 1) as nat) >> 1 }
}

/* Symbolic right-shift amount model and dispatch bridge (s < 32) */
pub open spec fn shrs_u32(v: u32, s: nat) -> u32
    decreases s,
{
    if s == 0 { v } else { shrs_u32(v, (s - 1) as nat) >> 1 }
}

/* Symbolic right-shift amount model and dispatch bridge (s < 64) */
pub open spec fn shrs_u64(v: u64, s: nat) -> u64
    decreases s,
{
    if s == 0 { v } else { shrs_u64(v, (s - 1) as nat) >> 1 }
}

/* Symbolic right-shift amount model and dispatch bridge (s < 128) */
pub open spec fn shrs_u128(v: u128, s: nat) -> u128
    decreases s,
{
    if s == 0 { v } else { shrs_u128(v, (s - 1) as nat) >> 1 }
}


/* revm64/revm128 (byte-composite chains; isomorphic to the exec rev64/rev128) */
pub open spec fn revm64(x: u64) -> u64 {
    (shls_u64(revm32((x % 4294967296) as u32) as u64, 32)) | (revm32((x / 4294967296) as u32) as u64)
}
pub open spec fn revm128(x: u128) -> u128 {
    (shls_u128(revm64((x % 18446744073709551616) as u64) as u128, 64)) | (revm64((x / 18446744073709551616) as u64) as u128)
}

/* ============================================================
 * Per-family run models (machine uN; left shifts via the explicit mod forms shl1/shlK)
 * ============================================================ */

// -- u8 --
pub open spec fn crc8r_step(poly: u8, v: u8) -> u8 {
    (v >> 1) ^ (if v % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc8r_run(poly: u8, base: u8, n: nat) -> u8
    decreases n,
{
    if n == 0 { base } else { crc8r_step(poly, crc8r_run(poly, base, (n - 1) as nat)) }
}
pub open spec fn crc8n_step(poly: u8, v: u8) -> u8 {
    shl1_u8(v) ^ (if (v >> 7) % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc8n_run(poly: u8, base: u8, n: nat) -> u8
    decreases n,
{
    if n == 0 { base } else { crc8n_step(poly, crc8n_run(poly, base, (n - 1) as nat)) }
}

// -- u16 --
pub open spec fn crc16r_step(poly: u16, v: u16) -> u16 {
    (v >> 1) ^ (if v % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc16r_run(poly: u16, base: u16, n: nat) -> u16
    decreases n,
{
    if n == 0 { base } else { crc16r_step(poly, crc16r_run(poly, base, (n - 1) as nat)) }
}
pub open spec fn crc16n_step(poly: u16, v: u16) -> u16 {
    shl1_u16(v) ^ (if (v >> 15) % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc16n_run(poly: u16, base: u16, n: nat) -> u16
    decreases n,
{
    if n == 0 { base } else { crc16n_step(poly, crc16n_run(poly, base, (n - 1) as nat)) }
}

// -- u32 --
pub open spec fn crc32r_step(poly: u32, v: u32) -> u32 {
    (v >> 1) ^ (if v % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc32r_run(poly: u32, base: u32, n: nat) -> u32
    decreases n,
{
    if n == 0 { base } else { crc32r_step(poly, crc32r_run(poly, base, (n - 1) as nat)) }
}
pub open spec fn crc32n_step(poly: u32, v: u32) -> u32 {
    shl1_u32(v) ^ (if (v >> 31) % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc32n_run(poly: u32, base: u32, n: nat) -> u32
    decreases n,
{
    if n == 0 { base } else { crc32n_step(poly, crc32n_run(poly, base, (n - 1) as nat)) }
}

// -- u64 --
pub open spec fn crc64r_step(poly: u64, v: u64) -> u64 {
    (v >> 1) ^ (if v % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc64r_run(poly: u64, base: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 { base } else { crc64r_step(poly, crc64r_run(poly, base, (n - 1) as nat)) }
}
pub open spec fn crc64n_step(poly: u64, v: u64) -> u64 {
    shl1_u64(v) ^ (if (v >> 63) % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc64n_run(poly: u64, base: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 { base } else { crc64n_step(poly, crc64n_run(poly, base, (n - 1) as nat)) }
}

// -- u128 --
pub open spec fn crc128r_step(poly: u128, v: u128) -> u128 {
    (v >> 1) ^ (if v % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc128r_run(poly: u128, base: u128, n: nat) -> u128
    decreases n,
{
    if n == 0 { base } else { crc128r_step(poly, crc128r_run(poly, base, (n - 1) as nat)) }
}
pub open spec fn crc128n_step(poly: u128, v: u128) -> u128 {
    shl1_u128(v) ^ (if (v >> 127) % 2 == 1 { poly } else { 0 })
}
pub open spec fn crc128n_run(poly: u128, base: u128, n: nat) -> u128
    decreases n,
{
    if n == 0 { base } else { crc128n_step(poly, crc128n_run(poly, base, (n - 1) as nat)) }
}

/* ============================================================
 * Parallel bit reversal rev:uN (machine semantics = bit mirroring). Upstream `reverse_bits` has no
 * verus builtin; its semantics is defined here as an int summation, with exec helpers accumulating and proving bit by bit.
 * [Origin Rust: core::num reverse_bits -- expression-level replacement by local revw calls]
 * ============================================================ */

pub open spec fn bit(x: nat, m: nat) -> nat { (x / pow2(m)) % 2 }

// rev_w(x) = the sum of bit_m(x)*2^(W-1-m), a closed-form summation (no xor, all int arithmetic)
pub open spec fn rev8v(x: nat) -> nat {
    bit(x, 0) * 128 + bit(x, 1) * 64 + bit(x, 2) * 32 + bit(x, 3) * 16
        + bit(x, 4) * 8 + bit(x, 5) * 4 + bit(x, 6) * 2 + bit(x, 7)
}
pub open spec fn rev16v(x: nat) -> nat {
    (rev8v(x % 256) * 256) + rev8v(x / 256)
}

// =========================================================================
// Proof lemmas (moved to the end of the file; only the order changed).
// =========================================================================

/* ============================================================
 * Common: uN single-machine fact bridges (one copy per family, including bit extraction and the or-add equality)
 * ============================================================ */

pub broadcast proof fn lem_and1_u8(v: u8)
    ensures #[trigger] (v & 1) == v % 2,
{ assert((v & 1) == (v % 2)) by(bit_vector); }

pub broadcast proof fn lem_and1_u16(v: u16)
    ensures #[trigger] (v & 1) == v % 2,
{ assert((v & 1) == (v % 2)) by(bit_vector); }

pub broadcast proof fn lem_and1_u32(v: u32)
    ensures #[trigger] (v & 1) == v % 2,
{ assert((v & 1) == (v % 2)) by(bit_vector); }

pub broadcast proof fn lem_and1_u64(v: u64)
    ensures #[trigger] (v & 1) == v % 2,
{ assert((v & 1) == (v % 2)) by(bit_vector); }

pub broadcast proof fn lem_and1_u128(v: u128)
    ensures #[trigger] (v & 1) == v % 2,
{ assert((v & 1) == (v % 2)) by(bit_vector); }

/* Truncating left-shift bridge: exec (v << 1) == shl1_uN(v).
 * Route: mask off the high bits so the shift cannot overflow -> lemma_uN_shl_is_mul -> machine multiplication <-> int mod. */

pub broadcast proof fn lem_shl1_u8(v: u8)
    ensures #[trigger] (v << 1) == shl1_u8(v),
{ assert((v << 1) == shl1_u8(v)) by(bit_vector); }

pub broadcast proof fn lem_shl1_u16(v: u16)
    ensures #[trigger] (v << 1) == shl1_u16(v),
{ assert((v << 1) == shl1_u16(v)) by(bit_vector); }

pub broadcast proof fn lem_shl1_u32(v: u32)
    ensures #[trigger] (v << 1) == shl1_u32(v),
{ assert((v << 1) == shl1_u32(v)) by(bit_vector); }

pub broadcast proof fn lem_shl1_u64(v: u64)
    ensures #[trigger] (v << 1) == shl1_u64(v),
{ assert((v << 1) == shl1_u64(v)) by(bit_vector); }

pub broadcast proof fn lem_shl1_u128(v: u128)
    ensures #[trigger] (v << 1) == shl1_u128(v),
{ assert((v << 1) == shl1_u128(v)) by(bit_vector); }

/* Pre-shift bridge (the constant left shift before the loop entry of the non-reflect trunk of util crcX):
 * exec (v << K) == shlK(v, K) (K = 24/8/56/120, one per family) */

pub broadcast proof fn lem_shl24_u32(v: u32)
    ensures #[trigger] (v << 24) == shl24_u32(v),
{ assert((v << 24) == shl24_u32(v)) by(bit_vector); }

pub broadcast proof fn lem_shl8_u16(v: u16)
    ensures #[trigger] (v << 8) == shl8_u16(v),
{ assert((v << 8) == shl8_u16(v)) by(bit_vector); }

pub broadcast proof fn lem_shl56_u64(v: u64)
    ensures #[trigger] (v << 56) == shl56_u64(v),
{ assert((v << 56) == shl56_u64(v)) by(bit_vector); }

pub broadcast proof fn lem_shl120_u128(v: u128)
    ensures #[trigger] (v << 120) == shl120_u128(v),
{ assert((v << 120) == shl120_u128(v)) by(bit_vector); }

pub broadcast proof fn lem_shls_u8(v: u8, s: u8)
    requires s < 8,
    ensures (v << s) == shls_u8(v, s as nat),
{
    if s == 0 {
        assert((v << 0u8) == v) by(bit_vector);
    } else if s == 1 {
        assert((v << 1u8) == shls_u8(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v << 2u8) == shls_u8(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v << 3u8) == shls_u8(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v << 4u8) == shls_u8(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v << 5u8) == shls_u8(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v << 6u8) == shls_u8(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v << 7u8) == shls_u8(v, 7)) by(bit_vector);
    }
}
pub broadcast proof fn lem_shls_u16(v: u16, s: u16)
    requires s < 16,
    ensures (v << s) == shls_u16(v, s as nat),
{
    if s == 0 {
        assert((v << 0u16) == v) by(bit_vector);
    } else if s == 1 {
        assert((v << 1u16) == shls_u16(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v << 2u16) == shls_u16(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v << 3u16) == shls_u16(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v << 4u16) == shls_u16(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v << 5u16) == shls_u16(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v << 6u16) == shls_u16(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v << 7u16) == shls_u16(v, 7)) by(bit_vector);
    } else if s == 8 {
        assert((v << 8u16) == shls_u16(v, 8)) by(bit_vector);
    } else if s == 9 {
        assert((v << 9u16) == shls_u16(v, 9)) by(bit_vector);
    } else if s == 10 {
        assert((v << 10u16) == shls_u16(v, 10)) by(bit_vector);
    } else if s == 11 {
        assert((v << 11u16) == shls_u16(v, 11)) by(bit_vector);
    } else if s == 12 {
        assert((v << 12u16) == shls_u16(v, 12)) by(bit_vector);
    } else if s == 13 {
        assert((v << 13u16) == shls_u16(v, 13)) by(bit_vector);
    } else if s == 14 {
        assert((v << 14u16) == shls_u16(v, 14)) by(bit_vector);
    } else if s == 15 {
        assert((v << 15u16) == shls_u16(v, 15)) by(bit_vector);
    }
}
pub broadcast proof fn lem_shls_u32(v: u32, s: u32)
    requires s < 32,
    ensures (v << s) == shls_u32(v, s as nat),
{
    if s == 0 {
        assert((v << 0u32) == v) by(bit_vector);
    } else if s == 1 {
        assert((v << 1u32) == shls_u32(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v << 2u32) == shls_u32(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v << 3u32) == shls_u32(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v << 4u32) == shls_u32(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v << 5u32) == shls_u32(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v << 6u32) == shls_u32(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v << 7u32) == shls_u32(v, 7)) by(bit_vector);
    } else if s == 8 {
        assert((v << 8u32) == shls_u32(v, 8)) by(bit_vector);
    } else if s == 9 {
        assert((v << 9u32) == shls_u32(v, 9)) by(bit_vector);
    } else if s == 10 {
        assert((v << 10u32) == shls_u32(v, 10)) by(bit_vector);
    } else if s == 11 {
        assert((v << 11u32) == shls_u32(v, 11)) by(bit_vector);
    } else if s == 12 {
        assert((v << 12u32) == shls_u32(v, 12)) by(bit_vector);
    } else if s == 13 {
        assert((v << 13u32) == shls_u32(v, 13)) by(bit_vector);
    } else if s == 14 {
        assert((v << 14u32) == shls_u32(v, 14)) by(bit_vector);
    } else if s == 15 {
        assert((v << 15u32) == shls_u32(v, 15)) by(bit_vector);
    } else if s == 16 {
        assert((v << 16u32) == shls_u32(v, 16)) by(bit_vector);
    } else if s == 17 {
        assert((v << 17u32) == shls_u32(v, 17)) by(bit_vector);
    } else if s == 18 {
        assert((v << 18u32) == shls_u32(v, 18)) by(bit_vector);
    } else if s == 19 {
        assert((v << 19u32) == shls_u32(v, 19)) by(bit_vector);
    } else if s == 20 {
        assert((v << 20u32) == shls_u32(v, 20)) by(bit_vector);
    } else if s == 21 {
        assert((v << 21u32) == shls_u32(v, 21)) by(bit_vector);
    } else if s == 22 {
        assert((v << 22u32) == shls_u32(v, 22)) by(bit_vector);
    } else if s == 23 {
        assert((v << 23u32) == shls_u32(v, 23)) by(bit_vector);
    } else if s == 24 {
        assert((v << 24u32) == shls_u32(v, 24)) by(bit_vector);
    } else if s == 25 {
        assert((v << 25u32) == shls_u32(v, 25)) by(bit_vector);
    } else if s == 26 {
        assert((v << 26u32) == shls_u32(v, 26)) by(bit_vector);
    } else if s == 27 {
        assert((v << 27u32) == shls_u32(v, 27)) by(bit_vector);
    } else if s == 28 {
        assert((v << 28u32) == shls_u32(v, 28)) by(bit_vector);
    } else if s == 29 {
        assert((v << 29u32) == shls_u32(v, 29)) by(bit_vector);
    } else if s == 30 {
        assert((v << 30u32) == shls_u32(v, 30)) by(bit_vector);
    } else if s == 31 {
        assert((v << 31u32) == shls_u32(v, 31)) by(bit_vector);
    }
}
pub broadcast proof fn lem_shls_u64(v: u64, s: u64)
    requires s < 64,
    ensures (v << s) == shls_u64(v, s as nat),
{
    if s == 0 {
        assert((v << 0u64) == v) by(bit_vector);
    } else if s == 1 {
        assert((v << 1u64) == shls_u64(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v << 2u64) == shls_u64(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v << 3u64) == shls_u64(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v << 4u64) == shls_u64(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v << 5u64) == shls_u64(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v << 6u64) == shls_u64(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v << 7u64) == shls_u64(v, 7)) by(bit_vector);
    } else if s == 8 {
        assert((v << 8u64) == shls_u64(v, 8)) by(bit_vector);
    } else if s == 9 {
        assert((v << 9u64) == shls_u64(v, 9)) by(bit_vector);
    } else if s == 10 {
        assert((v << 10u64) == shls_u64(v, 10)) by(bit_vector);
    } else if s == 11 {
        assert((v << 11u64) == shls_u64(v, 11)) by(bit_vector);
    } else if s == 12 {
        assert((v << 12u64) == shls_u64(v, 12)) by(bit_vector);
    } else if s == 13 {
        assert((v << 13u64) == shls_u64(v, 13)) by(bit_vector);
    } else if s == 14 {
        assert((v << 14u64) == shls_u64(v, 14)) by(bit_vector);
    } else if s == 15 {
        assert((v << 15u64) == shls_u64(v, 15)) by(bit_vector);
    } else if s == 16 {
        assert((v << 16u64) == shls_u64(v, 16)) by(bit_vector);
    } else if s == 17 {
        assert((v << 17u64) == shls_u64(v, 17)) by(bit_vector);
    } else if s == 18 {
        assert((v << 18u64) == shls_u64(v, 18)) by(bit_vector);
    } else if s == 19 {
        assert((v << 19u64) == shls_u64(v, 19)) by(bit_vector);
    } else if s == 20 {
        assert((v << 20u64) == shls_u64(v, 20)) by(bit_vector);
    } else if s == 21 {
        assert((v << 21u64) == shls_u64(v, 21)) by(bit_vector);
    } else if s == 22 {
        assert((v << 22u64) == shls_u64(v, 22)) by(bit_vector);
    } else if s == 23 {
        assert((v << 23u64) == shls_u64(v, 23)) by(bit_vector);
    } else if s == 24 {
        assert((v << 24u64) == shls_u64(v, 24)) by(bit_vector);
    } else if s == 25 {
        assert((v << 25u64) == shls_u64(v, 25)) by(bit_vector);
    } else if s == 26 {
        assert((v << 26u64) == shls_u64(v, 26)) by(bit_vector);
    } else if s == 27 {
        assert((v << 27u64) == shls_u64(v, 27)) by(bit_vector);
    } else if s == 28 {
        assert((v << 28u64) == shls_u64(v, 28)) by(bit_vector);
    } else if s == 29 {
        assert((v << 29u64) == shls_u64(v, 29)) by(bit_vector);
    } else if s == 30 {
        assert((v << 30u64) == shls_u64(v, 30)) by(bit_vector);
    } else if s == 31 {
        assert((v << 31u64) == shls_u64(v, 31)) by(bit_vector);
    } else if s == 32 {
        assert((v << 32u64) == shls_u64(v, 32)) by(bit_vector);
    } else if s == 33 {
        assert((v << 33u64) == shls_u64(v, 33)) by(bit_vector);
    } else if s == 34 {
        assert((v << 34u64) == shls_u64(v, 34)) by(bit_vector);
    } else if s == 35 {
        assert((v << 35u64) == shls_u64(v, 35)) by(bit_vector);
    } else if s == 36 {
        assert((v << 36u64) == shls_u64(v, 36)) by(bit_vector);
    } else if s == 37 {
        assert((v << 37u64) == shls_u64(v, 37)) by(bit_vector);
    } else if s == 38 {
        assert((v << 38u64) == shls_u64(v, 38)) by(bit_vector);
    } else if s == 39 {
        assert((v << 39u64) == shls_u64(v, 39)) by(bit_vector);
    } else if s == 40 {
        assert((v << 40u64) == shls_u64(v, 40)) by(bit_vector);
    } else if s == 41 {
        assert((v << 41u64) == shls_u64(v, 41)) by(bit_vector);
    } else if s == 42 {
        assert((v << 42u64) == shls_u64(v, 42)) by(bit_vector);
    } else if s == 43 {
        assert((v << 43u64) == shls_u64(v, 43)) by(bit_vector);
    } else if s == 44 {
        assert((v << 44u64) == shls_u64(v, 44)) by(bit_vector);
    } else if s == 45 {
        assert((v << 45u64) == shls_u64(v, 45)) by(bit_vector);
    } else if s == 46 {
        assert((v << 46u64) == shls_u64(v, 46)) by(bit_vector);
    } else if s == 47 {
        assert((v << 47u64) == shls_u64(v, 47)) by(bit_vector);
    } else if s == 48 {
        assert((v << 48u64) == shls_u64(v, 48)) by(bit_vector);
    } else if s == 49 {
        assert((v << 49u64) == shls_u64(v, 49)) by(bit_vector);
    } else if s == 50 {
        assert((v << 50u64) == shls_u64(v, 50)) by(bit_vector);
    } else if s == 51 {
        assert((v << 51u64) == shls_u64(v, 51)) by(bit_vector);
    } else if s == 52 {
        assert((v << 52u64) == shls_u64(v, 52)) by(bit_vector);
    } else if s == 53 {
        assert((v << 53u64) == shls_u64(v, 53)) by(bit_vector);
    } else if s == 54 {
        assert((v << 54u64) == shls_u64(v, 54)) by(bit_vector);
    } else if s == 55 {
        assert((v << 55u64) == shls_u64(v, 55)) by(bit_vector);
    } else if s == 56 {
        assert((v << 56u64) == shls_u64(v, 56)) by(bit_vector);
    } else if s == 57 {
        assert((v << 57u64) == shls_u64(v, 57)) by(bit_vector);
    } else if s == 58 {
        assert((v << 58u64) == shls_u64(v, 58)) by(bit_vector);
    } else if s == 59 {
        assert((v << 59u64) == shls_u64(v, 59)) by(bit_vector);
    } else if s == 60 {
        assert((v << 60u64) == shls_u64(v, 60)) by(bit_vector);
    } else if s == 61 {
        assert((v << 61u64) == shls_u64(v, 61)) by(bit_vector);
    } else if s == 62 {
        assert((v << 62u64) == shls_u64(v, 62)) by(bit_vector);
    } else if s == 63 {
        assert((v << 63u64) == shls_u64(v, 63)) by(bit_vector);
    }
}
pub broadcast proof fn lem_shls_u128(v: u128, s: u128)
    requires s < 128,
    ensures (v << s) == shls_u128(v, s as nat),
{
    if s == 0 {
        assert((v << 0u128) == v) by(bit_vector);
    } else if s == 1 {
        assert((v << 1u128) == shls_u128(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v << 2u128) == shls_u128(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v << 3u128) == shls_u128(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v << 4u128) == shls_u128(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v << 5u128) == shls_u128(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v << 6u128) == shls_u128(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v << 7u128) == shls_u128(v, 7)) by(bit_vector);
    } else if s == 8 {
        assert((v << 8u128) == shls_u128(v, 8)) by(bit_vector);
    } else if s == 9 {
        assert((v << 9u128) == shls_u128(v, 9)) by(bit_vector);
    } else if s == 10 {
        assert((v << 10u128) == shls_u128(v, 10)) by(bit_vector);
    } else if s == 11 {
        assert((v << 11u128) == shls_u128(v, 11)) by(bit_vector);
    } else if s == 12 {
        assert((v << 12u128) == shls_u128(v, 12)) by(bit_vector);
    } else if s == 13 {
        assert((v << 13u128) == shls_u128(v, 13)) by(bit_vector);
    } else if s == 14 {
        assert((v << 14u128) == shls_u128(v, 14)) by(bit_vector);
    } else if s == 15 {
        assert((v << 15u128) == shls_u128(v, 15)) by(bit_vector);
    } else if s == 16 {
        assert((v << 16u128) == shls_u128(v, 16)) by(bit_vector);
    } else if s == 17 {
        assert((v << 17u128) == shls_u128(v, 17)) by(bit_vector);
    } else if s == 18 {
        assert((v << 18u128) == shls_u128(v, 18)) by(bit_vector);
    } else if s == 19 {
        assert((v << 19u128) == shls_u128(v, 19)) by(bit_vector);
    } else if s == 20 {
        assert((v << 20u128) == shls_u128(v, 20)) by(bit_vector);
    } else if s == 21 {
        assert((v << 21u128) == shls_u128(v, 21)) by(bit_vector);
    } else if s == 22 {
        assert((v << 22u128) == shls_u128(v, 22)) by(bit_vector);
    } else if s == 23 {
        assert((v << 23u128) == shls_u128(v, 23)) by(bit_vector);
    } else if s == 24 {
        assert((v << 24u128) == shls_u128(v, 24)) by(bit_vector);
    } else if s == 25 {
        assert((v << 25u128) == shls_u128(v, 25)) by(bit_vector);
    } else if s == 26 {
        assert((v << 26u128) == shls_u128(v, 26)) by(bit_vector);
    } else if s == 27 {
        assert((v << 27u128) == shls_u128(v, 27)) by(bit_vector);
    } else if s == 28 {
        assert((v << 28u128) == shls_u128(v, 28)) by(bit_vector);
    } else if s == 29 {
        assert((v << 29u128) == shls_u128(v, 29)) by(bit_vector);
    } else if s == 30 {
        assert((v << 30u128) == shls_u128(v, 30)) by(bit_vector);
    } else if s == 31 {
        assert((v << 31u128) == shls_u128(v, 31)) by(bit_vector);
    } else if s == 32 {
        assert((v << 32u128) == shls_u128(v, 32)) by(bit_vector);
    } else if s == 33 {
        assert((v << 33u128) == shls_u128(v, 33)) by(bit_vector);
    } else if s == 34 {
        assert((v << 34u128) == shls_u128(v, 34)) by(bit_vector);
    } else if s == 35 {
        assert((v << 35u128) == shls_u128(v, 35)) by(bit_vector);
    } else if s == 36 {
        assert((v << 36u128) == shls_u128(v, 36)) by(bit_vector);
    } else if s == 37 {
        assert((v << 37u128) == shls_u128(v, 37)) by(bit_vector);
    } else if s == 38 {
        assert((v << 38u128) == shls_u128(v, 38)) by(bit_vector);
    } else if s == 39 {
        assert((v << 39u128) == shls_u128(v, 39)) by(bit_vector);
    } else if s == 40 {
        assert((v << 40u128) == shls_u128(v, 40)) by(bit_vector);
    } else if s == 41 {
        assert((v << 41u128) == shls_u128(v, 41)) by(bit_vector);
    } else if s == 42 {
        assert((v << 42u128) == shls_u128(v, 42)) by(bit_vector);
    } else if s == 43 {
        assert((v << 43u128) == shls_u128(v, 43)) by(bit_vector);
    } else if s == 44 {
        assert((v << 44u128) == shls_u128(v, 44)) by(bit_vector);
    } else if s == 45 {
        assert((v << 45u128) == shls_u128(v, 45)) by(bit_vector);
    } else if s == 46 {
        assert((v << 46u128) == shls_u128(v, 46)) by(bit_vector);
    } else if s == 47 {
        assert((v << 47u128) == shls_u128(v, 47)) by(bit_vector);
    } else if s == 48 {
        assert((v << 48u128) == shls_u128(v, 48)) by(bit_vector);
    } else if s == 49 {
        assert((v << 49u128) == shls_u128(v, 49)) by(bit_vector);
    } else if s == 50 {
        assert((v << 50u128) == shls_u128(v, 50)) by(bit_vector);
    } else if s == 51 {
        assert((v << 51u128) == shls_u128(v, 51)) by(bit_vector);
    } else if s == 52 {
        assert((v << 52u128) == shls_u128(v, 52)) by(bit_vector);
    } else if s == 53 {
        assert((v << 53u128) == shls_u128(v, 53)) by(bit_vector);
    } else if s == 54 {
        assert((v << 54u128) == shls_u128(v, 54)) by(bit_vector);
    } else if s == 55 {
        assert((v << 55u128) == shls_u128(v, 55)) by(bit_vector);
    } else if s == 56 {
        assert((v << 56u128) == shls_u128(v, 56)) by(bit_vector);
    } else if s == 57 {
        assert((v << 57u128) == shls_u128(v, 57)) by(bit_vector);
    } else if s == 58 {
        assert((v << 58u128) == shls_u128(v, 58)) by(bit_vector);
    } else if s == 59 {
        assert((v << 59u128) == shls_u128(v, 59)) by(bit_vector);
    } else if s == 60 {
        assert((v << 60u128) == shls_u128(v, 60)) by(bit_vector);
    } else if s == 61 {
        assert((v << 61u128) == shls_u128(v, 61)) by(bit_vector);
    } else if s == 62 {
        assert((v << 62u128) == shls_u128(v, 62)) by(bit_vector);
    } else if s == 63 {
        assert((v << 63u128) == shls_u128(v, 63)) by(bit_vector);
    } else if s == 64 {
        assert((v << 64u128) == shls_u128(v, 64)) by(bit_vector);
    } else if s == 65 {
        assert((v << 65u128) == shls_u128(v, 65)) by(bit_vector);
    } else if s == 66 {
        assert((v << 66u128) == shls_u128(v, 66)) by(bit_vector);
    } else if s == 67 {
        assert((v << 67u128) == shls_u128(v, 67)) by(bit_vector);
    } else if s == 68 {
        assert((v << 68u128) == shls_u128(v, 68)) by(bit_vector);
    } else if s == 69 {
        assert((v << 69u128) == shls_u128(v, 69)) by(bit_vector);
    } else if s == 70 {
        assert((v << 70u128) == shls_u128(v, 70)) by(bit_vector);
    } else if s == 71 {
        assert((v << 71u128) == shls_u128(v, 71)) by(bit_vector);
    } else if s == 72 {
        assert((v << 72u128) == shls_u128(v, 72)) by(bit_vector);
    } else if s == 73 {
        assert((v << 73u128) == shls_u128(v, 73)) by(bit_vector);
    } else if s == 74 {
        assert((v << 74u128) == shls_u128(v, 74)) by(bit_vector);
    } else if s == 75 {
        assert((v << 75u128) == shls_u128(v, 75)) by(bit_vector);
    } else if s == 76 {
        assert((v << 76u128) == shls_u128(v, 76)) by(bit_vector);
    } else if s == 77 {
        assert((v << 77u128) == shls_u128(v, 77)) by(bit_vector);
    } else if s == 78 {
        assert((v << 78u128) == shls_u128(v, 78)) by(bit_vector);
    } else if s == 79 {
        assert((v << 79u128) == shls_u128(v, 79)) by(bit_vector);
    } else if s == 80 {
        assert((v << 80u128) == shls_u128(v, 80)) by(bit_vector);
    } else if s == 81 {
        assert((v << 81u128) == shls_u128(v, 81)) by(bit_vector);
    } else if s == 82 {
        assert((v << 82u128) == shls_u128(v, 82)) by(bit_vector);
    } else if s == 83 {
        assert((v << 83u128) == shls_u128(v, 83)) by(bit_vector);
    } else if s == 84 {
        assert((v << 84u128) == shls_u128(v, 84)) by(bit_vector);
    } else if s == 85 {
        assert((v << 85u128) == shls_u128(v, 85)) by(bit_vector);
    } else if s == 86 {
        assert((v << 86u128) == shls_u128(v, 86)) by(bit_vector);
    } else if s == 87 {
        assert((v << 87u128) == shls_u128(v, 87)) by(bit_vector);
    } else if s == 88 {
        assert((v << 88u128) == shls_u128(v, 88)) by(bit_vector);
    } else if s == 89 {
        assert((v << 89u128) == shls_u128(v, 89)) by(bit_vector);
    } else if s == 90 {
        assert((v << 90u128) == shls_u128(v, 90)) by(bit_vector);
    } else if s == 91 {
        assert((v << 91u128) == shls_u128(v, 91)) by(bit_vector);
    } else if s == 92 {
        assert((v << 92u128) == shls_u128(v, 92)) by(bit_vector);
    } else if s == 93 {
        assert((v << 93u128) == shls_u128(v, 93)) by(bit_vector);
    } else if s == 94 {
        assert((v << 94u128) == shls_u128(v, 94)) by(bit_vector);
    } else if s == 95 {
        assert((v << 95u128) == shls_u128(v, 95)) by(bit_vector);
    } else if s == 96 {
        assert((v << 96u128) == shls_u128(v, 96)) by(bit_vector);
    } else if s == 97 {
        assert((v << 97u128) == shls_u128(v, 97)) by(bit_vector);
    } else if s == 98 {
        assert((v << 98u128) == shls_u128(v, 98)) by(bit_vector);
    } else if s == 99 {
        assert((v << 99u128) == shls_u128(v, 99)) by(bit_vector);
    } else if s == 100 {
        assert((v << 100u128) == shls_u128(v, 100)) by(bit_vector);
    } else if s == 101 {
        assert((v << 101u128) == shls_u128(v, 101)) by(bit_vector);
    } else if s == 102 {
        assert((v << 102u128) == shls_u128(v, 102)) by(bit_vector);
    } else if s == 103 {
        assert((v << 103u128) == shls_u128(v, 103)) by(bit_vector);
    } else if s == 104 {
        assert((v << 104u128) == shls_u128(v, 104)) by(bit_vector);
    } else if s == 105 {
        assert((v << 105u128) == shls_u128(v, 105)) by(bit_vector);
    } else if s == 106 {
        assert((v << 106u128) == shls_u128(v, 106)) by(bit_vector);
    } else if s == 107 {
        assert((v << 107u128) == shls_u128(v, 107)) by(bit_vector);
    } else if s == 108 {
        assert((v << 108u128) == shls_u128(v, 108)) by(bit_vector);
    } else if s == 109 {
        assert((v << 109u128) == shls_u128(v, 109)) by(bit_vector);
    } else if s == 110 {
        assert((v << 110u128) == shls_u128(v, 110)) by(bit_vector);
    } else if s == 111 {
        assert((v << 111u128) == shls_u128(v, 111)) by(bit_vector);
    } else if s == 112 {
        assert((v << 112u128) == shls_u128(v, 112)) by(bit_vector);
    } else if s == 113 {
        assert((v << 113u128) == shls_u128(v, 113)) by(bit_vector);
    } else if s == 114 {
        assert((v << 114u128) == shls_u128(v, 114)) by(bit_vector);
    } else if s == 115 {
        assert((v << 115u128) == shls_u128(v, 115)) by(bit_vector);
    } else if s == 116 {
        assert((v << 116u128) == shls_u128(v, 116)) by(bit_vector);
    } else if s == 117 {
        assert((v << 117u128) == shls_u128(v, 117)) by(bit_vector);
    } else if s == 118 {
        assert((v << 118u128) == shls_u128(v, 118)) by(bit_vector);
    } else if s == 119 {
        assert((v << 119u128) == shls_u128(v, 119)) by(bit_vector);
    } else if s == 120 {
        assert((v << 120u128) == shls_u128(v, 120)) by(bit_vector);
    } else if s == 121 {
        assert((v << 121u128) == shls_u128(v, 121)) by(bit_vector);
    } else if s == 122 {
        assert((v << 122u128) == shls_u128(v, 122)) by(bit_vector);
    } else if s == 123 {
        assert((v << 123u128) == shls_u128(v, 123)) by(bit_vector);
    } else if s == 124 {
        assert((v << 124u128) == shls_u128(v, 124)) by(bit_vector);
    } else if s == 125 {
        assert((v << 125u128) == shls_u128(v, 125)) by(bit_vector);
    } else if s == 126 {
        assert((v << 126u128) == shls_u128(v, 126)) by(bit_vector);
    } else if s == 127 {
        assert((v << 127u128) == shls_u128(v, 127)) by(bit_vector);
    }
}

/* or-add bit bridge: b in {0,1} ==> (a << 1) | b == (a << 1) + b (for the rev accumulation) */
/* Shift-right-by-1 bridge (kept in case the spec side wants division-based phrasing) */
pub broadcast proof fn lem_shr1_u8(v: u8)
    ensures #[trigger] ((v >> 1) as nat) == (v as nat) / 2,
{ assert((v >> 1) == (v / 2)) by(bit_vector); }

#[verifier::allow(broadcast_without_trigger)]
pub broadcast proof fn lem_or_add_u8(a: u8, b: u8)
    requires b <= 1,
    ensures (((a << 1) | b) == ((a << 1) + b)),
{
    if b == 0 {
        assert(((a << 1) | 0) == ((a << 1) + 0)) by(bit_vector);
    } else {
        assert(b == 1);
        assert(((a << 1) | 1) == ((a << 1) + 1)) by(bit_vector);
    }
}

#[verifier::allow(broadcast_without_trigger)]
pub broadcast proof fn lem_or_add_u16(a: u16, b: u16)
    requires b <= 1,
    ensures (((a << 1) | b) == ((a << 1) + b)),
{
    if b == 0 {
        assert(((a << 1) | 0) == ((a << 1) + 0)) by(bit_vector);
    } else {
        assert(b == 1);
        assert(((a << 1) | 1) == ((a << 1) + 1)) by(bit_vector);
    }
}

#[verifier::allow(broadcast_without_trigger)]
pub broadcast proof fn lem_or_add_u32(a: u32, b: u32)
    requires b <= 1,
    ensures (((a << 1) | b) == ((a << 1) + b)),
{
    if b == 0 {
        assert(((a << 1) | 0) == ((a << 1) + 0)) by(bit_vector);
    } else {
        assert(b == 1);
        assert(((a << 1) | 1) == ((a << 1) + 1)) by(bit_vector);
    }
}

#[verifier::allow(broadcast_without_trigger)]
pub broadcast proof fn lem_or_add_u64(a: u64, b: u64)
    requires b <= 1,
    ensures (((a << 1) | b) == ((a << 1) + b)),
{
    if b == 0 {
        assert(((a << 1) | 0) == ((a << 1) + 0)) by(bit_vector);
    } else {
        assert(b == 1);
        assert(((a << 1) | 1) == ((a << 1) + 1)) by(bit_vector);
    }
}

#[verifier::allow(broadcast_without_trigger)]
pub broadcast proof fn lem_or_add_u128(a: u128, b: u128)
    requires b <= 1,
    ensures (((a << 1) | b) == ((a << 1) + b)),
{
    if b == 0 {
        assert(((a << 1) | 0) == ((a << 1) + 0)) by(bit_vector);
    } else {
        assert(b == 1);
        assert(((a << 1) | 1) == ((a << 1) + 1)) by(bit_vector);
    }
}

pub broadcast proof fn lem_shl8_u32b(v: u32)
    ensures #[trigger] ((v << 8) as u32) == shl8_u32m(v),
{ assert((v << 8) == shls_u32(v, 8)) by(bit_vector); }
pub broadcast proof fn lem_shl8_u64b(v: u64)
    ensures #[trigger] ((v << 8) as u64) == shl8_u64m(v),
{ assert((v << 8) == shls_u64(v, 8)) by(bit_vector); }
pub broadcast proof fn lem_shl8_u128b(v: u128)
    ensures #[trigger] ((v << 8) as u128) == shl8_u128m(v),
{ assert((v << 8) == shls_u128(v, 8)) by(bit_vector); }

/* Machine model of bit reversal rev (u8 primitive; u16/u32 by byte composition) */

/* [Adapter: the int-level fact source of masked lower bounds -- self-proved by the bv engine and offered
 *  on the chain as broadcast lemmas; harness/ut_equiv's lane-0 table-contract instantiation uses it to lift the (x & 0xff) bound to the integer layer] */
pub broadcast proof fn lem_andmask_u16(v: u16)
    ensures #[trigger] (v & 0xff) < 256,
{ assert((v & 0xff) < 256) by(bit_vector); }
pub broadcast proof fn lem_andmask_u32(v: u32)
    ensures #[trigger] (v & 0xff) < 256,
{ assert((v & 0xff) < 256) by(bit_vector); }
pub broadcast proof fn lem_andmask_u64(v: u64)
    ensures #[trigger] (v & 0xff) < 256,
{ assert((v & 0xff) < 256) by(bit_vector); }
pub broadcast proof fn lem_andmask_u128(v: u128)
    ensures #[trigger] (v & 0xff) < 256,
{ assert((v & 0xff) < 256) by(bit_vector); }

pub broadcast proof fn lem_shrs_u128(v: u128, s: u128)
    requires s < 128,
    ensures (v >> s) == shrs_u128(v, s as nat),
{
    if s == 0 {
        assert((v >> 0u128) == v) by(bit_vector);
    } else if s == 1 {
        assert((v >> 1u128) == shrs_u128(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v >> 2u128) == shrs_u128(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v >> 3u128) == shrs_u128(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v >> 4u128) == shrs_u128(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v >> 5u128) == shrs_u128(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v >> 6u128) == shrs_u128(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v >> 7u128) == shrs_u128(v, 7)) by(bit_vector);
    } else if s == 8 {
        assert((v >> 8u128) == shrs_u128(v, 8)) by(bit_vector);
    } else if s == 9 {
        assert((v >> 9u128) == shrs_u128(v, 9)) by(bit_vector);
    } else if s == 10 {
        assert((v >> 10u128) == shrs_u128(v, 10)) by(bit_vector);
    } else if s == 11 {
        assert((v >> 11u128) == shrs_u128(v, 11)) by(bit_vector);
    } else if s == 12 {
        assert((v >> 12u128) == shrs_u128(v, 12)) by(bit_vector);
    } else if s == 13 {
        assert((v >> 13u128) == shrs_u128(v, 13)) by(bit_vector);
    } else if s == 14 {
        assert((v >> 14u128) == shrs_u128(v, 14)) by(bit_vector);
    } else if s == 15 {
        assert((v >> 15u128) == shrs_u128(v, 15)) by(bit_vector);
    } else if s == 16 {
        assert((v >> 16u128) == shrs_u128(v, 16)) by(bit_vector);
    } else if s == 17 {
        assert((v >> 17u128) == shrs_u128(v, 17)) by(bit_vector);
    } else if s == 18 {
        assert((v >> 18u128) == shrs_u128(v, 18)) by(bit_vector);
    } else if s == 19 {
        assert((v >> 19u128) == shrs_u128(v, 19)) by(bit_vector);
    } else if s == 20 {
        assert((v >> 20u128) == shrs_u128(v, 20)) by(bit_vector);
    } else if s == 21 {
        assert((v >> 21u128) == shrs_u128(v, 21)) by(bit_vector);
    } else if s == 22 {
        assert((v >> 22u128) == shrs_u128(v, 22)) by(bit_vector);
    } else if s == 23 {
        assert((v >> 23u128) == shrs_u128(v, 23)) by(bit_vector);
    } else if s == 24 {
        assert((v >> 24u128) == shrs_u128(v, 24)) by(bit_vector);
    } else if s == 25 {
        assert((v >> 25u128) == shrs_u128(v, 25)) by(bit_vector);
    } else if s == 26 {
        assert((v >> 26u128) == shrs_u128(v, 26)) by(bit_vector);
    } else if s == 27 {
        assert((v >> 27u128) == shrs_u128(v, 27)) by(bit_vector);
    } else if s == 28 {
        assert((v >> 28u128) == shrs_u128(v, 28)) by(bit_vector);
    } else if s == 29 {
        assert((v >> 29u128) == shrs_u128(v, 29)) by(bit_vector);
    } else if s == 30 {
        assert((v >> 30u128) == shrs_u128(v, 30)) by(bit_vector);
    } else if s == 31 {
        assert((v >> 31u128) == shrs_u128(v, 31)) by(bit_vector);
    } else if s == 32 {
        assert((v >> 32u128) == shrs_u128(v, 32)) by(bit_vector);
    } else if s == 33 {
        assert((v >> 33u128) == shrs_u128(v, 33)) by(bit_vector);
    } else if s == 34 {
        assert((v >> 34u128) == shrs_u128(v, 34)) by(bit_vector);
    } else if s == 35 {
        assert((v >> 35u128) == shrs_u128(v, 35)) by(bit_vector);
    } else if s == 36 {
        assert((v >> 36u128) == shrs_u128(v, 36)) by(bit_vector);
    } else if s == 37 {
        assert((v >> 37u128) == shrs_u128(v, 37)) by(bit_vector);
    } else if s == 38 {
        assert((v >> 38u128) == shrs_u128(v, 38)) by(bit_vector);
    } else if s == 39 {
        assert((v >> 39u128) == shrs_u128(v, 39)) by(bit_vector);
    } else if s == 40 {
        assert((v >> 40u128) == shrs_u128(v, 40)) by(bit_vector);
    } else if s == 41 {
        assert((v >> 41u128) == shrs_u128(v, 41)) by(bit_vector);
    } else if s == 42 {
        assert((v >> 42u128) == shrs_u128(v, 42)) by(bit_vector);
    } else if s == 43 {
        assert((v >> 43u128) == shrs_u128(v, 43)) by(bit_vector);
    } else if s == 44 {
        assert((v >> 44u128) == shrs_u128(v, 44)) by(bit_vector);
    } else if s == 45 {
        assert((v >> 45u128) == shrs_u128(v, 45)) by(bit_vector);
    } else if s == 46 {
        assert((v >> 46u128) == shrs_u128(v, 46)) by(bit_vector);
    } else if s == 47 {
        assert((v >> 47u128) == shrs_u128(v, 47)) by(bit_vector);
    } else if s == 48 {
        assert((v >> 48u128) == shrs_u128(v, 48)) by(bit_vector);
    } else if s == 49 {
        assert((v >> 49u128) == shrs_u128(v, 49)) by(bit_vector);
    } else if s == 50 {
        assert((v >> 50u128) == shrs_u128(v, 50)) by(bit_vector);
    } else if s == 51 {
        assert((v >> 51u128) == shrs_u128(v, 51)) by(bit_vector);
    } else if s == 52 {
        assert((v >> 52u128) == shrs_u128(v, 52)) by(bit_vector);
    } else if s == 53 {
        assert((v >> 53u128) == shrs_u128(v, 53)) by(bit_vector);
    } else if s == 54 {
        assert((v >> 54u128) == shrs_u128(v, 54)) by(bit_vector);
    } else if s == 55 {
        assert((v >> 55u128) == shrs_u128(v, 55)) by(bit_vector);
    } else if s == 56 {
        assert((v >> 56u128) == shrs_u128(v, 56)) by(bit_vector);
    } else if s == 57 {
        assert((v >> 57u128) == shrs_u128(v, 57)) by(bit_vector);
    } else if s == 58 {
        assert((v >> 58u128) == shrs_u128(v, 58)) by(bit_vector);
    } else if s == 59 {
        assert((v >> 59u128) == shrs_u128(v, 59)) by(bit_vector);
    } else if s == 60 {
        assert((v >> 60u128) == shrs_u128(v, 60)) by(bit_vector);
    } else if s == 61 {
        assert((v >> 61u128) == shrs_u128(v, 61)) by(bit_vector);
    } else if s == 62 {
        assert((v >> 62u128) == shrs_u128(v, 62)) by(bit_vector);
    } else if s == 63 {
        assert((v >> 63u128) == shrs_u128(v, 63)) by(bit_vector);
    } else if s == 64 {
        assert((v >> 64u128) == shrs_u128(v, 64)) by(bit_vector);
    } else if s == 65 {
        assert((v >> 65u128) == shrs_u128(v, 65)) by(bit_vector);
    } else if s == 66 {
        assert((v >> 66u128) == shrs_u128(v, 66)) by(bit_vector);
    } else if s == 67 {
        assert((v >> 67u128) == shrs_u128(v, 67)) by(bit_vector);
    } else if s == 68 {
        assert((v >> 68u128) == shrs_u128(v, 68)) by(bit_vector);
    } else if s == 69 {
        assert((v >> 69u128) == shrs_u128(v, 69)) by(bit_vector);
    } else if s == 70 {
        assert((v >> 70u128) == shrs_u128(v, 70)) by(bit_vector);
    } else if s == 71 {
        assert((v >> 71u128) == shrs_u128(v, 71)) by(bit_vector);
    } else if s == 72 {
        assert((v >> 72u128) == shrs_u128(v, 72)) by(bit_vector);
    } else if s == 73 {
        assert((v >> 73u128) == shrs_u128(v, 73)) by(bit_vector);
    } else if s == 74 {
        assert((v >> 74u128) == shrs_u128(v, 74)) by(bit_vector);
    } else if s == 75 {
        assert((v >> 75u128) == shrs_u128(v, 75)) by(bit_vector);
    } else if s == 76 {
        assert((v >> 76u128) == shrs_u128(v, 76)) by(bit_vector);
    } else if s == 77 {
        assert((v >> 77u128) == shrs_u128(v, 77)) by(bit_vector);
    } else if s == 78 {
        assert((v >> 78u128) == shrs_u128(v, 78)) by(bit_vector);
    } else if s == 79 {
        assert((v >> 79u128) == shrs_u128(v, 79)) by(bit_vector);
    } else if s == 80 {
        assert((v >> 80u128) == shrs_u128(v, 80)) by(bit_vector);
    } else if s == 81 {
        assert((v >> 81u128) == shrs_u128(v, 81)) by(bit_vector);
    } else if s == 82 {
        assert((v >> 82u128) == shrs_u128(v, 82)) by(bit_vector);
    } else if s == 83 {
        assert((v >> 83u128) == shrs_u128(v, 83)) by(bit_vector);
    } else if s == 84 {
        assert((v >> 84u128) == shrs_u128(v, 84)) by(bit_vector);
    } else if s == 85 {
        assert((v >> 85u128) == shrs_u128(v, 85)) by(bit_vector);
    } else if s == 86 {
        assert((v >> 86u128) == shrs_u128(v, 86)) by(bit_vector);
    } else if s == 87 {
        assert((v >> 87u128) == shrs_u128(v, 87)) by(bit_vector);
    } else if s == 88 {
        assert((v >> 88u128) == shrs_u128(v, 88)) by(bit_vector);
    } else if s == 89 {
        assert((v >> 89u128) == shrs_u128(v, 89)) by(bit_vector);
    } else if s == 90 {
        assert((v >> 90u128) == shrs_u128(v, 90)) by(bit_vector);
    } else if s == 91 {
        assert((v >> 91u128) == shrs_u128(v, 91)) by(bit_vector);
    } else if s == 92 {
        assert((v >> 92u128) == shrs_u128(v, 92)) by(bit_vector);
    } else if s == 93 {
        assert((v >> 93u128) == shrs_u128(v, 93)) by(bit_vector);
    } else if s == 94 {
        assert((v >> 94u128) == shrs_u128(v, 94)) by(bit_vector);
    } else if s == 95 {
        assert((v >> 95u128) == shrs_u128(v, 95)) by(bit_vector);
    } else if s == 96 {
        assert((v >> 96u128) == shrs_u128(v, 96)) by(bit_vector);
    } else if s == 97 {
        assert((v >> 97u128) == shrs_u128(v, 97)) by(bit_vector);
    } else if s == 98 {
        assert((v >> 98u128) == shrs_u128(v, 98)) by(bit_vector);
    } else if s == 99 {
        assert((v >> 99u128) == shrs_u128(v, 99)) by(bit_vector);
    } else if s == 100 {
        assert((v >> 100u128) == shrs_u128(v, 100)) by(bit_vector);
    } else if s == 101 {
        assert((v >> 101u128) == shrs_u128(v, 101)) by(bit_vector);
    } else if s == 102 {
        assert((v >> 102u128) == shrs_u128(v, 102)) by(bit_vector);
    } else if s == 103 {
        assert((v >> 103u128) == shrs_u128(v, 103)) by(bit_vector);
    } else if s == 104 {
        assert((v >> 104u128) == shrs_u128(v, 104)) by(bit_vector);
    } else if s == 105 {
        assert((v >> 105u128) == shrs_u128(v, 105)) by(bit_vector);
    } else if s == 106 {
        assert((v >> 106u128) == shrs_u128(v, 106)) by(bit_vector);
    } else if s == 107 {
        assert((v >> 107u128) == shrs_u128(v, 107)) by(bit_vector);
    } else if s == 108 {
        assert((v >> 108u128) == shrs_u128(v, 108)) by(bit_vector);
    } else if s == 109 {
        assert((v >> 109u128) == shrs_u128(v, 109)) by(bit_vector);
    } else if s == 110 {
        assert((v >> 110u128) == shrs_u128(v, 110)) by(bit_vector);
    } else if s == 111 {
        assert((v >> 111u128) == shrs_u128(v, 111)) by(bit_vector);
    } else if s == 112 {
        assert((v >> 112u128) == shrs_u128(v, 112)) by(bit_vector);
    } else if s == 113 {
        assert((v >> 113u128) == shrs_u128(v, 113)) by(bit_vector);
    } else if s == 114 {
        assert((v >> 114u128) == shrs_u128(v, 114)) by(bit_vector);
    } else if s == 115 {
        assert((v >> 115u128) == shrs_u128(v, 115)) by(bit_vector);
    } else if s == 116 {
        assert((v >> 116u128) == shrs_u128(v, 116)) by(bit_vector);
    } else if s == 117 {
        assert((v >> 117u128) == shrs_u128(v, 117)) by(bit_vector);
    } else if s == 118 {
        assert((v >> 118u128) == shrs_u128(v, 118)) by(bit_vector);
    } else if s == 119 {
        assert((v >> 119u128) == shrs_u128(v, 119)) by(bit_vector);
    } else if s == 120 {
        assert((v >> 120u128) == shrs_u128(v, 120)) by(bit_vector);
    } else if s == 121 {
        assert((v >> 121u128) == shrs_u128(v, 121)) by(bit_vector);
    } else if s == 122 {
        assert((v >> 122u128) == shrs_u128(v, 122)) by(bit_vector);
    } else if s == 123 {
        assert((v >> 123u128) == shrs_u128(v, 123)) by(bit_vector);
    } else if s == 124 {
        assert((v >> 124u128) == shrs_u128(v, 124)) by(bit_vector);
    } else if s == 125 {
        assert((v >> 125u128) == shrs_u128(v, 125)) by(bit_vector);
    } else if s == 126 {
        assert((v >> 126u128) == shrs_u128(v, 126)) by(bit_vector);
    } else if s == 127 {
        assert((v >> 127u128) == shrs_u128(v, 127)) by(bit_vector);
    }
}

pub broadcast proof fn lem_shrs_u8(v: u8, s: u8)
    requires s < 8,
    ensures (v >> s) == shrs_u8(v, s as nat),
{
    if s == 0 {
        assert((v >> 0u8) == v) by(bit_vector);
    } else if s == 1 {
        assert((v >> 1u8) == shrs_u8(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v >> 2u8) == shrs_u8(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v >> 3u8) == shrs_u8(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v >> 4u8) == shrs_u8(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v >> 5u8) == shrs_u8(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v >> 6u8) == shrs_u8(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v >> 7u8) == shrs_u8(v, 7)) by(bit_vector);
    }
}

pub broadcast proof fn lem_shrs_u16(v: u16, s: u16)
    requires s < 16,
    ensures (v >> s) == shrs_u16(v, s as nat),
{
    if s == 0 {
        assert((v >> 0u16) == v) by(bit_vector);
    } else if s == 1 {
        assert((v >> 1u16) == shrs_u16(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v >> 2u16) == shrs_u16(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v >> 3u16) == shrs_u16(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v >> 4u16) == shrs_u16(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v >> 5u16) == shrs_u16(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v >> 6u16) == shrs_u16(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v >> 7u16) == shrs_u16(v, 7)) by(bit_vector);
    } else if s == 8 {
        assert((v >> 8u16) == shrs_u16(v, 8)) by(bit_vector);
    } else if s == 9 {
        assert((v >> 9u16) == shrs_u16(v, 9)) by(bit_vector);
    } else if s == 10 {
        assert((v >> 10u16) == shrs_u16(v, 10)) by(bit_vector);
    } else if s == 11 {
        assert((v >> 11u16) == shrs_u16(v, 11)) by(bit_vector);
    } else if s == 12 {
        assert((v >> 12u16) == shrs_u16(v, 12)) by(bit_vector);
    } else if s == 13 {
        assert((v >> 13u16) == shrs_u16(v, 13)) by(bit_vector);
    } else if s == 14 {
        assert((v >> 14u16) == shrs_u16(v, 14)) by(bit_vector);
    } else if s == 15 {
        assert((v >> 15u16) == shrs_u16(v, 15)) by(bit_vector);
    }
}

pub broadcast proof fn lem_shrs_u32(v: u32, s: u32)
    requires s < 32,
    ensures (v >> s) == shrs_u32(v, s as nat),
{
    if s == 0 {
        assert((v >> 0u32) == v) by(bit_vector);
    } else if s == 1 {
        assert((v >> 1u32) == shrs_u32(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v >> 2u32) == shrs_u32(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v >> 3u32) == shrs_u32(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v >> 4u32) == shrs_u32(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v >> 5u32) == shrs_u32(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v >> 6u32) == shrs_u32(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v >> 7u32) == shrs_u32(v, 7)) by(bit_vector);
    } else if s == 8 {
        assert((v >> 8u32) == shrs_u32(v, 8)) by(bit_vector);
    } else if s == 9 {
        assert((v >> 9u32) == shrs_u32(v, 9)) by(bit_vector);
    } else if s == 10 {
        assert((v >> 10u32) == shrs_u32(v, 10)) by(bit_vector);
    } else if s == 11 {
        assert((v >> 11u32) == shrs_u32(v, 11)) by(bit_vector);
    } else if s == 12 {
        assert((v >> 12u32) == shrs_u32(v, 12)) by(bit_vector);
    } else if s == 13 {
        assert((v >> 13u32) == shrs_u32(v, 13)) by(bit_vector);
    } else if s == 14 {
        assert((v >> 14u32) == shrs_u32(v, 14)) by(bit_vector);
    } else if s == 15 {
        assert((v >> 15u32) == shrs_u32(v, 15)) by(bit_vector);
    } else if s == 16 {
        assert((v >> 16u32) == shrs_u32(v, 16)) by(bit_vector);
    } else if s == 17 {
        assert((v >> 17u32) == shrs_u32(v, 17)) by(bit_vector);
    } else if s == 18 {
        assert((v >> 18u32) == shrs_u32(v, 18)) by(bit_vector);
    } else if s == 19 {
        assert((v >> 19u32) == shrs_u32(v, 19)) by(bit_vector);
    } else if s == 20 {
        assert((v >> 20u32) == shrs_u32(v, 20)) by(bit_vector);
    } else if s == 21 {
        assert((v >> 21u32) == shrs_u32(v, 21)) by(bit_vector);
    } else if s == 22 {
        assert((v >> 22u32) == shrs_u32(v, 22)) by(bit_vector);
    } else if s == 23 {
        assert((v >> 23u32) == shrs_u32(v, 23)) by(bit_vector);
    } else if s == 24 {
        assert((v >> 24u32) == shrs_u32(v, 24)) by(bit_vector);
    } else if s == 25 {
        assert((v >> 25u32) == shrs_u32(v, 25)) by(bit_vector);
    } else if s == 26 {
        assert((v >> 26u32) == shrs_u32(v, 26)) by(bit_vector);
    } else if s == 27 {
        assert((v >> 27u32) == shrs_u32(v, 27)) by(bit_vector);
    } else if s == 28 {
        assert((v >> 28u32) == shrs_u32(v, 28)) by(bit_vector);
    } else if s == 29 {
        assert((v >> 29u32) == shrs_u32(v, 29)) by(bit_vector);
    } else if s == 30 {
        assert((v >> 30u32) == shrs_u32(v, 30)) by(bit_vector);
    } else if s == 31 {
        assert((v >> 31u32) == shrs_u32(v, 31)) by(bit_vector);
    }
}

pub broadcast proof fn lem_shrs_u64(v: u64, s: u64)
    requires s < 64,
    ensures (v >> s) == shrs_u64(v, s as nat),
{
    if s == 0 {
        assert((v >> 0u64) == v) by(bit_vector);
    } else if s == 1 {
        assert((v >> 1u64) == shrs_u64(v, 1)) by(bit_vector);
    } else if s == 2 {
        assert((v >> 2u64) == shrs_u64(v, 2)) by(bit_vector);
    } else if s == 3 {
        assert((v >> 3u64) == shrs_u64(v, 3)) by(bit_vector);
    } else if s == 4 {
        assert((v >> 4u64) == shrs_u64(v, 4)) by(bit_vector);
    } else if s == 5 {
        assert((v >> 5u64) == shrs_u64(v, 5)) by(bit_vector);
    } else if s == 6 {
        assert((v >> 6u64) == shrs_u64(v, 6)) by(bit_vector);
    } else if s == 7 {
        assert((v >> 7u64) == shrs_u64(v, 7)) by(bit_vector);
    } else if s == 8 {
        assert((v >> 8u64) == shrs_u64(v, 8)) by(bit_vector);
    } else if s == 9 {
        assert((v >> 9u64) == shrs_u64(v, 9)) by(bit_vector);
    } else if s == 10 {
        assert((v >> 10u64) == shrs_u64(v, 10)) by(bit_vector);
    } else if s == 11 {
        assert((v >> 11u64) == shrs_u64(v, 11)) by(bit_vector);
    } else if s == 12 {
        assert((v >> 12u64) == shrs_u64(v, 12)) by(bit_vector);
    } else if s == 13 {
        assert((v >> 13u64) == shrs_u64(v, 13)) by(bit_vector);
    } else if s == 14 {
        assert((v >> 14u64) == shrs_u64(v, 14)) by(bit_vector);
    } else if s == 15 {
        assert((v >> 15u64) == shrs_u64(v, 15)) by(bit_vector);
    } else if s == 16 {
        assert((v >> 16u64) == shrs_u64(v, 16)) by(bit_vector);
    } else if s == 17 {
        assert((v >> 17u64) == shrs_u64(v, 17)) by(bit_vector);
    } else if s == 18 {
        assert((v >> 18u64) == shrs_u64(v, 18)) by(bit_vector);
    } else if s == 19 {
        assert((v >> 19u64) == shrs_u64(v, 19)) by(bit_vector);
    } else if s == 20 {
        assert((v >> 20u64) == shrs_u64(v, 20)) by(bit_vector);
    } else if s == 21 {
        assert((v >> 21u64) == shrs_u64(v, 21)) by(bit_vector);
    } else if s == 22 {
        assert((v >> 22u64) == shrs_u64(v, 22)) by(bit_vector);
    } else if s == 23 {
        assert((v >> 23u64) == shrs_u64(v, 23)) by(bit_vector);
    } else if s == 24 {
        assert((v >> 24u64) == shrs_u64(v, 24)) by(bit_vector);
    } else if s == 25 {
        assert((v >> 25u64) == shrs_u64(v, 25)) by(bit_vector);
    } else if s == 26 {
        assert((v >> 26u64) == shrs_u64(v, 26)) by(bit_vector);
    } else if s == 27 {
        assert((v >> 27u64) == shrs_u64(v, 27)) by(bit_vector);
    } else if s == 28 {
        assert((v >> 28u64) == shrs_u64(v, 28)) by(bit_vector);
    } else if s == 29 {
        assert((v >> 29u64) == shrs_u64(v, 29)) by(bit_vector);
    } else if s == 30 {
        assert((v >> 30u64) == shrs_u64(v, 30)) by(bit_vector);
    } else if s == 31 {
        assert((v >> 31u64) == shrs_u64(v, 31)) by(bit_vector);
    } else if s == 32 {
        assert((v >> 32u64) == shrs_u64(v, 32)) by(bit_vector);
    } else if s == 33 {
        assert((v >> 33u64) == shrs_u64(v, 33)) by(bit_vector);
    } else if s == 34 {
        assert((v >> 34u64) == shrs_u64(v, 34)) by(bit_vector);
    } else if s == 35 {
        assert((v >> 35u64) == shrs_u64(v, 35)) by(bit_vector);
    } else if s == 36 {
        assert((v >> 36u64) == shrs_u64(v, 36)) by(bit_vector);
    } else if s == 37 {
        assert((v >> 37u64) == shrs_u64(v, 37)) by(bit_vector);
    } else if s == 38 {
        assert((v >> 38u64) == shrs_u64(v, 38)) by(bit_vector);
    } else if s == 39 {
        assert((v >> 39u64) == shrs_u64(v, 39)) by(bit_vector);
    } else if s == 40 {
        assert((v >> 40u64) == shrs_u64(v, 40)) by(bit_vector);
    } else if s == 41 {
        assert((v >> 41u64) == shrs_u64(v, 41)) by(bit_vector);
    } else if s == 42 {
        assert((v >> 42u64) == shrs_u64(v, 42)) by(bit_vector);
    } else if s == 43 {
        assert((v >> 43u64) == shrs_u64(v, 43)) by(bit_vector);
    } else if s == 44 {
        assert((v >> 44u64) == shrs_u64(v, 44)) by(bit_vector);
    } else if s == 45 {
        assert((v >> 45u64) == shrs_u64(v, 45)) by(bit_vector);
    } else if s == 46 {
        assert((v >> 46u64) == shrs_u64(v, 46)) by(bit_vector);
    } else if s == 47 {
        assert((v >> 47u64) == shrs_u64(v, 47)) by(bit_vector);
    } else if s == 48 {
        assert((v >> 48u64) == shrs_u64(v, 48)) by(bit_vector);
    } else if s == 49 {
        assert((v >> 49u64) == shrs_u64(v, 49)) by(bit_vector);
    } else if s == 50 {
        assert((v >> 50u64) == shrs_u64(v, 50)) by(bit_vector);
    } else if s == 51 {
        assert((v >> 51u64) == shrs_u64(v, 51)) by(bit_vector);
    } else if s == 52 {
        assert((v >> 52u64) == shrs_u64(v, 52)) by(bit_vector);
    } else if s == 53 {
        assert((v >> 53u64) == shrs_u64(v, 53)) by(bit_vector);
    } else if s == 54 {
        assert((v >> 54u64) == shrs_u64(v, 54)) by(bit_vector);
    } else if s == 55 {
        assert((v >> 55u64) == shrs_u64(v, 55)) by(bit_vector);
    } else if s == 56 {
        assert((v >> 56u64) == shrs_u64(v, 56)) by(bit_vector);
    } else if s == 57 {
        assert((v >> 57u64) == shrs_u64(v, 57)) by(bit_vector);
    } else if s == 58 {
        assert((v >> 58u64) == shrs_u64(v, 58)) by(bit_vector);
    } else if s == 59 {
        assert((v >> 59u64) == shrs_u64(v, 59)) by(bit_vector);
    } else if s == 60 {
        assert((v >> 60u64) == shrs_u64(v, 60)) by(bit_vector);
    } else if s == 61 {
        assert((v >> 61u64) == shrs_u64(v, 61)) by(bit_vector);
    } else if s == 62 {
        assert((v >> 62u64) == shrs_u64(v, 62)) by(bit_vector);
    } else if s == 63 {
        assert((v >> 63u64) == shrs_u64(v, 63)) by(bit_vector);
    }
}

} // verus!
