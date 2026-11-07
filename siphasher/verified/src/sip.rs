//! verified/src/sip.rs -- Verus-translated mirror of code/src/sip.rs
//! (pin 2fcf2a7), the 64-bit SipHash
//!
//! Translation adaptations (auditability notes; the semantics are
//! cross-checked API by API by the runtime re-verification drivers):
//! - [Origin Rust: code/src/sip.rs:55-78 `Hasher<S: Sip>`/`State`]
//!   The upstream `PhantomData<S>` static generic dispatch becomes the
//!   two entities `Hasher13` / `Hasher24`;
//!   the nested `State{v0,v2,v1,v3}` (SIMD field order) becomes the flat
//!   fields v0,v1,v2,v3 (same semantic name and order).
//! - [Origin Rust: code/src/sip.rs:259-282 `short_write<T>`] The generic
//!   is expanded once into the five mirrors
//!   write_u8/u16/u32/u64/usize; usize takes size = 8 per the host's
//!   64-bit width
//!   (a width assumption).
//! - [Origin Rust: `x.to_le()` / `to_le_bytes` / `from_le_bytes`]
//!   Under the host little-endian (LE) assumption to_le() is the identity;
//!   the translated bodies assemble directly with LE semantics,
//!   the assumption enters the assumption ledger and is checked on this
//!   machine by the runtime re-verification.
//! - [Origin Rust: `self.length: usize`] -> `length: u64` (equal width on
//!   the 64-bit host);
//!   the upstream plain `+=` carries a u64 overflow panic face on debug
//!   builds (a priori unreachable on 64-bit targets) -- this translation
//!   models that obligation explicitly as a `requires` upper bound.
//! - [Origin Rust: `impl hash::Hasher for ...`] The std trait becomes
//!   inherent methods
//!   (write/finish/write_uN), forwarding statement-by-statement
//!   isomorphically.
//! - `write(&[u8])`/`hash(&[u8])` (the slice paths): L0 contract
//!   (panic/out-of-bounds free);
//!   the value-level spec is blocked by the encoding limitation of
//!   Expr-if gates + Seq-index terms not passing into the bv channel,
//!   covered by the harness scalar paths
//!   (write_uN + finish) + the runtime re-verification.

use vstd::prelude::*;

use crate::common::{compress_exec, compress_spec, load_u64_le, u8to64_le_exec};

verus! {

/* ============================================================
 * State views and spec twins
 * H9 = (k0, k1, v0, v1, v2, v3, length, tail, ntail)
 * ============================================================ */

pub type H9 = (u64, u64, u64, u64, u64, u64, u64, u64, u64);
pub type T4 = (u64, u64, u64, u64);

pub struct Hasher13 {
    pub k0: u64,
    pub k1: u64,
    pub v0: u64,
    pub v1: u64,
    pub v2: u64,
    pub v3: u64,
    pub length: u64,
    pub tail: u64,
    pub ntail: u64,
}

pub struct Hasher24 {
    pub k0: u64,
    pub k1: u64,
    pub v0: u64,
    pub v1: u64,
    pub v2: u64,
    pub v3: u64,
    pub length: u64,
    pub tail: u64,
    pub ntail: u64,
}

pub open spec fn hash13_view(h: &Hasher13) -> H9 {
    (h.k0, h.k1, h.v0, h.v1, h.v2, h.v3, h.length, h.tail, h.ntail)
}

pub open spec fn hash24_view(h: &Hasher24) -> H9 {
    (h.k0, h.k1, h.v0, h.v1, h.v2, h.v3, h.length, h.tail, h.ntail)
}

#[allow(non_snake_case)]
pub open spec fn SPEC_RESET(k0: u64, k1: u64) -> T4 {
    (k0 ^ 0x736f6d6570736575u64, k1 ^ 0x646f72616e646f6du64,
     k0 ^ 0x6c7967656e657261u64, k1 ^ 0x7465646279746573u64)
}

#[verifier::inline]
pub open spec fn spec_new_13(k0: u64, k1: u64) -> H9 {
    (k0, k1, SPEC_RESET(k0, k1).0, SPEC_RESET(k0, k1).1,
     SPEC_RESET(k0, k1).2, SPEC_RESET(k0, k1).3, 0, 0, 0)
}

#[verifier::inline]
pub open spec fn spec_new_24(k0: u64, k1: u64) -> H9 {
    (k0, k1, SPEC_RESET(k0, k1).0, SPEC_RESET(k0, k1).1,
     SPEC_RESET(k0, k1).2, SPEC_RESET(k0, k1).3, 0, 0, 0)
}

/// The generic semantics of short_write (upstream sip.rs:259-282,
/// statement-by-statement isomorphic).
/// x is the zero-extended value, size in 1..=8; the call side requires
/// ntail < 8.
#[verifier::inline]
pub open spec fn spec_short_write_13(v: H9, x: u64, size: u64) -> H9 {
    let (k0, k1, v0, v1, v2, v3, length, tail, ntail) = v;
    let new_tail = tail | (x << (8 * ntail));
    let needed: u64 = (8 - ntail) as u64;
    if size < needed {
        (k0, k1, v0, v1, v2, v3, length.wrapping_add(size), new_tail,
         ntail.wrapping_add(size))
    } else {
        let s1 = compress_spec((v0, v1, v2, v3 ^ new_tail));
        let s2 = (s1.0 ^ new_tail, s1.1, s1.2, s1.3);
        (k0, k1, s2.0, s2.1, s2.2, s2.3, length.wrapping_add(size),
         if needed < 8 { (x >> (8 * needed)) } else { 0u64 },
         size.wrapping_sub(needed))
    }
}

#[verifier::inline]
pub open spec fn spec_short_write_24(v: H9, x: u64, size: u64) -> H9 {
    let (k0, k1, v0, v1, v2, v3, length, tail, ntail) = v;
    let new_tail = tail | (x << (8 * ntail));
    let needed: u64 = (8 - ntail) as u64;
    if size < needed {
        (k0, k1, v0, v1, v2, v3, length.wrapping_add(size), new_tail,
         ntail.wrapping_add(size))
    } else {
        let s1 = compress_spec((v0, v1, v2, v3 ^ new_tail));
        let s1b = compress_spec(s1);
        let s2 = (s1b.0 ^ new_tail, s1b.1, s1b.2, s1b.3);
        (k0, k1, s2.0, s2.1, s2.2, s2.3, length.wrapping_add(size),
         if needed < 8 { (x >> (8 * needed)) } else { 0u64 },
         size.wrapping_sub(needed))
    }
}

#[verifier::inline]
pub open spec fn spec_write_u8_13(h: H9, b: u8) -> H9 {
    spec_short_write_13(h, b as u64, 1)
}

#[verifier::inline]
pub open spec fn spec_write_u16_13(h: H9, b: u16) -> H9 {
    spec_short_write_13(h, b as u64, 2)
}

#[verifier::inline]
pub open spec fn spec_write_u32_13(h: H9, b: u32) -> H9 {
    spec_short_write_13(h, b as u64, 4)
}

#[verifier::inline]
pub open spec fn spec_write_u64_13(h: H9, b: u64) -> H9 {
    spec_short_write_13(h, b, 8)
}

#[cfg(target_pointer_width = "64")]
#[verifier::inline]
pub open spec fn spec_write_usize_13(h: H9, b: u64) -> H9 {
    spec_short_write_13(h, b, 8)
}

#[verifier::inline]
pub open spec fn spec_write_u8_24(h: H9, b: u8) -> H9 {
    spec_short_write_24(h, b as u64, 1)
}

#[verifier::inline]
pub open spec fn spec_write_u16_24(h: H9, b: u16) -> H9 {
    spec_short_write_24(h, b as u64, 2)
}

#[verifier::inline]
pub open spec fn spec_write_u32_24(h: H9, b: u32) -> H9 {
    spec_short_write_24(h, b as u64, 4)
}

#[verifier::inline]
pub open spec fn spec_write_u64_24(h: H9, b: u64) -> H9 {
    spec_short_write_24(h, b, 8)
}

/// Semantics of finish_with_state (upstream sip.rs:320-332),
/// SipHash-1-3.
/// b = ((length & 0xff) << 56) | tail;
/// v3 ^= b; c_rounds (x1); v0 ^= b; v2 ^= 0xff; d_rounds (x3); reduce.
#[verifier::inline]
pub open spec fn spec_finish_13(h: H9) -> u64 {
    let (k0, k1, v0, v1, v2, v3, length, tail, ntail) = h;
    let b = ((length & 0xffu64) << 56) | tail;
    let s1 = compress_spec((v0, v1, v2, v3 ^ b));
    let s2 = (s1.0 ^ b, s1.1, s1.2 ^ 0xffu64, s1.3);
    let d1 = compress_spec(s2);
    let d2 = compress_spec(d1);
    let d3 = compress_spec(d2);
    d3.0 ^ d3.1 ^ d3.2 ^ d3.3
}

/// Same as above, SipHash-2-4 (c x2, d x4).
#[verifier::inline]
pub open spec fn spec_finish_24(h: H9) -> u64 {
    let (k0, k1, v0, v1, v2, v3, length, tail, ntail) = h;
    let b = ((length & 0xffu64) << 56) | tail;
    let s1 = compress_spec((v0, v1, v2, v3 ^ b));
    let s1b = compress_spec(s1);
    let s2 = (s1b.0 ^ b, s1b.1, s1b.2 ^ 0xffu64, s1b.3);
    let d1 = compress_spec(s2);
    let d2 = compress_spec(d1);
    let d3 = compress_spec(d2);
    let d4 = compress_spec(d3);
    d4.0 ^ d4.1 ^ d4.2 ^ d4.3
}

/// The overflow obligation of `length +=` brought up front (the
/// upstream usize `+=` debug panic face,
/// panic-classification F1: a priori unreachable on 64-bit targets;
/// this constant is the modeled upper bound).
#[allow(non_snake_case)]
pub open spec fn LENGTH_BOUND(h: H9) -> bool {
    h.6 <= 0xffff_ffff_ffff_fff0u64
}

/* ============================================================
 * exec -- Hasher13
 * ============================================================ */

impl Hasher13 {

    /// [Origin Rust: new_with_keys + reset (sip.rs:218-245)]
    pub exec fn new_with_keys(key0: u64, key1: u64) -> (r: Hasher13)
        ensures hash13_view(&r) == spec_new_13(key0, key1)
    {
        Hasher13 {
            k0: key0,
            k1: key1,
            v0: key0 ^ 0x736f6d6570736575u64,
            v1: key1 ^ 0x646f72616e646f6du64,
            v2: key0 ^ 0x6c7967656e657261u64,
            v3: key1 ^ 0x7465646279746573u64,
            length: 0,
            tail: 0,
            ntail: 0,
        }
    }

    /// [Origin Rust: short_write(i, i as u64), T=u8] (sip.rs:453-455)
    pub exec fn write_u8(&mut self, i: u8)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures hash13_view(final(self)) == spec_write_u8_13(hash13_view(old(self)), i)
    {
        let size: u64 = 1;
        let x: u64 = i as u64;
        self.length += size;

        let needed = 8u64 - self.ntail;
        self.tail = self.tail | (x << (8 * self.ntail));
        if size < needed {
            self.ntail += size;
            return;
        }
        self.v3 ^= self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
        self.v0 = s1.0 ^ self.tail;
        self.v1 = s1.1;
        self.v2 = s1.2;
        self.v3 = s1.3;
        self.ntail = size - needed;
        self.tail = if needed < 8 { x >> (8 * needed) } else { 0u64 };
    }

    /// [Origin Rust: short_write(i, i.to_le() as u64), T=u16] (sip.rs:458-460)
    /// LE host assumption: to_le() is the identity (header note).
    pub exec fn write_u16(&mut self, i: u16)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures hash13_view(final(self)) == spec_write_u16_13(hash13_view(old(self)), i)
    {
        let size: u64 = 2;
        let x: u64 = i as u64;
        self.length += size;

        let needed = 8u64 - self.ntail;
        self.tail = self.tail | (x << (8 * self.ntail));
        if size < needed {
            self.ntail += size;
            return;
        }
        self.v3 ^= self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
        self.v0 = s1.0 ^ self.tail;
        self.v1 = s1.1;
        self.v2 = s1.2;
        self.v3 = s1.3;
        self.ntail = size - needed;
        self.tail = if needed < 8 { x >> (8 * needed) } else { 0u64 };
    }

    /// [Origin Rust: short_write(i, i.to_le() as u64), T=u32] (sip.rs:463-465)
    pub exec fn write_u32(&mut self, i: u32)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures hash13_view(final(self)) == spec_write_u32_13(hash13_view(old(self)), i)
    {
        let size: u64 = 4;
        let x: u64 = i as u64;
        self.length += size;

        let needed = 8u64 - self.ntail;
        self.tail = self.tail | (x << (8 * self.ntail));
        if size < needed {
            self.ntail += size;
            return;
        }
        self.v3 ^= self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
        self.v0 = s1.0 ^ self.tail;
        self.v1 = s1.1;
        self.v2 = s1.2;
        self.v3 = s1.3;
        self.ntail = size - needed;
        self.tail = if needed < 8 { x >> (8 * needed) } else { 0u64 };
    }

    /// [Origin Rust: short_write(i, i.to_le()), T=u64] (sip.rs:468-470)
    pub exec fn write_u64(&mut self, i: u64)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures hash13_view(final(self)) == spec_write_u64_13(hash13_view(old(self)), i)
    {
        let size: u64 = 8;
        let x: u64 = i;
        self.length += size;

        let needed = 8u64 - self.ntail;
        self.tail = self.tail | (x << (8 * self.ntail));
        if size < needed {
            self.ntail += size;
            return;
        }
        self.v3 ^= self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
        self.v0 = s1.0 ^ self.tail;
        self.v1 = s1.1;
        self.v2 = s1.2;
        self.v3 = s1.3;
        self.ntail = size - needed;
        self.tail = if needed < 8 { x >> (8 * needed) } else { 0u64 };
    }

    /// [Origin Rust: Hasher::finish -> finish_with_state] (sip.rs:284-332, 446 block)
    pub exec fn finish(&self) -> (r: u64)
        ensures r == spec_finish_13(hash13_view(self))
    {
        let b = ((self.length & 0xffu64) << 56) | self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3 ^ b));
        let s2 = (s1.0 ^ b, s1.1, s1.2 ^ 0xffu64, s1.3);
        let d1 = compress_exec(s2);
        let d2 = compress_exec(d1);
        let d3 = compress_exec(d2);
        d3.0 ^ d3.1 ^ d3.2 ^ d3.3
    }
}

/* ============================================================
 * exec -- Hasher24 (isomorphic to Hasher13, rounds c x2/d x4)
 * ============================================================ */

impl Hasher24 {

    pub exec fn new_with_keys(key0: u64, key1: u64) -> (r: Hasher24)
        ensures hash24_view(&r) == spec_new_24(key0, key1)
    {
        Hasher24 {
            k0: key0,
            k1: key1,
            v0: key0 ^ 0x736f6d6570736575u64,
            v1: key1 ^ 0x646f72616e646f6du64,
            v2: key0 ^ 0x6c7967656e657261u64,
            v3: key1 ^ 0x7465646279746573u64,
            length: 0,
            tail: 0,
            ntail: 0,
        }
    }

    pub exec fn write_u8(&mut self, i: u8)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures hash24_view(final(self)) == spec_write_u8_24(hash24_view(old(self)), i)
    {
        let size: u64 = 1;
        let x: u64 = i as u64;
        self.length += size;

        let needed = 8u64 - self.ntail;
        self.tail = self.tail | (x << (8 * self.ntail));
        if size < needed {
            self.ntail += size;
            return;
        }
        self.v3 ^= self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
        let s1b = compress_exec(s1);
        self.v0 = s1b.0 ^ self.tail;
        self.v1 = s1b.1;
        self.v2 = s1b.2;
        self.v3 = s1b.3;
        self.ntail = size - needed;
        self.tail = if needed < 8 { x >> (8 * needed) } else { 0u64 };
    }

    pub exec fn write_u16(&mut self, i: u16)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures hash24_view(final(self)) == spec_write_u16_24(hash24_view(old(self)), i)
    {
        let size: u64 = 2;
        let x: u64 = i as u64;
        self.length += size;

        let needed = 8u64 - self.ntail;
        self.tail = self.tail | (x << (8 * self.ntail));
        if size < needed {
            self.ntail += size;
            return;
        }
        self.v3 ^= self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
        let s1b = compress_exec(s1);
        self.v0 = s1b.0 ^ self.tail;
        self.v1 = s1b.1;
        self.v2 = s1b.2;
        self.v3 = s1b.3;
        self.ntail = size - needed;
        self.tail = if needed < 8 { x >> (8 * needed) } else { 0u64 };
    }

    pub exec fn write_u32(&mut self, i: u32)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures hash24_view(final(self)) == spec_write_u32_24(hash24_view(old(self)), i)
    {
        let size: u64 = 4;
        let x: u64 = i as u64;
        self.length += size;

        let needed = 8u64 - self.ntail;
        self.tail = self.tail | (x << (8 * self.ntail));
        if size < needed {
            self.ntail += size;
            return;
        }
        self.v3 ^= self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
        let s1b = compress_exec(s1);
        self.v0 = s1b.0 ^ self.tail;
        self.v1 = s1b.1;
        self.v2 = s1b.2;
        self.v3 = s1b.3;
        self.ntail = size - needed;
        self.tail = if needed < 8 { x >> (8 * needed) } else { 0u64 };
    }

    pub exec fn write_u64(&mut self, i: u64)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures hash24_view(final(self)) == spec_write_u64_24(hash24_view(old(self)), i)
    {
        let size: u64 = 8;
        let x: u64 = i;
        self.length += size;

        let needed = 8u64 - self.ntail;
        self.tail = self.tail | (x << (8 * self.ntail));
        if size < needed {
            self.ntail += size;
            return;
        }
        self.v3 ^= self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
        let s1b = compress_exec(s1);
        self.v0 = s1b.0 ^ self.tail;
        self.v1 = s1b.1;
        self.v2 = s1b.2;
        self.v3 = s1b.3;
        self.ntail = size - needed;
        self.tail = if needed < 8 { x >> (8 * needed) } else { 0u64 };
    }

    pub exec fn finish(&self) -> (r: u64)
        ensures r == spec_finish_24(hash24_view(self))
    {
        let b = ((self.length & 0xffu64) << 56) | self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3 ^ b));
        let s1b = compress_exec(s1);
        let s2 = (s1b.0 ^ b, s1b.1, s1b.2 ^ 0xffu64, s1b.3);
        let d1 = compress_exec(s2);
        let d2 = compress_exec(d1);
        let d3 = compress_exec(d2);
        let d4 = compress_exec(d3);
        d4.0 ^ d4.1 ^ d4.2 ^ d4.3
    }
}

/* ============================================================
 * exec -- the slice paths (write / hash): L0 contract
 * (the value-level spec is blocked by the encoding limitation; the
 * semantics are covered by the harness scalar paths + the runtime
 * re-verification)
 * ============================================================ */

impl Hasher13 {

    /// [Origin Rust: hash::Hasher::write for Hasher<S> (sip.rs:464-510)]
    /// The block loop is the equivalent rewritten form.
    pub exec fn write(&mut self, msg: &[u8])
        requires
            self.ntail < 8,
            self.length + (msg.len() as u64) <= 0xffff_ffff_ffff_fff0u64,
        ensures
            final(self).ntail < 8,
    {
        let length = msg.len() as u64;      // upstream length local (this message's length)
        self.length += length;

        let mut needed = 0u64;

        if self.ntail != 0 {
            needed = 8u64 - self.ntail;
            let take = if length < needed { length } else { needed };
            let chunk = u8to64_le_exec(msg, 0, take as usize);
            self.tail = self.tail | (chunk << (8 * self.ntail));
            if length < needed {
                self.ntail += length;
                return;
            } else {
                self.v3 ^= self.tail;
                let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
                self.v0 = s1.0 ^ self.tail;
                self.v1 = s1.1;
                self.v2 = s1.2;
                self.v3 = s1.3;
                self.ntail = 0u64;
            }
        }

        let len = length - needed;           // upstream len
        let left = len & 0x7;               // upstream left

        let mut i = needed;
        while i + 8 <= length
            invariant
                needed <= i,
                i <= length,
                i % 8 == needed % 8,
                length == msg.len() as u64,
                length <= 0xffff_ffff_ffff_fff0u64,
            decreases length - i
        {
            let mi = load_u64_le(msg, i as usize);

            self.v3 ^= mi;
            let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
            self.v0 = s1.0 ^ mi;
            self.v1 = s1.1;
            self.v2 = s1.2;
            self.v3 = s1.3;

            i += 8;
        }

        let take2 = length - i;             // mathematically == left
        proof {
            assert(take2 < 8);                // first derived from the exit guard i + 8 > length
        }
        self.tail = u8to64_le_exec(msg, i as usize, take2 as usize);
        self.ntail = take2;
    }
}

impl Hasher24 {

    /// [Origin Rust: hash::Hasher::write for Hasher<S> (sip.rs:473-510), 2-4 rounds]
    /// The block loop is the equivalent rewritten form.
    pub exec fn write(&mut self, msg: &[u8])
        requires
            self.ntail < 8,
            self.length + (msg.len() as u64) <= 0xffff_ffff_ffff_fff0u64,
        ensures
            final(self).ntail < 8,
    {
        let length = msg.len() as u64;
        self.length += length;

        let mut needed = 0u64;

        if self.ntail != 0 {
            needed = 8u64 - self.ntail;
            let take = if length < needed { length } else { needed };
            let chunk = u8to64_le_exec(msg, 0, take as usize);
            self.tail = self.tail | (chunk << (8 * self.ntail));
            if length < needed {
                self.ntail += length;
                return;
            } else {
                self.v3 ^= self.tail;
                let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
                let s1b = compress_exec(s1);
                self.v0 = s1b.0 ^ self.tail;
                self.v1 = s1b.1;
                self.v2 = s1b.2;
                self.v3 = s1b.3;
                self.ntail = 0u64;
            }
        }

        let len = length - needed;
        let left = len & 0x7;

        let mut i = needed;
        while i + 8 <= length
            invariant
                needed <= i,
                i <= length,
                i % 8 == needed % 8,
                length == msg.len() as u64,
                length <= 0xffff_ffff_ffff_fff0u64,
            decreases length - i
        {
            let mi = load_u64_le(msg, i as usize);

            self.v3 ^= mi;
            let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3));
            let s1b = compress_exec(s1);
            self.v0 = s1b.0 ^ mi;
            self.v1 = s1b.1;
            self.v2 = s1b.2;
            self.v3 = s1b.3;

            i += 8;
        }

        let take2 = length - i;             // mathematically == left
        proof {
            assert(take2 < 8);
        }
        self.tail = u8to64_le_exec(msg, i as usize, take2 as usize);
        self.ntail = take2;
    }
}

/* ============================================================
 * Public wrappers (upstream pub struct SipHasher13/SipHasher24/SipHasher)
 * [Origin Rust: sip.rs:24-53 + 124-214]
 * ============================================================ */

pub struct SipHasher13 {
    pub hasher: Hasher13, // upstream hasher: Hasher<Sip13Rounds>
}

pub struct SipHasher24 {
    pub hasher: Hasher24,
}

pub struct SipHasher {
    pub h: SipHasher24, // upstream SipHasher(SipHasher24)
}

impl SipHasher13 {
    /// Upstream doc (sip.rs:125-125):
    ///   Creates a new `SipHasher13` with the two initial keys set to 0.
    pub exec fn new() -> (r: SipHasher13)
        ensures hash13_view(&r.hasher) == spec_new_13(0, 0)
    {
        SipHasher13 { hasher: Hasher13::new_with_keys(0, 0) }
    }

    /// Upstream doc (sip.rs:131-131):
    ///   Creates a `SipHasher13` that is keyed off the provided keys.
    pub exec fn new_with_keys(k0: u64, k1: u64) -> (r: SipHasher13)
        ensures hash13_view(&r.hasher) == spec_new_13(k0, k1)
    {
        SipHasher13 { hasher: Hasher13::new_with_keys(k0, k1) }
    }

    /// Upstream doc (sip.rs:150-150):
    ///   Get the keys used by this hasher
    pub exec fn keys(&self) -> (r: (u64, u64))
        ensures r == (self.hasher.k0, self.hasher.k1)
    {
        (self.hasher.k0, self.hasher.k1)
    }

    /// [Origin Rust: hash(bytes) (sip.rs:165-167)] -- L0 + delegates to write/finish
    /// Upstream doc (sip.rs:163-163):
    ///   Hash a byte array - This is the easiest and safest way to use SipHash.
    pub exec fn hash(&self, bytes: &[u8]) -> (r: u64)
        requires
            self.hasher.ntail < 8,
            self.hasher.length + (bytes.len() as u64)
                <= 0xffff_ffff_ffff_fff0u64,
        ensures self.hasher.ntail < 8
    {
        let mut hc = Hasher13::new_with_keys(self.hasher.k0, self.hasher.k1);
        hc.v0 = self.hasher.v0; hc.v1 = self.hasher.v1;
        hc.v2 = self.hasher.v2; hc.v3 = self.hasher.v3;
        hc.length = self.hasher.length; hc.tail = self.hasher.tail;
        hc.ntail = self.hasher.ntail;
        hc.write(bytes);
        hc.finish()
    }

    /// [Origin Rust: new_with_key(&[u8; 16])] (sip.rs:140-148)
    /// -- shape adaptation: &[u8;16] -> &[u8] (requires len == 16); the
    /// key assembling goes through the index path
    /// Upstream doc (sip.rs:139-139):
    ///   Creates a `SipHasher13` from a 16 byte key.
    pub exec fn new_with_key(key: &[u8]) -> (r: SipHasher13)
        requires key.len() == 16
        ensures
            hash13_view(&r.hasher).0 == crate::common::spec_load_u64(key@, 0),
            hash13_view(&r.hasher).1 == crate::common::spec_load_u64(key@, 8),
            hash13_view(&r.hasher).2
                == (crate::common::spec_load_u64(key@, 0)
                    ^ 0x736f6d6570736575u64),
    {
        let k0 = load_u64_le(key, 0);
        let k1 = load_u64_le(key, 8);
        SipHasher13 { hasher: Hasher13::new_with_keys(k0, k1) }
    }
}

impl SipHasher13 {
    pub open spec fn view(&self) -> H9 {
        hash13_view(&self.hasher)
    }
}

impl SipHasher24 {
    /// Upstream doc (sip.rs:171-171):
    ///   Creates a new `SipHasher24` with the two initial keys set to 0.
    pub exec fn new() -> (r: SipHasher24)
        ensures hash24_view(&r.hasher) == spec_new_24(0, 0)
    {
        SipHasher24 { hasher: Hasher24::new_with_keys(0, 0) }
    }

    /// Upstream doc (sip.rs:177-177):
    ///   Creates a `SipHasher24` that is keyed off the provided keys.
    pub exec fn new_with_keys(k0: u64, k1: u64) -> (r: SipHasher24)
        ensures hash24_view(&r.hasher) == spec_new_24(k0, k1)
    {
        SipHasher24 { hasher: Hasher24::new_with_keys(k0, k1) }
    }

    /// Upstream doc (sip.rs:196-196):
    ///   Get the keys used by this hasher
    pub exec fn keys(&self) -> (r: (u64, u64))
        ensures r == (self.hasher.k0, self.hasher.k1)
    {
        (self.hasher.k0, self.hasher.k1)
    }

    /// Upstream doc (sip.rs:209-209):
    ///   Hash a byte array - This is the easiest and safest way to use SipHash.
    pub exec fn hash(&self, bytes: &[u8]) -> (r: u64)
        requires
            self.hasher.ntail < 8,
            self.hasher.length + (bytes.len() as u64)
                <= 0xffff_ffff_ffff_fff0u64,
        ensures self.hasher.ntail < 8
    {
        let mut hc = Hasher24::new_with_keys(self.hasher.k0, self.hasher.k1);
        hc.v0 = self.hasher.v0; hc.v1 = self.hasher.v1;
        hc.v2 = self.hasher.v2; hc.v3 = self.hasher.v3;
        hc.length = self.hasher.length; hc.tail = self.hasher.tail;
        hc.ntail = self.hasher.ntail;
        hc.write(bytes);
        hc.finish()
    }

    /// Upstream doc (sip.rs:185-185):
    ///   Creates a `SipHasher24` from a 16 byte key.
    pub exec fn new_with_key(key: &[u8]) -> (r: SipHasher24)
        requires key.len() == 16
        ensures
            hash24_view(&r.hasher).0 == crate::common::spec_load_u64(key@, 0),
            hash24_view(&r.hasher).1 == crate::common::spec_load_u64(key@, 8),
    {
        let k0 = load_u64_le(key, 0);
        let k1 = load_u64_le(key, 8);
        SipHasher24 { hasher: Hasher24::new_with_keys(k0, k1) }
    }
}

impl SipHasher {
    /// Upstream doc (sip.rs:81-81):
    ///   Creates a new `SipHasher` with the two initial keys set to 0.
    pub exec fn new() -> (r: SipHasher)
        ensures hash24_view(&r.h.hasher) == spec_new_24(0, 0)
    {
        SipHasher { h: SipHasher24 { hasher: Hasher24::new_with_keys(0, 0) } }
    }

    /// Upstream doc (sip.rs:87-87):
    ///   Creates a `SipHasher` that is keyed off the provided keys.
    pub exec fn new_with_keys(key0: u64, key1: u64) -> (r: SipHasher)
        ensures hash24_view(&r.h.hasher) == spec_new_24(key0, key1)
    {
        SipHasher { h: SipHasher24 { hasher: Hasher24::new_with_keys(key0, key1) } }
    }

    /// Upstream doc (sip.rs:104-104):
    ///   Get the keys used by this hasher
    pub exec fn keys(&self) -> (r: (u64, u64))
        ensures r == (self.h.hasher.k0, self.h.hasher.k1)
    {
        (self.h.hasher.k0, self.h.hasher.k1)
    }

    /// Upstream doc (sip.rs:117-117):
    ///   Hash a byte array - This is the easiest and safest way to use SipHash.
    pub exec fn hash(&self, bytes: &[u8]) -> (r: u64)
        requires
            self.h.hasher.ntail < 8,
            self.h.hasher.length + (bytes.len() as u64)
                <= 0xffff_ffff_ffff_fff0u64,
    {
        let mut hc = Hasher24::new_with_keys(self.h.hasher.k0, self.h.hasher.k1);
        hc.v0 = self.h.hasher.v0; hc.v1 = self.h.hasher.v1;
        hc.v2 = self.h.hasher.v2; hc.v3 = self.h.hasher.v3;
        hc.length = self.h.hasher.length; hc.tail = self.h.hasher.tail;
        hc.ntail = self.h.hasher.ntail;
        hc.write(bytes);
        hc.finish()
    }

    /// Upstream doc (sip.rs:93-93):
    ///   Creates a `SipHasher` from a 16 byte key.
    pub exec fn new_with_key(key: &[u8]) -> (r: SipHasher)
        requires key.len() == 16
        ensures
            hash24_view(&r.h.hasher).0 == crate::common::spec_load_u64(key@, 0),
            hash24_view(&r.h.hasher).1 == crate::common::spec_load_u64(key@, 8),
    {
        let k0 = load_u64_le(key, 0);
        let k1 = load_u64_le(key, 8);
        SipHasher { h: SipHasher24 { hasher: Hasher24::new_with_keys(k0, k1) } }
    }
}

#[verifier::inline]
pub open spec fn hash_u64_24(k0: u64, k1: u64, v: u64) -> u64 {
    spec_finish_24(spec_write_u64_24(spec_new_24(k0, k1), v))
}

#[verifier::inline]
pub open spec fn hash_u32_24(k0: u64, k1: u64, v: u32) -> u64 {
    spec_finish_24(spec_write_u32_24(spec_new_24(k0, k1), v))
}

} // verus!

fn main() {}
