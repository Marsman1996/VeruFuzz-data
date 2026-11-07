//! verified/src/sip128.rs -- translated mirror of code/src/sip128.rs
//! (pin 2fcf2a7), the 128-bit SipHash
//!
//! Translation adaptations (the same note rules as sip.rs; the semantics
//! are cross-checked API by API by the runtime re-verification):
//! - [Origin Rust: sip128.rs:84-92 `Hasher<S: Sip>`] -> the two entities
//!   Hasher128_13 / Hasher128_24
//!   (PhantomData generic-dispatch translation); State{v0,v2,v1,v3} ->
//!   the flat v0,v1,v2,v3.
//! - [Origin Rust: sip128.rs:294-301 reset] The v1 initial value 0xee
//!   given at construction is overwritten by reset; the 128-bit v1
//!   constant 0x646f72616e646f83 (differing from the 64-bit 0x...6d) is
//!   kept faithfully.
//! - [Origin Rust: finish128_with_state (sip128.rs:369-385)]
//!   The two-stage reduce: v2^=0xee -> d -> h1; v1^=0xdd -> d -> h2.
//! - [Origin Rust: `impl Hasher128 for ...` trait] -> the inherent
//!   `finish128` method.
//! - [Origin Rust: `Hash128::eq`: a volatile constant-time comparison]
//!   The volatile read is outside Verus's support range; translated
//!   into a pure value comparison (same value semantics, the witness
//!   proven on the harness side); constancy (the timing side-channel
//!   property) is explicitly scoped out of the verification,
//!   and its value equivalence is checked by the runtime re-verification.
//! - [Origin Rust: `impl<S: Sip> Hasher<S>::finish` -> finish128().h2]
//!   The 64-bit finish returns h2 (faithful mirror).
//! - The LE host assumption and the usize->u64 width assumption are the
//!   same as the sip.rs header.
//! - write(&[u8]): L0 contract + the equivalent rewritten block loop.

use vstd::prelude::*;

use crate::common::{compress_exec, compress_spec, load_u64_le, u8to64_le_exec};

verus! {

pub type H9 = (u64, u64, u64, u64, u64, u64, u64, u64, u64);
pub type T4 = (u64, u64, u64, u64);

/* ============================================================
 * Hash128 and its conversions (upstream pub struct Hash128 / From / as_*)
 * ============================================================ */

/// [Origin Rust: sip128.rs:24-27]
pub struct Hash128 {
    pub h1: u64,
    pub h2: u64,
}

/// [Origin Rust: as_bytes / as_u128 / as_u64 (sip128.rs:643-667)]
/// LE host assumption: to_le()/to_le_bytes() is the identity / the native
/// byte order.
impl Hash128 {
    /// Upstream doc (sip128.rs:660-660):
    ///   Convert into `(u64, u64)`
    pub exec fn as_u64(&self) -> (r: (u64, u64))
        ensures r == (self.h1, self.h2)
    {
        (self.h1, self.h2)
    }

    /// Upstream doc (sip128.rs:652-652):
    ///   Convert into a `u128`
    pub exec fn as_u128(&self) -> (r: u128)
        ensures
            r == (self.h1 as u128) | ((self.h2 as u128) << 64),
            r == u128_from_pair(self.h1, self.h2)
    {
        let h1 = self.h1 as u128;
        let h2 = self.h2 as u128;
        h1 | (h2 << 64)
    }

    /// [Origin Rust: as_bytes -- to_le_bytes byte by byte (LE assumption)]
    /// Shape adaptation: a per-position 16-byte extraction fn (array
    /// return values are outside the supported surface).
    /// Upstream doc (sip128.rs:643-643):
    ///   Convert into a 16-bytes vector
    pub exec fn byte(&self, j: usize) -> (r: u8)
        requires j < 16
        ensures
            j < 8 ==> r == ((self.h1 >> (8 * (j as u64))) & 0xffu64) as u8,
            j >= 8 ==> r == ((self.h2 >> (8 * ((j - 8) as u64))) & 0xffu64) as u8,
    {
        if j < 8 {
            ((self.h1 >> (8 * (j as u64))) & 0xffu64) as u8
        } else {
            ((self.h2 >> (8 * ((j - 8) as u64))) & 0xffu64) as u8
        }
    }
}

#[verifier::inline]
pub open spec fn u128_from_pair(h1: u64, h2: u64) -> u128 {
    (h1 as u128) | ((h2 as u128) << 64)
}

/// [Origin Rust: impl From<u128> for Hash128 (sip128.rs:39-46)]
pub exec fn hash128_from_u128(v: u128) -> (r: Hash128)
    ensures
        r.h1 == v as u64,
        r.h2 == (v >> 64) as u64,
{
    Hash128 { h1: v as u64, h2: (v >> 64) as u64 }
}

/// [Origin Rust: impl From<Hash128> for u128 (sip128.rs:48-52)]
#[verifier::inline]
pub open spec fn u128_from_hash128(h: Hash128) -> u128 {
    u128_from_pair(h.h1, h.h2)
}

/// [Origin Rust: Hash128::eq -- constant-time comparison (the value-
/// semantics witness is this spec)]
#[verifier::inline]
pub open spec fn hash128_eq_spec(a: Hash128, b: Hash128) -> bool {
    a.h1 == b.h1 && a.h2 == b.h2
}

/// Upstream doc (sip128.rs:30-30):
///   Constant-time equality comparison to prevent timing attacks.
pub exec fn hash128_eq(a: Hash128, b: Hash128) -> (r: bool)
    ensures r == hash128_eq_spec(a, b)
{
    a.h1 == b.h1 && a.h2 == b.h2
}

/* ============================================================
 * State views and spec twins
 * ============================================================ */

pub struct Hasher128_13 {
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

pub struct Hasher128_24 {
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

pub open spec fn h128v13(h: &Hasher128_13) -> H9 {
    (h.k0, h.k1, h.v0, h.v1, h.v2, h.v3, h.length, h.tail, h.ntail)
}

pub open spec fn h128v24(h: &Hasher128_24) -> H9 {
    (h.k0, h.k1, h.v0, h.v1, h.v2, h.v3, h.length, h.tail, h.ntail)
}

/// 128-bit reset (the v1 constant 0x...83 differs from the 64-bit 0x...6d)
#[verifier::inline]
pub open spec fn spec_new_128_13(k0: u64, k1: u64) -> H9 {
    (k0, k1,
     k0 ^ 0x736f6d6570736575u64, k1 ^ 0x646f72616e646f83u64,
     k0 ^ 0x6c7967656e657261u64, k1 ^ 0x7465646279746573u64,
     0, 0, 0)
}

#[verifier::inline]
pub open spec fn spec_new_128_24(k0: u64, k1: u64) -> H9 {
    (k0, k1,
     k0 ^ 0x736f6d6570736575u64, k1 ^ 0x646f72616e646f83u64,
     k0 ^ 0x6c7967656e657261u64, k1 ^ 0x7465646279746573u64,
     0, 0, 0)
}

#[verifier::inline]
pub open spec fn spec_short_write_128_13(v: H9, x: u64, size: u64) -> H9 {
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
pub open spec fn spec_short_write_128_24(v: H9, x: u64, size: u64) -> H9 {
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
pub open spec fn spec_write_u8_128_13(h: H9, b: u8) -> H9 {
    spec_short_write_128_13(h, b as u64, 1)
}

#[verifier::inline]
pub open spec fn spec_write_u32_128_13(h: H9, b: u32) -> H9 {
    spec_short_write_128_13(h, b as u64, 4)
}

#[verifier::inline]
pub open spec fn spec_write_u64_128_13(h: H9, b: u64) -> H9 {
    spec_short_write_128_13(h, b, 8)
}

#[verifier::inline]
pub open spec fn spec_write_u8_128_24(h: H9, b: u8) -> H9 {
    spec_short_write_128_24(h, b as u64, 1)
}

#[verifier::inline]
pub open spec fn spec_write_u32_128_24(h: H9, b: u32) -> H9 {
    spec_short_write_128_24(h, b as u64, 4)
}

#[verifier::inline]
pub open spec fn spec_write_u64_128_24(h: H9, b: u64) -> H9 {
    spec_short_write_128_24(h, b, 8)
}

/// Semantics of finish128_with_state (upstream sip128.rs:369-385),
/// SipHash128-1-3:
/// v3^=b; c(x1); v0^=b; v2^=0xee; d(x3); h1 = reduce;
/// v1^=0xdd; d(x3); h2 = reduce.
#[verifier::inline]
pub open spec fn spec_finish128_13(h: H9) -> (u64, u64) {
    let (k0, k1, v0, v1, v2, v3, length, tail, ntail) = h;
    let b = ((length & 0xffu64) << 56) | tail;
    let s1 = compress_spec((v0, v1, v2, v3 ^ b));
    let s2 = (s1.0 ^ b, s1.1, s1.2 ^ 0xeeu64, s1.3);
    let d1 = compress_spec(s2);
    let d2 = compress_spec(d1);
    let d3 = compress_spec(d2);
    let h1 = d3.0 ^ d3.1 ^ d3.2 ^ d3.3;
    let e0 = (d3.0, d3.1 ^ 0xddu64, d3.2, d3.3);
    let f1 = compress_spec(e0);
    let f2 = compress_spec(f1);
    let f3 = compress_spec(f2);
    let h2 = f3.0 ^ f3.1 ^ f3.2 ^ f3.3;
    (h1, h2)
}

/// Same as above, SipHash128-2-4 (two stages of c x2, d x4).
#[verifier::inline]
pub open spec fn spec_finish128_24(h: H9) -> (u64, u64) {
    let (k0, k1, v0, v1, v2, v3, length, tail, ntail) = h;
    let b = ((length & 0xffu64) << 56) | tail;
    let s1 = compress_spec((v0, v1, v2, v3 ^ b));
    let s1b = compress_spec(s1);
    let s2 = (s1b.0 ^ b, s1b.1, s1b.2 ^ 0xeeu64, s1b.3);
    let d1 = compress_spec(s2);
    let d2 = compress_spec(d1);
    let d3 = compress_spec(d2);
    let d4 = compress_spec(d3);
    let h1 = d4.0 ^ d4.1 ^ d4.2 ^ d4.3;
    let e0 = (d4.0, d4.1 ^ 0xddu64, d4.2, d4.3);
    let f1 = compress_spec(e0);
    let f2 = compress_spec(f1);
    let f3 = compress_spec(f2);
    let f4 = compress_spec(f3);
    let h2 = f4.0 ^ f4.1 ^ f4.2 ^ f4.3;
    (h1, h2)
}

/* ============================================================
 * exec -- Hasher128_13
 * ============================================================ */

impl Hasher128_13 {

    pub exec fn new_with_keys(key0: u64, key1: u64) -> (r: Hasher128_13)
        ensures h128v13(&r) == spec_new_128_13(key0, key1)
    {
        Hasher128_13 {
            k0: key0,
            k1: key1,
            v0: key0 ^ 0x736f6d6570736575u64,
            v1: key1 ^ 0x646f72616e646f83u64,
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
        ensures h128v13(final(self)) == spec_write_u8_128_13(h128v13(old(self)), i)
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

    pub exec fn write_u32(&mut self, i: u32)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures h128v13(final(self)) == spec_write_u32_128_13(h128v13(old(self)), i)
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

    pub exec fn write_u64(&mut self, i: u64)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures h128v13(final(self)) == spec_write_u64_128_13(h128v13(old(self)), i)
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


    /// [Origin Rust: hash::Hasher::write for Hasher<S> (sip128.rs:506-570)]
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
                self.v0 = s1.0 ^ self.tail;
                self.v1 = s1.1;
                self.v2 = s1.2;
                self.v3 = s1.3;
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
            self.v0 = s1.0 ^ mi;
            self.v1 = s1.1;
            self.v2 = s1.2;
            self.v3 = s1.3;

            i += 8;
        }

        let take2 = length - i;
        proof {
            assert(take2 < 8);
        }
        self.tail = u8to64_le_exec(msg, i as usize, take2 as usize);
        self.ntail = take2;
    }

    /// [Origin Rust: finish128 / finish128_with_state (sip128.rs:369-393)]
    pub exec fn finish128(&self) -> (r: Hash128)
        ensures
            r.h1 == spec_finish128_13(h128v13(self)).0,
            r.h2 == spec_finish128_13(h128v13(self)).1,
    {
        let b = ((self.length & 0xffu64) << 56) | self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3 ^ b));
        let s2 = (s1.0 ^ b, s1.1, s1.2 ^ 0xeeu64, s1.3);
        let d1 = compress_exec(s2);
        let d2 = compress_exec(d1);
        let d3 = compress_exec(d2);
        let h1 = d3.0 ^ d3.1 ^ d3.2 ^ d3.3;
        let e0 = (d3.0, d3.1 ^ 0xddu64, d3.2, d3.3);
        let f1 = compress_exec(e0);
        let f2 = compress_exec(f1);
        let f3 = compress_exec(f2);
        let h2 = f3.0 ^ f3.1 ^ f3.2 ^ f3.3;
        Hash128 { h1, h2 }
    }

    /// [Origin Rust: impl Hasher::finish -- finish128().h2 (sip128.rs:573-575)]
    pub exec fn finish(&self) -> (r: u64)
        ensures r == spec_finish128_13(h128v13(self)).1
    {
        self.finish128().h2
    }
}

/* ============================================================
 * exec -- Hasher128_24
 * ============================================================ */

impl Hasher128_24 {

    pub exec fn new_with_keys(key0: u64, key1: u64) -> (r: Hasher128_24)
        ensures h128v24(&r) == spec_new_128_24(key0, key1)
    {
        Hasher128_24 {
            k0: key0,
            k1: key1,
            v0: key0 ^ 0x736f6d6570736575u64,
            v1: key1 ^ 0x646f72616e646f83u64,
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
        ensures h128v24(final(self)) == spec_write_u8_128_24(h128v24(old(self)), i)
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

    pub exec fn write_u32(&mut self, i: u32)
        requires
            self.ntail < 8,
            self.length <= 0xffff_ffff_ffff_fff0u64,
        ensures h128v24(final(self)) == spec_write_u32_128_24(h128v24(old(self)), i)
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
        ensures h128v24(final(self)) == spec_write_u64_128_24(h128v24(old(self)), i)
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


    /// [Origin Rust: hash::Hasher::write for Hasher<S> (sip128.rs:506-570), 2-4 rounds]
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

        let take2 = length - i;
        proof {
            assert(take2 < 8);
        }
        self.tail = u8to64_le_exec(msg, i as usize, take2 as usize);
        self.ntail = take2;
    }

        pub exec fn finish128(&self) -> (r: Hash128)
        ensures
            r.h1 == spec_finish128_24(h128v24(self)).0,
            r.h2 == spec_finish128_24(h128v24(self)).1,
    {
        let b = ((self.length & 0xffu64) << 56) | self.tail;
        let s1 = compress_exec((self.v0, self.v1, self.v2, self.v3 ^ b));
        let s1b = compress_exec(s1);
        let s2 = (s1b.0 ^ b, s1b.1, s1b.2 ^ 0xeeu64, s1b.3);
        let d1 = compress_exec(s2);
        let d2 = compress_exec(d1);
        let d3 = compress_exec(d2);
        let d4 = compress_exec(d3);
        let h1 = d4.0 ^ d4.1 ^ d4.2 ^ d4.3;
        let e0 = (d4.0, d4.1 ^ 0xddu64, d4.2, d4.3);
        let f1 = compress_exec(e0);
        let f2 = compress_exec(f1);
        let f3 = compress_exec(f2);
        let f4 = compress_exec(f3);
        let h2 = f4.0 ^ f4.1 ^ f4.2 ^ f4.3;
        Hash128 { h1, h2 }
    }

    pub exec fn finish(&self) -> (r: u64)
        ensures r == spec_finish128_24(h128v24(self)).1
    {
        self.finish128().h2
    }
}

/* ============================================================
 * Public wrappers (upstream sip128::SipHasher13/SipHasher24/SipHasher)
 * ============================================================ */

pub struct SipHasher128_13 {
    pub hasher: Hasher128_13,
}

pub struct SipHasher128_24 {
    pub hasher: Hasher128_24,
}

/// Upstream sip128::SipHasher(SipHasher128_24)
pub struct SipHasher128 {
    pub h: SipHasher128_24,
}

impl SipHasher128_13 {
    /// Upstream doc (sip128.rs:171-171):
    ///   Creates a `SipHasher13` that is keyed off the provided keys.
    pub exec fn new_with_keys(k0: u64, k1: u64) -> (r: SipHasher128_13)
        ensures h128v13(&r.hasher) == spec_new_128_13(k0, k1)
    {
        SipHasher128_13 { hasher: Hasher128_13::new_with_keys(k0, k1) }
    }

    /// Upstream doc (sip128.rs:190-190):
    ///   Get the keys used by this hasher
    pub exec fn keys(&self) -> (r: (u64, u64))
        ensures r == (self.hasher.k0, self.hasher.k1)
    {
        (self.hasher.k0, self.hasher.k1)
    }
}

impl SipHasher128_24 {
    /// Upstream doc (sip128.rs:225-225):
    ///   Creates a `SipHasher24` that is keyed off the provided keys.
    pub exec fn new_with_keys(k0: u64, k1: u64) -> (r: SipHasher128_24)
        ensures h128v24(&r.hasher) == spec_new_128_24(k0, k1)
    {
        SipHasher128_24 { hasher: Hasher128_24::new_with_keys(k0, k1) }
    }

    /// Upstream doc (sip128.rs:244-244):
    ///   Get the keys used by this hasher
    pub exec fn keys(&self) -> (r: (u64, u64))
        ensures r == (self.hasher.k0, self.hasher.k1)
    {
        (self.hasher.k0, self.hasher.k1)
    }
}

impl SipHasher128 {
    /// Upstream doc (sip128.rs:113-113):
    ///   Creates a new `SipHasher` with the two initial keys set to 0.
    pub exec fn new() -> (r: SipHasher128)
        ensures h128v24(&r.h.hasher) == spec_new_128_24(0, 0)
    {
        SipHasher128 {
            h: SipHasher128_24 { hasher: Hasher128_24::new_with_keys(0, 0) },
        }
    }

    /// Upstream doc (sip128.rs:119-119):
    ///   Creates a `SipHasher` that is keyed off the provided keys.
    pub exec fn new_with_keys(k0: u64, k1: u64) -> (r: SipHasher128)
        ensures h128v24(&r.h.hasher) == spec_new_128_24(k0, k1)
    {
        SipHasher128 {
            h: SipHasher128_24 { hasher: Hasher128_24::new_with_keys(k0, k1) },
        }
    }

    /// Upstream doc (sip128.rs:136-136):
    ///   Get the keys used by this hasher
    pub exec fn keys(&self) -> (r: (u64, u64))
        ensures r == (self.h.hasher.k0, self.h.hasher.k1)
    {
        (self.h.hasher.k0, self.h.hasher.k1)
    }
}

} // verus!

fn main() {}
