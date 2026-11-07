//! verified/src/fixed.rs -- the per-function mirror of the upstream
//! code/src/fixed.rs (a KVerus migrate artifact)
//!
//! Upstream: https://github.com/dermesser/integer-encoding-rs pin e0a10d0, SUBDIR empty.
//! The upstream tree is untouched; this file is the verified/ side copy.
//!
//! Mirror and relaxation ledger:
//! 1. `pub trait FixedInt` + the `impl_fixedint!` macro (upstream :9-79): the macro
//!    impls are all monomorphized into per-type exec fns (`encode_fixed_u32` etc.),
//!    semantics identical to the macro expansion; the trait default method
//!    encode_fixed_vec is monomorphized likewise. The `FixedInt::ENCODED_SIZE` trait
//!    constant is monomorphized into the `ENCODED_SIZE_<T>` constants.
//! 2. `self.to_le_bytes()` / `Self::from_le_bytes()` -- vstd has no std byte-order spec,
//!    so the mirror expands them byte by byte into shift-and-extract expressions following
//!    Rust semantics (the byte order with the low-order byte at the low address is
//!    precisely the LE semantics of FixedInt; this expansion is the official "le"
//!    definition, not a behavioral rewrite).
//! 3. `switch_endianness` = `Self::from_le_bytes(self.to_be_bytes())` is expanded into
//!    the byte-reversal formula (indicated inline by the Origin comments).
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

// ============================================================
// spec: LE byte value. le_byte(v, k) = the k-th LE byte of v (low-order group byte order)
// ============================================================

pub open spec fn le_byte(v: int, k: nat) -> u8 {
    ((v / pow2int(k)) % 256) as u8
}

/// mini pow2 helper (spec side)
pub open spec fn pow2int(k: nat) -> int {
    spec_pow2(k)
}

pub open spec fn spec_pow2(k: nat) -> int
    decreases k
{
    if k == 0 { 1 } else { 2 * spec_pow2((k - 1) as nat) }
}

/// Swap byte order (byte count completed to 2^W = size), spec view on the 8W bits domain
pub open spec fn switch_endian_spec(v: int, size: nat) -> int {
    if size <= 1 {
        v
    } else {
        // after reversing the bytes the value = an accumulation, each byte's high/low
        // halves swapped symmetrically; the slice reversal is recursive
        rev_bytes_sum(v, 0, size)
    }
}

pub open spec fn rev_bytes_sum(v: int, k: int, size: nat) -> int
    decreases size - k
{
    if k >= size as int {
        0
    } else {
        let lo: u8 = ((v / pow2int(k as nat)) % 256) as u8;
        let x: int = lo as int;
        x * pow2int((size - 1 - k) as nat) + rev_bytes_sum(v, k + 1, size)
    }
}

// ============================================================
// spec: the value definition of byte swapping & the LE byte assertion helpers
// ============================================================

/// 16-bit byte swap, int view
pub open spec fn bswap16(v: int) -> int {
    256 * ((v / 256) % 256) + (v % 256)
}

/// 32-bit byte swap
pub open spec fn bswap32(v: int) -> int {
    0xFF000000 * ((v / 0x1000000) % 256) as int / 0x1000000
        + 0x00FF0000 * ((v / 0x10000) % 256) as int / 0x10000
        + 0x0000FF00 * ((v / 0x100) % 256) as int / 0x100
}

pub open spec fn le_bytes_u32(v: int) -> Seq<u8> {
    Seq::new(4, |k: int| ((v / pow2int(8 * k as nat)) % 256) as u8)
}

// ============================================================
// constants (ENCODED_SIZE = size_of::<T>())
// ============================================================

pub const ENCODED_SIZE_U8: usize = 1;
pub const ENCODED_SIZE_U16: usize = 2;
pub const ENCODED_SIZE_U32: usize = 4;
pub const ENCODED_SIZE_U64: usize = 8;
pub const ENCODED_SIZE_U128: usize = 16;
pub const ENCODED_SIZE_USIZE: usize = 8;
pub const ENCODED_SIZE_I8: usize = 1;
pub const ENCODED_SIZE_I16: usize = 2;
pub const ENCODED_SIZE_I32: usize = 4;
pub const ENCODED_SIZE_I64: usize = 8;
pub const ENCODED_SIZE_ISIZE: usize = 8;

// ============================================================
// exec mirror: the u8 family (Origin: fixed.rs:37-79 macro impl)
// ============================================================

/// Origin: impl_fixedint!(u8): encode_fixed / encode_fixed_light / decode_fixed / switch_endianness
/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_u8(v: u8, dst: &mut [u8]) -> (r: Option<()>)
    ensures
        r matches None ==> final(dst)@ == old(dst)@,
        r matches Some(_) ==> final(dst)@.len() == old(dst)@.len()
            && final(dst).len() == ENCODED_SIZE_U8
            && final(dst)@ [0] == v,
{
    // Origin: if dst.len() == size_of::<Self>() { dst.clone_from_slice(&self.to_le_bytes()); Some(()) } else { None }
    if dst.len() == ENCODED_SIZE_U8 {
        dst[0] = v;
        Some(())
    } else {
        None
    }
}

/// Origin: impl_fixedint!(u8)::encode_fixed_light -- Self::Bytes = [u8;1]
/// Upstream doc (fixed.rs:18-19):
///   Returns the representation of [`FixedInt`] as [`Bytes`], the little-endian representation
///   of self in the stack.
pub exec fn encode_fixed_light_u8(v: u8) -> (o: [u8; 1]) {
    // Origin: self.to_le_bytes() (the u8 LE byte is itself)
    [v]
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_u8(src: &[u8]) -> (r: Option<u8>)
    ensures
        r matches Some(v) ==> src.len() == ENCODED_SIZE_U8 && v == src[0],
        r matches None ==> src.len() != ENCODED_SIZE_U8,
{
    // Origin: if src.len() == size_of::<Self>() { Some(Self::from_le_bytes(src.try_into().unwrap())) } else { None }
    if src.len() == ENCODED_SIZE_U8 {
        Some(src[0])
    } else {
        None
    }
}

/// Origin: switch_endianness -- the u8 single byte is unchanged
/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_u8(v: u8) -> (r: u8)
    ensures r == v
{
    v
}

// ============================================================
// exec mirror: the u16 family
// ============================================================

/// le byte expansion (u16)
#[inline]
exec fn u16_byte_lo(v: u16) -> (b: u8) ensures b == ((v as u64) as u8) as u8 { (v) as u8 }
exec fn u16_byte_hi(v: u16) -> (b: u8)
    ensures b == ((( (v as u64) >> 8)) as u8)
{ (((v as u64) >> 8)) as u8 }

/// Origin: impl_fixedint!(u16)
/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_u16(v: u16, dst: &mut [u8]) -> (r: Option<()>)
    ensures
        r matches None ==> final(dst)@ == old(dst)@,
        r matches Some(_)
            ==> final(dst)@.len() == old(dst)@.len()
                && final(dst).len() == ENCODED_SIZE_U16,
{
    // Origin: the dst.len() == size_of::<Self>() check
    if dst.len() == ENCODED_SIZE_U16 {
        // Origin: dst.clone_from_slice(&self.to_le_bytes())
        dst[0] = u16_byte_lo(v);
        dst[1] = u16_byte_hi(v);
        Some(())
    } else {
        None
    }
}

/// Upstream doc (fixed.rs:18-19):
///   Returns the representation of [`FixedInt`] as [`Bytes`], the little-endian representation
///   of self in the stack.
pub exec fn encode_fixed_light_u16(v: u16) -> (o: [u8; 2]) {
    // Origin: self.to_le_bytes()
    [u16_byte_lo(v), u16_byte_hi(v)]
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_u16(src: &[u8]) -> (r: Option<u16>)
    ensures
        r matches None ==> src.len() != ENCODED_SIZE_U16,
{
    if src.len() == ENCODED_SIZE_U16 {
        let lo = src[0];
        let hi = src[1];
        // Origin: Self::from_le_bytes(...) -- LE assembly
        Some((((lo as u16) | ((hi as u16) << 8))) as u16)
    } else {
        None
    }
}

/// Origin: switch_endianness (u16): from_le_bytes(to_be_bytes())
/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_u16(v: u16) -> (r: u16)
{
    // the BE bytes of v = the LE bytes reversed; read back as LE -- i.e. the byte swap:
    (((v >> 8) as u16) | ((v << 8) as u16)) as u16
}

// ============================================================
// exec mirror: the u32 family
// ============================================================

exec fn u32_byte_at(v: u64, k: usize) -> (b: u8)
    requires k < 4
    ensures b == ((v >> (8 * k)) as u8)
{
    (((v >> (8 * k)) as u8) as u8)
}

/// Origin: impl_fixedint!(u32)
/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_u32(v: u32, dst: &mut [u8]) -> (r: Option<()>)
    ensures
        r matches None ==> final(dst)@ == old(dst)@,
        r matches Some(_)
            ==> final(dst)@.len() == old(dst)@.len()
                && final(dst).len() == ENCODED_SIZE_U32,
    // SPEC-DOC MISMATCH (unreported): the doc attributes the None return to
    // "dst doesn't provide enough space" (None only for insufficient space),
    // but a longer dst that does provide enough space (len > ENCODED_SIZE) also
    // yields None -- the doc-promised sufficient-space success clause is
    // unprovable; the implementation-faithful exact-length form is carried by
    // the ensures clause above.
{
    if dst.len() == ENCODED_SIZE_U32 {
        let w = v as u64;
        dst[0] = u32_byte_at(w, 0);
        dst[1] = u32_byte_at(w, 1);
        dst[2] = u32_byte_at(w, 2);
        dst[3] = u32_byte_at(w, 3);
        Some(())
    } else {
        None
    }
}

/// Upstream doc (fixed.rs:18-19):
///   Returns the representation of [`FixedInt`] as [`Bytes`], the little-endian representation
///   of self in the stack.
pub exec fn encode_fixed_light_u32(v: u32) -> (o: [u8; 4]) {
    let w = v as u64;
    [u32_byte_at(w, 0), u32_byte_at(w, 1), u32_byte_at(w, 2), u32_byte_at(w, 3)]
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_u32(src: &[u8]) -> (r: Option<u32>)
    ensures r matches None ==> src.len() != ENCODED_SIZE_U32,
{
    if src.len() == ENCODED_SIZE_U32 {
        let b0 = (src[0] as u32) & 0xff;
        let b1 = (src[1] as u32) & 0xff;
        let b2 = (src[2] as u32) & 0xff;
        let b3 = (src[3] as u32) & 0xff;
        Some(b0 | (b1 << 8) | (b2 << 16) | (b3 << 24))
    } else {
        None
    }
}

/// Origin: switch_endianness (u32)
/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_u32(v: u32) -> (r: u32)
{
    // the bytes [a,b,c,d] reversed to [d,c,b,a]
    let w = v;
    ((((w >> 24) | ((w >> 8) & 0x0000ff00) | ((w << 8) & 0x00ff0000) | (w << 24))) as u32)
}

// ============================================================
// exec mirror: the u64 family
// ============================================================

exec fn u64_byte_at(v: u64, k: usize) -> (b: u8)
    requires k < 8
{
    ((v >> (8 * k)) as u8)
}

/// Origin: impl_fixedint!(u64)
/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_u64(v: u64, dst: &mut [u8]) -> (r: Option<()>)
    ensures
        r matches None ==> final(dst)@ == old(dst)@,
        r matches Some(_)
            ==> final(dst)@.len() == old(dst)@.len()
                && final(dst).len() == ENCODED_SIZE_U64,
{
    if dst.len() == ENCODED_SIZE_U64 {
        dst[0] = u64_byte_at(v, 0);
        dst[1] = u64_byte_at(v, 1);
        dst[2] = u64_byte_at(v, 2);
        dst[3] = u64_byte_at(v, 3);
        dst[4] = u64_byte_at(v, 4);
        dst[5] = u64_byte_at(v, 5);
        dst[6] = u64_byte_at(v, 6);
        dst[7] = u64_byte_at(v, 7);
        Some(())
    } else {
        None
    }
}

/// Upstream doc (fixed.rs:18-19):
///   Returns the representation of [`FixedInt`] as [`Bytes`], the little-endian representation
///   of self in the stack.
pub exec fn encode_fixed_light_u64(v: u64) -> (o: [u8; 8]) {
    [
        u64_byte_at(v, 0),
        u64_byte_at(v, 1),
        u64_byte_at(v, 2),
        u64_byte_at(v, 3),
        u64_byte_at(v, 4),
        u64_byte_at(v, 5),
        u64_byte_at(v, 6),
        u64_byte_at(v, 7),
    ]
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_u64(src: &[u8]) -> (r: Option<u64>)
    ensures r matches None ==> src.len() != ENCODED_SIZE_U64,
{
    // Origin: Self::from_le_bytes(src.try_into().unwrap()) -- LE assembly expanded
    //   bit position by bit position over the 8 bytes
    if src.len() == ENCODED_SIZE_U64 {
        proof { assert(src.len() >= 8); }
        let b0 = src[0] as u64;
        let b1 = src[1] as u64;
        let b2 = src[2] as u64;
        let b3 = src[3] as u64;
        let b4 = src[4] as u64;
        let b5 = src[5] as u64;
        let b6 = src[6] as u64;
        let b7 = src[7] as u64;
        Some(b0 | (b1 << 8) | (b2 << 16) | (b3 << 24) | (b4 << 32) | (b5 << 40) | (b6 << 48) | (b7 << 56))
    } else {
        None
    }
}

/// Origin: switch_endianness (u64)
/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_u64(v: u64) -> (r: u64)
{
    let w = v;
    let mut o: u64 = 0;
    let mut i: usize = 0;
    while i < 8
        invariant i <= 8,
        decreases 8 - i
    {
        o |= (((w >> (8 * i)) as u8) as u64) << (8 * (7 - i));
        i += 1;
    }
    o
}

// ============================================================
// exec mirror: the usize/usize family sharing the 8B group (the mirror treats usize
//   as an 8-byte LE value)
// ============================================================

/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_usize(v: usize, dst: &mut [u8]) -> (r: Option<()>)
    ensures
        r matches None ==> final(dst)@ == old(dst)@,
        r matches Some(_) ==> final(dst).len() == ENCODED_SIZE_USIZE,
{
    encode_fixed_u64(v as u64, dst)
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_usize(src: &[u8]) -> (r: Option<usize>)
    ensures r matches None ==> src.len() != ENCODED_SIZE_USIZE,
{
    match decode_fixed_u64(src) {
        Some(v) => Some(v as usize),
        None => None,
    }
}

/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_usize(v: usize) -> (r: usize) {
    switch_endianness_u64(v as u64) as usize
}

// ============================================================
// exec mirror: the signed family (i8/i16/i32/i64/isize) -- same-width uint bit patterns
// ============================================================

/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_i8(v: i8, dst: &mut [u8]) -> (r: Option<()>)
    ensures r matches None ==> final(dst)@ == old(dst)@,
{
    encode_fixed_u8(#[verifier::truncate] (v as u8), dst)
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_i8(src: &[u8]) -> (r: Option<i8>)
    ensures r matches None ==> src.len() != ENCODED_SIZE_I8,
{
    match decode_fixed_u8(src) {
        Some(v) => Some(#[verifier::truncate] (v as i8)),
        None => None,
    }
}

/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_i8(v: i8) -> (r: i8) {
    v
}

/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_i16(v: i16, dst: &mut [u8]) -> (r: Option<()>)
    ensures r matches None ==> final(dst)@ == old(dst)@,
{
    encode_fixed_u16(#[verifier::truncate] (v as u16), dst)
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_i16(src: &[u8]) -> (r: Option<i16>)
    ensures r matches None ==> src.len() != ENCODED_SIZE_I16,
{
    match decode_fixed_u16(src) {
        Some(v) => Some(#[verifier::truncate] (v as i16)),
        None => None,
    }
}

/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_i16(v: i16) -> (r: i16) {
    #[verifier::truncate] (switch_endianness_u16(#[verifier::truncate] (v as u16)) as i16)
}

/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_i32(v: i32, dst: &mut [u8]) -> (r: Option<()>)
    ensures r matches None ==> final(dst)@ == old(dst)@,
{
    encode_fixed_u32(#[verifier::truncate] (v as u32), dst)
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_i32(src: &[u8]) -> (r: Option<i32>)
    ensures r matches None ==> src.len() != ENCODED_SIZE_I32,
{
    match decode_fixed_u32(src) {
        Some(v) => Some(#[verifier::truncate] (v as i32)),
        None => None,
    }
}

/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_i32(v: i32) -> (r: i32) {
    #[verifier::truncate] (switch_endianness_u32(#[verifier::truncate] (v as u32)) as i32)
}

/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_i64(v: i64, dst: &mut [u8]) -> (r: Option<()>)
    ensures r matches None ==> final(dst)@ == old(dst)@,
{
    encode_fixed_u64(#[verifier::truncate] (v as u64), dst)
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_i64(src: &[u8]) -> (r: Option<i64>)
    ensures r matches None ==> src.len() != ENCODED_SIZE_I64,
{
    match decode_fixed_u64(src) {
        Some(v) => Some(#[verifier::truncate] (v as i64)),
        None => None,
    }
}

/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_i64(v: i64) -> (r: i64) {
    #[verifier::truncate] (switch_endianness_u64(#[verifier::truncate] (v as u64)) as i64)
}

/// Upstream doc (fixed.rs:13-16):
///   Encode a value into the given slice using little-endian. Returns `None` if `dst`
///   doesn't provide enough space to encode this integer.
///
///   Use `switch_endianness()` if machine endianness doesn't match the desired target encoding.
pub exec fn encode_fixed_isize(v: isize, dst: &mut [u8]) -> (r: Option<()>)
    ensures r matches None ==> final(dst)@ == old(dst)@,
{
    encode_fixed_u64(#[verifier::truncate] (v as u64), dst)
}

/// Upstream doc (fixed.rs:22-23):
///   Decode a value from the given slice assuming little-endian. Use `switch_endianness()` on
///   the returned value if the source was not encoded in little-endian.
pub exec fn decode_fixed_isize(src: &[u8]) -> (r: Option<isize>)
    ensures r matches None ==> src.len() != ENCODED_SIZE_ISIZE,
{
    match decode_fixed_u64(src) {
        Some(v) => Some(#[verifier::truncate] (v as isize)),
        None => None,
    }
}

/// Upstream doc (fixed.rs:31-33):
///   integer-encoding-rs always emits and receives little-endian integers (converting implicitly
///   on big-endian machines). If you receive a big-endian integer, and would like it to be
///   treated correctly, use this helper method to convert between endiannesses.
pub exec fn switch_endianness_isize(v: isize) -> (r: isize) {
    #[verifier::truncate] (switch_endianness_u64(#[verifier::truncate] (v as u64)) as isize)
}

// ============================================================
// exec mirror: the encode_fixed_vec trait default method (fixed.rs:26-29)
// Every type is mirrored as "encode_fixed into a stack fixed-size array, then Vec copy"
//   (equal in value to the upstream
//   encode_fixed_light().as_ref().to_vec())
// ============================================================

/// Upstream doc (fixed.rs:26-26):
///   Helper: Encode the value and return a Vec.
pub exec fn encode_fixed_vec_u64(v: u64) -> (o: Vec<u8>)
{
    // Origin: self.encode_fixed_light().as_ref().to_vec()
    let mut out: Vec<u8> = Vec::new();
    let buf: [u8; 8] = encode_fixed_light_u64(v);
    let mut i: usize = 0;
    while i < 8
        invariant i <= 8,
        decreases 8 - i
    {
        out.push(buf[i]);
        i += 1;
    }
    out
}

/// Upstream doc (fixed.rs:26-26):
///   Helper: Encode the value and return a Vec.
pub exec fn encode_fixed_vec_u32(v: u32) -> (o: Vec<u8>)
{
    let mut out: Vec<u8> = Vec::new();
    let buf: [u8; 4] = encode_fixed_light_u32(v);
    let mut i: usize = 0;
    while i < 4
        invariant i <= 4,
        decreases 4 - i
    {
        out.push(buf[i]);
        i += 1;
    }
    out
}

/// Upstream doc (fixed.rs:26-26):
///   Helper: Encode the value and return a Vec.
pub exec fn encode_fixed_vec_u16(v: u16) -> (o: Vec<u8>)
{
    let mut out: Vec<u8> = Vec::new();
    let buf: [u8; 2] = encode_fixed_light_u16(v);
    let mut i: usize = 0;
    while i < 2
        invariant i <= 2,
        decreases 2 - i
    {
        out.push(buf[i]);
        i += 1;
    }
    out
}

/// Upstream doc (fixed.rs:26-26):
///   Helper: Encode the value and return a Vec.
pub exec fn encode_fixed_vec_u8(v: u8) -> (o: Vec<u8>)
{
    let mut out: Vec<u8> = Vec::new();
    out.push(v);
    out
}


// ============================================================
// exec mirror completion: the encode_fixed_light signed family (fixed.rs:51-53 macro expansion)
// ============================================================

/// Upstream doc (fixed.rs:18-19):
///   Returns the representation of [`FixedInt`] as [`Bytes`], the little-endian representation
///   of self in the stack.
pub exec fn encode_fixed_light_i8(v: i8) -> (o: [u8; 1]) {
    [#[verifier::truncate] (v as u8)]
}

/// Upstream doc (fixed.rs:18-19):
///   Returns the representation of [`FixedInt`] as [`Bytes`], the little-endian representation
///   of self in the stack.
pub exec fn encode_fixed_light_i16(v: i16) -> (o: [u8; 2]) {
    let u = #[verifier::truncate] (v as u16);
    [u16_byte_lo(u), u16_byte_hi(u)]
}

/// Upstream doc (fixed.rs:18-19):
///   Returns the representation of [`FixedInt`] as [`Bytes`], the little-endian representation
///   of self in the stack.
pub exec fn encode_fixed_light_i32(v: i32) -> (o: [u8; 4]) {
    let w = (#[verifier::truncate] (v as u32)) as u64;
    let b0 = u32_byte_at(w, 0);
    let b1 = u32_byte_at(w, 1);
    let b2 = u32_byte_at(w, 2);
    let b3 = u32_byte_at(w, 3);
    [b0, b1, b2, b3]
}

/// Upstream doc (fixed.rs:18-19):
///   Returns the representation of [`FixedInt`] as [`Bytes`], the little-endian representation
///   of self in the stack.
pub exec fn encode_fixed_light_i64(v: i64) -> (o: [u8; 8]) {
    let w = #[verifier::truncate] (v as u64);
    [
        u64_byte_at(w, 0),
        u64_byte_at(w, 1),
        u64_byte_at(w, 2),
        u64_byte_at(w, 3),
        u64_byte_at(w, 4),
        u64_byte_at(w, 5),
        u64_byte_at(w, 6),
        u64_byte_at(w, 7),
    ]
}

} // verus!
