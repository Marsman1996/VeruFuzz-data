//! data-encoding library mirror
//!
//! Upstream: https://github.com/ia0/data-encoding
//!   pin 53e2ff65eb3157a7b113b8a1a8b3fc89ce898dbf (SUBDIR=lib; the code/ tree is untouched)
//!   The single library source file code/lib/src/lib.rs maps to this file (same-name mirror).
//!
//! Mirror and relaxation ledger (KVerus relax conventions; see out/bug-finder-summary.md):
//! 1. The `Static<usize>`/`Bool`/`Option<u8>` + `dispatch!` constant-monomorphization macro
//!    (lib.rs:165-242) is a performance-only compile-time trick (the panic face sits in
//!    the `dispatch!` `_ => panic!()` arm), outside the Verus supported surface; its
//!    semantics = "value parameters + value matching". This mirror monomorphizes on
//!    the value parameters (bit, msb, pad, wrap), the contract being the upstream generic instance's contract.
//! 2. `vectorize` (lib.rs:264-274) = the f(i) for i in 0..n calls bucketed by bs and invoked in
//!    order; for bit=4 (bs=1) it always equals a sequential for loop, so the mirror writes a sequential loop (Origin note).
//! 3. The 514+ byte literal tables of the predefined constants (HEXLOWER etc., lib.rs:2032-2816)
//!    are transcribed per the hex-crate precedent (database/hex) into equivalent interval-logic
//!    queries; the table <-> interval equivalence is fully witnessed at runtime against the
//!    upstream pin tree (byte-by-byte comparison of the 256xN entries).
//! 4. `chunk_unchecked` (lib.rs:244-248, unsafe slicing) is replaced in the mirror by the safe
//!    indexed slice `&x[a..b]` (the up-front length assertion carried by the contract), equivalent behavior.
//! 5. The `Cow<'static, [u8]>`/`Vec` allocation paths (Encoding::encode/decode etc.) are rewritten
//!    per the database/hex precedent as incremental `Vec::new`+push construction, the sequence
//!    contract being identical to the upstream resize+fill.
//! 6. The String/alloc side (Specification::encoding, encode_append, Encoder, etc.) needs a
//!    String spec layer and is not transcribed this cycle (see the summary).
//!
//! Consumption: no fn main in this file; the harness/ files pull it in via `#[path]` mods
//! and must not copy its spec.

use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::std_specs::vec::*;
use vstd::arithmetic::mul::{lemma_mul_upper_bound, lemma_mul_is_commutative};
use vstd::arithmetic::div_mod::{lemma_div_is_ordered, lemma_div_by_multiple, lemma_remainder_lower};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ============================================================
 * Decoding error model (Origin: lib.rs:276-340)
 * ============================================================ */

/// Origin: lib.rs:277-290 `pub enum DecodeKind`
#[derive(PartialEq, Eq)]
pub enum DecodeKind {
    Length,
    Symbol,
    Trailing,
    Padding,
}

/// Origin: lib.rs:304-314 `pub struct DecodeError` (position/kind public field semantics)
#[derive(PartialEq, Eq)]
pub struct DecodeError {
    pub position: usize,
    pub kind: DecodeKind,
}

/// Origin: lib.rs:325-340 `pub struct DecodePartial`
#[derive(PartialEq, Eq)]
pub struct DecodePartial {
    pub read: usize,
    pub written: usize,
    pub error: DecodeError,
}

/// Origin: lib.rs:342-344 table sentinel constants (INVALID=128 / IGNORE=129 / PADDING=130)
pub const INVALID: u8 = 128;

/* ============================================================
 * Common arithmetic core (Origin: lib.rs:244-368; dispatch!/Static monomorphization, see ledger 1)
 * ============================================================ */

/// div_ceil from the spec viewpoint (for use in contracts)
pub open spec fn div_ceil_spec(x: int, m: int) -> int {
    (x + m - 1) / m
}

/// Origin: lib.rs:256-258 `fn div_ceil(x, m) -> usize { (x + m - 1) / m }`
pub exec fn div_ceil(x: usize, m: usize) -> (r: usize)
    requires
        m > 0,
        (x as int) + (m as int) <= usize::MAX as int,
    ensures
        (r as int) == div_ceil_spec(x as int, m as int),
{
    (x + m - 1) / m
}

/// Origin: lib.rs:260-262 `fn floor(x, m) -> usize { x / m * m }`
pub exec fn floor_up(x: usize, m: usize) -> (r: usize)
    requires
        m > 0,
        (x as int) <= usize::MAX as int,
    ensures (r as int) == x as int / m as int * (m as int)
{
    proof {
        lemma_remainder_lower(x as int, m as int);
    }
    x / m * m
}

/// enc from the spec viewpoint (lib.rs:354-362; referenced across contracts)
pub open spec fn enc_of_bit_spec(bit: int) -> int
{
    if bit == 1 || bit == 2 || bit == 4 {
        1
    } else if bit == 3 || bit == 6 {
        3
    } else {
        5
    }
}

/// dec from the spec viewpoint (lib.rs:364-367)
pub open spec fn dec_of_bit_spec(bit: int) -> int {
    enc_of_bit_spec(bit) * 8 / bit
}

/// Origin: lib.rs:354-362 `fn enc(bit)` (input block length; `_ => unreachable!()` excluded
/// by the requires)
pub exec fn enc_of_bit(bit: usize) -> (r: usize)
    requires 1 <= bit <= 6
    ensures
        bit == 1 || bit == 2 || bit == 4 ==> r == 1,
        bit == 3 || bit == 6 ==> r == 3,
        bit == 5 ==> r == 5,
{
    match bit {
        1 => 1,
        2 => 1,
        4 => 1,
        3 => 3,
        6 => 3,
        5 => 5,
        _ => unreachable!(),
    }
}

/// Origin: lib.rs:364-367 `fn dec(bit) = enc(bit) * 8 / bit`
pub exec fn dec_of_bit(bit: usize) -> (r: usize)
    requires 1 <= bit <= 6
    ensures (r as int) == dec_of_bit_spec(bit as int)
{
    match bit {
        1 => 8,
        2 => 4,
        4 => 2,
        3 => 8,
        6 => 4,
        5 => 8,
        _ => unreachable!(),
    }
}

/// Origin: lib.rs:346-352 `fn order(msb, n, i)`
pub exec fn order(msb: bool, n: usize, i: usize) -> (r: usize)
    requires i < n
    ensures (r as int) == if msb { n as int - 1 - i as int } else { i as int }
{
    if msb {
        n - 1 - i
    } else {
        i
    }
}

/* ============================================================
 * Length API family (Origin: lib.rs:369-602)
 * Bound constraints mirror the upstream public panic contracts: encode_len asserts len <= usize::MAX / 512
 * (lib.rs:1328), decode_len asserts len <= usize::MAX / 8 (lib.rs:1543).
 * ============================================================ */

/// Origin: lib.rs:369-371 `fn encode_len::<B>(bit, len)
/// = div_ceil(8 * len, bit.val())` (Static monomorphized to value parameters)
pub exec fn encode_len_of(bit: usize, len: usize) -> (r: usize)
    requires
        1 <= bit <= 6,
        (len as int) <= usize::MAX as int / 512,
    ensures
        (r as int) == div_ceil_spec(8 * len as int, bit as int),
{
    let eight_len = 8 * len;
    div_ceil(eight_len, bit)
}


/// Origin: lib.rs:481-483 `fn encode_base_len::<B>(bit, len)
/// = encode_len(bit, len)`
pub exec fn encode_base_len(bit: usize, len: usize) -> (r: usize)
    requires
        1 <= bit <= 6,
        (len as int) <= usize::MAX as int / 512,
    ensures (r as int) == div_ceil_spec(8 * len as int, bit as int),
{
    encode_len_of(bit, len)
}

/// Origin: lib.rs:492-497 `fn encode_pad_len::<B,P>(bit, pad, len)`
pub exec fn encode_pad_len(bit: usize, pad: Option<u8>, len: usize) -> (r: usize)
    requires
        1 <= bit <= 6,
        (len as int) <= usize::MAX as int / 512,
    ensures
        pad.is_none() ==> (r as int) == div_ceil_spec(8 * len as int, bit as int),
        pad.is_some() ==> (r as int)
            == div_ceil_spec(len as int, enc_of_bit_spec(bit as int))
                * dec_of_bit_spec(bit as int),
{
    match pad {
        None => encode_base_len(bit, len),
        Some(_) => {
            /* Origin Rust: dispatch! { let bit:usize = self.bit(); ... } static dispatch
               => each branch's bit is the constant N1..N6 (lib.rs:216-242) => enc/dec are also constants */
            let (e, d) = match bit {
                1 => (1usize, 8usize),
                2 => (1usize, 4usize),
                3 => (3usize, 8usize),
                4 => (1usize, 2usize),
                5 => (5usize, 8usize),
                _ => (3usize, 4usize), // bit == 6
            };
            let q = div_ceil(len, e);
            proof {
                lemma_enc_dec_constants(bit as int);
                assert((q as int) == div_ceil_spec(len as int, e as int));
                assert(enc_of_bit_spec(bit as int) == (e as int));
                assert(dec_of_bit_spec(bit as int) == (d as int));
                // product upper bound: d <= 8 and q <= len+e <= MAX/512+5 (bit a constant per branch)
                assert(0 <= (q as int) && (q as int) <= (len as int) + (e as int));
                assert(0 < (d as int) && (d as int) <= 8);
                lemma_mul_upper_bound(
                    (q as int),
                    (len as int) + (e as int),
                    d as int,
                    8,
                );
                lemma_mul_upper_bound(
                    (len as int) + (e as int),
                    usize::MAX as int / 512 + 5,
                    d as int,
                    8,
                );
                assert(((len as int) + (e as int)) * (d as int)
                    <= (usize::MAX as int / 512 + 5) * 8);
                assert((usize::MAX as int / 512 + 5) * 8 <= usize::MAX as int);
            }
            let rr = q * d;
            rr
        }
    }
}

/// spec viewpoint of encode_pad_len / encode_wrap_len (lib.rs:492-527;
/// pad_some: the upstream pad Option semantics, wrap parameterized by the (col, end_len) ints)
pub open spec fn encode_pad_len_spec(bit: int, pad_some: bool, len: int) -> int {
    if pad_some {
        div_ceil_spec(len, enc_of_bit_spec(bit)) * dec_of_bit_spec(bit)
    } else {
        div_ceil_spec(8 * len, bit)
    }
}

pub open spec fn encode_wrap_len_spec(
    bit: int,
    pad_some: bool,
    ilen: int,
    wrap_col: int,
    wrap_end: int,
) -> int {
    let olen = encode_pad_len_spec(bit, pad_some, ilen);
    if wrap_col <= 0 && wrap_end <= 0 {
        olen
    } else {
        olen + wrap_end * div_ceil_spec(olen, wrap_col)
    }
}

/// Origin: lib.rs:514-527 `fn encode_wrap_len::<B,P,W>(bit, pad, wrap, ilen)`
///   olen + end.len() * div_ceil(olen, col)`)
pub exec fn encode_wrap_len(
    bit: usize,
    pad: Option<u8>,
    wrap: Option<(usize, &[u8])>,
    ilen: usize,
) -> (r: usize)
    requires
        1 <= bit <= 6,
        (ilen as int) <= usize::MAX as int / 512,
        wrap.is_some() ==> {
            let (col, end) = wrap.get_Some_0();
            0 < (col as int)
                && (col as int) % dec_of_bit_spec(bit as int) == 0
                && encode_pad_len_spec(bit as int, pad.is_some(), ilen as int)
                    + col as int <= usize::MAX as int
                && (end@.len() as int)
                    * div_ceil_spec(
                        encode_pad_len_spec(bit as int, pad.is_some(), ilen as int),
                        col as int,
                    )
                    + encode_pad_len_spec(bit as int, pad.is_some(), ilen as int)
                    <= usize::MAX as int
        },
    // SPEC-DOC MISMATCH (unreported): the upstream wrap-extension doc promises
    //  "the output always ends with the separator" unconditionally, but that clause
    //  is unprovable as stated; this ensures carries the implementation-faithful form
    //  -- with an empty input (ilen == 0) it gives r == 0, i.e. no separator at all.
    ensures
        wrap.is_none() ==> (r as int) == encode_wrap_len_spec(
            bit as int,
            pad.is_some(),
            ilen as int,
            0,
            0, /* no wrap: olen = encode_pad_len */
        ),
        wrap.is_some() ==> {
            let (col, end) = wrap.get_Some_0();
            (r as int) == encode_wrap_len_spec(
                bit as int,
                pad.is_some(),
                ilen as int,
                col as int,
                end@.len() as int,
            )
        },
{
    let olen = encode_pad_len(bit, pad, ilen);
    match wrap {
        None => olen,
        Some((col, end)) => {
            let add = div_ceil(olen, col);
            proof {
                assert((add as int) == div_ceil_spec(olen as int, col as int));
                assert((olen as int) == encode_pad_len_spec(
                    bit as int,
                    pad.is_some(),
                    ilen as int,
                ));
                assert((end.len() as int) * (add as int)
                    + encode_pad_len_spec(bit as int, pad.is_some(), ilen as int)
                    <= usize::MAX as int);
            }
            let head = end.len() * add;
            olen + head
        }
    }
}

/// spec viewpoint of decode_wrap_len (lib.rs:562-573): the "longest valid input length" and its output length
pub open spec fn decode_wrap_len_spec(bit: int, pad: bool, len: int) -> (int, int) {
    if pad {
        (len / dec_of_bit_spec(bit) * dec_of_bit_spec(bit),
            len / dec_of_bit_spec(bit) * enc_of_bit_spec(bit))
    } else {
        (len - bit * len % 8 / bit, bit * len / 8)
    }
}

/// Origin: lib.rs:562-573 `fn decode_wrap_len::<B,P>(bit, pad, len)`
///   -> (longest valid input length, associated output length)
pub exec fn decode_wrap_len(bit: usize, pad: bool, len: usize) -> (r: (usize, usize))
    requires
        1 <= bit <= 6,
        (len as int) <= usize::MAX as int / 8,
    ensures
        (r.0 as int) == decode_wrap_len_spec(bit as int, pad, len as int).0,
        (r.1 as int) == decode_wrap_len_spec(bit as int, pad, len as int).1,
{
    /* Origin Rust: dispatch! { let bit: usize = self.bit(); ... } static dispatch
       => bit is a constant => dec/enc are constants (lib.rs:216-242) */
    let (d, e) = match bit {
        1 => (8usize, 1usize),
        2 => (4usize, 1usize),
        3 => (8usize, 3usize),
        4 => (2usize, 1usize),
        5 => (8usize, 5usize),
        _ => (4usize, 3usize), // bit == 6
    };
    if pad {
        /* Origin Rust: (floor(len, dec(bit)), len / dec(bit) * enc(bit)) */
        proof {
            lemma_enc_dec_constants(bit as int);
            assert((d as int) == dec_of_bit_spec(bit as int));
            assert((e as int) == enc_of_bit_spec(bit as int));
            assert(0 <= (len as int) && (len as int) <= usize::MAX as int / 8);
            assert(0 < (e as int) && (e as int) <= 5);
            assert((len as int) / (d as int) <= (len as int));
            lemma_mul_upper_bound(
                (len as int) / (d as int),
                (len as int),
                e as int,
                5,
            );
            assert(((len as int) / (d as int)) * (e as int) <= (len as int) * 5);
            assert((len as int) * 5 <= usize::MAX as int);
        }
        let f = floor_up(len, d);
        let o = len / d * e;
        (f, o)
    } else {
        /* Origin Rust: len - (bit*len % 8)/bit, bit*len/8 */
        proof {
            assert(0 <= (bit as int) && (bit as int) <= 6);
            assert(0 <= (len as int) && (len as int) <= usize::MAX as int / 8);
            lemma_mul_upper_bound(bit as int, 6, len as int, usize::MAX as int / 8);
            assert((bit as int) * (len as int) <= 6 * (usize::MAX as int / 8));
            assert(8 * (usize::MAX as int / 8) <= usize::MAX as int);
            assert(6 * (usize::MAX as int / 8) <= 8 * (usize::MAX as int / 8));
            assert((bit as int) * (len as int) <= usize::MAX as int);
        }
        let trail = bit * len % 8;
        proof {
            assert((trail as int) == (bit as int) * (len as int) % 8);
            lemma_div_is_ordered(trail as int, (bit as int) * (len as int), bit as int);
            assert((trail as int) / (bit as int) <= (bit as int) * (len as int) / (bit as int));
            lemma_mul_is_commutative(len as int, bit as int);
            assert((bit as int) * (len as int) == (len as int) * (bit as int));
            lemma_div_by_multiple(len as int, bit as int);
            assert((len as int) * (bit as int) / (bit as int) == (len as int));
            assert((bit as int) * (len as int) / (bit as int) == (len as int));
            assert(0 <= (len as int) - (trail as int) / (bit as int));
        }
        let i = len - trail / bit;
        let o = bit * len / 8;
        (i, o)
    }
}

/// Origin: lib.rs:577-583 `fn decode_pad_len::<B,P>(bit, pad, len)`
///   check!(DecodeError{position: ilen, Length}, ilen == len) -- the macro expands to an
///   if-return (lib.rs:165-171 `check!` definition).
/// Documented contract (lib.rs:1536): "The error kind is Length and the position is the
/// greatest valid input length."
pub exec fn decode_pad_len(bit: usize, pad: bool, len: usize) -> (r: Result<usize, DecodeError>)
    requires
        1 <= bit <= 6,
        (len as int) <= usize::MAX as int / 8,
    ensures
        ({
            let (ilen, olen) = decode_wrap_len_spec(bit as int, pad, len as int);
            (ilen == len as int ==> r == Result::Ok(olen as usize))
                && (ilen != len as int ==> r == Result::Err(
                    DecodeError { position: ilen as usize, kind: DecodeKind::Length },
                ))
        }),
{
    let (ilen, olen) = decode_wrap_len(bit, pad, len);
    if ilen != len {
        return Result::Err(DecodeError { position: ilen, kind: DecodeKind::Length });
    }
    Result::Ok(olen)
}

/// Origin: lib.rs:587-589 `fn decode_base_len::<B>(bit, len)
///   = decode_pad_len(bit, Bf, len)`
pub exec fn decode_base_len(bit: usize, len: usize) -> (r: Result<usize, DecodeError>)
    requires
        1 <= bit <= 6,
        (len as int) <= usize::MAX as int / 8,
    ensures
        ({
            let (ilen, olen) = decode_wrap_len_spec(bit as int, false, len as int);
            (ilen == len as int ==> r == Result::Ok(olen as usize))
                && (ilen != len as int ==> r == Result::Err(
                    DecodeError { position: ilen as usize, kind: DecodeKind::Length },
                ))
        }),
{
    decode_pad_len(bit, false, len)
}

/* ============================================================
 * Encoding-level entries (Origin: lib.rs:1256-1756 impl Encoding,
 * table accesses (sym/val/pad/ctb/msb/bit) monomorphized to value parameters, see ledger 3)
 * ============================================================ */

/// Origin: lib.rs:1542-1554 `Encoding::decode_len(&self, len)`
///   check!(DecodeError{position: ilen, Length}, self.has_ignore() || len == ilen)
/// Upstream doc (lib.rs:1512-1541):
///   Returns the maximum decoded length of an input of length `len`
///   See [`decode_mut`] for when to use it. In particular, the actual decoded length might be
///   smaller if the actual input contains padding or ignored characters.
///   # Panics
///   May panic if `len` is greater than `usize::MAX / 8`:
///   - `len <= 536_870_911` when `target_pointer_width = "32"`
///   - `len <= 2_305843_009213_693951` when `target_pointer_width = "64"`
///   If you need to decode an input of length greater than this limit (possibly of infinite
///   length), then you must chunk your input, decode each chunk, and concatenate to obtain the
///   output. The number of non-ignored characters of each input chunk (except the last) must be a
///   multiple of [`decode_align`].
///   Note that this function only _may_ panic in those cases. The function may also return the
///   correct value in some cases depending on the implementation. In other words, those limits
///   are the guarantee below which the function will not panic, and not the guarantee above which
///   the function will panic.
///   # Errors
///   Returns an error if `len` is invalid. The error kind is [`Length`] and the [position] is the
///   greatest valid input length.
pub exec fn encoding_decode_len(
    bit: usize,
    has_pad: bool,
    has_ignore: bool,
    len: usize,
) -> (r: Result<usize, DecodeError>)
    requires
        1 <= bit <= 6,
        (len as int) <= usize::MAX as int / 8,
    ensures
        ({
            let (ilen, olen) = decode_wrap_len_spec(bit as int, has_pad, len as int);
            ((has_ignore || ilen == len as int) ==> r == Result::Ok(olen as usize))
                && (!has_ignore && ilen != len as int ==> r == Result::Err(
                    DecodeError { position: ilen as usize, kind: DecodeKind::Length },
                ))
        }),
{
    let (ilen, olen) = decode_wrap_len(bit, has_pad, len);
    if !has_ignore && ilen != len {
        return Result::Err(DecodeError { position: ilen, kind: DecodeKind::Length });
    }
    Result::Ok(olen)
}

/// Origin: lib.rs:1327-1335 `Encoding::encode_len(&self, len)`
///   assert!(len <= usize::MAX / 512) public panic contract + after the dispatch! static dispatch
///   encode_wrap_len (this layer's duty isomorphic to encoding_encode_align)
/// Upstream doc (lib.rs:1305-1325):
///   Returns the encoded length of an input of length `len`
///   See [`encode_mut`] for when to use it.
///   # Panics
///   May panic if `len` is greater than `usize::MAX / 512`:
///   - `len <= 8_388_607` when `target_pointer_width = "32"`
///   - `len <= 36028_797018_963967` when `target_pointer_width = "64"`
///   If you need to encode an input of length greater than this limit (possibly of infinite
///   length), then you must chunk your input, encode each chunk, and concatenate to obtain the
///   output. The length of each input chunk must be a multiple of [`encode_align`].
///   Note that this function only _may_ panic in those cases. The function may also return the
///   correct value in some cases depending on the implementation. In other words, those limits
///   are the guarantee below which the function will not panic, and not the guarantee above which
///   the function will panic.
pub exec fn encoding_encode_len(
    bit: usize,
    pad: Option<u8>,
    wrap: Option<(usize, &[u8])>,
    len: usize,
) -> (r: usize)
    requires
        1 <= bit <= 6,
        (len as int) <= usize::MAX as int / 512,
        wrap.is_some() ==> {
            let (col, end) = wrap.get_Some_0();
            0 < (col as int)
                && (col as int) % dec_of_bit_spec(bit as int) == 0
                && encode_pad_len_spec(bit as int, pad.is_some(), len as int)
                    + col as int <= usize::MAX as int
                && (end@.len() as int)
                    * div_ceil_spec(
                        encode_pad_len_spec(bit as int, pad.is_some(), len as int),
                        col as int,
                    )
                    + encode_pad_len_spec(bit as int, pad.is_some(), len as int)
                    <= usize::MAX as int
        },
    ensures
        (r as int) == ({
            let base = encode_pad_len_spec(bit as int, pad.is_some(), len as int);
            if wrap.is_none() {
                base
            } else {
                let (col, end) = wrap.get_Some_0();
                base + (end@.len() as int) * div_ceil_spec(base, col as int)
            }
        }),
{
    let olen = encode_pad_len(bit, pad, len);
    match wrap {
        None => olen,
        Some((col, end)) => {
            let add = div_ceil(olen, col);
            let head = end.len() * add;
            olen + head
        }
    }
}

/// Origin: lib.rs:1343-1349 `Encoding::encode_align(&self)` (wrap-parameterized)
/// Upstream doc (lib.rs:1337-1341):
///   Returns the minimum alignment when chunking a long input
///   See [`encode_len`] for context.
pub exec fn encoding_encode_align(bit: usize, wrap: Option<(usize, &[u8])>) -> (r: usize)
    requires
        1 <= bit <= 6,
        wrap.is_some() ==> {
            let (col, end) = wrap.get_Some_0();
            0 < (col as int)
                && (col as int) % dec_of_bit_spec(bit as int) == 0
                && (col as int) * (bit as int) <= usize::MAX as int
        },
    ensures
        wrap.is_none() ==> (r as int) == enc_of_bit_spec(bit as int),
        wrap.is_some() ==> (r as int)
            == wrap.get_Some_0().0 as int * (bit as int) / 8,
{
    match wrap {
        None => enc_of_bit(bit),
        Some((col, _)) => col * bit / 8,
    }
}

/// Origin: lib.rs:1655-1657 `Encoding::bit_width(&self)`
/// Upstream doc (lib.rs:1653-1653):
///   Returns the bit-width
pub exec fn bit_width(bit: usize) -> (r: usize)
    requires 1 <= bit <= 6
    ensures r == bit
{
    bit
}

/// Origin: lib.rs:1562-1564 `Encoding::decode_align(&self)
///   = dec(self.bit())`
/// Upstream doc (lib.rs:1556-1560):
///   Returns the minimum alignment when chunking a long input
///   See [`decode_len`] for context.
pub exec fn decode_align(bit: usize) -> (r: usize)
    requires 1 <= bit <= 6
    ensures (r as int) == dec_of_bit_spec(bit as int)
{
    let d = dec_of_bit(bit);
    d
}

/* ============================================================
 * HEXLOWER / HEXUPPER family (bit=4, msb, no pad/wrap/ignore)
 * Origin: lib.rs:349-479 encode/decode algorithms + lib.rs:2032-2215 static tables;
 * the table lookups are transcribed per ledger 3 into interval logic (the equivalence
 * is fully witnessed at runtime against the upstream pin tree)
 * ============================================================ */

/// Origin: the HEXLOWER/HEXUPPER `_IMPL` tables (sentinel INVALID=128, i.e. the lib.rs:342 constant)

/// Digit values (Specifications "0123456789abcdef" / "...ABCDEF", bit=4 => value domain [0,16))
pub open spec fn hex_val(c: u8, upper: bool) -> u8 {
    if 0x30 <= c && c <= 0x39 {
        ((c as int) - 0x30) as u8
    } else if upper && 0x41 <= c && c <= 0x46 {
        ((c as int) - 0x41 + 10) as u8
    } else if !upper && 0x61 <= c && c <= 0x66 {
        ((c as int) - 0x61 + 10) as u8
    } else {
        INVALID
    }
}

/// Digit value => symbol character
pub open spec fn hex_sym(v: u8, upper: bool) -> u8 {
    if v < 10 {
        (0x30 + v as int) as u8
    } else if upper {
        (0x41 + ((v as int) - 10)) as u8
    } else {
        (0x61 + ((v as int) - 10)) as u8
    }
}

/// Encoding sequence model (bit=4, msb: byte i => symbol pair (2i, 2i+1))
pub open spec fn encode_seq(s: Seq<u8>, upper: bool) -> Seq<u8> {
    Seq::new(
        2 * s.len(),
        |j: int| if j % 2 == 0 {
            hex_sym((s[j / 2] / 16) as u8, upper)
        } else {
            hex_sym((s[j / 2] % 16) as u8, upper)
        },
    )
}

/// Decoding sequence model (even-length input; byte i <- pairs (2i, 2i+1))
pub open spec fn decode_seq(s: Seq<u8>, upper: bool) -> Seq<u8> {
    Seq::new(s.len() / 2, |i: int| ((hex_val(s[2 * i], upper) as int) * 16
        + hex_val(s[2 * i + 1], upper) as int) as u8)
}

/// Index of the first invalid byte (-1 = all valid); byte granularity, mirroring the upstream
/// "consume sequentially, short-circuit return at the first invalid byte" execution order (the j order inside decode_block, lib.rs:420-423)
pub open spec fn first_invalid(s: Seq<u8>, upper: bool) -> int {
    first_invalid_from(s, upper, 0)
}

pub open spec fn first_invalid_from(s: Seq<u8>, upper: bool, from: int) -> int
    decreases s.len() - from
{
    if from >= s.len() {
        -1
    } else if hex_val(s[from], upper) == INVALID {
        from
    } else {
        first_invalid_from(s, upper, from + 1)
    }
}

/// Equivalent description of the first invalid byte of an offset suffix (for the decode_mut contracts)
pub open spec fn valid_all_until(s: Seq<u8>, upper: bool, until: int) -> bool {
    forall|j: int| 0 <= j < until ==> hex_val(s[j], upper) != INVALID
}

/* ---------- exec lookups (interval logic; Origin: see ledger 3) ---------- */

/// Origin: lib.rs:188-190 `set(&mut values, *symbols, v)?` + the HEXLOWER/HEXUPPER
/// 256-byte literal table's val segment -> equivalent interval logic
pub exec fn hex_value(c: u8, upper: bool) -> (r: u8)
    ensures
        r == hex_val(c, upper),
        r != INVALID ==> r < 16,
{
    if 0x30 <= c && c <= 0x39 {
        c - 0x30
    } else if !upper && 0x61 <= c && c <= 0x66 {
        c - 0x61 + 10
    } else if upper && 0x41 <= c && c <= 0x46 {
        c - 0x41 + 10
    } else {
        INVALID
    }
}

/// Origin: the HEXLOWER/HEXUPPER 256-byte sym table segment (16 repeats) -> equivalent interval logic
pub exec fn hex_symbol(v: u8, upper: bool) -> (r: u8)
    requires v < 16
    ensures r == hex_sym(v, upper)
{
    if v < 10 {
        0x30 + v
    } else if upper {
        0x41 + (v - 10)
    } else {
        0x61 + (v - 10)
    }
}

/* ---------- encode side (Origin: lib.rs:373-408 + 1494-1510) ---------- */

/// Origin: lib.rs:373-388 `fn encode_block::<B,M>(bit, msb, symbols, input, output)`
/// bit=4/msb monomorphization; `input.len() <= enc(bit) = 1` (the debug_assert domain) => at most 1 iteration,
/// the loop is unfolded into a conditional per the bound (iteration order kept: collect input first, then scatter output)
pub exec fn encode_block_hex(input: &[u8], output: &mut [u8], upper: bool)
    requires
        input.len() <= 1,
        output.len() == 2 * input.len(),
    ensures
        input.len() == 0 ==> final(output)@ == Seq::<u8>::empty(),
        input.len() == 1 ==> final(output)@ [0] == hex_sym((input[0] / 16) as u8, upper)
            && final(output)@ [1] == hex_sym((input[0] % 16) as u8, upper),
{
    /* Origin Rust: let mut x = 0u64;
       for (i, input) in input.iter().enumerate() {
           x |= u64::from(*input) << (8 * order(msb, enc(bit), i)); }
       -- with the bit=4 monomorphization enc(bit)=1, so the loop runs at most 1
       iteration (the upstream debug_assert!(input.len() <= enc(bit.val())) domain),
       and the shift 8*order(msb=true, 1, 0) == 0, hence x == u64::from(input[0]);
       unfolded here into the equivalent direct access under that constant domain (semantics unchanged). */
    /* Origin Rust: for (i, output) in output.iter_mut().enumerate() {
           let y = x >> (bit * order(msb, dec(bit), i));
           *output = symbols[(y & 0xff) as usize]; }
       -- under bit=4/msb the shifts are 4*order(2,0)=4 and 4*order(2,1)=0;
       the upstream 256-byte sym table is the 16-byte alphabet repeated 16 times
       (built by the lib.rs:1986-1988 encoding.extend_from_slice repetition); the lookup
       result only takes the (y & 0x0f) bits, rewritten equivalently as the interval-logic query of ledger 3. */
    if output.len() == 2 {
        let b = input[0];
        let s0 = (b / 16) as u8;
        let s1 = (b % 16) as u8;
        proof {
            assert(s0 < 16 && s1 < 16);
        }
        output[0] = hex_symbol(s0, upper);
        output[1] = hex_symbol(s1, upper);
    }
}

/// Upstream doc (lib.rs:1351-1369):
///   Encodes `input` in `output`
///   # Panics
///   Panics if the `output` length does not match the result of [`encode_len`] for the `input`
///   length.
pub exec fn encode_mut_hex(input: &[u8], output: &mut [u8], upper: bool)
    requires
        output.len() == 2 * input.len(),
        input.len() <= usize::MAX / 2,
    ensures ({ let out_final = final(output)@;
        forall|j: int| 0 <= j < out_final.len() ==> out_final[j]
            == encode_seq(input@, upper)[j] })
{
    let ghost s = input@;
    let mut i: usize = 0;
    while i < input.len()
        invariant
            0 <= i <= input@.len(),
            s == input@,
            output@.len() == 2 * input@.len(),
            forall|j: int| 0 <= j < 2 * (i as int) ==> output@ [j]
                == encode_seq(s, upper)[j],
        decreases input.len() - i
    {
        proof {
            assert(i < input.len());
            assert(2 * i + 2 <= output.len());
        }
        let blk_in = &input[i..i + 1];
        let blk_out = &mut output[2 * i..2 * i + 2];
        encode_block_hex(blk_in, blk_out, upper);
        proof {
            assert(blk_in@ == s.subrange(i as int, i as int + 1));
            assert(blk_out@ == output@.subrange(2 * i as int, 2 * i as int + 2));
            let b = s[i as int];
            assert(blk_out@[0] == hex_sym((b / 16) as u8, upper));
            assert(blk_out@[1] == hex_sym((b % 16) as u8, upper));
            assert(encode_seq(s, upper)[2 * i as int] == hex_sym((b / 16) as u8, upper));
            assert(encode_seq(s, upper)[2 * i as int + 1] == hex_sym((b % 16) as u8, upper));
            assert forall|j: int| 0 <= j < 2 * (i as int + 1) implies output@ [j]
                == encode_seq(s, upper)[j] by {
                if 0 <= j < 2 * i as int {
                } else if j == 2 * i as int {
                    let b = s[i as int];
                    assert(encode_seq(s, upper)[j] == hex_sym((b / 16) as u8, upper));
                } else {
                    let b = s[i as int];
                    assert(encode_seq(s, upper)[j] == hex_sym((b % 16) as u8, upper));
                }
            }
        }
        i += 1;
    }
    proof {
        assert(i == input@.len());
        assert(output@.len() == 2 * s.len());
        assert(encode_seq(s, upper).len() == output@.len());
    }
}

/// Origin: lib.rs:1502-1510 `Encoding::encode(&self, input) -> String`
/// (the alloc face per ledger 5: returns a Vec<u8> byte string; the consistency of
///  String::from_utf8_unchecked is carried by the ASCII prior lemma_hex_output_ascii)
/// Upstream doc (lib.rs:1494-1501):
///   Returns encoded `input`
pub exec fn encode_hex(input: &[u8], upper: bool) -> (r: Vec<u8>)
    ensures
        r@ == encode_seq(input@, upper),
        r@.len() == 2 * input@.len(),
{
    let mut out: Vec<u8> = Vec::new();
    let ghost s = input@;
    let mut i: usize = 0;
    while i < input.len()
        invariant
            0 <= i <= input@.len(),
            s == input@,
            out@.len() == 2 * i,
            forall|j: int| 0 <= j < out@.len() ==> out@ [j]
                == encode_seq(s, upper)[j],
        decreases input.len() - i
    {
        proof {
            assert(encode_seq(s, upper).len() == 2 * s.len());
            let b = s[i as int];
            assert(encode_seq(s, upper)[2 * i as int] == hex_sym((b / 16) as u8, upper));
            assert(encode_seq(s, upper)[2 * i as int + 1] == hex_sym((b % 16) as u8, upper));
        }
        let hi = hex_symbol((input[i] / 16) as u8, upper);
        let lo = hex_symbol((input[i] % 16) as u8, upper);
        out.push(hi);
        out.push(lo);
        i += 1;
    }
    proof {
        assert(i == input@.len());
        assert(out@.len() == 2 * s.len());
        assert(encode_seq(s, upper).len() == out@.len());
    }
    out
}

/// All encode output is ASCII (the precondition for String::from_utf8_unchecked, the
/// spec carrier of the upstream safety_assert!(output.is_ascii()))
pub open spec fn hex_output_ascii(s: Seq<u8>, upper: bool) -> bool {
    forall|j: int| 0 <= j < encode_seq(s, upper).len() ==> encode_seq(s, upper)[j] < 0x80
}

/* ---------- decode side (Origin: lib.rs:412-448, 594-607) ---------- */

/// Origin: lib.rs:412-429 `fn decode_block::<B,M>(bit, msb, values, input, output)`
/// -> Result<(), usize>; bit=4/msb monomorphization; the input block dec(bit)=2 bytes, the output 1 byte;
/// the loop bound enc(bit)=1 => at most 1 scatter
pub exec fn decode_block_hex(input: &[u8], output: &mut [u8], upper: bool)
    -> (r: Result<(), usize>)
    requires
        input.len() == 2,
        output.len() == 1,
    ensures
        ({
            let v0 = hex_val(input[0], upper);
            let v1 = hex_val(input[1], upper);
            (v0 == INVALID ==> r == Result::Err(0))
                && (v0 != INVALID && v1 == INVALID ==> r == Result::Err(1))
                && (v0 != INVALID && v1 != INVALID ==> (r == Result::Ok(())
                    && final(output)@ [0] == ((v0 as int) * 16 + (v1 as int)) as u8))
        })
{
    /* Origin Rust: let mut x = 0u64; for j in 0..input.len() {
       let y = values[input[j] as usize]; check!(j, y < 1 << bit);
       x |= u64::from(y) << (bit * order(msb, dec(bit), j)); }
       -- bit=4/msb monomorphization: the supervision order j=0,1 (the check! macro expands to
       an if-return, lib.rs:165-171/421-423); x's boxed bit packing is equivalent to
       y0*16 + y1 in the monomorphized domain (0 <= y0,y1 < 16 => <= 255, no truncation), unfolded here. */
    let y0 = hex_value(input[0], upper);
    if y0 >= 16 {
        proof { let c0 = input[0]; assert(hex_val(c0, upper) == INVALID); }
        return Result::Err(0);
    }
    let y1 = hex_value(input[1], upper);
    if y1 >= 16 {
        proof { let c1 = input[1]; assert(hex_val(c1, upper) == INVALID); }
        return Result::Err(1);
    }
    /* Origin Rust: for (j, output) in output.iter_mut().enumerate() {
       *output = ((x >> (8 * order(msb, enc(bit), j))) & 0xff) as u8; }
       -- enc(bit)=1, j only takes 0: *output = (x & 0xff) as u8 == y0*16+y1 */
    proof {
        assert(y0 < 16 && y1 < 16);
        assert((y0 as int) * 16 + (y1 as int) <= 255);
        let c0 = input[0];
        let c1 = input[1];
        assert(hex_val(c0, upper) == y0);
        assert(hex_val(c1, upper) == y1);
    }
    let byte = y0 * 16 + y1;
    proof {
        assert(byte == ((y0 as int) * 16 + (y1 as int)) as u8);
    }
    output[0] = byte;
    Result::Ok(())
}

pub exec fn decode_mut_hex(
    input: &[u8],
    output: &mut [u8],
    upper: bool,
) -> (r: Result<(), usize>)
    requires
        input.len() == 2 * output.len(),
    ensures
        ({ let out_final = final(output)@;
            (first_invalid(input@, upper) == -1 ==> (r.is_Ok()
                && forall|j: int| 0 <= j < out_final.len() ==> out_final[j]
                    == decode_seq(input@, upper)[j])) }),
        (first_invalid(input@, upper) != -1 ==> r == Result::Err(
            first_invalid(input@, upper) as usize,
        )),
        (r.is_Ok() ==> valid_all_until(input@, upper, input@.len() as int))
{
    let ghost s = input@;
    let mut i: usize = 0;
    while i < output.len()
        invariant
            0 <= i <= output@.len(),
            s == input@,
            input@.len() == 2 * output@.len(),
            forall|j: int| 0 <= j < 2 * (i as int) ==> hex_val(s[j], upper) != INVALID,
            forall|j: int| 0 <= j < (i as int) ==> output@ [j]
                == decode_seq(s, upper)[j],
        decreases output.len() - i
    {
        proof {
            assert(i < output.len());
            assert(2 * i + 2 <= input.len());
        }
        let blk_in = &input[2 * i..2 * i + 2];
        let blk_out = &mut output[i..i + 1];
        match decode_block_hex(blk_in, blk_out, upper) {
            Result::Ok(()) => {
                proof {
                    assert(blk_in@ == s.subrange(2 * i as int, 2 * i as int + 2));
                    let v0 = hex_val(s[2 * i as int], upper);
                    let v1 = hex_val(s[2 * i as int + 1], upper);
                    assert(v0 != INVALID && v1 != INVALID);
                    assert(v0 < 16 && v1 < 16);
                    assert(blk_out@[0] == ((v0 as int) * 16 + v1 as int) as u8);
                    assert(decode_seq(s, upper)[i as int]
                        == ((v0 as int) * 16 + v1 as int) as u8);
                    assert(output@[i as int] == blk_out@[0]);
                    assert forall|j: int| 0 <= j <= i as int implies output@ [j]
                        == decode_seq(s, upper)[j] by {}
                }
                i += 1;
            }
            Result::Err(e) => {
                proof {
                    first_invalid_range(s, upper);
                    let bad = 2 * i as int + e as int;
                    assert(0 <= bad < s.len());
                    assert forall|j: int| 0 <= j < bad implies hex_val(s[j], upper) != INVALID by {}
                    if e == 0 {
                        assert(hex_val(s[bad], upper) == INVALID);
                        lip_exact(s, upper, bad);
                    } else {
                        assert(hex_val(s[bad], upper) == INVALID);
                        lip_exact(s, upper, bad);
                    }
                    assert(first_invalid(s, upper) == bad);
                }
                return Result::Err(2 * i + e);
            }
        }
    }
    proof {
        assert(i == output@.len());
        assert forall|j: int| 0 <= j < input@.len() implies hex_val(s[j], upper) != INVALID by {
            assert(2 * i as int == s.len());
        }
        lip_none(s, upper, 0);
        assert(first_invalid(s, upper) == -1);
        assert forall|j: int| 0 <= j < output@.len() implies output@ [j]
            == decode_seq(s, upper)[j] by {
            assert(0 <= j < i as int);
        }
    }
    Result::Ok(())
}

/* ---------- Common decoding entries (Origin: lib.rs:604-682 decode chain + 1645-1651
 * Encoding::decode) ---------- */

/// Origin: lib.rs:594-607 `fn decode_base_mut::<B,M>(bit, msb, ctb, values, input, output)`
///   -> Result<usize, DecodePartial>; bit=4 monomorphization: 8 % 4 == 0 => check_trail
/// is always Ok (the lib.rs:454-456 8 % bit.val() == 0 early exit), the decoding order = decode_mut
/// Upstream doc (lib.rs:1566-1602):
///   Decodes `input` in `output`
///   Returns the length of the decoded output. This length may be smaller than the output length
///   if the input contained padding or ignored characters. The output bytes after the returned
///   length are not initialized and should not be read.
///   # Panics
///   Panics if the `output` length does not match the result of [`decode_len`] for the `input`
///   length. Also panics if `decode_len` fails for the `input` length.
///   # Errors
///   Returns an error if `input` is invalid. See [`decode`] for more details. The are two
///   differences though:
///   - [`Length`] may be returned only if the encoding allows ignored characters, because
///   otherwise this is already checked by [`decode_len`].
///   - The [`read`] first bytes of the input have been successfully decoded to the [`written`]
///   first bytes of the output.
pub exec fn decode_base_mut_hex(
    input: &[u8],
    output: &mut [u8],
    upper: bool,
) -> (r: Result<usize, DecodePartial>)
    requires
        input.len() == 2 * output.len(),
        input.len() <= usize::MAX / 2,
    ensures
        ({
            let fi = first_invalid(input@, upper);
            (fi == -1 ==> (r.is_Ok()
                // the return value is written == output.len() == input.len()/2 (requires)
                && r.get_Ok_0() == input.len() / 2))
                && (fi != -1 ==> r == Result::Err(DecodePartial {
                    read: (fi / 2 * 2) as usize,
                    written: (fi / 2) as usize,
                    error: DecodeError { position: fi as usize, kind: DecodeKind::Symbol },
                }))
        })
{
    /* The element-level contract is carried by decode_mut_hex (this function is its
       up-layer: check_trail is always Ok at bit=4 (the lib.rs:454-456 8 % bit == 0 early
       exit), no pad => the upstream chain's decode_base_mut map_err only rebuilds read/written, the element output unchanged) */
    proof { first_invalid_range(input@, upper); }
    let olen = output.len();
    match decode_mut_hex(input, output, upper) {
        Result::Ok(()) => {
            proof {
                let fi = first_invalid(input@, upper);
                assert(fi == -1);
                assert(olen == input.len() / 2);
            }
            Result::Ok(olen)
        }
        Result::Err(pos) => {
            proof {
                let fi = first_invalid(input@, upper);
                assert(fi != -1);
                assert((pos as int) == fi);
                assert(pos / 2 * 2 == (fi / 2 * 2) as usize);
                assert(pos / 2 == (fi / 2) as usize);
            }
            Result::Err(DecodePartial {
                read: pos / 2 * 2,
                written: pos / 2,
                // Origin Rust: map_err(|pos| fail(pos, DecodeKind::Symbol)) (lib.rs:603)
                error: DecodeError { position: pos, kind: DecodeKind::Symbol },
            })
        }
    }
}

/// Origin: lib.rs:1645-1651 `Encoding::decode(&self, input) -> Result<Vec<u8>, DecodeError>`
///  (static-table bit=4 with no pad/wrap/ignore semantics; decode_len first -> Length;
///   the alloc face builds incrementally with Vec push per ledger 5)
/// The error order is the upstream public contract (lib.rs:1620-1631): Length (invalid len)
/// before Symbol (first invalid character); Trailing/Padding are unreachable at bit=4 (8%4==0, no padding).
/// Upstream doc (lib.rs:1616-1644):
///   Returns decoded `input`
///   # Errors
///   Returns an error if `input` is invalid. The error kind can be:
///   - [`Length`] if the input length is invalid. The [position] is the greatest valid input
///   length.
///   - [`Symbol`] if the input contains an invalid character. The [position] is the first invalid
///   character.
///   - [`Trailing`] if the input has non-zero trailing bits. This is only possible if the
///   encoding checks trailing bits. The [position] is the first character containing non-zero
///   trailing bits.
///   - [`Padding`] if the input has an invalid padding length. This is only possible if the
///   encoding uses padding. The [position] is the first padding character of the first padding
///   of invalid length.
pub exec fn decode_hex(input: &[u8], upper: bool) -> (r: Result<Vec<u8>, DecodeError>)
    ensures
        ({
            let s = input@;
            let fi = first_invalid(s, upper);
            (s.len() % 2 != 0 ==> r == Result::Err(DecodeError {
                position: (s.len() - 1) as usize,
                kind: DecodeKind::Length,
            }))
                && (s.len() % 2 == 0 && fi == -1 ==> (r.is_Ok()
                    && r.get_Ok_0()@.len() == s.len() / 2
                    && forall|j: int| 0 <= j < s.len() / 2 ==> r.get_Ok_0()@ [j]
                        == decode_seq(s, upper)[j]))
                && (s.len() % 2 == 0 && fi != -1 ==> r == Result::Err(DecodeError {
                    position: fi as usize,
                    kind: DecodeKind::Symbol,
                }))
        })
{
    /* Origin Rust: let mut output = vec![0u8; self.decode_len(input.len())?];
       -- the decode_len parity check (decode_wrap_len(4,false,len)'s ilen != len
       being exactly the odd lengths) comes first, returning Length(position = ilen) */
    let ghost s = input@;
    if input.len() % 2 != 0 {
        proof { decode_len_odd_positions(s); }
        return Result::Err(DecodeError {
            position: input.len() - 1,
            kind: DecodeKind::Length,
        });
    }
    /* Origin Rust: let len = self.decode_mut(input, &mut output)
       .map_err(|partial| partial.error)?;
       output.truncate(len); */
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < input.len() / 2
        invariant
            0 <= i <= input@.len() / 2,
            s == input@,
            input@.len() % 2 == 0,
            out@.len() == i,
            forall|j: int| 0 <= j < 2 * (i as int) ==> hex_val(s[j], upper) != INVALID,
            forall|j: int| 0 <= j < (i as int) ==> out@ [j]
                == decode_seq(s, upper)[j],
        decreases input@.len() / 2 - i
    {
        proof {
            assert(2 * i + 2 <= input.len());
            assert(i + 1 <= input.len() / 2);
        }
        let blk: [u8; 2] = [input[2 * i], input[2 * i + 1]];
        let mut b: [u8; 1] = [0];
        match decode_block_hex(&blk, &mut b, upper) {
            Result::Ok(()) => {
                proof {
                    assert(blk@.len() == 2);
                    assert(blk@[0] == s[2 * i as int]);
                    assert(blk@[1] == s[2 * i as int + 1]);
                    let v0 = hex_val(s[2 * i as int], upper);
                    let v1 = hex_val(s[2 * i as int + 1], upper);
                    assert(v0 != INVALID && v1 != INVALID);
                    assert(b[0] == ((v0 as int) * 16 + v1 as int) as u8);
                    assert(decode_seq(s, upper)[i as int]
                        == ((v0 as int) * 16 + v1 as int) as u8);
                    assert(b[0] == decode_seq(s, upper)[i as int]);
                }
                out.push(b[0]);
                i += 1;
            }
            Result::Err(e) => {
                proof {
                    first_invalid_range(s, upper);
                    let bad = 2 * i as int + e as int;
                    assert(0 <= bad < s.len());
                    assert forall|j: int| 0 <= j < bad implies hex_val(s[j], upper) != INVALID by {}
                    lip_exact(s, upper, bad);
                    assert(first_invalid(s, upper) == bad);
                }
                return Result::Err(DecodeError {
                    position: (2 * i + e) as usize,
                    kind: DecodeKind::Symbol,
                });
            }
        }
    }
    proof {
        assert(i == input@.len() / 2);
        assert forall|j: int| 0 <= j < s.len() implies hex_val(s[j], upper) != INVALID by {
            assert(2 * i as int == s.len());
        }
        lip_none(s, upper, 0);
        assert(first_invalid(s, upper) == -1);
    }
    Result::Ok(out)
}


// ===========================================================================
// Proof lemmas (the enc/dec constant table, the first_invalid / encode_seq
// model bridges, and the decode_len parity facts)
// ===========================================================================
/// The enc/dec constant table (an isolated small-lookup proof, avoiding the SMT branch
/// burden inside big functions; the content is the upstream dispatch! constant dispatch N1..N6, lib.rs:216-242)
pub proof fn lemma_enc_dec_constants(bit: int)
    requires 1 <= bit <= 6
    ensures
        bit == 1 ==> enc_of_bit_spec(bit) == 1 && dec_of_bit_spec(bit) == 8,
        bit == 2 ==> enc_of_bit_spec(bit) == 1 && dec_of_bit_spec(bit) == 4,
        bit == 3 ==> enc_of_bit_spec(bit) == 3 && dec_of_bit_spec(bit) == 8,
        bit == 4 ==> enc_of_bit_spec(bit) == 1 && dec_of_bit_spec(bit) == 2,
        bit == 5 ==> enc_of_bit_spec(bit) == 5 && dec_of_bit_spec(bit) == 8,
        bit == 6 ==> enc_of_bit_spec(bit) == 3 && dec_of_bit_spec(bit) == 4,
{
    assert(bit == 1 || bit == 2 || bit == 3 || bit == 4 || bit == 5 || bit == 6);
}

/// The first `until` bytes all valid and the `until`-th invalid => first_invalid is exactly until
pub proof fn lip_exact(s: Seq<u8>, upper: bool, j: int)
    requires
        0 <= j < s.len(),
        valid_all_until(s, upper, j),
        hex_val(s[j], upper) == INVALID,
    ensures first_invalid(s, upper) == j
{
    first_invalid_from_unfold(s, upper, 0, j);
}

pub proof fn first_invalid_from_unfold(s: Seq<u8>, upper: bool, from: int, j: int)
    requires
        0 <= from <= j < s.len(),
        valid_all_until(s, upper, j),
        hex_val(s[j], upper) == INVALID,
    ensures first_invalid_from(s, upper, from) == j
    decreases j - from
{
    if from == j {
    } else {
        assert(hex_val(s[from], upper) != INVALID);
        first_invalid_from_unfold(s, upper, from + 1, j);
    }
}

/// All valid => first_invalid == -1 (equivalent form: the suffix from any start is all valid)
pub proof fn lip_none(s: Seq<u8>, upper: bool, k: int)
    requires
        0 <= k <= s.len(),
        valid_all_until(s, upper, s.len() as int),
    ensures first_invalid_from(s, upper, k) == -1
    decreases s.len() - k
{
    if k >= s.len() {
    } else {
        assert(hex_val(s[k], upper) != INVALID);
        lip_none(s, upper, k + 1);
    }
}

/// Every byte of the encode output is a valid symbol (the precondition for decode(encode(x)) never raising a Symbol error)
pub proof fn lemma_encode_bytes_valid(s: Seq<u8>, upper: bool)
    requires forall|j: int| 0 <= j < s.len() ==> s[j] <= 255
    ensures forall|j: int| 0 <= j < encode_seq(s, upper).len() ==> hex_val(
        encode_seq(s, upper)[j],
        upper,
    ) != INVALID
{
    let e = encode_seq(s, upper);
    assert(e.len() == 2 * s.len());
    assert forall|j: int| 0 <= j < e.len() implies hex_val(e[j], upper) != INVALID by {
        if j % 2 == 0 {
            let b = s[j / 2];
            assert(e[j] == hex_sym((b / 16) as u8, upper));
            let nib = (b / 16) as u8;
            assert(nib < 16);
            if nib < 10 {
                assert(hex_sym(nib, upper) == 0x30 + nib);
                assert(0x30 <= hex_sym(nib, upper) <= 0x39);
            } else if upper {
                assert(hex_sym(nib, upper) == 0x41 + (nib - 10));
                assert(0x41 <= hex_sym(nib, upper) <= 0x46);
            } else {
                assert(0x61 <= hex_sym(nib, upper) <= 0x66);
            }
        } else {
            let b = s[j / 2];
            assert(e[j] == hex_sym((b % 16) as u8, upper));
            let nib = (b % 16) as u8;
            assert(nib < 16);
            if nib < 10 {
                assert(0x30 <= hex_sym(nib, upper) <= 0x39);
            } else if upper {
                assert(0x41 <= hex_sym(nib, upper) <= 0x46);
            } else {
                assert(0x61 <= hex_sym(nib, upper) <= 0x66);
            }
        }
    }
}

/// Prefix-seam corollary of encode_seq (the well-founded cornerstone of the decode-after-encode readback)
pub proof fn lemma_encode_seq_concat(s: Seq<u8>, upper: bool, k: int)
    requires 0 <= k <= s.len()
    ensures encode_seq(s.subrange(0, k as int), upper) == encode_seq(s, upper).subrange(
        0,
        2 * k as int,
    )
{
    assert(s.subrange(0, k).len() == k);
    assert(encode_seq(s.subrange(0, k), upper).len() == 2 * s.subrange(0, k).len());
    assert(encode_seq(s, upper).len() == 2 * s.len());
    assert(encode_seq(s.subrange(0, k), upper).len() == 2 * k);
    assert(encode_seq(s, upper).subrange(0, 2 * k).len() == 2 * k);
    assert forall|j: int| 0 <= j < 2 * k implies
        encode_seq(s.subrange(0, k), upper)[j]
            == encode_seq(s, upper).subrange(0, 2 * k)[j] by {
        let p = s.subrange(0, k);
        if j % 2 == 0 {
            assert(p[j / 2] == s[j / 2]);
        } else {
            assert(p[j / 2] == s[j / 2]);
        }
    }
}

pub proof fn lemma_hex_output_ascii(s: Seq<u8>, upper: bool)
    ensures hex_output_ascii(s, upper)
{
    assert(encode_seq(s, upper).len() == 2 * s.len());
    assert forall|j: int| 0 <= j < encode_seq(s, upper).len() implies
        encode_seq(s, upper)[j] < 0x80 by {
        encode_sym_ascii(s[j / 2] as int / 16, upper);
        encode_sym_ascii(s[j / 2] as int % 16, upper);
    }
}

pub proof fn encode_sym_ascii(v: int, upper: bool)
    requires 0 <= v <= 255
{
    if 0x30 <= v && v <= 0x39 {
    } else if v < 10 {
        assert(v <= 9 && 0x30 + v <= 0x39);
    } else if v <= 15 {
    } else {
    }
}

pub proof fn first_invalid_range(s: Seq<u8>, upper: bool)
    requires 0 <= s.len()
    ensures
        first_invalid(s, upper) == -1
            || (0 <= first_invalid(s, upper) < s.len()),
{
    first_invalid_from_range(s, upper, 0);
}

pub proof fn first_invalid_from_range(s: Seq<u8>, upper: bool, from: int)
    requires 0 <= from <= s.len()
    ensures
        first_invalid_from(s, upper, from) == -1
            || (from <= first_invalid_from(s, upper, from) < s.len()),
    decreases s.len() - from
{
    if from >= s.len() {
    } else if hex_val(s[from], upper) == INVALID {
        assert(first_invalid_from(s, upper, from) == from);
    } else {
        assert(first_invalid_from(s, upper, from) == first_invalid_from(s, upper, from + 1));
        first_invalid_from_range(s, upper, from + 1);
    }
}

/// decode_len odd length => position == len - 1 (the bit=4 special case of the upstream "greatest valid input length")
pub proof fn decode_len_odd_positions(s: Seq<u8>)
    ensures
        s.len() % 2 != 0 ==> (decode_wrap_len_spec(4, false, s.len() as int).0
            == s.len() - 1),
{
    if s.len() % 2 == 1 {
        assert(s.len() == 2 * (s.len() / 2) + 1);
        assert(4 * s.len() % 8 == 4);
        assert((s.len() as int) - (4 * s.len() as int % 8) / 4
            == s.len() as int - 1);
    }
}
}
