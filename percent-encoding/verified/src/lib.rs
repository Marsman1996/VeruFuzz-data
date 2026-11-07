//! `percent-encoding` crate mirror
//!
//! Upstream: https://github.com/servo/rust-url (pin 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a)
//! crate root at `code/percent_encoding/` (SUBDIR=percent_encoding; code/ tree untouched)
//! This file is the same-name mirror of `src/lib.rs` (the percent_encode_byte table, the
//! PercentEncode/PercentDecode iterator family, and the percent_encode/utf8_percent_encode/
//! percent_decode/percent_decode_str entry points).
//!
//! Mirror and relaxation ledger (KVerus relax criteria):
//! 1. `percent_encode_byte` (lib.rs:73-97) is upstream a 768-byte static literal table
//!    ENC_TABLE + `unsafe str::from_utf8_unchecked` slicing to return `&'static str`. Verus
//!    supports neither literal-str table indexing nor that unsafe; the mirror *computes* the
//!    same mathematical semantics ('%' + two uppercase hex digits) and returns `[u8; 3]` (relax:
//!    the return type changes from `&'static str` to a fixed 3-byte array; the byte-content
//!    contract = the upstream table entries). The bytewise full equivalence of table vs
//!    computation is confirmed by a runtime 256x3-entry matrix comparison.
//! 2. `PercentEncode` (lib.rs:141-209): iterator + `Display` + `From<Cow<str>>`.
//!    `next()` (split_first + the remaining scan + the split_at(1+i) token split) and the
//!    fmt/alloc layer are outside the verus support surface (`&str` slices, fmt::Formatter,
//!    Cow); the mirror converts the collect semantics into a recursive span (`enc_span_exec`)
//!    -- the per-byte decision matches upstream verbatim (the should_percent_encode branch is
//!    copied word for word; the verbatim grouping of non-escaped runs is equivalent under ==
//!    collect concatenation semantics), only the token assembly (memcpy grouping) is relaxed
//!    to Vec pushes. `Display`/`Cow::from` are outside the verus surface; their output
//!    contract (= concatenation of per-byte tokens) is verified at span level.
//! 3. `PercentDecode` (lib.rs:248-333): iterator + `if_any`/`decode_utf8`/
//!    `decode_utf8_lossy`: likewise mirrored as a recursive span (`dec_span_exec`); the branch
//!    decisions of the greedy `%XY` decode match the upstream `after_percent_sign` verbatim
//!    (the acceptance face of char::from().to_digit(16) is mixed-case hexadecimal)
//!    (`hex_val`/`hex_val_exec`). `to_digit` is expanded per Rust semantics into an explicit
//!    range check (Origin comments). `decode_utf8`/`decode_utf8_lossy` (the std layer of
//!    str::from_utf8 / String::from_utf8_lossy) and the `Cow::from` borrow face are outside
//!    the verus surface; the two-sided bounds of `size_hint` are generically verified per the
//!    std::iter::Iterator contract (harness/coverage_props.rs).
//! 4. The `static ENC_TABLE` literal table and the `#[cfg]`/cfg_attr face are not translated.
//! 5. The same verus engineering pitfalls as in ascii_set.rs apply (quantified asserts
//!    always live at module level; quantified asserts inside exec bodies advance in
//!    small steps via empty by-blocks).
//!
//! Consumption: this file has no fn main; KVerus drives it via harness files; the files
//! under harness/ reference this module's work via `#[path]` and must not copy its spec.

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "ascii_set.rs"]
mod ascii_set;

pub use self::ascii_set::{
    add_bit_spec, bit_at, is_alnum, lemma_added_list_concrete, lemma_add_membership, lemma_controls,
    lemma_empty_members, lemma_remove_membership, non_alphanumeric, remove_bit_spec,
    should_encode, AsciiSet, CONTROLS,
};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ============================================================
 * Hex digit model (the expansion face of char::to_digit(16))
 * Origin: lib.rs:254-255 `char::from(*cloned_iter.next()?).to_digit(16)?`
 * ============================================================ */

/// Acceptance face and values of Rust `char::to_digit(16)` ('0'..='9' -> 0..=9,
/// 'a'..='f' / 'A'..='F' -> 10..=15; otherwise -1).
pub open spec fn hex_val(c: int) -> int {
    if 0x30 <= c <= 0x39 {
        c - 0x30
    } else if 0x41 <= c <= 0x46 {
        c - 0x41 + 10
    } else if 0x61 <= c <= 0x66 {
        c - 0x61 + 10
    } else {
        -1
    }
}

/// Uppercase hex byte (the mathematical form of the upstream ENC_TABLE entries:
/// 0..=9 -> '0'+d, 10..=15 -> 'A'+d-10).
pub open spec fn hex_char_upper(d: int) -> u8
    recommends
        0 <= d <= 15,
{
    if 0 <= d && d <= 9 {
        (0x30 + d) as u8
    } else {
        (0x41 + (d - 10)) as u8
    }
}

/// Origin: lib.rs:80-97, the table-entry content of percent_encode_byte `"%{:02X}"`:
/// '%' + high-digit uppercase hex byte + low-digit uppercase hex byte.
pub open spec fn enc_byte_spec(b: u8) -> Seq<u8> {
    seq![0x25, hex_char_upper((b as int) / 16), hex_char_upper((b as int) % 16)]
}

/// Exec companion of hex_char_upper: d in [0,15] is panic-free and equals the spec.
pub exec fn hex_char_upper_exec(d: u8) -> (c: u8)
    requires
        (d as int) <= 15,
    ensures
        c == hex_char_upper(d as int),
{
    if d <= 9 {
        0x30 + d
    } else {
        0x41 + (d - 10)
    }
}

/* ============================================================
 * percent_encode_byte (Origin: lib.rs:60-97)
 * ============================================================ */

/// Origin: lib.rs:73-97
/// `pub fn percent_encode_byte(byte: u8) -> &'static str`
/// relax (ledger item 1): returns `[u8; 3]` (= the byte content of the upstream &str);
/// the upstream `ENC_TABLE[byte*3 .. byte*3+3]` table indexing becomes a computed implementation.
/// Upstream doc (lib.rs:60-62):
///   Return the percent-encoding of the given byte.
///   This is unconditional, unlike `percent_encode()` which has an `AsciiSet` parameter.
pub exec fn percent_encode_byte(b: u8) -> (t: [u8; 3])
    ensures
        t@ == enc_byte_spec(b),
{
    /* Origin Rust: let index = usize::from(byte) * 3;
     *              unsafe { str::from_utf8_unchecked(&ENC_TABLE[index..index + 3]) } */
    let hi = hex_char_upper_exec((b / 16) as u8);
    let lo = hex_char_upper_exec((b % 16) as u8);
    [0x25, hi, lo]
}

/* ============================================================
 * percent_encode semantics (Origin: lib.rs:99-138 + 141-209)
 * ============================================================ */

/// enc span: the percent-encode output of the input remainder from position start
/// (per byte: '%'+two hex digits if should_encode, otherwise the byte verbatim).
pub open spec fn enc_span(s: Seq<u8>, start: int, mask: Seq<u32>) -> Seq<u8>
    recommends
        0 <= start <= s.len(),
    decreases
        s.len() - start,
{
    if start >= s.len() {
        Seq::empty()
    } else {
        let b = s[start];
        let rest = enc_span(s, start + 1, mask);
        if should_encode(mask, b as int) {
            enc_byte_spec(b) + rest
        } else {
            seq![b] + rest
        }
    }
}

/// Whole-input encode spec: the output model of percent_encode / utf8_percent_encode.
pub open spec fn enc_seq(s: Seq<u8>, mask: Seq<u32>) -> Seq<u8> {
    enc_span(s, 0, mask)
}

/// Origin: lib.rs:117 `pub fn percent_encode<'a>(input, ascii_set) -> PercentEncode<'a>`
/// relax (ledger item 2): the PercentEncode iterator + collect semantics is mirrored as a recursive span.
/// Upstream doc (lib.rs:140-140):
///   The return type of [`percent_encode`] and [`utf8_percent_encode`].
pub exec fn enc_span_exec(s: &[u8], start: usize, set: &AsciiSet) -> (v: Vec<u8>)
    requires
        start <= s.len(),
    ensures
        v@ == enc_span(s@, start as int, set.mask@),
    decreases
        s.len() - start,
{
    if start == s.len() {
        Vec::new()
    } else {
        let b = s[start];
        /* Origin Rust: if self.ascii_set.should_percent_encode(first_byte) {
         *   Some(percent_encode_byte(first_byte)) } else { unchanged run } */
        let mut out = Vec::new();
        if set.should_percent_encode(b) {
            let t = percent_encode_byte(b);
            out.push(t[0]);
            out.push(t[1]);
            out.push(t[2]);
            assert(out@ == enc_byte_spec(b));
        } else {
            out.push(b);
            assert(out@ == seq![b]);
        }
        let rest = enc_span_exec(s, start + 1, set);
        /* Origin Rust: token concatenation of the iterator collect (relaxed to byte-wise pushes) */
        let mut i: usize = 0;
        let ghost token = out@;
        let ghost restv = rest@;
        while i < rest.len()
            invariant
                restv == rest@,
                0 <= i <= restv.len(),
                out@ == token + restv.subrange(0, i as int),
            decreases
                rest.len() - i
        {
            let x = rest[i];
            proof {
                assert(i < restv.len());
                assert(restv[i as int] == x);
                let lhs = restv.subrange(0, (i + 1) as int);
                let rhs = restv.subrange(0, i as int) + seq![x];
                assert(lhs.len() == rhs.len());
                assert forall|j: int| 0 <= j < lhs.len() implies lhs[j] == rhs[j] by {
                    if (j as int) < i as int {
                        assert(lhs[j] == restv[j]);
                        assert(rhs[j] == restv[j]);
                    } else {
                        assert(j == i as int);
                        assert(lhs[j] == x);
                        assert(rhs[j] == x);
                    }
                };
                assert(out@.push(x) == (token + restv.subrange(0, i as int)).push(x));
                assert((token + restv.subrange(0, i as int)).push(x)
                    == token + (restv.subrange(0, i as int)).push(x));
                assert(token + rhs == out@.push(x));
            }
            out.push(x);
            i += 1;
        }
        proof {
            assert(restv.subrange(0, restv.len() as int) == restv);
        }
        assert(out@ == token + restv);
        out
    }
}

/// Origin: lib.rs:116-122, the collect-total of percent_encode (same-shape delegation).
/// Upstream doc (lib.rs:99-107):
///   Percent-encode the given bytes with the given set.
///   Non-ASCII bytes and bytes in `ascii_set` are encoded.
///   The return type:
///   * Implements `Iterator<Item = &str>` and therefore has a `.collect::<String>()` method,
///   * Implements `Display` and therefore has a `.to_string()` method,
///   * Implements `Into<Cow<str>>` borrowing `input` when none of its bytes are encoded.
pub exec fn enc_all_bytes(s: &[u8], set: &AsciiSet) -> (v: Vec<u8>)
    ensures
        v@ == enc_seq(s@, set.mask@),
{
    enc_span_exec(s, 0, set)
}

/// Origin: lib.rs:136 `pub fn utf8_percent_encode<'a>(input: &str, ascii_set)`
/// The one-line delegation `percent_encode(input.as_bytes(), ascii_set)` copied verbatim.
/// Upstream doc (lib.rs:124-126):
///   Percent-encode the UTF-8 encoding of the given string.
///   See [`percent_encode`] regarding the return type.
pub exec fn utf8_percent_encode_bytes(s: &[u8], set: &AsciiSet) -> (v: Vec<u8>)
    ensures
        v@ == enc_seq(s@, set.mask@),
{
    /* Origin Rust: percent_encode(input.as_bytes(), ascii_set) */
    enc_all_bytes(s, set)
}

/* ============================================================
 * percent_decode semantics (Origin: lib.rs:211-333)
 * ============================================================ */

/// dec span: the greedy percent-decode output from position start
/// (the three-byte `%XY` decode (XY mixed-case hexadecimal), otherwise the single byte verbatim).
pub open spec fn dec_span(s: Seq<u8>, start: int) -> Seq<u8>
    recommends
        0 <= start <= s.len(),
    decreases
        s.len() - start,
{
    if start >= s.len() {
        Seq::empty()
    } else if s[start] == 0x25 && start + 2 < s.len()
        && hex_val(s[start + 1] as int) >= 0 && hex_val(s[start + 2] as int) >= 0
    {
        seq![((hex_val(s[start + 1] as int) * 16 + hex_val(s[start + 2] as int)) % 256) as u8]
            + dec_span(s, start + 3)
    } else {
        seq![s[start]] + dec_span(s, start + 1)
    }
}

/// Whole-input decode spec: the output model of percent_decode / percent_decode_str.
pub open spec fn dec_seq(s: Seq<u8>) -> Seq<u8> {
    dec_span(s, 0)
}

/// Origin: lib.rs:252-258, the character-decision face of `after_percent_sign`:
/// the verus expansion of `char::from(c).to_digit(16)` (Option form).
exec fn hex_val_exec(c: u8) -> (d: Option<u8>)
    ensures
        match d {
            Option::Some(v) => v as int == hex_val(c as int),
            Option::None => hex_val(c as int) < 0,
        },
{
    /* Origin Rust: char::from(*cloned_iter.next()?).to_digit(16)? */
    if c >= 0x30 && c <= 0x39 {
        Option::Some(c - 0x30)
    } else if c >= 0x41 && c <= 0x46 {
        Option::Some(c - 0x41 + 10)
    } else if c >= 0x61 && c <= 0x66 {
        Option::Some(c - 0x61 + 10)
    } else {
        Option::None
    }
}

/// Origin: lib.rs:252-258, the pair decision of `after_percent_sign`:
/// Some((h,l) values) when both h and l are hex digits, otherwise None.
exec fn sync_hex_pair(hc: u8, lc: u8) -> (r: Option<(u8, u8)>)
    ensures
        match r {
            Option::Some((h, l)) => {
                (h as int) == hex_val(hc as int) && (l as int) == hex_val(lc as int)
                    && hex_val(hc as int) >= 0 && hex_val(lc as int) >= 0
            }
            Option::None => hex_val(hc as int) < 0 || hex_val(lc as int) < 0,
        },
{
    let h = hex_val_exec(hc);
    let l = hex_val_exec(lc);
    match h {
        Option::Some(hv) => match l {
            Option::Some(lv) => {
                proof {
                    assert((hv as int) == hex_val(hc as int));
                    assert((lv as int) == hex_val(lc as int));
                }
                Option::Some((hv, lv))
            }
            Option::None => {
                proof {
                    assert((hv as int) == hex_val(hc as int));
                }
                Option::None
            }
        },
        Option::None => Option::None,
    }
}

/// Origin: lib.rs:240 `pub fn percent_decode(input: &[u8]) -> PercentDecode<'_>`
/// relax (ledger item 3): the PercentDecode iterator + collect semantics is mirrored as a recursive span.
/// Upstream doc (lib.rs:246-246):
///   The return type of [`percent_decode`].
pub exec fn dec_span_exec(s: &[u8], start: usize) -> (v: Vec<u8>)
    requires
        start <= s.len(),
    ensures
        v@ == dec_span(s@, start as int),
    decreases
        s.len() - start,
{
    if start == s.len() {
        Vec::new()
    } else {
        let b = s[start];
        /* Origin Rust: if byte == b'%' {
         *   after_percent_sign(&mut self.bytes).unwrap_or(byte) } else { byte } */
        let mut out = Vec::new();
        let mut skip: usize = start + 1;
        let mut wrote_escape: bool = false;
        if b == 0x25 && s.len() - start >= 3 {
            /* Origin Rust: after_percent_sign(&mut self.bytes).unwrap_or(byte) */
            let pair = sync_hex_pair(s[start + 1], s[start + 2]);
            match pair {
                Option::Some((hv, lv)) => {
                    /* Origin Rust: Some(h as u8 * 0x10 + l as u8) */
                    proof {
                        assert(hex_val(s[start + 1] as int) == hv as int);
                        assert(hex_val(s[start + 2] as int) == lv as int);
                        lemma_hex_val_range(s[start + 1] as int);
                        lemma_hex_val_range(s[start + 2] as int);
                        assert(hv < 16);
                        assert(lv < 16);
                    }
                    out.push((hv * 0x10) + lv);
                    assert(out@ == seq![((hex_val(s[start + 1] as int) * 16
                        + hex_val(s[start + 2] as int)) % 256) as u8]);
                    skip = start + 3;
                    wrote_escape = true;
                }
                Option::None => {
                }
            }
        }
        if !wrote_escape {
            out.push(b);
            assert(out@ == seq![b]);
        }
        let rest = dec_span_exec(s, skip);
        /* Origin Rust: token concatenation of the iterator collect (relaxed to byte-wise pushes) */
        let mut i: usize = 0;
        let ghost token = out@;
        let ghost restv = rest@;
        while i < rest.len()
            invariant
                restv == rest@,
                0 <= i <= restv.len(),
                out@ == token + restv.subrange(0, i as int),
            decreases
                rest.len() - i
        {
            let x = rest[i];
            proof {
                assert(i < restv.len());
                assert(restv[i as int] == x);
                let lhs = restv.subrange(0, (i + 1) as int);
                let rhs = restv.subrange(0, i as int) + seq![x];
                assert(lhs.len() == rhs.len());
                assert forall|j: int| 0 <= j < lhs.len() implies lhs[j] == rhs[j] by {
                    if (j as int) < i as int {
                        assert(lhs[j] == restv[j]);
                        assert(rhs[j] == restv[j]);
                    } else {
                        assert(j == i as int);
                        assert(lhs[j] == x);
                        assert(rhs[j] == x);
                    }
                };
                assert(out@.push(x) == (token + restv.subrange(0, i as int)).push(x));
                assert((token + restv.subrange(0, i as int)).push(x)
                    == token + (restv.subrange(0, i as int)).push(x));
                assert(token + rhs == out@.push(x));
            }
            out.push(x);
            i += 1;
        }
        proof {
            assert(restv.subrange(0, restv.len() as int) == restv);
        }
        assert(out@ == token + restv);
        out
    }
}

/// Origin: lib.rs:216-219, the percent_decode_str form (countable delegation).
/// Upstream doc (lib.rs:211-215):
///   Percent-decode the given string.
///   <https://url.spec.whatwg.org/#string-percent-decode>
///   See [`percent_decode`] regarding the return type.
pub exec fn dec_all_bytes(s: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == dec_seq(s@),
{
    dec_span_exec(s, 0)
}


// =========================================================================
// Proof lemma -- the standalone proof fn lives at the end of the file so
// the exec pipeline reads directly; the signature and contract are untouched.
// measured: all five verification panels identical before and after the move.
/// hex_val range: -1..=15.
pub proof fn lemma_hex_val_range(c: int)
    ensures
        -1 <= hex_val(c) <= 15,
{
}


}
