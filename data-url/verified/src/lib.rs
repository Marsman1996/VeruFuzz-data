//! data-url 0.3.2 @ servo/rust-url 00a6ce58; the crate root module.
//! Upstream source: data-url/src/lib.rs (pin tree code/data-url/src/lib.rs).
//! This file mirrors that upstream module, src zone (the library code proper):
//! the data-url processor (pretend_parse_data_url, find_comma_before_fragment,
//! parse_header, remove_base64_suffix, percent_encode, the decode arm) plus
//! the DataUrl / FragmentIdentifier faces. The crate doc example
//! (lib.rs:5-15) is transcribed in verified/harness/ut_lib.rs; the in-file
//! upstream UT of the mime module is transcribed in verified/harness/ut_mime.rs.
//! Carrier note: upstream inputs are &str with String/Slice faces; the byte
//! carrier &[u8] with Seq<u8> views is used throughout (vstd has no String
//! spec), and a subslice carries Seq::new semantics matching slice_seq. The
//! streaming decode writer `F: FnMut(&[u8]) -> Result<(), E>` is blocked for
//! quantification in this build (the same probeD closure evidence as the
//! forgiving_base64 carrier note): every decode face instantiates the writer
//! at the concrete `out: &mut Vec<u8>` accumulator, which is exactly the
//! upstream decode_to_vec face. Display-for-Mime and the Result-to-String
//! faces are carried by mime::serialize_bytes and local byte serializers.
//! Domain narrowing: inputs are ASCII (all bytes < 0x80) and bounded below
//! 18446744073709551615 (parser range bounds); char-based upstream faces (trim over
//! chars, `ch <= ' '`) coincide with the byte face there, and the narrowing
//! only restricts the declared domain, never widens a contract.

use vstd::prelude::*;
use vstd::seq::Seq;

pub mod mime;  // upstream lib.rs declares pub (verified copy had it
// crate-private; pub restores the upstream surface and lets harness files
// reference mime spec machines through the lib module)
pub mod forgiving_base64;

verus! {

// ================= Section A: spec model =================

/// the case-insensitive scheme target "data:" (lib.rs:167-171)
pub open spec fn scheme_byte(k: int) -> u8 {
    if k == 0 { 0x64 } else if k == 1 { 0x61 } else if k == 2 { 0x74 }
    else if k == 3 { 0x61 } else { 0x3A }
}

pub open spec fn ic_ascii(b: u8, target: u8) -> bool {
    b == target || (b >= 0x41 && b <= 0x5A && (b + 0x20) as u8 == target)
        || (b >= 0x61 && b <= 0x7A && (b - 0x20) as u8 == target)
}

/// Origin Rust: input.trim_start_matches(|ch| ch <= ' ') (lib.rs:159):
/// trim C0 control or space on the byte face.
pub open spec fn c0_or_space(b: u8) -> bool {
    b <= 0x20
}

pub open spec fn ltrim_c0(s: Seq<u8>, i: int, b0: int) -> int
    decreases b0 - i
{
    if i < b0 && c0_or_space(s[i]) { ltrim_c0(s, i + 1, b0) } else { i }
}

pub open spec fn rtrim_c0(s: Seq<u8>, hi: int, lo: int) -> int
    decreases hi - lo
{
    if hi > lo && c0_or_space(s[hi - 1]) { rtrim_c0(s, hi - 1, lo) } else { hi }
}

/// Origin Rust: the "data:" match over the whitespace-filtered byte stream
/// (lib.rs:163-172), as a left-to-right scan: \t, \n and \r are skipped
/// (the URL parser would ignore them), the five scheme bytes match
/// case-insensitively in order. Returns the position after ':' or -1.
pub open spec fn scheme_scan(s: Seq<u8>, pos: int, k: int, b0: int) -> int
    decreases b0 - pos
{
    if pos >= b0 {
        -1
    } else if k == 5 {
        pos
    } else if s[pos] == 0x09 || s[pos] == 0x0A || s[pos] == 0x0D {
        scheme_scan(s, pos + 1, k, b0)
    } else if ic_ascii(s[pos], scheme_byte(k)) {
        scheme_scan(s, pos + 1, k + 1, b0)
    } else {
        -1
    }
}

/// Origin Rust: pretend_parse_data_url (lib.rs:157-178): after trimming C0
/// control or space on both ends, the scheme scan decides data-URL-ness.
/// Returns Some((after_colon, trimmed_end)) or None.
pub open spec fn pretend_parse_spec(s: Seq<u8>) -> Option<(int, int)> {
    let n = s.len() as int;
    let lo = ltrim_c0(s, 0, n);
    let c = scheme_scan(s, lo, 0, n);
    if c < 0 {
        None
    } else {
        Some((c, rtrim_c0(s, n, c)))
    }
}

/// Origin Rust: find_comma_before_fragment (lib.rs:180-190): the first ','
/// before the first '#'. Returns its position or -1.
pub open spec fn comma_scan(s: Seq<u8>, i: int, b0: int) -> int
    decreases b0 - i
{
    if i >= b0 {
        -1
    } else if s[i] == 0x2C {
        i
    } else if s[i] == 0x23 {
        -1
    } else {
        comma_scan(s, i + 1, b0)
    }
}

/// Origin Rust: remove_base64_suffix (lib.rs:245-265): the reversed match of
/// the ";base64" suffix over the \t-\n-\r-filtered stream (the filter skips
/// them), then the skip_while(' ') run, then the ';' (lib.rs:262). Scanning
/// right-to-left within [lo, b0): k is the number of target bytes matched so
/// far (right-to-left target: '4','6','e','s','a','b', case-insensitive but
/// the digits exact), then k == 6 skips spaces, k == 7 expects ';'.
/// Returns the position of that ';' (the exclusive upper bound of the prefix)
/// or -1.
pub open spec fn b64tail_scan(s: Seq<u8>, pos: int, k: int, lo: int, b0: int) -> int
    recommends 0 <= lo && lo - 1 <= pos && pos < b0 && 0 <= k && k <= 6
    decreases pos - lo + 1
{
    if pos < lo {
        -1
    } else if k == 7 {
        pos
    } else if s[pos] == 0x09 || s[pos] == 0x0A || s[pos] == 0x0D {
        b64tail_scan(s, pos - 1, k, lo, b0)
    } else if k == 0 && s[pos] == 0x34 {
        b64tail_scan(s, pos - 1, 1, lo, b0)
    } else if k == 1 && s[pos] == 0x36 {
        b64tail_scan(s, pos - 1, 2, lo, b0)
    } else if k == 2 && (s[pos] == 0x45 || s[pos] == 0x65) {
        b64tail_scan(s, pos - 1, 3, lo, b0)
    } else if k == 3 && (s[pos] == 0x73 || s[pos] == 0x53) {
        b64tail_scan(s, pos - 1, 4, lo, b0)
    } else if k == 4 && (s[pos] == 0x61 || s[pos] == 0x41) {
        b64tail_scan(s, pos - 1, 5, lo, b0)
    } else if k == 5 && (s[pos] == 0x62 || s[pos] == 0x42) {
        b64tail_scan(s, pos - 1, 6, lo, b0)
    } else if k == 6 {
        if s[pos] == 0x20 {
            b64tail_scan(s, pos - 1, 6, lo, b0)
        } else if s[pos] == 0x3B {
            pos
        } else {
            -1
        }
    } else {
        -1
    }
}

/// the uppercase-hex digit of nibble d (percent_encode, lib.rs:268-272)
pub open spec fn hex_upper(d: int) -> u8 {
    if d <= 9 { (0x30 + d) as u8 } else { (0x37 + d) as u8 }
}

/// Origin Rust: fn percent_encode(byte: u8, string: &mut String) (lib.rs:267-272)
pub open spec fn pct_enc(b: u8) -> Seq<u8> {
    seq![0x25, hex_upper(b as int / 16), hex_upper(b as int % 16)]
}

/// Origin Rust: char::to_digit(16): '0'-'9', 'a'-'f', 'A'-'F'
pub open spec fn hex_val(b: u8) -> int {
    if b >= 0x30 && b <= 0x39 { b as int - 0x30 }
    else if b >= 0x41 && b <= 0x46 { b as int - 0x41 + 10 }
    else if b >= 0x61 && b <= 0x66 { b as int - 0x61 + 10 }
    else { -1 }
}

/// Origin Rust: the header re-encoding loop (lib.rs:203-230): C0 controls and
/// DEL-and-above always percent-encode, ' ', '"', '<', '>' percent-encode only
/// in the query state, '?' switches the query state, \t, \n, \r are ignored,
/// everything else is passed through. inq is the query state.
pub open spec fn header_enc(s: Seq<u8>, pos: int, b0: int, inq: bool) -> Seq<u8>
    decreases b0 - pos
{
    if pos >= b0 {
        Seq::empty()
    } else {
        let b = s[pos];
        let tail = header_enc(
            s,
            pos + 1,
            b0,
            if b == 0x3F { true } else { inq },
        );
        if b == 0x09 || b == 0x0A || b == 0x0D {
            tail
        } else if b <= 0x1F || b >= 0x7F {
            pct_enc(b) + tail
        } else if (b == 0x20 || b == 0x22 || b == 0x3C || b == 0x3E) && inq {
            pct_enc(b) + tail
        } else {
            seq![b] + tail
        }
    }
}

/// the byte payload "text/plain" (lib.rs:204-206)
pub open spec fn text_plain() -> Seq<u8> {
    seq![0x74, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E]
}

/// the fallback mime of parse_header (lib.rs:234-238)
pub open spec fn default_mime_triple() -> (Seq<u8>, Seq<u8>, Seq<(Seq<u8>, Seq<u8>)>) {
    (
        seq![0x74, 0x65, 0x78, 0x74],
        seq![0x70, 0x6C, 0x61, 0x69, 0x6E],
        seq![(seq![0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74],
            seq![0x55, 0x53, 0x2D, 0x41, 0x53, 0x43, 0x49, 0x49])],
    )
}

/// Origin Rust: fn parse_header(from_colon_to_comma: &str) (lib.rs:192-241):
/// trim HTTP whitespace, remove the base64 suffix, re-encode the remaining
/// header, prepend "text/plain" when it starts with ';', then parse it as a
/// MIME type with the text/plain;charset=US-ASCII fallback (lib.rs:232-238).
/// Returns (mime triple, base64 flag).
pub open spec fn header_spec(s: Seq<u8>, a: int, b: int)
    -> ((Seq<u8>, Seq<u8>, Seq<(Seq<u8>, Seq<u8>)>), bool) {
    let a1 = mime::ltrim(s, a, b);
    let b1 = mime::rtrim(s, a1, b);
    let u = b64tail_scan(s, b1 - 1, 0, a1, b1);
    let (am, is64) = if u >= 0 { (u, true) } else { (b1, false) };
    let out0 = if a1 < am && s[a1] == 0x3B { text_plain() } else { Seq::empty() };
    let encoded = out0 + header_enc(s, a1, am, false);
    let parsed = mime::mime_parse_spec(encoded);
    let triple = match parsed {
        Option::Some(t) => t,
        Option::None => default_mime_triple(),
    };
    (triple, is64)
}

/// Origin Rust: the whole DataUrl::process pipeline (lib.rs:69-87):
/// Some((mime triple, base64 flag, body start, body end)) or None for
/// NotADataUrl / NoComma.
pub open spec fn data_url_spec(s: Seq<u8>)
    -> Option<((Seq<u8>, Seq<u8>, Seq<(Seq<u8>, Seq<u8>)>), bool, int, int)> {
    match pretend_parse_spec(s) {
        Option::None => None,
        Option::Some((blo, bhi)) => {
            let cm = comma_scan(s, blo, bhi);
            if cm < 0 {
                None
            } else {
                let hdr = header_spec(s, blo, cm);
                Some((hdr.0, hdr.1, cm + 1, bhi))
            }
        }
    }
}

/// Origin Rust: decode_without_base64 (lib.rs:282-331): percent-decode with
/// mixed-case hex pairs, skip \t, \n, \r, stop at the first '#' (the fragment
/// starts after it). Returns (fragment start position, decoded output).
pub open spec fn body_dec_spec(s: Seq<u8>, pos: int, b0: int) -> (int, Seq<u8>)
    decreases b0 - pos
{
    if pos >= b0 {
        (-1, Seq::empty())
    } else {
        let b = s[pos];
        if b == 0x25 && pos + 3 <= b0
            && hex_val(s[pos + 1]) >= 0 && hex_val(s[pos + 2]) >= 0
        {
            let tail = body_dec_spec(s, pos + 3, b0);
            (tail.0,
                seq![((hex_val(s[pos + 1]) * 16 + hex_val(s[pos + 2])) % 256) as u8]
                    + tail.1)
        } else if b == 0x23 {
            (pos + 1, Seq::empty())
        } else if b == 0x09 || b == 0x0A || b == 0x0D {
            body_dec_spec(s, pos + 1, b0)
        } else {
            let tail = body_dec_spec(s, pos + 1, b0);
            (tail.0, seq![b] + tail.1)
        }
    }
}

/// Origin Rust: FragmentIdentifier::to_percent_encoded (lib.rs:126-144):
/// skip \t, \n, \r; percent-encode the fragment percent-encode set
/// (C0 controls and space, '"', '<', '>', '`', DEL and above); anything
/// else passes through.
pub open spec fn frag_enc_spec(s: Seq<u8>, pos: int, b0: int) -> Seq<u8>
    decreases b0 - pos
{
    if pos >= b0 {
        Seq::empty()
    } else {
        let b = s[pos];
        let tail = frag_enc_spec(s, pos + 1, b0);
        if b == 0x09 || b == 0x0A || b == 0x0D {
            tail
        } else if b <= 0x20 || b == 0x22 || b == 0x3C || b == 0x3E || b == 0x60
            || b >= 0x7F
        {
            pct_enc(b) + tail
        } else {
            seq![b] + tail
        }
    }
}

// ================= Section B: exec transcription =================

// Carrier domain note: the reversed-scan and fragment faces pass indices as
// isize; this build's finite casts carry value identity only under a
// provable in-range precondition, so the exec faces below require the input
// length below isize::MAX (real byte payloads are far below).

/// Origin Rust: fn pretend_parse_data_url(input: &str) -> Option<&str>
/// (lib.rs:157-178); the Option<&str> face is (lo, hi) bounds.
/// Transcribed as index recursions mirroring the spec scans.
pub exec fn c0_or_space_exec(b: u8) -> (r: bool)
    ensures
        r == c0_or_space(b),
{
    b <= 0x20
}

pub exec fn ic_ascii_exec(b: u8, target: u8) -> (r: bool)
    ensures
        r == ic_ascii(b, target),
{
    b == target
        || (b >= 0x41 && b <= 0x5A && b + 0x20 == target)
        || (b >= 0x61 && b <= 0x7A && b >= target && b - 0x20 == target)
}

pub exec fn ltrim_c0_exec(s: &[u8], i: usize, b0: usize) -> (r: usize)
    requires
        i <= b0 <= s.len(),
    ensures
        i <= r <= b0,
        r as int == ltrim_c0(s@, i as int, b0 as int),
    decreases b0 - i,
{
    if i < b0 && c0_or_space_exec(s[i]) {
        ltrim_c0_exec(s, i + 1, b0)
    } else {
        i
    }
}

pub exec fn rtrim_c0_exec(s: &[u8], hi: usize, lo: usize) -> (r: usize)
    requires
        lo <= hi <= s.len(),
    ensures
        lo <= r <= hi,
        r as int == rtrim_c0(s@, hi as int, lo as int),
    decreases hi - lo,
{
    if hi > lo && c0_or_space_exec(s[hi - 1]) {
        rtrim_c0_exec(s, hi - 1, lo)
    } else {
        hi
    }
}

/// Origin Rust: the "data:" letter-by-letter match over the filtered stream
/// (lib.rs:164-172), one byte per recursion.
pub exec fn scheme_scan_exec(s: &[u8], pos: usize, k: usize, b0: usize)
    -> (r: Option<usize>)
    requires
        pos <= b0 <= s.len(),
        k <= 5,
    ensures
        match r {
            Option::Some(p) => p as int == scheme_scan(s@, pos as int, k as int, b0 as int)
                && scheme_scan(s@, pos as int, k as int, b0 as int) >= 0
                && (p as int) <= b0 as int,
            Option::None => scheme_scan(s@, pos as int, k as int, b0 as int) == -1,
        },
    decreases b0 - pos,
{
    proof { reveal_with_fuel(scheme_scan, 2); }
    if pos >= b0 {
        Option::None
    } else if k == 5 {
        Option::Some(pos)
    } else if s[pos] == 0x09 || s[pos] == 0x0A || s[pos] == 0x0D {
        scheme_scan_exec(s, pos + 1, k, b0)
    } else {
        let bb = s[pos];
        if !ic_ascii_exec(bb, scheme_byte_target(k)) {
            proof {
                assert(bb == s@.index(pos as int));
                assert(!ic_ascii(s@.index(pos as int), scheme_byte(k as int)));
            }
            return Option::None;
        }
        proof {
            assert(bb == s@.index(pos as int));
            assert(ic_ascii(s@.index(pos as int), scheme_byte(k as int)));
        }
        scheme_scan_exec(s, pos + 1, k + 1, b0)
    }
}

/// exec face of scheme_byte (the "data:" target byte)
pub exec fn scheme_byte_target(k: usize) -> (r: u8)
    requires
        k <= 4,
    ensures
        r == scheme_byte(k as int),
{
    if k == 0 { 0x64 } else if k == 1 { 0x61 } else if k == 2 { 0x74 }
    else if k == 3 { 0x61 } else { 0x3A }
}

pub exec fn pretend_parse_exec(s: &[u8]) -> (r: Option<(usize, usize)>)
    requires
        s.len() < 18446744073709551615,
    ensures
        match r {
            Option::Some((lo, hi)) => match pretend_parse_spec(s@) {
                Option::Some((plo, phi)) => lo as int == plo && hi as int == phi
                    && plo <= phi && phi <= s.len() as int,
                Option::None => false,
            },
            Option::None => pretend_parse_spec(s@) == Option::None,
        },
{
    let n = s.len();
    let lo = ltrim_c0_exec(s, 0, n);
    let c = scheme_scan_exec(s, lo, 0, n);
    match c {
        Option::None => None,
        Option::Some(cpos) => {
            let hi = rtrim_c0_exec(s, n, cpos);
            Some((cpos, hi))
        }
    }
}

/// Origin Rust: fn find_comma_before_fragment(after_colon: &str)
/// (lib.rs:180-190).
pub exec fn comma_scan_exec(s: &[u8], i: usize, b0: usize) -> (r: Option<usize>)
    requires
        i <= b0 <= s.len(),
    ensures
        match r {
            Option::Some(p) => p as int == comma_scan(s@, i as int, b0 as int)
                && comma_scan(s@, i as int, b0 as int) >= 0
                && (i as int) <= (p as int)
                && (p as int) < b0 as int,
            Option::None => comma_scan(s@, i as int, b0 as int) == -1,
        },
    decreases b0 - i,
{
    proof { reveal_with_fuel(comma_scan, 2); }
    if i >= b0 {
        Option::None
    } else if s[i] == 0x2C {
        Option::Some(i)
    } else if s[i] == 0x23 {
        Option::None
    } else {
        comma_scan_exec(s, i + 1, b0)
    }
}

/// Origin Rust: fn remove_base64_suffix(s: &str) -> Option<&str>
/// (lib.rs:245-265): right-to-left index recursion mirroring b64tail_scan
/// (the reversed filtered-iterator scan transcribed as one byte per step;
/// k is the match count).
pub exec fn b64tail_scan_exec(
    s: &[u8],
    pos: usize,
    k: usize,
    lo: usize,
    b0: usize,
) -> (r: Option<usize>)
    requires
        lo <= b0 <= s.len(),
        k <= 6,
        lo <= pos,
        pos < b0,
    ensures
        match r {
            Option::Some(p) => p as int == b64tail_scan(s@, pos as int, k as int, lo as int, b0 as int)
                && b64tail_scan(s@, pos as int, k as int, lo as int, b0 as int) >= 0
                && (lo as int) <= (p as int)
                && (p as int) < b0 as int,
            Option::None => b64tail_scan(s@, pos as int, k as int, lo as int, b0 as int) == -1,
        },
    decreases pos - lo + 1,
{
    proof { reveal_with_fuel(b64tail_scan, 2); }
    if s[pos] == 0x09 || s[pos] == 0x0A || s[pos] == 0x0D {
        if pos > lo {
            b64tail_scan_exec(s, pos - 1, k, lo, b0)
        } else {
            proof {
                assert(b64tail_scan(s@, (pos - 1) as int, k as int, lo as int, b0 as int) == -1);
            }
            Option::None
        }
    } else if k == 0 && s[pos] == 0x34 {
        if pos > lo {
            b64tail_scan_exec(s, pos - 1, 1, lo, b0)
        } else {
            proof {
                assert(b64tail_scan(s@, (pos - 1) as int, 1, lo as int, b0 as int) == -1);
            }
            Option::None
        }
    } else if k == 1 && s[pos] == 0x36 {
        if pos > lo {
            b64tail_scan_exec(s, pos - 1, 2, lo, b0)
        } else {
            proof {
                assert(b64tail_scan(s@, (pos - 1) as int, 2, lo as int, b0 as int) == -1);
            }
            Option::None
        }
    } else if k == 2 && (s[pos] == 0x45 || s[pos] == 0x65) {
        if pos > lo {
            b64tail_scan_exec(s, pos - 1, 3, lo, b0)
        } else {
            proof {
                assert(b64tail_scan(s@, (pos - 1) as int, 3, lo as int, b0 as int) == -1);
            }
            Option::None
        }
    } else if k == 3 && (s[pos] == 0x73 || s[pos] == 0x53) {
        if pos > lo {
            b64tail_scan_exec(s, pos - 1, 4, lo, b0)
        } else {
            proof {
                assert(b64tail_scan(s@, (pos - 1) as int, 4, lo as int, b0 as int) == -1);
            }
            Option::None
        }
    } else if k == 4 && (s[pos] == 0x61 || s[pos] == 0x41) {
        if pos > lo {
            b64tail_scan_exec(s, pos - 1, 5, lo, b0)
        } else {
            proof {
                assert(b64tail_scan(s@, (pos - 1) as int, 5, lo as int, b0 as int) == -1);
            }
            Option::None
        }
    } else if k == 5 && (s[pos] == 0x62 || s[pos] == 0x42) {
        if pos > lo {
            b64tail_scan_exec(s, pos - 1, 6, lo, b0)
        } else {
            proof {
                assert(b64tail_scan(s@, (pos - 1) as int, 6, lo as int, b0 as int) == -1);
            }
            Option::None
        }
    } else if k == 6 {
        if s[pos] == 0x20 {
            if pos > lo {
                b64tail_scan_exec(s, pos - 1, 6, lo, b0)
            } else {
                proof {
                    assert(b64tail_scan(s@, (pos - 1) as int, 6, lo as int, b0 as int) == -1);
                }
                Option::None
            }
        } else if s[pos] == 0x3B {
            Option::Some(pos)
        } else {
            Option::None
        }
    } else {
        Option::None
    }
}

/// exec face of hex_upper (percent_encode, lib.rs:268-272)
pub exec fn hex_upper_exec(d: u8) -> (r: u8)
    requires
        d <= 15,
    ensures
        r == hex_upper(d as int),
{
    if d <= 9 { 0x30 + d } else { 0x37 + d }
}

/// Origin Rust: fn percent_encode(byte: u8, string: &mut String)
/// (lib.rs:267-272): pushes "%HH" with uppercase hex digits.
pub exec fn pct_enc_exec(b: u8, out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + pct_enc(b),
{
    let h = hex_upper_exec(b / 16);
    proof {
        assert(h == hex_upper(b as int / 16));
    }
    let l = hex_upper_exec(b % 16);
    proof {
        assert(l == hex_upper(b as int % 16));
        assert(pct_enc(b) == seq![0x25, hex_upper(b as int / 16), hex_upper(b as int % 16)]);
    }
    let ghost pre = out@;
    out.push(0x25);
    proof {
        assert(out@ == pre + seq![0x25]);
    }
    out.push(h);
    proof {
        assert(out@ == (pre + seq![0x25]) + seq![h]);
        assert(out@ == pre + seq![0x25, h]);
    }
    out.push(l);
    proof {
        assert(out@ == (pre + seq![0x25, h]) + seq![l]);
        assert(out@ == pre + seq![0x25, h, l]);
        assert(out@ == pre + pct_enc(b));
    }
}

/// Origin Rust: char::from(b).to_digit(16) (lib.rs:305-306)
pub exec fn hex_val_exec(b: u8) -> (d: Option<u8>)
    ensures
        match d {
            Option::Some(v) => v as int == hex_val(b) && hex_val(b) >= 0,
            Option::None => hex_val(b) < 0,
        },
{
    if b >= 0x30 && b <= 0x39 {
        Option::Some(b - 0x30)
    } else if b >= 0x41 && b <= 0x46 {
        Option::Some(b - 0x41 + 10)
    } else if b >= 0x61 && b <= 0x66 {
        Option::Some(b - 0x61 + 10)
    } else {
        Option::None
    }
}

/// Origin Rust: the header re-encoding loop (lib.rs:208-230) as an index
/// recursion with the concrete output accumulator.
pub exec fn header_enc_exec(
    s: &[u8],
    pos: usize,
    b0: usize,
    inq: bool,
    out: &mut Vec<u8>,
)
    requires
        pos <= b0 <= s.len(),
    ensures
        final(out)@ == old(out)@ + header_enc(s@, pos as int, b0 as int, inq),
        final(out)@.len() <= old(out)@.len() + 3 * (b0 as int - pos as int),
    decreases b0 - pos,
{
    if pos >= b0 {
    } else {
        let b = s[pos];
        let inq2 = if b == 0x3F { true } else { inq };
        proof {
            reveal_with_fuel(header_enc, 2);
        }
        if b == 0x09 || b == 0x0A || b == 0x0D {
            // Ignore ASCII tabs or newlines like the URL parser would
        } else if b <= 0x1F || b >= 0x7F {
            pct_enc_exec(b, out);
        } else if (b == 0x20 || b == 0x22 || b == 0x3C || b == 0x3E) && inq {
            pct_enc_exec(b, out);
        } else {
            let ghost pre = out@;
            out.push(b);
            proof {
                assert(out@ == pre + seq![b]);
            }
        }
        header_enc_exec(s, pos + 1, b0, inq2, out);
    }
}

/// exec face of the default mime of parse_header (lib.rs:234-238)
pub exec fn default_mime() -> (m: mime::Mime)
    ensures
        mime::mime_view_of(&m) == default_mime_triple(),
{
    let type_ = mime::sub_vec(
        &[0x74, 0x65, 0x78, 0x74],
        0,
        4,
    );
    let subtype = mime::sub_vec(
        &[0x70, 0x6C, 0x61, 0x69, 0x6E],
        0,
        5,
    );
    let charset = mime::sub_vec(
        &[0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74],
        0,
        7,
    );
    let us_ascii = mime::sub_vec(
        &[0x55, 0x53, 0x2D, 0x41, 0x53, 0x43, 0x49, 0x49],
        0,
        8,
    );
    let mut parameters: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    let ghost pv0 = mime::params_view(&parameters);
    parameters.push((charset, us_ascii));
    let m = mime::Mime { type_, subtype, parameters };
    proof {
        assert(type_@ == seq![0x74, 0x65, 0x78, 0x74]);
        assert(subtype@ == seq![0x70, 0x6C, 0x61, 0x69, 0x6E]);
        assert(mime::params_view(&m.parameters) == pv0
            + seq![(charset@, us_ascii@)]);
        assert(charset@ == seq![0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74]);
        assert(us_ascii@ == seq![0x55, 0x53, 0x2D, 0x41, 0x53, 0x43, 0x49, 0x49]);
        assert(mime::mime_view_of(&m) == default_mime_triple());
    }
    m
}

/// Origin Rust: fn parse_header(from_colon_to_comma: &str) (lib.rs:192-241).
/// The re-encoded header is always ASCII by construction (controls and bytes
/// at or above DEL percent-encode), so the MIME parse face's ASCII domain is
/// satisfied structurally.
pub exec fn parse_header_exec(s: &[u8], a: usize, b: usize)
    -> (h: (mime::Mime, bool))
    requires
        a <= b <= s.len(),
        s.len() < 1300000000,
    ensures
        (mime::mime_view_of(&h.0), h.1) == header_spec(s@, a as int, b as int),
{
    let a1 = mime::ltrim_exec(s, a, b);
    let b1 = mime::rtrim_exec(s, a1, b);
    proof {
        assert(header_spec(s@, a as int, b as int).1
            == (b64tail_scan(s@, (b1 - 1) as int, 0, a1 as int, b1 as int) >= 0));
    }
    let u = if b1 > a1 {
        b64tail_scan_exec(s, b1 - 1, 0, a1, b1)
    } else {
        proof {
            reveal_with_fuel(b64tail_scan, 2);
            assert(b64tail_scan(s@, (b1 - 1) as int, 0, a1 as int, b1 as int) == -1);
        }
        Option::None
    };
    let (am, is64) = match u {
        Option::Some(p) => (p, true),
        Option::None => (b1, false),
    };
    let mut buf: Vec<u8> = Vec::new();
    if a1 < am && s[a1] == 0x3B {
        // Origin Rust: string.push_str("text/plain") (lib.rs:204-206)
        let tpv = mime::sub_vec(
            &[0x74, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E],
            0,
            10,
        );
        proof {
            assert(buf@.len() == 0);
            assert(buf@ == Seq::empty());
            assert(tpv@ == text_plain());
        }
        mime::append_all(&tpv, &mut buf);
        proof {
            assert(buf@ == text_plain());
        }
    }
    header_enc_exec(s, a1, am, false, &mut buf);
    proof {
        let out0 = if a1 < am && s@.index(a1 as int) == 0x3B { text_plain() } else { Seq::empty() };
        if a1 < am && s@.index(a1 as int) == 0x3B {
            assert(buf@ == out0 + header_enc(s@, a1 as int, am as int, false));
        } else {
            assert(buf@ == Seq::empty() + header_enc(s@, a1 as int, am as int, false));
        }
    }
    proof {
        assert((am as int) <= s.len() as int);
        assert(((am as int) - (a1 as int)) <= s.len() as int);
        assert(((s.len()) as int) < 1300000000);
        assert(buf@.len() <= 3 * (((am as int) - (a1 as int))) + 10);
        assert(((buf@.len()) as int) <= 3900000007);
        assert(((buf@.len()) as int) < 4000000000);
    }
    let parsed = mime::parse_bytes(&buf);
    match parsed {
        Option::Some(m) => (m, is64),
        Option::None => {
            proof {
                        assert(mime::mime_parse_spec(buf@) == None);
                let hs = header_spec(s@, a as int, b as int);
                assert(hs.0 == default_mime_triple());
            }
            (default_mime(), is64)
        }
    }
}

/// Origin Rust: pub enum DataUrlError { NotADataUrl, NoComma }
/// (lib.rs:48-52); the Display/Error impls cover the message face through
/// the byte-serializer mirror below (fmt itself has no vstd spec).
pub enum DataUrlError {
    NotADataUrl,
    NoComma,
}

/// Origin Rust (lib.rs:54-64):
///     impl fmt::Display for DataUrlError {
///         Self::NotADataUrl => write!(f, "not a valid data url"),
///         Self::NoComma => write!(
///             f, "data url is missing comma delimiting attributes and body"),
///     }
/// The Display-for-DataUrlError byte face: each arm writes exactly the
/// upstream message literal, carried as slice_seq over that literal's own
/// view (a literal's view is opaque to the solver in this build, so the
/// spec arm and the exec mirror reference the SAME literal and close by
/// identity; the literals are the upstream strings verbatim).
pub open spec fn data_url_err_msg(e: &DataUrlError) -> Seq<u8> {
    match e {
        DataUrlError::NotADataUrl => mime::slice_seq(b"not a valid data url"@, 0, 20),
        DataUrlError::NoComma => mime::slice_seq(
            b"data url is missing comma delimiting attributes and body"@,
            0,
            56,
        ),
    }
}

impl DataUrlError {
    /// The Display-for-DataUrlError face as a byte serializer (fmt::Display
    /// has no vstd spec; the mirror writes the upstream message bytes).
    pub exec fn display_bytes(&self) -> (r: Vec<u8>)
        ensures
            r@ == data_url_err_msg(self),
    {
        match *self {
            DataUrlError::NotADataUrl => mime::sub_vec(b"not a valid data url", 0, 20),
            DataUrlError::NoComma => mime::sub_vec(
                b"data url is missing comma delimiting attributes and body",
                0,
                56,
            ),
        }
    }
}
// ---- The InvalidBase64 Display byte face (upstream lines 11-24, 59-66) ----
// fmt::Display has no vstd spec; the messages are carried as mime::slice_seq
// over the upstream string literals' own views (a literal's view is opaque to
// the solver in this build, so the spec arm and the exec mirror reference the
// SAME literal and close by identity; the literals are the upstream strings
// verbatim). The remaining DecodeError Display arm -- the generic write-error
// E of upstream line 62, `write!(f, "write error: {}", err)` -- stays outside
// the zone (the E face is the blocked closure/carrier face of the file-header
// note). The mirror lives here rather than in the forgiving_base64 module
// because the byte builders are the mime helpers, whose sibling module paths
// resolve from this module in the single-file builds.

/// Origin Rust (upstream forgiving_base64.rs line 64):
/// write!(f, "symbol with codepoint {} not expected", code_point) -- the
/// lowercase decimal expansion of the carried byte (u8 Display), three
/// digits at most, no leading zeros.
pub open spec fn dec_digit(t: int) -> u8 {
    if 0 <= t <= 9 { (t + 0x30) as u8 } else { 0 }
}

pub open spec fn dec_u8(b: u8) -> Seq<u8> {
    let v = b as int;
    let h = v / 100;
    let t = (v / 10) % 10;
    let o = v % 10;
    if h > 0 {
        seq![dec_digit(h), dec_digit(t), dec_digit(o)]
    } else if t > 0 {
        seq![dec_digit(t), dec_digit(o)]
    } else {
        seq![dec_digit(o)]
    }
}

/// Origin Rust (upstream forgiving_base64.rs lines 11-24): the Display of
/// InvalidBase64 over the InvalidBase64Details payload (the carrier of it
/// is forgiving_base64::B64Error):
///     UnexpectedSymbol(code_point) =>
///         write!(f, "symbol with codepoint {} not expected", code_point)
///     AlphabetSymbolAfterPadding =>
///         write!(f, "alphabet symbol present after padding")
///     LoneAlphabetSymbol => write!(f, "lone alphabet symbol present")
///     Padding => write!(f, "incorrect padding")
pub open spec fn b64_err_msg(e: &forgiving_base64::B64Error) -> Seq<u8> {
    match e {
        forgiving_base64::B64Error::UnexpectedSymbol(b) => mime::slice_seq(
            b"symbol with codepoint "@,
            0,
            22,
        ) + dec_u8(*b) + mime::slice_seq(b" not expected"@, 0, 13),
        forgiving_base64::B64Error::AlphabetSymbolAfterPadding => mime::slice_seq(
            b"alphabet symbol present after padding"@,
            0,
            37,
        ),
        forgiving_base64::B64Error::LoneAlphabetSymbol => mime::slice_seq(
            b"lone alphabet symbol present"@,
            0,
            28,
        ),
        forgiving_base64::B64Error::Padding => {
            mime::slice_seq(b"incorrect padding"@, 0, 17)
        }
    }
}

/// Origin Rust (upstream forgiving_base64.rs line 61): the DecodeError
/// blanket Display arm `Self::InvalidBase64(inner) =>
/// write!(f, "base64 not valid: {}", inner)` on the concrete-writer
/// instantiation (the WriteError arm is the blocked generic-E face).
pub open spec fn decode_err_msg(e: &forgiving_base64::B64Error) -> Seq<u8> {
    mime::slice_seq(b"base64 not valid: "@, 0, 18) + b64_err_msg(e)
}

/// exec face of dec_digit (one decimal digit byte, 0 <= t <= 9).
pub exec fn digit_byte(t: u8) -> (r: u8)
    requires
        t <= 9,
    ensures
        r == dec_digit(t as int),
{
    0x30 + t
}

impl forgiving_base64::B64Error {
    /// The InvalidBase64 Display face as a byte serializer (fmt::Display has
    /// no vstd spec; the mirror writes the upstream message bytes, the code
    /// point in its lowercase decimal expansion).
    pub exec fn display_bytes(&self) -> (r: Vec<u8>)
        ensures
            r@ == b64_err_msg(self),
    {
        match self {
            forgiving_base64::B64Error::UnexpectedSymbol(b) => {
                let bb = *b;
                let mut out: Vec<u8> = Vec::new();
                let pre = mime::sub_vec(b"symbol with codepoint ", 0, 22);
                mime::append_all(&pre, &mut out);
                proof {
                    assert(out@ == mime::slice_seq(
                        b"symbol with codepoint "@, 0, 22));
                }
                // the lowercase decimal expansion of the carried byte
                let h3 = bb / 100;
                let t2 = (bb / 10) % 10;
                let o1 = bb % 10;
                let d0 = digit_byte(h3);
                let d1 = digit_byte(t2);
                let d2 = digit_byte(o1);
                let ghost P = mime::slice_seq(b"symbol with codepoint "@, 0, 22);
                if h3 > 0 {
                    proof {
                        assert(dec_u8(bb) == seq![dec_digit(h3 as int),
                            dec_digit(t2 as int), dec_digit(o1 as int)]);
                    }
                    let ghost pre_state = out@;
                    out.push(d0);
                    proof {
                        assert(out@ == pre_state + seq![d0]);
                        assert(out@ == P + seq![dec_digit(h3 as int)]);
                    }
                    let ghost pre_state = out@;
                    out.push(d1);
                    proof {
                        assert(out@ == pre_state + seq![d1]);
                        assert(seq![dec_digit(h3 as int), dec_digit(t2 as int)]
                            == seq![dec_digit(h3 as int)] + seq![dec_digit(t2 as int)]);
                        assert(out@ == P
                            + seq![dec_digit(h3 as int), dec_digit(t2 as int)]);
                    }
                    let ghost pre_state = out@;
                    out.push(d2);
                    proof {
                        assert(out@ == pre_state + seq![d2]);
                        assert(seq![dec_digit(h3 as int), dec_digit(t2 as int),
                            dec_digit(o1 as int)]
                            == seq![dec_digit(h3 as int), dec_digit(t2 as int)]
                                + seq![dec_digit(o1 as int)]);
                        assert(out@ == P + dec_u8(bb));
                    }
                } else if t2 > 0 {
                    proof {
                        assert(dec_u8(bb) == seq![dec_digit(t2 as int),
                            dec_digit(o1 as int)]);
                    }
                    let ghost pre_state = out@;
                    out.push(d1);
                    proof {
                        assert(out@ == pre_state + seq![d1]);
                        assert(out@ == P + seq![dec_digit(t2 as int)]);
                    }
                    let ghost pre_state = out@;
                    out.push(d2);
                    proof {
                        assert(out@ == pre_state + seq![d2]);
                        assert(seq![dec_digit(t2 as int), dec_digit(o1 as int)]
                            == seq![dec_digit(t2 as int)] + seq![dec_digit(o1 as int)]);
                        assert(out@ == P + dec_u8(bb));
                    }
                } else {
                    proof {
                        assert(dec_u8(bb) == seq![dec_digit(o1 as int)]);
                    }
                    let ghost pre_state = out@;
                    out.push(d2);
                    proof {
                        assert(out@ == pre_state + seq![d2]);
                        assert(out@ == P + dec_u8(bb));
                    }
                }
                let post = mime::sub_vec(b" not expected", 0, 13);
                mime::append_all(&post, &mut out);
                proof {
                    assert(out@ == P + dec_u8(bb)
                        + mime::slice_seq(b" not expected"@, 0, 13));
                    assert(b64_err_msg(&forgiving_base64::B64Error::UnexpectedSymbol(bb))
                        == P + dec_u8(bb)
                            + mime::slice_seq(b" not expected"@, 0, 13));
                }
                out
            }
            forgiving_base64::B64Error::AlphabetSymbolAfterPadding => mime::sub_vec(
                b"alphabet symbol present after padding",
                0,
                37,
            ),
            forgiving_base64::B64Error::LoneAlphabetSymbol => mime::sub_vec(
                b"lone alphabet symbol present",
                0,
                28,
            ),
            forgiving_base64::B64Error::Padding => {
                mime::sub_vec(b"incorrect padding", 0, 17)
            }
        }
    }

    /// The DecodeError blanket arm's byte form on the concrete-writer
    /// instantiation (the "base64 not valid: " prefix + the inner message).
    pub exec fn wrapped_display_bytes(&self) -> (r: Vec<u8>)
        ensures
            r@ == decode_err_msg(self),
    {
        let mut out: Vec<u8> = Vec::new();
        let pre = mime::sub_vec(b"base64 not valid: ", 0, 18);
        mime::append_all(&pre, &mut out);
        let inner = self.display_bytes();
        mime::append_all(&inner, &mut out);
        proof {
            assert(out@ == mime::slice_seq(b"base64 not valid: "@, 0, 18)
                + b64_err_msg(self));
            assert(decode_err_msg(self) == mime::slice_seq(
                b"base64 not valid: "@, 0, 18) + b64_err_msg(self));
        }
        out
    }
}


/// Origin Rust: pub struct DataUrl<'a> (lib.rs:42-46): the borrow keeps the
/// upstream zero-copy shape on the byte carrier.
// fields pub: byte-carrier note (the spec views of process/decode read them;
// upstream keeps them private with an accessor, the byte carrier carries the
// accessors as the view functions pinned in the ensures clauses)
pub struct DataUrl<'a> {
    pub mime_type: mime::Mime,
    pub base64: bool,
    pub encoded_body_plus_fragment: &'a [u8],
}

impl<'a> DataUrl<'a> {
    /// Upstream doc (lib.rs:70-71):
    ///   <https://fetch.spec.whatwg.org/#data-url-processor>
    ///   but starting from a string rather than a parsed `Url`, to avoid extra string copies.
    pub exec fn process(input: &'a [u8])
        -> (r: Result<DataUrl<'a>, DataUrlError>)
        requires
            input.len() < 18446744073709551615,
            input.len() < 1300000000,
        ensures
            match r {
                Result::Ok(d) => match data_url_spec(input@) {
                    Option::Some((mt, is64, blo, bhi)) => {
                        mime::mime_view_of(&d.mime_type) == mt
                            && d.base64 == is64
                            && d.encoded_body_plus_fragment@.len() == bhi - blo
                            && (bhi as int) <= input.len() as int
                            && (blo as int) <= (bhi as int)
                    },
                    Option::None => false,
                },
                Result::Err(e) => match e {
                    DataUrlError::NotADataUrl => pretend_parse_spec(input@) == None,
                    DataUrlError::NoComma => match pretend_parse_spec(input@) {
                        Option::Some((plo, phi)) => {
                            comma_scan(input@, plo, phi) == -1
                        }
                        Option::None => false,
                    },
                },
            },
    {
        let pp = pretend_parse_exec(input);
        let (blo, bhi) = match pp {
            Option::Some((blo, bhi)) => (blo, bhi),
            Option::None => {
                return Result::Err(DataUrlError::NotADataUrl);
            }
        };
        proof {
            assert((blo as int) <= (bhi as int));
            assert((bhi as int) <= input.len() as int);
        }
        let cm = comma_scan_exec(input, blo, bhi);
        let cm = match cm {
            Option::Some(p) => p,
            Option::None => {
                return Result::Err(DataUrlError::NoComma);
            }
        };
        proof {
            assert((blo as int) <= (cm as int));
            assert((cm as int) < (bhi as int));
        }
        let (m, is64) = parse_header_exec(input, blo, cm);
        proof {
                assert(data_url_spec(input@) == Option::Some((
                header_spec(input@, blo as int, cm as int).0,
                header_spec(input@, blo as int, cm as int).1,
                (cm + 1) as int,
                bhi as int,
            )));
        }
        Result::Ok(DataUrl {
            mime_type: m,
            base64: is64,
            encoded_body_plus_fragment: &input[cm + 1..bhi],
        })
    }

    /// Origin Rust: pub fn mime_type(&self) -> &mime::Mime (lib.rs:89-91)
    pub exec fn mime_type(&self) -> (m: &mime::Mime)
        ensures
            mime::mime_view_of(m) == mime::mime_view_of(&self.mime_type),
    {
        &self.mime_type
    }
}

/// Origin Rust: pub struct FragmentIdentifier<'a>(&'a str) (lib.rs:124),
/// with to_percent_encoded (lib.rs:126-144): the byte carrier holds the
/// fragment slice; the serializer is the index recursion below.
pub struct FragmentIdentifier<'a> {
    pub fragment: &'a [u8],
}

/// Origin Rust: the to_percent_encoded serializer (lib.rs:128-143) as an
/// index recursion with the concrete output accumulator: skip tab/newline,
/// percent-encode the fragment percent-encode set, pass the rest through.
pub exec fn frag_enc_exec(s: &[u8], pos: usize, out: &mut Vec<u8>) -> ()
    requires
        pos <= s.len(),
    ensures
        final(out)@ == old(out)@ + frag_enc_spec(s@, pos as int, s.len() as int),
    decreases s.len() - pos,
{
    if pos >= s.len() {
    } else {
        let b = s[pos];
        let ghost pre = out@;
        proof {
            reveal_with_fuel(frag_enc_spec, 2);
        }
        if b == 0x09 || b == 0x0A || b == 0x0D {
            proof {
                assert(out@ == pre + Seq::empty());
            }
        } else if b <= 0x20 || b == 0x22 || b == 0x3C || b == 0x3E || b == 0x60
            || b >= 0x7F
        {
            pct_enc_exec(b, out);
            proof {
                assert(out@ == pre + pct_enc(b));
            }
        } else {
            out.push(b);
            proof {
                assert(out@ == pre + seq![b]);
            }
        }
        frag_enc_exec(s, pos + 1, out);
    }
}

impl FragmentIdentifier<'_> {
    /// Origin Rust: fn to_percent_encoded(&self) -> String (lib.rs:128-143)
    pub exec fn to_percent_encoded(&self) -> (v: Vec<u8>)
        ensures
            v@ == frag_enc_spec(self.fragment@, 0, self.fragment.len() as int),
    {
        let mut out: Vec<u8> = Vec::new();
        frag_enc_exec(self.fragment, 0, &mut out);
        out
    }
}

// ================= Section C: the body decode faces =================

/// Origin Rust: fn decode_without_base64 (lib.rs:282-331) as an index
/// recursion with the concrete output accumulator; the chunk-batching of
/// upstream write_by-slices is flattened to per-byte accumulation (the
/// observable output is identical). Returns the fragment start position or -1.
pub exec fn body_dec_exec(s: &[u8], pos: usize, out: &mut Vec<u8>)
    -> (frag: Option<usize>)
    requires
        pos <= s.len(),
        s.len() < 1300000000,
    ensures
        match frag {
            Option::Some(f) => f as int
                == body_dec_spec(s@, pos as int, s.len() as int).0
                && body_dec_spec(s@, pos as int, s.len() as int).0 >= 0
                && (f as int) <= s.len() as int,
            Option::None => body_dec_spec(s@, pos as int, s.len() as int).0 == -1,
        },
        final(out)@ == old(out)@ + body_dec_spec(s@, pos as int, s.len() as int).1,
    decreases s.len() - pos,
{
    if pos >= s.len() {
        proof {
            reveal_with_fuel(body_dec_spec, 2);
        }
        Option::None
    } else {
        let b = s[pos];
        if b == 0x25 && s.len() - pos >= 3 {
            let h = hex_val_exec(s[pos + 1]);
            let l = hex_val_exec(s[pos + 2]);
            match (h, l) {
                (Option::Some(hv), Option::Some(lv)) => {
                    proof {
                        reveal_with_fuel(body_dec_spec, 2);
                        assert(hex_val(s[pos + 1]) == hv as int);
                        assert(hex_val(s[pos + 2]) == lv as int);
                        assert((hv as int) < 16);
                        assert((lv as int) < 16);
                    }
                    let byte = hv * 0x10 + lv;
                    /* Origin Rust: let one_byte = h as u8 * 0x10 + l as u8; */
                    let ghost pre = out@;
                    out.push(byte);
                    proof {
                        assert(out@ == pre
                            + seq![((hex_val(s[pos + 1]) * 16
                                + hex_val(s[pos + 2])) % 256) as u8]);
                    }
                    body_dec_exec(s, pos + 3, out)
                }
                _ => {
                    // Do nothing. Leave the % sign part of the next
                    // slice: the byte passes through verbatim.
                    proof {
                        reveal_with_fuel(body_dec_spec, 2);
                        assert(body_dec_spec(s@, pos as int, s.len() as int).1
                            == seq![b]
                                + body_dec_spec(s@, (pos + 1) as int, s.len() as int).1);
                        assert(body_dec_spec(s@, pos as int, s.len() as int).0
                            == body_dec_spec(s@, (pos + 1) as int, s.len() as int).0);
                    }
                    let ghost pre = out@;
                    out.push(b);
                    proof {
                        assert(out@ == pre + seq![b]);
                    }
                    body_dec_exec(s, pos + 1, out)
                }
            }
        } else if b == 0x23 {
            // the fragment starts after '#'
            proof {
                reveal_with_fuel(body_dec_spec, 2);
                assert(out@ == old(out)@ + Seq::empty());
            }
            Option::Some(pos + 1)
        } else if b == 0x09 || b == 0x0A || b == 0x0D {
            proof {
                reveal_with_fuel(body_dec_spec, 2);
                assert(out@ == old(out)@ + Seq::empty());
            }
            body_dec_exec(s, pos + 1, out)
        } else {
            proof {
                reveal_with_fuel(body_dec_spec, 2);
            }
            let ghost pre = out@;
            out.push(b);
            proof {
                assert(out@ == pre + seq![b]);
            }
            body_dec_exec(s, pos + 1, out)
        }
    }
}

impl<'a> DataUrl<'a> {
    /// Upstream doc (lib.rs:93-94):
    ///   Streaming-decode the data URL's body to `write_body_bytes`,
    ///   and return the URL's fragment identifier if it has one.
    /// Carrier note: the streaming writer closure is the blocked face; the
    /// concrete `out` accumulator is the decode_to_vec writer face. In the
    /// base64 arm the verified whole-stream decoder runs on the internal
    /// buffer (write slices of the upstream chunking collapse into the same
    /// concatenation), so no partial output escapes on an invalid-base64
    /// error.
    pub exec fn decode(
        &self,
        out: &mut Vec<u8>,
    ) -> (r: Result<Option<FragmentIdentifier<'a>>, forgiving_base64::B64Error>)
        requires
            self.encoded_body_plus_fragment.len() < 1300000000,
        ensures
            match r {
                Result::Ok(fr) => {
                    let dec = body_dec_spec(
                        self.encoded_body_plus_fragment@,
                        0,
                        self.encoded_body_plus_fragment.len() as int,
                    );
                    if self.base64 {
                        match forgiving_base64::dec64_run(dec.1, 0, 0, 0, 0) {
                            Result::Ok(o) => {
                                final(out)@ == old(out)@ + o
                                    && (match fr {
                                        Option::Some(f) => dec.0 >= 0
                                            && f.fragment@
                                                == mime::slice_seq(
                                                    self.encoded_body_plus_fragment@,
                                                    dec.0,
                                                    self.encoded_body_plus_fragment.len() as int,
                                                ),
                                        Option::None => dec.0 == -1,
                                    })
                            }
                            Result::Err(_) => false,
                        }
                    } else {
                        final(out)@ == old(out)@ + dec.1
                            && (match fr {
                                Option::Some(f) => dec.0 >= 0
                                    && f.fragment@
                                        == mime::slice_seq(
                                            self.encoded_body_plus_fragment@,
                                            dec.0,
                                            self.encoded_body_plus_fragment.len() as int,
                                        ),
                                Option::None => dec.0 == -1,
                            })
                    }
                }
                Result::Err(e) => self.base64
                    && match forgiving_base64::dec64_run(
                        body_dec_spec(
                            self.encoded_body_plus_fragment@,
                            0,
                            self.encoded_body_plus_fragment.len() as int,
                        ).1,
                        0,
                        0,
                        0,
                        0,
                    ) {
                        Result::Ok(_) => false,
                        Result::Err((k, b)) => {
                            forgiving_base64::kind_of(e) == k
                                && (k != 0 || forgiving_base64::sym_of(e) == b)
                        }
                    }
                    && final(out)@ == old(out)@,
            },
    {
        let blen = self.encoded_body_plus_fragment.len();
        if self.base64 {
            let mut plain: Vec<u8> = Vec::new();
            let frag = body_dec_exec(self.encoded_body_plus_fragment, 0, &mut plain);
            match forgiving_base64::decode_to_vec(&plain) {
                Result::Ok(v) => {
                    let ghost pre = out@;
                    mime::append_all(&v, out);
                    proof {
                        let dec = body_dec_spec(
                            self.encoded_body_plus_fragment@,
                            0,
                            self.encoded_body_plus_fragment.len() as int,
                        );
                        assert(plain@ == dec.1);
                        assert(out@ == pre + v@);
                        let dr = forgiving_base64::dec64_run(dec.1, 0, 0, 0, 0);
                        assert(dr == forgiving_base64::dec64_run(plain@, 0, 0, 0, 0));
                        assert(match dr {
                            Result::Ok(o) => v@ == o,
                            _ => false,
                        });
                    }
                    match frag {
                        Option::Some(f) => Result::Ok(Option::Some(FragmentIdentifier {
                            fragment: &self.encoded_body_plus_fragment[f..blen],
                        })),
                        Option::None => Result::Ok(Option::None),
                    }
                }
                Result::Err(e) => {
                    proof {
                        let dec = body_dec_spec(
                            self.encoded_body_plus_fragment@,
                            0,
                            self.encoded_body_plus_fragment.len() as int,
                        );
                        assert(plain@ == dec.1);
                    }
                    Result::Err(e)
                }
            }
        } else {
            let frag = body_dec_exec(self.encoded_body_plus_fragment, 0, out);
            match frag {
                Option::Some(f) => Result::Ok(Option::Some(FragmentIdentifier {
                    fragment: &self.encoded_body_plus_fragment[f..blen],
                })),
                Option::None => Result::Ok(Option::None),
            }
        }
    }

    /// Upstream doc (lib.rs:110-111):
    ///   Return the decoded body, and the URL's fragment identifier if it has one.
    pub exec fn decode_to_vec(
        &self,
    ) -> (r: Result<(Vec<u8>, Option<FragmentIdentifier<'a>>), forgiving_base64::B64Error>)
        requires
            self.encoded_body_plus_fragment.len() < 1300000000,
        ensures
            match r {
                Result::Ok((body, fr)) => {
                    let dec = body_dec_spec(
                        self.encoded_body_plus_fragment@,
                        0,
                        self.encoded_body_plus_fragment.len() as int,
                    );
                    if self.base64 {
                        match forgiving_base64::dec64_run(dec.1, 0, 0, 0, 0) {
                            Result::Ok(o) => body@ == o
                                && (match fr {
                                    Option::Some(f) => dec.0 >= 0
                                        && f.fragment@
                                            == mime::slice_seq(
                                                self.encoded_body_plus_fragment@,
                                                dec.0,
                                                self.encoded_body_plus_fragment.len() as int,
                                            ),
                                    Option::None => dec.0 == -1,
                                }),
                            Result::Err(_) => false,
                        }
                    } else {
                        body@ == dec.1
                            && (match fr {
                                Option::Some(f) => dec.0 >= 0
                                    && f.fragment@
                                        == mime::slice_seq(
                                            self.encoded_body_plus_fragment@,
                                            dec.0,
                                            self.encoded_body_plus_fragment.len() as int,
                                        ),
                                Option::None => dec.0 == -1,
                            })
                    }
                }
                Result::Err(e) => self.base64
                    && match forgiving_base64::dec64_run(
                        body_dec_spec(
                            self.encoded_body_plus_fragment@,
                            0,
                            self.encoded_body_plus_fragment.len() as int,
                        ).1,
                        0,
                        0,
                        0,
                        0,
                    ) {
                        Result::Ok(_) => false,
                        Result::Err((k, b)) => {
                            forgiving_base64::kind_of(e) == k
                                && (k != 0 || forgiving_base64::sym_of(e) == b)
                        }
                    },
            },
    {
        let mut body: Vec<u8> = Vec::new();
        match self.decode(&mut body) {
            Result::Ok(fr) => Result::Ok((body, fr)),
            Result::Err(e) => Result::Err(e),
        }
    }
}

}

fn main() {}
