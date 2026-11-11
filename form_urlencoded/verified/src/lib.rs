//! form_urlencoded 1.2.2 @ servo/rust-url 00a6ce58
//! Upstream source: form_urlencoded/src/lib.rs (pin tree DB/code/form_urlencoded/src/lib.rs).
//! This file mirrors that upstream single-file structure, **src zone (the library
//!   code proper)**, aggregating: section A the spec model (serializer / parse /
//!   decode semantics) / section B the exec transcription (Origin Rust notes) /
//!   section C: the F1 panic reproduction (Serializer::for_suffix, lib.rs:222-229)
//!   / section D (remainder): the H1 reachability witness (a library-side
//!   obligation anchor, kept in src) / section E the auxiliary lemmas. The
//!   auto-generated harnesses (H2/H3/H4) live in verified/harness/ (no fact duplication).
//! Carrier note: String has no vstd spec; everything is transcribed on byte
//!   payloads Vec<u8>/&[u8>/Seq<u8>. encoding_override is always None (the private
//!   encode, lib.rs:392-397, is then just input.as_bytes()).
//! Section F (coverage-delta batch): the Serializer state-machine carrier
//!   (SerializerByte) with the new/for_suffix constructors, clear,
//!   encoding_override, encode (the None domain), the generic
//!   extend_pairs/extend_keys_only, finish (+ the string guard),
//!   Parse::into_owned/ParseIntoOwned, the byte_serialize structure model and
//!   size_hint.
//! Section G (residual batch, 2026-11-08): the discharge of the library's only
//!   `unsafe` (ByteSerialize::next, lib.rs:159 str::from_utf8_unchecked) via
//!   vstd's own UTF-8 model -- the position-scan spec of lib.rs:148 and the
//!   unchanged-checked slice => valid_utf8 chain, with the actual std call
//!   as the live obligation anchor.
//!
//! Migration note (matches!/splitn/Cow/iterators are all unsupported by Verus;
//!   every executable change keeps its original in an Origin Rust note);
//!   decode_utf8_lossy (lib.rs:402-428) is modeled as the identity: every exemplar
//!   decode output in this file is valid UTF-8 (ASCII or a valid 0xC3 0xA9 pair), so
//!   the lossy replacement branch is unreachable; this simplification only narrows
//!   the declared domain, never widens a contract.

use vstd::prelude::*;
use vstd::seq::Seq;
#[allow(unused)]
use vstd::string::*;
#[allow(unused)]
use vstd::utf8::*;

verus! {

// ================= Section A: spec model =================

/// Origin Rust: fn byte_serialized_unchanged(byte: u8) -> bool {
///     matches!(byte, b'*'|b'-'|b'.'|b'0'..=b'9'|b'A'..=b'Z'|b'_'|b'a'..=b'z')
/// }  (lib.rs:131-133)
pub open spec fn unchanged(b: u8) -> bool {
    b == b'*' || b == b'-' || b == b'.' || (b >= b'0' && b <= b'9')
        || (b >= b'A' && b <= b'Z') || b == b'_' || (b >= b'a' && b <= b'z')
}

/// Origin Rust: pub fn percent_encode_byte(byte: u8) -> &'static str  // "%{:02X}"
/// (percent_encoding lib.rs:73; its UT percent_encoding/tests:373-378 proves == "%{:02X}")
pub open spec fn hex_digit(d: int) -> u8 {
    if d <= 9 { (0x30 + d) as u8 } else { (0x41 + d - 10) as u8 }
}

/// Single-byte encoding (the single-byte branch of ByteSerialize::next, lib.rs:138-152):
/// unchanged -> verbatim; ' ' -> '+' (lib.rs:142-143); the rest -> percent_encode_byte.
pub open spec fn encode_byte(b: u8) -> Seq<u8> {
    if unchanged(b) {
        seq![b]
    } else if b == b' ' {
        seq![b'+']
    } else {
        seq![b'%', hex_digit(b as int / 16), hex_digit(b as int % 16)]
    }
}

/// Byte-level semantics of `append_encoded` (lib.rs:388-390): the first i bytes encoded.
pub open spec fn encode_len(s: Seq<u8>, i: int) -> Seq<u8>
    decreases i
{
    if i <= 0 { Seq::empty() } else { encode_len(s, i - 1) + encode_byte(s[i - 1]) }
}

pub open spec fn encoded(s: Seq<u8>) -> Seq<u8> {
    encode_len(s, s.len() as int)
}

/// Origin Rust: fn append_separator_if_needed(lib.rs:352-356)
pub open spec fn append_sep(s: Seq<u8>, start: int) -> Seq<u8> {
    if s.len() > start { s + seq![0x26u8] } else { s }
}

/// Origin Rust: fn append_pair (private, lib.rs:365-376)
pub open spec fn append_pair_spec(s: Seq<u8>, start: int, name: Seq<u8>, value: Seq<u8>) -> Seq<u8> {
    let s1 = append_sep(s, start);
    s1 + encoded(name) + seq![0x3Du8] + encoded(value)
}

/// Origin Rust: fn append_key_only (private, lib.rs:378-386)
pub open spec fn append_key_only_spec(s: Seq<u8>, start: int, name: Seq<u8>) -> Seq<u8> {
    let s1 = append_sep(s, start);
    s1 + encoded(name)
}

/// For the roundtrip (empty target, start=0): Serializer::new + append_pair + finish.
pub open spec fn serialize_pair(name: Seq<u8>, value: Seq<u8>) -> Seq<u8> {
    encoded(name) + seq![0x3Du8] + encoded(value)
}

/// Origin Rust: fn after_percent_sign(percent_encoding lib.rs:252-258)
///   `char::to_digit(16)`: accepts '0'-'9', 'a'-'f', 'A'-'F'
pub open spec fn hex_val(b: u8) -> int {
    if b >= 0x30 && b <= 0x39 { b as int - 0x30 }
    else if b >= 0x41 && b <= 0x46 { b as int - 0x41 + 10 }
    else if b >= 0x61 && b <= 0x66 { b as int - 0x61 + 10 }
    else { -1 }
}

/// Origin Rust: fn decode(input: &[u8])(lib.rs:70-76)=
///   decode_utf8_lossy(percent_decode(replace_plus(input)))
/// folded into a single-pass state machine (the two-pass composition equals the
/// per-byte fold: since '+' is not a hex digit, replacing '+' by ' ' first never
/// changes a '%'-triplet decision). decode(s, i) = the decode output of
/// s[i..]; '%' + two hex -> that byte, otherwise verbatim; '+' -> ' '.
pub open spec fn decode(s: Seq<u8>, i: int) -> Seq<u8>
    decreases s.len() - i
{
    if i >= s.len() {
        Seq::empty()
    } else if s[i] == 0x25 && i + 3 <= s.len()
        && hex_val(s[i + 1]) >= 0 && hex_val(s[i + 2]) >= 0 {
        let h = hex_val(s[i + 1]);
        let l = hex_val(s[i + 2]);
        seq![(h * 16 + l) as u8] + decode(s, i + 3)
    } else if s[i] == 0x2B {
        seq![0x20u8] + decode(s, i + 1)
    } else {
        seq![s[i]] + decode(s, i + 1)
    }
}

// ---- parse state-machine model (structural recursion, mirroring Parse::next lib.rs:51-67) ----

/// Scans within [i, b); the first '=' splits name/value (splitn(2,'='), lib.rs:62-64;
/// name = [a, i), value = [i+1, b) -- later '='s belong to value, matching splitn(2)).
pub open spec fn emit_pair_scan(s: Seq<u8>, a: int, i: int, b: int) -> Seq<(Seq<u8>, Seq<u8>)>
    decreases b - i
{
    if i >= b {
        seq![(decode(Seq::new((b - a) as nat, |j: int| s[a + j]), 0),
              decode(Seq::<u8>::empty(), 0))]
    } else if s[i] == 0x3D {
        seq![(decode(Seq::new((i - a) as nat, |j: int| s[a + j]), 0),
              decode(Seq::new((b - i - 1) as nat, |j: int| s[i + 1 + j]), 0))]
    } else {
        emit_pair_scan(s, a, i + 1, b)
    }
}

/// A non-empty sequence [a, b) yields one pair (an empty sequence yields none --
/// upstream `if sequence.is_empty() { continue; }`, lib.rs:59-61).
pub open spec fn emit_seg(s: Seq<u8>, a: int, b: int) -> Seq<(Seq<u8>, Seq<u8>)>
    decreases b - a
{
    if b <= a { Seq::empty() } else { emit_pair_scan(s, a, a, b) }
}

/// Origin Rust: the whole model of fn next(&mut self) -> splitn(2, '&') (lib.rs:56):
/// from is the current position, seg_start the current sequence start (a per-byte
/// '&' scan).
pub open spec fn parse_scan(s: Seq<u8>, from: int, seg_start: int) -> Seq<(Seq<u8>, Seq<u8>)>
    decreases s.len() - from
{
    if from >= s.len() {
        (if seg_start < s.len() { emit_seg(s, seg_start, s.len() as int) } else { Seq::empty() })
    } else if s[from] == 0x26 {
        emit_seg(s, seg_start, from) + parse_scan(s, from + 1, from + 1)
    } else {
        parse_scan(s, from + 1, seg_start)
    }
}

/// Full semantics of `parse(input)` (lib.rs:39), the collect view.
pub open spec fn parse_seq(s: Seq<u8>) -> Seq<(Seq<u8>, Seq<u8>)> {
    parse_scan(s, 0, 0)
}

/// Spec view of the (Vec, Vec) collect carrier.
pub open spec fn pairs_view(v: Seq<(Vec<u8>, Vec<u8>)>) -> Seq<(Seq<u8>, Seq<u8>)> {
    v.map_values(|p: (Vec<u8>, Vec<u8>)| (p.0@, p.1@))
}

// ================= Section B: exec transcription =================

pub exec fn byte_serialized_unchanged(b: u8) -> (r: bool)
    ensures r == unchanged(b)
{
    /* Origin Rust: matches!(byte, b'*'|b'-'|b'.'|b'0'..=b'9'|b'A'..=b'Z'|b'_'|b'a'..=b'z') */
    b == b'*' || b == b'-' || b == b'.' || (b >= b'0' && b <= b'9')
        || (b >= b'A' && b <= b'Z') || b == b'_' || (b >= b'a' && b <= b'z')
}

/// Exec version of hex_digit (the digit position of percent_encode_byte's "%{:02X}").
/// Upstream doc (percent_encoding/src/lib.rs:60-71):
///   Return the percent-encoding of the given byte.
///   This is unconditional, unlike `percent_encode()` which has an `AsciiSet` parameter.
pub exec fn hex_digit_exec(d: u8) -> (c: u8)
    requires d <= 15
    ensures c == hex_digit(d as int)
{
    if d <= 9 { b'0' + d } else { b'A' + (d - 10) }
}

/// Origin Rust: char::from(*b).to_digit(16)(percent_encoding lib.rs:254-255)
pub exec fn hex_val_exec(b: u8) -> (r: Option<u8>)
    ensures r.is_some() == (hex_val(b) >= 0)
        && (hex_val(b) >= 0 ==> r.unwrap() as int == hex_val(b))
{
    if b >= b'0' && b <= b'9' {
        Some(b - b'0')
    } else if b >= b'A' && b <= b'F' {
        Some(b - b'A' + 10)
    } else if b >= b'a' && b <= b'f' {
        Some(b - b'a' + 10)
    } else {
        None
    }
}

/// Origin Rust: fn append_encoded(s: &str, string: &mut String, encoding)(lib.rs:388-390)
///   string.extend(byte_serialize(&encode(encoding, s)))
/// The collect total effect of the `byte_serialize` iterator == sequential per-byte
/// encoding, hence the per-byte loop transcription.
pub exec fn append_encoded(s: &Vec<u8>, out: &mut Vec<u8>)
    ensures final(out)@ == old(out)@ + encoded(s@)
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            out@ == old(out)@ + encode_len(s@, i as int),
        decreases s.len() - i,
    {
        // Origin Rust: the byte_serialize per-byte branch (lib.rs:139-153)
        let b = s[i];
        if !byte_serialized_unchanged(b) {
            if b == b' ' {
                out.push(b'+');       // lib.rs:142: "+"
            } else {
                // Origin Rust: percent_encode_byte(first) -> "%{:02X}";
                // exec-side the nibbles use u8 div/mod (their vstd spec is exactly
                // (b as int)/16 and %16)
                let hi: u8 = b / 16;
                let lo: u8 = b % 16;
                out.push(b'%');
                out.push(hex_digit_exec(hi));
                out.push(hex_digit_exec(lo));
            }
        } else {
            out.push(b);
        }
        i = i + 1;
    }
    assert(encode_len(s@, s@.len() as int) == encoded(s@));
}

/// Origin Rust: fn append_separator_if_needed(string: &mut String, start)(lib.rs:352-356)
pub exec fn append_separator_if_needed_exec(s: &mut Vec<u8>, start_position: usize)
    ensures final(s)@ == append_sep(old(s)@, start_position as int)
{
    if s.len() > start_position {
        s.push(b'&');
    }
}

/// Origin Rust: fn append_pair (private free fn, lib.rs:365-376)
pub exec fn append_pair_exec(s: &mut Vec<u8>, start_position: usize, name: &Vec<u8>, value: &Vec<u8>)
    ensures final(s)@ == append_pair_spec(old(s)@, start_position as int, name@, value@)
{
    append_separator_if_needed_exec(s, start_position);
    append_encoded(name, s);
    s.push(b'=');
    append_encoded(value, s);
}

/// Origin Rust: pub fn append_key_only(&mut self, name: &str)(lib.rs:269-277)
pub exec fn append_key_only_exec(s: &mut Vec<u8>, start_position: usize, name: &Vec<u8>)
    ensures final(s)@ == append_key_only_spec(old(s)@, start_position as int, name@)
{
    append_separator_if_needed_exec(s, start_position);
    append_encoded(name, s);
}

/// Origin Rust: fn decode(input: &[u8])(lib.rs:70-76)
///   replace_plus(lib.rs:79-93)+ percent_decode(percent_encoding lib.rs:264-272)
/// The two passes equal the folded single pass (the folding analysis is in the
/// section A decode note), hence the single loop transcribed branch by branch;
/// the lossy identity is per the file-header note.
pub exec fn decode_exec(input: &[u8]) -> (out: Vec<u8>)
    ensures out@ == decode(input@, 0)
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            out@ + decode(input@, i as int) == decode(input@, 0),
        decreases input.len() - i,
    {
        let b = input[i];
        if b == b'%' && input.len() - i >= 3
            && hex_val_exec(input[i + 1]).is_some()
            && hex_val_exec(input[i + 2]).is_some() {
            let h = hex_val_exec(input[i + 1]).unwrap();
            let l = hex_val_exec(input[i + 2]).unwrap();
            /* Origin Rust: Some(h as u8 * 0x10 + l as u8)(percent_encoding lib.rs:258) */
            out.push(h * 16 + l);
            i = i + 3;
        } else if b == b'+' {
            out.push(b' ');       // Origin Rust: replaced[first_position] = b' '(lib.rs:84)
            i = i + 1;
        } else {
            out.push(b);
            i = i + 1;
        }
    }
    assert(decode(input@, input.len() as int) == Seq::<u8>::empty());
    out
}

/// Copies [a, b) into a standalone Vec (the carrier of the splitn slices; the
/// exec recursion advances by copying Vecs).
exec fn copy_new(s: &[u8], a: usize, b: usize) -> (v: Vec<u8>)
    requires a <= b <= s.len()
    ensures v@ == Seq::new((b as int - a as int) as nat, |j: int| s@[a as int + j])
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < b - a
        invariant
            0 <= i <= b - a,
            a + i <= b <= s.len(),
            v@ == Seq::new(i as int as nat, |j: int| s@[a as int + j]),
        decreases b - a - i,
    {
        proof { seq_new_step(s@, a as int, i as int); }
        v.push(s[a + i]);
        i = i + 1;
    }
    v
}

/// Origin Rust: sequence.splitn(2, '=') -> name/value + decode (lib.rs:62-65)
exec fn emit_pair_scan_exec(s: &[u8], a: usize, i: usize, b: usize,
    out: &mut Vec<(Vec<u8>, Vec<u8>)>)
    requires
        a < b,
        a <= i <= b <= s.len(),
    ensures
        pairs_view(final(out)@) == pairs_view(old(out)@) + emit_pair_scan(s@, a as int, i as int, b as int)
    decreases b - i
{
    if i >= b {
        let name = copy_new(s, a, b);
        let value: Vec<u8> = Vec::new();
        let name_dec = decode_exec(&name);
        out.push((name_dec, value));
        proof {
            pairs_view_concat(old(out)@, seq![(name_dec, value)]);
            assert(pairs_view(seq![(name_dec, value)]) == seq![(name_dec@, value@)]);
            assert(decode(Seq::<u8>::empty(), 0) == Seq::<u8>::empty());
        }
    } else if s[i] == b'=' {
        let name = copy_new(s, a, i);
        let value = copy_new(s, i + 1, b);
        let name_dec = decode_exec(&name);
        let value_dec = decode_exec(&value);
        out.push((name_dec, value_dec));
        proof {
            pairs_view_concat(old(out)@, seq![(name_dec, value_dec)]);
            assert(pairs_view(seq![(name_dec, value_dec)]) == seq![(name_dec@, value_dec@)]);
        }
    } else {
        emit_pair_scan_exec(s, a, i + 1, b, out);
    }
}

/// A non-empty sequence [a, b) yields one pair (an empty sequence yields none).
exec fn emit_seg_exec(s: &[u8], a: usize, b: usize, out: &mut Vec<(Vec<u8>, Vec<u8>)>)
    requires a <= b <= s.len()
    ensures pairs_view(final(out)@) == pairs_view(old(out)@) + emit_seg(s@, a as int, b as int)
{
    if a < b {
        emit_pair_scan_exec(s, a, a, b, out);
    }
}

/// Origin Rust: impl Iterator for Parse (lib.rs:51-67): a per-byte '&' driven
/// transcription (&mut out is the collect carrier).
pub exec fn parse_scan_exec(s: &[u8], from: usize, seg_start: usize,
    out: &mut Vec<(Vec<u8>, Vec<u8>)>)
    requires 0 <= seg_start <= from <= s.len()
    ensures pairs_view(final(out)@) == pairs_view(old(out)@) + parse_scan(s@, from as int, seg_start as int)
    decreases s.len() - from
{
    if from == s.len() {
        // the final sequence [seg_start, len)
        if seg_start < s.len() {
            emit_seg_exec(s, seg_start, s.len(), out);
        }
        return;
    }
    if s[from] == b'&' {
        // the current segment [seg_start, from); empty -> continue (lib.rs:59-61)
        emit_seg_exec(s, seg_start, from, out);
        parse_scan_exec(s, from + 1, from + 1, out);
        return;
    }
    parse_scan_exec(s, from + 1, seg_start, out);
}

/// Byte-level transcription entry of `parse(input).collect::<Vec<(String, String)>>`.
/// Upstream doc (lib.rs:31-37):
///   Convert a byte string in the `application/x-www-form-urlencoded` syntax
///   into a iterator of (name, value) pairs.
///   Use `parse(input.as_bytes())` to parse a `&str` string.
///   The names and values are percent-decoded. For instance, `%23first=%25try%25` will be
///   converted to `[("#first", "%try%")]`.
pub exec fn parse_all(input: &[u8]) -> (out: Vec<(Vec<u8>, Vec<u8>)>)
    ensures pairs_view(out@) == parse_seq(input@)
{
    let mut out: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    parse_scan_exec(input, 0, 0, &mut out);
    out
}

// ================= Section C: F1 panic reproduction (Serializer::for_suffix) =================

// ---------- L0: verbatim transcription of lib.rs:222-224 (the branch and the panic! verbatim) ----------

/// Transcription of `for_suffix`. The doc (lib.rs:217-221) sets no constraint on
/// `start_position` at all (no `# Panics`, while the sibling methods
/// clear/encoding_override/append_pair/finish document theirs) => requires stays
/// empty (faithful to the doc). Carrier note: `as_mut_string().len()` ~ the
/// byte-payload length. Verus encodes `panic!` as a call with requires false =>
/// the obligation on that line failing means "the panic branch is not provably
/// unreachable" -- the machine-detected form of F1 (the expected error site).
/// SPEC-DOC MISMATCH (#1168, fixed upstream by #1172): the rustdoc promises only
/// "Create a new ... serializer for a suffix of the given target" and no
/// `# Panics`, so the doc-default-duty reading "returns a serializer for any
/// (target, start_position)" is unprovable: with start_position > target.len()
/// the panic branch below fires; this transcription keeps the doc-faithful empty
/// requires (the panic line is the expected error).
/// Upstream doc (lib.rs:217-221):
///   Create a new `application/x-www-form-urlencoded` serializer
///   for a suffix of the given target.
///   If that suffix is non-empty,
///   its content is assumed to already be in `application/x-www-form-urlencoded` syntax.
pub exec fn for_suffix_upstream(target: &mut Vec<u8>, start_position: usize) -> () {
    if target.len() < start_position { // lib.rs:223 (branch verbatim)
        panic!(                        // lib.rs:224-228 <-- EXPECTED ERROR: precondition `false` (the F1 anchor; SPEC-DOC MISMATCH note above)
            "invalid length {} for target of length {}",
            start_position,
            target.len()
        );
    }
    // lib.rs:231-235:Serializer { target: Some(target), start_position, encoding: None }
    // (irrelevant to F1; the return is represented as ())
}

// ---------- Repair counter-proof (the formal shape of the Fix Document) ----------

/// The same code plus the one-line requires the doc leaves missing -- the branch
/// is provably false => the panic branch is unreachable => all obligations pass.
/// That is the formal meaning of "Fix Document: add a `# Panics` section": the
/// guard adds exactly the missing one-line precondition.
pub exec fn for_suffix_documented(target: &mut Vec<u8>, start_position: usize) -> ()
    requires
        start_position <= target.len(), // FIX (Document): the missing one-line precondition
{
    if target.len() < start_position {
        panic!(                        // now unreachable-provable given the requires
            "invalid length {} for target of length {}",
            start_position,
            target.len()
        );
    }
}

// ---------- Controls (new and the boundary) ----------

/// `new` == `for_suffix(target, 0)` (lib.rs:213-215): 0 <= len always => this
/// panic never fires.
pub exec fn new_equivalent_for_suffix_zero(target: &mut Vec<u8>) -> () {
    let start_position: usize = 0; // lib.rs:214: Self::for_suffix(target, 0)
    if target.len() < start_position {
        panic!(
            "invalid length {} for target of length {}",
            start_position,
            target.len()
        );
    }
}

/// Boundary control: `for_suffix("a=1", 3)` (start == len, the PoC control group)
/// constructs normally.
pub exec fn for_suffix_boundary_control(target: &mut Vec<u8>, start_position: usize) -> ()
    requires
        start_position <= target.len(), // the control calls only inside the legal domain
{
    if target.len() < start_position {
        panic!("invalid length {} for target of length {}", start_position, target.len());
    }
}

// ================= Section D (remainder): the H1 F1 reachability witness =================
// (H2/H3/H4 moved to verified/harness/harness.rs by the two-zone split, obligation
//  bodies verbatim; H1's witness lemma stays in src as the library-side anchor.)

// ================= Section F: the coverage-delta batch (2026-11-02) =================
// The public face the early batch (2026-10-29) left uncovered: the Serializer
// constructors/state machine (new/for_suffix/clear/encoding_override/finish), the
// generic extend_pairs/extend_keys_only, encode (pub(crate)),
// Parse::into_owned/ParseIntoOwned, and the byte_serialize structure (the next
// single-step advance + size_hint). The obligation anchor is unchanged: only the
// one section C F1 site.

// ---------- F-1: the state-machine carrier and spec model ----------

/// Origin Rust: pub struct Serializer<'a, T: Target> {
///     target: Option<T>, start_position: usize, encoding: EncodingOverride<'a>,
/// }  (lib.rs:176-180)
/// Carrier projection: Option<T> <-> target_present (false after take);
/// Target::as_mut_string() <-> payload: Vec<u8>; the closure values of
/// EncodingOverride<'a> = Option<&'a dyn Fn(...)> (lib.rs:430) are unsupported by Verus
/// => only the Some projection encoding_set is carried (per the file-header
/// ruling).
pub struct SerializerByte {
    pub target_present: bool,
    pub payload: Vec<u8>,
    pub start_position: usize,
    pub encoding_set: bool,
}

/// Origin Rust: fn string<T: Target>(target: &mut Option<T>) -> &mut String {
///     target.as_mut()
///         .expect("url::form_urlencoded::Serializer finished")
///         .as_mut_string() }  (lib.rs:358-363)
/// The doc already declares at each caller "Panics if called after `.finish()`."
/// => the has_target=true requires (the doc contract); contrast section C F1:
/// for_suffix's panic has no # Panics doc, so it is the obligation anchor;
/// this guard is not.
pub exec fn string_guard(has_target: bool)
    requires has_target
{
    assert(has_target);
}

/// Origin Rust: impl Target for String { fn as_mut_string(&mut self) -> &mut
///     String { self } ... } and impl Target for &mut String (same shape,
/// lib.rs:188-206); as_mut_string is a String identity map => the carrier is the
/// &mut Vec<u8> itself.
pub exec fn target_as_mut_string(s: &mut Vec<u8>) -> (r: &mut Vec<u8>)
    ensures r@ == old(s)@
{
    s
}

/// Origin Rust: impl Target for String { fn finish(self) -> Self { self }
///     type Finished = Self; }  (lib.rs:188-196, &mut String same shape at
/// 198-206); move <-> byte-payload identity; the return carrier is a clone (its
/// vstd spec is exactly content identity).
pub exec fn target_finish_move(s: &Vec<u8>) -> (r: Vec<u8>)
    ensures r@ == s@
{
    s.clone()
}

/// Spec of clear: truncate(start) (lib.rs:242) -- keeps the [0, start) prefix,
/// drops every byte appended after the construction point (doc: "Remove any
/// existing name/value pair.").
pub open spec fn clear_spec(s: Seq<u8>, start: int) -> Seq<u8> {
    if s.len() > start { s.subrange(0, start) } else { s }
}

/// Sequence view (the keys carrier of extend_keys_only).
pub open spec fn keys_view(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    v.map_values(|k: Vec<u8>| k@)
}

/// Origin Rust: pub fn extend_pairs<I, K, V>(..) for pair in iter { ... append_pair(
///     string, self.start_position, self.encoding, k.as_ref(), v.as_ref()) }  (lib.rs:286-307)
/// The generic IntoIterator/Borrow carrier <-> a sequential pair table; folds
/// append_pair pair by pair.
pub open spec fn extend_pairs_spec(s: Seq<u8>, start: int, pairs: Seq<(Seq<u8>, Seq<u8>)>) -> Seq<u8>
    decreases pairs.len()
{
    if pairs.len() == 0 {
        s
    } else {
        extend_pairs_spec(
            append_pair_spec(s, start, pairs[0].0, pairs[0].1),
            start,
            pairs.subrange(1, pairs.len() as int),
        )
    }
}

/// Origin Rust: pub fn extend_keys_only<I, K>(...) for key in iter { ... append_key_only(
///     string, self.start_position, self.encoding, k) }  (lib.rs:316-330)
pub open spec fn extend_keys_only_spec(s: Seq<u8>, start: int, keys: Seq<Seq<u8>>) -> Seq<u8>
    decreases keys.len()
{
    if keys.len() == 0 {
        s
    } else {
        extend_keys_only_spec(
            append_key_only_spec(s, start, keys[0]),
            start,
            keys.subrange(1, keys.len() as int),
        )
    }
}

// ---------- F-2: free-function transcripts (the equivalent position the upstream
// private free fns occupy before their in-method expansion) ----------

/// Origin Rust: pub(crate) fn encode<'a>(encoding_override: EncodingOverride<'_>,
///     input: &'a str) -> Cow<'a, [u8]> {
///     if let Some(o) = encoding_override { return o(input); }
///     input.as_bytes().into() }  (lib.rs:392-397)
/// Only the None branch is transcribed (lib.rs:396 `input.as_bytes().into()` is
/// the byte identity); the Some(o) branch (lib.rs:394-395) is a caller-injected
/// closure oracle; the in-library obligation domain is closed to None per the
/// file-header ruling (carried by the !encoding_set precondition).
pub exec fn encode_none(encoding_set: bool, input: &[u8]) -> (out: &[u8])
    requires !encoding_set
    ensures out@ == input@
{
    input
}

/// Transcription of the extend_pairs generic loop (lib.rs:293-305 in byte-carrier form).
pub exec fn extend_pairs_exec(s: &mut Vec<u8>, start_position: usize, has_target: bool,
    pairs: &Vec<(Vec<u8>, Vec<u8>)>)
    requires
        has_target, // doc:"Panics if called after `.finish()`."(lib.rs:285)
    ensures
        final(s)@ == extend_pairs_spec(old(s)@, start_position as int, pairs_view(pairs@)),
{
    string_guard(has_target);
    proof {
        assert(pairs_view(pairs@).subrange(0, pairs.len() as int) == pairs_view(pairs@));
        assert(s@ == old(s)@);
    }
    let mut i: usize = 0;
    while i < pairs.len()
        invariant
            0 <= i <= pairs.len(),
            extend_pairs_spec(old(s)@, start_position as int, pairs_view(pairs@))
                == extend_pairs_spec(s@, start_position as int,
                    pairs_view(pairs@).subrange(i as int, pairs.len() as int)),
        decreases pairs.len() - i,
    {
        let k: &Vec<u8> = &pairs[i].0;
        let v: &Vec<u8> = &pairs[i].1;
        append_pair_exec(s, start_position, k, v);
        proof {
            pairs_view_point(pairs@, i as int);
            subrange_head_tail(pairs_view(pairs@), i as int, pairs.len() as int);
            reveal_with_fuel(extend_pairs_spec, 1);
        }
        i = i + 1;
    }
    proof {
        assert(pairs_view(pairs@).subrange(pairs.len() as int, pairs.len() as int).len() == 0);
        reveal_with_fuel(extend_pairs_spec, 1);
    }
}

/// Transcription of the extend_keys_only generic loop (lib.rs:322-329 in byte-carrier form).
pub exec fn extend_keys_only_exec(s: &mut Vec<u8>, start_position: usize, has_target: bool,
    keys: &Vec<Vec<u8>>)
    requires
        has_target, // doc:"Panics if called after `.finish()`."(lib.rs:315)
    ensures
        final(s)@ == extend_keys_only_spec(old(s)@, start_position as int, keys_view(keys@)),
{
    string_guard(has_target);
    proof {
        assert(keys_view(keys@).subrange(0, keys.len() as int) == keys_view(keys@));
        assert(s@ == old(s)@);
    }
    let mut i: usize = 0;
    while i < keys.len()
        invariant
            0 <= i <= keys.len(),
            extend_keys_only_spec(old(s)@, start_position as int, keys_view(keys@))
                == extend_keys_only_spec(s@, start_position as int,
                    keys_view(keys@).subrange(i as int, keys.len() as int)),
        decreases keys.len() - i,
    {
        let k: &Vec<u8> = &keys[i];
        append_key_only_exec(s, start_position, k);
        proof {
            keys_view_point(keys@, i as int);
            subrange_head_tail(keys_view(keys@), i as int, keys.len() as int);
            reveal_with_fuel(extend_keys_only_spec, 1);
        }
        i = i + 1;
    }
    proof {
        assert(keys_view(keys@).subrange(keys.len() as int, keys.len() as int).len() == 0);
        reveal_with_fuel(extend_keys_only_spec, 1);
    }
}

// ---------- F-3: SerializerByte methods (verbatim counterparts of the
// upstream method layer) ----------

impl SerializerByte {
    /// Origin Rust: pub fn new(target: T) -> Self { Self::for_suffix(target, 0) }  (lib.rs:213-215)
    /// Upstream doc (lib.rs:209-212):
    ///   Create a new `application/x-www-form-urlencoded` serializer for the given target.
    ///   If the target is non-empty,
    ///   its content is assumed to already be in `application/x-www-form-urlencoded` syntax.
    pub exec fn new(payload: Vec<u8>) -> (r: Self)
        ensures
            r.target_present,
            r.payload@ == payload@,
            r.start_position == 0,
            !r.encoding_set, // lib.rs:234:encoding: None
    {
        SerializerByte { target_present: true, payload, start_position: 0, encoding_set: false }
    }

    /// Origin Rust: pub fn for_suffix(mut target: T, start_position: usize) -> Self { ...
    ///     Serializer { target: Some(target), start_position, encoding: None } }
    /// (lib.rs:222-235; the panic face is anchored by section C for_suffix_upstream;
    ///  only the surviving path is taken here)
    /// Upstream doc (lib.rs:217-221):
    ///   Create a new `application/x-www-form-urlencoded` serializer
    ///   for a suffix of the given target.
    ///   If that suffix is non-empty,
    ///   its content is assumed to already be in `application/x-www-form-urlencoded` syntax.
    /// SPEC-DOC MISMATCH (#1168, fixed upstream by #1172): the rustdoc sets no
    ///  constraint on `start_position` (no `# Panics`), so the requires below is not
    ///  doc-derived -- it carries the doc-missing guard explicitly (the surviving
    ///  path of the lib.rs:223 branch).
    pub exec fn for_suffix(payload: Vec<u8>, start_position: usize) -> (r: Self)
        requires
            start_position <= payload.len(), // the surviving domain in which the lib.rs:223 branch is false
        ensures
            r.target_present,
            r.payload@ == payload@,
            r.start_position == start_position,
            !r.encoding_set, // lib.rs:234:encoding: None
    {
        SerializerByte { target_present: true, payload, start_position, encoding_set: false }
    }

    /// Origin Rust: pub fn clear(&mut self) -> &mut Self {
    ///     string(&mut self.target).truncate(self.start_position); self }  (lib.rs:241-244)
    /// Upstream doc (lib.rs:238-240):
    ///   Remove any existing name/value pair.
    ///   Panics if called after `.finish()`.
    pub exec fn clear(&mut self)
        requires
            old(self).target_present, // the doc contract via the string guard, lib.rs:259-261
            old(self).start_position <= old(self).payload.len(), // the for_suffix construction invariant
        ensures
            final(self).payload@ == clear_spec(old(self).payload@, old(self).start_position as int),
            final(self).target_present == old(self).target_present,
            final(self).start_position == old(self).start_position,
            final(self).encoding_set == old(self).encoding_set,
    {
        let has_target = self.target_present;
        string_guard(has_target);
        let start = self.start_position;
        self.payload.truncate(start);
        proof {
            assert(final(self).payload@.len() == old(self).payload@.len()
                - (if old(self).payload@.len() > old(self).start_position as int {
                    old(self).payload@.len() - old(self).start_position as int
                } else { 0 }));
            assert(final(self).payload@ == old(self).payload@.subrange(0, final(self).payload@.len() as int));
        }
    }

    /// Origin Rust: pub fn encoding_override(&mut self, new: EncodingOverride<'a>)
    ///     -> &mut Self { self.encoding = new; self }  (lib.rs:247-250)
    /// Closure values are not carryable (file-header ruling); only the is_some
    /// projection is carried.
    /// Upstream doc (lib.rs:246-246):
    ///   Set the character encoding to be used for names and values before percent-encoding.
    pub exec fn encoding_override(&mut self, new_is_some: bool)
        ensures
            final(self).encoding_set == new_is_some,
            final(self).target_present == old(self).target_present,
            final(self).payload@ == old(self).payload@,
            final(self).start_position == old(self).start_position,
    {
        self.encoding_set = new_is_some;
    }

    /// Origin Rust: pub fn append_pair(&mut self, name: &str, value: &str)
    ///     -> &mut Self { append_pair(string(&mut self.target), self.start_position,
    ///     self.encoding, name, value); self }  (lib.rs:255-264)
    /// Upstream doc (lib.rs:252-254):
    ///   Serialize and append a name/value pair.
    ///   Panics if called after `.finish()`.
    pub exec fn append_pair(&mut self, name: &Vec<u8>, value: &Vec<u8>)
        requires
            old(self).target_present, // doc(lib.rs:254)
            !old(self).encoding_set, // the encode None carrier domain (file-header ruling)
        ensures
            final(self).payload@ == append_pair_spec(old(self).payload@,
                old(self).start_position as int, name@, value@),
            final(self).target_present == old(self).target_present,
            final(self).start_position == old(self).start_position,
            final(self).encoding_set == old(self).encoding_set,
    {
        let has_target = self.target_present;
        string_guard(has_target);
        let start = self.start_position;
        append_pair_exec(&mut self.payload, start, name, value);
    }

    /// Origin Rust: pub fn append_key_only(&mut self, name: &str) -> &mut Self {
    ///     append_key_only(string(&mut self.target), self.start_position,
    ///     self.encoding, name); self }  (lib.rs:269-277)
    /// Upstream doc (lib.rs:266-268):
    ///   Serialize and append a name of parameter without any value.
    ///   Panics if called after `.finish()`.
    pub exec fn append_key_only(&mut self, name: &Vec<u8>)
        requires
            old(self).target_present, // doc(lib.rs:268)
            !old(self).encoding_set,
        ensures
            final(self).payload@ == append_key_only_spec(old(self).payload@,
                old(self).start_position as int, name@),
            final(self).target_present == old(self).target_present,
            final(self).start_position == old(self).start_position,
            final(self).encoding_set == old(self).encoding_set,
    {
        let has_target = self.target_present;
        string_guard(has_target);
        let start = self.start_position;
        append_key_only_exec(&mut self.payload, start, name);
    }

    /// Origin Rust: pub fn extend_pairs<I, K, V>(&mut self, iter: I) -> &mut Self
    ///     { { let string = string(&mut self.target); for pair in iter { … } } self }
    ///     (lib.rs:286-307; the loop-body shim is carried by extend_pairs_exec)
    /// Upstream doc (lib.rs:279-285):
    ///   Serialize and append a number of name/value pairs.
    ///   This simply calls `append_pair` repeatedly.
    ///   This can be more convenient, so the user doesn’t need to introduce a block
    ///   to limit the scope of `Serializer`’s borrow of its string.
    ///   Panics if called after `.finish()`.
    pub exec fn extend_pairs(&mut self, pairs: &Vec<(Vec<u8>, Vec<u8>)>)
        requires
            old(self).target_present, // doc(lib.rs:285)
            !old(self).encoding_set,
        ensures
            final(self).payload@ == extend_pairs_spec(old(self).payload@,
                old(self).start_position as int, pairs_view(pairs@)),
            final(self).target_present == old(self).target_present,
            final(self).start_position == old(self).start_position,
            final(self).encoding_set == old(self).encoding_set,
    {
        let has_target = self.target_present;
        string_guard(has_target);
        let start = self.start_position;
        extend_pairs_exec(&mut self.payload, start, has_target, pairs);
    }

    /// Origin Rust: pub fn extend_keys_only<I, K>(&mut self, iter: I) -> &mut Self
    ///     { { let string = string(&mut self.target); for key in iter { … } } self }
    ///     (lib.rs:316-330)
    /// Upstream doc (lib.rs:309-315):
    ///   Serialize and append a number of names without values.
    ///   This simply calls `append_key_only` repeatedly.
    ///   This can be more convenient, so the user doesn’t need to introduce a block
    ///   to limit the scope of `Serializer`’s borrow of its string.
    ///   Panics if called after `.finish()`.
    pub exec fn extend_keys_only(&mut self, keys: &Vec<Vec<u8>>)
        requires
            old(self).target_present, // doc(lib.rs:315)
            !old(self).encoding_set,
        ensures
            final(self).payload@ == extend_keys_only_spec(old(self).payload@,
                old(self).start_position as int, keys_view(keys@)),
            final(self).target_present == old(self).target_present,
            final(self).start_position == old(self).start_position,
            final(self).encoding_set == old(self).encoding_set,
    {
        let has_target = self.target_present;
        string_guard(has_target);
        let start = self.start_position;
        extend_keys_only_exec(&mut self.payload, start, has_target, keys);
    }

    /// Origin Rust: pub fn finish(&mut self) -> T::Finished {
    ///     self.target.take()
    ///         .expect("url::form_urlencoded::Serializer double finish")
    ///         .finish() }  (lib.rs:344-349)
    /// The doc's "# Panics" line => the target_present precondition: on the second
    /// call target has been taken to None => the expect panic (already declared by
    /// the doc, not a defect).
    /// Carrier: Option::take moves the String out whole (bytes untouched) => the
    /// payload is identical; Target::finish(self) == self (a move) => the return is a
    /// clone carrier; afterwards every serializer-side access is sealed off by
    /// !target_present (the panic face of the lib.rs:358-363 string guard).
    /// Upstream doc (lib.rs:332-343):
    ///   If this serializer was constructed with a string, take and return that string.
    pub exec fn finish(&mut self) -> (r: Vec<u8>)
        requires
            old(self).target_present, // doc(lib.rs:343)
        ensures
            r@ == old(self).payload@,
            !final(self).target_present,
            final(self).payload@ == old(self).payload@,
            final(self).start_position == old(self).start_position,
            final(self).encoding_set == old(self).encoding_set,
    {
        let has_target = self.target_present;
        string_guard(has_target);
        let r = self.payload.clone();
        self.target_present = false;
        r
    }
}

// ---------- F-4: Parse::into_owned/ParseIntoOwned ----------

/// Origin Rust: pub fn into_owned(self) -> ParseIntoOwned<'a> { ParseIntoOwned {
///     inner: self } }  (lib.rs:95-99)
/// Origin Rust: impl Iterator for ParseIntoOwned<'_> { fn next(&mut self) ->
///     Option<Self::Item> { self.inner.next().map(|(k, v)|
///     (k.into_owned(), v.into_owned())) } }  (lib.rs:107-115)
/// Carrier: both sides are owned, already-decoded byte payloads (early section B
/// already transcribes decode output as owned Vecs); whether Cow is Borrowed or
/// Owned is indistinguishable at the byte payload -- into_owned only adds copy
/// ownership, never changes content => the ParseIntoOwned full collect == the
/// Parse full collect.
/// Upstream doc (lib.rs:96-96):
///   Return a new iterator that yields pairs of `String` instead of pairs of `Cow<str>`.
pub exec fn parse_into_owned_all(input: &[u8]) -> (out: Vec<(Vec<u8>, Vec<u8>)>)
    ensures pairs_view(out@) == parse_seq(input@)
{
    let mut out: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    parse_scan_exec(input, 0, 0, &mut out);
    out
}

// ---------- F-5: the byte_serialize structure model and size_hint ----------

/// Origin Rust: fn next(&mut self) -> Option<&'a str>(lib.rs:138-163):
/// A first byte that is not unchanged -> exactly 1 byte consumed, a single-byte
/// piece (b' ' -> "+", the rest "%XX"); a first byte that IS unchanged -> one
/// maximal unchanged run, stopping just before the first non-unchanged byte
/// after it (lib.rs:148-153: tail.position(!unchanged) -> split_at(1+i)).
/// Carrier: next's piecing structure <-> the piece-start set: i is a piece
/// start iff (i == 0), or s[i] is not unchanged (a single-byte piece), or
/// s[i-1] is not unchanged (the head of a run piece). The collect total effect
/// (== encoded) is already transcribed by section B's append_encoded; here only
/// the piece-structure model is built, to bound the actual piece count for
/// size_hint.
pub open spec fn chunk_start(s: Seq<u8>, i: int) -> bool {
    i == 0 || (0 < i < s.len() && (!unchanged(s[i]) || !unchanged(s[i - 1])))
}

/// The number of pieces within the remaining interval [i, len) (a +1 step;
/// termination trivial).
pub open spec fn piece_total(s: Seq<u8>, i: int) -> int
    decreases s.len() - i
{
    if i >= s.len() {
        0
    } else {
        (if chunk_start(s, i) { 1int } else { 0int }) + piece_total(s, i + 1)
    }
}

/// The total number of pieces the byte_serialize iterator actually yields from
/// construction on.
pub open spec fn piece_count_all(s: Seq<u8>) -> int {
    piece_total(s, 0)
}

/// Origin Rust: pub fn byte_serialize(input: &[u8]) -> ByteSerialize<'_>
///     { ByteSerialize { bytes: input } }  (lib.rs:121-123)
/// Construction <-> remaining-interval position 0 (the collect effect is section
/// B's append_encoded).
/// Upstream doc (lib.rs:117-120):
///   The [`application/x-www-form-urlencoded` byte serializer](
///   https://url.spec.whatwg.org/#concept-urlencoded-byte-serializer).
///   Return an iterator of `&str` slices.
pub exec fn byte_serialize_entry(input: &[u8]) -> (position: usize)
    ensures position == 0
{
    0
}

/// Origin Rust: fn size_hint(&self) -> (usize, Option<usize>) {
///     if self.bytes.is_empty() { (0, Some(0)) } else { (1, Some(self.bytes.len())) }
/// }  (lib.rs:165-171: the original counts over the whole self.bytes interval;
///      the carrier counts over the remaining interval [position, len))
pub exec fn byte_serialize_size_hint(bytes: &[u8], position: usize) -> (r: (usize, Option<usize>))
    requires position <= bytes.len()
    ensures
        position < bytes.len() ==> r.0 == 1 && r.1 == Some((bytes.len() - position) as usize),
        position == bytes.len() ==> r.0 == 0 && r.1 == Some(0usize),
{
    /* Origin Rust: if self.bytes.is_empty() { (0, Some(0)) } else { (1, Some(self.bytes.len())) } */
    if position == bytes.len() {
        (0usize, Some(0usize))
    } else {
        (1usize, Some(bytes.len() - position))
    }
}


// ===========================================================================
// Proof lemmas (scan-skip, view/seq helpers, the section F-6 shared lemmas and
// the H1 F1 reachability witness; moved to the end of the file so the exec
// implementations read directly -- only the order changed, signatures and
// contracts untouched)
// ===========================================================================
/// Scan-skip lemma: no '&' inside [from, k) => parse_scan leaves
/// (from, seg_start) unchanged.
/// (Minimal pub adjustment: after the two-zone split the H3 lemma/roundtrip
///  proof of harness/harness.rs references this lemma via #[path] mod;
///  relaxing the visibility does not change the verification semantics.)
pub proof fn parse_scan_skip(s: Seq<u8>, from: int, k: int, seg_start: int)
    requires
        0 <= from <= k <= s.len(),
        forall|j: int| from <= j < k ==> #[trigger] s[j] != 0x26,
    ensures parse_scan(s, from, seg_start) == parse_scan(s, k, seg_start)
    decreases k - from
{
    if from == k {
    } else {
        reveal_with_fuel(parse_scan, 1);
        parse_scan_skip(s, from + 1, k, seg_start);
    }
}

/// '=' scan-skip lemma: no '=' inside [i, k) => emit_pair_scan only advances the
/// index.
/// (Minimal pub adjustment: as above; referenced by the harness-side H3/H2
///  roundtrip proofs.)
pub proof fn emit_pair_scan_skip(s: Seq<u8>, a: int, i: int, k: int, b: int)
    requires
        0 <= a <= i <= k <= b <= s.len(),
        forall|j: int| i <= j < k ==> #[trigger] s[j] != 0x3D,
    ensures emit_pair_scan(s, a, i, b) == emit_pair_scan(s, a, k, b)
    decreases k - i
{
    if i == k {
    } else {
        reveal_with_fuel(emit_pair_scan, 1);
        emit_pair_scan_skip(s, a, i + 1, k, b);
    }
}

proof fn pairs_view_concat(a: Seq<(Vec<u8>, Vec<u8>)>, b: Seq<(Vec<u8>, Vec<u8>)>)
    ensures pairs_view(a + b) == pairs_view(a) + pairs_view(b)
{
    assert(pairs_view(a + b).len() == a.len() + b.len());
    assert(pairs_view(a + b) =~= pairs_view(a) + pairs_view(b));
}

proof fn seq_new_step(s: Seq<u8>, a: int, k: int)
    requires 0 <= k, a + k < s.len()
    ensures Seq::new((k + 1) as nat, |j: int| s[a + j]) == Seq::new(k as nat, |j: int| s[a + j]) + seq![s[a + k]]
{
    assert(Seq::new((k + 1) as nat, |j: int| s[a + j]).len() == k + 1);
    assert(Seq::new((k + 1) as nat, |j: int| s[a + j]) =~=
        Seq::new(k as nat, |j: int| s[a + j]) + seq![s[a + k]]);
}

// ---------- F-6: shared lemmas (subrange stepping / view pointwise) ----------

/// Three subrange head/tail facts (for the extend_* loop stepping): the length of
/// a subrange, its first element, and the tail-minus-1 subrange == the subrange
/// shifted by one (pointwise immediate from the vstd subrange axioms).
pub proof fn subrange_head_tail<T>(p: Seq<T>, i: int, n: int)
    requires 0 <= i < n <= p.len()
    ensures
        p.subrange(i, n).len() == n - i,
        p.subrange(i, n).index(0) == p.index(i),
        p.subrange(i, n).subrange(1, n - i) == p.subrange(i + 1, n),
{ }

/// pairs_view pointwise: pairs_view(p)[i] == (p[i].0@, p[i].1@).
pub proof fn pairs_view_point(pairs: Seq<(Vec<u8>, Vec<u8>)>, i: int)
    requires 0 <= i < pairs.len()
    ensures pairs_view(pairs).index(i) == (pairs.index(i).0@, pairs.index(i).1@)
{
    assert(pairs_view(pairs).len() == pairs.len());
}

/// keys_view pointwise: keys_view(v)[i] == v[i]@.
pub proof fn keys_view_point(keys: Seq<Vec<u8>>, i: int)
    requires 0 <= i < keys.len()
    ensures keys_view(keys).index(i) == keys.index(i)@
{
    assert(keys_view(keys).len() == keys.len());
}

/// H1 reachability bridge: the PoC triggers `for_suffix(String::new(), 1)`.
/// Every documented claim ("the suffix content is assumed to already be
/// urlencoded", vacuously true for an empty target) holds while `0 < 1` is true
/// => the panic branch is reachable. Counterexample made concrete: target_len=0,
/// start_position=1.
proof fn f1_reachability_witness() {
    let target_len: int = 0;
    let start_position: int = 1;
    assert(true); // documented-side: vacuously satisfied (empty suffix)
    assert(target_len < start_position); // branch condition true => panic reachable
}

// ================= Section G: the unsafe-discharge residual batch
// (2026-11-08) =================
// The single `unsafe` of the library lives in ByteSerialize::next, lib.rs:159
//   Some(unsafe { str::from_utf8_unchecked(unchanged_slice) })
// with the in-source safety argument (lib.rs:155-157): "This unsafe is
// appropriate because we have already checked these bytes in
// byte_serialized_unchanged, which checks for a subset of UTF-8. So we know
// these bytes are valid UTF-8, and doing another UTF-8 check would be wasteful."
// This section discharges that argument against vstd's own UTF-8 model: the
// std call is reached through the assume_specification re-declared below. It
// repeats vstd's own spec verbatim (vstd string.rs:169-174, requires
// valid_utf8(v@), ensures res.spec_bytes() =~= v@): the prebuilt vstd of this
// verus build registers its spec under a `str::` path key, while this
// toolchain resolves the call def-id as core::str::converts::from_utf8_unchecked,
// so the re-declaration is required merely to make vstd's own spec resolve;
// the declared requires is thereby a live obligation at the call below
// (measured: an unsatisfied valid_utf8 premise fails the call).

pub assume_specification[std::str::from_utf8_unchecked](v: &[u8]) -> (res: &str)
    requires
        valid_utf8(v@),
    ensures
        res.spec_bytes() =~= v@,
;

/// Origin Rust: tail.iter().position(|&b| !byte_serialized_unchanged(b))
/// (lib.rs:148; tail = the bytes after the head): the first index at or after i
/// whose byte is *not* unchanged, or len() when every byte in [i, len) is
/// unchanged. (Minimal pub adjustment: the harness-side UT-5 exemplars assert
/// on the pieces this scan carves; relaxing the visibility changes no
/// verification semantics, as with the skip lemmas above.)
pub open spec fn scan_nonunchanged(s: Seq<u8>, i: int) -> int
    decreases s.len() - i
{
    if i >= s.len() || !unchanged(s[i]) { i } else { scan_nonunchanged(s, i + 1) }
}

/// Position-semantics, one step: an unchanged byte at i does not move the
/// boundary (position() skips over it).
proof fn scan_step(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
        unchanged(s[i]),
    ensures
        scan_nonunchanged(s, i) == scan_nonunchanged(s, i + 1),
{
    reveal_with_fuel(scan_nonunchanged, 1);
}

/// Position-semantics, terminal: at a non-unchanged byte (or the end) the
/// boundary is the index itself.
proof fn scan_terminal(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
        i == s.len() || !unchanged(s[i]),
    ensures
        i <= scan_nonunchanged(s, i) <= s.len(),
        scan_nonunchanged(s, i) == i,
{
    reveal_with_fuel(scan_nonunchanged, 1);
}

/// Position() returns the FIRST non-unchanged index: every byte at or after i
/// and strictly before the boundary was passed over by the scan, i.e. checked
/// unchanged -- exactly the premise the in-source safety remark relies on.
proof fn scan_all_before_unchanged(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= scan_nonunchanged(s, i) <= s.len(),
        forall|j: int| i <= j < scan_nonunchanged(s, i) ==> #[trigger] unchanged(s[j]),
    decreases s.len() - i,
{
    reveal_with_fuel(scan_nonunchanged, 1);
    if i < s.len() && unchanged(s[i]) {
        scan_all_before_unchanged(s, i + 1);
    }
}

/// The "checks for a subset of UTF-8" half of the safety remark: every
/// unchanged byte is an ASCII (width-1 leading) byte.
proof fn unchanged_ascii_lead(b: u8)
    ensures
        unchanged(b) ==> is_leading_byte_width_1(b),
{ }

/// The full safety argument (lib.rs:155-158): a slice whose every byte was
/// checked unchanged is valid UTF-8. Width-1 leading bytes only => each scalar
/// consumes exactly one byte => the vstd ascii-block prefix extension walks
/// the whole slice.
pub proof fn unchanged_slice_valid_utf8(s: Seq<u8>, a: int, b: int)
    requires
        0 <= a <= b <= s.len(),
        forall|j: int| a <= j < b ==> #[trigger] unchanged(s[j]),
    ensures
        #![trigger valid_utf8(s.subrange(a, b))]
        valid_utf8(s.subrange(a, b)),
{
    let q = s.subrange(a, b);
    assert forall|k: int| 0 <= k < q.len() implies #[trigger] is_leading_byte_width_1(q[k]) by {
        // q.len() == b - a, so 0 <= k < b - a gives a <= a + k < b
        vstd::seq::lemma_seq_subrange_len(s, a, b);
        assert(q.len() == b - a);
        // q[k] == s[a + k] (vstd subrange-index lemma), and s[a + k] was checked unchanged
        vstd::seq::lemma_seq_subrange_index(s, a, b, k);
        assert(q[k] == s[a + k]);
        assert(unchanged(s[a + k]));
        unchanged_ascii_lead(s[a + k]);
    }
    assert(valid_utf8(q.subrange(0, 0)));
    partial_valid_utf8_extend_ascii_block(q, 0, q.len() as int);
    assert(q.subrange(0, q.len() as int) =~= q);
}

/// Origin Rust: the unchanged-run branch of ByteSerialize::next
/// (lib.rs:148-159):
///     let position = tail.iter().position(|&b| !byte_serialized_unchanged(b));
///     let (unchanged_slice, remaining) = match position {
///         Some(i) => self.bytes.split_at(1 + i),
///         None => (self.bytes, &[][..]),
///     };
///     self.bytes = remaining;
///     Some(unsafe { str::from_utf8_unchecked(unchanged_slice) })
/// Carrier: the iterator state's self.bytes cursor is the (bytes, position)
/// pair; the branch's premise is the unchanged head requires below
/// (lib.rs:140); the str::from_utf8_unchecked is the actual std call under
/// the assume_specification above, so its `requires valid_utf8` is the live
/// obligation this fn must discharge -- the formal reading of the safety
/// remark (the only guarantee the checked-unchanged premise actually buys).
/// (Minimal pub adjustment as with the skip lemmas: the UT-5 exemplar calls
/// this anchor by name.)
pub exec fn next_utf8_unchecked_run(bytes: &[u8], position: usize) -> (r: &str)
    requires
        position < bytes.len(),
        unchanged(bytes@[position as int]), // lib.rs:140: the head was checked unchanged
    ensures
        r.spec_bytes() =~= bytes@.subrange(position as int,
            scan_nonunchanged(bytes@, position as int + 1)),
{
    // Origin Rust: tail.iter().position(...)(lib.rs:148) -- the exec scan
    let mut i: usize = position + 1;
    while i < bytes.len() && byte_serialized_unchanged(bytes[i])
        invariant
            position < i <= bytes.len(),
            forall|j: int| position < j < i ==> #[trigger] unchanged(bytes[j]),
            scan_nonunchanged(bytes@, position as int + 1) == scan_nonunchanged(bytes@, i as int),
        decreases bytes.len() - i,
    {
        proof { scan_step(bytes@, i as int); }
        i = i + 1;
    }
    // Origin Rust: match position { Some(i) => self.bytes.split_at(1 + i),
    //     None => (self.bytes, &[][..]) }(lib.rs:149-153; the None case is the
    // scan reaching len: the slice is the whole remaining run)
    let unchanged_slice: &[u8] = &bytes[position..i];
    proof {
        scan_terminal(bytes@, i as int);
        assert(unchanged(bytes@[position as int]));
        unchanged_slice_valid_utf8(bytes@, position as int, i as int);
        assert(unchanged_slice@ == bytes@.subrange(position as int, i as int));
    }
    // Origin Rust: Some(unsafe { str::from_utf8_unchecked(unchanged_slice) })(lib.rs:159)
    unsafe { std::str::from_utf8_unchecked(unchanged_slice) }
}
}

fn main() {}
