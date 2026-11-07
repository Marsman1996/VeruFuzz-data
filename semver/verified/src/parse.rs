//! Mirror of `code/src/parse.rs`.
//!
//! Transcription ledger (specific to this file, on top of the lib.rs ledger):
//! - `&str` -> `&[u8]` (lib.rs ledger item 1): `strip_prefix('c')`/`starts_with('c')`
//!   expand to first-byte tests; `trim_start_matches(' ')` expands to a space-scan
//!   loop (`trim_spaces`); `chars().next()` expands to the first byte. Each
//!   expansion carries an `Origin Rust:` annotation.
//! - The `version_req` stack-write technique (parse.rs:366-404): `out: &mut Vec<Comparator>` +
//!   `unsafe { comparators.set_len(len) }` + `out.as_mut_ptr().add(depth)
//!   .write(comparator)` is rewritten as a `Result<Vec<Comparator>, Error>`
//!   assembly recursion (assembly order = parse order, see `version_req_rec`).
//! - The upstream `unsafe { Identifier::new_unchecked(string) }` (an unsafe block)
//!   vanishes into the `Vec<u8>` model per lib.rs ledger item 2.
//! - Error obligations use lib.rs's `ek_num/ek_pos/ek_char` int slots.
//!   Contracts come in two grades: Ok is L2 doc-level (digit value /
//!   leading zeros / segment grammar / wildcard gate), Err is the
//!   necessary-condition direction; the full semantics are pinned by harness
//!   example theorems.
//! - The lemma layer L1--L4 (`first_dot` dotless-append stability, the scanning
//!   synthesis of `no_empty_segment`/`pre_no_leading_zero`) underlies the
//!   identifier loop invariants.

use vstd::prelude::*;
use vstd::seq::Seq;

use super::impls::{pre_cmp_spec_top, seg_end_at, Ord2};
use super::{
    ek_char, ek_num, first_dot, is_digit, no_empty_segment, num_str_value, BuildMetadata,
    Comparator, Error, ErrorKind, Op, Position, Prerelease, Version, VersionReq,
};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ======================================================================
 * Shared grammar spec model
 * ====================================================================== */

/// digits-only (true for the empty sequence -- mirroring upstream `bytes().all(is_ascii_digit)`).
pub open spec fn digits_only(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] is_digit(s[i])
}

/// identifier grammar byte domain (the identifier.rs module header: hyphen, dot, 0-9, A-Z, a-z).
pub open spec fn ident_char_or_dot(b: u8) -> bool {
    (0x30 <= b <= 0x39) || (0x41 <= b <= 0x5a) || (0x61 <= b <= 0x7a) || b == 0x2d || b == 0x2e
}

/// In-segment bytes (the identifier.rs module header minus the separating dot).
pub open spec fn ident_char(b: u8) -> bool {
    (0x30 <= b <= 0x39) || (0x41 <= b <= 0x5a) || (0x61 <= b <= 0x7a) || b == 0x2d
}

/// identifier grammar validity (the lib.rs Prerelease/BuildMetadata Syntax doc):
/// byte domain + all segments non-empty + no trailing '.'.
pub open spec fn ident_lang_valid(s: Seq<u8>) -> bool {
    &&& forall|i: int| 0 <= i < s.len() ==> #[trigger] ident_char_or_dot(s[i])
    &&& no_empty_segment(s)
    &&& (s.len() == 0 || s[s.len() - 1] != 0x2e)
}

/// doc: "Numeric identifiers must not include leading zeros." (Pre only).
/// Non-recursive pairwise form: a violation is a segment start (the first
/// character or a '.' predecessor) that begins with a digit and spans an
/// all-digit segment of length > 1 (a mirror of the upstream
/// `segment_len > 1 && !has_nondigit && starts_with('0')` form).
pub open spec fn nolead_seg_bad(s: Seq<u8>, i: int) -> bool {
    s[i] == 0x30
        && exists|e: int|
            #![trigger seg_end_at(s, i, e)]
            seg_end_at(s, i, e)
                && e - i > 1
                && forall|k: int| i <= k < e ==> #[trigger] is_digit(s[k])
}

pub open spec fn pre_no_leading_zero(s: Seq<u8>) -> bool {
    forall|i: int|
        #![trigger nolead_seg_bad(s, i)]
        (0 <= i < s.len() && (i == 0 || s[i - 1] == 0x2e)) ==> !nolead_seg_bad(s, i)
}

/// Pairwise carrier of the segment-structure invariant: k in [0..n) is '.' => (k>0 with a non-'.' predecessor).
pub open spec fn no_dot_here(s: Seq<u8>, k: int, n: int) -> bool {
    (0 <= k < n) ==> (s[k] != 0x2e || (0 < k && s[k - 1] != 0x2e))
}

/// Illegal-character carrier (an exists-variable trigger predicate).
pub open spec fn foreign_byte(input: Seq<u8>, i: int) -> bool {
    0 <= i < input.len() && !ident_char_or_dot(input[i])
}

/// Carrier of the necessary direction of the LeadingZero obligation (a leading-zero digit segment somewhere in the prefix).
pub open spec fn nolead_prefix(input: Seq<u8>, n: int) -> bool {
    0 <= n <= input.len() && !pre_no_leading_zero(input[..n])
}

/// Necessary pattern of EmptySegment: some '.' sits at position 0, or at the last boundary, or is followed by a non-segment character or another '.'.
pub open spec fn dot_empty_pattern(input: Seq<u8>) -> bool {
    exists|i: int|
        #![trigger input[i]]
        0 <= i < input.len() && #[trigger] input[i] == 0x2e && (i == 0 || i + 1 == input.len()
            || !ident_char(input[i + 1])
            || input[i + 1] == 0x2e)
}

/// `[from..upto]` is a legal numeric segment: digits, no leading zero, value = val.
pub open spec fn is_num_at(input: Seq<u8>, from: int, upto: int, val: int) -> bool {
    &&& 0 <= from < upto
    &&& digits_only(input[from..upto])
    &&& (upto - from == 1 || input[from] != 0x30)
    &&& val == num_str_value(input[from..upto], upto - from)
}

/// Full syntactic decomposition of Version::parse Ok (the lib.rs Version Syntax doc):
/// major '.' minor '.' patch [ '-' pre '+' build ], numbers without leading
/// zeros, pre inside the segment language and free of leading-zero digit
/// segments, build inside the segment language (build allows leading zeros -- doc).
pub open spec fn ver_ok(input: Seq<u8>, v: Version) -> bool {
    exists|n1: int, n2: int, n3: int, n4: int, n5: int| #![trigger ver_ok_split(
        input,
        v.major,
        v.minor,
        v.patch,
        v.pre.bytes@,
        v.build.bytes@,
        n1,
        n2,
        n3,
        n4,
        n5,
    )] ver_ok_split(input, v.major, v.minor, v.patch, v.pre.bytes@, v.build.bytes@, n1, n2, n3, n4, n5)
}

/// Full-form carrier of ver_ok (every exists variable inside the same trigger predicate, consumed by the unfolder).
pub open spec fn ver_ok_split(
    input: Seq<u8>,
    maj: u64,
    min: u64,
    pat: u64,
    pre: Seq<u8>,
    build: Seq<u8>,
    n1: int,
    n2: int,
    n3: int,
    n4: int,
    n5: int,
) -> bool {
    &&& 0 <= n1 && n1 < n2 && n2 < n3 <= input.len()
    &&& input[n1] == 0x2e && input[n2] == 0x2e
    &&& is_num_at(input, 0, n1, maj as int)
    &&& is_num_at(input, n1 + 1, n2, min as int)
    &&& is_num_at(input, n2 + 1, n3, pat as int)
    &&& (n3 == input.len()
        && pre == Seq::<u8>::empty()
        && build == Seq::<u8>::empty()
        || (input[n3] == 0x2d && n3 + 1 < n4 <= input.len()
            && pre == input[n3 + 1..n4]
            && ident_lang_valid(input[n3 + 1..n4])
            && pre_no_leading_zero(input[n3 + 1..n4])
            && (n4 == input.len() && build == Seq::<u8>::empty()
                || (input[n4] == 0x2b && n4 + 1 < n5 == input.len()
                    && build == input[n4 + 1..n5]
                    && ident_lang_valid(input[n4 + 1..n5]))))
        || (input[n3] == 0x2b && n3 + 1 < n5 == input.len()
            && pre == Seq::<u8>::empty()
            && build == input[n3 + 1..n5]
            && ident_lang_valid(input[n3 + 1..n5])))
}

/// Comparator structural invariant (the lib.rs Comparator doc:
/// "Patch is only allowed if minor is Some"/"Non-empty pre-release is only
/// "allowed if patch is Some").
pub open spec fn comp_struct_ok(c: Comparator) -> bool {
    (c.patch.is_Some() ==> c.minor.is_Some())
    && (c.pre.bytes@.len() > 0 ==>
        (c.patch.is_Some() && c.minor.is_Some() && pre_no_leading_zero(c.pre.bytes@)))
}

/// Byte pattern of the op span (mirroring op()'s 8-state recognition; m = the right-open boundary consumed).
pub open spec fn op_span_match(input: Seq<u8>, k: int, m: int, op: Op, default_op: bool) -> bool {
    (m == k + 1 && ((op == Op::Exact && input.len() > k && input[k] == 0x3d)
        || (op == Op::Greater
            && input.len() > k
            && input[k] == 0x3e
            && (k + 1 >= input.len() || input[k + 1] != 0x3d))
        || (op == Op::Less
            && input.len() > k
            && input[k] == 0x3c
            && (k + 1 >= input.len() || input[k + 1] != 0x3d))
        || (op == Op::Tilde && input.len() > k && input[k] == 0x7e)
        || (op == Op::Caret && input.len() > k && input[k] == 0x5e)))
        || (m == k + 2 && ((op == Op::GreaterEq && input.len() > k + 1 && input[k] == 0x3e && input[k + 1] == 0x3d)
            || (op == Op::LessEq
                && input.len() > k + 1
                && input[k] == 0x3c
                && input[k + 1] == 0x3d)))
        || (m == k
            && default_op
            && op == Op::Caret
            && (k == input.len()
                || (input[k] != 0x3d
                    && input[k] != 0x3e
                    && input[k] != 0x3c
                    && input[k] != 0x7e
                    && input[k] != 0x5e)))
}

/// VersionReq::parse Ok contract:
/// - non-wildcard path: 1 <= comparator count <= 32 (MAX_COMPARATORS-1), each
///   comparator structurally legal; wildcard = empty comparators;
/// - pure wildcard (%) STAR form: input = leading spaces + one of */x/X (the from_str wildcard gate).
pub open spec fn req_ok_spec(input: Seq<u8>, comps: Seq<Comparator>) -> bool {
    (comps.len() == 0
        ==> exists|k: int|
            0 <= k + 1 == input.len() && (forall|i: int| 0 <= i < k ==> input[i] == 0x20)
                && (input[k] == 0x2a || input[k] == 0x78 || input[k] == 0x58))
    && (comps.len() > 0
        ==> (1 <= comps.len() && comps.len() <= 0x20
            && forall|i: int| 0 <= i < comps.len() ==> #[trigger] comp_struct_ok(comps[i])))
}

/* ---------- byte-predicate exec layer ---------- */

/// Origin Rust: `is_ascii_digit()` etc. (the three ident-segment character predicates in one).
pub(crate) exec fn is_ident_char_utf(b: u8) -> (r: bool)
    ensures
        r == ident_char(b),
{
    (b >= 0x30 && b <= 0x39) || (b >= 0x41 && b <= 0x5a) || (b >= 0x61 && b <= 0x7a) || b == 0x2d
}

exec fn is_digit_exec(b: u8) -> (r: bool)
    ensures
        r == is_digit(b),
{
    b >= 0x30 && b <= 0x39
}

exec fn is_ident_char_exec(b: u8) -> (r: bool)
    ensures
        r == ident_char(b),
{
    (b >= 0x30 && b <= 0x39) || (b >= 0x41 && b <= 0x5a) || (b >= 0x61 && b <= 0x7a) || b == 0x2d
}

pub open spec fn is_wildcard_byte(b: u8) -> bool {
    b == 0x2a || b == 0x78 || b == 0x58
}

pub(crate) exec fn is_wildcard_exec(b: u8) -> (r: bool)
    ensures
        r == is_wildcard_byte(b),
{
    b == 0x2a || b == 0x78 || b == 0x58
}

pub open spec fn is_space(b: u8) -> bool {
    b == 0x20
}

pub open spec fn space_prefix_only(s: Seq<u8>, n: int) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] is_space(s[i])
}

/// Origin Rust: the byte expansion of `text.trim_start_matches(' ')`.
pub(crate) exec fn trim_spaces(input: &[u8]) -> (r: &[u8])
    ensures
        exists|n: int|
            0 <= n <= input.len() && r@ == input@[n..] && space_prefix_only(input@, n)
                && (n == input.len() || !is_space(input@[n])),
{
    let mut i: usize = 0;
    while i < input.len() && input[i] == 0x20
        invariant
            i <= input.len(),
            space_prefix_only(input@, i as int),
        decreases
            input.len() - i,
    {
        i += 1;
    }
    &input[i..]
}

/* ======================================================================
 * numeric_identifier -- parse.rs:156-184
 * ====================================================================== */


pub fn numeric_identifier(input: &[u8], pos: Position) -> (r: Result<(u64, &[u8]), Error>)
    ensures
        match r {
            Ok((value, rest)) => {
                &&& 0 <= rest@.len()
                &&& 1 <= input.len() - rest@.len()
                &&& digits_only(input@[..(input.len() - rest@.len())])
                &&& (input.len() - rest@.len() == 1 || input@[0] != 0x30)
                &&& value == num_str_value(input@, input.len() - rest@.len())
                &&& (value as int) <= 0xffff_ffff_ffff_ffff
                &&& (rest@.len() == 0 || !is_digit(input@[(input.len() - rest@.len()) as int]))
                &&& rest@ == input@[(input.len() - rest@.len()) as int..]
            },
            Err(e) => (input.len() == 0
                && ek_num(e.kind) == ek_num(ErrorKind::UnexpectedEnd(pos)))
                || (input.len() > 0
                    && !is_digit(input@[0])
                    && ek_num(e.kind) == ek_num(ErrorKind::UnexpectedChar(pos, input@[0])))
                || (input.len() > 1
                    && input@[0] == 0x30
                    && is_digit(input@[1])
                    && ek_num(e.kind) == ek_num(ErrorKind::LeadingZero(pos)))
                || (exists|n: int| {
                    &&& 1 <= n <= input.len()
                    &&& digits_only(input@[..n])
                    &&& (n == 1 || input@[0] != 0x30)
                    &&& num_str_value(input@, n) > 0xffff_ffff_ffff_ffff
                }),
        },
{
    let mut len: usize = 0;
    let mut value: u64 = 0;

    loop
        invariant
            len <= input.len(),
            forall|k: int| 0 <= k < len as int ==> #[trigger] is_digit(input@[k]),
            value == num_str_value(input@, len as int),
            value == 0 ==> len <= 1,
            len >= 2 ==> input@[0] != 0x30,
        decreases
            input.len() - len,
    {
        /* Origin Rust: while let Some(&digit) = input.as_bytes().get(len) { */
        if len >= input.len() {
            break;
        }
        let digit = input[len];

        /* Origin Rust: if digit < b'0' || digit > b'9' { break; } */
        if !is_digit_exec(digit) {
            break;
        }

        /* Origin Rust: if value == 0 && len > 0 {
         *     return Err(Error::new(ErrorKind::LeadingZero(pos)));
         * } */
        if value == 0 && len > 0 {
            proof {
                lemma_zero_value(input@, len as int);
                assert(len == 1);
                assert(input@[0] == 0x30);
                assert(input.len() >= 2 && is_digit(input@[1]));
            }
            return Err(Error::new(ErrorKind::LeadingZero(pos)));
        }

        /* Origin Rust: match value.checked_mul(10)
         *     .and_then(|value| value.checked_add((digit - b'0') as u64)) --
         * the same overflow semantics rewritten as a bound check */
        let digit_val = (digit - 0x30) as u64;
        if value > 0xffff_ffff_ffff_ffff / 10 {
            proof {
                lemma_num_overflow_hi(input@, len as int, value);
            }
            return Err(Error::new(ErrorKind::Overflow(pos)));
        }
        let scaled = value * 10;
        if scaled > 0xffff_ffff_ffff_ffff - digit_val {
            proof {
                lemma_num_overflow_add(input@, len as int, value, digit_val);
            }
            return Err(Error::new(ErrorKind::Overflow(pos)));
        }
        let ghost old_value = value;
        value = scaled + digit_val;
        proof {
            lemma_num_extend(input@, len as int);
            // the LeadingZero gate did not fire: the old value is nonzero (when len>=1)
            assert(old_value != 0 || len == 0);
        }
        len += 1;
    }

    if len > 0 {
        proof {
            lemma_digits_prefix(input@, len as int);
        }
        Ok((value, &input[len..]))
    } else {
        /* Origin Rust: } else if let Some(unexpected) = input[len..].chars().next() { ... } */
        if input.len() > 0 {
            Err(Error::new(ErrorKind::UnexpectedChar(pos, input[0])))
        } else {
            Err(Error::new(ErrorKind::UnexpectedEnd(pos)))
        }
    }
}

/* ======================================================================
 * wildcard -- parse.rs:186-196 / op -- parse.rs:262-285 / dot -- parse.rs:198-206
 * ====================================================================== */

/// Origin Rust: fn wildcard(input: &str) -> Option<(char, &str)>
pub fn wildcard(input: &[u8]) -> (r: Option<(u8, &[u8])>)
    ensures
        match r {
            None => input.len() == 0 || !is_wildcard_byte(input@[0]),
            Some((c, rest)) => input.len() >= 1
                && is_wildcard_byte(input@[0])
                && c == input@[0]
                && rest@ == input@[1..],
        },
{
    if input.len() > 0 && is_wildcard_exec(input[0]) {
        Some((input[0], &input[1..]))
    } else {
        None
    }
}

/// Origin Rust: fn op(input: &str) -> (Op, &str)
/// (the default_op boolean is exposed with the return value, to keep `^` apart
///     from the default op; Op::DEFAULT = Op::Caret, parse.rs:152-154)
pub fn op(input: &[u8]) -> (r: (Op, &[u8], bool))
    ensures
        op_span_match(input@, 0, input.len() - r.1.len(), r.0, r.2)
        && (r.2 == (input.len() == r.1.len()))
        && (r.2 ==> r.0 == Op::Caret),
{
    if input.len() > 0 && input[0] == 0x3d {
        (Op::Exact, &input[1..], false)
    } else if input.len() > 0 && input[0] == 0x3e {
        if input.len() > 1 && input[1] == 0x3d {
            (Op::GreaterEq, &input[2..], false)
        } else {
            (Op::Greater, &input[1..], false)
        }
    } else if input.len() > 0 && input[0] == 0x3c {
        if input.len() > 1 && input[1] == 0x3d {
            (Op::LessEq, &input[2..], false)
        } else {
            (Op::Less, &input[1..], false)
        }
    } else if input.len() > 0 && input[0] == 0x7e {
        (Op::Tilde, &input[1..], false)
    } else if input.len() > 0 && input[0] == 0x5e {
        (Op::Caret, &input[1..], false)
    } else {
        /* Origin Rust: (Op::DEFAULT, input) */
        (Op::Caret, input, true)
    }
}

/// Origin Rust: fn dot(input: &str, pos: Position) -> Result<&str, Error>
pub fn dot(input: &[u8], pos: Position) -> (r: Result<&[u8], Error>)
    ensures
        match r {
            Ok(rest) => input.len() >= 1
                && input@[0] == 0x2e
                && rest@ == input@[1..],
            Err(e) => if input.len() == 0 {
                ek_num(e.kind) == ek_num(ErrorKind::UnexpectedEnd(pos))
            } else {
                input@[0] != 0x2e
                    && ek_num(e.kind) == ek_num(ErrorKind::UnexpectedCharAfter(pos, input@[0]))
            },
        },
{
    if input.len() > 0 && input[0] == 0x2e {
        Ok(&input[1..])
    } else if input.len() > 0 {
        Err(Error::new(ErrorKind::UnexpectedCharAfter(pos, input[0])))
    } else {
        Err(Error::new(ErrorKind::UnexpectedEnd(pos)))
    }
}

/* ======================================================================
 * identifier -- parse.rs:220-260 (the pre/build segment-scan state machine)
 * ====================================================================== */

/// Full-decomposition carrier for Ok (all exists variables inside a single trigger predicate).
pub open spec fn ident_ok_split(
    input: Seq<u8>,
    string: Seq<u8>,
    rest: Seq<u8>,
    n: int,
    pos: Position,
) -> bool {
    &&& 0 <= n <= input.len()
    &&& string == input[..n]
    &&& rest == input[n..]
    &&& ident_lang_valid(string)
    &&& (pos == Position::Pre ==> pre_no_leading_zero(string))
    &&& (n == 0
        ==> (input.len() == 0 || (!ident_char(input[0]) && input[0] != 0x2e)))
    &&& (n > 0
        ==> (n == input.len() || (!ident_char(input[n]) && input[n] != 0x2e)))
}

/// Origin Rust: fn identifier(input: &str, pos: Position) -> Result<(&str, &str), Error>
///
/// Full Ok decomposition (the Prerelease/BuildMetadata Syntax doc): the returned
/// string = a grammar-legal identifier string (byte domain / non-empty
/// segments / no trailing dot), plus on the Pre side no leading-zero digit
/// segments (the complement of LeadingZero); the two Err classes (EmptySegment
/// / Pre's LeadingZero) carry the necessary-condition direction (patterns:
/// dot_empty_pattern / the prefix leading-zero violation).
pub fn identifier(input: &[u8], pos: Position) -> (r: Result<(&[u8], &[u8]), Error>)
    ensures
        match r {
            Ok((string, rest)) => exists|n: int|
                #![trigger ident_ok_split(input@, string@, rest@, n, pos)]
                ident_ok_split(input@, string@, rest@, n, pos),
            Err(e) => if ek_num(e.kind) == ek_num(ErrorKind::EmptySegment(pos)) {
                dot_empty_pattern(input@)
            } else {
                pos == Position::Pre
                    && ek_num(e.kind) == ek_num(ErrorKind::LeadingZero(pos))
                    && (exists|n: int|
                        #![trigger nolead_prefix(input@, n)]
                        nolead_prefix(input@, n))
            },
        },
{
    let mut accumulated_len: usize = 0;
    let mut segment_len: usize = 0;
    let mut segment_has_nondigit: bool = false;

    loop
        invariant
            accumulated_len + segment_len <= input.len(),
            // consumed-prefix byte domain + segment structure (pairwise form;
            // a mid-state that allows a trailing '.')
            forall|k: int|
                #![trigger no_dot_here(input@, k, accumulated_len as int)]
                no_dot_here(input@, k, accumulated_len as int),
            accumulated_len == 0 || input@[accumulated_len as int - 1] == 0x2e,
            // bytes of the current segment (non-'.')
            forall|k: int|
                accumulated_len as int <= k < (accumulated_len + segment_len) as int ==>
                    #[trigger] ident_char(input@[k]),
            // !has_nondigit <=> the segment is all digits (the state folding of upstream bytes().all)
            !segment_has_nondigit
                == (forall|k: int|
                    accumulated_len as int <= k < (accumulated_len + segment_len) as int ==>
                        #[trigger] is_digit(input@[k])),
            // Pre side: completed segments and the extended segment start have
            // no leading zero (in the nolead_seg_bad sense)
            forall|i: int|
                #![trigger nolead_seg_bad(input@, i)]
                0 <= i < accumulated_len as int
                    && (i == 0 || input@[i - 1] == 0x2e) ==> !nolead_seg_bad(input@, i),
        decreases
            input.len() - accumulated_len - segment_len,
    {
        let frontier = accumulated_len + segment_len;
        let boundary: Option<u8> = if frontier < input.len() {
            Some(input[frontier])
        } else {
            None
        };

        /* Origin Rust: match input.as_bytes().get(accumulated_len + segment_len) {
         *     Some(b'A'..=b'Z') | Some(b'a'..=b'z') | Some(b'-') => { ... }  */
        if let Some(b) = boundary {
            if is_ident_char_utf(b) && !is_digit_exec(b) {
                segment_len += 1;
                segment_has_nondigit = true;
                continue;
            }
            if is_digit_exec(b) {
                segment_len += 1;
                continue;
            }
        }

        /* boundary branches (None / non-segment character) */
        if segment_len == 0 {
            if accumulated_len == 0 && boundary != Some(0x2e) {
                proof {
                    assert(Seq::<u8>::empty() == input@[..0]);
                    assert(input@ == input@[0..]);
                    assert(ident_lang_valid(Seq::<u8>::empty()));
                    assert(0 <= input.len());
                    if input.len() > 0 {
                        let b = input@[0];
                        assert(b != 0x2e);
                        assert(!ident_char(input@[0]));
                    }
                    assert(ident_ok_split(input@, Seq::<u8>::empty(), input@, 0, pos));
                }
                return Ok((&input[..0], input));
            } else {
                proof {
                    assert(dot_empty_pattern(input@)) by {
                        if boundary == Some(0x2e) {
                            assert(0 <= 0 && 0 < input.len() && input@[0] == 0x2e);
                        } else {
                            assert(input.len() > 0);
                            let i = input.len() - 1;
                            assert(0 <= i < input.len() && input@[i] == 0x2e);
                            assert(i == 0 || i + 1 == input.len());
                        }
                    }
                }
                return Err(Error::new(ErrorKind::EmptySegment(pos)));
            }
        }

        /* Origin Rust: if pos == Position::Pre && segment_len > 1
         *     && !segment_has_nondigit && input[accumulated_len..].starts_with('0')*
         * (the exec side disambiguates the enum with a match, cf. the eval.rs ledger) */
        let pos_is_pre = match pos {
            Position::Pre => true,
            _ => false,
        };
        if pos_is_pre
            && segment_len > 1
            && !segment_has_nondigit
            && input[accumulated_len] == 0x30
        {
            return Err(Error::new(ErrorKind::LeadingZero(pos)));
        }

        /* Origin Rust: accumulated_len += segment_len;
         * if boundary == Some(&b'.') { accumulated_len += 1; segment_len = 0; ... } */
        accumulated_len += segment_len;
        if boundary == Some(0x2e) {
            accumulated_len += 1;
            segment_len = 0;
            segment_has_nondigit = false;
        } else {
            return Ok((&input[..accumulated_len], &input[accumulated_len..]));
        }
    }
}

/* ======================================================================
 * prerelease_identifier / build_identifier -- parse.rs:208-218
 * and the FromStr faces -- parse.rs:122-144 (the unsafe Identifier -> Vec model)
 * ====================================================================== */

pub(crate) fn clone_bytes(string: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == string@,
{
    let mut out: Vec<u8> = Vec::new();
    let ghost s = string@;
    let mut i: usize = 0;
    while i < string.len()
        invariant
            0 <= i <= string@.len(),
            s == string@,
            out@.len() == i,
            forall|j: int| 0 <= j < out@.len() ==> out@[j] == s[j],
        decreases
            string.len() - i,
    {
        out.push(string[i]);
        i += 1;
    }
    proof {
        assert(i == string@.len());
        assert(out@.len() == s.len());
    }
    out
}

/// Origin Rust: fn prerelease_identifier(input) -> Result<(Prerelease, &str), Error>
///     (the unsafe { Identifier::new_unchecked(string) } is absorbed by the model)
fn prerelease_identifier(input: &[u8]) -> (r: Result<(Prerelease, &[u8]), Error>)
    ensures
        match r {
            Ok((p, rest)) => exists|n: int|
                #![trigger pre_ok_split(input@, p.bytes@, rest@, n)]
                pre_ok_split(input@, p.bytes@, rest@, n),
            Err(e) => true,
        },
{
    match identifier(input, Position::Pre) {
        Ok((string, rest)) => {
            let pre = Prerelease {
                bytes: clone_bytes(string),
            };
            Ok((pre, rest))
        }
        Err(e) => Err(e),
    }
}

/// Carrier of the Prerelease Ok shape (n = string length; grammar-legal + no leading zeros on the Pre side).
pub open spec fn pre_ok_split(
    input: Seq<u8>,
    pre: Seq<u8>,
    rest: Seq<u8>,
    n: int,
) -> bool {
    &&& 0 <= n <= input.len()
    &&& pre == input[..n]
    &&& rest == input[n..]
    &&& ident_lang_valid(pre)
    &&& pre_no_leading_zero(pre)
}

fn build_identifier(input: &[u8]) -> (r: Result<(BuildMetadata, &[u8]), Error>)
    ensures
        match r {
            Ok((b, rest)) => exists|n: int|
                #![trigger pre_ok_split(input@, b.bytes@, rest@, n)]
                pre_ok_split(input@, b.bytes@, rest@, n),
            Err(e) => true,
        },
{
    match identifier(input, Position::Build) {
        Ok((string, rest)) => {
            let build = BuildMetadata {
                bytes: clone_bytes(string),
            };
            Ok((build, rest))
        }
        Err(e) => Err(e),
    }
}

/// Origin Rust: impl FromStr for Prerelease (parse.rs:122-132)
pub fn prerelease_from_str(input: &[u8]) -> (r: Result<Prerelease, Error>)
    ensures
        match r {
            Ok(p) => p.bytes@ == input@ && ident_lang_valid(input@)
                && pre_no_leading_zero(input@),
            Err(e) => if ek_num(e.kind) == ek_num(ErrorKind::IllegalCharacter(Position::Pre)) {
                exists|i: int|
                    #![trigger foreign_byte(input@, i)]
                    foreign_byte(input@, i)
            } else if ek_num(e.kind) == ek_num(ErrorKind::EmptySegment(Position::Pre)) {
                dot_empty_pattern(input@)
            } else {
                ek_num(e.kind) == ek_num(ErrorKind::LeadingZero(Position::Pre))
                    && (exists|n: int|
                        #![trigger nolead_prefix(input@, n)]
                        nolead_prefix(input@, n))
            },
        },
{
    /* Origin Rust: let (pre, rest) = prerelease_identifier(text)?;
     * if !rest.is_empty() { return Err(Error::new(ErrorKind::IllegalCharacter(
     *     Position::Pre))); } */
    let (pre, rest) = match prerelease_identifier(input) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    if rest.len() > 0 {
        proof {
            assert(foreign_byte(input@, input.len() - rest.len() as int));
        }
        return Err(Error::new(ErrorKind::IllegalCharacter(Position::Pre)));
    }
    Ok(pre)
}

/// Origin Rust: impl FromStr for BuildMetadata (parse.rs:134-144)
pub fn build_from_str(input: &[u8]) -> (r: Result<BuildMetadata, Error>)
    ensures
        match r {
            Ok(b) => b.bytes@ == input@ && ident_lang_valid(input@),
            Err(e) => if ek_num(e.kind) == ek_num(ErrorKind::IllegalCharacter(Position::Build)) {
                exists|i: int|
                    #![trigger foreign_byte(input@, i)]
                    foreign_byte(input@, i)
            } else {
                ek_num(e.kind) == ek_num(ErrorKind::EmptySegment(Position::Build))
                    && dot_empty_pattern(input@)
            },
        },
{
    let (build, rest) = match build_identifier(input) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    if rest.len() > 0 {
        proof {
            assert(foreign_byte(input@, input.len() - rest.len() as int));
        }
        return Err(Error::new(ErrorKind::IllegalCharacter(Position::Build)));
    }
    Ok(build)
}

/* ======================================================================
 * Version FromStr -- parse.rs:25-82
 * ====================================================================== */

/// Origin Rust: impl FromStr for Version::from_str (parse.rs:28-81)
///
/// Ok goes through `ver_ok` (the L2 full syntactic decomposition); Err pins
/// Empty <=> empty input (the first doc Errors entry); the remaining error
/// classes are pinned by harness example theorems.
pub fn version_from_str(input: &[u8]) -> (r: Result<Version, Error>)
    ensures
        match r {
            Ok(v) => ver_ok(input@, v),
            Err(e) => ((input.len() == 0) == (ek_num(e.kind) == ek_num(ErrorKind::Empty))),
        },
{
    /* Origin Rust: if text.is_empty() { return Err(Error::new(ErrorKind::Empty)); } */
    if input.len() == 0 {
        return Err(Error::new(ErrorKind::Empty));
    }

    let mut pos = Position::Major;
    let (major, text) = match numeric_identifier(input, pos) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    let text = match dot(text, pos) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };

    pos = Position::Minor;
    let (minor, text) = match numeric_identifier(text, pos) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    let text = match dot(text, pos) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };

    pos = Position::Patch;
    let (patch, text) = match numeric_identifier(text, pos) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };

    /* Origin Rust: if text.is_empty() { return Ok(Version::new(major, minor, patch)); } */
    if text.len() == 0 {
        let v = Version {
            major,
            minor,
            patch,
            pre: Prerelease {
                bytes: Vec::new(),
            },
            build: BuildMetadata {
                bytes: Vec::new(),
            },
        };
        return Ok(v);
    }

    /* Origin Rust: let (pre, text) = if let Some(text) = text.strip_prefix('-') { ... } */
    let (pre, text): (Prerelease, &[u8]) = if text[0] == 0x2d {
        pos = Position::Pre;
        let (pre, text) = match prerelease_identifier(&text[1..]) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        /*
         * Origin Rust: if pre.is_empty() { return Err(Error::new(ErrorKind::EmptySegment(pos))); }
         */
        if pre.is_empty() {
            return Err(Error::new(ErrorKind::EmptySegment(pos)));
        }
        (pre, text)
    } else {
        (Prerelease { bytes: Vec::new() }, text)
    };

    /* Origin Rust: let (build, text) = if let Some(text) = text.strip_prefix('+') { ... } */
    let (build, text): (BuildMetadata, &[u8]) = if text.len() > 0 && text[0] == 0x2b {
        pos = Position::Build;
        let (build, text) = match build_identifier(&text[1..]) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        /* Origin Rust: if build.is_empty() { return Err(...EmptySegment(pos)); } */
        if build.is_empty() {
            return Err(Error::new(ErrorKind::EmptySegment(pos)));
        }
        (build, text)
    } else {
        (BuildMetadata { bytes: Vec::new() }, text)
    };

    /* Origin Rust: if let Some(unexpected) = text.chars().next() {
     *     return Err(Error::new(ErrorKind::UnexpectedCharAfter(pos, unexpected))); } */
    if text.len() > 0 {
        return Err(Error::new(ErrorKind::UnexpectedCharAfter(pos, text[0])));
    }

    let v = Version {
        major,
        minor,
        patch,
        pre,
        build,
    };
    Ok(v)
}

/* ======================================================================
 * comparator -- parse.rs:287-364 / version_req -- parse.rs:366-404
 * ====================================================================== */

/// Full-decomposition carrier for Comparator Ok (all exists variables triggered).
pub open spec fn cmp_ok_split(
    input: Seq<u8>,
    c: Comparator,
    rest: Seq<u8>,
    op_end: int,
    sp: int,
    n1: int,
    n: int,
) -> bool {
    &&& 0 <= op_end <= sp <= n1 <= n <= input.len()
    &&& op_span_match(input, 0, op_end, c.op, op_end == 0)
    &&& space_prefix_only(input[op_end..sp], sp - op_end)
    &&& (sp == input.len() || !is_space(input[sp]))
    &&& (n1 == sp || (n1 > sp && is_num_at(input, sp, n1, c.major as int)
        && (n1 == input.len() || !is_digit(input[n1]))))
    &&& rest == input[n..]
    &&& (n == input.len() || !is_space(input[n]))
    &&& comp_struct_ok(c)
    &&& (c.minor.is_Some() ==>
        (exists|m_end: int|
            #![trigger is_num_at(input, n1 + 1, m_end, c.minor.unwrap() as int)]
            n1 + 1 < m_end <= input.len()
                && input[n1] == 0x2e
                && is_num_at(input, n1 + 1, m_end, c.minor.unwrap() as int)))
    &&& (c.minor.is_None() ==>
        (n1 == input.len() || input[n1] != 0x2e || is_wildcard_byte(input[n1 + 1])))
    &&& (c.patch.is_Some() ==>
        (exists|p_end: int, m_end: int|
            #![trigger is_num_at(input, m_end, p_end, c.patch.unwrap() as int)]
            m_end < p_end <= input.len()
                && input[m_end] == 0x2e
                && is_num_at(input, m_end, p_end, c.patch.unwrap() as int)))
    &&& (c.pre.bytes@.len() > 0
        ==> (ident_lang_valid(c.pre.bytes@) && pre_no_leading_zero(c.pre.bytes@)))
}

/// Origin Rust: fn comparator(input: &str) -> Result<(Comparator, Position, &str), Error>
///
/// Contract: the op byte pattern (op_span_match in all its tense-states) + the major
/// position decomposition (is_num_at) + the Comparator structural invariant
/// (comp_struct_ok) + the minor/patch/pre/build semantic anchors and the rest tail (after the trim).
pub fn comparator(input: &[u8]) -> (r: Result<(Comparator, Position, &[u8]), Error>)
    ensures
        match r {
            Ok((c, p, rest)) => exists|op_end: int, sp: int, n1: int, n: int|
                #![trigger cmp_ok_split(input@, c, rest@, op_end, sp, n1, n)]
                cmp_ok_split(input@, c, rest@, op_end, sp, n1, n),
            Err(e) => ek_num(e.kind) == ek_num(ErrorKind::UnexpectedEnd(Position::Major))
                || ek_num(e.kind) == ek_num(ErrorKind::UnexpectedChar(Position::Major, 0))
                || ek_num(e.kind) == ek_num(ErrorKind::LeadingZero(Position::Major))
                || ek_num(e.kind) == ek_num(ErrorKind::Overflow(Position::Major))
                || ek_num(e.kind) == ek_num(ErrorKind::UnexpectedAfterWildcard)
                || ek_num(e.kind) == ek_num(ErrorKind::EmptySegment(Position::Pre))
                || ek_num(e.kind) == ek_num(ErrorKind::LeadingZero(Position::Pre)),
        },
{
    /* Origin Rust: let (mut op, text) = op(input);
     * let default_op = input.len() == text.len();
     * let text = text.trim_start_matches(' '); */
    let (mut op, text0, _) = op(input);
    let default_op = input.len() == text0.len();
    let text = trim_spaces(text0);

    let mut pos = Position::Major;
    let (major, text) = match numeric_identifier(text, pos) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    let mut has_wildcard = false;

    /* Origin Rust: let (minor, text) = if let Some(text) = text.strip_prefix('.') { ... } */
    let (minor, text): (Option<u64>, &[u8]) = if text.len() > 0 && text[0] == 0x2e {
        pos = Position::Minor;
        if let Some((_, t)) = wildcard(&text[1..]) {
            has_wildcard = true;
            if default_op {
                op = Op::Wildcard;
            }
            (None, t)
        } else {
            let (minor, t) = match numeric_identifier(&text[1..], pos) {
                Ok(x) => x,
                Err(e) => return Err(e),
            };
            (Some(minor), t)
        }
    } else {
        (None, text)
    };

    /* Origin Rust: let (patch, text) = if let Some(text) = text.strip_prefix('.') { ... } */
    let (patch, text): (Option<u64>, &[u8]) = if text.len() > 0 && text[0] == 0x2e {
        pos = Position::Patch;
        if let Some((_, t)) = wildcard(&text[1..]) {
            if default_op {
                op = Op::Wildcard;
            }
            (None, t)
        } else if has_wildcard {
            return Err(Error::new(ErrorKind::UnexpectedAfterWildcard));
        } else {
            let (patch, t) = match numeric_identifier(&text[1..], pos) {
                Ok(x) => x,
                Err(e) => return Err(e),
            };
            (Some(patch), t)
        }
    } else {
        (None, text)
    };

    /* Origin Rust: let (pre, text) = if patch.is_some() && text.starts_with('-') { ... } */
    let (pre, text): (Prerelease, &[u8]) = if patch.is_some() && text.len() > 0 && text[0] == 0x2d {
        pos = Position::Pre;
        let (pre, t) = match prerelease_identifier(&text[1..]) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        if pre.is_empty() {
            return Err(Error::new(ErrorKind::EmptySegment(pos)));
        }
        (pre, t)
    } else {
        (Prerelease { bytes: Vec::new() }, text)
    };

    /* Origin Rust: let text = if patch.is_some() && text.starts_with('+') { ... } */
    let text: &[u8] = if patch.is_some() && text.len() > 0 && text[0] == 0x2b {
        pos = Position::Build;
        let (build, t) = match build_identifier(&text[1..]) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        if build.is_empty() {
            return Err(Error::new(ErrorKind::EmptySegment(pos)));
        }
        t
    } else {
        text
    };

    /* Origin Rust: let text = text.trim_start_matches(' ');
     * let comparator = Comparator { op, major, minor, patch, pre };
     * Ok((comparator, pos, text)) */
    let text = trim_spaces(text);
    let comparator = Comparator {
        op,
        major,
        minor,
        patch,
        pre,
    };
    Ok((comparator, pos, text))
}

/* ======================================================================
 * Comparator FromStr -- parse.rs:108-120
 * ====================================================================== */

/// Origin Rust: impl FromStr for Comparator::from_str (parse.rs:111-119)
pub fn comparator_from_str(input: &[u8]) -> (r: Result<Comparator, Error>)
    ensures
        match r {
            Ok(c) => comp_struct_ok(c),
            Err(e) => true,
        },
{
    /* Origin Rust: let text = text.trim_start_matches(' '); */
    let text = trim_spaces(input);
    let (comparator, _pos, rest) = match comparator(text) {
        Ok(x) => x,
        Err(e) => return Err(e),
    };
    /* Origin Rust: if !rest.is_empty() { let unexpected = rest.chars().next().unwrap();
     *     return Err(Error::new(ErrorKind::UnexpectedCharAfter(pos, unexpected))); } */
    if rest.len() > 0 {
        return Err(Error::new(ErrorKind::UnexpectedCharAfter(_pos, rest[0])));
    }
    Ok(comparator)
}

/* ======================================================================
 * version_req -- parse.rs:366-404 (the stack-write technique -> the Vec-assembly recursion)
 * ====================================================================== */

const MAX_COMPARATORS: usize = 32;

/// Origin Rust: fn version_req(input, out, depth) -> Result<usize, Error>
///
/// The stack-write technique (`out.reserve_exact(depth+1)` + `set_len` + `as_mut_ptr().add
/// (depth).write`) is rewritten: a recursion returning an assembled Vec (in parse order);
/// the error-rewrite branch (the wildcard error kind rewrite) and the
/// limit of 32 are preserved verbatim.
fn version_req_rec(input: &[u8], depth: usize) -> (r: Result<Vec<Comparator>, Error>)
    requires
        depth < MAX_COMPARATORS,
    ensures
        match r {
            Ok(v) => v@.len() >= 1
                && v@.len() + depth <= MAX_COMPARATORS
                && (forall|i: int|
                    0 <= i < v@.len() ==> #[trigger] comp_struct_ok(v@[i])),
            Err(e) => true,
        },
    decreases
        input.len(),
{
    let (comparator, pos, text) = match comparator(input) {
        Ok(x) => x,
        Err(mut error) => {
            /* Origin Rust: Err(mut error) => {
             *     if let Some((ch, mut rest)) = wildcard(input) {
             *         rest = rest.trim_start_matches(' ');
             *         if rest.is_empty() || rest.starts_with(',') {
             *             error.kind = ErrorKind::WildcardNotTheOnlyComparator(ch);
             *         }
             *     }
             *     return Err(error);
             * } */
            if let Some((ch, rest)) = wildcard(input) {
                let rest = trim_spaces(rest);
                if rest.len() == 0 || (rest.len() > 0 && rest[0] == 0x2c) {
                    error.kind = ErrorKind::WildcardNotTheOnlyComparator(ch);
                }
            }
            return Err(error);
        }
    };

    /* Origin Rust: if text.is_empty() {
     *     out.reserve_exact(depth + 1);
     *     unsafe { out.as_mut_ptr().add(depth).write(comparator) }
     *     return Ok(depth + 1);
     * } -- rewritten as a one-element Vec (the len obligation = the deep push of depth+1) */
    if text.len() == 0 {
        let mut out: Vec<Comparator> = Vec::new();
        out.push(comparator);
        return Ok(out);
    }

    /* Origin Rust: let text = if let Some(text) = text.strip_prefix(',') {
     *     text.trim_start_matches(' ')
     * } else {
     *     let unexpected = text.chars().next();
     *     return Err(Error::new(ErrorKind::ExpectedCommaFound(pos, unexpected)));
     * }; */
    let text = if text[0] == 0x2c {
        trim_spaces(&text[1..])
    } else {
        return Err(Error::new(ErrorKind::ExpectedCommaFound(pos, text[0])));
    };

    /* Origin Rust: if depth + 1 == MAX_COMPARATORS {
     *     return Err(Error::new(ErrorKind::ExcessiveComparators));
     * } */
    if depth + 1 == MAX_COMPARATORS {
        return Err(Error::new(ErrorKind::ExcessiveComparators));
    }

    /* Origin Rust: let len = version_req(text, out, depth + 1)?;
     * unsafe { out.as_mut_ptr().add(depth).write(comparator) }
     * Ok(len) -- rewritten as "reverse assembly + one final top-level reversal":
     * the reverse of the subtree parse order [curr, x1, x2] =
     * recursion-subtree-reversed ++ [curr], appending owned values throughout,
     * which sidesteps the Vec index-move forbidden zone. */
    let mut rev_tail: Vec<Comparator> = match version_req_rec(text, depth + 1) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    rev_tail.push(comparator);
    Ok(rev_tail)
}

/// Reversed Vec -> parse order (a loop moving owned values via pop).
fn reverse_comparators(rev: Vec<Comparator>, total: usize) -> (r: Vec<Comparator>)
    requires
        total == rev.len(),
    ensures
        r@.len() == total as int,
{
    let mut src: Vec<Comparator> = rev;
    let mut dst: Vec<Comparator> = Vec::new();
    while src.len() > 0
        decreases
            src.len(),
    {
        if let Some(c) = src.pop() {
            dst.push(c);
        }
    }
    dst
}

/// Origin Rust: impl FromStr for VersionReq (parse.rs:87-105)
pub fn version_req_from_str(input: &[u8]) -> (r: Result<VersionReq, Error>)
    ensures
        match r {
            Ok(req) => req_ok_spec(input@, req.comparators@),
            Err(e) => (ek_num(e.kind)
                == ek_num(ErrorKind::WildcardNotTheOnlyComparator(0)) ==>
                    (ek_char(e.kind) == 0x2a
                        || ek_char(e.kind) == 0x78
                        || ek_char(e.kind) == 0x58)),
        },
{
    /* Origin Rust: let text = text.trim_start_matches(' '); */
    let text = trim_spaces(input);

    /* Origin Rust: if let Some((ch, text)) = wildcard(text) { ... } -- the wildcard gate */
    if let Some((ch, t)) = wildcard(text) {
        let rest = trim_spaces(t);
        if rest.len() == 0 {
            return Ok(VersionReq {
                comparators: Vec::new(),
            });
        } else if rest[0] == 0x2c {
            return Err(Error::new(ErrorKind::WildcardNotTheOnlyComparator(ch)));
        } else {
            return Err(Error::new(ErrorKind::UnexpectedAfterWildcard));
        }
    }

    /* Origin Rust: let depth = 0; let mut comparators = Vec::new();
     * let len = version_req(text, &mut comparators, depth)?;
     * unsafe { comparators.set_len(len) } -- equivalent replacement by Vec assembly */
    match version_req_rec(text, 0) {
        Ok(comparators) => Ok(VersionReq { comparators }),
        Err(e) => Err(e),
    }
}

/* ======================================================================
 * Version::cmp_precedence -- the tuple-Ord expansion of lib.rs:466-471
 * ====================================================================== */

/// Lexicographic order of the `(major, minor, patch, &pre)` 4-tuple (the lib.rs
/// cmp_precedence doc: "Compare the major, minor, patch, and pre-release value
///   of two versions, disregarding build metadata."), relax ledger 4: Ordering -> Ord2.
pub open spec fn precedence_spec(
    a_maj: u64,
    a_min: u64,
    a_pat: u64,
    a_pre: Seq<u8>,
    b_maj: u64,
    b_min: u64,
    b_pat: u64,
    b_pre: Seq<u8>,
) -> Ord2 {
    if a_maj != b_maj {
        if a_maj < b_maj {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else if a_min != b_min {
        if a_min < b_min {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else if a_pat != b_pat {
        if a_pat < b_pat {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else {
        pre_cmp_spec_top(a_pre, b_pre)
    }
}

/// Origin Rust: Ord::cmp(&(self.major, self.minor, self.patch, &self.pre), &(...))
/// -- the tuple lexicographic order is expanded into three if-arms per Rust's Ord semantics.
pub fn cmp_precedence_model(
    a_maj: u64,
    a_min: u64,
    a_pat: u64,
    a_pre: &Prerelease,
    b_maj: u64,
    b_min: u64,
    b_pat: u64,
    b_pre: &Prerelease,
) -> (r: Ord2)
    ensures
        r == precedence_spec(a_maj, a_min, a_pat, a_pre.bytes@, b_maj, b_min, b_pat, b_pre.bytes@),
{
    if a_maj != b_maj {
        if a_maj < b_maj {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else if a_min != b_min {
        if a_min < b_min {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else if a_pat != b_pat {
        if a_pat < b_pat {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else {
        super::impls::pre_cmp(a_pre, b_pre)
    }
}


// ---------------------------------------------------------------------------
// Proof lemmas (machine-ground helpers for the numeric-identifier loop;
// measured: panels identical with the lemmas at this position)
// ---------------------------------------------------------------------------
/// Origin Rust: fn numeric_identifier(input: &str, pos: Position) -> Result<(u64, &str), Error>
///
/// (relax ledger 1: &str -> &[u8]). Doc contract (lib.rs Version::parse Errors):
/// the four precise classes leading zero / numeric overflow / non-digit
/// character / empty input; Ok's value = the prefix decimal value, no
/// leading zero, followed by a non-digit. A digit prefix of value 0 is all '0'
/// (the basis of the LeadingZero branch's contrapositive).
proof fn lemma_zero_value(input: Seq<u8>, n: int)
    requires
        0 <= n,
        forall|k: int| 0 <= k < n ==> #[trigger] is_digit(input[k]),
    ensures
        num_str_value(input, n) == 0 ==> (forall|k: int| 0 <= k < n ==> #[trigger] input[k] == 0x30),
    decreases
        n,
{
    if n > 0 {
        assert(forall|k: int| 0 <= k < n - 1 ==> is_digit(input[k]));
        lemma_zero_value(input, n - 1);
        if num_str_value(input, n) == 0 {
            assert(is_digit(input[n - 1]));
            assert(num_str_value(input, n - 1) == 0);
            assert(input[n - 1] == 0x30);
        }
    }
}

/// Flat digit quantifier <=> prefix digits_only (the index wiring into a subrange).
proof fn lemma_digits_prefix(input: Seq<u8>, n: int)
    requires
        0 <= n <= input.len(),
        forall|k: int| 0 <= k < n ==> #[trigger] is_digit(input[k]),
    ensures
        digits_only(input[..n]),
{
}

/// Single-step unfolding of num_str_value (the n+1-digit value = the n-digit value x10 + the current digit).
proof fn lemma_num_extend(input: Seq<u8>, n: int)
    requires
        0 <= n,
        n < input.len(),
        is_digit(input[n]),
    ensures
        num_str_value(input, n + 1) == num_str_value(input, n) * 10 + (input[n] - 0x30),
{
}

/// Overflow witness: a previous value above u64::MAX/10 => the n+1-digit value leaves the domain.
proof fn lemma_num_overflow_hi(input: Seq<u8>, n: int, value: u64)
    requires
        0 <= n,
        n < input.len(),
        is_digit(input[n]),
        value == num_str_value(input, n),
        value > 0xffff_ffff_ffff_ffffu64 / 10u64,
    ensures
        num_str_value(input, n + 1) > 0xffff_ffff_ffff_ffff,
{
    assert((0xffff_ffff_ffff_ffffu64) / 10u64 == 1844674407370955161u64);
    assert(value >= 1844674407370955162u64);
    assert((value as int) * 10 >= 18446744073709551620int);
    assert(num_str_value(input, n + 1) == (value as int) * 10 + (input[n] - 0x30));
}

/// Overflow witness: the tail addition leaves the domain (value*10 + digit > MAX).
proof fn lemma_num_overflow_add(input: Seq<u8>, n: int, value: u64, digit_val: u64)
    requires
        0 <= n,
        n < input.len(),
        is_digit(input[n]),
        value == num_str_value(input, n),
        digit_val == (input[n] - 0x30) as u64,
        value * 10 > 0xffff_ffff_ffff_ffff - digit_val,
    ensures
        num_str_value(input, n + 1) > 0xffff_ffff_ffff_ffff,
{
    assert((value as int) * 10 + (digit_val as int) >= 0);
}

} // verus!
