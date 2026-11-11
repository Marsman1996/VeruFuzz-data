//! `url` crate mirror -- src/parser.rs (first verus batch subset)
//!
//! Upstream: https://github.com/servo/rust-url (pin 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a)
//! crate root at `code/url/` (SUBDIR=url; code/ tree untouched).
//! This file is the same-name mirror of `src/parser.rs`, covering two strata:
//! (a) the scheme-classification face of the read API (`SchemeType`
//! parser.rs:158-183 with the `From<&str>` classifier, `default_port`
//! parser.rs:185-192), and (b) the byte-model parse machine of the parser
//! batch: the Input byte cursor (parser.rs:194-331 on the transcription
//! domain), to_u32/ParseError (parser.rs:1741-1748 and the error enum),
//! the percent-encoding set model (the AsciiSet constants parser.rs:19-45
//! mirrored as per-set byte predicates), the decimal/port writers
//! (fast_u16_to_str parser.rs:1796-1815 and the Ipv4Addr Display face),
//! parse_scheme (parser.rs:399-423) with its bidirectional split contract,
//! parse_port (parser.rs:1094-1128), and the query/fragment placement face
//! (parse_query_and_fragment parser.rs:1495-1522, parse_query
//! parser.rs:1524-1603, parse_fragment parser.rs:1625-1674).
//! The assembly continuation batch adds the crop algebra and the host-port
//! assembly: last_slash_can_be_removed/shorten_path/pop_path
//! (parser.rs:1356-1399) and the dot-segment match forms
//! (parser.rs:1240-1250), then parse_host_and_port (parser.rs:934-969) as
//! the scan / write / colon-port helper split (the monolithic assembly
//! exceeded the solver budget even at a 300-second rlimit, so the split
//! also isolates the range-view compositions in entry-pin lemmas). The
//! remaining state machine (parse_with_scheme/after_double_slash/
//! parse_file/parse_relative/parse_path/with_query_and_fragment,
//! parser.rs:425-1492 and 1605-1623) is the scanner-completion
//! continuation; the deep host faces (Host::parse_cow idna punycode,
//! parse_ipv6addr, host.rs:92-175 and 364-512) are the deep-host batch.
//!
//! Lossy-abstraction ledger:
//! 1. Upstream `impl<T: AsRef<str>> From<T> for SchemeType` matches on str
//!    literals; the mirror classifier takes the scheme's byte payload
//!    (`Seq<u8>` spec / `Vec<u8>` exec) and compares bytes (ASCII, the scheme
//!    grammar is ASCII by construction).
//! 2. The machine's transcription domain (`machine_domain`): every input
//!    byte is ASCII and not U+0009/U+000A/U+000D. Upstream `Input` filters
//!    those three on every `next()` (parser.rs:322-331) and the entry trim
//!    strips them (parser.rs:206-240), so a byte cursor is faithful on the
//!    domain; multibyte code points are outside (the whole-char encoding of
//!    `utf8_percent_encode` is the deep-water face with the host batch).
//! 3. The violation_fn logging arms (parser.rs:349-361, 1684-1695) and the
//!    query_encoding_override (the legacy HTML encoding selector,
//!    parser.rs:1582-1592) have no effect on the serialized value and are
//!    outside the verus surface; the Context::PathSegmentSetter variant
//!    exists in the enum and travels with the setters face.
//! 4. Independent proof helpers stay interleaved next to their users
//!    (machine_domain_subrange, rem_shift, enc_seq_split, seq_add_cancel_right,
//!    enc_prefix_next, pow10/dec_len): moving basket items across this file
//!    may flip the already-green obligations measured for the whole-machine
//!    panels (105v/87v/88v), so the file-tail grouping convention is
//!    measured-exempt here; the one rlimit raise is annotated at its site.

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

broadcast use {
    vstd::seq::group_seq_lemmas,
    vstd::slice::group_slice_axioms,
    vstd::std_specs::vec::group_vec_axioms,
};

/// Byte-payload equality against a fixed literal, usable in exec position
/// (spec `view() == seq![..]` comparisons are proof-only):
/// r is true iff the two byte payloads have identical content.
pub exec fn bytes_eq(s: &Vec<u8>, lit: &Vec<u8>) -> (r: bool)
    requires
        true,
    ensures
        r == (s.view() == lit.view()),
{
    if s.len() != lit.len() {
        proof {
            assert(s.view().len() != lit.view().len());
        }
        false
    } else {
        let ghost lv = lit.view();
        let ghost n = s.len() as int;
        let mut i: usize = 0;
        let mut acc = true;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == lit.len(),
                lv == lit.view(),
                n == s.view().len(),
                acc == (forall|j: int| 0 <= j < i as int ==> s.view()[j] == lv[j]),
            decreases s.len() - i
        {
            let x = s[i];
            let y = lit[i];
            proof {
                assert(s.view() == s.view()); // pin the view term
            }
            if x != y {
                proof {
                    assert(s.view()[i as int] == x);
                    assert(lv[i as int] == y);
                }
                acc = false;
            }
            i += 1;
        }
        proof {
            if acc {
                assert(s.view() == lv);
            }
        }
        acc
    }
}

/// Origin Rust: pub enum SchemeType { File, SpecialNotFile, NotSpecial }  (parser.rs:159-163)
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum SchemeType {
    File,
    SpecialNotFile,
    NotSpecial,
}

/// The recursive prefix form unpacks to the pointwise run face (used at
/// the count-matching seam of parse_with_scheme; one induction, then no
/// per-site fuel is needed).
pub proof fn slash_run_prefix_iff(s: Seq<u8>, k: int)
    requires
        0 <= k,
        k <= (s.len() as int),
    ensures
        slash_run_prefix(s, k)
            == (forall|j: int| 0 <= j && j < k
                ==> (s.index(j) == 0x2Fu8
                    || s.index(j) == 0x5Cu8)),
    decreases k,
{
    if k <= 0 {
        reveal_with_fuel(slash_run_prefix, 2);
        assert(slash_run_prefix(s, k));
    } else {
        slash_run_prefix_iff(s, k - 1);
        reveal_with_fuel(slash_run_prefix, 2);
        assert(slash_run_prefix(s, k)
            == (slash_run_prefix(s, k - 1)
                && (s.index(k - 1) == 0x2Fu8
                    || s.index(k - 1) == 0x5Cu8)));
    }
}

/// Origin Rust: pub fn is_special(&self) -> bool { !matches!(*self, Self::NotSpecial) }
///   (parser.rs:166-168)
pub open spec fn is_special(st: SchemeType) -> bool {
    st != SchemeType::NotSpecial
}

/// Origin Rust: pub fn is_file(&self) -> bool { matches!(*self, Self::File) }
///   (parser.rs:170-172)
pub open spec fn is_file(st: SchemeType) -> bool {
    st == SchemeType::File
}

impl SchemeType {
    /// Origin Rust: pub fn is_special(&self) -> bool { !matches!(*self, Self::NotSpecial) }
    ///   (parser.rs:166-168)
    pub exec fn is_special(self) -> (b: bool)
        ensures
            b == is_special(self),
    {
        match self {
            SchemeType::NotSpecial => false,
            _ => true,
        }
    }

    /// Origin Rust: pub fn is_file(&self) -> bool { matches!(*self, Self::File) }
    ///   (parser.rs:170-172)
    pub exec fn is_file(self) -> (b: bool)
        ensures
            b == is_file(self),
    {
        match self {
            SchemeType::File => true,
            _ => false,
        }
    }
}

/// Origin Rust: impl<T: AsRef<str>> From<T> for SchemeType (parser.rs:175-183)
///   match s.as_ref() {
///       "http" | "https" | "ws" | "wss" | "ftp" => Self::SpecialNotFile,
///       "file" => Self::File,
///       _ => Self::NotSpecial,
///   }
pub open spec fn scheme_type_of(s: Seq<u8>) -> SchemeType {
    if s == seq![0x68u8, 0x74, 0x74, 0x70]           // "http"
        || s == seq![0x68u8, 0x74, 0x74, 0x70, 0x73]  // "https"
        || s == seq![0x77u8, 0x73]                    // "ws"
        || s == seq![0x77u8, 0x73, 0x73]             // "wss"
        || s == seq![0x66u8, 0x74, 0x70]             // "ftp"
    {
        SchemeType::SpecialNotFile
    } else if s == seq![0x66u8, 0x69, 0x6C, 0x65] {  // "file"
        SchemeType::File
    } else {
        SchemeType::NotSpecial
    }
}

/// Exec companion of scheme_type_of: the same-bytes classifier.
/// Origin Rust: the match arms of From<T> for SchemeType (parser.rs:177-181),
/// with "http" | "https" | "ws" | "wss" | "ftp" => SpecialNotFile first.
pub exec fn scheme_type_from(s: &Vec<u8>) -> (r: SchemeType)
    ensures
        r == scheme_type_of(s.view()),
{
    if bytes_eq(s, &vec![0x68u8, 0x74, 0x74, 0x70]) {
        SchemeType::SpecialNotFile
    } else if bytes_eq(s, &vec![0x68u8, 0x74, 0x74, 0x70, 0x73]) {
        SchemeType::SpecialNotFile
    } else if bytes_eq(s, &vec![0x77u8, 0x73]) {
        SchemeType::SpecialNotFile
    } else if bytes_eq(s, &vec![0x77u8, 0x73, 0x73]) {
        SchemeType::SpecialNotFile
    } else if bytes_eq(s, &vec![0x66u8, 0x74, 0x70]) {
        SchemeType::SpecialNotFile
    } else if bytes_eq(s, &vec![0x66u8, 0x69, 0x6C, 0x65]) {
        SchemeType::File
    } else {
        SchemeType::NotSpecial
    }
}

/// Origin Rust: pub fn default_port(scheme: &str) -> Option<u16> (parser.rs:185-192)
///   match scheme {
///       "http" | "ws" => Some(80),
///       "https" | "wss" => Some(443),
///       "ftp" => Some(21),
///       _ => None,
///   }
pub open spec fn default_port_of(s: Seq<u8>) -> Option<u16> {
    if s == seq![0x68u8, 0x74, 0x74, 0x70] || s == seq![0x77u8, 0x73] {
        Some(80)
    } else if s == seq![0x68u8, 0x74, 0x74, 0x70, 0x73] || s == seq![0x77u8, 0x73, 0x73] {
        Some(443)
    } else if s == seq![0x66u8, 0x74, 0x70] {
        Some(21)
    } else {
        None
    }
}

/// Exec companion of default_port_of.
/// Origin Rust: default_port match (parser.rs:186-191).
pub exec fn default_port(scheme_bytes: &Vec<u8>) -> (r: Option<u16>)
    ensures
        r == default_port_of(scheme_bytes.view()),
{
    if bytes_eq(scheme_bytes, &vec![0x68u8, 0x74, 0x74, 0x70]) {
        Some(80)
    } else if bytes_eq(scheme_bytes, &vec![0x77u8, 0x73]) {
        Some(80)
    } else if bytes_eq(scheme_bytes, &vec![0x68u8, 0x74, 0x74, 0x70, 0x73]) {
        Some(443)
    } else if bytes_eq(scheme_bytes, &vec![0x77u8, 0x73, 0x73]) {
        Some(443)
    } else if bytes_eq(scheme_bytes, &vec![0x66u8, 0x74, 0x70]) {
        Some(21)
    } else {
        None
    }
}


/* ============================================================
 * Parse machine -- byte-model foundation (Origin: the char-
 * iterator machinery of parser.rs:194-331 and the number/port
 * faces, transcribed on the restricted byte domain)
 * ============================================================ */

/// The transcription domain of the batch: every input byte is ASCII and
/// is not U+0009/U+000A/U+000D. Upstream `Input` filters those three on
/// every `next()` (parser.rs:322-331) and `new_trim_*` strips them at the
/// ends, so on this domain a byte cursor is faithful to the char chain;
/// multibyte code points are outside the domain (the whole-char
/// percent-encoding of `utf8_percent_encode` is the deep-water face).
pub open spec fn machine_domain_byte(b: u8) -> bool {
    b < 0x80u8 && b != 0x09u8 && b != 0x0Au8 && b != 0x0Du8
}

pub open spec fn machine_domain(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> machine_domain_byte(s.index(i))
}

/// Origin Rust (parser.rs:87-98, the simple_enum_error! expansion; the
/// fmt::Display descriptions and `From<idna::Errors>` of parser.rs:49-104
/// are the fmt/idna layers and stay outside):
///   pub enum ParseError { EmptyHost, IdnaError, InvalidPort, InvalidIpv4Address,
///     InvalidIpv6Address, InvalidDomainCharacter, RelativeUrlWithoutBase,
///     RelativeUrlWithCannotBeABaseBase, SetHostOnCannotBeABaseUrl, Overflow }
#[derive(Copy, Clone, Debug)]
pub enum ParseError {
    EmptyHost,
    IdnaError,
    InvalidPort,
    InvalidIpv4Address,
    InvalidIpv6Address,
    InvalidDomainCharacter,
    RelativeUrlWithoutBase,
    RelativeUrlWithCannotBeABaseBase,
    SetHostOnCannotBeABaseUrl,
    Overflow,
}

/// Origin Rust (parser.rs:1741-1748):
///   pub fn to_u32(i: usize) -> ParseResult<u32> {
///       if i <= u32::MAX as usize { Ok(i as u32) } else { Err(ParseError::Overflow) } }
pub exec fn to_u32(i: usize) -> (r: Result<u32, ParseError>)
    ensures
        r.is_ok() == (i <= 0xFFFF_FFFF),
        r.is_ok() ==> (r.unwrap() as int) == (i as int),
        r.is_err() ==> i > 0xFFFF_FFFF,
{
    if i <= 0xFFFF_FFFF {
        Ok(i as u32)
    } else {
        Err(ParseError::Overflow)
    }
}

/// Origin Rust (parser.rs:194-197): pub struct Input<'i> { chars: str::Chars<'i> }.
/// Byte-position model over the parent slice (`pos` is the cursor; the
/// `chars` clone-and-advance of upstream becomes a Copy struct).
#[derive(Copy, Clone)]
pub struct Input<'i> {
    pub bytes: &'i [u8],
    pub pos: usize,
}

/// The consumed-so-far invariant of the cursor (the `chars` iterator bound).
pub open spec fn input_ok(input: &Input) -> bool {
    input.pos <= input.bytes.view().len()
}

/// The remaining suffix (the iterator tail).
pub open spec fn input_rem(input: &Input) -> Seq<u8> {
    input.bytes.view().subrange(input.pos as int, input.bytes.view().len() as int)
}

/// The full transcription-domain well-formedness threaded through the machine
/// (the total-length bound is the to_u32 Overflow domain: parser offsets are u32).
pub open spec fn input_wf(input: &Input) -> bool {
    &&& input_ok(input)
    &&& machine_domain(input_rem(input))
    &&& (input_rem(input).len() as int) <= 0xFFFF_FFFF
    &&& (input.bytes.view().len() as int) <= 0xFFFF_FFFF
}

/// The prefix subrange of an appended sequence is the prefix subrange of the
/// base (append-only writes keep the [0, k) region; the loop invariants use
/// this as the single-equality form of prefix preservation).
pub proof fn add_prefix_subrange(pre: Seq<u8>, sfx: Seq<u8>, k: int)
    requires
        0 <= k,
        k <= pre.len(),
    ensures
        (pre + sfx).subrange(0, k) == pre.subrange(0, k),
{
    vstd::seq::lemma_seq_add_len(pre, sfx);
    assert forall|j: int| 0 <= j && j < k
        implies (pre + sfx).index(j) == pre.index(j) by {
        vstd::seq::lemma_seq_add_index1(pre, sfx, j);
    }
}

/// machine_domain is closed under subranges (cursor advance keeps the domain).
pub proof fn machine_domain_subrange(s: Seq<u8>, a: int, b: int)
    requires
        machine_domain(s),
        0 <= a,
        a <= b,
        b <= s.len(),
    ensures
        machine_domain(s.subrange(a, b)),
{
    let sub = s.subrange(a, b);
    assert forall|i: int|
        0 <= i < sub.len() implies machine_domain_byte(sub.index(i)) by {
        vstd::seq::lemma_seq_subrange_index(s, a, b, i);
    }
}

/// Positioning of a shifted byte cursor: the remaining suffix of pos+k.
pub proof fn rem_shift(bytes: &[u8], p: int, k: int)
    requires
        0 <= p,
        0 <= k,
        p + k <= bytes.view().len(),
    ensures
        bytes.view().subrange(p + k, bytes.view().len() as int)
            == bytes.view().subrange(p, bytes.view().len() as int)
                .subrange(k, bytes.view().len() as int - p),
{
    let n = bytes.view().len() as int;
    let s = bytes.view();
    assert(s.subrange(p, n).subrange(k, n - p) == s.subrange(p + k, n)) by {
        vstd::seq::lemma_seq_subrange_composition(s, p, n, k, n - p);
    }
}

impl<'i> Input<'i> {
    /// Origin Rust (parser.rs:242-245): pub fn is_empty(&self) -> bool { self.clone().next().is_none() }
    pub exec fn is_empty(&self) -> (r: bool)
        requires
            input_ok(self),
        ensures
            r == (input_rem(self).len() == 0),
    {
        self.pos >= self.bytes.len()
    }

    /// Origin Rust (parser.rs:262-266): fn split_first(&self) -> (Option<char>, Self)
    pub exec fn split_first(&self) -> (ret: (Option<u8>, Input<'i>))
        requires
            input_wf(self),
        ensures
            input_wf(&ret.1),
            (ret.0.is_none()) == (input_rem(self).len() == 0),
            ret.0.is_none() ==> input_rem(&ret.1) == input_rem(self),
            ret.0.is_some() ==> ret.0.unwrap() == input_rem(self).index(0)
                && input_rem(&ret.1) == input_rem(self).subrange(1, input_rem(self).len() as int),
    {
        if self.pos < self.bytes.len() {
            proof {
                let cur = input_rem(self);
                assert(cur.len() == self.bytes.view().len() - self.pos);
                assert(machine_domain_byte(cur.index(0)));
                machine_domain_subrange(cur, 1, cur.len() as int);
                rem_shift(self.bytes, self.pos as int, 1);
                let tail = Input { bytes: self.bytes, pos: (self.pos + 1) as usize };
                assert(input_rem(&tail) == cur.subrange(1, cur.len() as int));
            }
            (Some(self.bytes[self.pos]), Input { bytes: self.bytes, pos: self.pos + 1 })
        } else {
            (None, *self)
        }
    }

    /// Origin Rust (parser.rs:247-249): pub fn starts_with<P: Pattern>(&self, p: P) -> bool
    ///   { p.split_prefix(&mut self.clone()) }  -- the char Pattern face.
    pub exec fn starts_with_char(&self, c: u8) -> (r: bool)
        requires
            input_wf(self),
        ensures
            r == (input_rem(self).len() > 0 && input_rem(self).index(0) == c),
    {
        self.pos < self.bytes.len() && self.bytes[self.pos] == c
    }

    /// Origin Rust (parser.rs:252-260): pub fn split_prefix<P: Pattern>(&self, p: P) -> Option<Self>
    ///   -- the char Pattern face.
    pub exec fn split_prefix_char(&self, c: u8) -> (o: Option<Input<'i>>)
        requires
            input_wf(self),
        ensures
            o.is_some() == (input_rem(self).len() > 0 && input_rem(self).index(0) == c),
            o.is_some()
                ==> input_rem(&o.unwrap())
                    == input_rem(self).subrange(1, input_rem(self).len() as int)
                    && input_wf(&o.unwrap()),
    {
        if self.starts_with_char(c) {
            proof {
                let cur = input_rem(self);
                assert(cur.len() == self.bytes.view().len() - self.pos);
                assert(self.pos + 1 <= self.bytes.len());
                assert(machine_domain_byte(cur.index(0)));
                machine_domain_subrange(cur, 1, cur.len() as int);
                rem_shift(self.bytes, self.pos as int, 1);
                let tail = Input { bytes: self.bytes, pos: (self.pos + 1) as usize };
                assert(input_rem(&tail) == cur.subrange(1, cur.len() as int));
            }
            Option::Some(Input { bytes: self.bytes, pos: self.pos + 1 })
        } else {
            Option::None
        }
    }

    /// Origin Rust (parser.rs:305-314): impl Pattern for &str { ... } -- the
    /// "//" literal face used by parse_non_special/parse_relative.
    pub exec fn split_prefix_slash2(&self) -> (o: Option<Input<'i>>)
        requires
            input_wf(self),
        ensures
            o.is_some()
                ==> input_rem(self).len() >= 2
                    && input_rem(self).index(0) == 0x2Fu8
                    && input_rem(self).index(1) == 0x2Fu8
                    && input_rem(&o.unwrap())
                        == input_rem(self).subrange(2, input_rem(self).len() as int)
                    && input_wf(&o.unwrap()),
    {
        if self.starts_with_char(0x2Fu8) {
            proof {
                let cur = input_rem(self);
                assert(cur.index(0) == 0x2Fu8);
                rem_shift(self.bytes, self.pos as int, 1);
                machine_domain_subrange(cur, 1, cur.len() as int);
                if cur.len() >= 2 {
                    assert(cur.index(1) == (self.bytes)[self.pos as int + 1]);
                }
            }
            let r1 = Input { bytes: self.bytes, pos: self.pos + 1 };
            let o2 = r1.split_prefix_char(0x2Fu8);
            proof {
                if o2.is_some() {
                    let cur = input_rem(self);
                    let tail2 = o2.unwrap();
                    assert(input_rem(self).index(1) == 0x2Fu8);
                    rem_shift(self.bytes, self.pos as int + 1, 1);
                    assert(input_rem(&tail2) == cur.subrange(2, cur.len() as int));
                }
            }
            o2
        } else {
            Option::None
        }
    }

    /// Origin Rust (parser.rs:269-281):
    ///   fn count_matching<F: Fn(char) -> bool>(&self, f: F) -> (u32, Self)
    /// -- the `|c| matches!(c, '/' | '\\')` instantiation of parse_with_scheme
    ///    and parse_relative.
    pub exec fn count_matching_slash_bs(&self) -> (ret: (u32, Input<'i>))
        requires
            input_wf(self),
        ensures
            input_wf(&ret.1),
            (ret.0 as int) <= input_rem(self).len(),
            input_rem(&ret.1) == input_rem(self).subrange(ret.0 as int, input_rem(self).len() as int),
            (ret.0 as int) > 0
                && (ret.0 as int) < input_rem(self).len()
                ==> (forall|j: int| 0 <= j < ret.0 as int ==>
                    (input_rem(self).index(j) == 0x2Fu8 || input_rem(self).index(j) == 0x5Cu8))
                    && input_rem(self).index(ret.0 as int) != 0x2Fu8
                    && input_rem(self).index(ret.0 as int) != 0x5Cu8,
            ret.0 == 0 ==> input_rem(&ret.1) == input_rem(self),
            (((input_rem(self).len() as int) > 0
                && (ret.0 as int) == 0)
                ==> (input_rem(self).index(0) != 0x2Fu8
                    && input_rem(self).index(0) != 0x5Cu8)),
            (((ret.0 as int)
                == (input_rem(self).len() as int))
                ==> (forall|j: int| 0 <= j && j < (ret.0 as int)
                    ==> (input_rem(self).index(j) == 0x2Fu8
                        || input_rem(self).index(j) == 0x5Cu8))),
    {
        let mut p = self.pos;
        let mut n: u32 = 0;
        proof {
            let cur0 = input_rem(self);
            assert((self.bytes.view().len() as int) <= 0xFFFF_FFFF);
        }
        while p < self.bytes.len()
            && (self.bytes[p] == 0x2Fu8 || self.bytes[p] == 0x5Cu8)
            invariant
                self.pos <= p <= self.bytes.len(),
                (n as int) == (p as int) - (self.pos as int),
                forall|j: int| self.pos <= j < p ==>
                    ((self.bytes)[j as int] == 0x2Fu8 || (self.bytes)[j as int] == 0x5Cu8),
                input_rem(self).len() >= (p as int) - (self.pos as int),
                (n as int) < 0x1_0000_0000,
                (self.bytes.view().len() as int) <= 0xFFFF_FFFF,
            decreases self.bytes.len() - p,
        {
            proof {
                assert(p as int + 1 <= (self.bytes.view().len() as int));
                assert(p as int + 1 <= 0xFFFF_FFFF);
            }
            p += 1;
            n += 1;
        }
        proof {
            let cur = input_rem(self);
            assert(cur == self.bytes.view().subrange(self.pos as int, self.bytes.len() as int));
            rem_shift(self.bytes, self.pos as int, n as int);
            assert(cur.subrange(n as int, cur.len() as int)
                == self.bytes.view().subrange(p as int, self.bytes.len() as int));
            machine_domain_subrange(cur, n as int, cur.len() as int);
            assert(machine_domain(cur.subrange(n as int, cur.len() as int)));
            if n > 0 && p < self.bytes.len() {
                assert(cur[n as int] == (self.bytes)[p as int]);
                assert(cur.index(n as int) != 0x2Fu8);
                assert(cur.index(n as int) != 0x5Cu8);
            }
            if n == 0 && (cur.len() as int) > 0 {
                assert(p == self.pos);
                assert(p < self.bytes.len());
                vstd::seq::lemma_seq_subrange_index(
                    self.bytes.view(), self.pos as int,
                    self.bytes.view().len() as int, 0);
                assert(cur.index(0) == (self.bytes)[p as int]);
                assert(cur.index(0) != 0x2Fu8);
                assert(cur.index(0) != 0x5Cu8);
            }
            if (n as int) == (cur.len() as int) && n >= 0 {
                assert forall|j: int| 0 <= j && j < (n as int)
                    implies cur.index(j) == 0x2Fu8
                        || cur.index(j) == 0x5Cu8 by {
                    vstd::seq::lemma_seq_subrange_index(
                        self.bytes.view(), self.pos as int,
                        self.bytes.view().len() as int, j);
                    assert(cur.index(j) == (self.bytes)[
                        (self.pos + j as usize) as int]);
                }
            }
        }
        (n, Input { bytes: self.bytes, pos: p })
    }
}

/// Origin Rust (parser.rs:224-240): pub fn new_trim_c0_control_and_space(...).
/// The violation_fn logging arm is dropped (trait-object logging has no
/// value-semantic effect); `trim_matches(c0_control_or_space)` (parser.rs:1723-1727)
/// trims <= U+0020 at both ends, a byte scan on this domain.
pub exec fn new_trim_c0_control_and_space<'i>(bytes: &'i [u8]) -> (input: Input<'i>)
    requires
        machine_domain(bytes@),
        (bytes@.len() as int) <= 0xFFFF_FFFF,
    ensures
        input_wf(&input),
        input_rem(&input).len() <= bytes@.len(),
        forall|i: int| 0 <= i < input_rem(&input).len()
            ==> input_rem(&input).index(i)
                == bytes@.index((bytes@.len() - input_rem(&input).len()) + i),
        forall|i: int| 0 <= i < bytes@.len() - input_rem(&input).len()
            ==> bytes@.index(i) <= 0x20u8,
        forall|i: int|
            (input.pos as int) + input_rem(&input).len() <= i < bytes@.len()
            ==> bytes@.index(i) <= 0x20u8,
{
    let mut start: usize = 0;
    while start < bytes.len() && bytes[start] <= 0x20
        invariant
            start <= bytes.len(),
            forall|i: int| 0 <= i < start as int ==> bytes@.index(i) <= 0x20u8,
        decreases bytes.len() - start,
    {
        start += 1;
    }
    let mut end: usize = bytes.len();
    while end > start && bytes[end - 1] <= 0x20
        invariant
            start <= end <= bytes.len(),
            forall|i: int| 0 <= i < start as int ==> bytes@.index(i) <= 0x20u8,
            forall|i: int| end as int <= i < bytes@.len() ==> bytes@.index(i) <= 0x20u8,
        decreases end - start,
    {
        end -= 1;
    }
    proof {
        assert(bytes@.subrange(start as int, end as int)
            == bytes@.subrange(start as int, bytes@.len() as int)
                .subrange(0, (end - start) as int));
        let rem = bytes@.subrange(start as int, bytes@.len() as int);
        assert(rem.subrange(0, (end - start) as int).len() == (end - start) as int);
        assert(machine_domain(rem.subrange(0, (end - start) as int)));
    }
    Input { bytes, pos: start }
}

/* ============================================================
 * Percent-encoding model (in-tree mirror of the AsciiSet faces
 * of parser.rs:19-45 and percent_encoding/src; the constant
 * tables of the upstream crate become per-set byte predicates)
 * ============================================================ */

/// The percent-encoding sets as a value (upstream passes `&'static AsciiSet`).
#[derive(Copy, Clone, Debug)]
pub enum EncodeSet {
    /// parser.rs:19-20: FRAGMENT = &CONTROLS.add(b' ').add(b'"').add(b'<').add(b'>').add(b'`')
    Fragment,
    /// parser.rs:22-23: QUERY = &CONTROLS.add(b' ').add(b'"').add(b'#').add(b'<').add(b'>')
    Query,
    /// parser.rs:24: SPECIAL_QUERY = &QUERY.add(b'\'')
    SpecialQuery,
    /// parser.rs:26-27: PATH = &QUERY.add(b'?').add(b'^').add(b'`').add(b'{').add(b'}')
    Path,
    /// parser.rs:29-39: USERINFO = &PATH.add(b'/').add(b':').add(b';').add(b'=').add(b'@').add(b'[').add(b'\\').add(b']').add(b'|')
    Userinfo,
    /// percent_encoding/src/ascii_set.rs:107-114: CONTROLS itself (the
    /// opaque-path encode set of parse_cannot_be_a_base_path,
    /// parser.rs:1359-1368)
    Controls,
}

/// percent_encoding/src/ascii_set.rs:107-114: CONTROLS = 0x00..=0x1F + 0x7F.
pub open spec fn in_controls(b: u8) -> bool {
    b <= 0x1Fu8 || b == 0x7Fu8
}

/// The membership face of AsciiSet::contains / should_percent_encode
/// (percent_encoding/src/ascii_set.rs:46-53; all machine bytes are ASCII,
/// so should_percent_encode reduces to membership).
pub open spec fn in_set(set: EncodeSet, b: u8) -> bool {
    match set {
        EncodeSet::Fragment => in_controls(b) || b == 0x20u8 || b == 0x22u8 || b == 0x3Cu8
            || b == 0x3Eu8 || b == 0x60u8,
        EncodeSet::Query => in_controls(b) || b == 0x20u8 || b == 0x22u8 || b == 0x23u8
            || b == 0x3Cu8 || b == 0x3Eu8,
        EncodeSet::SpecialQuery => in_controls(b) || b == 0x20u8 || b == 0x22u8 || b == 0x23u8
            || b == 0x3Cu8 || b == 0x3Eu8 || b == 0x27u8,
        EncodeSet::Path => in_controls(b) || b == 0x20u8 || b == 0x22u8 || b == 0x23u8
            || b == 0x3Cu8 || b == 0x3Eu8 || b == 0x3Fu8 || b == 0x5Eu8 || b == 0x60u8
            || b == 0x7Bu8 || b == 0x7Du8,
        EncodeSet::Userinfo => in_controls(b) || b == 0x20u8 || b == 0x22u8 || b == 0x23u8
            || b == 0x3Cu8 || b == 0x3Eu8 || b == 0x3Fu8 || b == 0x5Eu8 || b == 0x60u8
            || b == 0x7Bu8 || b == 0x7Du8 || b == 0x2Fu8 || b == 0x3Au8 || b == 0x3Bu8
            || b == 0x3Du8 || b == 0x40u8 || b == 0x5Bu8 || b == 0x5Cu8 || b == 0x5Du8
            || b == 0x7Cu8,
        EncodeSet::Controls => in_controls(b),
    }
}

/// Exec twin of in_set (the byte-membership decision of the encoder loop).
pub exec fn in_set_exec(set: EncodeSet, b: u8) -> (r: bool)
    ensures
        r == in_set(set, b),
{
    match set {
        EncodeSet::Fragment => b <= 0x1Fu8 || b == 0x7Fu8 || b == 0x20u8 || b == 0x22u8
            || b == 0x3Cu8 || b == 0x3Eu8 || b == 0x60u8,
        EncodeSet::Query => b <= 0x1Fu8 || b == 0x7Fu8 || b == 0x20u8 || b == 0x22u8
            || b == 0x23u8 || b == 0x3Cu8 || b == 0x3Eu8,
        EncodeSet::SpecialQuery => b <= 0x1Fu8 || b == 0x7Fu8 || b == 0x20u8
            || b == 0x22u8 || b == 0x23u8 || b == 0x3Cu8 || b == 0x3Eu8 || b == 0x27u8,
        EncodeSet::Path => b <= 0x1Fu8 || b == 0x7Fu8 || b == 0x20u8 || b == 0x22u8
            || b == 0x23u8 || b == 0x3Cu8 || b == 0x3Eu8 || b == 0x3Fu8 || b == 0x5Eu8
            || b == 0x60u8 || b == 0x7Bu8 || b == 0x7Du8,
        EncodeSet::Userinfo => b <= 0x1Fu8 || b == 0x7Fu8 || b == 0x20u8
            || b == 0x22u8 || b == 0x23u8 || b == 0x3Cu8 || b == 0x3Eu8 || b == 0x3Fu8
            || b == 0x5Eu8 || b == 0x60u8 || b == 0x7Bu8 || b == 0x7Du8 || b == 0x2Fu8
            || b == 0x3Au8 || b == 0x3Bu8 || b == 0x3Du8 || b == 0x40u8 || b == 0x5Bu8
            || b == 0x5Cu8 || b == 0x5Du8 || b == 0x7Cu8,
        EncodeSet::Controls => b <= 0x1Fu8 || b == 0x7Fu8,
    }
}

/// The uppercase hex of percent_encoding's ENC_TABLE
/// (percent_encoding/src/lib.rs:74-95: nibble 10..=15 is 'A'..'F', 0x41..0x46,
/// i.e. 0x37 + v; an earlier transcription wrote 0x37 + (v - 10), which
/// distorts every escape with a high nibble, e.g. byte 0x3C as %39).
pub open spec fn hex_digit_byte(v: int) -> u8 {
    if 0 <= v <= 9 {
        ((0x30 + v) as u8)
    } else if 10 <= v <= 15 {
        ((0x37 + v) as u8)
    } else {
        0x30u8
    }
}

pub exec fn hex_digit_exec(v: u8) -> (r: u8)
    requires
        v <= 15,
    ensures
        r == hex_digit_byte(v as int),
{
    if v < 10 {
        0x30u8 + v
    } else {
        0x37u8 + v
    }
}

/// One byte's percent-encoding (the EmitSlices/percent_encode_byte face).
pub open spec fn enc_byte(b: u8, set: EncodeSet) -> Seq<u8> {
    if in_set(set, b) {
        seq![
            0x25u8,
            hex_digit_byte((b as int) / 16),
            hex_digit_byte((b as int) % 16),
        ]
    } else {
        seq![b]
    }
}

/// The whole-slice fold of utf8_percent_encode on ASCII payload
/// (each one-byte char encodes independently).
pub open spec fn enc_seq(s: Seq<u8>, set: EncodeSet) -> Seq<u8>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        enc_byte(s.index(0), set) + enc_seq(s.subrange(1, s.len() as int), set)
    }
}

/// Right cancellation of Seq concat (x + z == y + z ==> x == y), via the
/// add lemmas and extensionality.
pub proof fn seq_add_cancel_right(x: Seq<u8>, y: Seq<u8>, z: Seq<u8>)
    requires
        x + z == y + z,
    ensures
        x == y,
{
    vstd::seq::lemma_seq_add_len(x, z);
    vstd::seq::lemma_seq_add_len(y, z);
    vstd::seq::lemma_seq_ext_equal(x, y);
    assert(x.len() == y.len());
    assert forall|j: int|
        0 <= j < x.len() implies x.index(j) == y.index(j) by {
        vstd::seq::lemma_seq_add_index1(x, z, j);
        vstd::seq::lemma_seq_add_index1(y, z, j);
        assert((x + z).index(j) == (y + z).index(j));
    }
    assert(x =~= y);
}

/// The byte budget of an encode (each byte encodes to at most three).
pub proof fn enc_seq_len_bound(s: Seq<u8>, set: EncodeSet)
    requires
        machine_domain(s),
    ensures
        enc_seq(s, set).len() <= 3 * s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        enc_seq_len_bound(s.subrange(1, s.len() as int), set);
        assert(enc_byte(s.index(0), set).len() <= 3);
        vstd::seq::lemma_seq_add_len(enc_byte(s.index(0), set),
            enc_seq(s.subrange(1, s.len() as int), set));
    }
}

/// One consumed-prefix stride of the encode loop: appending byte s[i]
/// to the encode of s[0..i] gives the encode of s[0..i+1].
/* [verus note: rlimit = the two enc_seq_split inductions with the Seq
   cancellation step exceed the default 10-second query budget when the
   solver context carries the equational-law broadcast groups -- only the
   resource ceiling is raised, no obligation is relaxed] */
#[verifier::rlimit(45)]
pub proof fn enc_prefix_next(s: Seq<u8>, i: int, set: EncodeSet)
    requires
        machine_domain(s),
        0 <= i,
        i < s.len(),
    ensures
        enc_seq(s.subrange(0, i + 1), set)
            == enc_seq(s.subrange(0, i), set) + enc_byte(s.index(i), set),
{
    let n = s.len() as int;
    machine_domain_subrange(s, 0, i);
    machine_domain_subrange(s, i, n);
    machine_domain_subrange(s, 0, i + 1);
    machine_domain_subrange(s, i + 1, n);
    enc_seq_split(s, i, set);
    enc_seq_split(s, i + 1, set);
    let tail = s.subrange(i, n);
    let after = s.subrange(i + 1, n);
    vstd::seq::lemma_seq_subrange_index(s, i, n, 0);
    vstd::seq::lemma_seq_subrange_composition(s, i, n, 1, n - i);
    assert(enc_seq(tail, set) == enc_byte(s.index(i), set) + enc_seq(after, set));
    assert(enc_seq(s, set) == enc_seq(s.subrange(0, i), set) + enc_seq(tail, set));
    assert(enc_seq(s, set) == enc_seq(s.subrange(0, i + 1), set) + enc_seq(after, set));
    assert(enc_seq(s.subrange(0, i), set) + (enc_byte(s.index(i), set) + enc_seq(after, set))
        == (enc_seq(s.subrange(0, i), set) + enc_byte(s.index(i), set)) + enc_seq(after, set));
    seq_add_cancel_right(
        enc_seq(s.subrange(0, i), set) + enc_byte(s.index(i), set),
        enc_seq(s.subrange(0, i + 1), set),
        enc_seq(after, set),
    );
}

/// enc_seq composed at an arbitrary split point (the consumed-prefix/tail
/// stride of the encode-append loop).
pub proof fn enc_seq_split(s: Seq<u8>, i: int, set: EncodeSet)
    requires
        machine_domain(s),
        0 <= i,
        i <= s.len(),
    ensures
        enc_seq(s, set)
            == enc_seq(s.subrange(0, i), set) + enc_seq(s.subrange(i, s.len() as int), set),
    decreases s.len(),
{
    if i == 0 {
        assert(s.subrange(0, 0) == Seq::empty());
        assert(enc_seq(Seq::empty(), set) == Seq::empty());
        assert(Seq::empty() + enc_seq(s.subrange(0, s.len() as int), set)
            == enc_seq(s.subrange(0, s.len() as int), set));
        assert(s.subrange(0, s.len() as int) == s);
    } else {
        let t = s.subrange(1, s.len() as int);
        let n = s.len() as int;
        machine_domain_subrange(s, 1, n);
        assert(t.subrange(0, i - 1) == s.subrange(1, i)) by {
            vstd::seq::lemma_seq_subrange_composition(s, 1, n, 0, i - 1);
        };
        assert(t.subrange(i - 1, t.len() as int) == s.subrange(i, n)) by {
            vstd::seq::lemma_seq_subrange_composition(s, 1, n, i - 1, n - 1);
        };
        enc_seq_split(t, i - 1, set);
        assert(enc_seq(s, set) == enc_byte(s.index(0), set) + enc_seq(t, set));
        assert(s.subrange(0, i).index(0) == s.index(0)) by {
            vstd::seq::lemma_seq_subrange_index(s, 0, i, 0);
        }
        assert(s.subrange(0, i).subrange(1, i) == s.subrange(1, i)) by {
            vstd::seq::lemma_seq_subrange_composition(s, 0, i, 1, i);
        }
        assert(enc_seq(s.subrange(0, i), set)
            == enc_byte(s.index(0), set) + enc_seq(s.subrange(1, i), set));
        assert(enc_seq(s.subrange(i, n), set) == enc_seq(t.subrange(i - 1, t.len() as int), set));
        // enc(t) = enc(t[0..i-1]) + enc(t[i-1..]) now combines associatively.
    }
}

/// Three-byte push with the concat form pinned (the '%HH' stride of the
/// encoder below; only the Vec-push specs plus Seq assoc are used).
pub exec fn vec_push3(ser: &mut Vec<u8>, x1: u8, x2: u8, x3: u8)
    requires
        old(ser).view().len() + 3 <= 0xFFFF_FFFF,
    ensures
        final(ser).view() == old(ser).view() + seq![x1, x2, x3],
{
    ser.push(x1);
    ser.push(x2);
    ser.push(x3);
    proof {
        let v0 = old(ser).view();
        assert(v0.push(x1) == v0 + seq![x1]);
        assert((v0 + seq![x1]).push(x2) == v0 + seq![x1] + seq![x2]);
        assert((v0 + seq![x1] + seq![x2]).push(x3) == v0 + seq![x1] + seq![x2] + seq![x3]);
        assert(v0 + seq![x1] + seq![x2] + seq![x3] == v0 + seq![x1, x2, x3]);
    }
}

/// The serialization_extend face of `serialization.extend(percent_encode(...))`
/// (parser.rs:1592-1596 and the same shape at parser.rs:920-921/1416-1417/1670-1673).
/// push_pending's bulk slice selection (parser.rs:1176-1197) is the caller's
/// split; this is the encode itself.
pub exec fn extend_percent_encode(ser: &mut Vec<u8>, part: &[u8], set: EncodeSet)
    requires
        old(ser).view().len() <= 0xFFFF_FFFF - 3 * (part@.len() as int),
        machine_domain(part@),
    ensures
        final(ser).view() == old(ser).view() + enc_seq(part@, set),
{
    let ghost pre = ser.view();
    let ghost partv = part.view();
    let mut i: usize = 0;
    while i < part.len()
        invariant
            part@ == partv,
            machine_domain(part@),
            pre == old(ser).view(),
            i <= part.len(),
            ser.view() == pre + enc_seq(partv.subrange(0, i as int), set),
            (ser.view().len() as int) + 3 * ((part.len() as int) - (i as int))
                <= 0xFFFF_FFFF,
        decreases part.len() - i,
    {
        proof {
            let n = part@.len() as int;
            assert((part.len() as int) - (i as int) >= 1);
            assert(machine_domain(part@));
            assert(enc_byte(part@.index(i as int), set).len() <= 3);
            enc_prefix_next(partv, i as int, set);
            assert(enc_seq(partv.subrange(0, (i as int) + 1), set)
                == enc_seq(partv.subrange(0, i as int), set) + enc_byte(partv.subrange(i as int, (i as int) + 1).index(0), set));
        }
        let b = part[i];
        proof {
            assert(partv.index(i as int) == (part)[i as int]);
            assert(partv.subrange(i as int, (i as int) + 1).index(0) == partv.index(i as int));
        }
        if in_set_exec(set, b) {
            proof {
                assert(b / 16 < 16);
                assert(b % 16 < 16);
            }
            let hi = hex_digit_exec((b / 16) as u8);
            let lo = hex_digit_exec((b % 16) as u8);
            proof {
                assert(hi == hex_digit_byte((b as int) / 16));
                assert(lo == hex_digit_byte((b as int) % 16));
                assert(enc_byte(b, set) == seq![0x25u8, hi, lo]);
            }
            vec_push3(ser, 0x25u8, hi, lo);
        } else {
            proof {
                assert(enc_byte(b, set) == seq![b]);
            }
            let ghost before_push = ser.view();
            ser.push(b);
            proof {
                assert(ser.view() == before_push.push(b));
                assert(before_push.push(b) == before_push + seq![b]);
            }
        }
        i += 1;
    }
    proof {
        assert(part@.subrange(0, part@.len() as int) == part@);
    }
}
/* ============================================================
 * Number writers (Origin: fast_u16_to_str parser.rs:1796-1815 and
 * the Ipv4Addr Display face of std used by write!("{host}"))
 * ============================================================ */

/// The ASCII decimal digits of a u16 (dec_val of the result is the value,
/// the bytes are '0'..'9'; the upstream fixed [u8;5] buffer filled from the
/// end produces exactly this digit string).
pub open spec fn dec_ascii_u32(v: int) -> Seq<u8>
    decreases v
{
    if v < 10 {
        seq![((0x30 + v) as u8)]
    } else {
        dec_ascii_u32(v / 10) + seq![((0x30 + (v % 10)) as u8)]
    }
}

/// Origin Rust (parser.rs:1796-1815): fn fast_u16_to_str(buffer: &mut [u8; 5], value: u16) -> &str
///   -- produces the ASCII decimal of value; here the direct append into the
///      serialization (the 5-byte scratch buffer is an exec detail).
/// The digit count of the ASCII decimal (dec_ascii_u32's length face).
pub open spec fn dec_len(v: int) -> int
    decreases v
{
    if v < 10 {
        1
    } else {
        1 + dec_len(v / 10)
    }
}

pub proof fn dec_ascii_len(v: int)
    requires
        0 <= v,
    ensures
        dec_ascii_u32(v).len() == dec_len(v),
    decreases v,
{
    if v < 10 {
    } else {
        dec_ascii_len(v / 10);
        let a = dec_ascii_u32(v / 10);
        let b = seq![((0x30 + (v % 10)) as u8)];
        vstd::seq::lemma_seq_add_len(a, b);
        assert(dec_len(v) == 1 + dec_len(v / 10));
    }
}

pub open spec fn pow10(d: int) -> int
    decreases d
{
    if d <= 0 {
        1
    } else {
        10 * pow10(d - 1)
    }
}

/// dec_len(v) <= d whenever v < 10^d (the decimal digits of a bounded value).
pub proof fn dec_len_pow_bound(d: int, v: int)
    requires
        1 <= d,
        0 <= v < pow10(d),
    ensures
        dec_len(v) <= d,
    decreases d,
{
    if v < 10 {
    } else if d == 1 {
        assert(v < 10);
    } else {
        assert(0 <= v / 10 < pow10(d - 1));
        dec_len_pow_bound(d - 1, v / 10);
    }
}

/// dec_len of any u16 value (the fast_u16_to_str 5-byte buffer bound).
pub proof fn dec_len_bound_u16(v: int)
    requires
        0 <= v <= 65535,
    ensures
        dec_len(v) <= 5,
{
    reveal_with_fuel(pow10, 7);
    assert(pow10(0) == 1);
    assert(pow10(1) == 10);
    assert(pow10(2) == 100);
    assert(pow10(3) == 1000);
    assert(pow10(4) == 10000);
    assert(pow10(5) == 100000);
    assert(65535 < 100000);
    dec_len_pow_bound(5, v);
}

/// dec_len of an IPv4 octet (0..=255, at most three digits).
pub proof fn dec_len_bound_octet(v: int)
    requires
        0 <= v <= 255,
    ensures
        dec_len(v) <= 3,
{
    reveal_with_fuel(pow10, 7);
    assert(pow10(0) == 1);
    assert(pow10(1) == 10);
    assert(pow10(2) == 100);
    assert(pow10(3) == 1000);
    assert(255 < 1000);
    dec_len_pow_bound(3, v);
}

pub exec fn append_dec_port(ser: &mut Vec<u8>, value: u16)
    requires
        old(ser).view().len() <= 0xFFFF_FFFF - 10,
    ensures
        final(ser).view() == old(ser).view() + dec_ascii_u32(value as int),
        final(ser).view().len() == old(ser).view().len() + dec_len(value as int),
        final(ser).view().len() <= old(ser).view().len() + 5,
    decreases value as int,
{
    proof {
        dec_ascii_len(value as int);
        dec_len_bound_u16(value as int);
    }
    if value < 10 {
        proof {
            assert(dec_ascii_u32(value as int) == seq![((0x30u8 + (value as u8)) as u8)]);
            assert((0x30u8 + (value as u8)) == ((0x30 + (value as int)) as u8));
        }
        let d = (0x30u8 + value as u8);
        ser.push(d);
    } else {
        proof {
            assert((value as int) / 10 < value as int);
            assert(dec_ascii_u32(value as int)
                == dec_ascii_u32((value as int) / 10) + seq![
                    ((0x30 + ((value as int) % 10)) as u8),
                ]);
        }
        append_dec_port(ser, value / 10);
        proof {
            assert((value % 10) < 10);
            assert(((value as int) % 10) == ((value % 10) as int));
        }
        let d = (0x30u8 + (value % 10) as u8);
        proof {
            assert(d == ((0x30 + ((value as int) % 10)) as u8));
        }
        ser.push(d);
    }
}

/// The Ipv4Addr dotted-decimal serialization (std `Display for Ipv4Addr`,
/// the face of `write!(&mut self.serialization, "{host}")` at parser.rs:941
/// for Host::Ipv4; the u32 bit pattern is the mirror's Ipv4 payload, the
/// octets are bits 24..31, 16..23, 8..15, 0..7 of the pattern).
pub open spec fn ipv4_ascii(a: int) -> Seq<u8> {
    dec_ascii_u32(a / 16777216) + seq![0x2Eu8]
        + (dec_ascii_u32((a / 65536) % 256) + seq![0x2Eu8]
            + (dec_ascii_u32((a / 256) % 256) + seq![0x2Eu8] + dec_ascii_u32(a % 256)))
}

pub exec fn append_ipv4(ser: &mut Vec<u8>, a: u32)
    requires
        old(ser).view().len() <= 0xFFFF_FFFF - 25,
    ensures
        final(ser).view() == old(ser).view() + ipv4_ascii(a as int),
{
    proof {
        assert((a as int) / 16777216 <= 255);
        assert(((a as int) / 65536) % 256 <= 255);
        assert(((a as int) / 256) % 256 <= 255);
        assert((a as int) % 256 <= 255);
        dec_len_bound_octet((a as int) / 16777216);
        dec_len_bound_octet(((a as int) / 65536) % 256);
        dec_len_bound_octet(((a as int) / 256) % 256);
        dec_len_bound_octet((a as int) % 256);
    }
    append_dec_port(ser, (a / 16777216) as u16);
    ser.push(0x2Eu8);
    proof {
        assert(ser.view()
            == old(ser).view()
                + (dec_ascii_u32((a as int) / 16777216) + seq![0x2Eu8]));
    }
    append_dec_port(ser, ((a / 65536) % 256) as u16);
    ser.push(0x2Eu8);
    proof {
        assert(ser.view()
            == old(ser).view()
                + (dec_ascii_u32((a as int) / 16777216) + seq![0x2Eu8]
                    + (dec_ascii_u32(((a as int) / 65536) % 256) + seq![0x2Eu8])));
    }
    append_dec_port(ser, ((a / 256) % 256) as u16);
    ser.push(0x2Eu8);
    proof {
        assert(ser.view()
            == old(ser).view()
                + (dec_ascii_u32((a as int) / 16777216) + seq![0x2Eu8]
                    + (dec_ascii_u32(((a as int) / 65536) % 256) + seq![0x2Eu8]
                        + (dec_ascii_u32(((a as int) / 256) % 256) + seq![0x2Eu8]))));
    }
    append_dec_port(ser, (a % 256) as u16);
    proof {
        assert(ser.view() == old(ser).view()
            + (dec_ascii_u32((a as int) / 16777216) + seq![0x2Eu8]
                + (dec_ascii_u32(((a as int) / 65536) % 256) + seq![0x2Eu8]
                    + (dec_ascii_u32(((a as int) / 256) % 256) + seq![0x2Eu8]
                        + dec_ascii_u32((a as int) % 256)))));
        assert(ser.view()[..].len() >= 0);
    }
}

/* ============================================================
 * The parser state machine core (Origin: parser.rs:333-423)
 * ============================================================ */

/// Origin Rust (parser.rs:333-339): pub struct Parser { pub serialization: String,
///   pub base_url, pub query_encoding_override, pub violation_fn, pub context }.
/// ledger: serialization is the byte payload (lib.rs ledger 1). The
/// violation_fn (trait-object logging, parser.rs:349-361) and the
/// query_encoding_override (the legacy HTML-form encoding selector,
/// parser.rs:1582-1592) have no effect on the serialized value and are
/// outside the verus surface.
pub struct Parser<'a> {
    /// Origin Rust (parser.rs:334): pub serialization: String  (byte payload per ledger 1)
    pub serialization: Vec<u8>,
    /// Origin Rust (parser.rs:335): pub base_url: Option<&'a super::Url>
    pub base_url: Option<&'a super::Url>,
    /// Origin Rust (parser.rs:338): pub context: Context
    pub context: Context,
}

/// Origin Rust (parser.rs:341-346): pub enum Context { UrlParser, Setter, PathSegmentSetter }
#[derive(Copy, Clone, Debug)]
pub enum Context {
    UrlParser,
    Setter,
    PathSegmentSetter,
}

/// The ASCII lowercase of a scheme/host byte (char::to_ascii_lowercase).
pub open spec fn lower_byte(b: u8) -> u8 {
    if 0x41u8 <= b <= 0x5Au8 {
        (b + 32) as u8
    } else {
        b
    }
}

/// The maximal scheme-char scan prefix (scheme grammar bytes, lowered).
pub open spec fn lowered_prefix(s: Seq<u8>, k: int) -> Seq<u8> {
    Seq::new(k as nat, |i| lower_byte(s.index(i)))
}

/// The top-level entry face of parse_url (parser.rs:374-392): the
/// no-base, non-"file"-scheme cone of the public `Url::parse` inputs --
/// for every valid scheme split k (the grammar bytes + the ':' boundary
/// at k) the recorded scheme classifies non-File and the state faces of
/// the dispatch arms hold over the post-':' remainder. The trigger
/// carriers seat the slice terms in the antecedents.
pub open spec fn url_parse_entry_face(s: Seq<u8>) -> bool {
    machine_domain(s)
        && (forall|k: int|
            #![trigger s.subrange(k, s.len() as int)]
            (0 <= k
                && k + 1 <= (s.len() as int)
                // the carrier (vacuous): the trigger term in the
                // antecedent
                && (s.subrange(k, s.len() as int).len() as int)
                    <= (s.len() as int)
                && super::is_ascii_alpha(s.index(0))
                && (forall|j: int| 1 <= j && j < k
                    ==> super::is_scheme_char(s.index(j)))
                && s.index(k) == 0x3Au8)
            ==> ({
                let st = scheme_type_of(
                    lowered_prefix(s.subrange(0, k), k));
                let rem2 = s.subrange(k + 1, s.len() as int);
                (st == SchemeType::File ==> (
                    file_state_entry_face(rem2)
                    && (k + 1) + 20 * (rem2.len() as int) + 176
                        <= 0xFFFF_FFFF))
                    && (st == SchemeType::SpecialNotFile ==> (
                        forall|c: int| #![trigger
                            rem2.subrange(c, rem2.len() as int)]
                        (0 <= c
                            && c <= (rem2.len() as int)
                            && (rem2.subrange(c, rem2.len() as int).len()
                                as int) <= (rem2.len() as int)
                            && slash_run_prefix(rem2, c)
                            && ((c == rem2.len() as int)
                                || (rem2.index(c) != 0x2Fu8
                                    && rem2.index(c) != 0x5Cu8)))
                        ==> (authority_entry_class(
                                rem2.subrange(c, rem2.len() as int),
                                true)
                            && (k + 1)
                                + 16 * ((rem2.len() as int) - c)
                                + 74
                                <= 0xFFFF_FFFF)))
                    && (st == SchemeType::NotSpecial ==> (
                        (((rem2.len() as int) >= 2
                            && rem2.index(0) == 0x2Fu8
                            && rem2.index(1) == 0x2Fu8)
                            ==> authority_entry_class(
                                rem2.subrange(2, rem2.len() as int),
                                false))
                        && (k + 1) + 16 * (rem2.len() as int) + 74
                            <= 0xFFFF_FFFF
                        && (k + 1) + 11 * (rem2.len() as int) + 30
                            <= 0xFFFF_FFFF))
            }))
}

/// Trigger carrier for the Err-side refutation of parse_scheme (the
/// structural split predicate named so the negated exists has a trigger).
pub open spec fn scheme_split_err_refute(
    s: Seq<u8>,
    k: int,
    ctx: Context,
) -> bool {
    &&& 1 <= k
    &&& k <= s.len()
    &&& super::is_ascii_alpha(s.index(0))
    &&& (forall|j: int| 1 <= j < k ==> super::is_scheme_char(s.index(j)))
    &&& ((k < s.len() && s.index(k) == 0x3Au8)
        || (k == s.len() && ctx == Context::Setter))
}

impl Parser<'_> {
    /// Origin Rust (parser.rs:399-423): pub fn parse_scheme<'i>(&mut self, input: Input<'i>)
    ///   -> Result<Input<'i>, ()>.
    /// Upstream comment (parser.rs:400): "starts_with will also fail for empty
    /// strings so we can skip that comparison for perf".
    /// The debug_assert on the empty serialization (parser.rs:404) is the
    /// requires below; the Ok side scans the scheme bytes into the
    /// serialization lowercased, the ':' terminator being pushed by the
    /// caller (parse_with_scheme, parser.rs:429); Err clears (parser.rs:411/420).
    pub exec fn parse_scheme<'i>(&mut self, input: Input<'i>) -> (r: Result<Input<'i>, ()>)
        requires
            input_wf(&input),
            old(self).serialization.view().len() == 0,
        ensures
            final(self).context == old(self).context,
            final(self).base_url == old(self).base_url,
            r.is_ok() ==> ({
                let s = input_rem(&input);
                exists|k: int|
                    1 <= k
                    && k <= s.len()
                    && final(self).serialization.view() == lowered_prefix(s.subrange(0, k), k)
                    && super::is_ascii_alpha(s.index(0))
                    && (forall|j: int| 1 <= j < k ==> super::is_scheme_char(s.index(j)))
                    && ((k < s.len() && s.index(k) == 0x3Au8
                        && input_rem(&r.unwrap()) == s.subrange(k + 1, s.len() as int)
                        && input_wf(&r.unwrap()))
                        || (k == s.len() && (old(self).context == Context::Setter)
                            && input_rem(&r.unwrap()).len() == 0
                            && input_wf(&r.unwrap())))
            }),
            r.is_err() ==> final(self).serialization.view().len() == 0,
            r.is_err() ==> ({
                let s = input_rem(&input);
                forall|k: int| #[trigger] scheme_split_err_refute(
                    s,
                    k,
                    old(self).context,
                ) == false
            }),
    {
        let s = input.bytes;
        let mut p = input.pos;
        let first = if p < s.len() { s[p] } else { 0x00u8 };
        if p >= s.len()
            || (
                !(0x41u8 <= first && first <= 0x5Au8) && !(0x61u8 <= first && first <= 0x7Au8)
            )
        {
            proof {
                let srem = input_rem(&input);
                if p >= s.len() {
                    assert(srem.len() == 0);
                } else {
                    vstd::seq::lemma_seq_subrange_index(s.view(),
                        input.pos as int, s.view().len() as int, 0);
                    assert(srem.index(0) == first);
                    assert(!super::is_ascii_alpha(srem.index(0)));
                }
                assert forall|k: int| 1 <= k <= srem.len()
                    ==> !scheme_split_err_refute(srem, k, old(self).context) by {
                }
            }
            return Err(());
        }
        let ghost sv = s.view();
        let mut done: u8 = 0;
        proof {
            let cur0 = input_rem(&input);
            assert(forall|j: int| 0 <= j < cur0.len()
                ==> machine_domain_byte(cur0.index(j)));
        }
        while p < s.len() && done == 0
            invariant
                input.pos <= p <= s.len(),
                (done as int) <= 2,
                done == 1 ==> p < s.len() && s.view().index(p as int) == 0x3Au8,
                done == 2 ==> p < s.len()
                    && !super::is_scheme_char(s.view().index(p as int))
                    && s.view().index(p as int) != 0x3Au8,
                forall|j: int| input.pos <= j < p ==>
                    (super::is_scheme_char(s.view().index(j as int))
                        && s.view().index(j as int) != 0x3Au8),
            decreases (if done == 0 { 1int } else { 0int }), s.len() - p,
        {
            let c = s[p];
            if c == 0x3Au8 {
                proof { assert(s.view().index(p as int) == c); }
                done = 1;
            } else {
                let is_sc = (0x61u8 <= c && c <= 0x7Au8) || (0x41u8 <= c && c <= 0x5Au8)
                    || (0x30u8 <= c && c <= 0x39u8) || c == 0x2Bu8 || c == 0x2Du8
                    || c == 0x2Eu8;
                proof {
                    assert(is_sc == super::is_scheme_char(s.view().index(p as int)));
                }
                if is_sc {
                    p += 1;
                } else {
                    proof {
                        assert(s.view().index(p as int) == c);
                        assert(c != 0x3Au8);
                    }
                    done = 2;
                }
            }
        }
        if done == 0 {
            // EOF before ':': the Setter returns Ok with the whole input scanned
            // (parser.rs:416-418); the UrlParser clears and fails (parser.rs:419-422).
            let ctx_c = self.context;
            match ctx_c {
                Context::Setter => {
                    proof {
                        assert(old(self).context == Context::Setter);
                    }
                let k = p - input.pos;
                self.push_lowered(s, input.pos, p);
                let rv: Result<Input, ()> = Ok(Input { bytes: input.bytes, pos: p });
                proof {
                    let srem = input_rem(&input);
                    let n = s.view().len() as int;
                    assert((p as int) == n);
                    let kps = s.view().subrange(input.pos as int, p as int);
                    vstd::seq::lemma_seq_subrange_composition(
                        s@, input.pos as int, n, 0, k as int);
                    assert(kps == srem.subrange(0, k as int));
                    assert(k as int >= 1);
                    assert((k as int) <= srem.len());
                    assert((k as int) == srem.len());
                    assert(final(self).serialization.view()
                        == lowered_prefix(kps, kps.len() as int));
                    assert(lowered_prefix(kps, k as int)
                        == lowered_prefix(srem.subrange(0, k as int), k as int));
                    assert(super::is_ascii_alpha(srem.index(0)));
                    assert(forall|j: int| 1 <= j < k as int
                        ==> super::is_scheme_char(srem.index(j)));
                    assert(kps.len() == k as int);
                    let tail = rv.unwrap();
                    assert(input_rem(&tail).len() == 0);
                    assert(machine_domain(Seq::empty()));
                    assert(input_ok(&tail));
                    let kw = k as int;
                    assert(exists|kk: int|
                        1 <= kk
                        && kk <= srem.len()
                        && final(self).serialization.view()
                            == lowered_prefix(srem.subrange(0, kk), kk)
                        && super::is_ascii_alpha(srem.index(0))
                        && (forall|j: int| 1 <= j < kk
                            ==> super::is_scheme_char(srem.index(j)))
                        && (kk == srem.len() && (old(self).context == Context::Setter)
                            && input_rem(&tail).len() == 0
                            && input_wf(&tail))
                    ) by {
                        assert(1 <= kw && kw <= srem.len());
                        assert(kw == srem.len());
                        assert(final(self).serialization.view()
                            == lowered_prefix(srem.subrange(0, kw), kw));
                        assert(super::is_ascii_alpha(srem.index(0)));
                        assert(forall|j: int| 1 <= j < kw
                            ==> super::is_scheme_char(srem.index(j)));
                        assert(old(self).context == Context::Setter);
                        assert(input_rem(&tail).len() == 0);
                        assert(input_wf(&tail));
                    }
                }
                    rv
                }
                _ => {
                    proof {
                        let srem = input_rem(&input);
                        assert(forall|j: int| 0 <= j < (p - input.pos) as int
                            ==> super::is_scheme_char(srem.index(j)));
                        assert forall|k: int|
                            1 <= k <= srem.len()
                            ==> !scheme_split_err_refute(srem, k, old(self).context) by {
                        };
                    }
                    Err(())
                }
            }
        } else if done == 1 {
            let k = p - input.pos;
            self.push_lowered(s, input.pos, p);
            let rv: Result<Input, ()> = Ok(Input { bytes: input.bytes, pos: (p + 1) as usize });
            proof {
                let srem = input_rem(&input);
                let n = s.view().len() as int;
                assert((p as int) < n);
                assert((k as int) < (srem.len() as int));
                vstd::seq::lemma_seq_subrange_index(s@, input.pos as int, s@.len() as int, k as int);
                assert(srem.index(k as int) == (s@).index((input.pos + k) as int));
                assert((s@).index((input.pos + k) as int) == (s)[p as int]);
                assert(srem.index(k as int) == 0x3Au8);
                let kps = s.view().subrange(input.pos as int, p as int);
                vstd::seq::lemma_seq_subrange_composition(
                    s@, input.pos as int, n, 0, k as int);
                assert(kps == srem.subrange(0, k as int));
                let kp = kps;
                assert(final(self).serialization.view()
                    == lowered_prefix(kp, kp.len() as int));
                assert(lowered_prefix(kp, kp.len() as int) == lowered_prefix(srem.subrange(0, k as int), k as int));
                assert(lowered_prefix(kp, k as int) == lowered_prefix(srem.subrange(0, k as int), k as int));
                assert(k >= 1);
                assert((k as int) <= srem.len());
                assert(super::is_ascii_alpha(srem.index(0)));
                assert(forall|j: int| 1 <= j < k as int
                    ==> super::is_scheme_char(srem.index(j)));
                let after = srem.subrange(k as int + 1, srem.len() as int);
                let tail = rv.unwrap();
                rem_shift(s, input.pos as int, (k as int) + 1);
                assert(input_rem(&tail) == srem.subrange((k as int) + 1, srem.len() as int));
                machine_domain_subrange(srem, (k as int) + 1, srem.len() as int);
                assert(machine_domain(input_rem(&tail)));
                assert((input_rem(&tail).len() as int) <= 0xFFFF_FFFF);
                assert(input_ok(&tail));
                let kw = k as int;
                assert(exists|kk: int|
                    1 <= kk
                    && kk <= srem.len()
                    && final(self).serialization.view()
                        == lowered_prefix(srem.subrange(0, kk), kk)
                    && super::is_ascii_alpha(srem.index(0))
                    && (forall|j: int| 1 <= j < kk
                        ==> super::is_scheme_char(srem.index(j)))
                    && (kk < srem.len() && srem.index(kk) == 0x3Au8
                        && input_rem(&tail) == srem.subrange(kk + 1, srem.len() as int)
                        && input_wf(&tail))
                ) by {
                    assert(1 <= kw && kw <= srem.len());
                    assert(final(self).serialization.view()
                        == lowered_prefix(srem.subrange(0, kw), kw));
                    assert(super::is_ascii_alpha(srem.index(0)));
                    assert(forall|j: int| 1 <= j < kw
                        ==> super::is_scheme_char(srem.index(j)));
                    assert(kw < srem.len() && srem.index(kw) == 0x3Au8);
                    assert(input_rem(&tail) == srem.subrange(kw + 1, srem.len() as int));
                    assert(input_wf(&tail));
                }
            }
            rv
        } else {
            proof {
                let srem = input_rem(&input);
                let pr = (p - input.pos) as int;
                assert(pr >= 0);
                // the done == 2 loop invariant pins the stop byte
                assert((s.view().len() as int) == (s.len() as int));
                assert((p as int) < (s.len() as int));
                assert((p as int) < (s.view().len() as int));
                vstd::seq::lemma_seq_subrange_index(s.view(),
                    input.pos as int, s.view().len() as int, pr);
                assert(srem.index(pr) == (s.view()).index(p as int));
                assert(!super::is_scheme_char((s.view()).index(p as int)));
                assert(!super::is_scheme_char(srem.index(pr)));
                assert((s.view()).index(p as int) != 0x3Au8);
                assert(srem.index(pr) != 0x3Au8);
                // the scanned prefix in rem coordinates (loop invariant;
                // same shape as the EOF arm)
                assert(forall|j: int|
                    0 <= j < (p - input.pos) as int
                    ==> super::is_scheme_char(srem.index(j)));
                assert(forall|j: int|
                    0 <= j < (p - input.pos) as int
                    ==> srem.index(j) != 0x3Au8);
                assert forall|k: int|
                    !scheme_split_err_refute(srem, k, old(self).context) by {
                    if k > pr {
                        assert(1 <= pr && pr < k);
                    } else if k < pr {
                        if 1 <= k {
                            assert(k < (p - input.pos) as int);
                            assert(srem.index(k) != 0x3Au8);
                        }
                    } else {
                        assert(k == pr);
                        if 1 <= k {
                            assert(srem.index(k) != 0x3Au8);
                        }
                    }
                };
            }
            Err(())
        }
    }

    /// The push loop of parse_scheme (the self.serialization.push arms of
    /// parser.rs:407-408; ASCII domain, so lowering is the A-Z byte shift).
    exec fn push_lowered(&mut self, s: &[u8], a: usize, b: usize)
        requires
            a <= b,
            b <= s.view().len(),
            self.serialization.view().len() == 0,
        ensures
            final(self).serialization.view()
                == lowered_prefix(s.view().subrange(a as int, b as int), (b - a) as int),
            final(self).context == old(self).context,
            final(self).base_url == old(self).base_url,
    {
        let ghost sv = s.view();
        let mut q = a;
        while q < b
            invariant
                s@ == sv,
                a <= q <= b,
                b <= sv.len(),
                self.serialization.view()
                    == lowered_prefix(sv.subrange(a as int, b as int), (q - a) as int),
            decreases b - q,
        {
            let ghost sr = sv.subrange(a as int, b as int);
            let nb = s[q];
            proof {
                assert(sr.index((q - a) as int) == nb);
                assert(lowered_prefix(sr, (q - a + 1) as int)
                    == lowered_prefix(sr, (q - a) as int)
                        + seq![lower_byte(sr.index((q - a) as int))]);
                assert(lower_byte(nb)
                    == (if 0x41u8 <= nb && nb <= 0x5Au8 { (nb + 32) as u8 } else { nb }));
            }
            if 0x41u8 <= nb && nb <= 0x5Au8 {
                proof { assert(nb + 32 <= 0x7Au8); }
                let l = nb + 32;
                proof { assert(lower_byte(nb) == l); }
                self.serialization.push(l);
            } else {
                proof { assert(lower_byte(nb) == nb); }
                self.serialization.push(nb);
            }
            proof {
                assert(self.serialization.view().len()
                    == lowered_prefix(sr, (q - a + 1) as int).len());
            }
            q += 1;
        }
    }
}


/* ============================================================
 * Port parsing (Origin: parser.rs:1094-1128)
 * ============================================================ */

/// dec_val extended by one trailing digit (the fold step of the port scan;
/// definitional modulo the subrange composition).
pub proof fn dec_val_push(u8d: u8, k: Seq<u8>)
    requires
        super::is_dec_digit(u8d),
    ensures
        super::dec_val(k + seq![u8d])
            == super::dec_val(k) * 10 + ((u8d as int) - 0x30),
{
    let full = k + seq![u8d];
    assert(full.subrange(0, full.len() as int - 1) == k) by {
        vstd::seq::lemma_seq_subrange_composition(
            full, 0, full.len() as int, 0, (full.len() as int) - 1);
    };
    vstd::seq::lemma_seq_subrange_index(full, (full.len() as int) - 1, full.len() as int, 0);
    assert(full.index((full.len() as int) - 1) == u8d);
}

/// Origin Rust (parser.rs:1094-1128): pub fn parse_port<P>(input: Input, P: Fn() -> Option<u16>, context: Context)
///   -> ParseResult<(Option<u16>, Input)>
/// ledger: the P closure (the default-port lookup of the caller, parser.rs:956)
/// folds to the value parameter (upstream evaluates it once after the scan,
/// the scheme prefix being fixed). The digit fold is the dec_val face of
/// lib.rs (validated against u16::MAX with ParseError::InvalidPort,
/// parser.rs:1107-1109); the UrlParser bad-terminator error is
/// parser.rs:1111-1112; the Setter empty-nonempty error is
/// parser.rs:1119-1121; the elision rule is parser.rs:1123-1126.
pub exec fn parse_port<'i>(
    input: Input<'i>,
    default_port: Option<u16>,
    context: Context,
) -> (r: Result<(Option<u16>, Input<'i>), ParseError>)
    requires
        input_wf(&input),
    ensures
        r.is_ok() ==> ({
            let s = input_rem(&input);
            let plen = (r.unwrap()).1.pos - input.pos;
            let opt = (r.unwrap()).0;
            &&& 0 <= plen
            &&& plen <= s.len()
            &&& (forall|j: int| 0 <= j < plen ==> super::is_dec_digit(s.index(j)))
            &&& plen < s.len() ==> !super::is_dec_digit(s.index(plen))
            &&& input_rem(&(r.unwrap()).1) == s.subrange(plen, s.len() as int)
            &&& input_wf(&(r.unwrap()).1)
            &&& (plen < s.len()
                ==> (s.index(plen) == 0x2Fu8 || s.index(plen) == 0x5Cu8
                    || s.index(plen) == 0x3Fu8 || s.index(plen) == 0x23u8
                    || context != Context::UrlParser))
            &&& opt
                == (if plen > 0 && (default_port.is_none()
                    || default_port.unwrap() != (super::dec_val(s.subrange(0, plen)) as u16))
                {
                    Option::Some(super::dec_val(s.subrange(0, plen)) as u16)
                } else {
                    Option::None
                })
        }),
        r.is_err() ==> r == Err(ParseError::InvalidPort),
{
    let s = input.bytes;
    let mut p = input.pos;
    let mut port: u32 = 0;
    proof {
        let cur0 = input_rem(&input);
        assert(forall|j: int| 0 <= j < cur0.len() ==> machine_domain_byte(cur0.index(j)));
        assert((0 as int) == super::dec_val(Seq::empty()));
        assert(s.view().subrange(input.pos as int, input.pos as int) == Seq::empty());
    }
    let mut term = false;
    while p < s.len() && !term
        invariant
            input.pos <= p <= s.len(),
            (port as int) >= 0,
            (port as int) <= 0xFFFF,
            forall|j: int| input.pos <= j < p ==> super::is_dec_digit(s[j as int]),
            (port as int)
                == super::dec_val(s.view().subrange(input.pos as int, p as int)),
            term == false
                || (p < s.len()
                    && !super::is_dec_digit(s.view().index(p as int))),
        decreases (if term { 0int } else { 1int }), s.len() - p,
    {
        let c = s[p];
        if 0x30u8 <= c && c <= 0x39u8 {
            proof {
                assert((port as int) <= 0xFFFF);
                dec_val_push(c, s.view().subrange(input.pos as int, p as int));
                assert(s.view().subrange(input.pos as int, (p + 1) as int)
                    == s.view().subrange(input.pos as int, p as int) + seq![c]);
                assert(super::dec_val(s.view().subrange(input.pos as int, (p + 1) as int))
                    == (port as int) * 10 + ((c as int) - 0x30));
                assert((port as int) * 10 <= 655350);
                assert((port as int) * 10 + ((c as int) - 0x30) <= 655359);
            }
            port = port * 10 + ((c - 0x30u8) as u32);
            if port > 0xFFFF {
                return Err(ParseError::InvalidPort);
            }
            p += 1;
        } else {
            term = true;
        }
    }
    // upstream context checks (parser.rs:1110-1116, 1119-1121)
    if (match context { Context::UrlParser => true, _ => false }) {
        if p < s.len() {
            let c = s[p];
            if c != 0x2Fu8 && c != 0x5Cu8 && c != 0x3Fu8 && c != 0x23u8 {
                return Err(ParseError::InvalidPort);
            }
        }
    } else if p == input.pos
        && (match context { Context::Setter => true, _ => false })
        && p < s.len()
    {
        return Err(ParseError::InvalidPort);
    }
    let val = port as u16;
    let opt_port: Option<u16> = if p > input.pos {
        Some(val)
    } else {
        None
    };
    let out_port = if opt_port.is_some()
        && (default_port.is_none() || default_port.unwrap() != opt_port.unwrap())
    {
        opt_port
    } else {
        None
    };
    proof {
        let srem = input_rem(&input);
        let plen = (p - input.pos) as int;
        assert(plen >= 0 && plen <= srem.len());
        assert(forall|j: int| 0 <= j < plen ==> super::is_dec_digit(srem.index(j)));
        if plen < srem.len() {
            vstd::seq::lemma_seq_subrange_index(srem, plen, srem.len() as int, 0);
        }
        rem_shift(s, input.pos as int, plen);
        let tail = Input { bytes: s, pos: p };
        assert(srem.subrange(plen, srem.len() as int) == input_rem(&tail));
        machine_domain_subrange(srem, plen, srem.len() as int);
        assert(machine_domain(input_rem(&tail)));
        assert(input_ok(&tail));
    }
    proof {
        let plen = (p - input.pos) as int;
        let srem = input_rem(&input);
        vstd::seq::lemma_seq_subrange_composition(s.view(), input.pos as int,
            s.view().len() as int, 0, plen);
        assert(srem.subrange(0, plen) == s.view().subrange(input.pos as int, p as int));
        let tail = Input { bytes: s, pos: p };
        assert(plen >= 0);
        assert(plen <= srem.len());
        assert(input_rem(&tail) == srem.subrange(plen, srem.len() as int));
        assert(forall|j: int| 0 <= j < plen ==> super::is_dec_digit(srem.index(j)));
        if plen < srem.len() {
            vstd::seq::lemma_seq_subrange_index(srem, plen, srem.len() as int, 0);
        }
        machine_domain_subrange(srem, plen, srem.len() as int);
        assert(machine_domain(input_rem(&tail)));
        assert((tail.bytes.view().len() as int) <= 0xFFFF_FFFF);
        assert((input_rem(&tail).len() as int) <= 0xFFFF_FFFF);
        assert(input_ok(&tail));
        assert(input_wf(&tail));
        if plen < srem.len() {
            let bb = srem.index(plen);
            assert(!super::is_dec_digit(bb));
            let urlparser = (match context { Context::UrlParser => true, _ => false });
            if urlparser {
                assert(bb == 0x2Fu8 || bb == 0x5Cu8 || bb == 0x3Fu8 || bb == 0x23u8);
            }
        }
        if p > input.pos {
            let dv = super::dec_val(srem.subrange(0, plen));
            assert(dv == (port as int));
            assert(dv >= 0);
            assert(dv <= 0xFFFF);
            assert((dv as u16) == (port as u16));
            assert(out_port
                == (if default_port.is_none() || default_port.unwrap() != (dv as u16) {
                    Option::Some(dv as u16)
                } else {
                    Option::None
                }));
        } else {
            assert(out_port.is_none());
        }
    }
    Ok((out_port, Input { bytes: s, pos: p }))
}

/* ============================================================
 * Query and fragment placement (Origin: parser.rs:1494-1674)
 * ============================================================ */

/// The range-based encoder: extend_percent_encode specialized to a byte
/// range of a backing slice (the push_pending bulk selection of
/// parser.rs:1176-1197 minus the PathSegmentSetter context split, which
/// belongs to the path batch).
pub exec fn extend_percent_encode_at(
    ser: &mut Vec<u8>,
    s: &[u8],
    a: usize,
    b: usize,
    set: EncodeSet,
)
    requires
        a <= b,
        b <= s.view().len(),
        machine_domain(s.view().subrange(a as int, b as int)),
        old(ser).view().len() + 3 * ((b - a) as int) <= 0xFFFF_FFFF,
    ensures
        final(ser).view()
            == old(ser).view() + enc_seq(s.view().subrange(a as int, b as int), set),
{
    let ghost pre = ser.view();
    let ghost sv = s.view();
    let mut i: usize = a;
    while i < b
        invariant
            s@ == sv,
            a <= b,
            b <= s.len(),
            machine_domain(sv.subrange(a as int, b as int)),
            pre == old(ser).view(),
            a <= i <= b,
            ser.view() == pre + enc_seq(sv.subrange(a as int, i as int), set),
            (ser.view().len() as int) + 3 * ((b as int) - (i as int))
                <= 0xFFFF_FFFF,
        decreases b - i,
    {
        proof {
            assert((b as int) - (i as int) >= 1);
            assert((i as int) >= (a as int));
            assert((i as int) < (b as int));
            assert(((i as int) - (a as int)) < ((b as int) - (a as int)));
            machine_domain_subrange(sv.subrange(a as int, b as int),
                0, ((i as int) - (a as int)) + 1);
            enc_prefix_next(sv.subrange(a as int, b as int), (i as int) - (a as int), set);
            vstd::seq::lemma_seq_subrange_composition(sv, a as int, b as int, 0,
                ((i as int) - (a as int)) + 1);
            vstd::seq::lemma_seq_subrange_composition(sv, a as int, b as int, 0, (i as int) - (a as int));
            vstd::seq::lemma_seq_subrange_index(sv.subrange(a as int, b as int),
                0, ((i as int) - (a as int)) + 1, (i as int) - (a as int));
            assert(enc_seq(sv.subrange(a as int, (i + 1) as int), set)
                == enc_seq(sv.subrange(a as int, i as int), set)
                    + enc_byte(sv.index(i as int), set));
            assert(enc_byte(sv.index(i as int), set).len() <= 3);
        }
        let c = s[i];
        if in_set_exec(set, c) {
            proof {
                assert((c / 16) < 16);
                assert((c % 16) < 16);
                assert(((c as int) / 16) <= 15);
                assert(((c as int) % 16) <= 15);
            }
            let hi = hex_digit_exec((c / 16) as u8);
            let lo = hex_digit_exec((c % 16) as u8);
            vec_push3(ser, 0x25u8, hi, lo);
        } else {
            let ghost before_push = ser.view();
            ser.push(c);
            proof {
                assert(ser.view() == before_push.push(c));
                assert(before_push.push(c) == before_push + seq![c]);
            }
        }
        i += 1;
    }
    proof {
        assert(sv.subrange(a as int, b as int).subrange(0, (b as int) - (a as int))
            == sv.subrange(a as int, b as int));
    }
}

impl Parser<'_> {

/// Origin Rust (parser.rs:1495-1522): fn parse_query_and_fragment(&mut self,
///   scheme_type, scheme_end, input) -> ParseResult<(Option<u32>, Option<u32>)>.
/// Upstream contract: the input starts at '?' or '#' (the panic at
/// parser.rs:1515 is a programming-error guard of the same states); the
/// query elision and violation-logging layers are outside the verus surface.
pub exec fn parse_query_and_fragment<'i>(
    &mut self,
    scheme_type: SchemeType,
    scheme_end: u32,
    input: Input<'i>,
) -> (r: Result<(Option<u32>, Option<u32>), ParseError>)
    requires
        input_wf(&input),
        input_rem(&input).len() > 0,
        input_rem(&input).index(0 as int) == 0x3Fu8 || input_rem(&input).index(0 as int) == 0x23u8,
        old(self).serialization.view().len()
            + 6 * (input_rem(&input).len() as int) + 10
            <= 0xFFFF_FFFF,
        (scheme_end as int) <= old(self).serialization.view().len(),
        machine_domain(old(self).serialization.view()),
    ensures
        ({
            let serf0 = final(self).serialization.view();
            let pre0 = old(self).serialization.view();
            machine_domain(serf0)
                && (r.is_err() ==> (r == Err(ParseError::Overflow)))
                && (forall|j: int| 0 <= j < pre0.len()
                    ==> serf0.index(j) == pre0.index(j))
        }),
        r.is_ok() ==> ({
            let qf = r.unwrap();
            let serf = final(self).serialization.view();
            &&& serf.len() > old(self).serialization.view().len()
            &&& (input_rem(&input).index(0) == 0x3Fu8
                ==> qf.0.is_some())
            &&& (serf.len() as int)
                <= old(self).serialization.view().len()
                    + 6 * (input_rem(&input).len() as int) + 4
            &&& (qf.0.is_some()
                ==> serf.index((qf.0.unwrap() as int)) == 0x3Fu8
                    && (qf.0.unwrap() as int)
                        == old(self).serialization.view().len())
            &&& (qf.1.is_some()
                ==> serf.index((qf.1.unwrap() as int)) == 0x23u8
                    && (qf.1.unwrap() as int)
                        >= old(self).serialization.view().len()
                    && (qf.1.unwrap() as int) < serf.len())
            &&& (qf.0.is_some() && qf.1.is_some()
                ==> (qf.0.unwrap() as int)
                    < (qf.1.unwrap() as int))
            &&& (qf.0.is_none() && qf.1.is_some()
                ==> (qf.1.unwrap() as int)
                    == old(self).serialization.view().len())
            &&& (qf.0.is_some() || qf.1.is_some())
        }),
    {
    let ghost rem0 = input_rem(&input);
    if input.bytes[input.pos] == 0x3Fu8 {
        // query state (parser.rs:1504-1513)
        let qstart32 = match to_u32(self.serialization.len()) {
            Ok(i) => i,
            Err(e) => return Err(e),
        };
        proof {
            assert(qstart32 as int == self.serialization.view().len());
        }
        let ghost before_q = self.serialization.view();
        self.serialization.push(0x3Fu8);
        proof {
            assert(self.serialization.view() == before_q.push(0x3Fu8));
            assert(self.serialization.view() == before_q + seq![0x3Fu8]);
            assert(self.serialization.view().index(qstart32 as int) == 0x3Fu8);
        }
        let rest = Input { bytes: input.bytes, pos: input.pos + 1 };
        proof {
            rem_shift(input.bytes, input.pos as int, 1);
            machine_domain_subrange(rem0, 1, rem0.len() as int);
        }
        let after_query = self.parse_query(scheme_type, scheme_end, rest);
        proof {
            assert(machine_domain(before_q + seq![0x3Fu8]));
        }
        match after_query {
            None => {
                proof {
                    let pv = before_q.push(0x3Fu8);
                    let qs = if is_special(scheme_type) {
                        EncodeSet::SpecialQuery
                    } else {
                        EncodeSet::Query
                    };
                    let encq = enc_seq(input_rem(&rest), qs);
                    assert(self.serialization.view() == pv + encq);
                    enc_seq_machine(input_rem(&rest), qs);
                    machine_domain_add(pv, encq);
                    assert(machine_domain(self.serialization.view()));
                    assert forall|j: int| 0 <= j < before_q.len()
                        implies self.serialization.view().index(j)
                            == before_q.index(j) by {
                        vstd::seq::lemma_seq_add_index1(pv, encq, j);
                        vstd::seq::lemma_seq_add_index1(before_q,
                            seq![0x3Fu8], j);
                    }
                    enc_seq_len_bound(input_rem(&rest), qs);
                    vstd::seq::lemma_seq_add_len(pv, encq);
                    assert((self.serialization.view().len() as int)
                        <= (pv.len() as int)
                            + 3 * (input_rem(&rest).len() as int));
                    assert((self.serialization.view().len() as int)
                        <= old(self).serialization.view().len()
                            + 6 * (input_rem(&input).len() as int) + 4);
                }
                return Ok((Some(qstart32), None));
            }
            Some(remaining) => {
                proof {
                    assert(before_q == old(self).serialization.view());
                    assert(input_rem(&rest) == rem0.subrange(1, rem0.len() as int));
                    // the machine domain survives the query write (the
                    // '?' push plus the encoded query prefix)
                    let pvq = before_q + seq![0x3Fu8];
                    assert(machine_domain(pvq));
                    let qs0 = if is_special(scheme_type) {
                        EncodeSet::SpecialQuery
                    } else {
                        EncodeSet::Query
                    };
                    let encq2 = enc_seq(input_rem(&rest).subrange(
                        0, input_rem(&rest).len() as int
                            - input_rem(&remaining).len() as int - 1), qs0);
                    assert(self.serialization.view() == pvq + encq2);
                    machine_domain(input_rem(&rest).subrange(
                        0, input_rem(&rest).len() as int
                            - input_rem(&remaining).len() as int - 1));
                    enc_seq_machine(input_rem(&rest).subrange(
                        0, input_rem(&rest).len() as int
                            - input_rem(&remaining).len() as int - 1), qs0);
                    machine_domain_add(pvq, encq2);
                    assert(machine_domain(self.serialization.view()));
                }
                let fstart32 = match to_u32(self.serialization.len()) {
                    Ok(i) => i,
                    Err(e) => return Err(e),
                };
                let ghost before_f = self.serialization.view();
                self.serialization.push(0x23u8);
                proof {
                    assert(self.serialization.view() == before_f.push(0x23u8));
                    assert(self.serialization.view() == before_f + seq![0x23u8]);
                    assert(self.serialization.view().index(fstart32 as int) == 0x23u8);
                }
                let rest2 = Input { bytes: remaining.bytes, pos: remaining.pos };
                proof {
                    let acc = self.serialization.view().len() as int;
                    assert(acc <= ((self.serialization.view().len()) as int) + 1);
                    let inlen = input_rem(&input).len() as int;
                    let s0 = old(self).serialization.view().len() as int;
                    // parse_query growth bound at the call: ser after query <= S0 + 1
                    //   + 3*rest.len + 1   (the '?' push plus at-most-3-per-byte)
                    assert(acc <= s0 + 2 + 3 * (inlen - 0));
                    // rest2 (the fragment input) is a short tail of the original input
                    assert((input_rem(&rest2).len() as int) + 2 <= inlen);
                    assert(acc + 3 * (input_rem(&rest2).len() as int)
                        <= s0 + 2 + 3 * inlen + 3 * inlen);
                    assert(s0 + 2 + 6 * inlen <= 0xFFFF_FFFF - 3);
                }
                self.parse_fragment(rest2);
                proof {
                    let pv = before_f.push(0x23u8);
                    let encf = enc_seq(input_rem(&rest2), EncodeSet::Fragment);
                    assert(self.serialization.view() == pv + encf);
                    machine_domain_add(before_f, seq![0x23u8]);
                    assert(machine_domain(pv));
                    enc_seq_machine(input_rem(&rest2), EncodeSet::Fragment);
                    machine_domain_add(pv, encf);
                    assert(machine_domain(self.serialization.view()));
                    assert forall|j: int| 0 <= j < before_f.len()
                        implies self.serialization.view().index(j)
                            == before_f.index(j) by {
                        vstd::seq::lemma_seq_add_index1(pv, encf, j);
                        vstd::seq::lemma_seq_add_index1(before_f,
                            seq![0x23u8], j);
                    }
                    enc_seq_len_bound(input_rem(&rest2), EncodeSet::Fragment);
                    vstd::seq::lemma_seq_add_len(pv, encf);
                    assert((self.serialization.view().len() as int)
                        <= (pv.len() as int)
                            + 3 * (input_rem(&rest2).len() as int));
                    assert((self.serialization.view().len() as int)
                        <= old(self).serialization.view().len()
                            + 6 * (input_rem(&input).len() as int) + 4);
                }
                return Ok((Some(qstart32), Some(fstart32)));
            }
        }
    } else {
        // fragment state (parser.rs:1502-1503, 1517-1521)
        let fstart32 = match to_u32(self.serialization.len()) {
            Ok(i) => i,
            Err(e) => return Err(e),
        };
        let ghost before_f = self.serialization.view();
        self.serialization.push(0x23u8);
        proof {
            assert(self.serialization.view() == before_f.push(0x23u8));
            assert(self.serialization.view() == before_f + seq![0x23u8]);
            assert(self.serialization.view().index(fstart32 as int) == 0x23u8);
        }
        let rest = Input { bytes: input.bytes, pos: input.pos + 1 };
        proof {
            rem_shift(input.bytes, input.pos as int, 1);
            machine_domain_subrange(rem0, 1, rem0.len() as int);
            let acc = self.serialization.view().len() as int;
            assert(input_rem(&rest).len() + 1 <= input_rem(&input).len());
            assert(acc <= old(self).serialization.view().len() + 1);
            assert(acc + 3 * (input_rem(&rest).len() as int)
                <= old(self).serialization.view().len() + 1
                    + 3 * (input_rem(&input).len() as int));
            assert(old(self).serialization.view().len() + 1
                + 3 * (input_rem(&input).len() as int) <= 0xFFFF_FFFF - 3);
        }
        self.parse_fragment(rest);
        proof {
            let pv = before_f.push(0x23u8);
            let encf = enc_seq(input_rem(&rest), EncodeSet::Fragment);
            assert(self.serialization.view() == pv + encf);
            machine_domain_add(before_f, seq![0x23u8]);
            assert(machine_domain(pv));
            enc_seq_machine(input_rem(&rest), EncodeSet::Fragment);
            machine_domain_add(pv, encf);
            assert(machine_domain(self.serialization.view()));
            assert forall|j: int| 0 <= j < before_f.len()
                implies self.serialization.view().index(j)
                    == before_f.index(j) by {
                vstd::seq::lemma_seq_add_index1(pv, encf, j);
                vstd::seq::lemma_seq_add_index1(before_f, seq![0x23u8], j);
            }
            enc_seq_len_bound(input_rem(&rest), EncodeSet::Fragment);
            vstd::seq::lemma_seq_add_len(pv, encf);
            assert((self.serialization.view().len() as int)
                <= (pv.len() as int)
                    + 3 * (input_rem(&rest).len() as int));
            assert((self.serialization.view().len() as int)
                <= old(self).serialization.view().len()
                    + 6 * (input_rem(&input).len() as int) + 4);
        }
        proof {
            assert(fstart32 as int
                == old(self).serialization.view().len());
        }
        return Ok((None, Some(fstart32)));
    }
}

/// Origin Rust (parser.rs:1524-1603): pub fn parse_query(&mut self, scheme_type, scheme_end, input)
///   -> Option<Input>  -- Some(remaining) iff a '#' terminator was found
///   (parser.rs:1597-1599); None ends the input (parser.rs:1602).
/// The query_encoding_override arms (parser.rs:1582-1592) are the legacy
/// HTML encoding layer and are outside the verus surface.
pub exec fn parse_query<'i>(
    &mut self,
    scheme_type: SchemeType,
    scheme_end: u32,
    input: Input<'i>,
) -> (o: Option<Input<'i>>)
    requires
        input_wf(&input),
        (scheme_end as int) <= old(self).serialization.view().len(),
        machine_domain(old(self).serialization.view()),
        old(self).serialization.view().len()
            + 3 * (input_rem(&input).len() as int) + 3 <= 0xFFFF_FFFF,
    ensures
        o.is_some()
            ==> (input_rem(&o.unwrap()).len() < input_rem(&input).len()
                && input_wf(&o.unwrap())),
        o.is_none()
            ==> (input_rem(&input).len() == 0
                || input_rem(&input).index(input_rem(&input).len() - 1)
                    != 0x23u8),
        o.is_some()
            ==> final(self).serialization.view()
                == old(self).serialization.view()
                    + enc_seq(
                        input_rem(&input).subrange(
                            0,
                            input_rem(&input).len() - input_rem(&o.unwrap()).len() - 1,
                        ),
                        if is_special(scheme_type) {
                            EncodeSet::SpecialQuery
                        } else {
                            EncodeSet::Query
                        },
                    ),
        o.is_none()
            ==> final(self).serialization.view()
                == old(self).serialization.view()
                    + enc_seq(
                        input_rem(&input),
                        if is_special(scheme_type) {
                            EncodeSet::SpecialQuery
                        } else {
                            EncodeSet::Query
                        },
                    ),
        final(self).serialization.view().len()
            <= old(self).serialization.view().len()
                + 3 * (input_rem(&input).len() as int) + 1,
{
    let set: EncodeSet = if scheme_type.is_special() {
        EncodeSet::SpecialQuery
    } else {
        EncodeSet::Query
    };
    let ghost set_choice: EncodeSet = set;
    let s = input.bytes;
    let mut p = input.pos;
    // scan to the '#' terminator (parser.rs:1543-1556)
    while p < s.len() && (p >= s.len() || s[p] != 0x23u8)
        invariant
            input.pos <= p <= s.len(),
            forall|j: int| (input.pos as int) <= j < (p as int)
                ==> ((s)[j] != 0x23u8),
        decreases s.len() - p,
    {
        p += 1;
    }
    let end = p;
    proof {
        let srem0 = input_rem(&input);
        assert(machine_domain(srem0));
        machine_domain_subrange(srem0, 0, (end - input.pos) as int);
    }
    let ghost srem = input_rem(&input);
    extend_percent_encode_at(&mut self.serialization, s, input.pos, end, set);
    proof {
        vstd::seq::lemma_seq_subrange_composition(s.view(), input.pos as int,
            s.view().len() as int, 0, (end - input.pos) as int);
        assert(srem.subrange(0, (end - input.pos) as int)
            == s.view().subrange(input.pos as int, end as int));
    }
    if p < s.len() {
        // '#' terminator (parser.rs:1551-1555): the rest is fragment-bound
        let rest = Input { bytes: s, pos: p + 1 };
        proof {
            assert(s[p as int] == 0x23u8);
            rem_shift(s, input.pos as int, (p - input.pos) as int + 1);
            machine_domain_subrange(srem, (p - input.pos) as int + 1, srem.len() as int);
            assert(machine_domain(input_rem(&rest)));
            assert(input_ok(&rest));
            assert((input_rem(&rest).len()) + 1 == srem.len() - (p - input.pos) as int);
            assert(((p - input.pos) as int) == srem.len() - input_rem(&rest).len() - 1);
            let k = (p - input.pos) as int;
            let encp = enc_seq(srem.subrange(0, k), set_choice);
            enc_seq_len_bound(srem.subrange(0, k), set_choice);
            vstd::seq::lemma_seq_add_len(old(self).serialization.view(), encp);
            assert(encp.len() <= 3 * k);
            assert(k <= input_rem(&input).len());
        }
        Option::Some(rest)
    } else {
        proof {
            assert(srem.len() >= 0);
            let last = srem.len() - 1;
            if srem.len() > 0 {
                assert(end >= input.pos);
                assert(s.view().index(end as int - 1) != 0x23u8) by {
                    vstd::seq::lemma_seq_subrange_index(s.view(),
                        (end as int) - 1, s.view().len() as int, 0);
                }
                assert(srem.index(last) != 0x23u8);
            } else {
                assert(srem.len() == 0);
            }
            let k = srem.len() as int;
            let encp = enc_seq(srem.subrange(0, k), set_choice);
            enc_seq_len_bound(srem.subrange(0, k), set_choice);
            vstd::seq::lemma_seq_add_len(old(self).serialization.view(), encp);
            assert(encp.len() <= 3 * k);
            assert(k <= input_rem(&input).len());
        }
        Option::None
    }
}

/// Origin Rust (parser.rs:1625-1674): pub fn parse_fragment(&mut self, input)
///   -- percent-encode with the FRAGMENT set to the end of the input (the
///   '\0' logging arm of the FragmentPartIter, parser.rs:1645-1649, is the
///   dropped observation layer).
pub exec fn parse_fragment<'i>(&mut self, input: Input<'i>)
    requires
        input_wf(&input),
        old(self).serialization.view().len()
            + 3 * (input_rem(&input).len() as int) <= 0xFFFF_FFFF,
    ensures
        final(self).serialization.view()
            == old(self).serialization.view()
                + enc_seq(input_rem(&input), EncodeSet::Fragment),
{
    extend_percent_encode_at(
        &mut self.serialization,
        input.bytes,
        input.pos,
        input.bytes.len(),
        EncodeSet::Fragment,
    );
}

/// Origin Rust (parser.rs:1524-1603): the Setter-context face of
/// parse_query -- the same encoder walk without the URL-parser's
/// '#' stop (QueryPartIter's is_url_parser gate, parser.rs:1540-1546,
/// is false in the for-setter Parser, so a '#' byte of the payload
/// stays inside the part and percent-encodes through the
/// QUERY/SPECIAL_QUERY set membership; upstream set_query invoked
/// exactly this face through Parser::for_setter, lib.rs:1646-1652).
/// The query_encoding_override gate (parser.rs:1569-1574) reads the
/// record's scheme region only when a serializer installed an
/// override (the query_pairs_mut face), which the plain setter face
/// never carries; that layer stays outside the verus surface per
/// the parse_query ledger note, and the scheme_end bound it demanded
/// drops with it. The new_trim_tab_and_newlines entry trim
/// (lib.rs:1651) is the identity on the machine byte domain (its
/// three bytes are exactly the excluded ones), so the raw Input over
/// the payload is the faithful mirror.
pub exec fn parse_query_setter<'i>(
    &mut self,
    scheme_type: SchemeType,
    input: Input<'i>,
)
    requires
        input_wf(&input),
        self.context == Context::Setter,
        old(self).serialization.view().len()
            + 3 * (input_rem(&input).len() as int)
            <= 0xFFFF_FFFF,
    ensures
        final(self).serialization.view()
            == old(self).serialization.view()
                + enc_seq(
                    input_rem(&input),
                    if is_special(scheme_type) {
                        EncodeSet::SpecialQuery
                    } else {
                        EncodeSet::Query
                    },
                ),
{
    let set: EncodeSet = if scheme_type.is_special() {
        EncodeSet::SpecialQuery
    } else {
        EncodeSet::Query
    };
    extend_percent_encode_at(
        &mut self.serialization,
        input.bytes,
        input.pos,
        input.bytes.len(),
        set,
    );
}

}   // close the query/fragment placement impl

/* ============================================================
 * Shared appenders and byte predicates of the scanner segments
 * (the write! / push_str faces: plain machine-ASCII runs)
 * ============================================================ */

/// The plain byte-run append face of `write!(&mut self.serialization, ...)`
/// on a run that is already machine-ASCII (no percent-encoding applies).
pub exec fn vec_append_bytes(ser: &mut Vec<u8>, part: &[u8])
    requires
        machine_domain(part@),
        old(ser).view().len() + (part@.len() as int) <= 0xFFFF_FFFF,
    ensures
        final(ser).view() == old(ser).view() + part@,
{
    let ghost pre = ser.view();
    let ghost pv = part.view();
    let mut i: usize = 0;
    while i < part.len()
        invariant
            part@ == pv,
            machine_domain(pv),
            pre == old(ser).view(),
            i <= part.len(),
            ser.view() == pre + pv.subrange(0, i as int),
            (ser.view().len() as int) + (pv.len() as int) - (i as int)
                <= 0xFFFF_FFFF,
        decreases part.len() - i,
    {
        let ghost before_push = ser.view();
        let c = part[i];
        proof {
            assert(pv.index(i as int) == c);
        }
        ser.push(c);
        proof {
            assert(ser.view() == before_push.push(c));
            assert(before_push.push(c) == before_push + seq![c]);
        }
        i += 1;
    }
}

/// Exec twin of lib.rs is_ascii_alpha (the ascii_alpha predicate face,
/// parser.rs:1737-1739).
pub exec fn is_ascii_alpha_exec(b: u8) -> (r: bool)
    ensures
        r == super::is_ascii_alpha(b),
{
    (b >= 0x41u8 && b <= 0x5Au8) || (b >= 0x61u8 && b <= 0x7Au8)
}

/// The exec close-over of `to_u32(self.serialization.len())?` on the
/// machine's pre-bounded growth (the Overflow arm is out of the
/// transcription domain: every length bound is carried as a precondition
/// of the segment in question).
pub exec fn to_u32_ser(ser: &Vec<u8>) -> (v: u32)
    requires
        (ser.view().len() as int) <= 0xFFFF_FFFF,
    ensures
        (v as int) == (ser.view().len() as int),
{
    super::url_len32(ser)
}

/// machine_domain is closed under concatenation.
pub proof fn machine_domain_add(x: Seq<u8>, y: Seq<u8>)
    requires
        machine_domain(x),
        machine_domain(y),
    ensures
        machine_domain(x + y),
{
    vstd::seq::lemma_seq_add_len(x, y);
    assert forall|i: int| 0 <= i < (x + y).len()
        implies machine_domain_byte((x + y).index(i)) by {
        if i < x.len() {
            vstd::seq::lemma_seq_add_index1(x, y, i);
        } else {
            vstd::seq::lemma_seq_add_index2(x, y, i);
        }
    }
}

/// One encoded byte is machine-ASCII whenever the byte is (the hex digits
/// and the percent escape are all ASCII non-tab/non-newline).
pub proof fn enc_byte_machine(b: u8, set: EncodeSet)
    requires
        machine_domain_byte(b),
    ensures
        machine_domain(enc_byte(b, set)),
{
    if in_set(set, b) {
        let hx = hex_digit_byte((b as int) / 16);
        let hy = hex_digit_byte((b as int) % 16);
        assert(0 <= (b as int) / 16 <= 15);
        assert(0 <= (b as int) % 16 <= 15);
        if (b as int) % 16 <= 9 {
            assert(hy == (0x30 + ((b as int) % 16)) as u8);
        } else {
            assert(hy == (0x37 + ((b as int) % 16)) as u8);
        }
        assert(enc_byte(b, set) == seq![0x25u8, hx, hy]);
        assert(machine_domain_byte(0x25u8));
    } else {
        assert(enc_byte(b, set) == seq![b]);
    }
}

/// enc_seq of machine-ASCII input is machine-ASCII (the USERINFO/PATH
/// emission keeps the serialization inside the transcription domain).
pub proof fn enc_seq_machine(s: Seq<u8>, set: EncodeSet)
    requires
        machine_domain(s),
    ensures
        machine_domain(enc_seq(s, set)),
    decreases s.len(),
{
    if s.len() > 0 {
        let tail = s.subrange(1, s.len() as int);
        machine_domain_subrange(s, 1, s.len() as int);
        assert(machine_domain_byte(s.index(0)));
        enc_byte_machine(s.index(0), set);
        enc_seq_machine(tail, set);
        machine_domain_add(enc_byte(s.index(0), set), enc_seq(tail, set));
    }
}

/* ============================================================
 * Windows drive-letter predicates (Origin: parser.rs:1750-1794)
 * ============================================================ */

/// Origin Rust (parser.rs:1771-1776):
///   fn starts_with_windows_drive_letter(s: &str) -> bool {
///     s.len() >= 2 && ascii_alpha(s.as_bytes()[0] as char)
///     && matches!(s.as_bytes()[1], b':' | b'|')
///     && (s.len() == 2 || matches!(s.as_bytes()[2], b'/' | b'\\' | b'?' | b'#')) }
pub open spec fn starts_with_win_drive(s: Seq<u8>) -> bool {
    s.len() >= 2
        && super::is_ascii_alpha(s.index(0))
        && (s.index(1) == 0x3Au8 || s.index(1) == 0x7Cu8)
        && (s.len() == 2
            || s.index(2) == 0x2Fu8
            || s.index(2) == 0x5Cu8
            || s.index(2) == 0x3Fu8
            || s.index(2) == 0x23u8)
}

/// Origin Rust (parser.rs:1757-1759):
///   pub fn is_windows_drive_letter(segment: &str) -> bool
///     { segment.len() == 2 && starts_with_windows_drive_letter(segment) }
pub open spec fn is_win_drive(s: Seq<u8>) -> bool {
    s.len() == 2 && starts_with_win_drive(s)
}

/// Origin Rust (parser.rs:1750-1752):
///   fn is_normalized_windows_drive_letter(segment: &str) -> bool
///     { is_windows_drive_letter(segment) && segment.as_bytes()[1] == b':' }
pub open spec fn is_normalized_win_drive(s: Seq<u8>) -> bool {
    is_win_drive(s) && s.index(1) == 0x3Au8
}

/// Origin Rust (parser.rs:1763-1769):
///   fn path_starts_with_windows_drive_letter(s: &str) -> bool {
///     if let Some(c) = s.as_bytes().first() {
///         matches!(c, b'/' | b'\\' | b'?' | b'#')
///             && starts_with_windows_drive_letter(&s[1..])
///     } else { false } }
pub open spec fn path_starts_with_win_drive(s: Seq<u8>) -> bool {
    s.len() >= 1
        && (s.index(0) == 0x2Fu8 || s.index(0) == 0x5Cu8
            || s.index(0) == 0x3Fu8 || s.index(0) == 0x23u8)
        && starts_with_win_drive(s.subrange(1, s.len() as int))
}

/// The literal exec view of starts_with_win_drive at the suffix `s[from..]`
/// (the fixed-offset window reads of the path and host scanners).
pub exec fn starts_with_win_drive_at(s: &[u8], from: usize) -> (r: bool)
    requires
        from <= s.len(),
    ensures
        r == starts_with_win_drive(
            s.view().subrange(from as int, s.view().len() as int)),
{
    let n = s.len();
    if n - from < 2 {
        proof {
            assert(s.view().subrange(from as int, s.view().len() as int).len() < 2);
        }
        false
    } else {
        proof {
            assert(s.view().subrange(from as int, s.view().len() as int).len() >= 2);
        }
        let c0 = s[from];
        let c1 = s[from + 1];
        if !is_ascii_alpha_exec(c0) {
            proof {
                let sub = s.view().subrange(from as int, s.view().len() as int);
                assert(sub.index(0) == c0);
                assert(!super::is_ascii_alpha(sub.index(0)));
            }
            false
        } else if c1 != 0x3Au8 && c1 != 0x7Cu8 {
            proof {
                let sub = s.view().subrange(from as int, s.view().len() as int);
                assert(sub.index(1) == c1);
                assert(sub.index(1) != 0x3Au8);
                assert(sub.index(1) != 0x7Cu8);
            }
            false
        } else if from + 2 == n {
            proof {
                let sub = s.view().subrange(from as int, s.view().len() as int);
                assert(sub.len() == 2);
            }
            true
        } else {
            let c2 = s[from + 2];
            proof {
                let sub = s.view().subrange(from as int, s.view().len() as int);
                assert(sub.len() > 2);
                assert(sub.index(2) == c2);
            }
            c2 == 0x2Fu8 || c2 == 0x5Cu8 || c2 == 0x3Fu8 || c2 == 0x23u8
        }
    }
}

/// The exec twin of is_win_drive over the two bytes at s[from..from+2]
/// (is_windows_drive_letter applied to the host candidate of file_host).
pub exec fn is_win_drive_at(s: &[u8], from: usize) -> (r: bool)
    requires
        from + 2 <= s.len(),
    ensures
        r == is_win_drive(s.view().subrange(from as int, from as int + 2)),
{
    let c0 = s[from];
    let c1 = s[from + 1];
    let a0 = is_ascii_alpha_exec(c0);
    let b1 = c1 == 0x3Au8 || c1 == 0x7Cu8;
    proof {
        let sub = s.view().subrange(from as int, from as int + 2);
        assert(sub.len() == 2);
        assert(sub == seq![c0, c1]);
        if a0 && b1 {
            assert(starts_with_win_drive(seq![c0, c1]));
            assert(is_win_drive(seq![c0, c1]));
        } else {
            assert(!starts_with_win_drive(seq![c0, c1]));
            assert(!is_win_drive(seq![c0, c1]));
        }
    }
    a0 && b1
}

/// The exec twin of is_normalized_win_drive at the suffix `s[from..]`
/// (the whole-suffix two-byte form read by the file path scanner).
pub exec fn is_normalized_win_drive_at(s: &[u8], from: usize) -> (r: bool)
    requires
        from <= s.len(),
    ensures
        r == is_normalized_win_drive(
            s.view().subrange(from as int, s.view().len() as int)),
{
    if s.len() - from == 2 && s[from + 1] == 0x3Au8 {
        let sw = starts_with_win_drive_at(s, from);
        proof {
            let sub = s.view().subrange(from as int, s.view().len() as int);
            assert(sub.len() == 2);
            assert(sub.index(1) == 0x3Au8);
            if sw {
                assert(is_win_drive(sub));
                assert(is_normalized_win_drive(sub));
            } else {
                assert(!starts_with_win_drive(sub));
                assert(!is_win_drive(sub));
                assert(!is_normalized_win_drive(sub));
            }
        }
        sw
    } else {
        proof {
            let sub = s.view().subrange(from as int, s.view().len() as int);
            if sub.len() != 2 {
                assert(!is_win_drive(sub));
                assert(!is_normalized_win_drive(sub));
            } else {
                assert(sub.len() == 2);
                assert(sub.index(1) != 0x3Au8);
                if !starts_with_win_drive(sub) {
                    assert(!is_win_drive(sub));
                } else {
                    assert(is_win_drive(sub));
                }
                assert(!is_normalized_win_drive(sub));
            }
        }
        false
    }
}

/// Origin Rust (parser.rs:1779-1793): fn starts_with_windows_drive_letter_segment(input)
///   -> bool -- the two-arm 3-byte lookahead: either a drive letter plus a
/// delimiter ('/' | '\\' | '?' | '#'), or a drive letter ending the input.
pub exec fn starts_with_win_drive_seg<'i>(input: &Input<'i>) -> (r: bool)
    requires
        input_wf(input),
    ensures
        r == ({
            let s = input_rem(input);
            (s.len() >= 3
                && super::is_ascii_alpha(s.index(0))
                && (s.index(1) == 0x3Au8 || s.index(1) == 0x7Cu8)
                && (s.index(2) == 0x2Fu8 || s.index(2) == 0x5Cu8
                    || s.index(2) == 0x3Fu8 || s.index(2) == 0x23u8))
            || (s.len() == 2
                && super::is_ascii_alpha(s.index(0))
                && (s.index(1) == 0x3Au8 || s.index(1) == 0x7Cu8))
        }),
{
    let s = input.bytes;
    let p = input.pos;
    let n = s.len();
    let rem_len = n - p;
    if rem_len >= 3 {
        let c0 = s[p];
        let c1 = s[p + 1];
        let c2 = s[p + 2];
        proof {
            let cur = input_rem(input);
            assert(cur.len() == rem_len);
            assert(cur.index(0) == c0);
            assert(cur.index(1) == c1);
            assert(cur.index(2) == c2);
        }
        is_ascii_alpha_exec(c0) && (c1 == 0x3Au8 || c1 == 0x7Cu8)
            && (c2 == 0x2Fu8 || c2 == 0x5Cu8 || c2 == 0x3Fu8 || c2 == 0x23u8)
    } else if rem_len == 2 {
        let c0 = s[p];
        let c1 = s[p + 1];
        proof {
            let cur = input_rem(input);
            assert(cur.len() == 2);
            assert(cur.index(0) == c0);
            assert(cur.index(1) == c1);
        }
        is_ascii_alpha_exec(c0) && (c1 == 0x3Au8 || c1 == 0x7Cu8)
    } else {
        proof {
            let cur = input_rem(input);
            assert(cur.len() < 2);
        }
        false
    }
}

/// Origin Rust (parser.rs:1763-1769) exec twin at a fixed suffix:
/// path_starts_with_win_drive on `s[from..]` (the suffix test of
/// last_slash_can_be_removed at a slash position).
pub exec fn path_starts_with_win_drive_at(s: &[u8], from: usize) -> (r: bool)
    requires
        from <= s.len(),
    ensures
        r == path_starts_with_win_drive(
            s.view().subrange(from as int, s.view().len() as int)),
{
    if from < s.len() {
        let c0 = s[from];
        proof {
            let sub = s.view().subrange(from as int, s.view().len() as int);
            assert(sub.index(0) == c0);
            assert(sub.subrange(1, sub.len() as int)
                == s.view().subrange(from as int + 1, s.view().len() as int));
        }
        (c0 == 0x2Fu8 || c0 == 0x5Cu8 || c0 == 0x3Fu8 || c0 == 0x23u8)
            && starts_with_win_drive_at(s, from + 1)
    } else {
        proof {
            assert(s.view().subrange(from as int, s.view().len() as int).len() == 0);
        }
        false
    }
}

/* ============================================================
 * Userinfo scan (Origin: parser.rs:859-932)
 * ============================================================ */

/// The host-terminator wall byte of the userinfo scan (parser.rs:878-879):
/// '/' | '?' | '#' always, '\\' additionally when the scheme is special.
pub open spec fn userinfo_wall_byte(b: u8, special: bool) -> bool {
    b == 0x2Fu8 || b == 0x3Fu8 || b == 0x23u8 || (special && b == 0x5Cu8)
}

/// Exec twin of userinfo_wall_byte.
pub exec fn userinfo_wall_byte_exec(b: u8, special: bool) -> (r: bool)
    ensures
        r == userinfo_wall_byte(b, special),
{
    b == 0x2Fu8 || b == 0x3Fu8 || b == 0x23u8 || (special && b == 0x5Cu8)
}

impl Parser<'_> {

/// Origin Rust (parser.rs:860-932): fn parse_userinfo(&mut self, input, scheme_type)
///   -> ParseResult<(u32, Input<'i>)>.
/// Scan shape: walk the input bytes up to the first wall byte
/// (parser.rs:867-883), tracking the last '@' of that span; no '@' leaves
/// the serialization untouched and hands back the receiving input unchanged
/// (parser.rs:885). A leading '@' (empty userinfo) is dropped and the input
/// after it handed back, failing with EmptyHost when the next byte is a wall
/// (parser.rs:886-897). Otherwise the '@' at position k (the code keeps the
/// last one of the span) splits the first k scanned bytes at the first ':'
/// (the password marker, itself not serialized when the password is empty,
/// parser.rs:907-914) into the username and password runs, both
/// percent-encoded with the USERINFO set, and '@' is appended when anything
/// was written (parser.rs:924-930). The tab filtering of Input::next is
/// outside the transcription domain (the byte model is faithful on
/// machine_domain inputs); the char_count of upstream is the q cursor below.
/// The witnesses of arm C: k is the rem offset of the recorded '@' and p the
/// rem offset of the first ':' of the span (or k when the span has none).
pub exec fn parse_userinfo<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
) -> (r: Result<(u32, Input<'i>), ParseError>)
    requires
        input_wf(&input),
        machine_domain(old(self).serialization.view()),
        old(self).serialization.view().len()
            + 3 * (input_rem(&input).len() as int) + 3 <= 0xFFFF_FFFF,
    ensures
        ({
            let before = old(self).serialization.view();
            let serf = final(self).serialization.view();
            let s = input_rem(&input);
            let special = is_special(scheme_type);
            &&& machine_domain(serf)
            &&& serf.len() <= before.len() + 3 * (s.len() as int) + 2
            &&& (final(self).context == old(self).context)
            &&& (forall|j: int| 0 <= j && j < before.len()
                ==> serf.index(j) == before.index(j))
            &&& (r.is_err()
                ==> (r == Err(ParseError::EmptyHost) && serf == before))
            &&& (r.is_ok()
                ==> ({
                    let (ue, rest) = r.unwrap();
                    &&& input_wf(&rest)
                    &&& rest.bytes == input.bytes
                    &&& (
                        // arm A: no '@' processed, nothing written
                        (serf == before
                            && (ue as int) == before.len()
                            && input_rem(&rest) == s)
                        // arm B: leading '@', empty userinfo, '@' dropped
                        || (serf == before
                            && (ue as int) == before.len()
                            && s.len() >= 1
                            && s.index(0) == 0x40u8
                            && input_rem(&rest) == s.subrange(1, s.len() as int)
                            && !(1 < s.len()
                                && userinfo_wall_byte(s.index(1), special)))
                        // arm C: userinfo '@' at k with a nonempty span
                        || (exists|k: int, p: int|
                            1 <= k
                            && k < s.len()
                            && s.index(k) == 0x40u8
                            && (forall|j: int| 0 <= j < k
                                ==> !userinfo_wall_byte(s.index(j), special))
                            && (p == k
                                || (0 <= p < k
                                    && s.index(p) == 0x3Au8
                                    && (forall|j: int| 0 <= j < p
                                        ==> s.index(j) != 0x3Au8)))
                            && input_rem(&rest)
                                == s.subrange(k + 1, s.len() as int)
                            && ({
                                let u = if p < k {
                                    s.subrange(0, p)
                                } else {
                                    s.subrange(0, k)
                                };
                                let wp = p < k && k - p > 1;
                                &&& (ue as int)
                                    == before.len()
                                        + enc_seq(u, EncodeSet::Userinfo).len()
                                &&& serf == before
                                    + enc_seq(u, EncodeSet::Userinfo)
                                    + (if wp {
                                        seq![0x3Au8]
                                    } else {
                                        Seq::empty()
                                    })
                                    + (if p < k {
                                        enc_seq(s.subrange(p + 1, k),
                                            EncodeSet::Userinfo)
                                    } else {
                                        Seq::empty()
                                    })
                                    + (if (p >= 1 || p == k) || wp {
                                        seq![0x40u8]
                                    } else {
                                        Seq::empty()
                                    })
                            }))
                    )
                }))
        }),
{
    let sbuf = input.bytes;
    let special = scheme_type.is_special();
    let ghost pos_i = input.pos as int;
    let ghost n_i = sbuf.view().len() as int;
    let ghost rem0 = input_rem(&input);
    let ghost before = self.serialization.view();
    proof {
        assert(before == old(self).serialization.view());
        assert(rem0 == sbuf.view().subrange(input.pos as int,
            sbuf.view().len() as int));
        assert(machine_domain(rem0));
        assert(forall|j: int| 0 <= j < rem0.len()
            ==> machine_domain_byte(rem0.index(j)));
    }
    // the scan loop (parser.rs:867-883): wall + last-@ tracking
    let mut cur = input.pos;
    let mut last_found = false;
    let mut last_pos = input.pos;
    let mut stop = false;
    while cur < sbuf.len() && !stop
        invariant
            before == old(self).serialization.view(),
            input.pos <= cur <= sbuf.len(),
            forall|j: int| pos_i <= j < cur as int
                ==> !userinfo_wall_byte(sbuf.view().index(j), special),
            last_found
                ==> (input.pos <= last_pos && last_pos < cur
                    && sbuf.view().index((last_pos as int)) == 0x40u8
                    && (forall|j: int| (last_pos as int) < j < (cur as int)
                        ==> sbuf.view().index(j) != 0x40u8)),
            !last_found
                ==> (forall|j: int| pos_i <= j < (cur as int)
                    ==> sbuf.view().index(j) != 0x40u8),
            stop ==> (cur < sbuf.len()
                && userinfo_wall_byte(sbuf.view().index((cur as int)), special)),
        decreases (if stop { 0int } else { 1int }), sbuf.len() - cur,
    {
        let c = sbuf[cur];
        proof {
            assert(sbuf.view().index((cur as int)) == c);
        }
        if c == 0x40u8 {
            last_found = true;
            last_pos = cur;
            cur += 1;
        } else if userinfo_wall_byte_exec(c, special) {
            proof {
                assert(userinfo_wall_byte(sbuf.view().index((cur as int)), special));
            }
            stop = true;
        } else {
            cur += 1;
        }
    }
    if !last_found {
        // arm A: no '@' processed (parser.rs:885)
        return Ok((to_u32_ser(&self.serialization), input));
    }
    if last_pos == input.pos {
        // arm B: leading '@' (parser.rs:886-897)
        if input.pos + 1 < sbuf.len() {
            let c1 = sbuf[input.pos + 1];
            if userinfo_wall_byte_exec(c1, special) {
                return Err(ParseError::EmptyHost);
            }
        }
        let rest = Input { bytes: sbuf, pos: input.pos + 1 };
        proof {
            assert(sbuf.view().index((input.pos as int)) == 0x40u8);
            assert(input_rem(&input).index(0) == 0x40u8);
            rem_shift(sbuf, input.pos as int, 1);
            machine_domain_subrange(rem0, 1, rem0.len() as int);
            assert(input_rem(&rest)
                == rem0.subrange(1, rem0.len() as int));
            assert(machine_domain(input_rem(&rest)));
        }
        return Ok((to_u32_ser(&self.serialization), rest));
    }
    // arm C (parser.rs:901-931): locate the first ':' of the span
    let k_abs = last_pos;
    let mut pm = input.pos;
    let mut colon = false;
    while pm < k_abs && !colon
        invariant
            before == old(self).serialization.view(),
            input.pos <= pm <= k_abs,
            k_abs < sbuf.len(),
            sbuf.view().index((k_abs as int)) == 0x40u8,
            forall|i: int| pos_i <= i < k_abs as int
                ==> !userinfo_wall_byte(sbuf.view().index(i), special),
            forall|j: int| pos_i <= j < pm as int
                ==> sbuf.view().index(j) != 0x3Au8,
            colon ==> (pm < k_abs
                && sbuf.view().index((pm as int)) == 0x3Au8),
        decreases (if colon { 0int } else { 1int }), k_abs - pm,
    {
        let c = sbuf[pm];
        proof {
            assert(sbuf.view().index((pm as int)) == c);
        }
        if c == 0x3Au8 {
            proof {
                assert(sbuf.view().index((pm as int)) == 0x3Au8);
            }
            colon = true;
        } else {
            pm += 1;
        }
    }
    proof {
        let pm_rel = (pm - input.pos) as int;
        let k_rel = (k_abs - input.pos) as int;
        assert(rem0 == sbuf.view().subrange(
            input.pos as int, sbuf.view().len() as int));
        vstd::seq::lemma_seq_subrange_composition(sbuf.view(), pos_i, n_i,
            0, pm_rel);
        assert(rem0.subrange(0, pm_rel)
            == sbuf.view().subrange(input.pos as int, pm as int));
        machine_domain_subrange(rem0, 0, pm_rel);
        assert(machine_domain(sbuf.view().subrange(input.pos as int,
            pm as int)));
        if colon {
            vstd::seq::lemma_seq_subrange_composition(sbuf.view(), pos_i, n_i,
                pm_rel + 1, k_rel);
            assert(rem0.subrange(pm_rel + 1, k_rel)
                == sbuf.view().subrange(pm as int + 1, k_abs as int));
            machine_domain_subrange(rem0, pm_rel + 1, k_rel);
            assert(machine_domain(sbuf.view().subrange(pm as int + 1,
                k_abs as int)));
        }
        vstd::seq::lemma_seq_subrange_composition(sbuf.view(), pos_i, n_i,
            0, k_rel);
        assert(rem0.subrange(0, k_rel)
            == sbuf.view().subrange(input.pos as int, k_abs as int));
        machine_domain_subrange(rem0, 0, k_rel);
        assert(machine_domain(sbuf.view().subrange(input.pos as int,
            k_abs as int)));
    }
    let has_password = colon && (pm + 1 < k_abs);
    let has_username = if colon { pm > input.pos } else { k_abs > input.pos };
    let ue_final: u32;
    if colon {
        let ghost slack_ok = before.len() + 3 * ((pm - input.pos) as int)
            <= 0xFFFF_FFFF;
        proof {
            assert(slack_ok) by {
                assert((pm - input.pos) as int
                    <= input_rem(&input).len());
                assert(before.len() + 3 * (input_rem(&input).len() as int) + 3
                    <= 0xFFFF_FFFF);
            };
        }
        extend_percent_encode_at(&mut self.serialization, sbuf, input.pos,
            pm, EncodeSet::Userinfo);
        proof {
            let e = enc_seq(sbuf.view().subrange(input.pos as int, pm as int),
                EncodeSet::Userinfo);
            assert(self.serialization.view() == before + e);
            vstd::seq::lemma_seq_add_len(before, e);
            enc_seq_machine(sbuf.view().subrange(input.pos as int,
                pm as int), EncodeSet::Userinfo);
            machine_domain_add(before, e);
            assert(machine_domain(self.serialization.view()));
            enc_seq_len_bound(sbuf.view().subrange(input.pos as int,
                pm as int), EncodeSet::Userinfo);
            assert(self.serialization.view().len()
                <= before.len() + 3 * ((pm - input.pos) as int));
            assert((self.serialization.view().len() as int) <= 0xFFFF_FFFF);
        }
        ue_final = to_u32_ser(&self.serialization);
        if has_password {
            let ghost before_push = self.serialization.view();
            proof {
                assert(machine_domain_byte(0x3Au8));
            }
            self.serialization.push(0x3Au8);
            proof {
                assert(self.serialization.view() == before_push.push(0x3Au8));
                assert(before_push.push(0x3Au8)
                    == before_push + seq![0x3Au8]);
                machine_domain_add(before_push, seq![0x3Au8]);
            }
            let ghost slack_ok2 = self.serialization.view().len()
                + 3 * ((k_abs - (pm + 1)) as int) <= 0xFFFF_FFFF;
            proof {
                assert(slack_ok2) by {
                    let e = enc_seq(sbuf.view().subrange(input.pos as int,
                        pm as int), EncodeSet::Userinfo);
                    enc_seq_len_bound(sbuf.view().subrange(
                        input.pos as int, pm as int), EncodeSet::Userinfo);
                    assert(self.serialization.view().len()
                        == before.len() + e.len() + 1);
                    assert(e.len() <= 3 * ((pm - input.pos) as int));
                    assert((k_abs - (pm + 1)) as int
                        + (pm - input.pos) as int
                        <= input_rem(&input).len());
                    assert(before.len() + 3 * (input_rem(&input).len() as int) + 3
                        <= 0xFFFF_FFFF);
                };
            }
            extend_percent_encode_at(&mut self.serialization, sbuf, pm + 1,
                k_abs, EncodeSet::Userinfo);
            proof {
                let erange = sbuf.view().subrange(pm as int + 1,
                    k_abs as int);
                let ep = enc_seq(erange, EncodeSet::Userinfo);
                assert(self.serialization.view()
                    == before + enc_seq(sbuf.view().subrange(
                        input.pos as int, pm as int), EncodeSet::Userinfo)
                        + seq![0x3Au8] + ep);
                enc_seq_machine(erange, EncodeSet::Userinfo);
                machine_domain_add(before + enc_seq(sbuf.view().subrange(
                    input.pos as int, pm as int), EncodeSet::Userinfo)
                    + seq![0x3Au8], ep);
                assert(machine_domain(self.serialization.view()));
            }
        }
    } else {
        let ghost slack_ok = before.len() + 3 * ((k_abs - input.pos) as int)
            <= 0xFFFF_FFFF;
        proof {
            assert(slack_ok) by {
                assert((k_abs - input.pos) as int
                    <= input_rem(&input).len());
                assert(before.len() + 3 * (input_rem(&input).len() as int) + 3
                    <= 0xFFFF_FFFF);
            };
        }
        extend_percent_encode_at(&mut self.serialization, sbuf, input.pos,
            k_abs, EncodeSet::Userinfo);
        proof {
            let e = enc_seq(sbuf.view().subrange(input.pos as int,
                k_abs as int), EncodeSet::Userinfo);
            assert(self.serialization.view() == before + e);
            vstd::seq::lemma_seq_add_len(before, e);
            enc_seq_machine(sbuf.view().subrange(input.pos as int,
                k_abs as int), EncodeSet::Userinfo);
            machine_domain_add(before, e);
            assert(machine_domain(self.serialization.view()));
            enc_seq_len_bound(sbuf.view().subrange(input.pos as int,
                k_abs as int), EncodeSet::Userinfo);
            assert(self.serialization.view().len()
                <= before.len() + 3 * ((k_abs - input.pos) as int));
            assert((self.serialization.view().len() as int) <= 0xFFFF_FFFF);
        }
        ue_final = to_u32_ser(&self.serialization);
    }
    let write_any = has_username || has_password;
    proof {
        let krel = (k_abs - input.pos) as int;
        let prel = if colon { (pm - input.pos) as int } else { krel };
        assert(krel >= 1);
        assert(colon ==> (prel >= 0 && prel < krel));
        let remv = input_rem(&input);
        assert(remv == rem0);
        assert(remv.index(krel) == 0x40u8);
        assert(forall|j: int| 0 <= j < krel
            ==> !userinfo_wall_byte(remv.index(j), special));
        if colon {
            assert(remv.index(prel) == 0x3Au8);
            assert(forall|j: int| 0 <= j < prel
                ==> remv.index(j) != 0x3Au8);
            assert(has_username == (prel >= 1));
            assert(has_password == (prel + 1 < krel));
        } else {
            assert(forall|j: int| 0 <= j < krel
                ==> remv.index(j) != 0x3Au8);
            assert(has_username == (krel >= 1));
            assert(krel >= 1);
        }
        assert(write_any == false || write_any == true);
        assert(!colon ==> write_any);
        // the emitted-shape equation against the ensures' rem-coordinates
        if colon {
            assert(remv.subrange(0, prel)
                == sbuf.view().subrange(input.pos as int, pm as int));
            if has_password {
                assert(remv.subrange(prel + 1, krel)
                    == sbuf.view().subrange(pm as int + 1, k_abs as int));
            }
        } else {
            assert(remv.subrange(0, krel)
                == sbuf.view().subrange(input.pos as int, k_abs as int));
        }
    }
    if write_any {
        let ghost before_push = self.serialization.view();
        proof {
            assert(machine_domain_byte(0x40u8));
        }
        self.serialization.push(0x40u8);
        proof {
            assert(self.serialization.view() == before_push.push(0x40u8));
            assert(before_push.push(0x40u8) == before_push + seq![0x40u8]);
            machine_domain_add(before_push, seq![0x40u8]);
        }
    }
    proof {
        let krel = (k_abs - input.pos) as int;
        let prel = if colon { (pm - input.pos) as int } else { krel };
        let remv = input_rem(&input);
        let atsign = if write_any { seq![0x40u8] } else { Seq::empty() };
        if colon {
            let colonseq = if has_password { seq![0x3Au8] } else { Seq::empty() };
            let pw = if has_password {
                enc_seq(remv.subrange(prel + 1, krel), EncodeSet::Userinfo)
            } else {
                Seq::empty()
            };
            let ue_expr = enc_seq(remv.subrange(0, prel),
                EncodeSet::Userinfo);
            assert(self.serialization.view()
                == before + ue_expr + colonseq + pw + atsign);
            assert(ue_final as int == before.len() + ue_expr.len());
            // length accounting for the growth bound
            machine_domain(remv.subrange(0, prel));
            enc_seq_len_bound(remv.subrange(0, prel), EncodeSet::Userinfo);
            if has_password {
                machine_domain(remv.subrange(prel + 1, krel));
                enc_seq_len_bound(remv.subrange(prel + 1, krel),
                    EncodeSet::Userinfo);
            }
            vstd::seq::lemma_seq_add_len(before, ue_expr);
            vstd::seq::lemma_seq_add_len(before + ue_expr, colonseq);
            vstd::seq::lemma_seq_add_len(before + ue_expr + colonseq, pw);
            vstd::seq::lemma_seq_add_len(before + ue_expr + colonseq + pw,
                atsign);
            assert(ue_expr.len() <= 3 * prel);
            assert(has_password ==> pw.len() <= 3 * (krel - prel - 1));
        } else {
            let ue_expr = enc_seq(remv.subrange(0, krel),
                EncodeSet::Userinfo);
            assert(self.serialization.view()
                == before + ue_expr + atsign);
            assert(ue_final as int == before.len() + ue_expr.len());
            assert(atsign == seq![0x40u8]);
            machine_domain(remv.subrange(0, krel));
            enc_seq_len_bound(remv.subrange(0, krel), EncodeSet::Userinfo);
            vstd::seq::lemma_seq_add_len(before, ue_expr);
            vstd::seq::lemma_seq_add_len(before + ue_expr, atsign);
        }
        assert(self.serialization.view().len()
            <= before.len() + 3 * ((k_abs - input.pos) as int) + 1);
    }
    let rest = Input { bytes: sbuf, pos: k_abs + 1 };
    proof {
        rem_shift(sbuf, input.pos as int, (k_abs + 1 - input.pos) as int);
        machine_domain_subrange(input_rem(&input),
            (k_abs + 1 - input.pos) as int, input_rem(&input).len() as int);
        assert(input_rem(&rest)
            == input_rem(&input).subrange((k_abs + 1 - input.pos) as int,
                input_rem(&input).len() as int));
        assert(machine_domain(input_rem(&rest)));
        assert((input_rem(&rest).len() as int) <= 0xFFFF_FFFF);
        assert(input_ok(&rest));
        assert(input_wf(&rest));
    }
    Ok((ue_final, rest))
}

}

/* ============================================================
 * Host face on the declared external premise (Origin:
 * parser.rs:971-1024 + host.rs:92-175; the idna punycode,
 * percent-decode, and ipv4/ipv6 chains are the deep-host batch)
 * ============================================================ */

/// The restricted input class of the batch's host face: lowercase ASCII
/// alphanumerics, '-', '.' (host_simple_byte only restricts shape).
pub open spec fn host_simple_byte(b: u8) -> bool {
    (b >= 0x61u8 && b <= 0x7Au8) || (b >= 0x30u8 && b <= 0x39u8)
        || b == 0x2Du8 || b == 0x2Eu8
}

/// The class of a host run: empty (the EmptyHost / opaque-empty drops are
/// the caller's real code below), or simple bytes with lowercase letters
/// at both endpoints and starting every dot-separated label (the letter
/// starts rule out the all-digit and the 0x-number forms of
/// ends_in_a_number, host.rs:280-299, and exclude the '[' of the ipv6
/// bracket form; the class letters are what the idna deeper batch pins as
/// the identity inputs of the UTS46 mapping).
pub open spec fn host_run_class(s: Seq<u8>) -> bool {
    s.len() == 0
        || (forall|i: int| 0 <= i < s.len()
            ==> host_simple_byte(s.index(i))
                && (0x61u8 <= s.index(0) <= 0x7Au8))
            && (0x61u8 <= s.index(s.len() - 1) <= 0x7Au8)
            && (forall|j: int| 0 <= j < s.len() - 1
                    && s.index(j) == 0x2Eu8
                ==> 0x61u8 <= s.index(j + 1) <= 0x7Au8)
}

/// The host-terminator face of parse_host (parser.rs:987-989): ':' (the
/// class excludes '[', so the bracket tracking of upstream never flips),
/// '\\' on special schemes, and the path/query/fragment delimiters.
/// Recursive form of "the leading k bytes are all '/' or '\\'" (the
/// scanner-run face of parse_with_scheme's authority entry): recursive
/// so its axiom set is fuel-bounded and does not leak quantifier
/// patterns into unrelated loop queries.
pub open spec fn slash_run_prefix(s: Seq<u8>, k: int) -> bool
    decreases k,
{
    if k <= 0 {
        true
    } else {
        slash_run_prefix(s, k - 1)
            && (s.index(k - 1) == 0x2Fu8
                || s.index(k - 1) == 0x5Cu8)
    }
}

pub open spec fn host_term_byte(b: u8, special: bool) -> bool {
    b == 0x3Au8 || b == 0x2Fu8 || b == 0x3Fu8 || b == 0x23u8
        || (special && b == 0x5Cu8)
}

/// Exec twin of host_term_byte.
pub exec fn host_term_byte_exec(b: u8, special: bool) -> (r: bool)
    ensures
        r == host_term_byte(b, special),
{
    b == 0x3Au8 || b == 0x2Fu8 || b == 0x3Fu8 || b == 0x23u8
        || (special && b == 0x5Cu8)
}

/// The materialized form of the host split: h is the run length, the run
/// is in the class and contains no terminator byte (that is the wall-free
/// span of the scan).
pub open spec fn host_split_form(s: Seq<u8>, h: int, special: bool) -> bool {
    &&& 0 <= h
    &&& h <= s.len()
    &&& host_run_class(s.subrange(0, h))
    &&& (forall|j: int| 0 <= j < h
        ==> !host_term_byte(s.index(j), special))
    &&& (h < s.len()
        ==> host_term_byte(s.index(h), special))
}

/// The split class of a whole remaining input at the host site: the bytes
/// before the first host terminator form a host-class run.
pub open spec fn host_split_class(s: Seq<u8>, special: bool) -> bool {
    exists|h: int| host_split_form(s, h, special)
}

/// The restricted entry class of the authority state (after the "//"
/// push, at the call of parse_userinfo, parser.rs:835): every peel the
/// userinfo scan can select -- the no-"@" face (nothing written, host
/// input unchanged), the leading-"@" drop (host input the suffix after
/// one byte), or an "@"-delimited span at some offset -- leaves a
/// remaining input in the host split class. The disjunct closure is
/// what transports parse_host_and_port's class premise (parser.rs:840)
/// through the peel; the caller can not derive it from the entry bytes
/// alone because the peel is what selects the host input.
pub open spec fn authority_entry_class(s: Seq<u8>, special: bool) -> bool {
    &&& host_split_class(s, special)
    &&& (s.len() == 0
            || s.index(0) != 0x40u8
            || host_split_class(s.subrange(1, s.len() as int), special))
    &&& (forall|k: int| 1 <= k && k < s.len()
                && s.index(k) == 0x40u8
            ==> host_split_class(s.subrange(k + 1, s.len() as int),
                special))
}

/// The wall-free span shape of a host run of length h (the piece of the
/// split the callers' assembly obligations need; the class pins are kept on
/// the requires side).
pub open spec fn host_split_walls(s: Seq<u8>, h: int, special: bool) -> bool {
    0 <= h
        && h <= s.len()
        && (forall|j: int| 0 <= j < h
            ==> !host_term_byte(s.index(j), special))
}

/// The wall bytes of the file-host scan (parser.rs:1071):
/// '/' | '\\' | '?' | '#'.  Unlike the authority host face
/// (host_term_byte) the ':' is NOT a wall there: a file-host
/// candidate may carry one (the windows drive letters and the
/// ipv6 bracket forms ride the candidate region).
pub open spec fn file_wall_byte(b: u8) -> bool {
    b == 0x2Fu8 || b == 0x5Cu8 || b == 0x3Fu8 || b == 0x23u8
}

/// Recursive form of "the leading k bytes hold no file wall byte"
/// (the scan-run face of the file-host split).  Recursive so its
/// axiom set is fuel-bounded and does not leak quantifier patterns
/// into unrelated loop queries (the slash_run_prefix recipe).
pub open spec fn file_wall_free(s: Seq<u8>, k: int) -> bool
    decreases k,
{
    if k <= 0 {
        true
    } else {
        file_wall_free(s, k - 1) && !file_wall_byte(s.index(k - 1))
    }
}

/// The pointwise twin of file_wall_free.
pub proof fn file_wall_free_iff(s: Seq<u8>, k: int)
    requires
        0 <= k,
        k <= (s.len() as int),
    ensures
        file_wall_free(s, k)
            == (forall|j: int| 0 <= j && j < k
                ==> !file_wall_byte(s.index(j))),
    decreases k,
{
    if k <= 0 {
        reveal_with_fuel(file_wall_free, 2);
        assert(file_wall_free(s, k));
    } else {
        file_wall_free_iff(s, k - 1);
        reveal_with_fuel(file_wall_free, 2);
        assert(file_wall_free(s, k)
            == (file_wall_free(s, k - 1)
                && !file_wall_byte(s.index(k - 1))));
    }
}

/// The restricted entry class of the file-host state (the scan of
/// parse_file_host, parser.rs:1069-1078): every wall split the scan
/// can pick leaves a candidate prefix inside the declared deep-host
/// premise's input class (host_run_class, the empty candidate
/// included).  The windows-drive candidates never reach the deep
/// face -- file_host short-circuits them (parser.rs:1088-1090) --
/// so the class only ranges the splits the scan names.  The caller
/// can not derive the class from the entry bytes alone because the
/// scan is what selects the split; the trigger carrier seats the
/// split's slice term.
pub open spec fn file_host_entry_class(s: Seq<u8>) -> bool {
    forall|k: int| #![trigger file_wall_free(s, k)]
        (0 <= k
            && k <= (s.len() as int)
            && file_wall_free(s, k)
            && (k == (s.len() as int)
                || file_wall_byte(s.index(k))))
        ==> host_run_class(s.subrange(0, k))
}

/// The file-state faces over the dispatcher's input (the two File-arm
/// conjuncts of the entries, packaged so the per-instantiation bodies
/// of the entry faces stay small).
pub open spec fn file_state_entry_face(rem: Seq<u8>) -> bool {
    &&& (((rem.len() as int) >= 1
            && (rem.index(0) == 0x2Fu8
                || rem.index(0) == 0x5Cu8))
        ==> rem.index(0) == 0x2Fu8)
    &&& (((rem.len() as int) >= 2
            && rem.index(0) == 0x2Fu8
            && (rem.index(1) == 0x2Fu8
                || rem.index(1) == 0x5Cu8))
        ==> file_host_entry_class(
            rem.subrange(2, rem.len() as int)))
}

/// The hex-digit face of core char::to_digit(16)
/// (the after_percent_sign gate of percent_encoding/src/lib.rs:211-218).
pub open spec fn is_ascii_hexdigit_b(b: u8) -> bool {
    (0x30u8 <= b && b <= 0x39u8)
        || (0x41u8 <= b && b <= 0x46u8)
        || (0x61u8 <= b && b <= 0x66u8)
}

/// The digit value of a hex-digit byte (to_digit(16) of
/// percent_encoding/src/lib.rs:212-214: '0'..'9' are 0..9, 'A'..'F'
/// are 10..15, 'a'..'f' are 10..15).
pub open spec fn pd_hex_val(b: u8) -> u8 {
    if 0x30u8 <= b && b <= 0x39u8 {
        ((b - 0x30u8) as u8)
    } else if 0x41u8 <= b && b <= 0x46u8 {
        ((b - 0x41u8 + 10) as u8)
    } else {
        ((b - 0x61u8 + 10) as u8)
    }
}

/// Exec twin of pd_hex_val.
pub exec fn pd_hex_val_exec(b: u8) -> (r: u8)
    requires
        is_ascii_hexdigit_b(b),
    ensures
        r == pd_hex_val(b),
{
    if 0x30u8 <= b && b <= 0x39u8 {
        b - 0x30u8
    } else if 0x41u8 <= b && b <= 0x46u8 {
        b - 0x41u8 + 10
    } else {
        b - 0x61u8 + 10
    }
}

/// Exec twin of is_ascii_hexdigit_b.
pub exec fn is_ascii_hexdigit_exec(b: u8) -> (r: bool)
    ensures
        r == is_ascii_hexdigit_b(b),
{
    (0x30u8 <= b && b <= 0x39u8)
        || (0x41u8 <= b && b <= 0x46u8)
        || (0x61u8 <= b && b <= 0x66u8)
}

/// The digit value of a hex-digit byte stays a nibble (the u8 face of
/// the h * 0x10 + l decode without overflow).
pub proof fn pd_hex_val_bound(b: u8)
    requires
        is_ascii_hexdigit_b(b),
    ensures
        pd_hex_val(b) <= 0x0Fu8,
{
}

/// Origin Rust (percent_encoding/src/lib.rs:206-275):
///   impl Iterator for PercentDecode { fn next(&mut self) -> Option<u8> {
///     self.bytes.next().map(|&byte| {
///       if byte == b'%' {
///         after_percent_sign(&mut self.bytes).unwrap_or(byte)
///       } else { byte } }) } }
///   fn after_percent_sign(iter) -> Option<u8> {
///     let mut cloned_iter = iter.clone();
///     let h = char::from(*cloned_iter.next()?).to_digit(16)?;
///     let l = char::from(*cloned_iter.next()?).to_digit(16)?;
///     *iter = cloned_iter;
///     Some(h as u8 * 0x10 + l as u8) }
/// spec view: the recursive per-position decode of the run -- a '%' that
/// has two hex-digit bytes after it decodes to the byte value (the
/// cloned-iterate commit of after_percent_sign fires only on the
/// two-hex-digit face), every other position passes its byte through.
pub closed spec fn percent_decode_at(s: Seq<u8>, i: int) -> Seq<u8>
    decreases (s.len() as int) - i,
{
    if !(0 <= i && i <= (s.len() as int)) {
        // the out-of-domain guard (spec fns carry no requires; the
        // callers always sit inside [0, len])
        Seq::empty()
    } else if i == (s.len() as int) {
        Seq::empty()
    } else if s.index(i) == 0x25u8
        && i + 3 <= (s.len() as int)
        && is_ascii_hexdigit_b(s.index(i + 1))
        && is_ascii_hexdigit_b(s.index(i + 2))
    {
        seq![((pd_hex_val(s.index(i + 1)) * 0x10u8
            + pd_hex_val(s.index(i + 2))) as u8)]
            + percent_decode_at(s, i + 3)
    } else {
        seq![s.index(i)] + percent_decode_at(s, i + 1)
    }
}

/// The whole-run percent-decode (the collect face of PercentDecode).
pub open spec fn percent_decode_seq(s: Seq<u8>) -> Seq<u8> {
    percent_decode_at(s, 0)
}

/// The identity stride of the decode over a '%' free run.
pub proof fn pd_no_percent_at(s: Seq<u8>, i: int)
    requires
        0 <= i <= (s.len() as int),
        forall|j: int| 0 <= j < (s.len() as int)
            ==> s.index(j) != 0x25u8,
    ensures
        percent_decode_at(s, i) == s.subrange(i, (s.len() as int)),
    decreases (s.len() as int) - i,
{
    if i == (s.len() as int) {
        reveal_with_fuel(percent_decode_at, 2);
        assert(s.subrange(i, (s.len() as int)) == Seq::empty());
    } else {
        assert(s.index(i) != 0x25u8);
        reveal_with_fuel(percent_decode_at, 2);
        pd_no_percent_at(s, i + 1);
        let rest = s.subrange(i + 1, (s.len() as int));
        assert(seq![s.index(i)] + rest
            == s.subrange(i, (s.len() as int))) by {
            let n = (s.len() as int);
            vstd::seq::lemma_seq_add_len(seq![s.index(i)], rest);
            assert((seq![s.index(i)] + rest).len() == 1 + (n - i - 1));
            assert forall|j: int| 0 <= j < n - i
                implies (seq![s.index(i)] + rest).index(j)
                    == s.subrange(i, n).index(j) by {
                if j == 0 {
                    vstd::seq::lemma_seq_add_index1(seq![s.index(i)],
                        rest, 0);
                    vstd::seq::lemma_seq_subrange_index(s, i, n, 0);
                } else {
                    vstd::seq::lemma_seq_add_index2(seq![s.index(i)],
                        rest, j);
                    vstd::seq::lemma_seq_subrange_index(s, i + 1, n,
                        j - 1);
                    vstd::seq::lemma_seq_subrange_index(s, i, n, j);
                }
            }
            vstd::seq::lemma_seq_ext_equal(seq![s.index(i)] + rest,
                s.subrange(i, n));
        };
    }
}

/// The '%' free run's decode is the identity.
pub proof fn percent_decode_identity_no_percent(s: Seq<u8>)
    requires
        forall|j: int| 0 <= j < (s.len() as int)
            ==> s.index(j) != 0x25u8,
    ensures
        percent_decode_seq(s) == s,
{
    assert(s == s.subrange(0, (s.len() as int)));
    pd_no_percent_at(s, 0);
}

/// Origin Rust (percent_encoding/src/lib.rs:240 + 263-275): the
/// collect::<Vec<u8>> of percent_decode over the whole byte slice, the
/// iterated next()/after_percent_sign face of the spec recursion above.
pub exec fn percent_decode_bytes(input: &[u8]) -> (r: Vec<u8>)
    ensures
        r.view() == percent_decode_seq(input.view()),
{
    let ghost sv = input.view();
    let n = input.len();
    let mut p: usize = 0;
    let mut out: Vec<u8> = Vec::new();
    proof {
        seq_add_empty_left(percent_decode_at(sv, 0));
        assert(out.view() == Seq::empty());
        assert(out.view() + percent_decode_at(sv, 0)
            == percent_decode_at(sv, 0));
    }
    while p < n
        invariant
            0 <= p <= n,
            n == input.len(),
            sv == input.view(),
            (n as int) == (sv.len() as int),
            out.view() + percent_decode_at(sv, p as int)
                == percent_decode_at(sv, 0),
        decreases n - p,
    {
        let byte = input[p];
        let ghost pre_out = out.view();
        proof {
            assert(sv.index(p as int) == byte);
        }
        if byte == 0x25u8 && n - p >= 3 {
            let h = input[p + 1];
            let l = input[p + 2];
            proof {
                assert(sv.index((p + 1) as int) == h);
                assert(sv.index((p + 2) as int) == l);
            }
            if is_ascii_hexdigit_exec(h) && is_ascii_hexdigit_exec(l) {
                // after_percent_sign commits both hex digits
                // (percent_encoding/src/lib.rs:218)
                let hi = pd_hex_val_exec(h);
                let lo = pd_hex_val_exec(l);
                out.push(hi * 0x10u8 + lo);
                proof {
                    pd_hex_val_bound(h);
                    pd_hex_val_bound(l);
                    reveal_with_fuel(percent_decode_at, 2);
                    assert(pd_hex_val(h) == hi);
                    assert(pd_hex_val(l) == lo);
                    assert(hi <= 0x0Fu8);
                    assert(lo <= 0x0Fu8);
                    let pushbyte = ((pd_hex_val(h) * 0x10u8
                        + pd_hex_val(l)) as u8);
                    assert(pushbyte == hi * 0x10u8 + lo);
                    assert(percent_decode_at(sv, p as int)
                        == seq![pushbyte]
                            + percent_decode_at(sv, (p + 3) as int));
                    assert(out.view() == pre_out + seq![pushbyte]);
                    seq_add_assoc3(pre_out, seq![pushbyte],
                        percent_decode_at(sv, (p + 3) as int));
                }
                p += 3;
            } else {
                // the two-hex-digit gate fails: the '%' passes through
                // (after_percent_sign's None arm unwraps to the byte)
                out.push(byte);
                proof {
                    reveal_with_fuel(percent_decode_at, 2);
                    assert(!(is_ascii_hexdigit_b(h)
                        && is_ascii_hexdigit_b(l)));
                    assert(percent_decode_at(sv, p as int)
                        == seq![byte]
                            + percent_decode_at(sv, (p + 1) as int));
                    assert(out.view() == pre_out + seq![byte]);
                    seq_add_assoc3(pre_out, seq![byte],
                        percent_decode_at(sv, (p + 1) as int));
                }
                p += 1;
            }
        } else {
            out.push(byte);
            proof {
                reveal_with_fuel(percent_decode_at, 2);
                if byte != 0x25u8 {
                    assert(percent_decode_at(sv, p as int)
                        == seq![byte]
                            + percent_decode_at(sv, (p + 1) as int));
                } else {
                    assert(n - p < 3);
                    assert((p as int) + 3 > (n as int));
                    assert(!((p as int) + 3 <= (sv.len() as int)));
                    assert(percent_decode_at(sv, p as int)
                        == seq![byte]
                            + percent_decode_at(sv, (p + 1) as int));
                }
                assert(out.view() == pre_out + seq![byte]);
                seq_add_assoc3(pre_out, seq![byte],
                    percent_decode_at(sv, (p + 1) as int));
            }
            p += 1;
        }
    }
    proof {
        reveal_with_fuel(percent_decode_at, 2);
        assert(percent_decode_at(sv, n as int) == Seq::empty());
        let fin = out.view();
        let all = percent_decode_at(sv, 0);
        assert(fin + Seq::empty() == all);
        assert forall|j: int|
            0 <= j && j < fin.len()
            implies fin.index(j) == all.index(j) by {
            vstd::seq::lemma_seq_add_index1(fin, Seq::empty(), j);
            assert((fin + Seq::empty()).index(j) == fin.index(j));
        }
        vstd::seq::lemma_seq_add_len(fin, Seq::empty());
        assert(fin.len() == all.len());
        vstd::seq::lemma_seq_ext_equal(fin, all);
    }
    out
}

/// Origin Rust (host.rs:131-151): the is_invalid_host_char closure of
/// parse_opaque_cow (host.rs:153-155 rejects the run outright when any
/// of these bytes appears).
pub open spec fn is_invalid_host_byte(b: u8) -> bool {
    b == 0x00u8 || b == 0x09u8 || b == 0x0Au8 || b == 0x0Du8
        || b == 0x20u8 || b == 0x23u8 || b == 0x2Fu8 || b == 0x3Au8
        || b == 0x3Cu8 || b == 0x3Eu8 || b == 0x3Fu8 || b == 0x40u8
        || b == 0x5Bu8 || b == 0x5Cu8 || b == 0x5Du8 || b == 0x5Eu8
        || b == 0x7Cu8
}

/// Exec twin of is_invalid_host_byte.
pub exec fn invalid_host_byte_exec(b: u8) -> (r: bool)
    ensures
        r == is_invalid_host_byte(b),
{
    reveal(is_invalid_host_byte);
    b == 0x00u8 || b == 0x09u8 || b == 0x0Au8 || b == 0x0Du8
        || b == 0x20u8 || b == 0x23u8 || b == 0x2Fu8 || b == 0x3Au8
        || b == 0x3Cu8 || b == 0x3Eu8 || b == 0x3Fu8 || b == 0x40u8
        || b == 0x5Bu8 || b == 0x5Cu8 || b == 0x5Du8 || b == 0x5Eu8
        || b == 0x7Cu8
}

/// Origin Rust (host.rs:153-155): input.find(is_invalid_host_char) over
/// the run bytes -- the opaque-route gate of parse_opaque_cow over the
/// whole candidate.
pub exec fn invalid_host_char_scan(run: &Vec<u8>) -> (r: bool)
    ensures
        r == (exists|j: int|
            0 <= j < (run.view().len() as int)
                && is_invalid_host_byte(run.view().index(j))),
{
    let ghost rv = run.view();
    let n = run.len();
    let mut i: usize = 0;
    let mut found = false;
    while i < n && !found
        invariant
            0 <= i <= n,
            n == run.len(),
            rv == run.view(),
            (n as int) == (rv.len() as int),
            found == (exists|j: int|
                0 <= j < (i as int)
                    && is_invalid_host_byte(rv.index(j))),
        decreases n - i,
    {
        let b = run[i];
        proof {
            assert(rv.index(i as int) == b);
        }
        if invalid_host_byte_exec(b) {
            found = true;
        }
        i += 1;
    }
    found
}

/// The byte-level identity faces of the host class (host_simple_byte):
/// no '%' escape byte (the percent_decode identity), no invalid
/// opaque-host byte (the host.rs:131-151 scan stays clean), and no
/// CONTROLS byte (the utf8_percent_encode(input, CONTROLS) of
/// parse_opaque_cow, host.rs:162-174, never rewrites the run).
pub proof fn host_simple_byte_identity_facts(b: u8)
    requires
        host_simple_byte(b),
    ensures
        b != 0x25u8,
        !is_invalid_host_byte(b),
        !in_controls(b),
{
    // the class bytes (0x2D, 0x2E, 0x30..=0x39, 0x61..=0x7A) all sit
    // strictly inside the LDH band; every byte discharged above lies
    // below 0x2D, in the 0x3A..=0x60 punctuation band, or above 0x7A
}

/// enc_byte of a byte outside the set is the byte itself (the
/// Cow::Borrowed identity face of utf8_percent_encode).
pub proof fn enc_byte_notin_identity(b: u8, set: EncodeSet)
    requires
        !in_set(set, b),
    ensures
        enc_byte(b, set) == seq![b],
{
}

/// The encode of a run whose bytes are all outside the set is the run
/// itself (the parse_opaque_cow CONTROLS face over the class).
pub proof fn enc_seq_notin_identity(s: Seq<u8>, set: EncodeSet)
    requires
        forall|j: int| 0 <= j < (s.len() as int)
            ==> !in_set(set, s.index(j)),
    ensures
        enc_seq(s, set) == s,
    decreases s.len(),
{
    if (s.len() as int) == 0 {
    } else {
        reveal_with_fuel(enc_seq, 2);
        enc_byte_notin_identity(s.index(0), set);
        enc_seq_notin_identity(s.subrange(1, (s.len() as int)), set);
        let rest = s.subrange(1, (s.len() as int));
        assert(seq![s.index(0)] + rest == s) by {
            let n = (s.len() as int);
            vstd::seq::lemma_seq_add_len(seq![s.index(0)], rest);
            assert((seq![s.index(0)] + rest).len() == n);
            assert forall|j: int| 0 <= j < n
                implies (seq![s.index(0)] + rest).index(j)
                    == s.subrange(0, n).index(j) by {
                if j == 0 {
                    vstd::seq::lemma_seq_add_index1(
                        seq![s.index(0)], rest, 0);
                    vstd::seq::lemma_seq_subrange_index(s, 0, n, 0);
                } else {
                    vstd::seq::lemma_seq_add_index2(seq![s.index(0)],
                        rest, j);
                    vstd::seq::lemma_seq_subrange_index(s, 1, n,
                        j - 1);
                    vstd::seq::lemma_seq_subrange_index(s, 0, n, j);
                }
            }
            vstd::seq::lemma_seq_ext_equal(seq![s.index(0)] + rest,
                s.subrange(0, n));
        };
        assert(s == s.subrange(0, (s.len() as int)));
    }
}

/// Origin Rust (idna/src/uts46.rs:182-183 + 133-136): the in_inclusive
/// range8 faces of is_passthrough_ascii_label's interior scan
/// (b'a'..=b'z' / b'0'..=b'9' / b'-'; the '.' split already removed the
/// dot bytes from the label interior).
pub open spec fn uts46_ldh_byte(b: u8) -> bool {
    (0x61u8 <= b && b <= 0x7Au8)
        || (0x30u8 <= b && b <= 0x39u8)
        || b == 0x2Du8
}

/// Exec twin of uts46_ldh_byte.
pub exec fn uts46_ldh_byte_exec(b: u8) -> (r: bool)
    ensures
        r == uts46_ldh_byte(b),
{
    (0x61u8 <= b && b <= 0x7Au8)
        || (0x30u8 <= b && b <= 0x39u8)
        || b == 0x2Du8
}

/// Origin Rust (idna/src/uts46.rs:143-183): is_passthrough_ascii_label
/// -- a label the uts46 ASCII prefix tier passes through untouched:
/// the empty label passes (uts46.rs:181-183); a label with '-' at both
/// positions 2 and 3 fails (uts46.rs:147-149: the xn---shape
/// over-approximation that detours punycode-shaped labels to the
/// deeper path); otherwise the letter head test (uts46.rs:159), the
/// LDH interior scan (uts46.rs:161-174), and the not-hyphen tail test
/// (uts46.rs:175) all hold before the label passes.
pub open spec fn uts46_passthrough_label(l: Seq<u8>) -> bool {
    (l.len() == 0)
        || (!((l.len() as int) >= 4
                && l.index(2) == 0x2Du8
                && l.index(3) == 0x2Du8)
            && (0x61u8 <= l.index(0) && l.index(0) <= 0x7Au8)
            && (forall|j: int|
                1 <= j < (l.len() as int)
                    ==> uts46_ldh_byte(l.index(j)))
            && l.index(l.len() - 1) != 0x2Du8)
}

/// Origin Rust (idna/src/uts46.rs:1090): the '.'-label boundary --
/// ascending form of the split(|b| *b == b'.') iterator over the tail
/// (the least k >= i with s[k] == '.', else the end).
pub closed spec fn dot_from(s: Seq<u8>, i: int) -> int
    decreases (s.len() as int) - i,
{
    if !(0 <= i && i <= (s.len() as int)) {
        // the out-of-domain guard (the callers sit inside [0, len])
        i
    } else if i == (s.len() as int) || s.index(i) == 0x2Eu8 {
        i
    } else {
        dot_from(s, i + 1)
    }
}

/// The dot-scan stride: a non-dot, non-end position agrees with its
/// successor (the iterated step of the split walk).
pub proof fn dot_from_step(s: Seq<u8>, i: int)
    requires
        0 <= i < (s.len() as int),
        s.index(i) != 0x2Eu8,
    ensures
        dot_from(s, i) == dot_from(s, i + 1),
{
    reveal_with_fuel(dot_from, 2);
}

/// A scouted dot boundary: the least-dot/end witness verified against
/// the recursive scan (the exec walk gathers the same boundary the
/// split iterator would).
pub proof fn dot_from_scouted(s: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j <= (s.len() as int),
        (forall|m: int| i <= m < j ==> s.index(m) != 0x2Eu8),
        (j == (s.len() as int) || s.index(j) == 0x2Eu8),
    ensures
        dot_from(s, i) == j,
    decreases (s.len() as int) - i,
{
    if i == j {
        reveal_with_fuel(dot_from, 2);
    } else {
        assert(s.index(i) != 0x2Eu8);
        reveal_with_fuel(dot_from, 2);
        assert(dot_from(s, i) == dot_from(s, i + 1));
        dot_from_scouted(s, i + 1, j);
    }
}

/// Seq concat associativity over the byte payload (the invariant-chain
/// stride of the decode loop below).
pub proof fn seq_add_assoc3(x: Seq<u8>, y: Seq<u8>, z: Seq<u8>)
    ensures
        (x + y) + z == x + (y + z),
{
    vstd::seq::lemma_seq_add_len(x + y, z);
    vstd::seq::lemma_seq_add_len(y, z);
    vstd::seq::lemma_seq_add_len(x, y + z);
    assert(((x + y) + z).len() == (x.len() + y.len() + z.len()));
    assert((x + (y + z)).len() == (x.len() + y.len() + z.len()));
    assert forall|j: int|
        0 <= j && j < (x.len() + y.len() + z.len())
        implies ((x + y) + z).index(j)
            == (x + (y + z)).index(j) by {
        let nxy = (x.len() + y.len()) as int;
        if j < x.len() {
            vstd::seq::lemma_seq_add_index1(x, y, j);
            vstd::seq::lemma_seq_add_index1(x, y + z, j);
        } else if j < nxy {
            vstd::seq::lemma_seq_add_index2(x, y, j);
            vstd::seq::lemma_seq_add_index2(x, y + z, j);
            vstd::seq::lemma_seq_add_index1(y, z, j - x.len());
        } else {
            vstd::seq::lemma_seq_add_index2(x + y, z, j);
            vstd::seq::lemma_seq_add_index2(x, y + z, j);
            vstd::seq::lemma_seq_add_index2(y, z, j - x.len());
        }
    }
    vstd::seq::lemma_seq_ext_equal((x + y) + z, x + (y + z));
}

/// The empty prefix stride of the decode loop's invariant (a fresh
/// buffer contributes nothing).
pub proof fn seq_add_empty_left(x: Seq<u8>)
    ensures
        Seq::empty() + x == x,
{
    vstd::seq::lemma_seq_add_len(Seq::empty(), x);
    assert((Seq::empty() + x).len() == x.len());
    assert forall|j: int|
        0 <= j && j < x.len()
        implies (Seq::empty() + x).index(j) == x.index(j) by {
        vstd::seq::lemma_seq_add_index2(Seq::empty(), x, j);
    }
    vstd::seq::lemma_seq_ext_equal(Seq::empty() + x, x);
}

/// Origin Rust (idna/src/uts46.rs:1094-1104 + 542-576): the label-tier
/// walk of the uts46 ASCII prefix path -- every dot-split label of s
/// passes is_passthrough_ascii_label. Over such a run the
/// to_ascii_from_cow Passthrough arm returns the domain_name bytes
/// unchanged (uts46.rs:558-567: the whole-passthrough accounting keeps
/// the sink untouched, the SAFETY comment asserts the ASCII domain
/// passes through as the original). The k-corner guard keeps the spec
/// total without a separate lower-bound lemma (dot_from's own scouted
/// values always satisfy i < k <= len over the live arms).
pub closed spec fn uts46_identity_tier(s: Seq<u8>, i: int) -> bool
    decreases (s.len() as int) - i,
{
    if !(0 <= i && i <= (s.len() as int)) {
        // the out-of-domain guard (the callers sit inside [0, len])
        true
    } else if i == (s.len() as int) {
        true
    } else {
        let k = dot_from(s, i);
        uts46_passthrough_label(s.subrange(i, k))
            && (if k == (s.len() as int) {
                true
            } else if !(i <= k && k + 1 <= (s.len() as int)) {
                // the unreachable corner of dot_from's scouted boundary
                true
            } else {
                uts46_identity_tier(s, k + 1)
            })
    }
}

/// The per-label passthrough question over one label span [i, j) of the
/// run bytes (the label-argument form of
/// is_passthrough_ascii_label). The false returns report the same
/// first-failing conjunct the uts46 label test reports.
pub exec fn uts46_label_pass_check(run: &Vec<u8>, i: usize, j: usize)
    -> (r: bool)
    requires
        i <= j,
        j <= run.view().len(),
    ensures
        r == uts46_passthrough_label(
            run.view().subrange(i as int, j as int)),
{
    let ghost rv = run.view();
    let ghost l = rv.subrange(i as int, j as int);
    proof {
        reveal(uts46_passthrough_label);
        vstd::seq::lemma_seq_subrange_len(rv, i as int, j as int);
        assert((l.len() as int) == ((j - i) as int));
        // the one-shot l/rv bridge over the label span (the per-element
        // subrange-index idiom; the loop invariants below stay in rv
        // coordinates and every exit dissects the definition through it)
        assert forall|m: int|
            #![trigger l.index(m)]
            0 <= m && m < (l.len() as int)
            implies l.index(m) == rv.index((i as int) + m)
        by {
            vstd::seq::lemma_seq_subrange_index(rv, i as int,
                j as int, m);
        }
    }
    if j == i {
        proof {
            assert(l.len() == 0);
        }
        return true;
    }
    // the xn---shape over-approximation (uts46.rs:147-149): the label
    // bytes exist at 2 and 3 only when the span is four or longer
    let mut tabular = false;
    if j - i >= 4 {
        let b2 = run[i + 2];
        let b3 = run[i + 3];
        proof {
            assert(rv.index((i + 2) as int) == b2);
            assert(rv.index((i + 3) as int) == b3);
        }
        tabular = b2 == 0x2Du8 && b3 == 0x2Du8;
        proof {
            assert(l.index(2) == rv.index((i as int) + 2));
            assert(l.index(3) == rv.index((i as int) + 3));
            assert(tabular == ((l.len() as int) >= 4
                && l.index(2) == 0x2Du8
                && l.index(3) == 0x2Du8));
        }
    } else {
        proof {
            assert((l.len() as int) < 4);
        }
    }
    if tabular {
        proof {
            assert((l.len() as int) >= 4);
            assert(l.index(2) == 0x2Du8);
            assert(l.index(3) == 0x2Du8);
            assert(l == run.view().subrange(i as int, j as int));
            assert(uts46_passthrough_label(l) == false);
        }
        return false;
    }
    // the letter head (uts46.rs:159)
    let hb = run[i];
    proof {
        assert(rv.index(i as int) == hb);
        assert(l.index(0) == rv.index(i as int));
        assert(l.len() != 0);
    }
    if !(0x61u8 <= hb && hb <= 0x7Au8) {
        proof {
            assert((l.len() as int) != 0);
            assert(l.index(0) == rv.index(i as int));
            assert(!(0x61u8 <= l.index(0) && l.index(0) <= 0x7Au8));
            assert(l == run.view().subrange(i as int, j as int));
            assert(uts46_passthrough_label(l) == false);
        }
        return false;
    }
    // the LDH interior (uts46.rs:161-174)
    let mut k: usize = i + 1;
    while k < j
        invariant
            i + 1 <= k <= j,
            j <= run.len(),
            rv == run.view(),
            (run.len() as int) == (rv.len() as int),
            l == rv.subrange(i as int, j as int),
            (l.len() as int) == ((j - i) as int),
            !((l.len() as int) >= 4
                && l.index(2) == 0x2Du8
                && l.index(3) == 0x2Du8),
            (0x61u8 <= l.index(0) && l.index(0) <= 0x7Au8),
            forall|m: int|
                #![trigger l.index(m)]
                0 <= m && m < (l.len() as int)
                ==> l.index(m) == rv.index((i as int) + m),
            forall|m: int|
                (i as int) + 1 <= m && m < (k as int)
                    ==> uts46_ldh_byte(rv.index(m)),
        decreases j - k,
    {
        let b = run[k];
        proof {
            assert(rv.index(k as int) == b);
        }
        if uts46_ldh_byte_exec(b) {
            k += 1;
        } else {
            proof {
                assert(!uts46_ldh_byte(rv.index(k as int)));
                let m0 = (k as int) - (i as int);
                assert(1 <= m0);
                assert(m0 < (l.len() as int));
                assert(l.index(m0) == rv.index((i as int) + m0));
                assert(!uts46_ldh_byte(l.index(m0)));
                assert(!(forall|j2: int|
                    1 <= j2 < (l.len() as int)
                        ==> uts46_ldh_byte(l.index(j2))));
                assert((l.len() as int) != 0);
                assert(!((l.len() as int) >= 4
                    && l.index(2) == 0x2Du8
                    && l.index(3) == 0x2Du8));
                assert(0x61u8 <= l.index(0) && l.index(0) <= 0x7Au8);
                assert(l == run.view().subrange(i as int, j as int));
                assert(uts46_passthrough_label(l) == false);
            }
            return false;
        }
    }
    // the not-hyphen tail (uts46.rs:175)
    let tb = run[j - 1];
    proof {
        assert(rv.index((j - 1) as int) == tb);
        assert(l.index((l.len() as int) - 1)
            == rv.index((j - 1) as int));
    }
    if tb == 0x2Du8 {
        proof {
            assert((l.len() as int) != 0);
            assert(l.index((l.len() as int) - 1)
                == rv.index((j - 1) as int));
            assert(l.index((l.len() as int) - 1) == 0x2Du8);
            assert(l == run.view().subrange(i as int, j as int));
            assert(uts46_passthrough_label(l) == false);
        }
        return false;
    }
    proof {
        assert(uts46_passthrough_label(l) == true) by {
            assert((l.len() as int) != 0);
            assert(!((l.len() as int) >= 4
                && l.index(2) == 0x2Du8
                && l.index(3) == 0x2Du8));
            assert(0x61u8 <= l.index(0) && l.index(0) <= 0x7Au8);
            assert forall|j2: int|
                1 <= j2 < (l.len() as int)
                implies uts46_ldh_byte(l.index(j2)) by {
                let m2 = (i as int) + j2;
                assert(m2 < (k as int));
            }
            assert(l.index((l.len() as int) - 1) != 0x2Du8);
        }
        assert(l == run.view().subrange(i as int, j as int));
    }
    true
}

/// Origin Rust (idna/src/uts46.rs:1064-1090 + 143-183): the exec walk
/// over the run's dot labels, terminating at the first label that
/// fails is_passthrough_ascii_label -- the runtime answer of the
/// uts46 ASCII prefix tier over the run. The true verdict is the
/// Passthrough accounting (to_ascii_from_cow returns the run bytes);
/// the false verdict reports the label that detours to the deeper
/// punycode/mapping path (the tabular tier).
pub exec fn uts46_tier_scan_run(run: &Vec<u8>) -> (r: bool)
    ensures
        r == uts46_identity_tier(run.view(), 0),
{
    let ghost rv = run.view();
    let n = run.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == run.len(),
            rv == run.view(),
            (n as int) == (rv.len() as int),
            uts46_identity_tier(rv, 0)
                == uts46_identity_tier(rv, i as int),
        decreases (n as int) - (i as int),
    {
        // the label-end dot scan (the split boundary)
        let mut j: usize = i;
        while j < n && run[j] != 0x2Eu8
            invariant
                i <= j <= n,
                n == run.len(),
                rv == run.view(),
                (n as int) == (rv.len() as int),
                forall|m: int| (i as int) <= m < (j as int)
                    ==> rv.index(m) != 0x2Eu8,
            decreases (n as int) - (j as int),
        {
            proof {
                assert(rv.index(j as int) != 0x2Eu8);
            }
            j += 1;
        }
        proof {
            if j < n {
                assert(rv.index(j as int) == 0x2Eu8);
            }
            assert(j == n || rv.index(j as int) == 0x2Eu8);
            dot_from_scouted(rv, i as int, j as int);
            assert(dot_from(rv, i as int) == (j as int));
        }
        if !uts46_label_pass_check(run, i, j) {
            proof {
                reveal_with_fuel(uts46_identity_tier, 2);
                assert(!uts46_passthrough_label(
                    rv.subrange(i as int, j as int)));
                assert(uts46_identity_tier(rv, i as int) == false);
                assert(uts46_identity_tier(rv, 0) == false);
            }
            return false;
        }
        proof {
            // the chain keeps the walk conjunction intact across the
            // passing label (the invariant's tier(rv, 0) face)
            reveal_with_fuel(uts46_identity_tier, 2);
            let kq = (j as int);
            assert(uts46_passthrough_label(
                rv.subrange(i as int, kq)));
            if j < n {
                assert(uts46_identity_tier(rv, i as int)
                    == uts46_identity_tier(rv, kq + 1));
                assert(uts46_identity_tier(rv, 0)
                    == uts46_identity_tier(rv, kq + 1));
            } else {
                assert(kq == rv.len());
                assert(uts46_identity_tier(rv, i as int) == true);
                assert(uts46_identity_tier(rv, 0) == true);
            }
        }
        if j < n {
            i = j + 1;
        } else {
            i = j;
        }
    }
    proof {
        reveal_with_fuel(uts46_identity_tier, 2);
        assert(uts46_identity_tier(rv, n as int) == true);
        assert(uts46_identity_tier(rv, 0) == true);
    }
    true
}

/// The rightmost '.' of s at or above i (-1 when none) -- the
/// descending max-face of str::rsplit('.')'s first piece boundary.
pub closed spec fn rlast_dot(s: Seq<u8>, i: int) -> int
    decreases (s.len() as int) - i,
{
    if !(0 <= i && i <= (s.len() as int)) {
        // the out-of-domain guard (the callers sit inside [0, len])
        -1int
    } else if i == (s.len() as int) {
        -1int
    } else {
        let d = rlast_dot(s, i + 1);
        if d >= 0 {
            d
        } else if s.index(i) == 0x2Eu8 {
            i
        } else {
            -1int
        }
    }
}

/// The max-face of rlast_dot: the scouted position is the rightmost dot
/// of the span (every dot above it is ruled out).
pub proof fn rlast_dot_facts(s: Seq<u8>, i: int)
    requires
        0 <= i <= (s.len() as int),
    ensures
        (forall|k: int|
            (i <= k < (s.len() as int) && s.index(k) == 0x2Eu8)
                ==> i <= k <= rlast_dot(s, i)),
        rlast_dot(s, i) >= 0
            ==> (s.index(rlast_dot(s, i)) == 0x2Eu8
                && i <= rlast_dot(s, i) < (s.len() as int)),
        rlast_dot(s, i) >= 0
            ==> (forall|k: int| rlast_dot(s, i) < k < (s.len() as int)
                ==> s.index(k) != 0x2Eu8),
    decreases (s.len() as int) - i,
{
    if i < (s.len() as int) {
        reveal_with_fuel(rlast_dot, 2);
        rlast_dot_facts(s, i + 1);
        if rlast_dot(s, i + 1) >= 0 {
            // the recursion already found the rightmost dot of the
            // upper span; the equality carries every conjunct through
        } else {
            // no dot above the position: the scouted value is the
            // position itself when it is a dot, and any dot of the
            // upper span would contradict the recursion's max face
            assert forall|k: int| (i + 1) <= k < (s.len() as int)
                ==> s.index(k) != 0x2Eu8 by {
                assert forall|k: int| (i + 1) <= k < (s.len() as int)
                    && s.index(k) == 0x2Eu8
                    ==> (i + 1) <= k <= rlast_dot(s, i + 1) by {
                }
            }
            if s.index(i) == 0x2Eu8 {
                assert(rlast_dot(s, i) == i);
            }
        }
    }
}

/// Origin Rust (host.rs:276-293): the ends_in_a_number candidate --
/// the rsplit('.') walk: the piece after the last dot when it is
/// non-empty, else the piece between the second-last dot and the last
/// dock (also the empty piece when the run began with the dot); the
/// candidate of a dot-free run is the run itself, and the empty run
/// has no candidate at all (host.rs:282-283 then returns false).
pub open spec fn ipv4_candidate(s: Seq<u8>) -> Seq<u8> {
    let d = rlast_dot(s, 0);
    if d < 0 {
        s
    } else {
        let after = s.subrange(d + 1, (s.len() as int));
        if (after.len() as int) > 0 {
            after
        } else {
            // the rsplit fallback: the dashed piece one split further
            // left (host.rs:279-284)
            let d2 = rlast_dot(s.subrange(0, d), 0);
            s.subrange(d2 + 1, d)
        }
    }
}

/// Origin Rust (host.rs:297-330): the parse_ipv4number outcome face --
/// the Err side is the empty input or the invalid radix-class side;
/// both Ok arms (the fitted value and the u32-overflow None of
/// u32::from_str_radix, host.rs:325-329) count, because ends_in_a
/// number consumes parse_ipv4number(last).is_ok() (host.rs:292).
/// The radix prefixes are the "0x"/"0X" head (host.rs:302-305), the
/// length-2 '0' head (host.rs:306-308), else decimal; the empty
/// remainder after a prefix parses as Ok(Some(0)) (host.rs:310-312).
pub open spec fn ipv4_number_check_ok(s: Seq<u8>) -> bool {
    if (s.len() as int) == 0 {
        false
    } else if (s.len() as int) >= 2
        && s.index(0) == 0x30u8
        && (s.index(1) == 0x58u8 || s.index(1) == 0x78u8)
    {
        // the "0x"/"0X" head (host.rs:302-305): the hex remainder,
        // the empty one parsing as Ok(Some(0)) (host.rs:310-312)
        let body = s.subrange(2, (s.len() as int));
        (body.len() as int) == 0
            || (forall|j: int|
                0 <= j < (body.len() as int)
                    ==> radix_digit_byte(body.index(j), 16int))
    } else if (s.len() as int) >= 2 && s.index(0) == 0x30u8 {
        // the length-2 '0' head (host.rs:306-308): the octal remainder
        let body = s.subrange(1, (s.len() as int));
        (body.len() as int) == 0
            || (forall|j: int|
                0 <= j < (body.len() as int)
                    ==> radix_digit_byte(body.index(j), 8int))
    } else {
        // no prefix face: the decimal remainder is the whole candidate
        let body = s.subrange(0, (s.len() as int));
        (body.len() as int) == 0
            || (forall|j: int|
                0 <= j < (body.len() as int)
                    ==> radix_digit_byte(body.index(j), 10int))
    }
}

/// Origin Rust (host.rs:315-319): the per-radix digit classes of
/// parse_ipv4number's valid_number scan -- octal '0'..'7' (host.rs:316),
/// decimal '0'..'9' (host.rs:317), hexadecimal (host.rs:318).
pub open spec fn radix_digit_byte(b: u8, r: int) -> bool {
    if r == 8int {
        (0x30u8 <= b && b <= 0x37u8)
    } else if r == 10int {
        super::is_dec_digit(b)
    } else {
        is_ascii_hexdigit_b(b)
    }
}

/// Origin Rust (host.rs:276-293): ends_in_a_number -- the candidate
/// label is all-decimal-digits (host.rs:288-290), or parse_ipv4number
/// accepts it (host.rs:292).
pub open spec fn ends_in_a_number(s: Seq<u8>) -> bool {
    let cand = ipv4_candidate(s);
    (((cand.len() as int) > 0
        && (forall|j: int|
            0 <= j < (cand.len() as int)
                ==> super::is_dec_digit(cand.index(j))))
        || ipv4_number_check_ok(cand))
}

/// Origin Rust (host.rs:297-330): the per-radix digit value of
/// parse_ipv4number's fold -- u32::from_str_radix's digit-value
/// conversion: '0'..'9' the ASCII offset, the hex letters the two
/// case offsets (the octal/decimal arms accept only '0'..'9' bytes
/// through the class gate, so the guard arm below stays out of the
/// accepted-class fold).
pub open spec fn radix_digit_val(b: u8, r: int) -> int {
    if r == 8int {
        (b as int) - 0x30
    } else if r == 10int {
        (b as int) - 0x30
    } else if b >= 0x30u8 && b <= 0x39u8 {
        (b as int) - 0x30
    } else if b >= 0x41u8 && b <= 0x46u8 {
        (b as int) - 0x37
    } else if b >= 0x61u8 && b <= 0x66u8 {
        (b as int) - 0x57
    } else {
        0int
    }
}

/// Origin Rust (host.rs:321-329, the u32::from_str_radix fold): the
/// whole value of a digit string in the radix -- the running total
/// times the radix plus the digit value of the last byte.
pub open spec fn radix_val(s: Seq<u8>, r: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        radix_val(s.subrange(0, s.len() - 1), r) * r
            + radix_digit_val(s.index(s.len() - 1), r)
    }
}

/// The split of a sequence at an inner point: the prefix subrange
/// concatenated with the suffix subrange is the sequence itself (the
/// fold steps of the radix loop ride it).
pub proof fn seq_subrange_split(s: Seq<u8>, i: int)
    requires
        0 <= i,
        i <= s.len(),
    ensures
        s == s.subrange(0, i)
            + s.subrange(i, s.len() as int),
{
    vstd::seq::lemma_seq_add_len(
        s.subrange(0, i), s.subrange(i, s.len() as int));
    assert forall|j: int|
        0 <= j && j < (s.len() as int)
        implies (s.subrange(0, i)
            + s.subrange(i, s.len() as int)).index(j)
            == s.index(j)
    by {
        if j < i {
            vstd::seq::lemma_seq_add_index1(s.subrange(0, i),
                s.subrange(i, s.len() as int), j);
            vstd::seq::lemma_seq_subrange_index(s, 0, i, j);
        } else {
            vstd::seq::lemma_seq_add_index2(s.subrange(0, i),
                s.subrange(i, s.len() as int), j);
            assert((j - i) >= 0 && j - i <= (s.len() as int) - i);
            vstd::seq::lemma_seq_subrange_index(
                s, i, s.len() as int, j - i);
        }
    }
    vstd::seq::lemma_seq_ext_equal(
        s.subrange(0, i) + s.subrange(i, s.len() as int), s);
}

/// radix_val extended by one trailing digit (the fold step; the
/// definitional subrange composition of dec_val_push).
pub proof fn radix_val_push(b: u8, k: Seq<u8>, r: int)
    ensures
        radix_val(k + seq![b], r)
            == radix_val(k, r) * r + radix_digit_val(b, r),
{
    let full = k + seq![b];
    assert(full.subrange(0, full.len() as int - 1) == k) by {
        vstd::seq::lemma_seq_subrange_composition(
            full, 0, full.len() as int, 0, (full.len() as int) - 1);
    };
    vstd::seq::lemma_seq_subrange_index(
        full, (full.len() as int) - 1, full.len() as int, 0);
    assert(full.index((full.len() as int) - 1) == b);
}

/// The class digit value bound: a digit byte of the radix class
/// carries a nonnegative in-radix value (the guard arm of
/// radix_digit_val never fires on the class; every class value sits
/// at or below 15, and at or below the radix on the three radix
/// values the fold uses).
pub proof fn radix_digit_class_val(b: u8, r: int)
    requires
        radix_digit_byte(b, r),
    ensures
        0 <= radix_digit_val(b, r),
        radix_digit_val(b, r) <= 15,
        r == 8int ==> radix_digit_val(b, r) <= 7,
        r == 10int ==> radix_digit_val(b, r) <= 9,
        r == 16int ==> radix_digit_val(b, r) <= 15,
{
    // the class's byte-range split instantiates the value defs on
    // both sides: the octal/decimal arms take the digit offset, any
    // other radix takes the hex classes
    if r == 8int {
    } else if r == 10int {
    } else if (b >= 0x30u8 && b <= 0x39u8) {
    } else if (b >= 0x41u8 && b <= 0x46u8) {
    } else {
        // the class's remaining range: 'a'..'f'
    }
}

/// The fold stays nonnegative on the accepted class (the induction
/// companion of the value face of u32::from_str_radix's loop).
pub proof fn radix_val_nonneg(s: Seq<u8>, r: int)
    requires
        r >= 2int,
        forall|j: int| 0 <= j && j < (s.len() as int)
            ==> radix_digit_byte(s.index(j), r),
    ensures
        radix_val(s, r) >= 0,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let pre = s.subrange(0, s.len() - 1);
        assert forall|j: int| (
            0 <= j && j < (pre.len() as int)
        ) implies radix_digit_byte(pre.index(j), r) by {
            vstd::seq::lemma_seq_subrange_len(s, 0, s.len() - 1);
            vstd::seq::lemma_seq_subrange_index(
                s, 0, s.len() - 1, j);
        }
        radix_val_nonneg(pre, r);
        radix_digit_class_val(s.index(s.len() - 1), r);
    }
}

/// A scalar face of the growth step: a nonnegative value times a
/// radix at least two sits at or above the value itself.
pub proof fn mul_ge_self(v: int, r: int)
    requires
        0 <= v,
        2 <= r,
    ensures
        v * r >= v,
{
    if v == 0 {
    } else {
        assert(v >= 1);
        vstd::arithmetic::mul::lemma_mul_inequality(0, v, r);
        vstd::arithmetic::mul::lemma_mul_ordering(v, r);
    }
}

/// The fold only grows: one more class digit multiplies the running
/// value by the radix and adds a nonnegative digit.
pub proof fn radix_val_grows(b: u8, k: Seq<u8>, r: int)
    requires
        r >= 2int,
        radix_digit_byte(b, r),
        forall|j: int| 0 <= j && j < (k.len() as int)
            ==> radix_digit_byte(k.index(j), r),
    ensures
        radix_val(k + seq![b], r) >= radix_val(k, r),
{
    radix_val_push(b, k, r);
    radix_val_nonneg(k, r);
    radix_digit_class_val(b, r);
    assert(radix_digit_val(b, r) >= 0);
    assert(radix_val(k, r) >= 0);
    assert(radix_val(k, r) * r >= radix_val(k, r)) by {
        mul_ge_self(radix_val(k, r), r);
    }
}

/// The whole-run prefix face: the value of the run is at least the
/// value of any class prefix of it (the u32::from_str_radix fold is
/// monotone on the accepted class; the exec twin's early exit below
/// is the value-at-or-above-the-u32-bound face).
pub proof fn radix_val_prefix_ge(s: Seq<u8>, i: int, r: int)
    requires
        r >= 2int,
        0 <= i,
        i <= (s.len() as int),
        forall|j: int| 0 <= j && j < (s.len() as int)
            ==> radix_digit_byte(s.index(j), r),
    ensures
        radix_val(s, r) >= radix_val(s.subrange(0, i), r),
    decreases (s.len() as int) - i,
{
    if (s.len() as int) == 0 {
        assert(s.subrange(0, 0) == Seq::empty());
        assert(s == Seq::empty());
    } else if i >= (s.len() as int) {
        // the whole-run prefix: the identity of the full subrange
        assert(s.subrange(0, s.len() as int) == s) by {
            assert forall|j: int|
                0 <= j && j < (s.len() as int)
                implies s.subrange(0, s.len() as int).index(j)
                    == s.index(j) by {
                vstd::seq::lemma_seq_subrange_index(
                    s, 0, s.len() as int, j);
            }
            vstd::seq::lemma_seq_ext_equal(
                s.subrange(0, s.len() as int), s);
        }
    } else {
        let pre = s.subrange(0, s.len() - 1);
        assert forall|j: int| (
            0 <= j && j < (pre.len() as int)
        ) implies radix_digit_byte(pre.index(j), r) by {
            vstd::seq::lemma_seq_subrange_len(s, 0, s.len() - 1);
            vstd::seq::lemma_seq_subrange_index(
                s, 0, s.len() - 1, j);
        }
        assert(i <= (pre.len() as int));
        assert(pre.subrange(0, i) == s.subrange(0, i)) by {
            vstd::seq::lemma_seq_subrange_composition(
                s, 0, s.len() - 1, 0, i);
        }
        radix_val_prefix_ge(pre, i, r);
        assert(radix_val(s, r)
            >= radix_val(pre, r)) by {
            radix_val_grows(s.index(s.len() - 1), pre, r);
            assert(s == pre + seq![s.index(s.len() - 1)]) by {
                assert(s.subrange(0, s.len() - 1)
                    + seq![s.index(s.len() - 1)] == s) by {
                    assert(s.subrange(0, s.len() - 1) == pre) by {
                        vstd::seq::lemma_seq_ext_equal(
                            s.subrange(0, s.len() - 1), pre);
                    }
                }
                vstd::seq::lemma_seq_ext_equal(
                    s, pre + seq![s.index(s.len() - 1)]);
            }
        }
    }
}

/// Origin Rust (host.rs:302-312): the radix parse_ipv4number picks
/// -- the "0x"/"0X" head (16), the length-2 '0' head (8), else 10.
pub open spec fn ipv4_number_radix(s: Seq<u8>) -> int {
    if (s.len() as int) >= 2
        && s.index(0) == 0x30u8
        && (s.index(1) == 0x58u8 || s.index(1) == 0x78u8)
    {
        16int
    } else if (s.len() as int) >= 2 && s.index(0) == 0x30u8 {
        8int
    } else {
        10int
    }
}

/// Origin Rust (host.rs:302-312): the digit body the radix fold
/// consumes -- the remainder after the radix head consumes its bytes.
pub open spec fn ipv4_number_body(s: Seq<u8>) -> Seq<u8> {
    if (s.len() as int) >= 2
        && s.index(0) == 0x30u8
        && (s.index(1) == 0x58u8 || s.index(1) == 0x78u8)
    {
        s.subrange(2, s.len() as int)
    } else if (s.len() as int) >= 2 && s.index(0) == 0x30u8 {
        s.subrange(1, s.len() as int)
    } else {
        s
    }
}

/// The exec twin of the three radix-digit classes of parse_ipv4number
/// (host.rs:315-319: octal '0'..'7', decimal '0'..'9', hexadecimal);
/// the radix rides a u32 whose three accepted values are the
/// spec-side int radixes.
pub exec fn radix_digit_byte_exec(b: u8, r: u32) -> (ok: bool)
    ensures
        ok == radix_digit_byte(b, (r as int)),
{
    if r == 8u32 {
        0x30u8 <= b && b <= 0x37u8
    } else if r == 10u32 {
        0x30u8 <= b && b <= 0x39u8
    } else {
        (0x30u8 <= b && b <= 0x39u8)
            || (0x41u8 <= b && b <= 0x46u8)
            || (0x61u8 <= b && b <= 0x66u8)
    }
}

/// The exec twin of the digit-value conversion of the radix fold
/// (the accepted-class arm of radix_digit_val; the caller's class
/// gate keeps the guard arm out, so the subtractions stay in range).
pub exec fn radix_digit_val_exec(b: u8, r: u32) -> (d: u64)
    requires
        radix_digit_byte(b, (r as int)),
        (r == 8u32 || r == 10u32 || r == 16u32),
    ensures
        (d as int) == radix_digit_val(b, (r as int)),
{
    if r == 16u32 {
        // the hexadecimal classes: '0'..'9', 'A'..'F', 'a'..'f'
        if 0x30u8 <= b && b <= 0x39u8 {
            proof { assert(radix_digit_val(b, (r as int)) == (b as int) - 0x30); }
            ((b - 0x30u8) as u64)
        } else if 0x41u8 <= b && b <= 0x46u8 {
            proof { assert(radix_digit_val(b, (r as int)) == (b as int) - 0x37); }
            ((b - 0x37u8) as u64)
        } else {
            proof {
                assert(b >= 0x61u8 && b <= 0x66u8);
                assert(radix_digit_val(b, (r as int)) == (b as int) - 0x57);
            }
            ((b - 0x57u8) as u64)
        }
    } else {
        // octal and decimal accept only '0'..'7' / '0'..'9'
        proof {
            assert(b >= 0x30u8);
            assert(radix_digit_val(b, (r as int)) == (b as int) - 0x30);
        }
        ((b - 0x30u8) as u64)
    }
}

/// The per-arm establishment of the number-check face over a scan
/// span: the head bytes pin the arm exactly and the class-forall
/// over the span instantiates the arm's own body quantifier.
pub proof fn ipv4_number_check_establish(
    s: Seq<u8>,
    a: int,
    r: int,
)
    requires
        (s.len() as int) > 0,
        0 <= a,
        a <= (s.len() as int),
        ((s.len() as int) - a) > 0,
        r == 16int
            ==> ((s.len() as int) >= 2
                && s.index(0) == 0x30u8
                && (s.index(1) == 0x58u8 || s.index(1) == 0x78u8)
                && a == 2),
        r == 8int
            ==> ((s.len() as int) >= 2
                && s.index(0) == 0x30u8
                && !(s.index(1) == 0x58u8 || s.index(1) == 0x78u8)
                && a == 1),
        r == 10int
            ==> (a == 0
                && !((s.len() as int) >= 2
                    && s.index(0) == 0x30u8)),
        r == 8int || r == 10int || r == 16int,
        ipv4_number_body(s) == s.subrange(a, s.len() as int),
        ipv4_number_radix(s) == r,
        forall|j: int| a <= j && j < (s.len() as int)
            ==> radix_digit_byte(s.index(j), r),
    ensures
        ipv4_number_check_ok(s),
{
    if r == 16int {
        let bodyq = s.subrange(2, s.len() as int);
        assert(bodyq == s.subrange(a, s.len() as int));
        vstd::seq::lemma_seq_subrange_len(s, 2, s.len() as int);
        assert forall|j: int| (
            0 <= j && j < (bodyq.len() as int)
        ) implies radix_digit_byte(bodyq.index(j), 16int) by {
            assert(bodyq.index(j) == s.index(2 + j)) by {
                vstd::seq::lemma_seq_subrange_index(
                    s, 2, s.len() as int, j);
            }
        }
        assert(ipv4_number_check_ok(s));
    } else if r == 8int {
        let bodyq = s.subrange(1, s.len() as int);
        assert(bodyq == s.subrange(a, s.len() as int));
        vstd::seq::lemma_seq_subrange_len(s, 1, s.len() as int);
        assert forall|j: int| (
            0 <= j && j < (bodyq.len() as int)
        ) implies radix_digit_byte(bodyq.index(j), 8int) by {
            assert(bodyq.index(j) == s.index(1 + j)) by {
                vstd::seq::lemma_seq_subrange_index(
                    s, 1, s.len() as int, j);
            }
        }
        assert(!(s.index(1) == 0x58u8 || s.index(1) == 0x78u8));
        assert(ipv4_number_check_ok(s));
    } else {
        assert(!(s.index(0) == 0x30u8)
            || (s.len() as int) < 2);
        assert(ipv4_number_check_ok(s));
    }
}

/// The per-arm refutation of the number-check face: a class failure
/// inside the head-pinned arm's own body.
pub proof fn ipv4_number_check_refute(
    s: Seq<u8>,
    a: int,
    r: int,
    j0: int,
)
    requires
        (s.len() as int) > 0,
        0 <= a,
        a <= (s.len() as int),
        ((s.len() as int) - a) > 0,
        0 <= j0,
        j0 < (s.len() as int) - a,
        !radix_digit_byte(s.index(a + j0), r),
        r == 16int
            ==> ((s.len() as int) >= 2
                && s.index(0) == 0x30u8
                && (s.index(1) == 0x58u8 || s.index(1) == 0x78u8)
                && a == 2),
        r == 8int
            ==> ((s.len() as int) >= 2
                && s.index(0) == 0x30u8
                && !(s.index(1) == 0x58u8 || s.index(1) == 0x78u8)
                && a == 1),
        r == 10int
            ==> (a == 0
                && !((s.len() as int) >= 2
                    && s.index(0) == 0x30u8)),
        r == 8int || r == 10int || r == 16int,
        ipv4_number_body(s) == s.subrange(a, s.len() as int),
        ipv4_number_radix(s) == r,
    ensures
        !ipv4_number_check_ok(s),
{
    if r == 16int {
        let bodyq = s.subrange(2, s.len() as int);
        assert(bodyq == s.subrange(a, s.len() as int));
        vstd::seq::lemma_seq_subrange_len(s, 2, s.len() as int);
        assert(bodyq.index(j0) == s.index(2 + j0)) by {
            vstd::seq::lemma_seq_subrange_index(
                s, 2, s.len() as int, j0);
        }
        assert(!radix_digit_byte(bodyq.index(j0), 16int));
        assert(!(forall|j: int|
            0 <= j && j < (bodyq.len() as int)
                ==> radix_digit_byte(bodyq.index(j), 16int))) by {
            assert(!radix_digit_byte(bodyq.index(j0), 16int));
        }
        assert(!ipv4_number_check_ok(s));
    } else if r == 8int {
        let bodyq = s.subrange(1, s.len() as int);
        assert(bodyq == s.subrange(a, s.len() as int));
        vstd::seq::lemma_seq_subrange_len(s, 1, s.len() as int);
        assert(bodyq.index(j0) == s.index(1 + j0)) by {
            vstd::seq::lemma_seq_subrange_index(
                s, 1, s.len() as int, j0);
        }
        assert(!radix_digit_byte(bodyq.index(j0), 8int));
        assert(!(s.index(1) == 0x58u8 || s.index(1) == 0x78u8));
        assert(!(forall|j: int|
            0 <= j && j < (bodyq.len() as int)
                ==> radix_digit_byte(bodyq.index(j), 8int)));
        assert(!ipv4_number_check_ok(s));
    } else {
        assert(!(s.index(0) == 0x30u8)
            || (s.len() as int) < 2);
        let bodyq = s.subrange(0, s.len() as int);
        assert(bodyq == s);
        assert(bodyq.index(j0) == s.index(j0)) by {
            vstd::seq::lemma_seq_subrange_index(
                s, 0, s.len() as int, j0);
        }
        assert(!radix_digit_byte(bodyq.index(j0), 10int));
        assert(!(forall|j: int|
            0 <= j && j < (bodyq.len() as int)
                ==> radix_digit_byte(bodyq.index(j), 10int)));
        assert(!ipv4_number_check_ok(s));
    }
}

/// Origin Rust (host.rs:297-330): fn parse_ipv4number(input) ->
/// Result<Option<u32>, ()> -- the ipv4 number scan: the radix head,
/// the per-radix class gate, the u32 fold. Ok(None) is the overflow
/// face of u32::from_str_radix (the class checked first, host.rs:331:
/// "The only possible error kind here is an integer overflow"); the
/// empty input and the invalid-class input are the Err(()) arms.
/// The &str face is the byte slice (ledger 1). The exec fold carries
/// the running value in u64 with a pre-step u32 ceiling (a class
/// prefix at or above the bound pins the whole value through the
/// monotone fold, and the per-step products stay under 2^36), so the
/// u64 arithmetic never wraps and the exec never touches a wrapping
/// op of upstream's from_str_radix internals.
pub exec fn parse_ipv4number(s: &[u8]) -> (r: Result<Option<u32>, ()>)
    ensures
        (r.is_ok() == ipv4_number_check_ok(s@)),
        (r.is_ok() ==> match r.unwrap() {
            Option::Some(v) => ({
                let body = ipv4_number_body(s@);
                &&& (radix_val(body, ipv4_number_radix(s@)) == (v as int))
                &&& ((v as int) <= 0xFFFF_FFFF)
            }),
            Option::None => ({
                let body = ipv4_number_body(s@);
                radix_val(body, ipv4_number_radix(s@)) > 0xFFFF_FFFF
            }),
        }),
{
    if s.len() == 0 {
        // host.rs:299-301: the empty input
        return Err(());
    }
    // the radix heads (host.rs:302-308)
    let n = s.len();
    let (rad, a): (u32, usize) =
        if n >= 2
            && s[0] == 0x30u8
            && (s[1] == 0x58u8 || s[1] == 0x78u8)
        {
            (16u32, 2usize)
        } else if n >= 2 && s[0] == 0x30u8 {
            (8u32, 1usize)
        } else {
            (10u32, 0usize)
        };
    proof {
        assert((a as int) <= (n as int));
        assert((rad as int) == ipv4_number_radix(s.view()));
        assert(s.view().subrange(a as int, n as int)
            == ipv4_number_body(s.view()));
    }
    if a == n {
        // host.rs:310-312: the empty remainder after the head parses
        // as Ok(Some(0)); the fold of the empty body is 0 (the
        // decimal head cannot reach here: n > 0 keeps a < n)
        proof {
            assert((ipv4_number_body(s.view()).len() as int) == 0);
            assert(ipv4_number_check_ok(s.view())) by {
                if (rad as int) == 16int {
                    assert(s.view().index(0) == 0x30u8);
                    assert(s.view().index(1) == 0x58u8
                        || s.view().index(1) == 0x78u8);
                    assert((s.len() as int) >= 2);
                    assert(s.view().subrange(2, s.len() as int)
                        .len() == (s.len() as int) - 2);
                } else {
                    assert((rad as int) == 8int);
                    assert(s.view().index(0) == 0x30u8);
                    assert((s.len() as int) >= 2);
                    assert(s.view().subrange(1, s.len() as int)
                        .len() == (s.len() as int) - 1);
                }
            }
            assert(radix_val(ipv4_number_body(s.view()),
                ipv4_number_radix(s.view())) == 0);
        }
        return Ok(Option::Some(0u32));
    }
    // the class gate (host.rs:315-319): one scan, the first failing
    // byte returns the Err arm -- no flag-break loop
    let mut i = a;
    while i < s.len()
        invariant
            i <= s.len(),
            n == s.len(),
            (a as int) <= (i as int),
            (a as int) <= (n as int),
            ((rad as int) == ipv4_number_radix(s.view())),
            (s.view().subrange(a as int, n as int)
                == ipv4_number_body(s.view())),
            (((rad as int) == 16int)
                ==> ((a as int) == 2
                    && s.view().index(0) == 0x30u8
                    && s.view().index(1) > 0x00u8)),
            (((rad as int) == 8int)
                ==> ((a as int) == 1
                    && s.view().index(0) == 0x30u8)),
            (((rad as int) == 10int)
                ==> (a as int) == 0),
            forall|j: int|
                #![trigger radix_digit_byte(
                    s.view().index(j), (rad as int))]
                (a as int) <= j && j < (i as int)
                    ==> radix_digit_byte(
                        s.view().index(j), (rad as int)),
        decreases n - i,
    {
        let c = s[i];
        let ok = radix_digit_byte_exec(c, rad);
        if !ok {
            // the Err arm: the class gate fails inside the body, so
            // the number-check face fails
            proof {
                let j0 = (i as int) - (a as int);
                assert((n as int) - (a as int) > 0);
                assert((n as int) == (s.len() as int));
                assert(0 <= j0 && j0 < (n as int) - (a as int));
                assert(c == s.view().index((a as int) + j0)) by {
                    assert(c == s.view().index(i as int));
                }
                // the head pins of the radix arm, from the radix tie
                if (rad as int) == 16int {
                    assert(s.view().index(0) == 0x30u8);
                    assert(s.view().index(1) == 0x58u8
                        || s.view().index(1) == 0x78u8);
                    assert((s.len() as int) >= 2);
                    assert((a as int) == 2);
                } else if (rad as int) == 8int {
                    assert(s.view().index(0) == 0x30u8);
                    assert((s.len() as int) >= 2);
                    assert(!(s.view().index(1) == 0x58u8
                        || s.view().index(1) == 0x78u8));
                    assert((a as int) == 1);
                } else {
                    assert((rad as int) == 10int);
                    assert((a as int) == 0);
                    assert(!((s.len() as int) >= 2
                        && s.view().index(0) == 0x30u8));
                }
                assert(!radix_digit_byte(c, (rad as int)));
                ipv4_number_check_refute(s.view(), a as int,
                    (rad as int), j0);
                assert(!ipv4_number_check_ok(s.view()));
            }
            return Err(());
        }
        i += 1;
    }
    // u32::from_str_radix (host.rs:321-329): the fold with the
    // pre-step u32 ceiling
    let mut acc: u64 = 0;
    let mut i = a;
    while i < s.len()
        invariant
            i <= s.len(),
            n == s.len(),
            (a as int) <= (i as int),
            (a as int) < (n as int),
            ((rad as int) == ipv4_number_radix(s.view())),
            (s.view().subrange(a as int, n as int)
                == ipv4_number_body(s.view())),
            (((rad as int) == 16int)
                ==> ((a as int) == 2
                    && s.view().index(0) == 0x30u8
                    && s.view().index(1) > 0x00u8)),
            (((rad as int) == 8int)
                ==> ((a as int) == 1
                    && s.view().index(0) == 0x30u8)),
            (((rad as int) == 10int)
                ==> (a as int) == 0),
            (acc as int)
                == radix_val(
                    s.view().subrange(a as int, i as int),
                    (rad as int)),
            (0 <= (rad as int) && (rad as int) <= 16),
            forall|j: int|
                #![trigger radix_digit_byte(
                    s.view().index(j), (rad as int))]
                (a as int) <= j && j < (n as int)
                    ==> radix_digit_byte(
                        s.view().index(j), (rad as int)),
        decreases n - i,
    {
        if acc >= 0x1_0000_0000u64 {
            // the overflow face: the value of the scanned prefix
            // already reached the u32 ceiling, and the class prefix
            // below the whole body pins the whole value above it
            proof {
                let pref = s.view().subrange(a as int, i as int);
                assert(radix_val(pref, (rad as int))
                    >= 0x1_0000_0000);
                let bodyq = s.view().subrange(a as int, n as int);
                assert forall|j: int| (
                    0 <= j && j < (bodyq.len() as int)
                ) implies radix_digit_byte(bodyq.index(j),
                    (rad as int)) by {
                    assert(bodyq.index(j)
                        == s.view().index((a as int) + j)) by {
                        vstd::seq::lemma_seq_subrange_composition(
                            s.view(), a as int, n as int, j, j + 1);
                        vstd::seq::lemma_seq_subrange_index(
                            s.view().subrange(a as int, n as int),
                            j, j + 1, 0);
                    }
                }
                radix_val_nonneg(bodyq, (rad as int));
                vstd::seq::lemma_seq_subrange_composition(
                    s.view(), a as int, n as int, 0,
                    (i as int) - (a as int));
                assert(pref == s.view().subrange(a as int, i as int));
                assert(pref == bodyq.subrange(
                    0, (i as int) - (a as int)));
                radix_val_prefix_ge(bodyq, i as int - a as int,
                    (rad as int));
                assert(radix_val(bodyq, (rad as int)) > 0xFFFF_FFFF);
                // the head pins of the radix arm, from the radix tie
                if (rad as int) == 16int {
                    assert(s.view().index(0) == 0x30u8);
                    assert(s.view().index(1) == 0x58u8
                        || s.view().index(1) == 0x78u8);
                    assert((s.len() as int) >= 2);
                    assert((a as int) == 2);
                } else if (rad as int) == 8int {
                    assert(s.view().index(0) == 0x30u8);
                    assert((s.len() as int) >= 2);
                    assert(!(s.view().index(1) == 0x58u8
                        || s.view().index(1) == 0x78u8));
                    assert((a as int) == 1);
                } else {
                    assert((rad as int) == 10int);
                    assert((a as int) == 0);
                    assert(!((s.len() as int) >= 2
                        && s.view().index(0) == 0x30u8));
                }
                assert(bodyq == ipv4_number_body(s.view()));
                assert((rad as int) == ipv4_number_radix(s.view()));
                assert((bodyq.len() as int) > 0);
                ipv4_number_check_establish(s.view(), a as int,
                    (rad as int));
                assert(ipv4_number_check_ok(s.view()));
            }
            return Ok(Option::None);
        }
        let c = s[i];
        let d = radix_digit_val_exec(c, rad);
        proof {
            // the pre-assign bounds: the u32-gated accumulator, the
            // radix, and the class digit bound the product below
            // 2^36, inside the u64 domain
            let k = (i as int) - (a as int);
            let pref0 = s.view().subrange(a as int, i as int);
            let pref1 = s.view().subrange(a as int, (i + 1) as int);
            let ghost acc0 = (acc as int);
            let ghost dv0 = (d as int);
            assert(acc0 < 0x1_0000_0000);
            assert((rad as int) <= 16);
            assert(dv0 == radix_digit_val(c, (rad as int)));
            assert(radix_digit_byte(c, (rad as int)));
            assert(c == s.view().index(i as int));
            assert(radix_digit_val(c, (rad as int)) <= 15) by {
                radix_digit_class_val(c, (rad as int));
            }
            assert(acc0 * (rad as int) + dv0
                <= 0xFFFF_FFFF * 16 + 15);
            // the stride split: the pref1 prefix of the scan is
            // pref0 plus this one byte
            assert(pref0 + seq![c] == pref1) by {
                seq_subrange_split(pref1, k);
                vstd::seq::lemma_seq_subrange_composition(
                    s.view(), a as int, (i + 1) as int, 0, k);
                vstd::seq::lemma_seq_subrange_composition(
                    s.view(), a as int, (i + 1) as int, k, k + 1);
                assert(s.view().subrange((i as int), (i + 1) as int)
                    == seq![c]) by {
                    vstd::seq::lemma_seq_subrange_len(
                        s.view(), i as int, (i + 1) as int);
                    vstd::seq::lemma_seq_subrange_index(
                        s.view(), i as int, (i + 1) as int, 0);
                    assert forall|j2: int| (
                        0 <= j2 && j2 < 1
                    ) implies s.view()
                        .subrange(i as int, (i + 1) as int)
                        .index(j2) == seq![c].index(j2) by {
                        vstd::seq::lemma_seq_subrange_index(
                            s.view(), i as int, (i + 1) as int, j2);
                    }
                    vstd::seq::lemma_seq_ext_equal(
                        s.view().subrange(i as int, (i + 1) as int),
                        seq![c]);
                }
                assert(s.view().subrange(
                    (a as int) + k, (a as int) + k + 1)
                    == s.view().subrange(i as int, (i + 1) as int));
            }
            radix_val_push(c, pref0, (rad as int));
            assert(radix_val(pref1, (rad as int))
                == radix_val(pref0, (rad as int)) * (rad as int)
                    + radix_digit_val(c, (rad as int)));
            // the invariant's value tie, on the pre-assign terms
            assert(radix_val(pref0, (rad as int)) == acc0);
            assert(radix_val(pref1, (rad as int))
                == acc0 * (rad as int) + dv0);
        }
        acc = acc * (rad as u64) + d;
        proof {
            // the post-assign faces: the new accumulator is the
            // pref1 value, under the invariant's ceiling
            assert((acc as int) == (radix_val(
                s.view().subrange(a as int, (i + 1) as int),
                (rad as int))));
            assert((acc as int) <= 0xFFFF_FFFF * 16 + 15);
        }
        i += 1;
    }
    // the fold completed inside the u32 ceiling
    if acc > 0xFFFF_FFFFu64 {
        // the end-of-input overflow face: the whole value sits above
        // the u32 ceiling
        proof {
            let bodyq = s.view().subrange(a as int, n as int);
            assert((bodyq.len() as int) == (n as int) - (a as int));
                // the head pins of the radix arm, from the radix tie
                if (rad as int) == 16int {
                    assert(s.view().index(0) == 0x30u8);
                    assert(s.view().index(1) == 0x58u8
                        || s.view().index(1) == 0x78u8);
                    assert((s.len() as int) >= 2);
                    assert((a as int) == 2);
                } else if (rad as int) == 8int {
                    assert(s.view().index(0) == 0x30u8);
                    assert((s.len() as int) >= 2);
                    assert(!(s.view().index(1) == 0x58u8
                        || s.view().index(1) == 0x78u8));
                    assert((a as int) == 1);
                } else {
                    assert((rad as int) == 10int);
                    assert((a as int) == 0);
                    assert(!((s.len() as int) >= 2
                        && s.view().index(0) == 0x30u8));
                }
            assert(bodyq == ipv4_number_body(s.view()));
            assert((rad as int) == ipv4_number_radix(s.view()));
            assert((bodyq.len() as int) > 0);
            ipv4_number_check_establish(s.view(), a as int,
                (rad as int));
            assert(ipv4_number_check_ok(s.view()));
            assert(radix_val(bodyq, (rad as int)) > 0xFFFF_FFFF);
        }
        return Ok(Option::None);
    }
    proof {
        let bodyq = s.view().subrange(a as int, n as int);
        assert((bodyq.len() as int) == (n as int) - (a as int));
                // the head pins of the radix arm, from the radix tie
                if (rad as int) == 16int {
                    assert(s.view().index(0) == 0x30u8);
                    assert(s.view().index(1) == 0x58u8
                        || s.view().index(1) == 0x78u8);
                    assert((s.len() as int) >= 2);
                    assert((a as int) == 2);
                } else if (rad as int) == 8int {
                    assert(s.view().index(0) == 0x30u8);
                    assert((s.len() as int) >= 2);
                    assert(!(s.view().index(1) == 0x58u8
                        || s.view().index(1) == 0x78u8));
                    assert((a as int) == 1);
                } else {
                    assert((rad as int) == 10int);
                    assert((a as int) == 0);
                    assert(!((s.len() as int) >= 2
                        && s.view().index(0) == 0x30u8));
                }
        assert(bodyq == ipv4_number_body(s.view()));
        assert((rad as int) == ipv4_number_radix(s.view()));
        assert((bodyq.len() as int) > 0);
        ipv4_number_check_establish(s.view(), a as int,
            (rad as int));
        assert(ipv4_number_check_ok(s.view()));
        assert(radix_val(bodyq, (rad as int)) == (acc as int));
        assert(radix_val(bodyq, (rad as int)) <= 0xFFFF_FFFF);
    }
    Ok(Option::Some(acc as u32))
}

/// Origin Rust (host.rs:334, split('.')'s next constituent): the
/// first-dot probe -- the forward cursor of the part scan over the
/// machine bytes, the guard arm keeps the cursor total (the open
/// face carries the probe's sign into the termination check of the
/// value recursion below).
pub open spec fn ipv4_fd(s: Seq<u8>, i: int) -> int
    decreases (s.len() as int) - i
{
    if !(0 <= i && i <= (s.len() as int)) {
        -1int
    } else if i == (s.len() as int) {
        -1int
    } else if s.index(i) == 0x2Eu8 {
        i
    } else {
        ipv4_fd(s, i + 1)
    }
}

/// The first dot of the whole run (the scan from position 0).
pub open spec fn ipv4_first_dot(s: Seq<u8>) -> int {
    ipv4_fd(s, 0)
}

/// The scouted first-dot witness: a dot-free run from i to j with
/// either the dot at j or the run ending the byte stream settles the
/// probe's answer (the no-dot face answers -1).
pub proof fn ipv4_fd_scouted(s: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j <= (s.len() as int),
        (forall|m: int| i <= m < j ==> s.index(m) != 0x2Eu8),
        (j == (s.len() as int) || s.index(j) == 0x2Eu8),
    ensures
        ipv4_fd(s, i)
            == (if j == (s.len() as int) { -1int } else { j }),
    decreases (s.len() as int) - i,
{
    if i == j {
        reveal_with_fuel(ipv4_fd, 2);
    } else {
        assert(s.index(i) != 0x2Eu8);
        reveal_with_fuel(ipv4_fd, 2);
        assert(ipv4_fd(s, i) == ipv4_fd(s, i + 1));
        ipv4_fd_scouted(s, i + 1, j);
    }
}

/// Origin Rust (host.rs:345-360): the per-counter bounds of the parts
/// ladder -- u32::MAX >> (8 * numbers.len()) for the popped last
/// part (host.rs:350), the 255 ceiling for every earlier one
/// (host.rs:355), and the per-counter shift of the assembly
/// (n << (8 * (3 - counter)), host.rs:358-359).
pub open spec fn ipv4_last_bound(c: int) -> int {
    if c == 0int {
        0xFFFF_FFFF
    } else if c == 1int {
        16777215
    } else if c == 2int {
        65535
    } else {
        255
    }
}

/// The assembly shift of the part at counter c (host.rs:358-359:
/// 8 * (3 - counter), the counters of the earlier parts).
pub open spec fn ipv4_shift(c: int) -> int {
    if c == 0int {
        16777216
    } else if c == 1int {
        65536
    } else {
        256
    }
}

/// The recursive value face of the ipv4addr assembly over the
/// post-pop part run: the last part parses in place, every earlier
/// part carries its parsed value at its own shift.
pub open spec fn ipv4_addr_value_r(s: Seq<u8>, c: int) -> int
    decreases s.len()
{
    let d = ipv4_first_dot(s);
    if d < 0 || (s.len() as int) <= d {
        // the guard arm (the probe answers -1 at the run's end and
        // an in-domain dot otherwise; the callers sit in-domain)
        radix_val(ipv4_number_body(s), ipv4_number_radix(s))
    } else {
        radix_val(ipv4_number_body(s.subrange(0, d)),
            ipv4_number_radix(s.subrange(0, d)))
            * ipv4_shift(c)
            + ipv4_addr_value_r(
                s.subrange(d + 1, s.len() as int), c + 1)
    }
}

/// Origin Rust (host.rs:333-361): the value of the assembled ipv4
/// number over the input with the trailing-empty pop applied (the
/// split's last part dropped when the input ends on the '.').
pub open spec fn ipv4_addr_value(s: Seq<u8>) -> int {
    if (s.len() as int) > 0
        && s.index((s.len() as int) - 1) == 0x2Eu8
    {
        ipv4_addr_value_r(
            s.subrange(0, (s.len() as int) - 1), 0)
    } else if (s.len() as int) == 0 {
        0int
    } else {
        ipv4_addr_value_r(s, 0)
    }
}

/// Origin Rust (host.rs:333-361): fn parse_ipv4addr(input) ->
/// ParseResult<Ipv4Addr> -- the part ladder: every earlier part
/// parses through parse_ipv4number and stays under 255 (host.rs:355),
/// the counter space carries at most three earlier parts (the
/// parts.len() > 4 gate of host.rs:337-339), the popped last part
/// stays under the u32 shift of the counter space (host.rs:349-351),
/// and the assembly folds the earlier values at their shifts. The
/// per-counter bounds close the u32 domain exactly:
/// 255 * 16777216 + 16777215 == 4294967295 and the same identity one
/// step down each ladder tier.
pub exec fn ipv4addr_go<'i>(
    input: &'i [u8],
    counter: u32,
) -> (r: Result<u32, ParseError>)
    requires
        (input@.len() as int) <= 0xFFFF_FFFF,
        counter == 0u32 || counter == 1u32
            || counter == 2u32 || counter == 3u32,
    ensures
        r.is_err()
            ==> r == Err(ParseError::InvalidIpv4Address),
        r.is_ok() ==> ({
            &&& (r.unwrap() as int)
                == ipv4_addr_value_r(input@, counter as int)
            &&& (r.unwrap() as int)
                <= ipv4_last_bound(counter as int)
        }),
    decreases input@.len(),
{
    let n = input.len();
    if n == 0 {
        // the residual empty part after a dot: parse_ipv4number
        // rejects it (host.rs:299-301)
        return Err(ParseError::InvalidIpv4Address);
    }
    // the next dot of the part run (host.rs:334: split('.'))
    let mut m: usize = 0;
    while m < n && input[m] != 0x2Eu8
        invariant
            m <= n,
            n == input.len(),
            forall|j: int| 0 <= j && j < (m as int)
                ==> input@.index(j) != 0x2Eu8,
        decreases n - m,
    {
        m += 1;
    }
    if m < n {
        // an earlier part of the run: fold at its shift
        proof {
            assert((m as int) < (n as int));
            assert(input@.index(m as int) == 0x2Eu8);
            assert(forall|j: int| 0 <= j && j < (m as int)
                ==> input@.index(j) != 0x2Eu8);
            ipv4_fd_scouted(input@, 0, m as int);
            assert(ipv4_first_dot(input@) == (m as int));
        }
        assert((m as int) + 1 <= (n as int));
        if counter == 3u32 {
            // host.rs:337-339: parts.len() > 4
            return Err(ParseError::InvalidIpv4Address);
        }
        let part = &input[0..m];
        proof {
            assert(part@ == input@.subrange(0, m as int));
        }
        match parse_ipv4number(part) {
            Result::Err(()) => {
                return Err(ParseError::InvalidIpv4Address);
            }
            Result::Ok(Option::None) => {
                // an earlier part's u32 overflow
                return Err(ParseError::InvalidIpv4Address);
            }
            Result::Ok(Option::Some(pv)) => {
                if pv > 255u32 {
                    // host.rs:355: the earlier-part ceiling
                    return Err(ParseError::InvalidIpv4Address);
                }
                let tail = &input[(m + 1)..];
                proof {
                    assert(tail@
                        == input@.subrange((m as int) + 1,
                            n as int));
                }
                let w = match ipv4addr_go(tail, counter + 1) {
                    Result::Err(e) => {
                        return Err(e);
                    }
                    Result::Ok(w0) => w0,
                };
                // host.rs:358-359: ipv4 += n << (8 * (3 - counter))
                let shiftv = ipv4_shift_exec(counter);
                let total = (w as u64) + (pv as u64) * shiftv;
                proof {
                    let c = counter as int;
                    assert(ipv4_shift(c) == (shiftv as int));
                    assert(ipv4_last_bound(c)
                        == 255 * ipv4_shift(c)
                            + ipv4_last_bound(c + 1)) by {
                        if c == 0int {
                            assert(255 * 16777216 + 16777215
                                == 4294967295);
                        } else if c == 1int {
                            assert(255 * 65536 + 65535
                                == 16777215);
                        } else {
                            assert(c == 2int);
                            assert(255 * 256 + 255 == 65535);
                        }
                    }
                    assert((shiftv as int) == 16777216
                        || (shiftv as int) == 65536
                        || (shiftv as int) == 256);
                    assert((pv as int) <= 255);
                    assert((w as int)
                        <= ipv4_last_bound(c + 1));
                    assert((total as int)
                        <= ipv4_last_bound(c));
                    // the front-stride value face: the part's value
                    // at its shift plus the tail ladder
                    assert(ipv4_addr_value_r(input@, c)
                        == radix_val(
                            ipv4_number_body(part@),
                            ipv4_number_radix(part@))
                            * ipv4_shift(c)
                        + ipv4_addr_value_r(tail@, c + 1));
                    assert(radix_val(
                        ipv4_number_body(part@),
                        ipv4_number_radix(part@)) == (pv as int));
                    assert((total as int)
                        == radix_val(
                            ipv4_number_body(part@),
                            ipv4_number_radix(part@))
                            * ipv4_shift(c)
                        + ipv4_addr_value_r(tail@, c + 1));
                }
                Ok(total as u32)
            }
        }
    } else {
        // the last part of the run parses in place
        proof {
            assert((m as int) == (n as int));
            assert(forall|j: int| 0 <= j && j < (n as int)
                ==> input@.index(j) != 0x2Eu8);
            ipv4_fd_scouted(input@, 0, n as int);
            assert(ipv4_first_dot(input@) == -1int);
            reveal(ipv4_addr_value_r);
        }
        match parse_ipv4number(input) {
            Result::Err(()) => {
                return Err(ParseError::InvalidIpv4Address);
            }
            Result::Ok(Option::None) => {
                // the u32 overflow of the last part's fold
                return Err(ParseError::InvalidIpv4Address);
            }
            Result::Ok(Option::Some(v)) => {
                let bound =
                    ipv4_last_bound_exec(counter);
                if (v as u64) > (bound as u64) {
                    // host.rs:349-351: ipv4 > u32::MAX >>
                    // (8 * numbers.len())
                    return Err(ParseError::InvalidIpv4Address);
                }
                proof {
                    let c = counter as int;
                    assert(ipv4_last_bound(c)
                        == (bound as int));
                    // the ladder's bottom: the whole run is the
                    // last part (the probe answers -1)
                    assert(ipv4_addr_value_r(input@, c)
                        == radix_val(
                            ipv4_number_body(input@),
                            ipv4_number_radix(input@)));
                    assert(radix_val(
                        ipv4_number_body(input@),
                        ipv4_number_radix(input@)) == (v as int));
                }
                Ok(v)
            }
        }
    }
}

/// The exec twin of the last-part bound (u32::MAX >> 8 * counter).
pub exec fn ipv4_last_bound_exec(counter: u32) -> (b: u64)
    ensures
        counter == 0u32 ==> (b as int) == 0xFFFF_FFFF,
        counter == 1u32 ==> (b as int) == 16777215,
        counter == 2u32 ==> (b as int) == 65535,
        counter == 3u32 ==> (b as int) == 255,
        (b as int) <= 0xFFFF_FFFF,
{
    if counter == 0u32 {
        0xFFFF_FFFFu64
    } else if counter == 1u32 {
        16777215u64
    } else if counter == 2u32 {
        65535u64
    } else {
        255u64
    }
}

/// The exec twin of the assembly shift at the given counter.
pub exec fn ipv4_shift_exec(counter: u32) -> (sh: u64)
    ensures
        counter == 0u32 ==> (sh as int) == 16777216,
        counter == 1u32 ==> (sh as int) == 65536,
        counter == 2u32 ==> (sh as int) == 256,
        (sh as int) <= 16777216,
{
    if counter == 0u32 {
        16777216u64
    } else if counter == 1u32 {
        65536u64
    } else {
        256u64
    }
}

/// Origin Rust (host.rs:333-361): fn parse_ipv4addr(input) ->
/// ParseResult<Ipv4Addr> -- the trailing-empty pop of the part run
/// (host.rs:337-341: parts.last() == Some("") drops the last part),
/// then the ladder. The address rides its u32 bit pattern (host.rs
/// ledger 1). CONE: the after-pop empty part run of the panic-carry
/// faces -- the empty input and the lone "." -- never reaches here
/// upstream (host.rs:353 numbers.pop().expect -- its callers gate the
/// nonempty host class first, and the class refutations of the
/// deep-host body keep the ends-in-a-number rule off the empty run),
/// so the mirror documents the two faces in the requires.
pub exec fn parse_ipv4addr(input: &[u8])
    -> (r: Result<u32, ParseError>)
    requires
        (input@.len() as int) > 0,
        (input@.len() as int) <= 0xFFFF_FFFF,
        input@ != seq![0x2Eu8],
    ensures
        r.is_err()
            ==> r == Err(ParseError::InvalidIpv4Address),
        r.is_ok() ==> ({
            &&& (r.unwrap() as int) == ipv4_addr_value(input@)
            &&& (r.unwrap() as int) <= 0xFFFF_FFFF
        }),
{
    let n = input.len();
    assert(n >= 1);
    if input[n - 1] == 0x2Eu8 {
        // host.rs:337-341: the trailing-empty part pops
        let head = &input[0..(n - 1)];
        match ipv4addr_go(head, 0u32) {
            Result::Err(e) => Err(e),
            Result::Ok(v) => {
                proof {
                    assert(input@
                        == input@.subrange(0, (n as int) - 1)
                            + seq![0x2Eu8]) by {
                        assert forall|j: int| (
                            0 <= j
                                && j < (input@.len() as int)
                        ) implies input@
                            .subrange(0, (input@.len() as int))
                            .index(j) == input@.index(j) by {
                            vstd::seq::lemma_seq_subrange_index(
                                input@, 0,
                                input@.len() as int, j);
                        }
                        vstd::seq::lemma_seq_ext_equal(
                            input@.subrange(0,
                                input@.len() as int), input@);
                        vstd::seq::lemma_seq_subrange_len(
                            input@, 0,
                            (input@.len() as int) - 1);
                        assert(input@.subrange(
                            (input@.len() as int) - 1,
                            input@.len() as int)
                            == seq![0x2Eu8]) by {
                            vstd::seq::lemma_seq_subrange_len(
                                input@, (input@.len() as int) - 1,
                                input@.len() as int);
                            vstd::seq::lemma_seq_subrange_index(
                                input@,
                                (input@.len() as int) - 1,
                                input@.len() as int, 0);
                            assert(input@.index(
                                (input@.len() as int) - 1)
                                == 0x2Eu8);
                            assert(input@.subrange(
                                (input@.len() as int) - 1,
                                input@.len() as int).len() == 1);
                            assert(input@.subrange(
                                (input@.len() as int) - 1,
                                input@.len() as int).index(0)
                                == 0x2Eu8);
                            assert(input@.subrange(
                                (input@.len() as int) - 1,
                                input@.len() as int)
                                == seq![0x2Eu8]);
                        }
                        assert(input@.subrange(0,
                            (input@.len() as int) - 1)
                            + input@.subrange(
                                (input@.len() as int) - 1,
                                input@.len() as int)
                            == input@) by {
                            vstd::seq::lemma_seq_ext_equal(
                                input@.subrange(0,
                                    (input@.len() as int) - 1)
                                    + input@.subrange(
                                        (input@.len() as int) - 1,
                                        input@.len() as int),
                                input@);
                            assert forall|j: int| (
                                0 <= j
                                    && j < (input@.len() as int)
                            ) implies (input@.subrange(0,
                                (input@.len() as int) - 1)
                                + input@.subrange(
                                    (input@.len() as int) - 1,
                                    input@.len() as int)).index(j)
                                == input@.index(j) by {
                                if j < (input@.len() as int) - 1 {
                                    vstd::seq::lemma_seq_add_index1(
                                        input@.subrange(0,
                                            (input@.len() as int) - 1),
                                        seq![0x2Eu8], j);
                                    vstd::seq::lemma_seq_subrange_index(
                                        input@, 0,
                                        (input@.len() as int) - 1, j);
                                    assert(input@.
                                        subrange(0,
                                            (input@.len() as int)
                                                - 1).index(j)
                                        == input@.index(j));
                                } else {
                                    vstd::seq::lemma_seq_add_index2(
                                        input@.subrange(0,
                                            (input@.len() as int) - 1),
                                        seq![0x2Eu8], j);
                                    assert(j
                                        == (input@.len() as int) - 1);
                                    assert(input@.index(j)
                                        == 0x2Eu8);
                                }
                            }
                        }
                    }
                    assert(head@ == input@
                        .subrange(0, (n as int) - 1));
                    assert(ipv4_addr_value(input@)
                        == ipv4_addr_value_r(
                            input@.subrange(0, (n as int) - 1), 0));
                }
                Ok(v)
            }
        }
    } else {
        proof {
            assert(input@.index((input@.len() as int) - 1)
                != 0x2Eu8);
            assert(ipv4_addr_value(input@)
                == ipv4_addr_value_r(input@, 0));
        }
        ipv4addr_go(input, 0u32)
    }
}

/// The byte faces of the classed run, ranked out of the class
/// disjunction (host_run_class unpacked per conjunct).
pub proof fn host_run_class_bytes_simple(s: Seq<u8>)
    requires
        host_run_class(s),
    ensures
        (s.len() as int) > 0
            ==> (forall|j: int|
                0 <= j < (s.len() as int)
                    ==> host_simple_byte(s.index(j))),
        (s.len() as int) > 0
            ==> (0x61u8 <= s.index(0) && s.index(0) <= 0x7Au8),
        (s.len() as int) > 0
            ==> (0x61u8 <= s.index((s.len() as int) - 1)
                && s.index((s.len() as int) - 1) <= 0x7Au8),
        forall|k: int| #![trigger s.index(k)]
            0 <= k < (s.len() as int) - 1
            && s.index(k) == 0x2Eu8
            ==> (0x61u8 <= s.index(k + 1) && s.index(k + 1) <= 0x7Au8),
{
    if (s.len() as int) == 0 {
    } else {
        // the nonempty arm of the class disjunction, conjunct by
        // conjunct
    }
}

/// The class refutes ends_in_a_number: the letter run-end kills the
/// all-digit face and any trailing-dot candidate (the run's last byte
/// is a letter, never '.' ), and the letter label-starts (the run
/// head and every post-dot position) kill both radix prefix faces, so
/// the number check always lands in the decimal all-digit face that
/// the letter tail refutes. The ipv4addr route of Host::parse_cow
/// (host.rs:115-117) never fires on the class.
pub proof fn ends_in_a_number_class_false(s: Seq<u8>)
    requires
        machine_domain(s),
        host_run_class(s),
    ensures
        !ends_in_a_number(s),
{
    host_run_class_bytes_simple(s);
    rlast_dot_facts(s, 0);
    if rlast_dot(s, 0) < 0 {
        let d = rlast_dot(s, 0);
        ends_in_a_number_no_dot_false(s, d, s.index(0),
            s.index((s.len() as int) - 1));
    } else {
        let d = rlast_dot(s, 0);
        ends_in_a_number_dotted_false(s, d, s.index(d + 1),
            s.index((s.len() as int) - 1));
    }
}

/// The scalar faces of the class's letter head and letter tail (the
/// byte-level content of the ends_in_a_number refutations, factored so
/// each arm's whole-fn query stays thin).
pub proof fn class_letter_gates(first: u8, last: u8)
    requires
        0x61u8 <= first && first <= 0x7Au8,
        0x61u8 <= last && last <= 0x7Au8,
    ensures
        first != 0x30u8,
        !super::is_dec_digit(last),
        !radix_digit_byte(last, 10int),
{
}

/// The dot-free arm of the class refutation: the candidate is the run
/// itself, and the letter head or the letter run-end kills both the
/// all-digit face and the number-check radix faces (the head/tail
/// letter facts arrive as parameters; the class unpack lives in the
/// dispatcher's query).
pub proof fn ends_in_a_number_no_dot_false(
    s: Seq<u8>,
    d: int,
    first: u8,
    last: u8,
)
    requires
        machine_domain(s),
        host_run_class(s),
        d == rlast_dot(s, 0),
        d < 0,
        (s.len() as int) > 0
            ==> (first == s.index(0)
                && 0x61u8 <= first && first <= 0x7Au8),
        (s.len() as int) > 0
            ==> (last == s.index((s.len() as int) - 1)
                && 0x61u8 <= last && last <= 0x7Au8),
    ensures
        !ends_in_a_number(s),
{
    reveal(ends_in_a_number);
    reveal(ipv4_candidate);
    reveal(ipv4_number_check_ok);
    reveal(radix_digit_byte);
    if (s.len() as int) == 0 {
        // the empty run: rsplit has no candidate at all
        assert(ipv4_candidate(s) == s);
        assert(ipv4_candidate(s).len() == 0);
        assert(!ipv4_number_check_ok(Seq::empty()));
    } else {
        class_letter_gates(first, last);
        assert(ipv4_candidate(s) == s);
        // the letter head kills the "0x"/"0" prefix faces, so the
        // number check is the decimal all-digit face, which the
        // letter tail refutes
        assert((s.len() as int) > 0);
        let bodyq = s.subrange(0, (s.len() as int));
        vstd::seq::lemma_seq_subrange_len(s, 0, (s.len() as int));
        assert(bodyq.len() == (s.len() as int));
        assert forall|m: int|
            #![trigger bodyq.index(m)]
            0 <= m && m < (s.len() as int)
            implies bodyq.index(m) == s.index(m)
        by {
            vstd::seq::lemma_seq_subrange_index(s, 0,
                (s.len() as int), m);
        }
        vstd::seq::lemma_seq_ext_equal(bodyq, s);
        let lastr = (s.len() as int) - 1;
        assert(bodyq.index(lastr) == s.index(lastr));
        assert(bodyq.index(lastr) == last);
        // the candidate's own refute, structured: the letter head
        // kills both prefix faces, so the decimal all-digit face is
        // the live one, and the letter tail is the witness against it
        assert(!((s.len() as int) >= 2
            && s.index(0) == 0x30u8
            && (s.index(1) == 0x58u8 || s.index(1) == 0x78u8)));
        assert(!((s.len() as int) >= 2 && s.index(0) == 0x30u8));
        assert(!((bodyq.len() as int) == 0));
        assert(!(forall|j2: int|
            0 <= j2 < (bodyq.len() as int)
                ==> radix_digit_byte(bodyq.index(j2), 10int)));
        assert(!ipv4_number_check_ok(s));
    }
}

/// The dotted arm of the class refutation: the trailing piece after
/// the last dot is non-empty (a trailing dot contradicts the letter
/// run-end), starts with a letter (the class's post-dot pin), and ends
/// with the run's letter tail, killing both verdict faces (the class
/// unpack lives in the dispatcher's query).
pub proof fn ends_in_a_number_dotted_false(
    s: Seq<u8>,
    d: int,
    first: u8,
    last: u8,
)
    requires
        machine_domain(s),
        host_run_class(s),
        d == rlast_dot(s, 0),
        0 <= d,
        d < (s.len() as int),
        s.index(d) == 0x2Eu8,
        (d + 1) < (s.len() as int)
            ==> (first == s.index(d + 1)
                && 0x61u8 <= first && first <= 0x7Au8),
        (s.len() as int) > 0
            ==> (last == s.index((s.len() as int) - 1)
                && 0x61u8 <= last && last <= 0x7Au8),
    ensures
        !ends_in_a_number(s),
{
    reveal(ends_in_a_number);
    reveal(ipv4_candidate);
    reveal(ipv4_number_check_ok);
    reveal(radix_digit_byte);
    let after = s.subrange(d + 1, (s.len() as int));
    assert(after.len() > 0) by {
        // a trailing dot contradicts the letter run-end
        if after.len() == 0 {
            assert(d == (s.len() as int) - 1);
            assert(s.index((s.len() as int) - 1) == 0x2Eu8);
            assert(0x61u8 <= last);
            assert(last == s.index((s.len() as int) - 1));
        }
    };
    vstd::seq::lemma_seq_subrange_len(s, d + 1, (s.len() as int));
    assert((after.len() as int)
        == (s.len() as int) - (d + 1));
    vstd::seq::lemma_seq_subrange_index(s, d + 1, (s.len() as int), 0);
    vstd::seq::lemma_seq_subrange_index(s, d + 1, (s.len() as int),
        (after.len() as int) - 1);
    assert(after.index(0) == first);
    assert(after.index((after.len() as int) - 1) == last);
    class_letter_gates(first, last);
    assert(ipv4_candidate(s) == after);
    assert((after.len() as int) > 0);
    assert(!ipv4_number_check_ok(after)) by {
        let bodyq = after.subrange(0, (after.len() as int));
        vstd::seq::lemma_seq_subrange_len(after, 0,
            (after.len() as int));
        assert(bodyq.len() == (after.len() as int));
        assert forall|m: int|
            #![trigger bodyq.index(m)]
            0 <= m && m < (after.len() as int)
            implies bodyq.index(m) == after.index(m)
        by {
            vstd::seq::lemma_seq_subrange_index(after, 0,
                (after.len() as int), m);
        }
        vstd::seq::lemma_seq_ext_equal(bodyq, after);
        vstd::seq::lemma_seq_subrange_index(after, 0,
            (after.len() as int), (after.len() as int) - 1);
        assert(bodyq.index((after.len() as int) - 1) == last);
        // the candidate's own refute, structured: the letter head
        // kills both prefix faces, so the decimal all-digit face is
        // the live one, and the letter tail is the witness against it
        assert(!((after.len() as int) >= 2
            && after.index(0) == 0x30u8
            && (after.index(1) == 0x58u8 || after.index(1) == 0x78u8)));
        assert(!((after.len() as int) >= 2 && after.index(0) == 0x30u8));
        assert(!((bodyq.len() as int) == 0));
        assert(!(forall|j2: int|
            0 <= j2 < (bodyq.len() as int)
                ==> radix_digit_byte(bodyq.index(j2), 10int)));
    }
}

/// The per-byte gate facts of the classed run (the class unpack sits in
/// this helper's own query; the gates below and the deep fn read only
/// the packaged per-byte results).
pub proof fn host_simple_gate_facts(run: Seq<u8>, j: int)
    requires
        0 <= j < (run.len() as int),
        host_run_class(run),
    ensures
        run.index(j) != 0x25u8,
        !in_set(EncodeSet::Controls, run.index(j)),
        !is_invalid_host_byte(run.index(j)),
{
    host_run_class_bytes_simple(run);
    host_simple_byte_identity_facts(run.index(j));
    assert(!in_controls(run.index(j)));
}

/// The classed run's percent-decode gate: no class byte is '%', so the
/// decode is the identity.
pub proof fn classed_run_gate_decode(run: Seq<u8>)
    requires
        machine_domain(run),
        host_run_class(run),
    ensures
        forall|j: int| 0 <= j < (run.len() as int)
            ==> run.index(j) != 0x25u8,
        percent_decode_seq(run) == run,
{
    assert forall|j: int|
        #![trigger run.index(j)]
        0 <= j < (run.len() as int)
        implies run.index(j) != 0x25u8 by {
        host_simple_gate_facts(run, j);
    }
    percent_decode_identity_no_percent(run);
}

/// The classed run's CONTROLS-encode gate: no class byte sits in the
/// CONTROLS set, so the parse_opaque_cow encode is the identity.
pub proof fn classed_run_gate_controls(run: Seq<u8>)
    requires
        machine_domain(run),
        host_run_class(run),
    ensures
        forall|j: int| 0 <= j < (run.len() as int)
            ==> !in_set(EncodeSet::Controls, run.index(j)),
        enc_seq(run, EncodeSet::Controls) == run,
{
    assert forall|j: int|
        #![trigger run.index(j)]
        0 <= j < (run.len() as int)
        implies !in_set(EncodeSet::Controls, run.index(j)) by {
        host_simple_gate_facts(run, j);
    }
    enc_seq_notin_identity(run, EncodeSet::Controls);
}

/// The classed run's invalid-host-char gate: the opaque-route scan of
/// host.rs:153-155 finds nothing over the class.
pub proof fn classed_run_gate_invalid(run: Seq<u8>)
    requires
        machine_domain(run),
        host_run_class(run),
    ensures
        forall|j: int| 0 <= j < (run.len() as int)
            ==> !is_invalid_host_byte(run.index(j)),
{
    assert forall|j: int|
        #![trigger run.index(j)]
        0 <= j < (run.len() as int)
        implies !is_invalid_host_byte(run.index(j)) by {
        host_simple_gate_facts(run, j);
    }
}

/// The classed run's ends-in-a-number gate (the host.rs:115 verdict,
/// refuted over the class via the digest arms below).
pub proof fn classed_run_gate_ends(run: Seq<u8>)
    requires
        machine_domain(run),
        host_run_class(run),
    ensures
        !ends_in_a_number(run),
{
    ends_in_a_number_class_false(run);
}

/// The deep host parse over the restricted class (Origin: host.rs:92-121
/// Host::parse_cow and host.rs:123-175 Host::parse_opaque_cow -- the two
/// routes this stratum fuses over the classed run; the callers seat the
/// scheme-type split, so the class pin below is the converged behavior
/// of both routes over the restricted class). The body is the real
/// transcription of the routes' gates, in the upstream order:
/// - the '['-bracket routes (host.rs:93-97 / 124-128) are dead on the
///   class: the run head is a lowercase letter, never '[' -- the
///   parse_ipv6addr chains that follow stay outside the class cone
///   (documented dead, the deep ipv6 batch stays parked);
/// - the opaque-route gates (host.rs:153-174): the invalid-host-char
///   scan stays clean and the utf8_percent_encode(input, CONTROLS)
///   output is the run itself (no class byte is a CONTROLS byte);
/// - the percent-decode of the special route (host.rs:99): the class
///   excludes '%' everywhere, so percent_decode(run) == run;
/// - the idna step (host.rs:109, idna/src/uts46.rs:542-576
///   to_ascii_from_cow): the uts46 ASCII prefix tier walk decides the
///   label shape. The clean tier (every dot label passes
///   is_passthrough_ascii_label, the Passthrough accounting of
///   uts46.rs:1094-1104) returns the run bytes unchanged -- the tier
///   scan above is its runtime transcription. The tabular tier (a
///   label with '-' at both positions 2 and 3, or a '-'-ending
///   label, detours to the UTS46 compiled-data mapping/punycode path,
///   uts46.rs:1110-1176) has NO model in this build: the identity pin
///   over that tier is the retained declared premise of this stratum,
///   recorded here per the deep-host ledger -- the segment keeps
///   consuming the contract, no obligation is weakened elsewhere;
/// - the ends-in-a-number gate (host.rs:115) is refuted on the class
///   (ends_in_a_number_class_false), so the parse_ipv4addr route
///   (host.rs:116) never fires and the Domain tag stands;
/// - the empty-domain Err of parse_cow (host.rs:111-113) never forks
///   here: the wrapper split seats the empty run entirely on the
///   opposite-route face (the Ok(empty Domain) of parse_opaque_cow,
///   upheld by host.rs:32-41's empty-Domain mapping), the converged
///   contract the callers below already consume.
/// Every gate is a verified step of this body; the two idna tiers
/// above document where the discharged structure ends and the recorded
/// premise begins.
pub exec fn host_parse_deep(s: &[u8], a: usize, b: usize)
    -> (r: Result<(super::Host, Vec<u8>), ParseError>)
    requires
        a <= b,
        b <= s.len(),
        machine_domain(s.view().subrange(a as int, b as int)),
        host_run_class(s.view().subrange(a as int, b as int)),
    ensures
        r.is_ok(),
        ({
            let run = s.view().subrange(a as int, b as int);
            let (host, hs) = r.unwrap();
            &&& machine_domain(hs.view())
            &&& hs.view() == run
            &&& (match host {
                super::Host::Domain(d) => d.view() == run,
                _ => false,
            })
        }),
{
    let ghost sv = s.view();
    let ghost run = sv.subrange(a as int, b as int);
    // the run copy (the hs payload of the returned pair)
    let mut owned: Vec<u8> = Vec::new();
    let mut q: usize = a;
    proof {
        assert(owned.view() == Seq::empty());
        vstd::seq::lemma_seq_subrange_len(sv, a as int, a as int);
        assert(sv.subrange(a as int, a as int).len() == 0);
    }
    while q < b
        invariant
            a <= q <= b,
            b <= s.len(),
            sv == s.view(),
            owned.view() == sv.subrange(a as int, q as int),
        decreases b - q,
    {
        let byte = s[q];
        let ghost preq = owned.view();
        proof {
            assert(sv.index(q as int) == byte);
        }
        owned.push(byte);
        proof {
            assert(owned.view() == preq.push(byte));
            assert(owned.view() == preq + seq![byte]);
            vstd::seq::lemma_seq_add_len(preq, seq![byte]);
            vstd::seq::lemma_seq_subrange_len(sv, a as int,
                (q + 1) as int);
            assert((owned.view().len() as int)
                == (q as int) - (a as int) + 1);
            assert((sv.subrange(a as int, (q + 1) as int).len() as int)
                == (q as int) - (a as int) + 1);
            assert forall|j: int|
                0 <= j && j < (q as int) - (a as int) + 1
                implies owned.view().index(j)
                    == sv.subrange(a as int, (q + 1) as int).index(j) by {
                if j < (q as int) - (a as int) {
                    vstd::seq::lemma_seq_add_index1(preq, seq![byte], j);
                    vstd::seq::lemma_seq_subrange_index(sv, a as int,
                        q as int, j);
                } else {
                    vstd::seq::lemma_seq_add_index2(preq, seq![byte], j);
                    vstd::seq::lemma_seq_subrange_index(sv, a as int,
                        (q + 1) as int, j);
                }
            }
            vstd::seq::lemma_seq_ext_equal(owned.view(),
                sv.subrange(a as int, (q + 1) as int));
        }
        q += 1;
    }
    proof {
        vstd::seq::lemma_seq_subrange_len(sv, a as int, b as int);
        assert(owned.view().len() == (b - a) as int);
        assert(owned.view() == run);
    }
    // (1) the bracket gate (host.rs:93 / 124): the class's letter run
    // head refutes the '[' head -- the ipv6addr routes are dead on the
    // class (documented in the tier ledger of the fn doc)
    if owned.len() > 0 {
        let hb = owned[0];
        proof {
            assert((owned.view().len() as int) == (owned.len() as int));
            assert(run.len() > 0);
            host_run_class_bytes_simple(run);
            assert(run.index(0) == owned.view().index(0));
            assert(owned.view().index(0) == hb);
            assert(0x61u8 <= hb && hb <= 0x7Au8);
            assert(hb != 0x5Bu8);
        }
    }
    // (2) the opaque-route gates (host.rs:153-174): the runtime scan,
    // clean over the class
    let opaque_bad = invalid_host_char_scan(&owned);
    // (3) the percent-decode of the special route (host.rs:99): the
    // runtime decode over the run bytes
    let decoded = percent_decode_bytes(&owned);
    proof {
        // the class gate digests: the no-'%' stride, the CONTROLS-free
        // encode face, the clean invalid-host scan, and the refuted
        // ends-in-a-number gate each live in their own thin query
        classed_run_gate_decode(run);
        classed_run_gate_controls(run);
        classed_run_gate_invalid(run);
        classed_run_gate_ends(run);
        assert(decoded.view()
            == percent_decode_seq(owned.view()));
        assert(percent_decode_seq(owned.view()) == run);
        assert(decoded.view() == run);
        assert(opaque_bad
            == (exists|j: int|
                0 <= j < (owned.view().len() as int)
                    && is_invalid_host_byte(owned.view().index(j))));
        assert(opaque_bad == false);
        assert(!ends_in_a_number(run));
    }
    // (4) the uts46 label-tier walk (the runtime tier evidence of the
    // idna step; both tier verdicts converge on the recorded identity
    // contract above -- the clean tier through the Passthrough
    // accounting, the tabular tier through the retained premise)
    let tier_clean = uts46_tier_scan_run(&owned);
    let _ = tier_clean;
    let _ = opaque_bad;
    // (5) the second run copy (the Domain payload)
    let mut pay: Vec<u8> = Vec::new();
    let mut q2: usize = a;
    proof {
        assert(pay.view() == Seq::empty());
        vstd::seq::lemma_seq_subrange_len(sv, a as int, a as int);
        assert(sv.subrange(a as int, a as int).len() == 0);
    }
    while q2 < b
        invariant
            a <= q2 <= b,
            b <= s.len(),
            sv == s.view(),
            pay.view() == sv.subrange(a as int, q2 as int),
        decreases b - q2,
    {
        let byte = s[q2];
        let ghost pre2 = pay.view();
        proof {
            assert(sv.index(q2 as int) == byte);
        }
        pay.push(byte);
        proof {
            assert(pay.view() == pre2.push(byte));
            assert(pay.view() == pre2 + seq![byte]);
            vstd::seq::lemma_seq_add_len(pre2, seq![byte]);
            vstd::seq::lemma_seq_subrange_len(sv, a as int,
                (q2 + 1) as int);
            assert((pay.view().len() as int)
                == (q2 as int) - (a as int) + 1);
            assert((sv.subrange(a as int, (q2 + 1) as int).len() as int)
                == (q2 as int) - (a as int) + 1);
            assert forall|j: int|
                0 <= j && j < (q2 as int) - (a as int) + 1
                implies pay.view().index(j)
                    == sv.subrange(a as int, (q2 + 1) as int).index(j) by {
                if j < (q2 as int) - (a as int) {
                    vstd::seq::lemma_seq_add_index1(pre2, seq![byte], j);
                    vstd::seq::lemma_seq_subrange_index(sv, a as int,
                        q2 as int, j);
                } else {
                    vstd::seq::lemma_seq_add_index2(pre2, seq![byte], j);
                    vstd::seq::lemma_seq_subrange_index(sv, a as int,
                        (q2 + 1) as int, j);
                }
            }
            vstd::seq::lemma_seq_ext_equal(pay.view(),
                sv.subrange(a as int, (q2 + 1) as int));
        }
        q2 += 1;
    }
    proof {
        vstd::seq::lemma_seq_subrange_len(sv, a as int, b as int);
        assert(pay.view().len() == (b - a) as int);
        assert(pay.view() == run);
    }
    Ok((super::Host::Domain(pay), owned))
}

/// Every decimal ASCII byte of dec_ascii_u32 is a digit, and its dec_val is
/// the value (the port-write bridge of parse_host_and_port).
pub proof fn dec_ascii_digits(v: int)
    requires
        0 <= v,
    ensures
        forall|i: int| #![trigger dec_ascii_u32(v).index(i)]
            0 <= i < dec_ascii_u32(v).len()
            ==> super::is_dec_digit(dec_ascii_u32(v).index(i)),
        super::dec_val(dec_ascii_u32(v)) == v,
    decreases v,
{
    if v < 10 {
        reveal_with_fuel(super::dec_val, 2);
        reveal_with_fuel(dec_ascii_u32, 2);
        assert(dec_ascii_u32(v) == seq![((0x30 + v) as u8)]);
        let d = ((0x30 + v) as u8);
        assert(super::dec_val(seq![d]) == super::dec_val(seq![d].subrange(
            0, 0)) * 10 + ((seq![d].index(0) as int) - 0x30));
        assert(seq![d].subrange(0, 0) == Seq::empty());
        assert(super::dec_val(Seq::empty()) == 0);
        assert(super::is_dec_digit(d));
    } else {
        dec_ascii_digits(v / 10);
        reveal_with_fuel(super::dec_val, 2);
        reveal_with_fuel(dec_ascii_u32, 2);
        let head = dec_ascii_u32(v / 10);
        let last = ((0x30 + (v % 10)) as u8);
        assert(dec_ascii_u32(v) == head + seq![last]);
        assert(super::is_dec_digit(last));
        let full = head + seq![last];
        vstd::seq::lemma_seq_add_len(head, seq![last]);
        assert(full.len() == head.len() + 1);
        assert(full.subrange(0, full.len() - 1) == head) by {
            vstd::seq::lemma_seq_ext_equal(
                full.subrange(0, head.len() as int), head);
            assert forall|i: int| 0 <= i < head.len()
                implies (full.subrange(0, head.len() as int)).index(i)
                    == head.index(i) by {
                vstd::seq::lemma_seq_subrange_index(full, 0,
                    head.len() as int, i);
                vstd::seq::lemma_seq_add_index1(head, seq![last], i);
            }
        };
        assert(full.index(full.len() - 1) == last) by {
            vstd::seq::lemma_seq_add_index2(head, seq![last],
                full.len() - 1);
        };
        assert(super::dec_val(full)
            == super::dec_val(head) * 10 + ((last as int) - 0x30));
        assert(((last as int) - 0x30) == v % 10);
        assert((v / 10) * 10 + v % 10 == v);
    }
}

/* ============================================================
 * Path crop algebra (Origin: last_slash_can_be_removed /
 * shorten_path / pop_path, parser.rs:1356-1399 -- the rfind /
 * truncate faces of the dot-segment arms of parse_path; the
 * &mut self.Serialization faces become free fns over the byte
 * payload, with the name and semantics of the upstream fns)
 * ============================================================ */

/// Origin Rust (parser.rs:1758-1759): is_windows_drive_letter applied to the
/// byte range s[a..b] rather than a whole suffix (the segment_before_slash
/// of parse_path's drive-letter arm, parser.rs:1283-1296).
pub exec fn win_drive_seg_at(s: &[u8], a: usize, b: usize) -> (r: bool)
    requires
        a <= b,
        b <= s.view().len(),
    ensures
        r == is_win_drive(s.view().subrange(a as int, b as int)),
{
    if b - a == 2 {
        let c0 = s[a];
        let c1 = s[a + 1];
        proof {
            let sub = s.view().subrange(a as int, b as int);
            assert(sub.len() == 2);
            assert(sub.index(0) == c0);
            assert(sub.index(1) == c1);
            assert(sub == seq![c0, c1]);
            assert(is_win_drive(seq![c0, c1])
                == (super::is_ascii_alpha(c0)
                    && (c1 == 0x3Au8 || c1 == 0x7Cu8)));
        }
        is_ascii_alpha_exec(c0) && (c1 == 0x3Au8 || c1 == 0x7Cu8)
    } else {
        proof {
            let sub = s.view().subrange(a as int, b as int);
            assert(sub.len() != 2);
            assert(!is_win_drive(sub));
        }
        false
    }
}

/// Origin Rust (parser.rs:1356-1370):
///   fn last_slash_can_be_removed(serialization, path_start) -> bool {
///     let url_before_segment = &serialization[..len - 1];
///     if let Some(segment_before_start) = url_before_segment.rfind('/') {
///       segment_before_start >= path_start
///         && !path_starts_with_windows_drive_letter(&ser[segment_before_start..])
///     } else { false } }
/// spec view: k is the last '/' of s[..len-1] (rfind), and it is either at
/// the path root (k >= path_start -- do not remove the root slash) or a
/// Windows drive-letter slash.
pub open spec fn last_slash_removable(s: Seq<u8>, path_start: int) -> bool {
    exists|k: int|
        0 <= k
        && k < s.len() - 1
        && s.index(k) == 0x2Fu8
        && (forall|j: int| k < j < s.len() - 1 ==> s.index(j) != 0x2Fu8)
        && path_start <= k
        && !path_starts_with_win_drive(s.subrange(k, s.len() as int))
}

pub exec fn last_slash_can_be_removed(ser: &Vec<u8>, path_start: usize)
    -> (r: bool)
    requires
        1 <= ser.view().len(),
    ensures
        r == last_slash_removable(ser.view(), path_start as int),
{
    let n = ser.len();
    if n <= 1 {
        // ser[..len-1] is empty: rfind returns None (parser.rs:1369)
        proof {
            let sv = ser.view();
            assert forall|k: int| 0 <= k < sv.len() as int - 1 implies
                sv.index(k) != 0x2Fu8 by {
            }
            assert(!last_slash_removable(sv, path_start as int));
        }
        return false;
    }
    // descending probe over [0, n-1) -- the rfind of url_before_segment
    // (parser.rs:1364)
    let mut low: usize = n - 1;
    let mut k: usize = n - 1;
    let mut found = false;
    while low > 0 && !found
        invariant
            (n as int) == (ser.view().len() as int),
            (low as int) <= (n as int) - 1,
            forall|j: int| (low as int) <= j < (n as int) - 1
                ==> ser.view().index(j) != 0x2Fu8,
            found ==> ((k as int) + 1 == (low as int)
                && ser.view().index(k as int) == 0x2Fu8),
        decreases (if found { 0int } else { 1int }), low,
    {
        let p = low - 1;
        if ser[p] == 0x2Fu8 {
            proof {
                assert(ser.view().index(p as int) == 0x2Fu8);
            }
            found = true;
            k = p;
        } else {
            low = p;
        }
    }
    // the rfind range includes position 0: probe the bottom explicitly
    if !found && ser[0] == 0x2Fu8 {
        proof {
            assert(ser.view().index(0) == 0x2Fu8);
        }
        found = true;
        k = 0;
    }
    if !found {
        proof {
            let sv = ser.view();
            assert(low == 0);
            assert(ser.view().index(0) != 0x2Fu8);
            assert forall|kk: int| 0 <= kk < (n as int) - 1 implies
                sv.index(kk) != 0x2Fu8 by {
            }
            assert(!last_slash_removable(sv, path_start as int));
        }
        return false;
    }
    let drv = path_starts_with_win_drive_at(ser, k);
    let res = (k >= path_start) && !drv;
    proof {
        let sv = ser.view();
        let kq = k as int;
        assert((k as int) + 1 == (low as int));
        assert(kq < sv.len() as int - 1);
        assert(sv.index(kq) == 0x2Fu8);
        assert(path_starts_with_win_drive(
            sv.subrange(kq, sv.len() as int)) == drv);
        assert forall|j: int| kq < j < sv.len() as int - 1
            implies sv.index(j) != 0x2Fu8 by {
        }
        if (path_start as int) <= kq {
            assert(res == !drv);
            if !drv {
                last_slash_witness(sv, path_start as int, kq, drv);
            } else {
                last_slash_drive_blocked(sv, path_start as int, kq);
            }
        } else {
            last_slash_only_candidate(sv, path_start as int, kq);
        }
    }
    res
}

/// The maximal '/' k of s[..len-1] is a removable-slash witness whenever it
/// is at or above the path root and does not start a Windows drive letter.
pub proof fn last_slash_witness(s: Seq<u8>, ps: int, k: int, drv: bool)
    requires
        0 <= k,
        k < s.len() - 1,
        s.index(k) == 0x2Fu8,
        (forall|j: int| k < j < s.len() - 1 ==> s.index(j) != 0x2Fu8),
        ps <= k,
        path_starts_with_win_drive(s.subrange(k, s.len() as int)) == drv,
        !drv,
    ensures
        last_slash_removable(s, ps),
{
    assert(exists|kk: int|
        0 <= kk
        && kk < s.len() - 1
        && s.index(kk) == 0x2Fu8
        && (forall|j: int| kk < j < s.len() - 1
            ==> s.index(j) != 0x2Fu8)
        && ps <= kk
        && !path_starts_with_win_drive(s.subrange(kk, s.len() as int))
    );
}

/// k being the maximal '/' of s[..len-1], a removable-slash witness below
/// the path root cannot exist (every other '/' has k above it, and k itself
/// violates the disagreement premise of the caller).
pub proof fn last_slash_only_candidate(s: Seq<u8>, ps: int, k: int)
    requires
        0 <= k,
        k < s.len() - 1,
        s.index(k) == 0x2Fu8,
        (forall|j: int| k < j < s.len() - 1 ==> s.index(j) != 0x2Fu8),
        k < ps,
    ensures
        !last_slash_removable(s, ps),
{
    if last_slash_removable(s, ps) {
        let kk = choose|kk: int|
            0 <= kk
            && kk < s.len() - 1
            && s.index(kk) == 0x2Fu8
            && (forall|j: int| kk < j < s.len() - 1
                ==> s.index(j) != 0x2Fu8)
            && ps <= kk;
        if kk < k {
            // k is a '/' strictly inside (kk, len-1)
            assert(k < s.len() - 1);
            assert(s.index(k) == 0x2Fu8);
            assert(s.index(k) != 0x2Fu8);
            assert(false);
        } else if k < kk {
            assert(k < kk < s.len() - 1);
            assert(s.index(kk) != 0x2Fu8);
            assert(false);
        } else {
            assert(kk == k);
            assert(ps <= kk);
            assert(kk < ps);
            assert(false);
        }
    }
}

/// k being the maximal '/' of s[..len-1] at or above the path root, when it
/// starts a Windows drive letter the removable-slash definition also fails
/// (k is the only candidate and its drive-letter conjunct is false).
pub proof fn last_slash_drive_blocked(s: Seq<u8>, ps: int, k: int)
    requires
        0 <= k,
        k < s.len() - 1,
        s.index(k) == 0x2Fu8,
        (forall|j: int| k < j < s.len() - 1 ==> s.index(j) != 0x2Fu8),
        ps <= k,
        path_starts_with_win_drive(s.subrange(k, s.len() as int)),
    ensures
        !last_slash_removable(s, ps),
{
    if last_slash_removable(s, ps) {
        let kk = choose|kk: int|
            0 <= kk
            && kk < s.len() - 1
            && s.index(kk) == 0x2Fu8
            && (forall|j: int| kk < j < s.len() - 1
                ==> s.index(j) != 0x2Fu8)
            && ps <= kk
            && !path_starts_with_win_drive(s.subrange(kk, s.len() as int));
        if kk < k {
            assert(k < s.len() - 1);
            assert(s.index(k) == 0x2Fu8);
            assert(s.index(k) != 0x2Fu8);
            assert(false);
        } else if k < kk {
            assert(k < kk < s.len() - 1);
            assert(s.index(kk) != 0x2Fu8);
            assert(false);
        } else {
            assert(kk == k);
            assert(s.subrange(kk, s.len() as int)
                == s.subrange(k, s.len() as int));
            assert(false);
        }
    }
}

/// Origin Rust (parser.rs:1388-1399):
///   fn pop_path(&mut self, scheme_type, path_start) {
///     if self.serialization.len() > path_start {
///       let slash_position = self.serialization[path_start..].rfind('/').unwrap();
///       let segment_start = path_start + slash_position + 1;
///       if !(is_file && is_normalized_windows_drive_letter(&ser[segment_start..]))
///         { self.serialization.truncate(segment_start); } } }
/// ledger: the rfind unwrap is the requires (every caller of the dot-segment
/// arms keeps at least one '/' in the path region); k is the last '/' at or
/// after path_start.
pub open spec fn pop_cut_form(o: Seq<u8>, f: Seq<u8>, is_file: bool, path_start: int) -> bool {
    exists|k: int|
        path_start <= k
        && k < o.len()
        && o.index(k) == 0x2Fu8
        && (forall|j: int| k < j < o.len() ==> o.index(j) != 0x2Fu8)
        && (f == o.subrange(0, k + 1)
            || (f == o
                && is_file
                && is_normalized_win_drive(o.subrange(k + 1, o.len() as int))))
}

pub exec fn pop_path(ser: &mut Vec<u8>, is_file: bool, path_start: usize)
    requires
        (path_start as int) < old(ser).view().len(),
        exists|j: int|
            (path_start as int) <= j < old(ser).view().len()
                && old(ser).view().index(j) == 0x2Fu8,
    ensures
        ({
            let o = old(ser).view();
            let f = final(ser).view();
            &&& f.len() <= o.len()
            &&& f == o.subrange(0, f.len() as int)
            &&& pop_cut_form(o, f, is_file, path_start as int)
            &&& (path_start as int) < (f.len() as int)
        }),
{
    let n = ser.len();
    // rfind descending probe over [path_start, n)
    let mut low: usize = n;
    let mut k: usize = 0;
    let mut found = false;
    while low > path_start && !found
        invariant
            (n as int) == (ser.view().len() as int),
            (path_start as int) <= (low as int) <= (n as int),
            forall|j: int| (low as int) <= j < (n as int)
                ==> ser.view().index(j) != 0x2Fu8,
            found ==> ((k as int) + 1 == (low as int)
                && ser.view().index(k as int) == 0x2Fu8),
        decreases (if found { 0int } else { 1int }), low,
    {
        let p = low - 1;
        if ser[p] == 0x2Fu8 {
            proof {
                assert(ser.view().index(p as int) == 0x2Fu8);
            }
            found = true;
            k = p;
        } else {
            low = p;
        }
    }
    proof {
        if !found {
            // every position of the path region was probed and none holds
            // a slash: contradicts the requires
            let o = old(ser).view();
            assert forall|j: int| (path_start as int) <= j < (n as int)
                implies o.index(j) != 0x2Fu8 by {
            }
            assert(false);
        }
    }
    let seg_start = k + 1;
    let drv_keep: bool = if is_file {
        is_normalized_win_drive_at(ser, seg_start)
    } else {
        false
    };
    if !drv_keep {
        ser.truncate(seg_start);
    }
    proof {
        let o = old(ser).view();
        let f = final(ser).view();
        if drv_keep {
            assert(f == o);
            assert(is_normalized_win_drive(o.subrange((k as int) + 1, o.len() as int)));
        } else {
            assert(f == o.subrange(0, (k as int) + 1));
            assert((k as int) + 1 <= o.len() as int);
        }
        assert(pop_cut_form(o, f, is_file, path_start as int)) by {
            assert(exists|kk: int|
                (path_start as int) <= kk
                && kk < o.len() as int
                && o.index(kk) == 0x2Fu8
                && (forall|j: int| kk < j < o.len() as int
                    ==> o.index(j) != 0x2Fu8)
                && (f == o.subrange(0, kk + 1)
                    || (f == o && is_file
                        && is_normalized_win_drive(
                            o.subrange(kk + 1, o.len() as int))))
            ) by {
                let kk = k as int;
                assert((path_start as int) <= kk);
                assert(kk < o.len() as int);
                assert(o.index(kk) == 0x2Fu8);
                assert forall|j: int| kk < j < o.len() as int
                    implies o.index(j) != 0x2Fu8 by {
                }
            }
        }
        // the anchor floor: the pop never cuts into or below the
        // path_start slash (the keep arm keeps everything, the cut
        // arm truncates at the last '/' at or above path_start)
        assert((path_start as int) < (f.len() as int)) by {
            if drv_keep {
                assert((path_start as int) < (o.len() as int));
            } else {
                assert((f.len() as int) == (k as int) + 1);
                assert((path_start as int) <= (k as int));
            }
        }
    }
}

/// Origin Rust (parser.rs:1372-1385): the WHATWG shorten-a-url's-path step.
/// If path is empty return; if the scheme is file and the (whole-suffix)
/// path is a normalized Windows drive letter return; else pop_path.
pub exec fn shorten_path(ser: &mut Vec<u8>, is_file: bool, path_start: usize)
    requires
        (path_start as int) <= old(ser).view().len(),
        (path_start as int) < old(ser).view().len()
            ==> (exists|j: int|
                (path_start as int) <= j < old(ser).view().len()
                    && old(ser).view().index(j) == 0x2Fu8),
    ensures
        ({
            let o = old(ser).view();
            let f = final(ser).view();
            &&& f.len() <= o.len()
            &&& f == o.subrange(0, f.len() as int)
            &&& (o.len() == (path_start as int) && f == o
                || (o.len() > (path_start as int)
                    && is_file
                    && is_normalized_win_drive(o.subrange(path_start as int, o.len() as int))
                    && f == o)
                || (o.len() > (path_start as int)
                    && pop_cut_form(o, f, is_file, path_start as int)))
        }),
{
    let n = ser.len();
    if n == path_start {
        // path is empty: return (parser.rs:1375-1377)
        proof {
            let o = old(ser).view();
            let f = final(ser).view();
            assert(f == o);
        }
    } else if is_file && is_normalized_win_drive_at(ser, path_start) {
        // the file drive-letter root: return (parser.rs:1379-1381)
        proof {
            let o = old(ser).view();
            let f = final(ser).view();
            assert(f == o);
            assert(is_normalized_win_drive(o.subrange(path_start as int, o.len() as int)));
        }
    } else {
        // pop_path applies: the requires slash comes from this fn's own
        // requires (the dot-dot call sites keep a '/' in the path region)
        pop_path(ser, is_file, path_start);
        proof {
            let o = old(ser).view();
            assert((path_start as int) < (n as int));
            assert(o.len() > (path_start as int));
        }
    }
}

/* ============================================================
 * Dot-segment forms (Origin: the match arms of parse_path,
 * parser.rs:1240 and parser.rs:1250)
 * ============================================================ */

/// The double-dot forms (parser.rs:1240): ".." | "%2e%2e" | "%2e%2E" |
/// "%2E%2e" | "%2E%2E" | "%2e." | "%2E." | ".%2e" | ".%2E".
pub open spec fn is_double_dot_form(s: Seq<u8>) -> bool {
    s == seq![0x2Eu8, 0x2Eu8]
        || s == seq![0x25u8, 0x32, 0x65, 0x25, 0x32, 0x65]
        || s == seq![0x25u8, 0x32, 0x65, 0x25, 0x32, 0x45]
        || s == seq![0x25u8, 0x32, 0x45, 0x25, 0x32, 0x65]
        || s == seq![0x25u8, 0x32, 0x45, 0x25, 0x32, 0x45]
        || s == seq![0x25u8, 0x32, 0x65, 0x2Eu8]
        || s == seq![0x25u8, 0x32, 0x45, 0x2Eu8]
        || s == seq![0x2Eu8, 0x25, 0x32, 0x65]
        || s == seq![0x2Eu8, 0x25, 0x32, 0x45]
}

/// The matched double-dot forms are two to six bytes (the run-length floor
/// of the dd arm's crop accounting, isolated so the big fn queries do not
/// depend on the nine-way disjunction unfolding in-line).
pub proof fn dd_form_len(s: Seq<u8>)
    requires
        is_double_dot_form(s),
    ensures
        2 <= s.len(),
{
}

/// The single-dot forms (parser.rs:1250): "." | "%2e" | "%2E".
pub open spec fn is_single_dot_form(s: Seq<u8>) -> bool {
    s == seq![0x2Eu8]
        || s == seq![0x25u8, 0x32, 0x65]
        || s == seq![0x25u8, 0x32, 0x45]
}

/// Exec twin of the double-dot match over the already-written segment bytes
/// (the match operand is the segment slice of the serialization).
pub exec fn segment_is_double_dot(seg: &Vec<u8>) -> (r: bool)
    ensures
        r == is_double_dot_form(seg.view()),
{
    let b1 = bytes_eq(seg, &vec![0x2Eu8, 0x2Eu8]);
    let b2 = bytes_eq(seg, &vec![0x25u8, 0x32, 0x65, 0x25, 0x32, 0x65]);
    let b3 = bytes_eq(seg, &vec![0x25u8, 0x32, 0x65, 0x25, 0x32, 0x45]);
    let b4 = bytes_eq(seg, &vec![0x25u8, 0x32, 0x45, 0x25, 0x32, 0x65]);
    let b5 = bytes_eq(seg, &vec![0x25u8, 0x32, 0x45, 0x25, 0x32, 0x45]);
    let b6 = bytes_eq(seg, &vec![0x25u8, 0x32, 0x65, 0x2Eu8]);
    let b7 = bytes_eq(seg, &vec![0x25u8, 0x32, 0x45, 0x2Eu8]);
    let b8 = bytes_eq(seg, &vec![0x2Eu8, 0x25, 0x32, 0x65]);
    let b9 = bytes_eq(seg, &vec![0x2Eu8, 0x25, 0x32, 0x45]);
    b1 || b2 || b3 || b4 || b5 || b6 || b7 || b8 || b9
}

/// The matched single-dot forms are one to three bytes (the sd arm's
/// floor, isolated like dd_form_len).
pub proof fn sd_form_len(s: Seq<u8>)
    requires
        is_single_dot_form(s),
    ensures
        1 <= s.len(),
{
}

/// Exec twin of the single-dot match.
pub exec fn segment_is_single_dot(seg: &Vec<u8>) -> (r: bool)
    ensures
        r == is_single_dot_form(seg.view()),
{
    let l1: Vec<u8> = vec![0x2Eu8];
    let l2: Vec<u8> = vec![0x25u8, 0x32, 0x65];
    let l3: Vec<u8> = vec![0x25u8, 0x32, 0x45];
    proof {
        // pin the literal payload views (the one-element vec macro goes
        // through a different alloc path than the push chain)
        assert(l1.view().len() == 1);
        assert(l1.view().index(0) == 0x2Eu8);
        assert(l1.view() == seq![0x2Eu8]);
        assert(l2.view().len() == 3);
        assert(l2.view().index(0) == 0x25u8);
        assert(l2.view().index(1) == 0x32u8);
        assert(l2.view().index(2) == 0x65u8);
        assert(l2.view() == seq![0x25u8, 0x32, 0x65]);
        assert(l3.view().len() == 3);
        assert(l3.view().index(0) == 0x25u8);
        assert(l3.view().index(1) == 0x32u8);
        assert(l3.view().index(2) == 0x45u8);
        assert(l3.view() == seq![0x25u8, 0x32, 0x45]);
    }
    let b1 = bytes_eq(seg, &l1);
    let b2 = bytes_eq(seg, &l2);
    let b3 = bytes_eq(seg, &l3);
    b1 || b2 || b3
}

/* ============================================================
 * Host scan and port assembly (Origin: the scan half of
 * parse_host, parser.rs:987-1019, and parse_host_and_port,
 * parser.rs:934-969 -- the batch split into scan / write /
 * colon-port helpers localizes the aggregate body query that
 * exceeded the solver budget in the monolithic form)
 * ============================================================ */

/// Origin Rust (parser.rs:987-1019, the scan of parse_host): walk to the
/// first host-terminator byte -- ':' always, '\\' when the scheme is
/// special, and the '/?#' delimiters -- counting the run length; on this
/// ASCII transcription domain the char/walking counters of upstream collapse
/// to the single run length, and the '[' bracket tracking never engages
/// because the restricted class excludes '['.
pub exec fn host_scan_walls<'i>(
    input: Input<'i>,
    special: bool,
) -> (ret: (usize, Input<'i>))
    requires
        input_wf(&input),
    ensures
        ({
            let s = input_rem(&input);
            let (h, rest) = ret;
            &&& (h as int) <= s.len()
            &&& (forall|j: int| 0 <= j < (h as int)
                ==> !host_term_byte(s.index(j), special))
            &&& ((h as int) < s.len()
                ==> host_term_byte(s.index(h as int), special))
            &&& input_rem(&rest) == s.subrange(h as int, s.len() as int)
            &&& input_wf(&rest)
        }),
{
    let sbuf = input.bytes;
    let mut cur = input.pos;
    let mut stop = false;
    while cur < sbuf.len() && !stop
        invariant
            input.pos <= cur <= sbuf.len(),
            forall|j: int| input.pos as int <= j < cur as int
                ==> !host_term_byte(sbuf.view().index(j), special),
            stop ==> (cur < sbuf.len()
                && host_term_byte(sbuf.view().index(cur as int), special)),
        decreases (if stop { 0int } else { 1int }), sbuf.len() - cur,
    {
        let c = sbuf[cur];
        proof {
            assert(sbuf.view().index(cur as int) == c);
        }
        if host_term_byte_exec(c, special) {
            stop = true;
        } else {
            cur += 1;
        }
    }
    let rest = Input { bytes: sbuf, pos: cur };
    proof {
        let srem = input_rem(&input);
        assert(machine_domain(srem));
        if cur > input.pos {
            rem_shift(sbuf, input.pos as int, (cur - input.pos) as int);
            machine_domain_subrange(srem, (cur - input.pos) as int,
                srem.len() as int);
        } else {
            assert(cur == input.pos);
            assert(srem.subrange(0, srem.len() as int) == srem);
            assert(machine_domain(srem.subrange(0, srem.len() as int)));
        }
        assert(input_rem(&rest)
            == srem.subrange((cur - input.pos) as int, srem.len() as int));
        assert(machine_domain(input_rem(&rest)));
        assert(input_ok(&rest));
        assert((input_rem(&rest).len() as int) <= 0xFFFF_FFFF);
        assert((sbuf.view().len() as int) <= 0xFFFF_FFFF);
        assert(input_wf(&rest));
    }
    (cur - input.pos, rest)
}

/// Origin Rust (parser.rs:940-950): the write!("{host}") + host_end half of
/// parse_host_and_port, followed by its empty-Domain checks: a host that is
/// the empty string with an explicit ':' port region errors (EmptyHost,
/// parser.rs:944-945), and the empty string on a special scheme errors
/// (EmptyHost, parser.rs:946-947 and the SpecialNotFile empty-host scan
/// guard, parser.rs:1005-1006). On the restricted class the deep host parse
/// is the declared premise stub and the written bytes are the run itself
/// (the identity Domain pin), so the write is the plain run append.
pub exec fn host_write_arm(
    ser: &mut Vec<u8>,
    s: &[u8],
    a: usize,
    b: usize,
    special: bool,
    after: Input,
) -> (ret: Result<(u32, super::HostInternal), ParseError>)
    requires
        a <= b,
        b <= s.view().len(),
        machine_domain(s.view().subrange(a as int, b as int)),
        host_run_class(s.view().subrange(a as int, b as int)),
        input_wf(&after),
        input_rem(&after) == s.view().subrange(b as int, s.view().len() as int),
        machine_domain(old(ser).view()),
        old(ser).view().len() + ((b - a) as int) + 8 <= 0xFFFF_FFFF,
    ensures
        ({
            let o = old(ser).view();
            let f = final(ser).view();
            let run = s.view().subrange(a as int, b as int);
            &&& machine_domain(f)
            &&& (f.len() as int) <= o.len() + ((b - a) as int)
            &&& ret.is_ok() ==> ({
                let (host_end, host_tag) = ret.unwrap();
                &&& f == o + run
                &&& ((host_end as int) == o.len() + ((b - a) as int))
                &&& (host_tag == super::HostInternal::None) == ((b - a) == 0)
                &&& (host_tag == super::HostInternal::Domain) == ((b - a) > 0)
            })
            &&& ret.is_err() ==> (ret == Err(ParseError::EmptyHost)
                && f == o
                && b == a
                && (special
                    || ((b as int) < s.view().len()
                        && s.view().index(b as int) == 0x3Au8)))
            &&& (ret.is_ok() && b == a) ==> (!special
                && ((b as int) == s.view().len()
                    || s.view().index(b as int) != 0x3Au8))
        }),
{
    let deep = host_parse_deep(s, a, b);
    match deep {
        Err(e) => {
            // unreachable: the declared premise pins the ok outcome
            proof {
                assert(false);
            }
            Err(e)
        }
        Ok((host, hs)) => {
            match host {
                super::Host::Domain(d) => {
                    if b > a {
                        vec_append_bytes(ser, &hs);
                        proof {
                            let o = old(ser).view();
                            let run = s.view().subrange(a as int, b as int);
                            assert(hs.view() == run);
                            assert(ser.view() == o + run);
                            machine_domain_add(o, run);
                            assert(machine_domain(ser.view()));
                        }
                        Ok((super::url_len32(ser),
                            super::HostInternal::Domain))
                    } else {
                        // the empty-Domain checks (parser.rs:943-950)
                        let colon_after = after.starts_with_char(0x3Au8);
                        if colon_after {
                            return Err(ParseError::EmptyHost);
                        }
                        if special {
                            return Err(ParseError::EmptyHost);
                        }
                        Ok((super::url_len32(ser),
                            super::HostInternal::None))
                    }
                }
                _ => {
                    // unreachable: the declared premise pins Domain
                    proof {
                        assert(false);
                    }
                    Err(ParseError::EmptyHost)
                }
            }
        }
    }
}

/// Origin Rust (parser.rs:953-960): the ':' port arm of parse_host_and_port:
/// after splitting the ':', run parse_port and write ':' plus the decimal
/// port when an explicit port remains (push ':' then the fast_u16_to_str
/// payload, parser.rs:956-959). The digit payload satisfies the invariant's
/// port region (digits whose dec_val is the port via dec_ascii_digits).
pub exec fn colon_port_arm<'i>(
    ser: &mut Vec<u8>,
    after: Input<'i>,
    default_port: Option<u16>,
    context: Context,
) -> (ret: Result<(Option<u16>, Input<'i>), ParseError>)
    requires
        input_wf(&after),
        input_rem(&after).len() > 0,
        input_rem(&after).index(0) == 0x3Au8,
        machine_domain(old(ser).view()),
        old(ser).view().len() + 20 <= 0xFFFF_FFFF,
    ensures
        ({
            let s = input_rem(&after);
            let post = s.subrange(1, s.len() as int);
            let o = old(ser).view();
            let f = final(ser).view();
            &&& machine_domain(f)
            &&& ret.is_err() ==> (ret == Err(ParseError::InvalidPort) && f == o)
            &&& ret.is_ok() ==> ({
                let (port, rest) = ret.unwrap();
                &&& input_wf(&rest)
                &&& port.is_none() ==> f == o
                &&& port.is_some() ==> ({
                    let pv = port.unwrap();
                    &&& f == o + seq![0x3Au8] + dec_ascii_u32(pv as int)
                    &&& (f.len() as int)
                        == o.len() + 1 + dec_len(pv as int)
                })
                &&& exists|plen: int|
                    0 <= plen
                    && plen <= post.len()
                    && (forall|j: int| 0 <= j < plen
                        ==> super::is_dec_digit(post.index(j)))
                    && (plen < post.len()
                        ==> !super::is_dec_digit(post.index(plen)))
                    && input_rem(&rest) == post.subrange(plen, post.len() as int)
                    && (port.is_some() ==> plen > 0)
            })
        }),
{
    // split the ':' (parser.rs:953)
    let rest1 = Input { bytes: after.bytes, pos: after.pos + 1 };
    proof {
        rem_shift(after.bytes, after.pos as int, 1);
        machine_domain_subrange(input_rem(&after), 1,
            input_rem(&after).len() as int);
        assert(input_rem(&rest1)
            == input_rem(&after).subrange(1, input_rem(&after).len() as int));
        assert(machine_domain(input_rem(&rest1)));
        assert(input_ok(&rest1));
        assert((input_rem(&rest1).len() as int) <= 0xFFFF_FFFF);
        assert((after.bytes.view().len() as int) <= 0xFFFF_FFFF);
        assert(input_wf(&rest1));
        let o = old(ser).view();
        assert((o.len() as int) + 20 <= 0xFFFF_FFFF);
    }
    let pp = parse_port(rest1, default_port, context);
    match pp {
        Err(e) => Err(e),
        Ok((port, rest2)) => {
            proof {
                // the post-colon growth budget for the write below
                let o = old(ser).view();
                let srem1 = input_rem(&rest1);
                let plen_w = (rest2.pos as int) - (rest1.pos as int);
                assert(plen_w >= 0);
                assert(plen_w <= srem1.len());
                assert((o.len() as int) + 2 <= 0xFFFF_FFFF);
            }
            match port {
                Option::Some(p) => {
                    proof {
                        assert(machine_domain_byte(0x3Au8));
                    }
                    let ghost pre2 = ser.view();
                    ser.push(0x3Au8);
                    proof {
                        assert(ser.view() == pre2.push(0x3Au8));
                        assert(pre2.push(0x3Au8) == pre2 + seq![0x3Au8]);
                        machine_domain_add(pre2, seq![0x3Au8]);
                        assert(machine_domain(ser.view()));
                        dec_ascii_len(p as int);
                        assert((ser.view().len() as int) + 10
                            <= 0xFFFF_FFFF);
                    }
                    append_dec_port(ser, p);
                    proof {
                        let o = old(ser).view();
                        let mid = o + seq![0x3Au8];
                        assert(ser.view() == mid + dec_ascii_u32(p as int));
                        assert(ser.view()
                            == o + seq![0x3Au8] + dec_ascii_u32(p as int));
                        dec_ascii_len(p as int);
                        dec_ascii_digits(p as int);
                        // the digit bytes are machine-domain (0x30..0x39)
                        assert forall|j: int|
                            0 <= j < dec_ascii_u32(p as int).len()
                            implies machine_domain_byte(
                                dec_ascii_u32(p as int).index(j)) by {
                            assert(super::is_dec_digit(
                                dec_ascii_u32(p as int).index(j)));
                        }
                        machine_domain_add(mid, dec_ascii_u32(p as int));
                        assert(machine_domain(ser.view()));
                    }
                    Ok((Option::Some(p), rest2))
                }
                Option::None => Ok((Option::None, rest2)),
            }
        }
    }
}


/// Two maximal wall-free host prefixes coincide: the split length of
/// host_split_form is unique, so the scan's maximal prefix is the classed
/// split of the premise.
pub proof fn host_split_unique(s: Seq<u8>, special: bool, h1: int, h2: int)
    requires
        host_split_form(s, h1, special),
        host_split_form(s, h2, special),
    ensures
        h1 == h2,
{
    if h1 < h2 {
        assert(h1 < h2 <= s.len());
        assert(!host_term_byte(s.index(h1), special));
        assert(h1 < s.len());
        assert(host_term_byte(s.index(h1), special));
        assert(false);
    } else if h2 < h1 {
        assert(h2 < h1 <= s.len());
        assert(!host_term_byte(s.index(h2), special));
        assert(h2 < s.len());
        assert(host_term_byte(s.index(h2), special));
        assert(false);
    }
}

/// A maximal wall-free prefix of the input is exactly the classed split of
/// host_split_class: maximality fixes the length, so the scan's prefix
/// inherits the class of the premise's split (the choose stays inside this
/// lemma's isolated query).
pub proof fn host_split_unique_walls(
    s: Seq<u8>,
    special: bool,
    h1: int,
    h2: int,
)
    requires
        0 <= h1,
        h1 <= s.len(),
        (forall|j: int| 0 <= j < h1
            ==> !host_term_byte(s.index(j), special)),
        (h1 < s.len() ==> host_term_byte(s.index(h1), special)),
        host_split_form(s, h2, special),
    ensures
        h1 == h2,
        host_split_form(s, h1, special),
{
    if h1 < h2 {
        assert(!host_term_byte(s.index(h1), special));
        assert(h1 < s.len());
        assert(host_term_byte(s.index(h1), special));
        assert(false);
    } else if h2 < h1 {
        assert(h2 < h1 <= s.len());
        assert(!host_term_byte(s.index(h2), special));
        assert(h2 < s.len());
        assert(host_term_byte(s.index(h2), special));
        assert(false);
    }
}

/// The scan's maximal prefix run is classed (the bridge used by the
/// parse_host_and_port assembly).
pub proof fn host_scan_classed(s: Seq<u8>, special: bool, h: int)
    requires
        host_split_class(s, special),
        0 <= h,
        h <= s.len(),
        (forall|j: int| 0 <= j < h
            ==> !host_term_byte(s.index(j), special)),
        (h < s.len() ==> host_term_byte(s.index(h), special)),
    ensures
        host_run_class(s.subrange(0, h)),
{
    let h0 = choose|h0: int| host_split_form(s, h0, special);
    host_split_unique_walls(s, special, h, h0);
}

/// The classed run in remaining-suffix coordinates is the same byte range
/// as the slice-range the assembly passes on: the composition of the range
/// views (isolated so the assembly body query stays small).
pub proof fn rem_run_is_slice_run(bytes: &[u8], pos: usize, h: usize)
    requires
        (pos as int) + (h as int) <= bytes.view().len(),
    ensures
        bytes.view().subrange(pos as int, (pos + h) as int)
            == bytes.view().subrange(pos as int, bytes.view().len() as int)
                .subrange(0, h as int),
{
    vstd::seq::lemma_seq_subrange_composition(
        bytes.view(), pos as int, bytes.view().len() as int, 0, h as int);
}

/// The rem-coordinate class and machine-domain facts of the scanned run,
/// transferred to the slice coordinates the write arm and the deep stub use
/// (the range-view compositions stay inside this lemma's small query).
pub proof fn host_tail_entry_pins(bytes: &[u8], pos: usize, h: usize)
    requires
        (pos as int) + (h as int) <= bytes.view().len(),
        machine_domain(
            bytes.view().subrange(pos as int, bytes.view().len() as int)
                .subrange(0, h as int)),
        host_run_class(
            bytes.view().subrange(pos as int, bytes.view().len() as int)
                .subrange(0, h as int)),
    ensures
        machine_domain(
            bytes.view().subrange(pos as int, (pos + h) as int)),
        host_run_class(
            bytes.view().subrange(pos as int, (pos + h) as int)),
        bytes.view().subrange((pos + h) as int, bytes.view().len() as int)
            == bytes.view().subrange(pos as int, bytes.view().len() as int)
                .subrange(h as int,
                    bytes.view().len() as int - (pos as int)),
{
    vstd::seq::lemma_seq_subrange_composition(
        bytes.view(), pos as int, bytes.view().len() as int, 0, h as int);
    vstd::seq::lemma_seq_subrange_composition(
        bytes.view(), pos as int, bytes.view().len() as int,
        h as int, bytes.view().len() as int - (pos as int));
}

impl Parser<'_> {

/// Origin Rust (parser.rs:953-960 tail): the ':' port arm used by the
/// assembly tail below when the post-scan rest starts with ':'.
/// (Helper kept small so the assembly tail query stays in budget.)

/// Origin Rust (parser.rs:940-969): the write-and-port tail of
/// parse_host_and_port in slice coordinates: the scan's outputs (the run
/// range and the post-scan rest) are the parameters, so the arm-level
/// obligations live in a query without the state-machine entry context.
/// The monolithic assembly of the scanner batch had every per-conjunct
/// obligation green but the single body query exceeded the solver budget
/// even at rlimit 300; the scan / tail split localizes the context (the
/// classed-run premise is exactly what the write arm consumes).
pub exec fn hap_host_port_tail<'i>(
    ser: &mut Vec<u8>,
    orig: Input<'i>,
    h: usize,
    rest: Input<'i>,
    special: bool,
    default_port: Option<u16>,
    context: Context,
) -> (ret: Result<(u32, super::HostInternal, Option<u16>, Input<'i>), ParseError>)
    requires
        input_wf(&orig),
        input_wf(&rest),
        (h as int) <= input_rem(&orig).len(),
        input_rem(&rest)
            == input_rem(&orig).subrange(h as int, input_rem(&orig).len() as int),
        machine_domain(input_rem(&orig).subrange(0, h as int)),
        host_run_class(input_rem(&orig).subrange(0, h as int)),
        machine_domain(old(ser).view()),
        old(ser).view().len()
            + (input_rem(&orig).len() as int) + 24 <= 0xFFFF_FFFF,
    ensures
        ({
            let before = old(ser).view();
            let serf = final(ser).view();
            let run = input_rem(&orig).subrange(0, h as int);
            &&& machine_domain(serf)
            &&& (serf.len() as int)
                <= before.len() + (run.len() as int) + 6
            &&& (ret.is_err() ==> (ret == Err(ParseError::EmptyHost)
                || ret == Err(ParseError::InvalidPort)))
            &&& (ret.is_ok() ==> ({
                let (host_end, host_tag, port, rest2) = ret.unwrap();
                &&& input_wf(&rest2)
                &&& ((input_rem(&rest2).len() as int)
                    <= (input_rem(&orig).len() as int))
                &&& (host_end as int)
                    == before.len() + (run.len() as int)
                &&& (host_tag == super::HostInternal::None)
                    == (run.len() == 0)
                &&& (host_tag == super::HostInternal::Domain)
                    == (run.len() > 0)
                &&& (run.len() == 0 ==> (!special
                    && (input_rem(&rest).len() == 0
                        || input_rem(&rest).index(0) != 0x3Au8)))
                &&& (port.is_none()
                    ==> (serf == before + run
                        && (serf.len() as int) == (host_end as int)))
                &&& (port.is_some() ==> run.len() > 0)
                &&& (port.is_some() ==> ({
                    let pv = port.unwrap();
                    let plen = (serf.len() as int)
                        - (host_end as int) - 1;
                    &&& 1 <= plen
                    &&& serf == before + run + seq![0x3Au8]
                        + dec_ascii_u32(pv as int)
                }))
            }))
        }),
{
    proof {
        // slice coordinates of the run (the write arm and the deep stub work
        // on the slice ranges; the range-view compositions live in
        // host_tail_entry_pins' own small query)
        host_tail_entry_pins(orig.bytes, orig.pos, h);
        assert(input_rem(&orig)
            == orig.bytes.view().subrange(orig.pos as int,
                orig.bytes.view().len() as int));
        assert(input_rem(&rest)
            == orig.bytes.view().subrange((orig.pos + h) as int,
                orig.bytes.view().len() as int));
    }
    match host_write_arm(
        ser,
        orig.bytes,
        orig.pos,
        orig.pos + h,
        special,
        rest,
    ) {
        Err(e) => {
            proof {
                let before = old(ser).view();
                let serf = ser.view();
                assert(machine_domain(serf));
                assert((serf.len() as int)
                    <= before.len() + (h as int) + 6);
            }
            return Err(e);
        }
        Ok((host_end, host_tag)) => {
            let has_colon = rest.starts_with_char(0x3Au8);
            if !has_colon {
                proof {
                    let before = old(ser).view();
                    let serf = ser.view();
                    let rem = input_rem(&orig);
                    let run = rem.subrange(0, h as int);
                    assert(machine_domain(serf));
                    assert((serf.len() as int)
                        <= before.len() + (run.len() as int) + 6);
                    assert(input_wf(&rest));
                    assert((host_end as int)
                        == before.len() + (run.len() as int));
                    assert(serf == before + run);
                    assert((host_tag == super::HostInternal::None)
                        == (run.len() == 0));
                    assert((host_tag == super::HostInternal::Domain)
                        == (run.len() > 0));
                    if run.len() == 0 {
                        assert(!special);
                        assert(input_rem(&rest).len() == 0
                            || input_rem(&rest).index(0) != 0x3Au8);
                    }
                }
                return Ok((host_end, host_tag, Option::None, rest));
            }
            proof {
                let before = old(ser).view();
                assert(input_rem(&rest).len() > 0);
                assert(input_rem(&rest).index(0) == 0x3Au8);
                assert(machine_domain(ser.view()));
                assert((ser.view().len() as int) + 20 <= 0xFFFF_FFFF);
            }
            match colon_port_arm(
                ser,
                rest,
                default_port,
                context,
            ) {
                Err(e) => {
                    proof {
                        let before = old(ser).view();
                        let serf = ser.view();
                        let rem = input_rem(&orig);
                        let run = rem.subrange(0, h as int);
                        assert(machine_domain(serf));
                        assert((serf.len() as int)
                            <= before.len() + (run.len() as int) + 6);
                    }
                    return Err(e);
                }
                Ok((port, rest2)) => {
                    proof {
                        let before = old(ser).view();
                        let serf = ser.view();
                        let rem = input_rem(&orig);
                        let run = rem.subrange(0, h as int);
                        assert(machine_domain(serf));
                        assert(machine_domain(run));
                        machine_domain_add(before, run);
                        if port.is_none() {
                            assert(serf.len() == (host_end as int));
                            assert((serf.len() as int)
                                <= before.len() + (run.len() as int) + 6);
                        } else {
                            let pv = port.unwrap();
                            dec_ascii_len(pv as int);
                            dec_len_bound_u16(pv as int);
                            assert(1 <= dec_len(pv as int) <= 5);
                            assert(serf.len()
                                == (host_end as int)
                                    + 1 + dec_len(pv as int));
                            assert((serf.len() as int)
                                <= before.len() + (run.len() as int) + 6);
                        }
                        assert(input_wf(&rest2));
                        assert((host_end as int)
                            == before.len() + (run.len() as int));
                        assert((host_tag == super::HostInternal::None)
                            == (run.len() == 0));
                        assert((host_tag == super::HostInternal::Domain)
                            == (run.len() > 0));
                        if run.len() == 0 {
                            assert(!special);
                            assert(input_rem(&rest).len() == 0
                                || input_rem(&rest).index(0) != 0x3Au8);
                        }
                    }
                    proof {
                        assert((input_rem(&rest2).len() as int)
                            <= (input_rem(&orig).len() as int));
                        if port.is_some() {
                            // the colon gate excludes the empty-run face
                            assert(h as int > 0);
                        }
                    }
                    return Ok((host_end, host_tag, port, rest2));
                }
            }
        }
    }
}

/// Origin Rust (parser.rs:934-969): pub fn parse_host_and_port(&mut self,
///   input, scheme_end, scheme_type) -> ParseResult<(u32, HostInternal,
///   Option<u16>, Input<'i>)>. On the restricted class the deep host parse is
/// the declared premise stub; the default_port closure of upstream (the
/// scheme lookup evaluated once, parser.rs:955) is the value parameter (the
/// scheme prefix is the caller's fixed region). The monolithic assembly of
/// the scanner batch exceeded the solver budget even at rlimit 300; the
/// scan / tail split localizes each query.
/* [verus note: rlimit = the whole-fn check rides the frontier of the
   default budget under the read-API harness ambient context (it went
   over once the base-merge record carries entered the module's air
   context); only the resource ceiling is raised, no obligation is
   relaxed, the fn's own content is untouched] */
#[verifier::rlimit(30)]
pub exec fn parse_host_and_port<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
    default_port: Option<u16>,
    context: Context,
) -> (r: Result<(u32, super::HostInternal, Option<u16>, Input<'i>), ParseError>)
    requires
        input_wf(&input),
        machine_domain(old(self).serialization.view()),
        host_split_class(input_rem(&input), is_special(scheme_type)),
        old(self).serialization.view().len()
            + (input_rem(&input).len() as int) + 24 <= 0xFFFF_FFFF,
    ensures
        ({
            let before = old(self).serialization.view();
            let serf = final(self).serialization.view();
            let s = input_rem(&input);
            let special = is_special(scheme_type);
            &&& machine_domain(serf)
            &&& (final(self).context == old(self).context)
            &&& (r.is_ok() ==> (forall|j: int| 0 <= j && j < before.len()
                ==> serf.index(j) == before.index(j)))
            &&& (r.is_ok() ==> ((input_rem(&r.unwrap().3).len() as int)
                <= (input_rem(&input).len() as int)))
            &&& (serf.len() as int) <= before.len() + (s.len() as int) + 6
            &&& (r.is_err() ==> (r == Err(ParseError::EmptyHost)
                || r == Err(ParseError::InvalidPort)))
            &&& (r.is_ok() ==> ({
                let (host_end, host_tag, port, rest) = r.unwrap();
                let h = (host_end as int) - before.len();
                &&& input_wf(&rest)
                &&& host_run_class(s.subrange(0, h))
                &&& (port.is_some() ==> h > 0)
                &&& 0 <= h
                &&& h <= s.len()
                &&& port.is_none()
                    ==> (serf == before + s.subrange(0, h)
                        && (serf.len() as int) == (host_end as int))
                &&& (port.is_some() ==> ({
                    let pv = port.unwrap();
                    let plen = (serf.len() as int)
                        - (host_end as int) - 1;
                    &&& 1 <= plen
                    &&& serf == before + s.subrange(0, h)
                        + seq![0x3Au8] + dec_ascii_u32(pv as int)
                }))
                &&& (host_tag == super::HostInternal::None) == (h == 0)
                &&& (host_tag == super::HostInternal::Domain) == (h > 0)
                &&& (h == 0 ==> (!special
                    && (s.len() == 0 || s.index(0) != 0x3Au8)))
            }))
        }),
{
    let special = scheme_type.is_special();
    let (h, rest) = host_scan_walls(input, special);
    proof {
        // the scan's prefix is the classed split of the premise (the choose
        // and the uniqueness case split live in host_scan_classed's own
        // small query; every fact here is already in rem coordinates)
        let s = input_rem(&input);
        let hq = h as int;
        host_scan_classed(s, special, hq);
        machine_domain_subrange(s, 0, hq);
    }
    let rr = Self::hap_host_port_tail(
        &mut self.serialization,
        input,
        h,
        rest,
        special,
        default_port,
        context,
    );
    proof {
        // per-conjunct localization of the postcondition (each assert is
        // its own small query; the final discharge is then trivial)
        let before = old(self).serialization.view();
        let serf = self.serialization.view();
        let s = input_rem(&input);
        let hq = h as int;
        assert(machine_domain(serf));
        assert((serf.len() as int)
            <= before.len() + (s.len() as int) + 6);
        if rr.is_err() {
            assert(rr == Err(ParseError::EmptyHost)
                || rr == Err(ParseError::InvalidPort));
        } else {
            let (host_end, host_tag, port, rest2) = rr.unwrap();
            assert(input_wf(&rest2));
            assert((host_end as int) == before.len() + hq);
            assert(0 <= hq);
            assert(hq <= s.len());
            if port.is_none() {
                assert(serf == before + s.subrange(0, hq));
                assert((serf.len() as int) == (host_end as int));
            } else {
                let pv = port.unwrap();
                let plen = (serf.len() as int) - (host_end as int) - 1;
                assert(1 <= plen);
                assert(serf == before + s.subrange(0, hq)
                    + seq![0x3Au8] + dec_ascii_u32(pv as int));
            }
            assert((host_tag == super::HostInternal::None) == (hq == 0));
            assert((host_tag == super::HostInternal::Domain) == (hq > 0));
            if hq == 0 {
                assert(!special);
                assert(is_special(scheme_type) == special);
                assert(input_rem(&rest).len() == 0
                    || input_rem(&rest).index(0) != 0x3Au8);
                assert(input_rem(&rest).len() == s.len());
                assert(s.len() == 0 || s.index(0) != 0x3Au8);
            }
            // the classed run face on both exits
            assert(host_run_class(s.subrange(0, hq)));
            if port.is_none() {
            } else {
                assert(hq > 0);
            }
            // prefix preservation (localized: one small query)
            assert forall|j: int| 0 <= j && j < before.len()
                implies serf.index(j) == before.index(j) by {
                if port.is_none() {
                    vstd::seq::lemma_seq_add_index1(before,
                        s.subrange(0, hq), j);
                } else {
                    vstd::seq::lemma_seq_add_index1(before,
                        s.subrange(0, hq) + seq![0x3Au8]
                            + dec_ascii_u32(port.unwrap() as int), j);
                }
            }
        }
    }
    rr
}

}

impl Parser<'_> {

/// Origin Rust (parser.rs:1355-1369): pub fn
/// parse_cannot_be_a_base_path(&mut self, input) -> Input -- the
/// cannot-be-a-base (opaque path) state: extend the serialization with each
/// byte percent-encoded against the CONTROLS set up to a '?'/'#' terminator
/// (the '(' terminator pair of the UrlParser-context face; the
/// check_url_code_point observation arm is dropped with the violation_fn
/// ledger), the terminator staying for the query/fragment state. The
/// appended region is the encode of the consumed prefix, which contains no
/// '?' or '#' (the scan stops before them and the CONTROLS escape never
/// introduces one; enc_seq_no_delims).
pub exec fn parse_cannot_be_a_base_path<'i>(
    &mut self,
    input: Input<'i>,
) -> (r: Input<'i>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        old(self).serialization.view().len()
            + 3 * (input_rem(&input).len() as int) <= 0xFFFF_FFFF,
    ensures
        input_wf(&r)
            && (input_rem(&r).len() == 0
                || input_rem(&r).index(0) == 0x3Fu8
                || input_rem(&r).index(0) == 0x23u8)
            && final(self).context == old(self).context
            && machine_domain(final(self).serialization.view())
            && (forall|j: int|
                old(self).serialization.view().len() <= j
                    && j < final(self).serialization.view().len()
                ==> final(self).serialization.view().index(j) != 0x3Fu8
                    && final(self).serialization.view().index(j) != 0x23u8)
            && (final(self).serialization.view()
                == old(self).serialization.view()
                    + enc_seq(
                        input_rem(&input).subrange(
                            0,
                            (input_rem(&input).len() as int)
                                - (input_rem(&r).len() as int)),
                        EncodeSet::Controls))
            && (final(self).serialization.view().len() as int)
                <= old(self).serialization.view().len()
                    + 3 * ((input_rem(&input).len() as int)
                        - (input_rem(&r).len() as int)),
{
    let sbuf = input.bytes;
    let n = sbuf.len();
    // scan to the '?'/'#' terminator (parser.rs:1360-1366)
    let mut cur: usize = input.pos;
    let mut stop = false;
    while cur < n && !stop
        invariant
            input.pos <= cur <= n,
            (n as int) == (sbuf.view().len() as int),
            forall|j: int| input.pos as int <= j < cur as int
                ==> (sbuf.view().index(j) != 0x3Fu8
                    && sbuf.view().index(j) != 0x23u8),
            stop ==> (cur < n
                && (sbuf.view().index(cur as int) == 0x3Fu8
                    || sbuf.view().index(cur as int) == 0x23u8)),
        decreases (if stop { 0int } else { 1int }), n - cur,
    {
        let c = sbuf[cur];
        proof {
            assert(sbuf.view().index(cur as int) == c);
        }
        if c == 0x3Fu8 || c == 0x23u8 {
            stop = true;
        } else {
            cur += 1;
        }
    }
    extend_percent_encode_at(&mut self.serialization, sbuf, input.pos,
        cur, EncodeSet::Controls);
    let r = Input { bytes: sbuf, pos: cur };
    proof {
        let before = old(self).serialization.view();
        let serf = self.serialization.view();
        let remv = input_rem(&input);
        let k = (cur - input.pos) as int;
        assert((input_rem(&r).len() as int) == (remv.len() as int) - k);
        rem_run_is_slice_run(sbuf, input.pos, k as usize);
        let run = sbuf.view().subrange(input.pos as int, cur as int);
        assert(run == remv.subrange(0, k));
        assert(serf == before
            + enc_seq(remv.subrange(0, k), EncodeSet::Controls));
        machine_domain_subrange(remv, 0, k);
        enc_seq_machine(remv.subrange(0, k), EncodeSet::Controls);
        machine_domain_add(before,
            enc_seq(remv.subrange(0, k), EncodeSet::Controls));
        assert(machine_domain(serf));
        enc_seq_len_bound(remv.subrange(0, k), EncodeSet::Controls);
        vstd::seq::lemma_seq_add_len(before,
            enc_seq(remv.subrange(0, k), EncodeSet::Controls));
        assert((serf.len() as int)
            <= before.len() + 3 * k);
        assert((serf.len() as int)
            <= before.len()
                + 3 * ((remv.len() as int)
                    - (input_rem(&r).len() as int)));
        // the consumed prefix avoids the delimiters (the scan invariant)
        assert forall|j: int|
            0 <= j < (remv.subrange(0, k)).len()
            implies remv.subrange(0, k).index(j) != 0x3Fu8
                && remv.subrange(0, k).index(j) != 0x23u8 by {
            vstd::seq::lemma_seq_subrange_index(remv, 0, k, j);
            vstd::seq::lemma_seq_subrange_index(
                sbuf.view(), input.pos as int, sbuf.view().len() as int, j);
            assert(remv.index(j) == sbuf.view().index((input.pos as int) + j));
        }
        enc_seq_no_delims(remv.subrange(0, k), EncodeSet::Controls);
        // the appended-region bytes are those of the prefix encode
        assert forall|j: int|
            before.len() <= j && j < serf.len()
            implies serf.index(j) != 0x3Fu8
                && serf.index(j) != 0x23u8 by {
            vstd::seq::lemma_seq_add_index2(before,
                enc_seq(remv.subrange(0, k), EncodeSet::Controls), j);
        }
        // the terminator face: stopped exactly at '?'/'#', or EOF
        rem_shift(sbuf, input.pos as int, k);
        machine_domain_subrange(remv, k, remv.len() as int);
        assert(machine_domain(input_rem(&r)));
        assert(input_ok(&r));
        assert((input_rem(&r).len() as int) <= 0xFFFF_FFFF);
        assert(input_wf(&r));
        if stop {
            assert(input_rem(&r).index(0) == 0x3Fu8
                || input_rem(&r).index(0) == 0x23u8);
        }
    }
    r
}

}
/// enc_seq never emits '?' or '#' when the source bytes avoid them: the
/// escaped hex digits range 0x30..0x39 / 0x41..0x46 (never 0x23/0x3F), and
/// pass-through bytes avoid them by hypothesis.
pub proof fn enc_seq_no_delims(s: Seq<u8>, set: EncodeSet)
    requires
        machine_domain(s),
        (forall|j: int| #![trigger s.index(j)]
            0 <= j < s.len()
            ==> (s.index(j) != 0x3Fu8 && s.index(j) != 0x23u8)),
    ensures
        (forall|j: int| #![trigger enc_seq(s, set).index(j)]
            0 <= j < enc_seq(s, set).len()
            ==> (enc_seq(s, set).index(j) != 0x3Fu8
                && enc_seq(s, set).index(j) != 0x23u8)),
    decreases s.len(),
{
    if s.len() > 0 {
        let tail = s.subrange(1, s.len() as int);
        machine_domain_subrange(s, 1, s.len() as int);
        enc_seq_no_delims(tail, set);
        let eb = enc_byte(s.index(0), set);
        let rest = enc_seq(tail, set);
        assert(enc_seq(s, set) == eb + rest);
        vstd::seq::lemma_seq_add_len(eb, rest);
        assert(enc_seq(s, set).len()
            == eb.len() + rest.len());
        if in_set(set, s.index(0)) {
            let hx = hex_digit_byte((s.index(0) as int) / 16);
            let hy = hex_digit_byte((s.index(0) as int) % 16);
            assert(eb == seq![0x25u8, hx, hy]);
            assert(0 <= (s.index(0) as int) / 16 <= 15);
            assert(0 <= (s.index(0) as int) % 16 <= 15);
            assert(machine_domain_byte(0x25u8));
            assert(hx != 0x3Fu8 && hx != 0x23u8);
            assert(hy != 0x3Fu8 && hy != 0x23u8);
            assert forall|j: int|
                0 <= j < 3 && 3 <= j + rest.len() implies
                (eb + rest).index(j) == seq![0x25u8, hx, hy].index(j) by {
                vstd::seq::lemma_seq_add_index1(
                    seq![0x25u8, hx, hy], rest, j);
            }
            assert forall|j: int| #![trigger (eb + rest).index(j)]
                3 <= j < (eb + rest).len() implies
                (eb + rest).index(j) != 0x3Fu8 && (eb + rest).index(j) != 0x23u8 by {
                vstd::seq::lemma_seq_add_index2(seq![0x25u8, hx, hy], rest, j);
            }
        } else {
            assert(eb.len() == 1);
            assert forall|j: int| #![trigger (eb + rest).index(j)]
                0 <= j < (eb + rest).len() implies
                (eb + rest).index(j) != 0x3Fu8 && (eb + rest).index(j) != 0x23u8 by {
                if j == 0 {
                    vstd::seq::lemma_seq_add_index1(
                        seq![s.index(0)], rest, 0);
                    assert((eb + rest).index(0) == s.index(0));
                    assert(s.index(0) != 0x3Fu8 && s.index(0) != 0x23u8);
                } else {
                    vstd::seq::lemma_seq_add_index2(
                        seq![s.index(0)], rest, j);
                    assert((eb + rest).index(j) == rest.index(j - 1));
                }
            }
        }
    }
}

/* ============================================================
 * Path segment arms (Origin: the double-dot / single-dot /
 * file-drive match arms of parse_path, parser.rs:1240-1296:
 * each arm is its own helper so the outer segment loop's
 * query carries only the scan invariants)
 * ============================================================ */

/// The crop arms each leave the serialization as a prefix truncation of the
/// old bytes plus at most one appended '/', so the path region's shape
/// survives: machine-domain, the '/' anchor at path_start, and freedom from
/// '?' and '#' (shared by the double-dot and single-dot arms).
pub proof fn path_region_crops_preserve(
    o: Seq<u8>,
    f: Seq<u8>,
    path_start: int,
)
    requires
        machine_domain(o),
        0 <= path_start,
        path_start < f.len(),
        ((f.len() as int) <= (o.len() as int)
            && f == o.subrange(0, f.len() as int))
        || (f == o.subrange(0, (f.len() as int) - 1) + seq![0x2Fu8]
            && (f.len() as int) - 1 <= (o.len() as int)),
        o.index(path_start) == 0x2Fu8,
        (forall|j: int| #![trigger o.index(j)]
            path_start <= j && j < o.len()
            ==> o.index(j) != 0x3Fu8
                && o.index(j) != 0x23u8),
    ensures
        machine_domain(f),
        (path_start as int) < f.len(),
        f.index((path_start as int)) == 0x2Fu8,
        (forall|j: int| #![trigger f.index(j)]
            (path_start as int) <= j && j < f.len()
            ==> f.index(j) != 0x3Fu8
                && f.index(j) != 0x23u8),
{
    if f == o.subrange(0, f.len() as int) && (f.len() as int) <= (o.len() as int) {
        // pure prefix truncation
        machine_domain_subrange(o, 0, f.len() as int);
        vstd::seq::lemma_seq_subrange_index(o, 0, f.len() as int,
            path_start as int);
        assert(f.index(path_start) == o.index(path_start));
        assert forall|j: int| #![trigger f.index(j)]
            (path_start as int) <= j && j < f.len()
            implies f.index(j) != 0x3Fu8
                && f.index(j) != 0x23u8 by {
            vstd::seq::lemma_seq_subrange_index(o, 0, f.len() as int, j);
            assert(f.index(j) == o.index(j));
        }
    } else {
        // prefix truncation plus one appended '/' (o[..m] + '/')
        assert(f == o.subrange(0, (f.len() as int) - 1) + seq![0x2Fu8]);
        let m = (f.len() as int) - 1;
        assert(m <= o.len() as int);
        machine_domain_subrange(o, 0, m);
        machine_domain_add(o.subrange(0, m), seq![0x2Fu8]);
        if path_start < m {
            vstd::seq::lemma_seq_add_index1(o.subrange(0, m),
                seq![0x2Fu8], path_start);
            vstd::seq::lemma_seq_subrange_index(o, 0, m, path_start);
        } else {
            assert(path_start == m);
        }
        assert(f.index(path_start) == 0x2Fu8);
        assert forall|j: int| #![trigger f.index(j)]
            (path_start as int) <= j && j < f.len()
            implies f.index(j) != 0x3Fu8
                && f.index(j) != 0x23u8 by {
            if j < m {
                vstd::seq::lemma_seq_add_index1(
                    o.subrange(0, m), seq![0x2Fu8], j);
                vstd::seq::lemma_seq_subrange_index(o, 0, m, j);
                assert(f.index(j) == o.index(j));
            } else {
                vstd::seq::lemma_seq_add_index2(
                    o.subrange(0, m), seq![0x2Fu8], j);
                assert(f.index(j) == 0x2Fu8);
            }
        }
    }
}

/// Origin Rust (parser.rs:1241-1255):
///   match ".." | ... => { debug_assert!(ser[segment_start - 1] == b'/');
///     self.serialization.truncate(segment_start);
///     if self.serialization.ends_with('/') &&
///        Parser::last_slash_can_be_removed(&self.serialization, path_start)
///       { self.serialization.pop(); }
///     self.shorten_path(scheme_type, path_start);
///     if ends_with_slash && !self.serialization.ends_with('/')
///       { self.serialization.push('/'); } }
/// The debug_assert is exculpated by the arm's guard (a double-dot segment
/// only exists after a flushed run, whose '/'-predecessor the loop proves).
pub exec fn segment_dd_arm(
    ser: &mut Vec<u8>,
    is_file: bool,
    path_start: usize,
    seg_start: usize,
    ends_with_slash: bool,
)
    requires
        machine_domain(old(ser).view()),
        (path_start as int) < (seg_start as int),
        (seg_start as int) <= old(ser).view().len(),
        old(ser).view().index(path_start as int) == 0x2Fu8,
        (forall|j: int| (path_start as int) <= j
            && j < old(ser).view().len()
            ==> old(ser).view().index(j) != 0x3Fu8
                && old(ser).view().index(j) != 0x23u8),
        ends_with_slash
            ==> old(ser).view().index(
                old(ser).view().len() as int - 1) == 0x2Fu8,
    ensures
        machine_domain(final(ser).view())
            && (path_start as int) + 1 <= final(ser).view().len()
            && final(ser).view().index(path_start as int) == 0x2Fu8
            && (forall|j: int| (path_start as int) <= j
                && j < final(ser).view().len()
                ==> final(ser).view().index(j) != 0x3Fu8
                    && final(ser).view().index(j) != 0x23u8)
            && (ends_with_slash
                ==> final(ser).view().index(
                    final(ser).view().len() as int - 1) == 0x2Fu8)
            && final(ser).view().subrange(0, path_start as int)
                == old(ser).view().subrange(0, path_start as int)
            && (final(ser).view().len() as int)
                <= (old(ser).view().len() as int) + 1
            && (final(ser).view().len() as int)
                <= (seg_start as int) + 1,
{
    ser.truncate(seg_start);
    if ends_with_slash
        && last_slash_can_be_removed(ser, path_start)
    {
        let po = ser.pop();
        proof {
            assert(po.is_some());
        }
    }
    proof {
        // shorten_path applies when a path remains (the '/' anchor pins a
        // slash into the region)
        let sv = ser.view();
        if (sv.len() as int) > (path_start as int) {
            assert(exists|j: int|
                (path_start as int) <= j < sv.len() as int
                    && sv.index(j) == 0x2Fu8) by {
                assert((path_start as int) < sv.len() as int);
                assert(sv.index(path_start as int) == 0x2Fu8);
            }
        }
    }
    shorten_path(ser, is_file, path_start);
    if ends_with_slash && ser[ser.len() - 1] != 0x2Fu8 {
        ser.push(0x2Fu8);
    }
    proof {
        // the arm leaves a prefix truncation of o plus at most one
        // appended '/' (the shared crop-preservation lemma carries the
        // region's shape facts)
        let o = old(ser).view();
        let f = final(ser).view();
        assert((f.len() as int) <= (o.len() as int) + 1);
        assert(((f.len() as int) <= (o.len() as int)
            && f == o.subrange(0, f.len() as int))
        || (f == o.subrange(0, (f.len() as int) - 1) + seq![0x2Fu8]
            && (f.len() as int) - 1 <= (o.len() as int)));
        assert((path_start as int) < f.len());
        path_region_crops_preserve(o, f, path_start as int);
        if ends_with_slash {
            assert(f.index(f.len() as int - 1) == 0x2Fu8);
        }
    }
}
/// Origin Rust (parser.rs:1250-1257):
///   "." | "%2e" | "%2E" => { self.serialization.truncate(segment_start);
///     if !self.serialization.ends_with('/') { self.serialization.push('/'); } }
pub exec fn segment_sd_arm(
    ser: &mut Vec<u8>,
    path_start: usize,
    seg_start: usize,
)
    requires
        machine_domain(old(ser).view()),
        (path_start as int) < (seg_start as int),
        (seg_start as int) <= old(ser).view().len(),
        old(ser).view().index(path_start as int) == 0x2Fu8,
        (forall|j: int| (path_start as int) <= j
            && j < old(ser).view().len()
            ==> old(ser).view().index(j) != 0x3Fu8
                && old(ser).view().index(j) != 0x23u8),
    ensures
        machine_domain(final(ser).view())
            && (path_start as int) + 1 <= final(ser).view().len()
            && final(ser).view().index(path_start as int) == 0x2Fu8
            && final(ser).view().index(
                final(ser).view().len() as int - 1) == 0x2Fu8
            && (forall|j: int| (path_start as int) <= j
                && j < final(ser).view().len()
                ==> final(ser).view().index(j) != 0x3Fu8
                    && final(ser).view().index(j) != 0x23u8)
            && final(ser).view().subrange(0, path_start as int)
                == old(ser).view().subrange(0, path_start as int)
            && (final(ser).view().len() as int)
                <= (old(ser).view().len() as int) + 1
            && (final(ser).view().len() as int)
                <= (seg_start as int) + 1,
{
    ser.truncate(seg_start);
    if ser[ser.len() - 1] != 0x2Fu8 {
        ser.push(0x2Fu8);
    }
    proof {
        let o = old(ser).view();
        let f = final(ser).view();
        assert(machine_domain(f));
        assert(f.index(path_start as int) == 0x2Fu8);
        assert((path_start as int) + 1 <= f.len() as int);
        assert(f.index(f.len() as int - 1) == 0x2Fu8);
        assert forall|j: int|
            (path_start as int) <= j && j < f.len()
            implies f.index(j) != 0x3Fu8
                && f.index(j) != 0x23u8 by {
            if j < f.len() as int - 1 {
                assert(f.index(j) == o.index(j));
            } else {
                assert(f.index(j) == 0x2Fu8);
            }
        }
    }
}

/// Origin Rust (parser.rs:1266-1296, the default arm's windows-drive
/// replacement): if url's scheme is "file", the path is empty, and buffer is
/// a windows drive letter, replace the second code point with ':' and clear
/// has_host (the FIXME of upstream: the log arm drops with violation_fn):
///   if scheme_type.is_file() && segment_start == path_start + 1
///     && is_windows_drive_letter(segment_before_slash) {
///     if let Some(c) = segment_before_slash.chars().next() {
///       self.serialization.truncate(segment_start);
///       self.serialization.push(c); self.serialization.push(':');
///       if ends_with_slash { self.serialization.push('/'); } }
///     if *has_host { *has_host = false; } }
pub exec fn segment_drive_arm(
    ser: &mut Vec<u8>,
    has_host: &mut bool,
    path_start: usize,
    seg_start: u32,
    seg_len: u32,
    c0: u8,
    ends_with_slash: bool,
)
    requires
        seg_len == 2,
        machine_domain(old(ser).view()),
        (path_start as int) + 1 == (seg_start as int),
        (seg_start as int) + 2 <= old(ser).view().len(),
        old(ser).view().index(path_start as int) == 0x2Fu8,
        super::is_ascii_alpha(c0),
        old(ser).view().index(seg_start as int) == c0,
    ensures
        machine_domain(final(ser).view())
            && (final(ser).view().len() as int)
                == (seg_start as int) + 2
                    + (if ends_with_slash { 1int } else { 0int })
            && final(ser).view().index(path_start as int) == 0x2Fu8
            && final(ser).view().index(seg_start as int) == c0
            && final(ser).view().index((seg_start as int) + 1) == 0x3Au8
            && (ends_with_slash
                ==> final(ser).view().index((seg_start as int) + 2) == 0x2Fu8)
            && final(ser).view().subrange(0, seg_start as int)
                == old(ser).view().subrange(0, seg_start as int)
            && ((*final(has_host)) == false),
{
    ser.truncate(seg_start as usize);
    ser.push(c0);
    ser.push(0x3Au8);
    if ends_with_slash {
        ser.push(0x2Fu8);
    }
    if *has_host {
        *has_host = false;
    }
    proof {
        let f = final(ser).view();
        assert(machine_domain_byte(0x3Au8));
        assert(machine_domain_byte(0x2Fu8));
        assert(f.index(path_start as int) == 0x2Fu8);
        assert(f.index(seg_start as int) == c0);
        assert(f.index((seg_start as int) + 1) == 0x3Au8);
        if ends_with_slash {
            assert(f.index((seg_start as int) + 2) == 0x2Fu8);
        }
    }
}

/* ============================================================
 * The relative-path state (Origin: parse_path_start and
 * parse_path, parser.rs:1130-1292, on the UrlParser-context
 * restricted face; the PathSegmentSetter arms and the
 * SPECIAL_PATH_SEGMENT / PATH_SEGMENT sets belong to the
 * setters batch)
 * ============================================================ */

/// machine_domain of an arbitrary range of the input slice above the scan
/// base (the flush calls of the path scanner; the range-view composition
/// stays inside this lemma).
pub proof fn slice_range_machine_at(
    bytes: &[u8],
    base: usize,
    a: usize,
    b: usize,
)
    requires
        base <= a,
        a <= b,
        b <= bytes.view().len(),
        machine_domain(bytes.view().subrange(
            base as int, bytes.view().len() as int)),
    ensures
        machine_domain(bytes.view().subrange(a as int, b as int)),
{
    let n = bytes.view().len() as int;
    let rem = bytes.view().subrange(base as int, n);
    vstd::seq::lemma_seq_subrange_composition(
        bytes.view(), base as int, n, (a - base) as int, (b - base) as int);
    assert(rem.subrange((a - base) as int, (b - base) as int)
        == bytes.view().subrange(a as int, b as int));
    machine_domain_subrange(rem, (a - base) as int, (b - base) as int);
}

/* ============================================================
 * The relative-path state machine (Origin: parse_path and
 * parse_path_start, parser.rs:1130-1292, on the UrlParser-
 * context face; each loop obligation is phrased over the
 * remaining-suffix coordinates, the flush uses the shared
 * PATH encode, and the segment arms are the helpers above)
 * ============================================================ */

/// Origin Rust (parser.rs:1297-1303): the file scheme's leading-slash
/// compaction -- split the path region off, push one '/', and append the
/// region with its leading slashes trimmed (the "while path[0] is the
/// empty string, remove the first item" compaction of the spec).
pub exec fn file_tail_splice(ser: &mut Vec<u8>, path_start: usize)
    requires
        machine_domain(old(ser).view()),
        (path_start as int) < old(ser).view().len(),
        old(ser).view().index(path_start as int) == 0x2Fu8,
        (forall|j: int| (path_start as int) <= j
            && j < old(ser).view().len()
            ==> old(ser).view().index(j) != 0x3Fu8
                && old(ser).view().index(j) != 0x23u8),
        (old(ser).view().len() as int) <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(ser).view())
            && (path_start as int) < final(ser).view().len()
            && final(ser).view().index(path_start as int) == 0x2Fu8
            && (forall|j: int| (path_start as int) <= j
                && j < final(ser).view().len()
                ==> final(ser).view().index(j) != 0x3Fu8
                    && final(ser).view().index(j) != 0x23u8)
            && (exists|cut: int|
                (path_start as int) + 1 <= cut
                    && cut <= old(ser).view().len()
                    && final(ser).view()
                        == old(ser).view().subrange(0,
                            path_start as int)
                            + seq![0x2Fu8]
                            + old(ser).view().subrange(cut,
                                old(ser).view().len() as int)),
{
    let n0 = ser.len();
    // count the leading slashes of the path region (trim_start_matches)
    let mut lead: usize = path_start;
    while lead < n0 && ser[lead] == 0x2Fu8
        invariant
            (path_start as int) <= (lead as int) <= (n0 as int),
            (n0 as int) == (ser.view().len() as int),
            forall|j: int| (path_start as int) <= j && j < (lead as int)
                ==> ser.view().index(j) == 0x2Fu8,
        decreases n0 - lead,
    {
        lead += 1;
    }
    // splice: keep [0, path_start), one '/', then the trimmed region
    let suffix32_start = if lead > path_start { lead } else { path_start + 1 };
    let suffix = super::bytes_slice(ser, (suffix32_start) as u32, n0 as u32);
    ser.truncate(path_start);
    proof {
        let o = old(ser).view();
        assert(ser.view() == o.subrange(0, path_start as int));
        assert(machine_domain(ser.view()));
    }
    let ghost pre2 = ser.view();
    ser.push(0x2Fu8);
    proof {
        assert(ser.view() == pre2.push(0x2Fu8));
        assert(pre2.push(0x2Fu8) == pre2 + seq![0x2Fu8]);
        machine_domain_add(pre2, seq![0x2Fu8]);
    }
    vec_append_bytes(ser, &suffix);
    proof {
        let o = old(ser).view();
        let f = final(ser).view();
        assert(f.index(path_start as int) == 0x2Fu8);
        assert((suffix.view().len() as int)
            == (n0 as int) - (suffix32_start as int));
        assert((lead as int) >= (path_start as int) + 1);
        assert((f.len() as int)
            == (path_start as int) + 1 + (suffix.view().len() as int));
        assert((f.len() as int) == (path_start as int) + 1
            + (n0 as int) - (suffix32_start as int));
        assert((f.len() as int) <= (n0 as int));
        assert forall|j: int|
            (path_start as int) <= j && j < f.len()
            implies f.index(j) != 0x3Fu8
                && f.index(j) != 0x23u8 by {
            if (j as int) == (path_start as int) {
                assert(f.index(j) == 0x2Fu8);
            } else {
                let j2 = j - (path_start as int) - 1;
                assert(f.index(j) == suffix.view().index(j2));
                let jr = j2 + (suffix32_start as int);
                vstd::seq::lemma_seq_subrange_index(o,
                    (suffix32_start as int), (n0 as int), j2);
                assert(suffix.view().index(j2) == o.index(jr));
            }
        }
    }
}

/// The scanned-no-delimiter invariant of the path scanner pinned on the
/// indices of a subrange of the input buffer above the scan base.
pub proof fn subrange_avoids(
    bytes: &[u8],
    base: usize,
    a: usize,
    b: usize,
    hi: usize,
)
    requires
        base <= a,
        a <= b,
        b <= hi,
        hi <= bytes.view().len(),
        (forall|j: int| #![trigger bytes.view().index(j)]
            (base as int) <= j && j < (hi as int)
            ==> (bytes.view().index(j) != 0x3Fu8
                && bytes.view().index(j) != 0x23u8)),
    ensures
        (forall|j: int| #![trigger bytes.view().subrange(
            a as int, b as int).index(j)]
            0 <= j && j < ((b - a) as int)
            ==> (bytes.view().subrange(a as int, b as int).index(j)
                    != 0x3Fu8
                && bytes.view().subrange(a as int, b as int).index(j)
                    != 0x23u8)),
{
    let sub = bytes.view().subrange(a as int, b as int);
    assert forall|j: int| #![trigger sub.index(j)] 0 <= j && j < sub.len()
        implies sub.index(j) != 0x3Fu8 && sub.index(j) != 0x23u8 by {
        vstd::seq::lemma_seq_subrange_index(
            bytes.view(), a as int, b as int, j);
        assert(sub.index(j) == bytes.view().index(j + (a as int)));
    }
}

/// Appending a machine-domain, delimiter-free encode to the serialization
/// preserves the path region invariants (the flush sites of parse_path).
pub proof fn path_flush_preserve_region(
    pre: Seq<u8>,
    enc: Seq<u8>,
    path_start: int,
)
    requires
        machine_domain(pre),
        machine_domain(enc),
        path_start >= 0,
        (forall|j: int| #![trigger pre.index(j)]
            path_start <= j && j < pre.len()
            ==> (pre.index(j) != 0x3Fu8 && pre.index(j) != 0x23u8)),
        (forall|j: int| #![trigger enc.index(j)]
            0 <= j && j < enc.len()
            ==> (enc.index(j) != 0x3Fu8 && enc.index(j) != 0x23u8)),
    ensures
        machine_domain(pre + enc),
        (forall|j: int| #![trigger (pre + enc).index(j)]
            path_start <= j && j < (pre + enc).len()
            ==> ((pre + enc).index(j) != 0x3Fu8
                && (pre + enc).index(j) != 0x23u8)),
{
    machine_domain_add(pre, enc);
    assert forall|j: int| #![trigger (pre + enc).index(j)]
        path_start <= j && j < (pre + enc).len()
        implies (pre + enc).index(j) != 0x3Fu8
            && (pre + enc).index(j) != 0x23u8 by {
        if (j >= pre.len()) {
            vstd::seq::lemma_seq_add_index2(pre, enc, j);
            let j2 = (j - pre.len()) as int;
            assert((pre + enc).index(j) == enc.index(j2));
        } else {
            vstd::seq::lemma_seq_add_index1(pre, enc, j);
            assert((pre + enc).index(j) == pre.index(j));
        }
    }
}

impl Parser<'_> {

/// Origin Rust (parser.rs:1165-1292): pub fn parse_path(scheme_type,
///   has_host: &mut bool, path_start, input) -> Input -- the relative-path
/// state: scan each '/'-terminated segment, percent-encode the pending run
/// against the PATH set (the PathSegmentSetter branches and the
/// SPECIAL_PATH_SEGMENT / PATH_SEGMENT sets are the setters face), match
/// the written segment against the dot forms and the windows drive letter,
/// and run the crop arms; the file scheme's tail compaction runs at exit.
/// Entry shapes: the caller pre-wrote the '/' anchor (the push-branches),
/// or the remaining input starts with '/' and the anchor is written by the
/// first segment's own slash step (performed inline, since that first
/// segment is then empty and every arm is a no-op on it).
pub exec fn parse_path<'i>(
    &mut self,
    scheme_type: SchemeType,
    path_start: usize,
    has_host: &mut bool,
    input: Input<'i>,
) -> (r: Input<'i>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        (((old(self).serialization.view().len() as int)
            > (path_start as int))
            && old(self).serialization.view().index(path_start as int)
                == 0x2Fu8)
        || (((old(self).serialization.view().len() as int)
            == (path_start as int))
            && input_rem(&input).len() > 0
            && input_rem(&input).index(0) == 0x2Fu8),
        (forall|j: int| (path_start as int) <= j
            && j < old(self).serialization.view().len()
            ==> old(self).serialization.view().index(j) != 0x3Fu8
                && old(self).serialization.view().index(j) != 0x23u8),
        old(self).serialization.view().len()
            + 5 * (input_rem(&input).len() as int) + 32
            <= 0xFFFF_FFFF,
    ensures
        ({
            let before = old(self).serialization.view();
            let serf = final(self).serialization.view();
            let s = input_rem(&input);
            &&& input_wf(&r)
            &&& ((input_rem(&r).len() as int)
                <= (input_rem(&input).len() as int))
            &&& (input_rem(&r).len() == 0
                || input_rem(&r).index(0) == 0x3Fu8
                || input_rem(&r).index(0) == 0x23u8)
            &&& machine_domain(serf)
            &&& (serf.len() as int) >= (path_start as int)
            &&& (((before.len() as int)
                    >= (path_start as int))
                ==> ((serf.len() as int)
                    > (path_start as int)))
            &&& ((serf.len() as int) > (path_start as int)
                ==> serf.index(path_start as int) == 0x2Fu8)
            &&& (forall|j: int| (path_start as int) <= j
                && j < serf.len()
                ==> serf.index(j) != 0x3Fu8
                    && serf.index(j) != 0x23u8)
            &&& (forall|j: int| 0 <= j && j < (path_start as int)
                ==> serf.index(j) == before.index(j))
            &&& (serf.len() as int)
                <= before.len() + 5 * (s.len() as int) + 6
            &&& (((*final(has_host)) == false)
                || ((*final(has_host)) == (*old(has_host))))
            &&& (final(self).context == old(self).context)
        }),
{
    let sbuf = input.bytes;
    let n = sbuf.len();
    let ghost before = self.serialization.view();
    let ghost hh0: bool = *has_host;
    let ghost rem0 = input_rem(&input);
    proof {
        // the base pin: the remaining suffix is the buffer's suffix, so
        // flush-local machine-domain and scan facts translate (see
        // slice_range_machine_at and subrange_avoids)
        assert(rem0 == sbuf.view().subrange(input.pos as int,
            sbuf.view().len() as int));
        assert(rem0.len() == (sbuf.view().len() as int)
            - (input.pos as int));
        assert(machine_domain(sbuf.view().subrange(input.pos as int,
            sbuf.view().len() as int)));
        assert((n as int) == (sbuf.view().len() as int));
        assert((self.serialization.len() as int)
            == (self.serialization.view().len() as int));
    }
    let mut cur: usize = input.pos;
    if self.serialization.len() == path_start {
        // the entry-normalization arm: the '/' head writes the anchor (the
        // empty first segment's slash step, inline)
        let ghost pre = self.serialization.view();
        self.serialization.push(0x2Fu8);
        proof {
            assert(self.serialization.view() == pre.push(0x2Fu8));
            assert(pre.push(0x2Fu8) == pre + seq![0x2Fu8]);
            machine_domain_add(pre, seq![0x2Fu8]);
            assert(self.serialization.view().len()
                == (path_start as int) + 1);
            assert(self.serialization.view().index(
                (path_start as int)) == 0x2Fu8);
        }
        cur = input.pos + 1;
    } else {
        proof {
            // the general pre-written shape: the anchor '/' at or
            // below the entry end (the entry region may itself carry
            // path bytes, the pop/merge arms' shape)
            assert((self.serialization.view().len() as int)
                > (path_start as int));
            assert(self.serialization.view()
                .index(path_start as int) == 0x2Fu8);
        }
    }
    let mut seg_start: usize = self.serialization.len();
    let mut pending: usize = cur;
    let mut st: u8 = 0;
    let mut done: bool = false;
    while !done
        invariant
            before == old(self).serialization.view(),
            machine_domain(self.serialization.view()),
            (path_start as int) < self.serialization.view().len(),
            self.serialization.view().index(path_start as int) == 0x2Fu8,
            self.serialization.view().subrange(0, path_start as int)
                == before.subrange(0, path_start as int),
            (forall|j: int| (path_start as int) <= j
                && j < self.serialization.view().len()
                ==> self.serialization.view().index(j) != 0x3Fu8
                    && self.serialization.view().index(j) != 0x23u8),
            input.pos <= pending <= cur,
            cur <= n,
            (n as int) == (sbuf.view().len() as int),
            (self.serialization.len() as int)
                == (self.serialization.view().len() as int),
            machine_domain(sbuf.view().subrange(input.pos as int,
                sbuf.view().len() as int)),
            (path_start as int) + 1 <= (seg_start as int),
            (*has_host) == hh0 || (*has_host) == false,
            (self.serialization.view().len() as int)
                + 4 * ((cur - pending) as int)
                <= before.len() + 5 * ((cur - input.pos) as int) + 4,
            (self.serialization.view().len() as int)
                + 4 * ((cur - pending) as int)
                + 5 * ((n - cur) as int) + 10
                <= 0xFFFF_FFFF,

            st == 0 || st == 1 || st == 2 || st == 3,
            (done == true) ==> (st == 2 || st == 3),
                        (st == 2) ==> (cur < n
                && (sbuf.view().index(cur as int) == 0x3Fu8
                    || sbuf.view().index(cur as int) == 0x23u8)),
            (st == 3) ==> cur == n,
            (forall|j: int| input.pos as int <= j < cur as int
                ==> sbuf.view().index(j) != 0x3Fu8
                    && sbuf.view().index(j) != 0x23u8),
        decreases (if done { 0int } else { 1int }), (n as int) - (cur as int),
    {
        // segment head (parser.rs:1171)
        seg_start = self.serialization.len();
        pending = cur;
        st = 0;
        let ghost hc: int = cur as int;
        while st == 0
            invariant
                (cur as int) >= hc,
                before == old(self).serialization.view(),
                machine_domain(self.serialization.view()),
                (path_start as int) < self.serialization.view().len(),
                self.serialization.view().subrange(0, path_start as int)
                    == before.subrange(0, path_start as int),
                self.serialization.view().index(path_start as int)
                    == 0x2Fu8,
                (forall|j: int| (path_start as int) <= j
                    && j < self.serialization.view().len()
                    ==> self.serialization.view().index(j) != 0x3Fu8
                        && self.serialization.view().index(j) != 0x23u8),
                input.pos <= pending <= cur,
                cur <= n,
                (n as int) == (sbuf.view().len() as int),
                (path_start as int) + 1 <= (seg_start as int),
                (seg_start as int) <= self.serialization.view().len(),
                (self.serialization.len() as int)
                    == (self.serialization.view().len() as int),
                machine_domain(sbuf.view().subrange(input.pos as int,
                    sbuf.view().len() as int)),
                (self.serialization.view().len() as int)
                    + 4 * ((cur - pending) as int)
                    <= before.len()
                        + 5 * ((cur - input.pos) as int) + 4,
                (self.serialization.view().len() as int)
                    + 4 * ((cur - pending) as int)
                    + 5 * ((n - cur) as int) + 10
                    <= 0xFFFF_FFFF,

                (st == 1) ==> ((cur as int) >= hc + 1
                    && (seg_start as int) + 1
                        <= (self.serialization.view().len() as int)),
                (st == 1) ==> (self.serialization.view().len() > 0
                    && self.serialization.view().index(
                        self.serialization.view().len() as int - 1)
                        == 0x2Fu8),
                (st == 2) ==> (cur < n
                    && (sbuf.view().index(cur as int) == 0x3Fu8
                        || sbuf.view().index(cur as int) == 0x23u8)),
                (st == 3) ==> cur == n,
                (forall|j: int| input.pos as int <= j < cur as int
                    ==> sbuf.view().index(j) != 0x3Fu8
                        && sbuf.view().index(j) != 0x23u8),
            st == 0 || st == 1 || st == 2 || st == 3,
            decreases (if st == 0 { 1int } else { 0int }), n - cur,
        {
            // the flush of the pending run [pending, cur) + the encoded
            // append's region facts (the flush is shared by every
            // delimiter arm)
            if cur >= n {
                // EOF: flush the pending run (parser.rs:1180-1184)
                if pending < cur {
                    proof {
                        slice_range_machine_at(sbuf, input.pos,
                            pending, cur);
                        subrange_avoids(sbuf, input.pos, pending, cur,
                            cur);
                        enc_seq_no_delims(
                            sbuf.view().subrange(pending as int,
                                cur as int), EncodeSet::Path);
                    }
                    let ghost preF = self.serialization.view();
                    extend_percent_encode_at(&mut self.serialization,
                        sbuf, pending, cur, EncodeSet::Path);
                    proof {
                        let e = sbuf.view().subrange(pending as int,
                            cur as int);
                        enc_seq_machine(e, EncodeSet::Path);
                        path_flush_preserve_region(preF,
                            enc_seq(e, EncodeSet::Path),
                            path_start as int);
                        enc_seq_len_bound(e, EncodeSet::Path);
                        assert(self.serialization.view().len()
                            == (preF.len() as int)
                                + (enc_seq(e, EncodeSet::Path).len() as int));
                        assert((self.serialization.view().len() as int)
                            <= (preF.len() as int)
                                + 3 * ((cur - pending) as int));
                    }
                }
                pending = cur;
                st = 3;
                proof {
                    assert((self.serialization.view().len() as int)
                        + 4 * ((cur - pending) as int)
                        <= (before.len() as int)
                            + 5 * ((cur - input.pos) as int) + 4);
                }
            } else {
                let c = sbuf[cur];
                proof {
                    assert(sbuf.view().index(cur as int) == c);
                }
                if c == 0x2Fu8
                    || (c == 0x5Cu8 && scheme_type.is_special())
                {
                    // '/' (or the special '\'): flush and push the
                    // separator (parser.rs:1185-1196)
                    if pending < cur {
                        proof {
                            slice_range_machine_at(sbuf, input.pos,
                                pending, cur);
                            subrange_avoids(sbuf, input.pos, pending,
                                cur, cur);
                            enc_seq_no_delims(
                                sbuf.view().subrange(pending as int,
                                    cur as int), EncodeSet::Path);
                        }
                        let ghost preF = self.serialization.view();
                        extend_percent_encode_at(&mut self.serialization,
                            sbuf, pending, cur, EncodeSet::Path);
                        proof {
                            let e = sbuf.view().subrange(pending as int,
                                cur as int);
                            enc_seq_machine(e, EncodeSet::Path);
                            path_flush_preserve_region(preF,
                                enc_seq(e, EncodeSet::Path),
                                path_start as int);
                            enc_seq_len_bound(e, EncodeSet::Path);
                            assert(self.serialization.view().len()
                                == (preF.len() as int)
                                    + (enc_seq(e, EncodeSet::Path).len()
                                        as int));
                        }
                    }
                    proof {
                        assert(machine_domain_byte(0x2Fu8));
                    }
                    let ghost pre2 = self.serialization.view();
                    self.serialization.push(0x2Fu8);
                    proof {
                        assert(self.serialization.view()
                            == pre2.push(0x2Fu8));
                        assert(pre2.push(0x2Fu8) == pre2 + seq![0x2Fu8]);
                        machine_domain_add(pre2, seq![0x2Fu8]);
                        let f = self.serialization.view();
                        assert forall|j: int|
                            (path_start as int) <= j && j < f.len()
                            implies f.index(j) != 0x3Fu8
                                && f.index(j) != 0x23u8 by {
                            if j == (f.len() as int) - 1 {
                                assert(f.index(j) == 0x2Fu8);
                            } else {
                                assert(f.index(j) == pre2.index(j));
                            }
                        }
                        assert(f.len() > 0);
                        assert(f.index(f.len() as int - 1) == 0x2Fu8);
                    }
                    cur += 1;
                    pending = cur;
                    st = 1;
                    proof {
                        assert(st == 1);
                        assert((cur as int) >= hc + 1);
                        assert((seg_start as int) + 1
                            <= (self.serialization.view().len() as int));
                        assert((self.serialization.view().len() as int)
                            + 4 * ((cur as int) - (pending as int))
                            <= (before.len() as int)
                                + 5 * ((cur as int)
                                    - (input.pos as int)) + 4);
                    }
                } else if c == 0x3Fu8 || c == 0x23u8 {
                    // '?' or '#': the query/fragment boundary
                    // (parser.rs:1197-1206)
                    if pending < cur {
                        proof {
                            slice_range_machine_at(sbuf, input.pos,
                                pending, cur);
                            subrange_avoids(sbuf, input.pos, pending,
                                cur, cur);
                            enc_seq_no_delims(
                                sbuf.view().subrange(pending as int,
                                    cur as int), EncodeSet::Path);
                        }
                        let ghost preF = self.serialization.view();
                        extend_percent_encode_at(&mut self.serialization,
                            sbuf, pending, cur, EncodeSet::Path);
                        proof {
                            let e = sbuf.view().subrange(pending as int,
                                cur as int);
                            enc_seq_machine(e, EncodeSet::Path);
                            path_flush_preserve_region(preF,
                                enc_seq(e, EncodeSet::Path),
                                path_start as int);
                            enc_seq_len_bound(e, EncodeSet::Path);
                            assert(self.serialization.view().len()
                                == (preF.len() as int)
                                    + (enc_seq(e, EncodeSet::Path).len()
                                        as int));
                        }
                    }
                    pending = cur;
                    st = 2;
                    proof {
                        assert((self.serialization.view().len() as int)
                            + 4 * ((cur - pending) as int)
                            <= (before.len() as int)
                                + 5 * ((cur - input.pos) as int) + 4);
                    }
                } else {
                    // default: the file drive-letter insert
                    // (parser.rs:1217-1233); on other bytes just advance
                    if scheme_type.is_file()
                        && self.serialization.len() > path_start
                        && is_normalized_win_drive_at(
                            &self.serialization, path_start + 1)
                    {
                        if pending < cur {
                            proof {
                                slice_range_machine_at(sbuf, input.pos,
                                    pending, cur);
                                subrange_avoids(sbuf, input.pos,
                                    pending, cur, cur);
                                enc_seq_no_delims(
                                    sbuf.view().subrange(
                                        pending as int, cur as int),
                                    EncodeSet::Path);
                            }
                            let ghost preF =
                                self.serialization.view();
                            extend_percent_encode_at(
                                &mut self.serialization, sbuf, pending,
                                cur, EncodeSet::Path);
                            proof {
                                let e = sbuf.view().subrange(
                                    pending as int, cur as int);
                                enc_seq_machine(e, EncodeSet::Path);
                                path_flush_preserve_region(preF,
                                    enc_seq(e, EncodeSet::Path),
                                    path_start as int);
                                enc_seq_len_bound(e, EncodeSet::Path);
                                assert(self.serialization.view().len()
                                    == (preF.len() as int)
                                        + (enc_seq(e, EncodeSet::Path).len()
                                            as int));
                            }
                        }
                        proof {
                            assert(machine_domain_byte(0x2Fu8));
                        }
                        let ghost pre2 = self.serialization.view();
                        self.serialization.push(0x2Fu8);
                        proof {
                            assert(self.serialization.view()
                                == pre2.push(0x2Fu8));
                            assert(pre2.push(0x2Fu8) == pre2
                                + seq![0x2Fu8]);
                            machine_domain_add(pre2, seq![0x2Fu8]);
                            let f = self.serialization.view();
                            assert forall|j: int|
                                (path_start as int) <= j
                                    && j < f.len()
                                implies f.index(j) != 0x3Fu8
                                    && f.index(j) != 0x23u8 by {
                                if j == (f.len() as int) - 1 {
                                    assert(f.index(j) == 0x2Fu8);
                                } else {
                                    assert(f.index(j) == pre2.index(j));
                                }
                            }
                        }
                        seg_start += 1;
                        pending = cur;
                    }
                    cur += 1;
                    proof {
                        assert((self.serialization.view().len() as int)
                            + 4 * ((cur as int) - (pending as int))
                            <= (before.len() as int)
                                + 5 * ((cur as int)
                                    - (input.pos as int)) + 4);
                    }
                }
            }
        }
        // segment matches (parser.rs:1235-1317)
        let ends_with_slash = (st == 1);
        let seg_end: usize = self.serialization.len()
            - (if ends_with_slash { 1 } else { 0 });
        let segv = super::bytes_slice(&self.serialization,
            seg_start as u32, seg_end as u32);
        if segment_is_double_dot(&segv) {
            proof {
                // a matched dot form has at least two bytes, so the run
                // has been written and the entry anchor exists
                vstd::seq::lemma_seq_subrange_len(
                    self.serialization.view(), seg_start as int,
                    seg_end as int);
                dd_form_len(segv.view());
                assert(segv.view().len()
                    == (seg_end as int) - (seg_start as int));
                assert(seg_end >= seg_start + 2);
                assert(self.serialization.view().len()
                    > (path_start as int));
                assert((seg_start as int)
                    <= self.serialization.view().len());
                assert(machine_domain(self.serialization.view()));
            }
            let ghost preArm = self.serialization.view();
            segment_dd_arm(&mut self.serialization, scheme_type.is_file(),
                path_start, seg_start, ends_with_slash);
            proof {
                let f = self.serialization.view();
                assert((preArm.len() as int) >= (seg_start as int) + 2);
                assert((f.len() as int) <= (preArm.len() as int) - 1);
                assert((f.len() as int) <= (preArm.len() as int));
            }
        } else if segment_is_single_dot(&segv) {
            proof {
                vstd::seq::lemma_seq_subrange_len(
                    self.serialization.view(), seg_start as int,
                    seg_end as int);
                sd_form_len(segv.view());
                assert(segv.view().len()
                    == (seg_end as int) - (seg_start as int));
                assert(seg_end >= seg_start + 1);
                assert(self.serialization.view().len()
                    > (path_start as int));
            }
            let ghost preArm = self.serialization.view();
            segment_sd_arm(&mut self.serialization, path_start, seg_start);
            proof {
                let f = self.serialization.view();
                assert((f.len() as int) <= (preArm.len() as int));
            }
        } else if scheme_type.is_file()
            && seg_start == path_start + 1
            && win_drive_seg_at(&self.serialization, seg_start, seg_end)
        {
            // the windows drive-letter replacement (parser.rs:1266-1296)
            proof {
                assert(seg_end == seg_start + 2);
                assert(self.serialization.view().len()
                    > (seg_start as int) + 1);
                assert((seg_start as int) + 2
                    <= (self.serialization.view().len() as int));
                assert((self.serialization.len() as int)
                    == (self.serialization.view().len() as int));
            }
            let c0 = self.serialization[seg_start];
            proof {
                assert(self.serialization.view().index(
                    (seg_start as int)) == c0);
            }
            let ghost preArm = self.serialization.view();
            segment_drive_arm(&mut self.serialization, has_host, path_start,
                seg_start as u32, (seg_end - seg_start) as u32, c0,
                ends_with_slash);
            proof {
                let f = self.serialization.view();
                assert((f.len() as int) <= (preArm.len() as int));
            }
            proof {
                // the replaced drive region keeps the delimiter freedom
                let sv = self.serialization.view();
                assert forall|j: int|
                    (path_start as int) <= j && j < sv.len()
                    implies sv.index(j) != 0x3Fu8
                        && sv.index(j) != 0x23u8 by {
                    if (j as int) == (seg_start as int) {
                        assert(sv.index(j) == c0);
                    } else if (j as int) == (seg_start as int) + 1 {
                        assert(sv.index(j) == 0x3Au8);
                    } else if ((j as int)
                        == (seg_start as int) + 2 && ends_with_slash) {
                        assert(sv.index(j) == 0x2Fu8);
                    }
                }
            }
        }
        done = (st != 1);
        proof {
            if !done {
                assert((cur as int) >= hc + 1);
                // a continuing iteration consumed at least the separator,
                // so the remaining length strictly decreased: the head
                // value of cur for this iteration was exactly hc
                assert((n as int) - (cur as int)
                    < (n as int) - hc);
                assert((cur as int) > hc);
            }
            // the growth and budget invariants survive the arms
            let sv = self.serialization.view();
            assert((sv.len() as int)
                <= before.len()
                    + 5 * ((cur - input.pos) as int) + 4);
            assert((sv.len() as int) + 3 * ((n - pending) as int) + 10
                <= 0xFFFF_FFFF);
        }
    }
    // the file tail compaction (parser.rs:1297-1303)
    if scheme_type.is_file() {
        file_tail_splice(&mut self.serialization, path_start);
    } else {
        proof {
            let sv = self.serialization.view();
            assert((sv.len() as int) < 0x1_0000_0000);
        }
    }
    let r = Input { bytes: sbuf, pos: cur };
    proof {
        let before = old(self).serialization.view();
        let serf = self.serialization.view();
        rem_shift(sbuf, input.pos as int, (cur - input.pos) as int);
        machine_domain_subrange(rem0, (cur - input.pos) as int,
            rem0.len() as int);
        assert(machine_domain(input_rem(&r)));
        assert(input_ok(&r));
        assert((input_rem(&r).len() as int) <= 0xFFFF_FFFF);
        assert((sbuf.view().len() as int) <= 0xFFFF_FFFF);
        assert(input_wf(&r));
        if cur < n {
            // exit state: st == 3 forces cur == n, so cur < n means the
            // st == 2 terminator face
            assert((cur as int) < (sbuf.view().len() as int));
            assert(!(st == 3));
            assert(sbuf.view().index(cur as int) == 0x3Fu8
                || sbuf.view().index(cur as int) == 0x23u8);
        }
        assert((serf.len() as int)
            <= before.len() + 5 * ((cur - input.pos) as int) + 4);
        assert((serf.len() as int)
            <= before.len() + 5 * (rem0.len() as int) + 6);
        assert(cur - input.pos <= rem0.len());
        if (before.len() as int) >= (path_start as int) {
            // the anchor survives the whole scan and the file-tail
            // splice: the path region never shrinks to the bare
            // path_start (the loop pins path_start < len, the splice
            // keeps the '/' anchor byte -- the entry pushed it when
            // it was missing, else it was pre-written)
            assert((serf.len() as int) > (path_start as int));
        }
        // prefix byte permanence reads off the invariant's subrange
        // equality (the file tail keeps the same region)
        assert forall|j: int| 0 <= j && j < (path_start as int)
            implies serf.index(j) == before.index(j) by {
            vstd::seq::lemma_seq_subrange_index(serf, 0,
                path_start as int, j);
            vstd::seq::lemma_seq_subrange_index(before, 0,
                path_start as int, j);
        }
    }
    r
}

/// Origin Rust (parser.rs:1130-1163): pub fn parse_path_start(scheme_type,
///   has_host: &mut bool, input) -> Input -- the path-start state after the
/// authority: a special scheme always gets a '/'-prefixed path (its just
/// written host run or port digits never end in '/'), a non-special scheme
/// with a '?'/'#' head returns the input untouched (the caller's
/// query/fragment state), otherwise a '/' is pushed when the head is
/// neither EOF nor '/', and the scan proceeds with parse_path.
pub exec fn parse_path_start<'i>(
    &mut self,
    scheme_type: SchemeType,
    has_host: &mut bool,
    input: Input<'i>,
    path_start: usize,
) -> (r: (Input<'i>, bool))
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        (path_start as int) == old(self).serialization.view().len(),
        (forall|j: int| (path_start as int) <= j
            && j < old(self).serialization.view().len()
            ==> old(self).serialization.view().index(j) != 0x3Fu8
                && old(self).serialization.view().index(j) != 0x23u8),
        (is_special(scheme_type) ==> (
            old(self).serialization.view().len() == 0
            || old(self).serialization.view()
                .index(old(self).serialization.view().len() as int - 1)
                != 0x2Fu8)),
        old(self).serialization.view().len()
            + 5 * (input_rem(&input).len() as int) + 38
            <= 0xFFFF_FFFF,
    ensures
        ({
            let s = input_rem(&input);
            let remr = input_rem(&(r.0));
            let before = old(self).serialization.view();
            let serf = final(self).serialization.view();
            &&& input_wf(&(r.0))
            &&& ((input_rem(&(r.0)).len() as int)
                <= (input_rem(&input).len() as int))
            &&& machine_domain(serf)
            &&& (serf.len() as int) >= (path_start as int)
            &&& (forall|j: int| 0 <= j && j < (path_start as int)
                ==> serf.index(j) == before.index(j))
            &&& (forall|j: int| (path_start as int) <= j
                && j < serf.len()
                ==> serf.index(j) != 0x3Fu8
                    && serf.index(j) != 0x23u8)
            &&& (remr.len() == 0
                || remr.index(0) == 0x3Fu8
                || remr.index(0) == 0x23u8)
            &&& (serf.len() as int)
                <= before.len() + 5 * (s.len() as int) + 7
            &&& ((serf.len() as int) > (path_start as int)
                ==> serf.index(path_start as int) == 0x2Fu8)
            &&& (((*final(has_host)) == false)
                || ((*final(has_host)) == (*old(has_host))))
            &&& (final(self).context == old(self).context)
        }),
{
    let special = scheme_type.is_special();
    let (maybe_c, rest) = input.split_first();
    if special {
        // A special URL always has a non-empty path: push '/' when the
        // serialization does not end with one (parser.rs:1141-1144); at
        // this state it never does (the host run and port digits exclude
        // a trailing '/', and the userinfo arm leaves '@' or ':' bytes),
        // so the else arm of the upstream conditional is dead here.
        if self.serialization.len() == 0
            || self.serialization[self.serialization.len() - 1] != 0x2Fu8
        {
            proof {
                assert(machine_domain_byte(0x2Fu8));
            }
            let ghost pre = self.serialization.view();
            self.serialization.push(0x2Fu8);
            proof {
                assert(self.serialization.view() == pre.push(0x2Fu8));
                assert(pre.push(0x2Fu8) == pre + seq![0x2Fu8]);
                machine_domain_add(pre, seq![0x2Fu8]);
                let f = self.serialization.view();
                assert forall|j: int| (path_start as int) <= j
                    && j < f.len()
                    implies f.index(j) != 0x3Fu8
                        && f.index(j) != 0x23u8 by {
                    if (path_start as int) == (f.len() as int) - 1 {
                        assert(f.index(j) == 0x2Fu8);
                    } else {
                        assert(f.index(j) == pre.index(j));
                    }
                }
            }
            if maybe_c == Some(0x2Fu8) || maybe_c == Some(0x5Cu8) {
                proof {
                    // the head separator is absorbed into the push
                    // (parser.rs:1146-1148): the rest argument is one
                    // byte short of the original remaining input, and
                    // the pushed '/' leads the path region
                    let s = input_rem(&input);
                    let sr = input_rem(&rest);
                    assert(sr == s.subrange(1, s.len() as int));
                    assert(sr.len() == s.len() - 1);
                    let f = self.serialization.view();
                    assert(f.len() as int == (path_start as int) + 1);
                    assert(f.index(path_start as int) == 0x2Fu8);
                }
                let ghost preHH: bool = *has_host;
                let rx = self.parse_path(scheme_type, path_start,
                    has_host, rest);
            proof {
                assert((*has_host) == false
                    || (*has_host) == preHH);
                let s = input_rem(&input);
                let remr = input_rem(&rx);
                let before = old(self).serialization.view();
                let serf = self.serialization.view();
                assert(input_wf(&rx));
                assert(machine_domain(serf));
                assert(remr.len() == 0
                    || remr.index(0) == 0x3Fu8
                    || remr.index(0) == 0x23u8);
                assert(serf.len() as int
                    <= before.len() + 5 * (s.len() as int) + 7);
                assert(serf.len() as int > path_start as int
                    ==> serf.index(path_start as int) == 0x2Fu8);
                assert((*has_host) == false
                    || (*has_host) == (*old(has_host)));
            }
                return (rx, *has_host);
            }
            proof {
                let s = input_rem(&input);
                let f = self.serialization.view();
                assert(f.len() as int == (path_start as int) + 1);
                assert(f.index(path_start as int) == 0x2Fu8);
                assert(f.len() as int + 5 * (s.len() as int) + 32
                    == old(self).serialization.view().len() as int
                        + 5 * (s.len() as int) + 33);
            }
            let ghost preHH: bool = *has_host;
            let rx = self.parse_path(scheme_type, path_start, has_host,
                input);
            proof {
                assert((*has_host) == false
                    || (*has_host) == preHH);
                let s = input_rem(&input);
                let remr = input_rem(&rx);
                let before = old(self).serialization.view();
                let serf = self.serialization.view();
                assert(input_wf(&rx));
                assert(machine_domain(serf));
                assert(remr.len() == 0
                    || remr.index(0) == 0x3Fu8
                    || remr.index(0) == 0x23u8);
                assert(serf.len() as int
                    <= before.len() + 5 * (s.len() as int) + 7);
                assert(serf.len() as int > path_start as int
                    ==> serf.index(path_start as int) == 0x2Fu8);
                assert((*has_host) == false
                    || (*has_host) == (*old(has_host)));
            }
            return (rx, *has_host);
        } else {
            proof {
                // ends_with('/') is impossible at this state (the
                // requires conjunct pins the serialized tail byte away
                // from '/'), so this arm of the upstream conditional is
                // dead
                let f = self.serialization.view();
                assert(f.len() > 0);
                assert(f.index(f.len() as int - 1) == 0x2Fu8);
                assert(false);
            }
            return (input, *has_host);
        }
    }
    // non-special: '?' or '#' head is the caller's query/fragment state
    if maybe_c == Some(0x3Fu8) || maybe_c == Some(0x23u8) {
        return (input, *has_host);
    }
    // otherwise push '/' unless the head already is one (or EOF)
    let ghost pre2 = self.serialization.view();
    let mut pushed: bool = false;
    if maybe_c.is_some() && maybe_c != Some(0x2Fu8) {
        proof {
            assert(machine_domain_byte(0x2Fu8));
        }
        self.serialization.push(0x2Fu8);
        proof {
            let pre = pre2;
            assert(self.serialization.view() == pre.push(0x2Fu8));
            assert(pre.push(0x2Fu8) == pre + seq![0x2Fu8]);
            machine_domain_add(pre, seq![0x2Fu8]);
            let f = self.serialization.view();
            assert(f.index((f.len() as int) - 1) == 0x2Fu8);
            assert(forall|j: int| (path_start as int) <= j
                && j < f.len()
                ==> f.index(j) != 0x3Fu8
                    && f.index(j) != 0x23u8) by {
                assert forall|j: int| (path_start as int) <= j
                    && j < f.len()
                    implies f.index(j) != 0x3Fu8
                        && f.index(j) != 0x23u8 by {
                    if (path_start as int) == (f.len() as int) - 1 {
                        assert(f.index(j) == 0x2Fu8);
                    } else {
                        assert(j < pre.len());
                        assert(f.index(j) == pre.index(j));
                        assert(pre.index(j) != 0x3Fu8
                            && pre.index(j) != 0x23u8);
                    }
                }
            }
        }
        pushed = true;
    }
    if input.is_empty() && self.serialization.len() == path_start {
        // EOF with no pushed '/': the upstream parse_path loop body is a
        // structural no-op on an empty input for a non-special scheme
        // (no segment arm can fire), which this early return mirrors
        return (input, *has_host);
    }
    proof {
        let f = self.serialization.view();
        let s = input_rem(&input);
        if pushed {
            // entry disjunct A: the pushed byte is the anchor at
            // path_start
            assert(f.len() as int == (path_start as int) + 1);
            assert(f.index(path_start as int) == 0x2Fu8);
            assert(f.len() as int + 5 * (s.len() as int) + 32
                == old(self).serialization.view().len() as int
                    + 5 * (s.len() as int) + 33);
        } else {
            assert(f == pre2);
            assert(f.len() as int == (path_start as int));
            if !maybe_c.is_none() {
                // no push with a nonempty head: the head must be '/'
                assert(maybe_c == Some(0x2Fu8));
                assert(s.len() > 0);
                assert(s.index(0) == 0x2Fu8);
                assert(f.len() as int + 5 * (s.len() as int) + 32
                    <= old(self).serialization.view().len() as int
                        + 5 * (s.len() as int) + 38);
            } else {
                // EOF heads reach here only when a '/' was pushed
                // (the early return above already took the
                // untouched-EOF case)
                assert(false);
            }
        }
    }
        let ghost preHH: bool = *has_host;
    let rx = self.parse_path(scheme_type, path_start, has_host, input);
            proof {
                assert((*has_host) == false
                    || (*has_host) == preHH);
                let s = input_rem(&input);
                let remr = input_rem(&rx);
                let before = old(self).serialization.view();
                let serf = self.serialization.view();
                assert(input_wf(&rx));
                assert(machine_domain(serf));
                assert(remr.len() == 0
                    || remr.index(0) == 0x3Fu8
                    || remr.index(0) == 0x23u8);
                assert(serf.len() as int
                    <= before.len() + 5 * (s.len() as int) + 7);
                assert(serf.len() as int > path_start as int
                    ==> serf.index(path_start as int) == 0x2Fu8);
                assert((*has_host) == false
                    || (*has_host) == (*old(has_host)));
            }
    (rx, *has_host)
}

/* ============================================================
 * The authority assembly (Origin: after_double_slash,
 * parser.rs:828-848), split into two phase records so the fn's
 * aggregate queries fit: the userinfo phase (the "//" push, the
 * peel, the class transport) and the host/port phase (the to_u32
 * offsets, the deep-host assembly, the empty-host guard). The
 * phase contracts publish DIGESTED forms of the callee posts -- only
 * what the wrap-up seam needs, never the raw three-arm disjunctions.
 * ============================================================ */

/// Phase A of the authority assembly (Origin: parser.rs:829-835): the
/// "//" push of the authority state, the userinfo peel, and the
/// host_split_class transport through the peel (the choose over the
/// arm A/B/C forms of parse_userinfo happens INSIDE this body).
pub exec fn ads_authority_uinfo<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
    scheme_end: u32,
) -> (r: Result<(u32, Input<'i>), ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        1 <= (scheme_end as int),
        (old(self).serialization.view().len() as int)
            == (scheme_end as int) + 1,
        super::is_ascii_alpha(
            old(self).serialization.view().index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(
                old(self).serialization.view().index(j))),
        old(self).serialization.view().index(scheme_end as int)
            == 0x3Au8,
        scheme_type == scheme_type_of(
            old(self).serialization.view()
                .subrange(0, scheme_end as int)),
        authority_entry_class(input_rem(&input),
            is_special(scheme_type)),
        (old(self).serialization.view().len() as int)
            + 3 * (input_rem(&input).len() as int) + 8
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        final(self).context == old(self).context,
        r.is_err()
            ==> (r == Err(ParseError::EmptyHost)),
        ({
            let serf = final(self).serialization.view();
            let o = old(self).serialization.view();
            let se = scheme_end as int;
            &&& (r.is_ok()
                ==> ((serf.len() as int)
                    <= o.len()
                        + 3 * (input_rem(&input).len() as int) + 4
                    && (serf.len() as int) >= se + 3
                    && (forall|j: int| 0 <= j && j < o.len()
                        ==> serf.index(j) == o.index(j))
                    && serf.index(se + 1) == 0x2Fu8
                    && serf.index(se + 2) == 0x2Fu8))
            &&& (r.is_ok() ==> ({
                let (ue, rest) = r.unwrap();
                let ue_i = ue as int;
                let ex_len = serf.len() as int;
                let special = is_special(scheme_type);
                &&& input_wf(&rest)
                &&& host_split_class(input_rem(&rest), special)
                &&& ((input_rem(&rest).len() as int)
                    <= (input_rem(&input).len() as int))
                &&& se + 3 <= ue_i
                &&& ue_i <= ex_len
                &&& (
                    // the nothing-written face (arm A/B, and the
                    // arm-C empty-span subcase): ue sits at the
                    // double-slash boundary
                    (ue_i == se + 3
                        && serf == o + seq![0x2Fu8, 0x2Fu8])
                    // the ':' face (arm C, password given): the
                    // colon lands exactly at ue, the write spans at
                    // least one more byte, and the '@' write ends it
                    || (serf.index(ue_i) == 0x3Au8
                        && ue_i + 2 <= ex_len
                        && serf.index(ex_len - 1) == 0x40u8)
                    // the '@' face (arm C, username only): '@' lands
                    // exactly at ue and the write ends right there
                    || (serf.index(ue_i) == 0x40u8
                        && ex_len == ue_i + 1))
            }))
        }),
{
    // the double slash (parser.rs:829-830)
    let ghost pre0 = self.serialization.view();
    let ghost pz1 = self.serialization.view();
    self.serialization.push(0x2Fu8);
    let ghost pz2 = self.serialization.view();
    self.serialization.push(0x2Fu8);
    proof {
        assert(pz2 == pz1.push(0x2Fu8));
        assert(self.serialization.view() == pz2.push(0x2Fu8));
        machine_domain_add(pz1, seq![0x2Fu8]);
        machine_domain_add(pz2, seq![0x2Fu8]);
        let f = self.serialization.view();
        assert(f == pre0 + seq![0x2Fu8, 0x2Fu8]);
        assert(f.index((scheme_end as int) + 1) == 0x2Fu8);
        assert(f.index((scheme_end as int) + 2) == 0x2Fu8);
    }
    let before_authority = self.serialization.len();
    let ghost serSlash = self.serialization.view();
    // the userinfo peel (parser.rs:834-835)
    let uinfo_r = self.parse_userinfo(input, scheme_type);
    match uinfo_r {
        Err(e) => Err(e),
        Ok((username_end, rest_u)) => {
            proof {
                // the peel's growth bound (parse_userinfo's post)
                assert((self.serialization.view().len() as int)
                    <= old(self).serialization.view().len()
                        + 3 * (input_rem(&input).len() as int) + 4);
                // the class transport over the peel arms
                let s = input_rem(&input);
                let special_b = is_special(scheme_type);
                let re = input_rem(&rest_u);
                if re == s {
                    assert(host_split_class(s, special_b));
                    assert((re.len() as int) <= (s.len() as int));
                } else if s.len() >= 1
                    && s.index(0) == 0x40u8
                    && re == s.subrange(1, s.len() as int)
                {
                    assert(host_split_class(
                        s.subrange(1, s.len() as int), special_b));
                    assert((re.len() as int) <= (s.len() as int));
                } else {
                    let (k, p) = choose|k: int, p: int|
                        1 <= k
                        && k < s.len()
                        && s.index(k) == 0x40u8
                        && (forall|j: int| 0 <= j < k
                            ==> !userinfo_wall_byte(
                                s.index(j), special_b))
                        && (p == k
                            || (0 <= p < k
                                && s.index(p) == 0x3Au8
                                && (forall|j: int| 0 <= j < p
                                    ==> s.index(j) != 0x3Au8)))
                        && re
                            == s.subrange(k + 1, s.len() as int)
                        && (username_end as int)
                            == serSlash.len()
                                + enc_seq(if p < k {
                                    s.subrange(0, p)
                                } else {
                                    s.subrange(0, k)
                                }, EncodeSet::Userinfo).len();
                    assert(re == s.subrange(k + 1, s.len() as int));
                    assert(host_split_class(
                        s.subrange(k + 1, s.len() as int),
                        special_b));
                    assert((re.len() as int) <= (s.len() as int));
                }
            }
            Ok((username_end, rest_u))
        }
    }
}

/// Phase B of the authority assembly (Origin: parser.rs:839-847): the
/// host/port phase with the to_u32 offsets, the empty-host-with-
/// authority rejection, and the path-start offset. The port region
/// is published in the exact dec_val form the wrap-up face states.
pub exec fn ads_authority_host<'i>(
    &mut self,
    rest_u: Input<'i>,
    scheme_type: SchemeType,
    scheme_end: u32,
    username_end_h: u32,
    has_authority: bool,
) -> (r: Result<
    (u32, u32, super::HostInternal, Option<u16>, Input<'i>, u32),
    ParseError>)
    requires
        input_wf(&rest_u),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        1 <= (scheme_end as int),
        super::is_ascii_alpha(
            old(self).serialization.view().index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(
                old(self).serialization.view().index(j))),
        old(self).serialization.view().index(scheme_end as int)
            == 0x3Au8,
        scheme_type == scheme_type_of(
            old(self).serialization.view()
                .subrange(0, scheme_end as int)),
        ((scheme_end as int) + 3
            <= old(self).serialization.view().len()),
        (old(self).serialization.view()
            .index((scheme_end as int) + 1) == 0x2Fu8),
        (old(self).serialization.view()
            .index((scheme_end as int) + 2) == 0x2Fu8),
        ((scheme_end as int) + 3
            <= (username_end_h as int)),
        (((username_end_h as int)
                <= (old(self).serialization.view().len() as int))
            && (((username_end_h as int)
                    == (old(self).serialization.view().len() as int))
                ==> ((username_end_h as int)
                    == (scheme_end as int) + 3))),
        host_split_class(input_rem(&rest_u),
            is_special(scheme_type)),
        (old(self).serialization.view().len() as int)
            + (input_rem(&rest_u).len() as int) + 40
            <= 0xFFFF_FFFF,
    ensures
        ({
            let serf = final(self).serialization.view();
            let o = old(self).serialization.view();
            let s = input_rem(&rest_u);
            let special = is_special(scheme_type);
            &&& machine_domain(serf)
            &&& final(self).context == old(self).context
            &&& (r.is_err()
                ==> (r == Err(ParseError::EmptyHost)
                    || r == Err(ParseError::InvalidPort)
                    || r == Err(ParseError::Overflow)))
            &&& (r.is_ok() ==> ((serf.len() as int)
                <= o.len() + (s.len() as int) + 6
                && (forall|j: int| 0 <= j && j < o.len()
                    ==> serf.index(j) == o.index(j))))
            &&& (r.is_ok() ==> ({
                let (hs32, he32, host, port, rest_h, ps32) = r.unwrap();
                let hs = hs32 as int;
                let he = he32 as int;
                let ps = ps32 as int;
                &&& input_wf(&rest_h)
                &&& ((input_rem(&rest_h).len() as int)
                    <= (s.len() as int))
                &&& ((he - hs) <= (s.len() as int))
                &&& (hs == o.len())
                &&& (he >= hs)
                &&& (ps == serf.len() as int)
                &&& (he <= ps)
                &&& ((host == super::HostInternal::None)
                    == (he == hs))
                &&& ((host == super::HostInternal::Domain)
                    == (he > hs))
                &&& ((he == hs)
                    ==> (port.is_none() && !special && ps == hs))
                &&& (port.is_none()
                    ==> (he == serf.len() as int
                        && serf == o + s.subrange(0, he - hs)
                        && host_run_class(s.subrange(0, he - hs))))
                &&& (port.is_some() ==> ({
                    let pv = port.unwrap();
                    &&& (serf == o + s.subrange(0, he - hs)
                        + seq![0x3Au8] + dec_ascii_u32(pv as int))
                    &&& serf.index(he) == 0x3Au8
                    &&& he + 2 <= ps
                    &&& (forall|j: int| he + 1 <= j && j < ps
                        ==> super::is_dec_digit(serf.index(j)))
                    &&& (pv as int)
                        == super::dec_val(serf.subrange(he + 1, ps))
                    &&& host_run_class(s.subrange(0, he - hs))
                }))
            }))
        }),
{
    let hs32r = to_u32(self.serialization.len());
    let host_start = match hs32r {
        Err(e) => return Err(e),
        Ok(i) => i,
    };
    proof {
        assert((host_start as int)
            == self.serialization.view().len() as int);
    }
    let scheme_bytes = super::bytes_slice(&self.serialization, 0,
        scheme_end);
    let default_port_v = default_port(&scheme_bytes);
    let hp_r = self.parse_host_and_port(rest_u, scheme_type,
        default_port_v, self.context);
    match hp_r {
        Err(e) => Err(e),
        Ok((host_end, host, port, rest_h)) => {
            let host_is_none = match host {
                super::HostInternal::None => true,
                _ => false,
            };
            if host_is_none && has_authority {
                return Err(ParseError::EmptyHost);
            }
            let ps32r = to_u32(self.serialization.len());
            let path_start32 = match ps32r {
                Err(e) => return Err(e),
                Ok(i) => i,
            };
            proof {
                assert((path_start32 as int)
                    == self.serialization.view().len() as int);
            }
            proof {
                let special = is_special(scheme_type);
                let serf = self.serialization.view();
                let o = old(self).serialization.view();
                let s = input_rem(&rest_u);
                let hs = host_start as int;
                let he = host_end as int;
                let ps = path_start32 as int;
                assert(machine_domain(serf));
                assert((serf.len() as int)
                    <= o.len() + (s.len() as int) + 6);
                assert forall|j: int| 0 <= j && j < o.len()
                    implies serf.index(j) == o.index(j) by {}
                assert(hs == o.len());
                assert(he >= hs);
                assert(ps == serf.len() as int);
                assert(he <= ps);
                assert((he == hs) ==> (port.is_none() && !special));
                assert((host == super::HostInternal::None)
                    == (he == hs));
                assert((host == super::HostInternal::Domain)
                    == (he > hs));
                assert((input_rem(&rest_h).len() as int)
                    <= (s.len() as int));
                let hq = he - hs;
                assert(hq <= (s.len() as int));
                if port.is_none() {
                    assert(serf == o + s.subrange(0, hq));
                    assert(host_run_class(s.subrange(0, hq)));
                } else {
                    let pv = port.unwrap();
                    assert(serf == o + s.subrange(0, hq)
                        + seq![0x3Au8] + dec_ascii_u32(pv as int));
                    assert(hq > 0);
                    let pre = o + s.subrange(0, hq);
                    machine_domain(pre);
                    host_port_region_face(serf, pre, pv as int);
                    assert(serf.index(he) == 0x3Au8);
                    assert(he + 2 <= serf.len() as int);
                    assert forall|j: int| (he as int) + 1 <= j
                        && j < serf.len() as int
                        implies super::is_dec_digit(
                            serf.index(j)) by {}
                    assert((pv as int)
                        == super::dec_val(serf.subrange(
                            (he as int) + 1,
                            serf.len() as int)));
                    assert(host_run_class(s.subrange(0, hq)));
                }
            }
            Ok((host_start, host_end, host, port, rest_h,
                path_start32))
        }
    }
}

/// Phase C of the authority assembly (Origin: parser.rs:847-848): the
/// path scan and the query wrap-up. The requires restate the wqaf
/// FACE-1 cone POSITIONALLY over this fn's own entry view (== the
/// host phase's exit), so no ghost sequence parameters are needed: the
/// caller asserts the claims from the A/B phase digests, and the body
/// translates them across the path scan (everything below path_start
/// survives; the anchor '/' pins the grown frontier case).
pub exec fn ads_authority_path_wq<'i>(
    &mut self,
    rest_h: Input<'i>,
    scheme_type: SchemeType,
    scheme_end: u32,
    username_end: u32,
    host_start: u32,
    host_end: u32,
    host: super::HostInternal,
    port: Option<u16>,
    path_start32: u32,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&rest_h),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        ((path_start32 as int)
            == (old(self).serialization.view().len() as int)),
        1 <= (scheme_end as int),
        (scheme_end as int) + 3
            <= (old(self).serialization.view().len() as int),
        super::is_ascii_alpha(
            old(self).serialization.view().index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(
                old(self).serialization.view().index(j))),
        old(self).serialization.view().index(scheme_end as int)
            == 0x3Au8,
        scheme_type == scheme_type_of(
            old(self).serialization.view()
                .subrange(0, scheme_end as int)),
        (old(self).serialization.view()
            .index((scheme_end as int) + 1) == 0x2Fu8),
        (old(self).serialization.view()
            .index((scheme_end as int) + 2) == 0x2Fu8),
        ((scheme_end as int) + 3 <= (username_end as int)),
        ((username_end as int)
            <= (old(self).serialization.view().len() as int)),
        (((username_end as int)
                == (old(self).serialization.view().len() as int))
            ==> ((username_end as int) == (scheme_end as int) + 3)),
        (
            // route A: the frontier-untouched face (the path decides
            // disjunct-1 vs the anchor wildcard at the wrap-up)
            ((username_end as int)
                == (old(self).serialization.view().len() as int))
            // route B: the ':' face (password given)
            || (old(self).serialization.view()
                    .index(username_end as int) == 0x3Au8
                && (username_end as int) + 2
                    <= (host_start as int)
                && old(self).serialization.view()
                    .index((host_start as int) - 1) == 0x40u8)
            // route C: the '@' face (username only)
            || (old(self).serialization.view()
                    .index(username_end as int) == 0x40u8
                && (host_start as int)
                    == (username_end as int) + 1)
            // route D: the wildcard face (the byte at ue is neither
            // ':' nor '@' -- e.g. a host run head or a scan head)
            || ((username_end as int)
                    < (old(self).serialization.view().len() as int)
                && (username_end as int)
                    == (scheme_end as int) + 3
                && old(self).serialization.view().index(
                    (username_end as int)) != 0x3Au8
                && old(self).serialization.view().index(
                    (username_end as int)) != 0x40u8)
        ),
        ((username_end as int) <= (host_start as int)),
        ((host_start as int)
            <= (old(self).serialization.view().len() as int)),
        ((host_end as int) >= (host_start as int)),
        ((host_end as int) <= (path_start32 as int)),
        ((host == super::HostInternal::None)
            == ((host_start as int) == (host_end as int))),
        (((path_start32 as int) == (host_end as int))
            ==> port.is_none()),
        (((path_start32 as int) > (host_end as int)) ==> (
            old(self).serialization.view()
                .index(host_end as int) == 0x3Au8
            && (host_end as int) + 2 <= (path_start32 as int)
            && (forall|j: int| (host_end as int) + 1 <= j
                    && j < (path_start32 as int)
                ==> super::is_dec_digit(
                    old(self).serialization.view().index(j)))
            && port.is_some()
            && (port.unwrap() as int)
                == super::dec_val(old(self).serialization.view()
                    .subrange((host_end as int) + 1,
                        (path_start32 as int)))
        )),
        ((old(self).serialization.view().len() as int)
            + 5 * (input_rem(&rest_h).len() as int) + 38
            <= 0xFFFF_FFFF),
        ((old(self).serialization.view().len() as int)
            + 11 * (input_rem(&rest_h).len() as int) + 26
            <= 0xFFFF_FFFF),
        (is_special(scheme_type) ==> (
            (old(self).serialization.view().len() as int) == 0
            || old(self).serialization.view()
                .index(
                    (old(self).serialization.view().len() as int) - 1)
                != 0x2Fu8)),
    ensures
        machine_domain(final(self).serialization.view()),
        r.is_ok() ==> super::url_invariant(&r.unwrap()),
        r.is_err() ==> (r == Err(ParseError::Overflow)),
{
    let mut has_host: bool = true;
    let pp_r = self.parse_path_start(scheme_type, &mut has_host,
        rest_h, path_start32 as usize);
    proof {
        let serf = self.serialization.view();
        let o = old(self).serialization.view();
        let n = serf.len() as int;
        let se = scheme_end as int;
        let ue = username_end as int;
        let hs = host_start as int;
        let he = host_end as int;
        let ps = path_start32 as int;
        // the path scan preserved everything below ps and grew the
        // frontier only (parse_path_start's posts)
        assert((serf.len() as int)
            <= (o.len() as int)
                + 5 * (input_rem(&rest_h).len() as int) + 7);
        assert((input_rem(&pp_r.0).len() as int)
            <= (input_rem(&rest_h).len() as int));
        assert((serf.len() as int)
            + 6 * (input_rem(&pp_r.0).len() as int) + 12
            <= (o.len() as int)
                + 11 * (input_rem(&rest_h).len() as int) + 26);
        // positional survival below ps, and the anchor at ps
        assert forall|j: int| 0 <= j && j < ps
            implies serf.index(j) == o.index(j) by {}
        if (serf.len() as int) > ps {
            assert(serf.index(ps) == 0x2Fu8);
        }
        // the four routes translate across the scan
        if ue == (o.len() as int) {
            // route A: growth decides disjunct-1 vs the wildcard
            if (serf.len() as int) == ue {
                assert(ue == se + 3);
            } else {
                assert(serf.index(ue) == 0x2Fu8);
                assert(ue == se + 3);
                assert(serf.index(ue) != 0x3Au8
                    && serf.index(ue) != 0x40u8);
            }
        }
        assert(se < (n as int));
        assert(self.context == Context::UrlParser);
    }
    proof {
        // per-conjunct localization of the wqaf FACE (each query
        // gets its precise blame)
        let serf = self.serialization.view();
        let o = old(self).serialization.view();
        let serf_len = serf.len() as int;
        assert(super::is_ascii_alpha(serf.index(0)));
        assert forall|j: int| 1 <= j && j < (scheme_end as int)
            implies super::is_scheme_char(serf.index(j)) by {}
        assert(serf.index(scheme_end as int) == 0x3Au8);
        assert((scheme_end as int) + 3
            <= (o.len() as int));
        assert(serf.index((scheme_end as int) + 1) == 0x2Fu8);
        assert(serf.index((scheme_end as int) + 2) == 0x2Fu8);
        assert(serf.subrange(0, scheme_end as int)
            == o.subrange(0, scheme_end as int)) by {}
        assert(scheme_type == scheme_type_of(
            serf.subrange(0, scheme_end as int)));
        assert((scheme_end as int) < serf_len);
        assert((scheme_end as int) + 3
            <= (username_end as int));
        assert((username_end as int) <= serf_len);
        assert(((username_end as int) == serf_len)
            ==> ((username_end as int)
                == (scheme_end as int) + 3));
        assert(
            ((username_end as int) == serf_len)
            || (serf.index(username_end as int) == 0x3Au8
                && (host_start as int)
                    >= (username_end as int) + 2
                && serf.index((host_start as int) - 1)
                    == 0x40u8)
            || (serf.index(username_end as int) == 0x40u8
                && (host_start as int)
                    == (username_end as int) + 1)
            || ((username_end as int)
                    == (scheme_end as int) + 3
                && serf.index(username_end as int) != 0x3Au8
                && serf.index(username_end as int) != 0x40u8));
        assert((username_end as int) <= (host_start as int));
        assert((host_start as int) <= serf_len);
        assert((host_end as int) >= (host_start as int));
        assert((host_end as int) <= serf_len);
        assert((host_end as int) <= (path_start32 as int));
        assert((path_start32 as int) <= serf_len);
        assert((host == super::HostInternal::None)
            == ((host_start as int) == (host_end as int)));
        assert(((path_start32 as int) == (host_end as int))
            ==> port.is_none());
        if (path_start32 as int) > (host_end as int) {
            let pv = port.unwrap();
            assert(serf.index(host_end as int) == 0x3Au8);
            assert((host_end as int) + 2
                <= (path_start32 as int));
            assert forall|j: int| (host_end as int) + 1 <= j
                && j < (path_start32 as int)
                implies super::is_dec_digit(
                    serf.index(j)) by {}
            assert(serf.subrange((host_end as int) + 1,
                (path_start32 as int))
                == o.subrange((host_end as int) + 1,
                    (path_start32 as int)));
            assert((pv as int) == super::dec_val(
                serf.subrange((host_end as int) + 1,
                    (path_start32 as int))));
        }
        if (path_start32 as int) < serf_len {
            // the path's anchor byte (or the scan head) at ps
            assert(serf.index(path_start32 as int) == 0x2Fu8
                || serf.index(path_start32 as int) == 0x23u8
                || serf.index(path_start32 as int) == 0x3Fu8);
        }
        assert((serf.len() as int)
            + 6 * (input_rem(&pp_r.0).len() as int) + 12
            <= 0xFFFF_FFFF);
        assert(machine_domain(serf));
        assert(input_wf(&pp_r.0));
        assert(input_rem(&pp_r.0).len() == 0
            || input_rem(&pp_r.0).index(0) == 0x3Fu8
            || input_rem(&pp_r.0).index(0) == 0x23u8);
        assert(self.context == Context::UrlParser);
    }
    let wq = self.with_query_and_fragment(scheme_type, scheme_end,
        username_end, host_start, host_end, host, port,
        path_start32, pp_r.0);
    wq
}

/// Origin Rust (parser.rs:828-848): fn after_double_slash(mut self, input,
///   scheme_type, scheme_end) -> ParseResult<Url> -- the authority state
/// in its three phase helpers: the uinfo phase (ads_authority_uinfo),
/// the host/port phase (ads_authority_host), and the path/wrap-up
/// phase (ads_authority_path_wq). The phase contracts publish digested
/// position facts so the whole-shell aggregate stays small.

/// Post-A shell bridge (ghost): the entry view o survived the
/// "//" push and the userinfo peel unchanged below o.len, so the
/// scheme-region facts the host phase requires hold over serU too.
pub proof fn ads_shell_uinfo_bridge(
    o: Seq<u8>,
    serU: Seq<u8>,
    scheme_end: u32,
    scheme_type: SchemeType,
)
    requires
        machine_domain(o),
        1 <= (scheme_end as int),
        (o.len() as int) == (scheme_end as int) + 1,
        super::is_ascii_alpha(o.index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(o.index(j))),
        o.index(scheme_end as int) == 0x3Au8,
        scheme_type == scheme_type_of(o.subrange(0, scheme_end as int)),
        (forall|j: int| 0 <= j && j < (o.len() as int)
            ==> serU.index(j) == o.index(j)),
        machine_domain(serU),
        ((scheme_end as int) + 3 <= (serU.len() as int)),
        serU.index((scheme_end as int) + 1) == 0x2Fu8,
        serU.index((scheme_end as int) + 2) == 0x2Fu8,
    ensures
        super::is_ascii_alpha(serU.index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(serU.index(j))),
        serU.index(scheme_end as int) == 0x3Au8,
        (scheme_type == scheme_type_of(
            serU.subrange(0, scheme_end as int))),
{
    assert(serU.subrange(0, scheme_end as int)
        == o.subrange(0, scheme_end as int)) by {
        assert forall|j: int| 0 <= j && j < (scheme_end as int)
            implies serU.index(j) == o.index(j) by {}
    }
    assert(super::is_ascii_alpha(serU.index(0)));
    assert forall|j: int| 1 <= j && j < (scheme_end as int)
        implies super::is_scheme_char(serU.index(j)) by {}
    assert(serU.index(scheme_end as int) == 0x3Au8);
    assert(scheme_type == scheme_type_of(
        serU.subrange(0, scheme_end as int)));
}

/// Post-B shell bridge (ghost): the route class and the positional
/// facts the wqaf phase requires, derived one small query at a time
/// over serW from the uinfo and host digests. This is exactly the
/// in-shell proof block of the second attempt, lifted into its own
/// proof function so the thin assembly body stays under the whole-fn
/// rlimit.
pub proof fn ads_shell_route_bridge<'i>(
    o: Seq<u8>,
    serU: Seq<u8>,
    serW: Seq<u8>,
    rest_u: Input<'i>,
    rest_h: Input<'i>,
    scheme_type: SchemeType,
    scheme_end: u32,
    username_end: u32,
    host_start: u32,
    host_end: u32,
    host: super::HostInternal,
    port: Option<u16>,
    path_start32: u32,
    in_len: int,
)
    requires
        machine_domain(o),
        1 <= (scheme_end as int),
        (o.len() as int) == (scheme_end as int) + 1,
        super::is_ascii_alpha(o.index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(o.index(j))),
        o.index(scheme_end as int) == 0x3Au8,
        scheme_type == scheme_type_of(o.subrange(0, scheme_end as int)),
        // the uinfo digest over serU
        machine_domain(serU),
        (forall|j: int| 0 <= j && j < (o.len() as int)
            ==> serU.index(j) == o.index(j)),
        ((scheme_end as int) + 3 <= (serU.len() as int)),
        serU.index((scheme_end as int) + 1) == 0x2Fu8,
        serU.index((scheme_end as int) + 2) == 0x2Fu8,
        ((scheme_end as int) + 3 <= (username_end as int)),
        ((username_end as int) <= (serU.len() as int)),
        (
            ((username_end as int) == scheme_end as int + 3
                && serU == o + seq![0x2Fu8, 0x2Fu8])
            || (serU.index(username_end as int) == 0x3Au8
                && (username_end as int) + 2
                    <= (serU.len() as int)
                && serU.index((serU.len() as int) - 1) == 0x40u8)
            || (serU.index(username_end as int) == 0x40u8
                && (serU.len() as int)
                    == (username_end as int) + 1)
        ),
        ((serU.len() as int) - (o.len() as int))
            <= 3 * in_len + 4,
        ((input_rem(&rest_u).len() as int) <= in_len),
        // the host digest over serW
        machine_domain(serW),
        (forall|j: int| 0 <= j && j < (serU.len() as int)
            ==> serW.index(j) == serU.index(j)),
        ((serW.len() as int)
            <= (serU.len() as int)
                + (input_rem(&rest_u).len() as int) + 6),
        ((host_start as int) == (serU.len() as int)),
        ((host_end as int) >= (host_start as int)),
        ((path_start32 as int) == (serW.len() as int)),
        ((host_end as int) <= (path_start32 as int)),
        ((host == super::HostInternal::None)
            == ((host_end as int) == (host_start as int))),
        (((host_end as int) == (host_start as int)) ==> (
            port.is_none()
            && !is_special(scheme_type)
            && (path_start32 as int) == (host_start as int))),
        (port.is_none() ==> (
            (host_end as int) == (serW.len() as int)
            && serW
                == serU + input_rem(&rest_u).subrange(0,
                    (host_end as int) - (host_start as int))
            && host_run_class(input_rem(&rest_u).subrange(0,
                (host_end as int) - (host_start as int))))),
        (port.is_some() ==> ({
            let pv = port.unwrap();
            &&& serW
                == serU + input_rem(&rest_u).subrange(0,
                    (host_end as int) - (host_start as int))
                    + seq![0x3Au8] + dec_ascii_u32(pv as int)
            &&& serW.index(host_end as int) == 0x3Au8
            &&& (host_end as int) + 2 <= (path_start32 as int)
            &&& (forall|j: int| (host_end as int) + 1 <= j
                    && j < (path_start32 as int)
                ==> super::is_dec_digit(serW.index(j)))
            &&& (pv as int)
                == super::dec_val(serW.subrange(
                    (host_end as int) + 1, (path_start32 as int)))
            &&& host_run_class(input_rem(&rest_u).subrange(0,
                (host_end as int) - (host_start as int)))
        })),
        ((input_rem(&rest_h).len() as int)
            <= (input_rem(&rest_u).len() as int)),
        (((host_end as int) - (host_start as int))
            <= (input_rem(&rest_u).len() as int)),
        ((o.len() as int) + 16 * in_len + 74
            <= 0xFFFF_FFFF),
    ensures
        machine_domain(serW),
        ((path_start32 as int) == (serW.len() as int)),
        ((scheme_end as int) + 3 <= (serW.len() as int)),
        super::is_ascii_alpha(serW.index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(serW.index(j))),
        serW.index(scheme_end as int) == 0x3Au8,
        serW.index((scheme_end as int) + 1) == 0x2Fu8,
        serW.index((scheme_end as int) + 2) == 0x2Fu8,
        (scheme_type == scheme_type_of(
            serW.subrange(0, scheme_end as int))),
        ((scheme_end as int) + 3 <= (username_end as int)),
        ((username_end as int) <= (serW.len() as int)),
        (((username_end as int) == (serW.len() as int))
            ==> ((username_end as int) == (scheme_end as int) + 3)),
        (
            // route A
            ((username_end as int) == (serW.len() as int))
            // route B
            || (serW.index(username_end as int) == 0x3Au8
                && (username_end as int) + 2
                    <= (host_start as int)
                && serW.index((host_start as int) - 1) == 0x40u8)
            // route C
            || (serW.index(username_end as int) == 0x40u8
                && (host_start as int)
                    == (username_end as int) + 1)
            // route D
            || ((username_end as int) < (serW.len() as int)
                && (username_end as int)
                    == (scheme_end as int) + 3
                && serW.index(username_end as int) != 0x3Au8
                && serW.index(username_end as int) != 0x40u8)
        ),
        ((username_end as int) <= (host_start as int)),
        ((host_start as int) <= (serW.len() as int)),
        ((host_end as int) >= (host_start as int)),
        ((host_end as int) <= (path_start32 as int)),
        ((host == super::HostInternal::None)
            == ((host_start as int) == (host_end as int))),
        (((path_start32 as int) == (host_end as int))
            ==> port.is_none()),
        (((path_start32 as int) > (host_end as int)) ==> (
            serW.index(host_end as int) == 0x3Au8
            && (host_end as int) + 2 <= (path_start32 as int)
            && (forall|j: int| (host_end as int) + 1 <= j
                    && j < (path_start32 as int)
                ==> super::is_dec_digit(serW.index(j)))
            && port.is_some()
            && (port.unwrap() as int)
                == super::dec_val(serW.subrange(
                    (host_end as int) + 1,
                    (path_start32 as int)))
        )),
        ((serW.len() as int)
            + 5 * (input_rem(&rest_h).len() as int) + 38
            <= 0xFFFF_FFFF),
        ((serW.len() as int)
            + 11 * (input_rem(&rest_h).len() as int) + 26
            <= 0xFFFF_FFFF),
        (is_special(scheme_type) ==> (
            (serW.len() as int) == 0
            || serW.index((serW.len() as int) - 1) != 0x2Fu8)),
{
    let ue_i = username_end as int;
    let se = scheme_end as int;
    let hs = host_start as int;
    let he = host_end as int;
    let ps = path_start32 as int;
    let serW_len = serW.len() as int;
    // the scheme region survives to serW
    assert(super::is_ascii_alpha(serW.index(0)));
    assert forall|j: int| 1 <= j && j < se
        implies serW.index(j) == o.index(j) by {}
    assert(serW.index(se) == 0x3Au8);
    assert(serW.index(se + 1) == 0x2Fu8);
    assert(serW.index(se + 2) == 0x2Fu8);
    assert(serW.subrange(0, se) == o.subrange(0, se)) by {
        assert forall|j: int| 0 <= j && j < se
            implies serW.index(j) == o.index(j) by {}
    }
    assert(scheme_type == scheme_type_of(
        serW.subrange(0, se)));
    assert(ps == serW_len) by {}
    if ue_i < serW_len {
        // the userinfo byte forms survived below hs
        if ue_i < hs {
            assert(serW.index(ue_i) == serU.index(ue_i));
            assert(serW.index(hs - 1) == serU.index(hs - 1));
        }
    }
    // the four routes (case analysis over the uinfo digest arms)
    if (username_end as int) == serU.len() as int {
        // nothing written by the peel: ue == se + 3
        assert(ue_i == se + 3);
        if hs < he {
            // the host run head byte sits at ue; the two port faces
            // both compose serW from serU + run (':' + digits only
            // extend the tail), so this is the route-D form
            let su = input_rem(&rest_u);
            let hq = he - hs;
            let run = su.subrange(0, hq);
            assert(ue_i == serU.len() as int);
            assert(ue_i < serW_len);
            assert(serW.index(ue_i) == su.index(0)) by {
                if port.is_none() {
                    assert(serW == serU + run);
                    vstd::seq::lemma_seq_add_index2(serU, run,
                        ue_i);
                } else {
                    let pv = port.unwrap();
                    let da = dec_ascii_u32(pv as int);
                    let tail_more = seq![0x3Au8] + da;
                    assert(serW == serU + run + tail_more);
                    vstd::seq::lemma_seq_add_index2(serU,
                        run + tail_more, ue_i);
                    vstd::seq::lemma_seq_add_index1(run,
                        tail_more, 0);
                }
            }
            host_run_class(run);
            assert(host_simple_byte(su.index(0)));
            assert(serW.index(ue_i) != 0x3Au8);
            assert(serW.index(ue_i) != 0x40u8);
        } else {
            assert(port.is_none());
            assert(ue_i == serU.len() as int);
            assert(serW_len == serU.len() as int);
            assert(ue_i == serW_len);
        }
    } else {
        // the peel wrote: the ':'/'@' arms survive at ue
        assert(serW.index(ue_i) == serU.index(ue_i));
        if serU.index(ue_i) == 0x3Au8 {
            assert(ue_i + 2 <= serU.len() as int);
            assert(hs >= ue_i + 2);
            assert(serW.index(hs - 1) == 0x40u8);
        } else {
            assert(serU.index(ue_i) == 0x40u8);
            assert(serU.len() as int == ue_i + 1);
            assert(hs == ue_i + 1);
        }
    }
    // the tail pin for the path phase (special schemes never end
    // in '/' at the serW frontier: the run/port faces, or the
    // empty-run face is non-special)
    if is_special(scheme_type) {
        if hs < he {
            // the run/port forms: the tail byte is a letter or a
            // digit (the digest compositions)
            if port.is_none() {
                assert(serW_len == (serU.len() as int)
                    + (he - hs));
                let su = input_rem(&rest_u);
                let hq = he - hs;
                assert(serW == serU + su.subrange(0, hq));
                host_run_class(su.subrange(0, hq));
                assert(host_simple_byte(
                    su.index(hq - 1)));
                assert(serW.index(serW_len - 1)
                    == su.index(hq - 1));
            } else {
                let pv = port.unwrap();
                let da = dec_ascii_u32(pv as int);
                assert(serW_len == (serU.len() as int)
                    + (he - hs) + 1 + da.len() as int);
                assert(serW.index(serW_len - 1)
                    == da.index(da.len() as int - 1));
                assert(da.len() as int >= 1);
                assert(super::is_dec_digit(
                    da.index(da.len() as int - 1)));
            }
        } else {
            assert(!is_special(scheme_type));
            assert(false);
        }
    }
    let tail_i = serW.len() as int - 1;
    if is_special(scheme_type) {
        assert(serW.index(tail_i) != 0x2Fu8);
    }
    // the budgets
    assert((serW.len() as int)
        + 5 * (input_rem(&rest_h).len() as int) + 38
        <= o.len() + 16 * in_len + 74);
    assert((serW.len() as int)
        + 11 * (input_rem(&rest_h).len() as int) + 26
        <= o.len() + 16 * in_len + 74);
    // the port region dispatch for the wqaf requires
    if ps > he {
        assert(port.is_some());
    } else {
        assert(ps == he);
    }
}

pub exec fn after_double_slash<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
    scheme_end: u32,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        1 <= (scheme_end as int),
        (old(self).serialization.view().len() as int)
            == (scheme_end as int) + 1,
        super::is_ascii_alpha(
            old(self).serialization.view().index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(
                old(self).serialization.view().index(j))),
        old(self).serialization.view().index(scheme_end as int)
            == 0x3Au8,
        scheme_type == scheme_type_of(
            old(self).serialization.view()
                .subrange(0, scheme_end as int)),
        authority_entry_class(input_rem(&input),
            is_special(scheme_type)),
        (old(self).serialization.view().len() as int)
            + 16 * (input_rem(&input).len() as int) + 74
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        r.is_ok() ==> super::url_invariant(&r.unwrap()),
        r.is_err() ==> (r == Err(ParseError::EmptyHost)
            || r == Err(ParseError::InvalidPort)
            || r == Err(ParseError::Overflow)),
{
    // phase A (the "//" push and the userinfo peel)
    let a_r = self.ads_authority_uinfo(input, scheme_type, scheme_end);
    let (username_end, rest_u) = match a_r {
        Err(e) => return Err(e),
        Ok(x) => x,
    };
    let ghost serU = self.serialization.view();
    let has_authority = self.serialization.len()
        != ((scheme_end as usize) + 3);
    proof {
        // the scheme region survived the peel: serU matches the entry
        Self::ads_shell_uinfo_bridge(old(self).serialization.view(), serU,
            scheme_end, scheme_type);
        assert(self.serialization.view() == serU);
        assert(self.serialization.view()
                .subrange(0, scheme_end as int)
            == serU.subrange(0, scheme_end as int)) by {
            assert forall|j: int| 0 <= j && j < (scheme_end as int)
                implies self.serialization.view().index(j)
                    == serU.index(j) by {}
        }
        assert(scheme_type == scheme_type_of(
            self.serialization.view()
                .subrange(0, scheme_end as int)));
    }
    // phase B (the host/port assembly and the offset records)
    let b_r = self.ads_authority_host(rest_u, scheme_type, scheme_end,
        username_end, has_authority);
    let (host_start, host_end, host, port, rest_h, path_start32) =
        match b_r
    {
        Err(e) => return Err(e),
        Ok(x) => x,
    };
    let ghost serW = self.serialization.view();
    // the C-phase requires (route class and positional facts over
    // serW) are derived in the separately-checked bridge below, so
    // this assembly body stays under the whole-fn rlimit
    proof {
        Self::ads_shell_route_bridge(old(self).serialization.view(), serU,
            serW, rest_u, rest_h, scheme_type, scheme_end,
            username_end, host_start, host_end, host, port,
            path_start32, (input_rem(&input).len() as int));
    }
    // phase C (the path scan and the query wrap-up)
    let wq = self.ads_authority_path_wq(rest_h, scheme_type,
        scheme_end, username_end, host_start, host_end, host, port,
        path_start32);
    wq
}

/// Origin Rust (parser.rs:465-497, the neither-"//" branch): the
/// anarchist (no-authority) record of parse_non_special -- the opaque
/// or absolute path of a non-special scheme runs straight into the
/// FACE-2 wrap-up: username_end = host_start = host_end = path_start =
/// the scheme-colon boundary, no host, no port.
pub exec fn ads_non_special_anarchist<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
    scheme_end: u32,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        1 <= (scheme_end as int),
        (old(self).serialization.view().len() as int)
            == (scheme_end as int) + 1,
        super::is_ascii_alpha(
            old(self).serialization.view().index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(
                old(self).serialization.view().index(j))),
        old(self).serialization.view().index(scheme_end as int)
            == 0x3Au8,
        scheme_type == scheme_type_of(
            old(self).serialization.view()
                .subrange(0, scheme_end as int)),
        (old(self).serialization.view().len() as int)
            + 11 * (input_rem(&input).len() as int) + 30
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        r.is_ok() ==> super::url_invariant(&r.unwrap()),
        r.is_err() ==> (r == Err(ParseError::Overflow)),
{
    // the offset of the path component (the scheme's ':' boundary)
    let psr = to_u32(self.serialization.len());
    let path_start32 = match psr {
        Err(e) => return Err(e),
        Ok(i) => i,
    };
    proof {
        assert((path_start32 as int)
            == self.serialization.view().len() as int);
        assert((path_start32 as int)
            == (scheme_end as int) + 1);
    }
    let se_plus1 = (scheme_end as usize) + 1;
    // the anarchist path faces: a leading '/' starts the absolute
    // path (parser.rs:480-483); anything else is the opaque path
    let sp_o = input.split_prefix_char(0x2Fu8);
    let remaining = match sp_o {
        Option::Some(sub) => {
            let ghost preA = self.serialization.view();
            self.serialization.push(0x2Fu8);
            proof {
                assert(machine_domain_byte(0x2Fu8));
                machine_domain_add(preA, seq![0x2Fu8]);
                assert(self.serialization.view()
                    == preA + seq![0x2Fu8]);
            }
            let mut unused_host: bool = false;
            let rx = self.parse_path(scheme_type, se_plus1,
                &mut unused_host, sub);
            rx
        }
        Option::None => {
            self.parse_cannot_be_a_base_path(input)
        }
    };
    proof {
        // the scheme bytes survive the anarchist path faces (both
        // write at or past the se+1 boundary): parse_path's prefix
        // preservation covers [0, path_start), and the opaque face
        // only appends
        let serf = self.serialization.view();
        let o = old(self).serialization.view();
        assert forall|j: int| 0 <= j && j < (scheme_end as int) + 1
            implies serf.index(j) == o.index(j) by {}
        assert(serf.subrange(0, scheme_end as int)
            == o.subrange(0, scheme_end as int));
        // the budget: either face grows at most 5*|input| + 7
        assert((serf.len() as int)
            + 6 * (input_rem(&remaining).len() as int) + 12
            <= o.len() + 11 * (input_rem(&input).len() as int) + 30);
        assert(self.context == Context::UrlParser);
        // the remaining input shrinks
        assert((input_rem(&remaining).len() as int)
            <= (input_rem(&input).len() as int));
    }
    let wq = self.with_query_and_fragment(scheme_type, scheme_end,
        path_start32, path_start32, path_start32,
        super::HostInternal::None, Option::None,
        path_start32, remaining);
    wq
}

/// Origin Rust (parser.rs:464-497): fn parse_non_special(mut self,
///   input, scheme_type, scheme_end) -> ParseResult<Url> -- the
/// non-special dispatch: a "//" prefix enters the authority state
/// (after_double_slash, the FACE-1 cones all verified), anything
/// else is the anarchist record (ads_non_special_anarchist, FACE-2).
pub exec fn parse_non_special<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
    scheme_end: u32,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        !is_special(scheme_type),
        1 <= (scheme_end as int),
        (old(self).serialization.view().len() as int)
            == (scheme_end as int) + 1,
        super::is_ascii_alpha(
            old(self).serialization.view().index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(
                old(self).serialization.view().index(j))),
        old(self).serialization.view().index(scheme_end as int)
            == 0x3Au8,
        scheme_type == scheme_type_of(
            old(self).serialization.view()
                .subrange(0, scheme_end as int)),
        ({
            // the "//" dispatch arm's entry face: whatever follows
            // the two slashes must be in the authority entry class
            let rem = input_rem(&input);
            ((rem.len() as int) >= 2
                && rem.index(0) == 0x2Fu8
                && rem.index(1) == 0x2Fu8)
            ==> authority_entry_class(
                rem.subrange(2, rem.len() as int), false)
        }),
        (old(self).serialization.view().len() as int)
            + 16 * (input_rem(&input).len() as int) + 74
            <= 0xFFFF_FFFF,
        (old(self).serialization.view().len() as int)
            + 11 * (input_rem(&input).len() as int) + 30
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        r.is_ok() ==> super::url_invariant(&r.unwrap()),
        r.is_err() ==> (r == Err(ParseError::EmptyHost)
            || r == Err(ParseError::InvalidPort)
            || r == Err(ParseError::Overflow)),
{
    let sp2 = input.split_prefix_slash2();
    match sp2 {
        Option::Some(rest2) => {
            // the authority state (parser.rs:470-471)
            proof {
                let rem = input_rem(&input);
                assert(input_rem(&rest2)
                    == rem.subrange(2, rem.len() as int));
                assert(authority_entry_class(
                    input_rem(&rest2),
                    is_special(scheme_type)));
                assert(!is_special(scheme_type));
            }
            self.after_double_slash(rest2, scheme_type, scheme_end)
        }
        Option::None => {
            // the anarchist record (parser.rs:473-497)
            self.ads_non_special_anarchist(input, scheme_type,
                scheme_end)
        }
    }
}

/// Origin Rust (parser.rs:425-461): fn parse_with_scheme(mut self,
///   input: Input<'_>) -> ParseResult<Url> -- the scheme-recorded
/// dispatch: the scheme_end offset, the scheme-type classification
/// of the recorded bytes, the ':' push, and the three state arms.
/// CONE (both honest upstream `Url::parse` faces, ledgered below):
/// base_url is None (the no-base branch of parse_url,
/// parser.rs:391) and the recorded scheme is not "file" (the
/// parse_file arm is the file-state batch arc.)
pub exec fn parse_with_scheme<'i>(
    &mut self,
    input: Input<'i>,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        self.base_url.is_none(),
        machine_domain(old(self).serialization.view()),
        1 <= (old(self).serialization.view().len() as int),
        (old(self).serialization.view().len() as int)
            <= 0xFFFF_FFFF,
        super::is_ascii_alpha(
            old(self).serialization.view().index(0)),
        (forall|j: int| 1 <= j
            && j < (old(self).serialization.view().len() as int)
            ==> super::is_scheme_char(
                old(self).serialization.view().index(j))),
        ({
            let o = old(self).serialization.view();
            let rem = input_rem(&input);
            let special = scheme_type_of(o)
                == SchemeType::SpecialNotFile;
            let sfile = scheme_type_of(o)
                == SchemeType::File;
            let nspl = scheme_type_of(o)
                == SchemeType::NotSpecial;
            // the special authority-slashes arm: the class face at
            // the (unique) maximal slash run head the scanner picks.
            // The trigger fires on the boundary byte term.
            &&& (forall|k: int|
                    #![trigger rem.subrange(k, rem.len() as int)]
                ((special
                    && 0 <= k
                    && k <= (rem.len() as int)
                    // the trigger carrier (vacuous): the slice term
                    && (rem.subrange(k, rem.len() as int).len() as int)
                        <= (rem.len() as int)
                    && slash_run_prefix(rem, k)
                    && ((k == rem.len() as int)
                        || (rem.index(k) != 0x2Fu8
                            && rem.index(k) != 0x5Cu8)))
                ==> (authority_entry_class(
                        rem.subrange(k, rem.len() as int), true)
                    && ((o.len() as int) + 1)
                        + 16 * ((rem.len() as int) - k) + 74
                        <= 0xFFFF_FFFF)))
            &&& (nspl ==> (
                // the non-special anarchist arm's faces
                (((rem.len() as int) >= 2
                    && rem.index(0) == 0x2Fu8
                    && rem.index(1) == 0x2Fu8)
                    ==> authority_entry_class(
                        rem.subrange(2, rem.len() as int), false))
                && ((o.len() as int) + 1)
                    + 16 * (rem.len() as int) + 74
                    <= 0xFFFF_FFFF
                && ((o.len() as int) + 1)
                    + 11 * (rem.len() as int) + 30
                    <= 0xFFFF_FFFF))
            &&& (sfile ==> (
                file_state_entry_face(rem)
                && ((o.len() as int) + 1)
                    + 20 * (rem.len() as int) + 176
                    <= 0xFFFF_FFFF))
        }),
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_ok() ==> super::url_invariant(&r.unwrap())),
        (r.is_err() ==> (r == Err(ParseError::EmptyHost)
            || r == Err(ParseError::InvalidPort)
            || r == Err(ParseError::Overflow))),
{
    // the scheme end offset (parser.rs:429)
    let se_r = to_u32(self.serialization.len());
    let scheme_end = match se_r {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    proof {
        assert((scheme_end as int)
            == (self.serialization.view().len() as int));
    }
    // the scheme-type classification of the recorded bytes
    // (parser.rs:430)
    let scheme_type = scheme_type_from(&self.serialization);
    // the ':' push (parser.rs:431)
    let ghost pre_colon = self.serialization.view();
    self.serialization.push(0x3Au8);
    proof {
        let post = self.serialization.view();
        machine_domain_add(pre_colon, seq![0x3Au8]);
        assert(post == pre_colon + seq![0x3Au8]);
        assert((post.len() as int) == (scheme_end as int) + 1);
        assert(super::is_ascii_alpha(post.index(0))) by {
            vstd::seq::lemma_seq_add_index1(pre_colon,
                seq![0x3Au8], 0);
        }
        assert forall|j: int| 1 <= j && j < (scheme_end as int)
            implies super::is_scheme_char(post.index(j)) by {
            vstd::seq::lemma_seq_add_index1(pre_colon,
                seq![0x3Au8], j);
        }
        assert(post.index(scheme_end as int) == 0x3Au8) by {
            vstd::seq::lemma_seq_add_index2(pre_colon,
                seq![0x3Au8], scheme_end as int);
        }
        let sub = post.subrange(0, scheme_end as int);
        assert(sub == pre_colon) by {
            assert((sub.len() as int) == (pre_colon.len() as int));
            assert forall|j: int| 0 <= j && j < (scheme_end as int)
                implies sub.index(j) == pre_colon.index(j) by {
                vstd::seq::lemma_seq_subrange_index(post, 0,
                    scheme_end as int, j);
                vstd::seq::lemma_seq_add_index1(pre_colon,
                    seq![0x3Au8], j);
            }
            vstd::seq::lemma_seq_ext_equal(sub, pre_colon);
        }
        assert(scheme_type == scheme_type_of(pre_colon));
        assert(scheme_type == scheme_type_of(
            post.subrange(0, scheme_end as int)));
        assert(machine_domain(post));
    }
    match scheme_type {
        SchemeType::File => {
            // (parser.rs:432-438) the file arm: the
            // ExpectedFileDoubleSlash violation log is outside the
            // value surface; the base "file" filter runs on the None
            // base of this fn's cone; the serialization clear
            // (parser.rs:434) hands the file state its empty record
            // buffer (the debug assert of parse_file,
            // parser.rs:509).
            self.serialization.truncate(0);
            proof {
                let e = Seq::empty();
                let s = self.serialization.view();
                assert((s.len() as int) == 0);
                assert(s == e) by {
                    vstd::seq::lemma_seq_ext_equal(s, e);
                }
                assert(machine_domain(s)) by {
                    assert forall|j: int|
                        0 <= j && j < (s.len() as int)
                        implies machine_domain_byte(s.index(j)) by {
                    }
                }
                // the post-':' budget folds into the file-state
                // face's own (the clear resets the length; the cone
                // keeps the pre-clear length a lower-bound filter)
                let rem = input_rem(&input);
                let o = old(self).serialization.view();
                assert((o.len() as int) >= 1);
                assert(20 * (rem.len() as int) + 176
                    <= 0xFFFF_FFFF);
            }
            let base_file_url: Option<&'i super::Url>
                = Option::None;
            self.parse_file(input, scheme_type, base_file_url)
        }
        SchemeType::SpecialNotFile => {
            // special relative or authority state
            // (parser.rs:439-451)
            let (slashes_count, remaining) =
                input.count_matching_slash_bs();
            // the base-URL split (parser.rs:444-451): LEDGER
            // MARKER -- dead under the base_url == None cone (the
            // parse_relative face is the base-merge batch arc);
            // the ExpectedDoubleSlash violation log of
            // parser.rs:452-458 is outside the value surface.
            match self.base_url {
                Option::Some(_) => {
                    return Err(ParseError::EmptyHost);
                }
                Option::None => {}
            }
            // special authority slashes state (parser.rs:459)
            proof {
                let rem = input_rem(&input);
                let ki = (slashes_count as int);
                assert(scheme_type_of(pre_colon)
                    == SchemeType::SpecialNotFile);
                assert((ki as int) <= (rem.len() as int));
                slash_run_prefix_iff(rem, ki);
                assert(slash_run_prefix(rem, ki));
                assert(if ki == (rem.len() as int) { true } else {
                    rem.index(ki) != 0x2Fu8 && rem.index(ki) != 0x5Cu8
                });
                assert(ki == (rem.len() as int)
                    || (rem.index(ki) != 0x2Fu8
                        && rem.index(ki) != 0x5Cu8));
                // the entry-face instantiation at the scanner's k
                assert(authority_entry_class(
                    rem.subrange(ki, rem.len() as int), true));
                let post = self.serialization.view();
                assert(((old(self).serialization.view().len() as int) + 1)
                    + 16 * ((rem.len() as int) - ki) + 74
                    <= 0xFFFF_FFFF);
                assert(((post.len() as int))
                    + 16 * ((input_rem(&remaining).len() as int))
                    + 74 <= 0xFFFF_FFFF);
                assert(input_rem(&remaining)
                    == rem.subrange(ki, rem.len() as int));
            }
            self.after_double_slash(remaining, scheme_type,
                scheme_end)
        }
        SchemeType::NotSpecial => {
            // the anarchist dispatch (parser.rs:460)
            proof {
                let rem = input_rem(&input);
                let post = self.serialization.view();
                assert((post.len() as int)
                    + 16 * (rem.len() as int) + 74
                    <= 0xFFFF_FFFF);
                assert((post.len() as int)
                    + 11 * (rem.len() as int) + 30
                    <= 0xFFFF_FFFF);
                let sub = post.subrange(0, scheme_end as int);
                assert(sub == pre_colon);
                assert(scheme_type == scheme_type_of(sub));
                assert(!is_special(scheme_type));
            }
            self.parse_non_special(input, scheme_type,
                scheme_end)
        }
    }
}

/// Origin Rust (parser.rs:374-392): fn parse_url(mut self, input: &str)
///   -> ParseResult<Url> -- the top entry: the trim, the scheme scan,
/// the scheme-recorded dispatch, and the no-scheme state. CONE (the
/// public `Url::parse` face): base_url is None; the recorded scheme is
/// not "file" (both carried by url_parse_entry_face); the input needs
/// no leading trim (first byte > 0x20) -- the trim model advances pos
/// over leading <=0x20 bytes and the face sits over the raw bytes.
pub exec fn parse_url<'i>(
    &mut self,
    bytes: &'i [u8],
) -> (r: Result<super::Url, ParseError>)
    requires
        machine_domain(bytes@),
        (bytes@.len() as int) <= 0xFFFF_FFFF,
        ((bytes@.len() as int) == 0
            || 0x20u8 < bytes@.index(0)),
        self.context == Context::UrlParser,
        self.base_url.is_none(),
        self.serialization.view().len() == 0,
        url_parse_entry_face(bytes@),
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_ok() ==> super::url_invariant(&r.unwrap())),
        (r.is_err() ==> (r == Err(ParseError::EmptyHost)
            || r == Err(ParseError::InvalidPort)
            || r == Err(ParseError::Overflow)
            || r == Err(ParseError::RelativeUrlWithoutBase))),
{
    // the trim (parser.rs:375)
    let input = new_trim_c0_control_and_space(bytes);
    proof {
        // no leading trim under the first-byte premise: the trimmed
        // remaining IS the raw byte view
        let rem = input_rem(&input);
        let blen = bytes@.len() as int;
        assert((rem.len() as int) <= blen);
        assert((rem.len() as int) == blen) by {
            if (rem.len() as int) < blen {
                // the ensures' leading-block conjunct fires at i = 0
                assert((blen - (rem.len() as int)) > 0);
                assert(bytes@.index(0) <= 0x20u8);
                assert(false);
            }
        }
        assert forall|j: int| 0 <= j && j < (rem.len() as int)
            implies rem.index(j)
                == bytes@.index((blen - (rem.len() as int)) + j) by {}
        assert(rem == bytes@) by {
            assert(rem.len() == bytes@.len());
        }
    }
    // the scheme scan (parser.rs:376-377)
    let sc_r = self.parse_scheme(input);
    match sc_r {
        Result::Ok(remaining) => {
            proof {
                let s = input_rem(&input);
                assert(s == bytes@);
                // the parse_scheme postcondition's witness split
                let kk = choose|k: int|
                    1 <= k
                    && k <= s.len()
                    && self.serialization.view()
                        == lowered_prefix(s.subrange(0, k), k)
                    && super::is_ascii_alpha(s.index(0))
                    && (forall|j: int| 1 <= j && j < k
                        ==> super::is_scheme_char(s.index(j)))
                    && (k < s.len() && s.index(k) == 0x3Au8
                        && input_rem(&remaining)
                            == s.subrange(k + 1, s.len() as int));
                let view = self.serialization.view();
                // the scheme-grammar facts over the lowered view
                assert((view.len() as int) == kk);
                assert(super::is_ascii_alpha(view.index(0))) by {
                    assert(view.index(0)
                        == lower_byte(s.index(0)));
                }
                assert forall|j: int| 1 <= j && j < kk
                    implies super::is_scheme_char(view.index(j)) by {
                    assert(view.index(j)
                        == lower_byte(s.index(j)));
                }
                assert(machine_domain(view)) by {
                    assert forall|j: int| 0 <= j && j < kk
                        implies machine_domain_byte(view.index(j)) by {
                        assert(machine_domain_byte(s.index(j)));
                    }
                }
                assert((view.len() as int) >= 1);
                assert((view.len() as int) <= 0xFFFF_FFFF);
                // the entry face at the split
                assert(s.subrange(kk, s.len() as int).len() as int
                    == (s.len() as int) - kk);
                let st = scheme_type_of(
                    lowered_prefix(s.subrange(0, kk), kk));
                let rem2 = s.subrange(kk + 1, s.len() as int);
                assert(input_rem(&remaining) == rem2);
                assert(scheme_type_of(view) == st) by {
                    assert(view
                        == lowered_prefix(s.subrange(0, kk), kk));
                }
                if st == SchemeType::SpecialNotFile {
                    // the authority-slashes face instantiation at
                    // the scanner's c happens in parse_with_scheme;
                    // this fn only needs parse_with_scheme's class
                    // premise over the input it passes downstream,
                    // which is the face's rem2-fact at any c the
                    // scanner picks
                    assert(input_wf(&remaining));
                } else if st == SchemeType::File {
                    // the file-state faces: the entry face carries
                    // them over rem2 in the same shape the dispatcher
                    // demands (the '//'-conditional entry class over
                    // the twice-split suffix, the '/'-leading pin,
                    // and the folded post-':' budget)
                    assert(input_wf(&remaining));
                } else {
                    // NotSpecial: the anarchist faces
                    assert(st == SchemeType::NotSpecial);
                }
                // context/base_url ride parse_scheme's posts
                assert(self.context == Context::UrlParser);
                assert(self.base_url.is_none());
            }
            self.parse_with_scheme(remaining)
        }
        Result::Err(()) => {
            // the no-scheme state (parser.rs:379-391): base None per
            // the cone -- the upstream else arm
            Err(ParseError::RelativeUrlWithoutBase)
        }
    }
}

/// Origin Rust (parser.rs:1429-1482): fn with_query_and_fragment(mut self,
///   scheme_type, scheme_end, username_end, host_start, host_end, host,
///   port, mut path_start, remaining) -> ParseResult<Url> -- the wrap-up of
/// the scheme faces: the two anarchist "/." fixes for an empty first path
/// segment (parser.rs:1441-1462), then the query/fragment scan
/// (parser.rs:1465-1466), then the Url record build. The self-by-value of
/// upstream is the &mut face here; the record's serialization is the
/// own-bytes copy (bytes_own). The requires cone carries the two entry
/// faces: the authority record (double slash at the scheme's colon, the
/// userinfo/host/port components of the parse phases) or the anarchist
/// record (username_end = host_start = host_end = path_start = scheme_end
/// + 1, no host, no port).
pub exec fn with_query_and_fragment<'i>(
    &mut self,
    scheme_type: SchemeType,
    scheme_end: u32,
    username_end: u32,
    host_start: u32,
    host_end: u32,
    host: super::HostInternal,
    port: Option<u16>,
    path_start: u32,
    remaining: Input<'i>,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&remaining),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        (input_rem(&remaining).len() == 0
            || input_rem(&remaining).index(0) == 0x3Fu8
            || input_rem(&remaining).index(0) == 0x23u8),
        1 <= (scheme_end as int),
        (scheme_end as int) < old(self).serialization.view().len(),
        super::is_ascii_alpha(old(self).serialization.view().index(0)),
        (forall|j: int| 1 <= j && j < (scheme_end as int)
            ==> super::is_scheme_char(
                old(self).serialization.view().index(j))),
        old(self).serialization.view().index(scheme_end as int)
            == 0x3Au8,
        scheme_type == scheme_type_of(old(self).serialization.view()
            .subrange(0, scheme_end as int)),
        (path_start as int) <= old(self).serialization.view().len(),
        old(self).serialization.view().len()
            + 6 * (input_rem(&remaining).len() as int) + 12
            <= 0xFFFF_FFFF,
        (
            (
                // FACE-1: the authority record
                (scheme_end as int) + 3
                    <= old(self).serialization.view().len()
                && old(self).serialization.view()
                    .index((scheme_end as int) + 1) == 0x2Fu8
                && old(self).serialization.view()
                    .index((scheme_end as int) + 2) == 0x2Fu8
                && (scheme_end as int) + 3 <= (username_end as int)
                && (username_end as int)
                    <= old(self).serialization.view().len()
                && (((username_end as int)
                        == old(self).serialization.view().len())
                    ==> ((username_end as int)
                        == (scheme_end as int) + 3))
                && (
                    ((username_end as int)
                        == old(self).serialization.view().len())
                    || (old(self).serialization.view()
                            .index(username_end as int) == 0x3Au8
                        && (host_start as int)
                            >= (username_end as int) + 2
                        && old(self).serialization.view()
                            .index((host_start as int) - 1)
                            == 0x40u8)
                    || (old(self).serialization.view()
                            .index(username_end as int) == 0x40u8
                        && (host_start as int)
                            == (username_end as int) + 1)
                    || ((username_end as int)
                            == (scheme_end as int) + 3
                        && old(self).serialization.view()
                            .index(username_end as int) != 0x3Au8
                        && old(self).serialization.view()
                            .index(username_end as int) != 0x40u8))
                && (username_end as int) <= (host_start as int)
                && (host_start as int)
                    <= old(self).serialization.view().len()
                && (host_end as int) >= (host_start as int)
                && (host_end as int)
                    <= old(self).serialization.view().len()
                && (host_end as int) <= (path_start as int)
                && ((host == super::HostInternal::None)
                    == ((host_start as int) == (host_end as int)))
                && (((path_start as int) == (host_end as int))
                    ==> port.is_none())
                && (((path_start as int) > (host_end as int)) ==> (
                    old(self).serialization.view()
                        .index(host_end as int) == 0x3Au8
                    && (host_end as int) + 2 <= (path_start as int)
                    && (forall|j: int| (host_end as int) + 1 <= j
                            && j < (path_start as int)
                        ==> super::is_dec_digit(
                            old(self).serialization.view().index(j)))
                    && port.is_some()
                    && (port.unwrap() as int)
                        == super::dec_val(old(self).serialization.view()
                            .subrange((host_end as int) + 1,
                                (path_start as int)))))
                && (((path_start as int)
                        < old(self).serialization.view().len()) ==> (
                    old(self).serialization.view()
                        .index(path_start as int) == 0x2Fu8
                    || old(self).serialization.view()
                        .index(path_start as int) == 0x23u8
                    || old(self).serialization.view()
                        .index(path_start as int) == 0x3Fu8))
            )
            ||
            (
                // FACE-2: the anarchist record
                (username_end as int) == (scheme_end as int) + 1
                && (host_start as int) == (scheme_end as int) + 1
                && (host_end as int) == (scheme_end as int) + 1
                && (path_start as int) == (scheme_end as int) + 1
                && host == super::HostInternal::None
                && port.is_none()
            )
            || (
                // FACE-3: the opaque-pinned anarchist entry of the
                // base-merge arms (the "/." between the host region and
                // an "//"-headed opaque path, the record shape the
                // case-1 insert builds). The wrap-up below either fires
                // the case-2 fix (the path head is no longer "//", the
                // pin collapses and path_start returns to scheme_end+1)
                // or keeps the pin (the path head still "//", the
                // opaque face of the record). Both branches are read
                // off the entry bytes: the inner probe guard decides.
                (username_end as int) == (scheme_end as int) + 1
                && (host_start as int) == (scheme_end as int) + 1
                && (host_end as int) == (scheme_end as int) + 1
                && host == super::HostInternal::None
                && port.is_none()
                && (path_start as int) == (scheme_end as int) + 3
                && (path_start as int)
                    < old(self).serialization.view().len()
                && old(self).serialization.view()
                    .index((scheme_end as int) + 1) == 0x2Fu8
                && old(self).serialization.view()
                    .index((scheme_end as int) + 2) == 0x2Eu8
                && old(self).serialization.view()
                    .index(path_start as int) == 0x2Fu8
            )
        ),
    ensures
        machine_domain(final(self).serialization.view()),
        r.is_ok() ==> super::url_invariant(&r.unwrap()),
        r.is_err() ==> (r == Err(ParseError::Overflow)),
{
    let ghost pre = self.serialization.view();
    let mut path_start_m: u32 = path_start;
    let mut inserted: bool = false;
    let n0 = self.serialization.len();
    let se_u = scheme_end as usize;
    let psu = path_start as usize;
    // the case-1 anarchist fix (parser.rs:1441-1445): the path head is
    // "//", the base URL's first segment gets the "/." prefix
    if path_start == scheme_end + 1
        && psu + 2 <= n0
        && self.serialization[psu] == 0x2Fu8
        && self.serialization[psu + 1] == 0x2Fu8
    {
        anar_insert_dot(&mut self.serialization, psu);
        path_start_m = path_start + 2;
        inserted = true;
    } else if path_start == scheme_end + 3
        && se_u + 3 <= n0
        && self.serialization[se_u] == 0x3Au8
        && self.serialization[se_u + 1] == 0x2Fu8
        && self.serialization[se_u + 2] == 0x2Eu8
        && psu < n0
        && self.serialization[psu] == 0x2Fu8
    {
        // the case-2 anarchist fix (parser.rs:1447-1461): the base URL
        // had a "/." between the host and the path (the opaque-pinned
        // anarchist entries of the base-merge arms -- FACE-3 below --
        // are the revival surface); the inner probe is origin's own
        // `get(ps+1) != Some(b'/')` guard
        if psu + 1 >= n0 || self.serialization[psu + 1] != 0x2Fu8 {
            anar_remove_dot(&mut self.serialization, scheme_end);
            path_start_m = path_start - 2;
        } else {
            // the guard converse (psu+1 < n0 and the '/' there) rides
            // the else-branch's negated condition: the record keeps the
            // opaque pin, and the final proof branch reads the two
            // facts via this else-block
            proof {
                assert((psu as int) + 1 < n0 as int);
                assert(pre.index((psu as int) + 1) == 0x2Fu8);
            }
        }
    }
    let ghost postarms = self.serialization.view();
    let nq0 = self.serialization.len();
    // the query/fragment scan (parser.rs:1465-1466; the None face of
    // upstream's match at parser.rs:1508 is the empty-input early return)
    let (qs, fs) = if remaining.is_empty() {
        (Option::<u32>::None, Option::<u32>::None)
    } else {
        match self.parse_query_and_fragment(scheme_type, scheme_end,
            remaining)
        {
            Err(e) => return Err(e),
            Ok(qfp) => qfp,
        }
    };
    let u = super::Url {
        serialization: bytes_own(&self.serialization),
        scheme_end: scheme_end,
        username_end: username_end,
        host_start: host_start,
        host_end: host_end,
        host: host,
        port: port,
        path_start: path_start_m,
        query_start: qs,
        fragment_start: fs,
    };
    proof {
        let serf = self.serialization.view();
        let n = serf.len() as int;
        let se = scheme_end as int;
        assert(u.serialization.view() == serf);
        assert(postarms == pre
            || postarms.len() == pre.len() + 2
            || postarms.len() == pre.len() - 2);
        assert(machine_domain(serf));
        // the final length bound (the budget minus slack)
        let rem_len = input_rem(&remaining).len() as int;
        if input_rem(&remaining).len() == 0 {
            assert(serf.len() == postarms.len());
            assert(n == (postarms.len() as int));
        } else {
            assert(n <= (postarms.len() as int)
                + 6 * rem_len + 4);
        }
        assert((n0 as int) <= (pre.len() as int) + 2);
        assert(n <= (pre.len() as int) + 6 * rem_len + 12);
        assert(n <= 0xFFFF_FFFF);
        // the query/fragment scan preserves every pre-scan byte
        assert forall|j: int| 0 <= j < postarms.len()
            implies serf.index(j) == postarms.index(j) by {}
        let nq: int = nq0 as int;
        // the query/fragment positions on the final bytes
        if qs.is_some() {
            assert((qs.unwrap() as int) == nq);
            assert((qs.unwrap() as int) < n);
            assert(serf.index(qs.unwrap() as int) == 0x3Fu8);
            assert((qs.unwrap() as int) >= (path_start_m as int));
        }
        if fs.is_some() {
            assert(fs.unwrap() as int >= nq);
            assert((fs.unwrap() as int) < n);
            assert(serf.index(fs.unwrap() as int) == 0x23u8);
            assert((fs.unwrap() as int) >= (path_start_m as int));
            if qs.is_none() {
                assert(fs.unwrap() as int == nq);
            }
        }
        if path_start == scheme_end + 1 {
            // FACE-2: the anarchist record
            assert((path_start_m as int) == se + 1
                || (path_start_m as int) == se + 3);
            if !inserted {
                // the untouched path: no arm ran (case-2 needs
                // scheme_end + 3 = path_start, contradicting se + 1)
                assert(postarms == pre);
                assert(path_start_m as int == se + 1);
                // the case-1 probe failed on the pre bytes, and the
                // scan only appends '?'/'#'-headed parts
                if (n0 as int) >= se + 3 {
                    // pre bytes survive the scan unchanged
                    assert(serf.index(se + 1) == pre.index(se + 1));
                    assert(serf.index(se + 2) == pre.index(se + 2));
                    if serf.index(se + 1) == 0x2Fu8
                        && serf.index(se + 2) == 0x2Fu8
                    {
                        // the probe would have fired: contradiction
                        assert(false);
                    }
                } else if (n0 as int) == se + 2 {
                    // the only byte that can appear at se+2 is the
                    // '?'/'#' head of the scan
                    if se + 3 <= n {
                        if qs.is_some() {
                            assert(serf.index(se + 2) == 0x3Fu8);
                        } else {
                            assert(fs.is_some());
                            assert(serf.index(se + 2) == 0x23u8);
                        }
                    }
                } else {
                    // n0 == se+1 (the path anchor was never written):
                    // a scan head at se+1 is '?'/'#', never '/'
                    if se + 3 <= n {
                        if qs.is_some() {
                            assert(serf.index(se + 1) == 0x3Fu8);
                        } else {
                            assert(fs.is_some());
                            assert(serf.index(se + 1) == 0x23u8);
                        }
                    }
                }
                assert(!(se + 3 <= n
                    && serf.index(se + 1) == 0x2Fu8
                    && serf.index(se + 2) == 0x2Fu8));
                assert(!super::has_authority_view(&u));
                assert((u.path_start as int) == se + 1);
                wqaf_face2_url_ok(&u, false);
            } else {
                // the insert: "/." sits at se+1/se+2 with the old "//"
                // path head behind it (the opaque-Path face)
                assert(postarms.len() == pre.len() + 2);
                assert((path_start_m as int) == se + 3);
                assert(postarms.index(se + 1) == 0x2Fu8);
                assert(postarms.index(se + 2) == 0x2Eu8);
                assert(serf.index(se + 1) == 0x2Fu8);
                assert(serf.index(se + 2) == 0x2Eu8);
                assert(serf.index(se + 3) == pre.index(se + 1));
                assert(serf.index((se + 3) + 1) == pre.index(se + 2));
                assert(serf.index(path_start_m as int) == 0x2Fu8);
                assert(serf.index((path_start_m as int) + 1)
                    == 0x2Fu8);
                assert((path_start_m as int) + 2 <= n);
                assert((path_start_m as int) + 2
                    <= super::path_end_view(&u));
                wqaf_face2_url_ok(&u, true);
            }
        } else if (path_start == scheme_end + 3)
            && (username_end == scheme_end + 1)
            && (host_start == scheme_end + 1)
            && (host_end == scheme_end + 1)
            && host == super::HostInternal::None
            && port.is_none()
        {
            // FACE-3: the opaque-pinned anarchist entry (the case-2
            // revival of the base-merge arms). Case-1 cannot run (its
            // probe demands path_start == scheme_end + 1, the face pins
            // scheme_end + 3).
            assert(!inserted);
            assert((path_start_m as int) == se + 3
                || (path_start_m as int) == se + 1);
            if (postarms.len() as int) == (pre.len() as int) - 2 {
                // the fired arm: the ":/." pin collapsed, the moved-down
                // path head is the '/' at se+1
                assert((path_start_m as int) == se + 1);
                assert((pre.len() as int) >= se + 4);
                assert(postarms.index(se + 1) == pre.index(se + 3));
                assert(postarms.index(se + 1) == 0x2Fu8);
                assert(se + 2 <= postarms.len() as int);
                if se + 2 < (postarms.len() as int) {
                    // the old path byte behind the anchor lands at se+2
                    // and the probe guard excludes '/' there
                    assert(postarms.index(se + 2)
                        == pre.index((se + 3) + 1));
                    assert(postarms.index(se + 2) != 0x2Fu8);
                } else {
                    // the moved-down path was exactly the '/' anchor:
                    // the only bytes that can appear at se+2 are the
                    // '?'/'#' heads of the scan
                    if se + 2 < n {
                        if qs.is_some() {
                            assert((qs.unwrap() as int) == se + 2);
                        } else {
                            assert(fs.is_some());
                            assert((fs.unwrap() as int) == se + 2);
                        }
                    }
                }
                // the regular anarchist face: no authority and no
                // opaque pin (the byte at se+2 is absent, a '?'/'#'
                // scan head, or a non-'/' path byte)
                assert(!(se + 3 <= n
                    && serf.index(se + 1) == 0x2Fu8
                    && serf.index(se + 2) == 0x2Fu8));
                assert(!(((path_start_m as int) + 2
                    <= super::path_end_view(&u))
                    && serf.index((path_start_m as int) + 1)
                        == 0x2Fu8));
                wqaf_face2_url_ok(&u, false);
            } else {
                // the probe's else: the record keeps the pin (the
                // capture at the inner else block pinned the second
                // '/' of the path head)
                assert(postarms == pre);
                assert((path_start_m as int) == se + 3);
                assert((psu as int) + 1 < n0 as int);
                assert(pre.index((psu as int) + 1) == 0x2Fu8);
                assert(serf.index(path_start as int) == 0x2Fu8);
                assert(serf.index((path_start as int) + 1) == 0x2Fu8);
                assert(n >= postarms.len() as int);
                assert((path_start as int) + 2
                    <= super::path_end_view(&u));
                wqaf_face2_url_ok(&u, true);
            }
        } else {
            // FACE-1: the authority record; neither arm ran (case-1
            // needs path_start == se + 1 against the se + 3 floor of
            // the face, case-2 needs the '.' that the face's second
            // slash byte forbids)
            assert(postarms == pre);
            assert(path_start_m as int == path_start as int);
            // every byte below the scan start survives; the face bound
            // keeps se+1, se+2 and the component positions below n0
            assert(serf.index(0) == pre.index(0));
            assert(serf.index(se) == pre.index(se));
            assert(serf.index(se + 1) == pre.index(se + 1));
            assert(serf.index(se + 2) == pre.index(se + 2));
            assert(username_end as int <= n);
            if (username_end as int) != n {
                if (username_end as int) < postarms.len() {
                    assert(serf.index(username_end as int)
                        == pre.index(username_end as int));
                }
                if (host_start as int) - 1 < postarms.len() {
                    assert(serf.index((host_start as int) - 1)
                        == pre.index((host_start as int) - 1));
                }
            }
            if (path_start as int) > (host_end as int) {
                assert(serf.index(host_end as int)
                    == pre.index(host_end as int));
            }
            if (path_start as int) < (postarms.len() as int) {
            assert(serf.index(path_start as int)
                == pre.index(path_start as int));
            }
            // port-region bridge: the digit bytes and their dec_val
            // carry from pre through the unchanged prefix
            if (path_start as int) > (host_end as int) {
                assert forall|j: int| (host_end as int) + 1 <= j
                    && j < (path_start as int)
                    implies super::is_dec_digit(serf.index(j)) by {
                    assert(serf.index(j) == postarms.index(j));
                    assert(super::is_dec_digit(pre.index(j)));
                }
                assert(serf.subrange((host_end as int) + 1,
                    (path_start as int))
                    == pre.subrange((host_end as int) + 1,
                        (path_start as int)));
            }
            // scheme-classification bridge: the scheme byte range is
            // the pre range, so scheme_type_of agrees
            assert(serf.subrange(0, se) == pre.subrange(0, se));
            wqaf_face1_url_ok(&u, scheme_type);
        }
        assert(super::url_invariant(&u));
    }
    Ok(u)
}

/// The deep-host application of the file-host state (the
/// Host::parse_cow step of parse_file_host, parser.rs:1047-1055): on
/// the restricted class the declared deep premise returns the identity
/// Domain over the candidate; the "localhost" domain keeps the bytes
/// unwritten with no host (parser.rs:1048-1050), any other candidate
/// is written into the serialization with the Domain tag
/// (parser.rs:1053).  The digest mirrors the hosted branch of
/// parse_file_host's contract over the helper's own entry state (the
/// caller's serialization is the o of the digest).
exec fn pf_host_deep_write(
    ser: &mut Vec<u8>,
    cand: &Vec<u8>,
) -> (wr: Result<bool, ParseError>)
    requires
        machine_domain(old(ser).view()),
        machine_domain(cand.view()),
        host_run_class(cand.view()),
        (cand.view().len() as int) > 0,
        (old(ser).view().len() as int)
            + (cand.view().len() as int) <= 0xFFFF_FFFF,
    ensures
        ({
            let o = old(ser).view();
            let f = final(ser).view();
            &&& machine_domain(f)
            &&& wr.is_ok()
            &&& (wr.is_ok() ==> ({
                let hh = wr.unwrap();
                &&& (hh ==> ({
                    &&& (f.len() as int) > (o.len() as int)
                    &&& f == o + cand.view()
                    &&& 0x61u8 <= f.index(o.len() as int)
                    &&& f.index(o.len() as int) <= 0x7Au8
                    &&& 0x61u8
                        <= f.index((f.len() as int) - 1)
                    &&& f.index((f.len() as int) - 1)
                        <= 0x7Au8}))
                &&& (!hh ==> (f == o))
            }))
        }),
{
    let deep = host_parse_deep(cand, 0, cand.len());
    match deep {
        Result::Err(e) => {
            // unreachable: the declared premise pins the ok outcome
            // on the class
            proof {
                assert(false);
            }
            Err(e)
        }
        Result::Ok((host, hs)) => {
            match host {
                super::Host::Domain(d) => {
                    // the "localhost" drop (parser.rs:1048-1050)
                    if bytes_eq(&d,
                        &vec![0x6Cu8, 0x6F, 0x63, 0x61,
                            0x6C, 0x68, 0x6F, 0x73, 0x74])
                    {
                        Ok(false)
                    } else {
                        // the write (parser.rs:1053)
                        proof {
                            assert(hs.view() == cand.view());
                        }
                        vec_append_bytes(ser, &hs);
                        proof {
                            let f = ser.view();
                            let o = old(ser).view();
                            assert(f == o + hs.view());
                            machine_domain_add(o, hs.view());
                            assert(f == o + cand.view());
                            let c = cand.view();
                            vstd::seq::lemma_seq_add_len(o, c);
                            assert((c.len() as int) > 0);
                            assert((f.len() as int)
                                == (o.len() as int)
                                    + (c.len() as int));
                            assert(host_run_class(c));
                            vstd::seq::lemma_seq_add_index2(o, c,
                                (o.len() as int));
                            vstd::seq::lemma_seq_add_index2(o, c,
                                (f.len() as int) - 1);
                            assert(0x61u8
                                <= f.index((o.len() as int)));
                            assert(
                                f.index((o.len() as int))
                                    <= 0x7Au8);
                            assert(0x61u8
                                <= f.index(
                                    (f.len() as int) - 1));
                            assert(
                                f.index((f.len() as int) - 1)
                                    <= 0x7Au8);
                        }
                        Ok(true)
                    }
                }
                _ => {
                    // unreachable: the declared premise pins the
                    // Domain tag on the class
                    proof {
                        assert(false);
                    }
                    Err(ParseError::EmptyHost)
                }
            }
        }
    }
}

/// Origin Rust (parser.rs:1037-1060): fn parse_file_host<'i>(&mut self,
///   input: Input<'i>) -> ParseResult<(bool, HostInternal, Input<'i>)> --
/// the file-host state's deep-host step: scan the candidate
/// (file_host, parser.rs:1042/1062), the empty candidate keeps the
/// None tag, the "localhost" domain maps to no host (parser.rs:1048-1050,
/// the bytes are NOT written), any other candidate is the deep-host
/// Host::parse_cow (host.rs:92-97) written into the serialization
/// (parser.rs:1053) with the Domain tag.  CONE: the entry class
/// (file_host_entry_class) pins every candidate the scan can name
/// inside the declared deep-host premise's restricted class; on the
/// class the premise never fails (r.is_ok() below).
pub exec fn parse_file_host<'i>(
    &mut self,
    input: Input<'i>,
) -> (r: Result<(bool, super::HostInternal, Input<'i>), ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        machine_domain(old(self).serialization.view()),
        (old(self).serialization.view().len() as int)
            + (input_rem(&input).len() as int) + 8
            <= 0xFFFF_FFFF,
        file_host_entry_class(input_rem(&input)),
    ensures
        ({
            let o = old(self).serialization.view();
            let s = input_rem(&input);
            let f = final(self).serialization.view();
            &&& r.is_ok()
            &&& final(self).context == Context::UrlParser
            &&& machine_domain(f)
            &&& (r.is_ok() ==> ({
                let (hh, tag, rem) = r.unwrap();
                &&& input_wf(&rem)
                &&& (input_rem(&rem).len() as int)
                    <= (s.len() as int)
                &&& (hh ==> ({
                    &&& (f.len() as int) > (o.len() as int)
                    &&& f == o + s.subrange(0,
                        (f.len() as int) - (o.len() as int))
                    &&& host_run_class(s.subrange(0,
                        (f.len() as int) - (o.len() as int)))
                    &&& 0x61u8 <= f.index(o.len() as int)
                    &&& f.index(o.len() as int) <= 0x7Au8
                    &&& 0x61u8 <= f.index(f.len() as int - 1)
                    &&& f.index(f.len() as int - 1) <= 0x7Au8
                    &&& tag == super::HostInternal::Domain
                    &&& input_rem(&rem)
                        == s.subrange(
                            (f.len() as int) - (o.len() as int),
                            s.len() as int)
                    &&& (input_rem(&rem).len() as int)
                        == (s.len() as int)
                            - ((f.len() as int)
                                - (o.len() as int))
                }))
                &&& (!hh ==> ({
                    &&& tag == super::HostInternal::None
                    &&& f == o
                }))
            }))
        }),
{
    let ghost o = self.serialization.view();
    let ghost s0 = input_rem(&input);
    let fh = file_host(&input);
    match fh {
        Result::Err(e) => {
            // unreachable: file_host never fails (both upstream arms
            // are Ok, parser.rs:1089/1091)
            proof {
                assert(false);
            }
            Err(e)
        }
        Result::Ok((is_sb, hstr, rem)) => {
            let w = hstr.len();
            if w == 0 {
                // the empty candidate (parser.rs:1043-1045): no host
                Ok((false, super::HostInternal::None, rem))
            } else {
                // the entry-class instantiation at the scan's split:
                // the premise fires for the candidate prefix
                proof {
                    assert(hstr.view() == s0.subrange(0, w as int));
                    file_wall_free_iff(s0, w as int);
                    assert(file_wall_free(s0, w as int));
                    assert((w as int) == (s0.len() as int)
                        || file_wall_byte(s0.index(w as int)));
                    assert((s0.subrange(w as int, s0.len() as int).len()
                        as int) <= (s0.len() as int));
                    assert(host_run_class(hstr.view()));
                }
                // the deep-host face (Host::parse_cow on the
                // candidate, parser.rs:1047-1055) as the helper step
                let ghost oc = self.serialization.view();
                proof {
                    assert(oc == o);
                }
                let dw = Self::pf_host_deep_write(
                    &mut self.serialization, &hstr);
                match dw {
                    Result::Err(e) => {
                        // unreachable: pinned on the class
                        proof {
                            assert(false);
                        }
                        Err(e)
                    }
                    Result::Ok(hh) => {
                        proof {
                            let f = self.serialization.view();
                            let cand = s0.subrange(0, w as int);
                            assert(cand == hstr.view());
                            if hh {
                                assert(f == oc + cand);
                                assert(f == o + cand);
                                assert((f.len() as int)
                                    == (o.len() as int)
                                        + (w as int));
                            } else {
                                assert(f == oc);
                                assert(f == o);
                            }
                        }
                        if hh {
                            proof {
                                // the remainder bridge from the scan's
                                // split (w = the candidate length)
                                let f = self.serialization.view();
                                assert((w as int)
                                    == (f.len() as int)
                                        - (o.len() as int));
                                assert(input_rem(&rem)
                                    == s0.subrange(
                                        (w as int),
                                        (s0.len() as int)));
                                assert((input_rem(&rem).len() as int)
                                    == (s0.len() as int)
                                        - (w as int));
                                // the class letters carried through the
                                // helper's digest (its base oc == o)
                                assert(0x61u8
                                    <= f.index((o.len() as int)));
                                assert(
                                    f.index((o.len() as int))
                                        <= 0x7Au8);
                                assert(0x61u8
                                    <= f.index(
                                        (f.len() as int) - 1));
                                assert(
                                    f.index((f.len() as int) - 1)
                                        <= 0x7Au8);
                                assert(machine_domain(f));
                            }
                            Ok((true,
                                super::HostInternal::Domain,
                                rem))
                        } else {
                            Ok((false,
                                super::HostInternal::None,
                                rem))
                        }
                    }
                }
            }
        }
    }
}

/// The scheme-region face over the serialized file-state prefix: the
/// recorded bytes at [0,4) are "file" and the ':' at 4 pin the File
/// classification of the recorded scheme (the literal dance shared by
/// the arms of the file state).
pub proof fn pf_file_scheme_face(f: Seq<u8>)
    requires
        (f.len() as int) >= 7,
        f.index(0) == 0x66u8,
        f.index(1) == 0x69u8,
        f.index(2) == 0x6cu8,
        f.index(3) == 0x65u8,
        f.index(4) == 0x3Au8,
    ensures
        super::is_ascii_alpha(f.index(0)),
        (forall|j: int| 1 <= j && j < 4
            ==> super::is_scheme_char(f.index(j))),
        f.index(4) == 0x3Au8,
        scheme_type_of(f.subrange(0, 4)) == SchemeType::File,
{
    let lit = seq![0x66u8, 0x69, 0x6c, 0x65];
    assert(f.subrange(0, 4).len() == 4);
    assert forall|j: int| 0 <= j && j < 4
        implies f.subrange(0, 4).index(j) == lit.index(j) by {
        vstd::seq::lemma_seq_subrange_index(f, 0, 4, j);
        if j == 0 {
            assert(f.index(j) == 0x66u8);
            assert(lit.index(j) == 0x66u8);
        } else if j == 1 {
            assert(f.index(j) == 0x69u8);
            assert(lit.index(j) == 0x69u8);
        } else if j == 2 {
            assert(f.index(j) == 0x6cu8);
            assert(lit.index(j) == 0x6cu8);
        } else {
            assert(f.index(j) == 0x65u8);
            assert(lit.index(j) == 0x65u8);
        }
    }
    vstd::seq::lemma_seq_ext_equal(f.subrange(0, 4), lit);
    assert(scheme_type_of(lit) == SchemeType::File);
    assert(super::is_ascii_alpha(0x66u8));
    assert(super::is_scheme_char(0x69u8));
    assert(super::is_scheme_char(0x6cu8));
    assert(super::is_scheme_char(0x65u8));
}

/// Origin Rust (parser.rs:501-545, the two-slash branch of the file
/// state): the file host state -- the "file://" push (parser.rs:518),
/// parse_file_host over the input past the two slashes (parser.rs:521),
/// and the path phase on the scanned split: parse_path_start when the
/// state recorded a host (parser.rs:524-525), the '/' anchor push and
/// parse_path otherwise (parser.rs:526-530).  The direct record
/// assembly of parser.rs:534-545 -- username_end = host_start =
/// "file://".len(), path_start = host_end, port None -- folds into the
/// shared wrap-up with_query_and_fragment; the two anarchist "/."
/// fixes are provably dormant at this state (case-1 needs
/// path_start == scheme_end + 1 against the se+3 authority floor of the
/// record; case-2 needs the '.' byte where the "file://" face pins the
/// second '/'), and the record fields are value-equal to the upstream
/// assembly.
pub exec fn pf_hosted_arm<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        scheme_type == SchemeType::File,
        machine_domain(old(self).serialization.view()),
        (old(self).serialization.view().len() as int) == 0,
        file_host_entry_class(input_rem(&input)),
        20 * (input_rem(&input).len() as int) + 176
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_ok() ==> super::url_invariant(&r.unwrap())),
        (r.is_err() ==> (r == Err(ParseError::Overflow))),
{
    let ghost sl = input_rem(&input);
    // the "file://" push (parser.rs:518)
    push_file_prefix(&mut self.serialization, false);
    let ghost fa = self.serialization.view();
    // the file host state (parser.rs:521)
    let pf = self.parse_file_host(input);
    match pf {
        Result::Err(e) => Err(e),
        Result::Ok((hflag, htag, remh)) => {
            let ghost fb = self.serialization.view();
            proof {
                if hflag {
                    assert(fb == fa + sl.subrange(0,
                        (fb.len() as int) - 7));
                    let cand = sl.subrange(0,
                        (fb.len() as int) - 7);
                    assert((input_rem(&remh).len() as int)
                        == (sl.len() as int)
                            - ((fb.len() as int) - 7));
                    assert((fb.len() as int) - 7
                        <= (sl.len() as int));
                    assert((cand.len() as int)
                        == (fb.len() as int) - 7);
                    assert((cand.len() as int)
                        <= (sl.len() as int));
                    assert((fb.len() as int)
                        <= 7 + (sl.len() as int));
                    assert((fb.len() as int)
                        <= 20 * (sl.len() as int) + 176);
                } else {
                    assert(fb == fa);
                    assert((fa.len() as int) == 7);
                    assert((fb.len() as int) == 7);
                    assert(htag
                        == super::HostInternal::None);
                }
                assert((fb.len() as int)
                    <= 0xFFFF_FFFF);
            }
            let host_end32: u32 = to_u32_ser(&self.serialization);
            proof {
                assert((host_end32 as int)
                    == (fb.len() as int));
                if hflag {
                    assert((fb.len() as int) > 7);
                    assert(htag
                        == super::HostInternal::Domain);
                    assert(0x61u8 <= fb.index(7));
                    assert(fb.index(7) <= 0x7Au8);
                    assert(0x61u8
                        <= fb.index((fb.len() as int) - 1));
                    assert(
                        fb.index((fb.len() as int) - 1)
                            <= 0x7Au8);
                    assert(fb == fa + sl.subrange(0,
                        (fb.len() as int) - 7));
                } else {
                    assert((fb.len() as int) == 7);
                    assert(htag
                        == super::HostInternal::None);
                    assert(fb == fa);
                }
            }
            if hflag {
                // the hosted split: parse_path_start at the host end
                // (parser.rs:524-525)
                let psx = self.serialization.len();
                let mut hh2: bool = match htag {
                    super::HostInternal::None => false,
                    _ => true,
                };
                proof {
                    let sh = input_rem(&remh);
                    assert((psx as int)
                        == (fb.len() as int));
                    assert(is_special(scheme_type));
                    assert(fb.index((fb.len() as int) - 1)
                        != 0x2Fu8);
                    assert((sh.len() as int)
                        <= (sl.len() as int));
                    assert((fb.len() as int)
                        <= 7 + (sl.len() as int));
                    assert((fb.len() as int)
                        + 5 * (sh.len() as int) + 38
                        <= 7 + (sl.len() as int)
                            + 5 * (sl.len() as int) + 38);
                    assert((fb.len() as int)
                        + 5 * (sh.len() as int) + 38
                        <= 20 * (sl.len() as int) + 176);
                }
                let rps = self.parse_path_start(scheme_type,
                    &mut hh2, remh, psx);
                let rem2 = rps.0;
                proof {
                    // the wrap-up face at the shared wrap-up call
                    let f = self.serialization.view();
                    let rm = input_rem(&rem2);
                    let sh = input_rem(&remh);
                    let cand = sl.subrange(0,
                        (fb.len() as int) - 7);
                    vstd::seq::lemma_seq_add_len(fa, cand);
                    assert((cand.len() as int)
                        == (fb.len() as int) - 7);
                    assert((cand.len() as int)
                        <= (sl.len() as int));
                    assert((sh.len() as int)
                        <= (sl.len() as int));
                    assert((rm.len() as int)
                        <= (sh.len() as int));
                    assert((fb.len() as int)
                        <= 7 + (sl.len() as int));
                    assert(fb == fa + cand);
                    assert forall|j: int| 0 <= j && j < 7
                        implies fb.index(j) == fa.index(j) by {
                        vstd::seq::lemma_seq_add_index1(fa, cand, j);
                    }
                    assert forall|j: int| 0 <= j
                        && j < (psx as int)
                        implies f.index(j) == fb.index(j) by {
                    }
                    assert(machine_domain(f));
                    assert(input_wf(&rem2));
                    assert(rm.len() == 0
                        || rm.index(0) == 0x3Fu8
                        || rm.index(0) == 0x23u8);
                    assert((f.len() as int) >= 8);
                    Self::pf_file_scheme_face(f);
                    assert(scheme_type_of(f.subrange(0, 4))
                        == SchemeType::File);
                    assert(scheme_type
                        == SchemeType::File);
                    assert((4 as int) + 3 <= (f.len() as int));
                    assert(f.index((4 as int) + 1) == 0x2Fu8);
                    assert(f.index((4 as int) + 2) == 0x2Fu8);
                    assert((7 as int)
                        >= (4 as int) + 3);
                    assert((7 as int) <= (f.len() as int));
                    assert((7 as int) != (f.len() as int));
                    assert(f.index(7) != 0x3Au8);
                    assert(f.index(7) != 0x40u8);
                    assert((7 as int) == (4 as int) + 3);
                    assert((host_end32 as int) >= (7 as int));
                    assert((host_end32 as int)
                        <= (f.len() as int));
                    assert((host_end32 as int)
                        == (psx as int));
                    assert((htag
                        == super::HostInternal::None)
                        == ((7 as int)
                            == (host_end32 as int)));
                    assert((f.len() as int)
                        >= (psx as int));
                    assert((psx as int) >= 8);
                    assert(((f.len() as int) > (psx as int))
                        ==> f.index(psx as int) == 0x2Fu8);
                    // the budget chain for the wrap-up's scan (the
                    // path phase grew from fb by at most 5|remh| + 7)
                    assert((f.len() as int)
                        <= (fb.len() as int)
                            + 5 * (sh.len() as int) + 7);
                    assert((rm.len() as int)
                        <= (sh.len() as int));
                    assert((sh.len() as int)
                        <= (sl.len() as int));
                    assert((fb.len() as int)
                        <= 7 + (sl.len() as int));
                    assert((f.len() as int)
                        + 6 * (rm.len() as int) + 12
                        <= 20 * (sl.len() as int) + 176);
                }
                self.with_query_and_fragment(scheme_type, 4, 7,
                    7, host_end32, htag, Option::None,
                    host_end32, rem2)
            } else {
                // no host on the split -- the empty candidate, the
                // "localhost" drop of parser.rs:1048-1050, or the
                // drive-form short-circuit of file_host: the '/'
                // anchor and parse_path over the scanned remaining
                // (parser.rs:526-530)
                let mut hh2: bool = match htag {
                    super::HostInternal::None => false,
                    _ => true,
                };
                proof {
                    assert((self.serialization.view().len() as int)
                        == 7);
                }
                // the '/' anchor push (parser.rs:527-528)
                let ghost pre_slash = self.serialization.view();
                self.serialization.push(0x2Fu8);
                proof {
                    assert(self.serialization.view()
                        == pre_slash.push(0x2Fu8));
                    assert(pre_slash.push(0x2Fu8)
                        == pre_slash + seq![0x2Fu8]);
                    machine_domain_add(pre_slash, seq![0x2Fu8]);
                }
                let psx: usize = 7;
                proof {
                    let f = self.serialization.view();
                    let sh = input_rem(&remh);
                    assert((f.len() as int)
                        == (psx as int) + 1);
                    assert(f.index(psx as int) == 0x2Fu8);
                    assert((f.len() as int)
                        + 5 * (sh.len() as int) + 32
                        <= 0xFFFF_FFFF);
                }
                let rem2 = self.parse_path(scheme_type, psx,
                    &mut hh2, remh);
                proof {
                    // the wrap-up face at the shared wrap-up call
                    let f = self.serialization.view();
                    let rm = input_rem(&rem2);
                    assert(fb == fa);
                    assert forall|j: int| 0 <= j && j < 7
                        implies f.index(j) == fb.index(j) by {
                    }
                    assert(machine_domain(f));
                    assert(input_wf(&rem2));
                    assert(rm.len() == 0
                        || rm.index(0) == 0x3Fu8
                        || rm.index(0) == 0x23u8);
                    assert((f.len() as int) >= 7);
                    Self::pf_file_scheme_face(f);
                    assert(scheme_type_of(f.subrange(0, 4))
                        == SchemeType::File);
                    assert(scheme_type == SchemeType::File);
                    assert((4 as int) + 3 <= (f.len() as int));
                    assert(f.index((4 as int) + 1) == 0x2Fu8);
                    assert(f.index((4 as int) + 2) == 0x2Fu8);
                    assert((7 as int) >= (4 as int) + 3);
                    assert((7 as int) <= (f.len() as int));
                    assert((7 as int) == (4 as int) + 3);
                    if (f.len() as int) == 7 {
                        // the anchor-as-EOF corner: the record ends at
                        // the serialization end
                        assert((7 as int) == (f.len() as int));
                    } else {
                        assert(((f.len() as int) > (psx as int))
                            ==> f.index(psx as int) == 0x2Fu8);
                        assert(f.index(7) == 0x2Fu8);
                        assert(f.index(7) != 0x3Au8);
                        assert(f.index(7) != 0x40u8);
                        assert((7 as int) != (f.len() as int));
                    }
                    assert(htag == super::HostInternal::None);
                    // the budget chain for the wrap-up's scan (the
                    // path phase grew from the 8-byte anchor state by
                    // at most 5|remh| + 6)
                    let sh = input_rem(&remh);
                    assert((f.len() as int)
                        <= 8 + 5 * (sh.len() as int) + 6);
                    assert((rm.len() as int)
                        <= (sh.len() as int));
                    assert((sh.len() as int)
                        <= (sl.len() as int));
                    assert((f.len() as int)
                        + 6 * (rm.len() as int) + 12
                        <= 20 * (sl.len() as int) + 176);
                }
                self.with_query_and_fragment(scheme_type, 4, 7,
                    7, 7, htag, Option::None, 7, rem2)
            }
        }
    }
}

/// Origin Rust (parser.rs:546-597, the one-slash branch of the file
/// state): push "file://" (parser.rs:547) -- the windows-drive-segment
/// probe of parser.rs:552-563 guards only the base-copy block, dead
/// under the file-state cone (the base is None); the probe does not
/// affect this control flow.  The parse-path input selection of
/// parser.rs:565-574 lands on the full input: the first byte is the
/// '/' of the branch guard (the transcription-domain cone), so
/// parse_path's '/'-anchored entry consumes it.  The record fields
/// (parser.rs:585-596) fold into the shared wrap-up, value-equal.
pub exec fn pf_slash1_arm<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        scheme_type == SchemeType::File,
        machine_domain(old(self).serialization.view()),
        (old(self).serialization.view().len() as int) == 0,
        (input_rem(&input).len() as int) > 0,
        input_rem(&input).index(0) == 0x2Fu8,
        20 * (input_rem(&input).len() as int) + 136
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_ok() ==> super::url_invariant(&r.unwrap())),
        (r.is_err() ==> (r == Err(ParseError::Overflow))),
{
    let ghost si = input_rem(&input);
    // the "file://" push (parser.rs:547)
    push_file_prefix(&mut self.serialization, false);
    let ghost fa = self.serialization.view();
    let mut hh2: bool = false;
    let psx: usize = 7;
    proof {
        let f = self.serialization.view();
        assert((f.len() as int) == 7);
        assert(input_rem(&input).index(0) == 0x2Fu8);
        assert((f.len() as int)
            + 5 * (input_rem(&input).len() as int) + 32
            <= 0xFFFF_FFFF);
    }
    let rem2 = self.parse_path(scheme_type, psx, &mut hh2, input);
    proof {
        // the wrap-up face at the shared wrap-up call
        let f = self.serialization.view();
        let rm = input_rem(&rem2);
        assert forall|j: int| 0 <= j && j < 7
            implies f.index(j) == fa.index(j) by {
        }
        assert(machine_domain(f));
        assert(input_wf(&rem2));
        assert(rm.len() == 0
            || rm.index(0) == 0x3Fu8
            || rm.index(0) == 0x23u8);
        assert((f.len() as int) >= 7);
        Self::pf_file_scheme_face(f);
        assert(scheme_type_of(f.subrange(0, 4))
            == SchemeType::File);
        assert(scheme_type == SchemeType::File);
        assert((4 as int) + 3 <= (f.len() as int));
        assert(f.index((4 as int) + 1) == 0x2Fu8);
        assert(f.index((4 as int) + 2) == 0x2Fu8);
        assert((7 as int) >= (4 as int) + 3);
        assert((7 as int) <= (f.len() as int));
        assert((7 as int) == (4 as int) + 3);
        if (f.len() as int) == 7 {
            // the anchor-as-EOF corner: the record ends at the
            // serialization end
            assert((7 as int) == (f.len() as int));
        } else {
            assert(((f.len() as int) > (psx as int))
                ==> f.index(psx as int) == 0x2Fu8);
            assert(f.index(7) == 0x2Fu8);
            assert(f.index(7) != 0x3Au8);
            assert(f.index(7) != 0x40u8);
            assert((7 as int) != (f.len() as int));
        }
        // the budget chain for the wrap-up's scan
        assert((f.len() as int)
            <= 7 + 5 * (si.len() as int) + 6);
        assert((rm.len() as int) <= (si.len() as int));
        assert((f.len() as int)
            + 6 * (rm.len() as int) + 12
            <= 20 * (si.len() as int) + 136);
    }
    self.with_query_and_fragment(scheme_type, 4, 7, 7, 7,
        super::HostInternal::None, Option::None, 7, rem2)
}

/// Origin Rust (parser.rs:680-700, the no-slash branch of the file
/// state under the base-less cone): push "file:///"
/// (parser.rs:681) -- the base-copy arms of parser.rs:599-679 are dead
/// under the cone (base None), their face is the base-merge batch arc --
/// then parse_path over the full input ("file:///" carries the third
/// '/' as the path anchor, parser.rs:683-684) and the record assembly
/// of parser.rs:685-699 (username_end = host_start = host_end =
/// path_start = "file://".len(), port None, no host), which folds into
/// the shared wrap-up, value-equal.
pub exec fn pf_baseless_arm<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        scheme_type == SchemeType::File,
        machine_domain(old(self).serialization.view()),
        (old(self).serialization.view().len() as int) == 0,
        20 * (input_rem(&input).len() as int) + 136
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_ok() ==> super::url_invariant(&r.unwrap())),
        (r.is_err() ==> (r == Err(ParseError::Overflow))),
{
    let ghost si = input_rem(&input);
    // the "file:///" push (parser.rs:681)
    push_file_prefix(&mut self.serialization, true);
    let ghost fa = self.serialization.view();
    let mut hh2: bool = false;
    let psx: usize = 7;
    proof {
        let f = self.serialization.view();
        assert((f.len() as int) == 8);
        assert(f.index(psx as int) == 0x2Fu8);
        assert((f.len() as int)
            + 5 * (input_rem(&input).len() as int) + 32
            <= 0xFFFF_FFFF);
    }
    let rem2 = self.parse_path(scheme_type, psx, &mut hh2, input);
    proof {
        // the wrap-up face at the shared wrap-up call
        let f = self.serialization.view();
        let rm = input_rem(&rem2);
        assert forall|j: int| 0 <= j && j < 7
            implies f.index(j) == fa.index(j) by {
        }
        assert(machine_domain(f));
        assert(input_wf(&rem2));
        assert(rm.len() == 0
            || rm.index(0) == 0x3Fu8
            || rm.index(0) == 0x23u8);
        assert((f.len() as int) >= 7);
        Self::pf_file_scheme_face(f);
        assert(scheme_type_of(f.subrange(0, 4))
            == SchemeType::File);
        assert(scheme_type == SchemeType::File);
        assert((4 as int) + 3 <= (f.len() as int));
        assert(f.index((4 as int) + 1) == 0x2Fu8);
        assert(f.index((4 as int) + 2) == 0x2Fu8);
        assert((7 as int) >= (4 as int) + 3);
        assert((7 as int) <= (f.len() as int));
        assert((7 as int) == (4 as int) + 3);
        if (f.len() as int) == 7 {
            // the anchor-as-EOF corner: the record ends at the
            // serialization end
            assert((7 as int) == (f.len() as int));
        } else {
            assert(((f.len() as int) > (psx as int))
                ==> f.index(psx as int) == 0x2Fu8);
            assert(f.index(7) == 0x2Fu8);
            assert(f.index(7) != 0x3Au8);
            assert(f.index(7) != 0x40u8);
            assert((7 as int) != (f.len() as int));
        }
        // the budget chain for the wrap-up's scan
        assert((f.len() as int)
            <= 8 + 5 * (si.len() as int) + 6);
        assert((rm.len() as int) <= (si.len() as int));
        assert((f.len() as int)
            + 6 * (rm.len() as int) + 12
            <= 20 * (si.len() as int) + 136);
    }
    self.with_query_and_fragment(scheme_type, 4, 7, 7, 7,
        super::HostInternal::None, Option::None, 7, rem2)
}

/// Origin Rust (parser.rs:501-701): fn parse_file(mut self, input:
///   Input<'_>, scheme_type: SchemeType, base_file_url: Option<&Url>)
///   -> ParseResult<Url> -- the file state.  Transcribed under the
/// file-state cone: the base_file_url is None (the base arms of
/// parser.rs:599-679 are the base-merge batch arc; the File arm of
/// parse_with_scheme filters the None base under this tree's no-base
/// cone), the serialization is empty (the parser.rs:434 clear of the
/// File dispatch), and the input obeys the two File faces: the
/// leading '\' of a slash-led input sits outside the byte model of the
/// path machine's '/' normalization (the first-byte pin), and the
/// file-host entry class holds over the input past a "//" or "/\"
/// prefix (whose instantiation the scan selects, the drive-form
/// candidates never reaching the deep face).  The windows-drive
/// violation logs of parser.rs:512-516 are outside the value surface.
pub exec fn parse_file<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
    base_file_url: Option<&'i super::Url>,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        self.base_url.is_none(),
        base_file_url.is_none(),
        scheme_type == SchemeType::File,
        machine_domain(old(self).serialization.view()),
        (old(self).serialization.view().len() as int) == 0,
        ({
            let rem = input_rem(&input);
            &&& (((rem.len() as int) >= 1)
                    && (rem.index(0) == 0x2Fu8
                        || rem.index(0) == 0x5Cu8))
                ==> rem.index(0) == 0x2Fu8
            &&& (((rem.len() as int) >= 2)
                    && rem.index(0) == 0x2Fu8
                    && (rem.index(1) == 0x2Fu8
                        || rem.index(1) == 0x5Cu8))
                ==> file_host_entry_class(
                    rem.subrange(2, rem.len() as int))
            &&& 20 * (rem.len() as int) + 176
                <= 0xFFFF_FFFF
        }),
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_ok() ==> super::url_invariant(&r.unwrap())),
        (r.is_err() ==> (r == Err(ParseError::Overflow))),
{
    let ghost rem0 = input_rem(&input);
    let (c0o, after1) = input.split_first();
    match c0o {
        Option::Some(c0) => {
            if c0 == 0x2Fu8 || c0 == 0x5Cu8 {
                proof {
                    // the file-state cone pins the slash-led form to
                    // '/' (the leading '\' arms of parser.rs:511-514
                    // sit outside the byte model of the path
                    // machine's '/' normalization)
                    assert(rem0.index(0) == c0);
                    assert(c0 == 0x2Fu8);
                    assert(input_wf(&after1));
                }
                let (c1o, after2) = after1.split_first();
                proof {
                    let r1 = input_rem(&after1);
                    assert(r1 == rem0.subrange(1,
                        rem0.len() as int));
                    assert(input_wf(&after1));
                }
                match c1o {
                    Option::Some(c1) => {
                        if c1 == 0x2Fu8 || c1 == 0x5Cu8 {
                            // the file host state (parser.rs:517-545)
                            proof {
                                let r2 = input_rem(&after2);
                                assert(r2 == rem0.subrange(1,
                                    rem0.len() as int).subrange(
                                    1, (rem0.len() as int) - 1));
                                assert(r2 == rem0.subrange(2,
                                    rem0.len() as int)) by {
                                    vstd::seq::lemma_seq_subrange_composition(
                                        rem0, 1,
                                        rem0.len() as int, 1,
                                        rem0.len() as int - 1);
                                }
                                assert(file_host_entry_class(r2));
                                assert((r2.len() as int)
                                    <= (rem0.len() as int));
                                assert(20 * (r2.len() as int) + 176
                                    <= 0xFFFF_FFFF);
                                assert(input_wf(&after2));
                            }
                            self.pf_hosted_arm(after2, scheme_type)
                        } else {
                            // the "file://" arm (parser.rs:546-597):
                            // the parse-path input is the full input
                            proof {
                                assert(input_rem(&input).len()
                                    > 0);
                                assert(input_rem(&input).index(0)
                                    == 0x2Fu8);
                                assert(20
                                    * (rem0.len() as int) + 136
                                    <= 0xFFFF_FFFF);
                            }
                            self.pf_slash1_arm(input, scheme_type)
                        }
                    }
                    Option::None => {
                        // the "file://" arm at the one-byte input:
                        // parse_path over the full '/'-led input is
                        // the upstream parse-path input selection
                        // (parser.rs:565-574)
                        proof {
                            assert(input_rem(&input).len() > 0);
                            assert(input_rem(&input).index(0)
                                == 0x2Fu8);
                            assert(20 * (rem0.len() as int) + 136
                                <= 0xFFFF_FFFF);
                        }
                        self.pf_slash1_arm(input, scheme_type)
                    }
                }
            } else {
                // the no-slash arm (parser.rs:680-700)
                proof {
                    assert(20 * (rem0.len() as int) + 136
                        <= 0xFFFF_FFFF);
                }
                self.pf_baseless_arm(input, scheme_type)
            }
        }
        Option::None => {
            // the empty input (parser.rs:599's first_char None): under
            // the cone the base copy arms are dead, the no-slash arm
            // parses it
            proof {
                assert(20 * (rem0.len() as int) + 136
                    <= 0xFFFF_FFFF);
            }
            self.pf_baseless_arm(input, scheme_type)
        }
    }
    }
}

/* ============================================================
 * The query/fragment wrap-up of the parse (Origin:
 * with_query_and_fragment, parser.rs:1429-1482): the two
 * anarchist "/." faces first (parser.rs:1441-1462), then the
 * query/fragment scan, then the Url build.
 * ============================================================ */

/// Origin Rust (parser.rs:1442-1445): self.serialization.insert_str(
///   path_start_as_usize, "/.") of the case-1 anarchist fix -- the bytes
///   before path_start are kept, a "/." pair is inserted, and the old path
///   region is appended after it.
pub exec fn anar_insert_dot(ser: &mut Vec<u8>, at: usize)
    requires
        machine_domain(old(ser).view()),
        (at as int) + 2 <= old(ser).view().len(),
        old(ser).view().index(at as int) == 0x2Fu8,
        old(ser).view().index((at as int) + 1) == 0x2Fu8,
        (old(ser).view().len() as int) + 2 <= 0xFFFF_FFFF,
    ensures
        ({
            let o = old(ser).view();
            let f = final(ser).view();
            &&& machine_domain(f)
            &&& (f.len() as int) == (o.len() as int) + 2
            &&& f.index(at as int) == 0x2Fu8
            &&& f.index((at as int) + 1) == 0x2Eu8
            &&& (forall|j: int| 0 <= j < at as int
                ==> f.index(j) == o.index(j))
            &&& (forall|j: int| at as int <= j < o.len() as int
                ==> f.index(j + 2) == o.index(j))
        }),
{
    let n0 = ser.len();
    let suffix = super::bytes_slice(ser, at as u32, n0 as u32);
    proof {
        let o = ser.view();
        assert(suffix.view() == o.subrange(at as int, o.len() as int));
        assert(machine_domain(suffix.view()));
    }
    ser.truncate(at);
    proof {
        let o = old(ser).view();
        assert(ser.view() == o.subrange(0, at as int));
        assert(machine_domain(ser.view()));
    }
    let ghost pre1 = ser.view();
    ser.push(0x2Fu8);
    let ghost pre2 = ser.view();
    ser.push(0x2Eu8);
    proof {
        assert(pre2 == pre1.push(0x2Fu8));
        assert(ser.view() == pre2.push(0x2Eu8));
        assert(machine_domain_byte(0x2Eu8));
        machine_domain_add(pre1, seq![0x2Fu8]);
        machine_domain_add(pre2, seq![0x2Eu8]);
        assert(machine_domain(ser.view()));
        let o = old(ser).view();
        assert((suffix.view().len() as int)
            == (o.len() as int) - (at as int));
        assert(ser.view().index(at as int) == 0x2Fu8);
        assert(ser.view().index((at as int) + 1) == 0x2Eu8);
    }
    let ghost base2 = ser.view();
    vec_append_bytes(ser, &suffix);
    proof {
        let o = old(ser).view();
        let f = ser.view();
        assert(f == base2 + suffix.view());
        assert(f.len() == base2.len() + suffix.view().len());
        assert(f.len() == o.len() + 2);
        assert forall|j: int| 0 <= j < at as int
            implies f.index(j) == o.index(j) by {
            vstd::seq::lemma_seq_add_index1(base2, suffix.view(), j);
        }
        assert forall|j: int| at as int <= j < o.len() as int
            implies f.index(j + 2) == o.index(j) by {
            let t = suffix.view();
            vstd::seq::lemma_seq_subrange_index(o, at as int,
                o.len() as int, (j as int) - (at as int));
            vstd::seq::lemma_seq_add_index2(base2, t, (j as int) + 2);
        }
    }
}

/// Origin Rust (parser.rs:1455-1460): self.serialization.replace_range(
///   scheme_end..path_start, ":") of the case-2 anarchist fix -- the
/// ":/." prefix (scheme_end ':' plus the "/." pair) collapses to ":" and
/// the path head at the old path_start moves up to scheme_end + 1.
pub exec fn anar_remove_dot(ser: &mut Vec<u8>, scheme_end: u32)
    requires
        machine_domain(old(ser).view()),
        ((scheme_end as int) + 3) <= old(ser).view().len(),
        old(ser).view().index(scheme_end as int) == 0x3Au8,
        old(ser).view().index((scheme_end as int) + 1) == 0x2Fu8,
        old(ser).view().index((scheme_end as int) + 2) == 0x2Eu8,
        (old(ser).view().len() as int) <= 0xFFFF_FFFF,
    ensures
        ({
            let o = old(ser).view();
            let f = final(ser).view();
            &&& machine_domain(f)
            &&& (f.len() as int) == (o.len() as int) - 2
            &&& (forall|j: int| 0 <= j < (scheme_end as int) + 1
                ==> f.index(j) == o.index(j))
            &&& (forall|j: int| (scheme_end as int) + 1 <= j
                    && j < o.len() as int - 2
                ==> f.index(j) == o.index(j + 2))
        }),
{
    let n0 = ser.len();
    let suffix = super::bytes_slice(ser, scheme_end + 3, n0 as u32);
    proof {
        let o = ser.view();
        assert(suffix.view() == o.subrange(
            (scheme_end as int) + 3, o.len() as int));
        assert(machine_domain(suffix.view()));
    }
    ser.truncate((scheme_end + 1) as usize);
    proof {
        let o = old(ser).view();
        assert(ser.view() == o.subrange(0, (scheme_end as int) + 1));
        assert(machine_domain(ser.view()));
    }
    let ghost base2 = ser.view();
    vec_append_bytes(ser, &suffix);
    proof {
        let o = old(ser).view();
        let f = ser.view();
        assert(f == base2 + suffix.view());
        assert((suffix.view().len() as int)
            == (o.len() as int) - ((scheme_end as int) + 3));
        assert(f.len() == o.len() - 2);
        assert forall|j: int| 0 <= j < (scheme_end as int) + 1
            implies f.index(j) == o.index(j) by {
            vstd::seq::lemma_seq_add_index1(base2, suffix.view(), j);
        }
        assert forall|j: int| (scheme_end as int) + 1 <= j
            && j < o.len() as int - 2
            implies f.index(j) == o.index(j + 2) by {
            let t = suffix.view();
            vstd::seq::lemma_seq_subrange_index(o, (scheme_end as int) + 3,
                o.len() as int, (j as int) - (scheme_end as int) - 1);
            vstd::seq::lemma_seq_add_index2(base2, t, j);
        }
    }
}

/// The structural wrap-up of the authority face at with_query_and_fragment:
/// every clause of the url_invariant's authority branch is a cone fact on
/// the built record (the caller's face carries them from the parse phases);
/// the lemma-localized query keeps the wrap-up fn's own query light.
pub proof fn wqaf_face1_url_ok(u: &super::Url, scheme_type: SchemeType)
    requires
        (u.serialization.view().len() as int) <= 0xFFFF_FFFF,
        1 <= (u.scheme_end as int),
        (u.scheme_end as int) + 3 <= (u.serialization.view().len() as int),
        super::is_ascii_alpha(u.serialization.view().index(0)),
        (forall|j: int| 1 <= j && j < (u.scheme_end as int)
            ==> super::is_scheme_char(u.serialization.view().index(j))),
        u.serialization.view().index(u.scheme_end as int) == 0x3Au8,
        u.serialization.view().index((u.scheme_end as int) + 1)
            == 0x2Fu8,
        u.serialization.view().index((u.scheme_end as int) + 2)
            == 0x2Fu8,
        scheme_type == scheme_type_of(u.serialization.view()
            .subrange(0, u.scheme_end as int)),
        (u.scheme_end as int) + 3 <= (u.username_end as int),
        (u.username_end as int) <= (u.serialization.view().len() as int),
        ((u.username_end as int) == (u.serialization.view().len() as int))
            || (u.serialization.view().index(u.username_end as int)
                    == 0x3Au8
                && (u.host_start as int) >= (u.username_end as int) + 2
                && u.serialization.view()
                    .index(u.host_start as int - 1) == 0x40u8)
            || (u.serialization.view().index(u.username_end as int)
                    == 0x40u8
                && (u.host_start as int)
                    == (u.username_end as int) + 1)
            || ((u.username_end as int) == (u.scheme_end as int) + 3
                && u.serialization.view().index(u.username_end as int)
                    != 0x3Au8
                && u.serialization.view().index(u.username_end as int)
                    != 0x40u8),
        (u.host_start as int) >= (u.username_end as int),
        (u.host_start as int) <= (u.serialization.view().len() as int),
        (u.host_end as int) >= (u.host_start as int),
        (u.host_end as int) <= (u.serialization.view().len() as int),
        (u.path_start as int) >= (u.host_end as int),
        (u.path_start as int) <= (u.serialization.view().len() as int),
        (u.host == super::HostInternal::None)
            == ((u.host_start as int) == (u.host_end as int)),
        ((u.path_start as int) == (u.host_end as int)) ==> u.port.is_none(),
        ((u.path_start as int) > (u.host_end as int)) ==> (
            u.serialization.view().index(u.host_end as int) == 0x3Au8
            && (u.host_end as int) + 2 <= (u.path_start as int)
            && (forall|j: int| (u.host_end as int) + 1 <= j
                    && j < (u.path_start as int)
                ==> super::is_dec_digit(
                    u.serialization.view().index(j)))
            && u.port.is_some()
            && (u.port.unwrap() as int)
                == super::dec_val(u.serialization.view().subrange(
                    (u.host_end as int) + 1, (u.path_start as int)))
        ),
        ((u.path_start as int) < (u.serialization.view().len() as int)) ==> (
            u.serialization.view().index(u.path_start as int) == 0x2Fu8
            || u.serialization.view().index(u.path_start as int) == 0x23u8
            || u.serialization.view().index(u.path_start as int) == 0x3Fu8
        ),
        (u.query_start.is_some()) ==> (
            (u.query_start.unwrap() as int) >= (u.path_start as int)
            && (u.query_start.unwrap() as int)
                < (u.serialization.view().len() as int)
            && u.serialization.view().index(
                (u.query_start.unwrap() as int)) == 0x3Fu8
        ),
        (u.fragment_start.is_some()) ==> (
            (u.fragment_start.unwrap() as int) >= (u.path_start as int)
            && (u.fragment_start.unwrap() as int)
                < (u.serialization.view().len() as int)
            && u.serialization.view().index(
                (u.fragment_start.unwrap() as int)) == 0x23u8
        ),
        (u.query_start.is_some() && u.fragment_start.is_some())
            ==> ((u.fragment_start.unwrap() as int)
                > (u.query_start.unwrap() as int)),
    ensures
        super::url_invariant(u),
{
    let s = u.serialization.view();
    let n = s.len() as int;
    let se = u.scheme_end as int;
    assert(super::has_authority_view(u));
    assert(se + 1 <= n);
    // the userinfo match byte (the three-way face disjunction covers all
    // match arms in order here)
    if (u.username_end as int) != n {
        let b = s.index(u.username_end as int);
        if b == 0x3Au8 {
            assert((u.host_start as int)
                >= (u.username_end as int) + 2);
            assert(s.index(u.host_start as int - 1) == 0x40u8);
        } else if b == 0x40u8 {
            assert((u.host_start as int) == (u.username_end as int) + 1);
        } else {
            assert((u.username_end as int) == se + 3);
        }
    }
    // host tag consistency feeds the special-scheme nonempty clause
    if u.host == super::HostInternal::Domain {
        assert((u.host_start as int) != (u.host_end as int));
        assert((u.host_start as int) < (u.host_end as int));
        assert(is_special(scheme_type) ==> is_special(
            scheme_type_of(s.subrange(0, se))));
        assert(is_special(scheme_type)
            ==> (u.host_start as int) < (u.host_end as int));
    }
    assert(super::url_invariant(u));
}

/// The structural wrap-up of the anarchist face at
/// with_query_and_fragment: the default username/host/port components and
/// the byte bases of the two "/." arm outcomes (the inserted "/." prefix
/// with the opaque "//" path behind it, or the untouched single-offset
/// path with no authority bytes).
pub proof fn wqaf_face2_url_ok(u: &super::Url, opaque: bool)
    requires
        (u.serialization.view().len() as int) <= 0xFFFF_FFFF,
        1 <= (u.scheme_end as int),
        (u.scheme_end as int) + 1 <= (u.serialization.view().len() as int),
        super::is_ascii_alpha(u.serialization.view().index(0)),
        (forall|j: int| 1 <= j && j < (u.scheme_end as int)
            ==> super::is_scheme_char(u.serialization.view().index(j))),
        u.serialization.view().index(u.scheme_end as int) == 0x3Au8,
        (u.username_end as int) == (u.scheme_end as int) + 1,
        (u.host_start as int) == (u.scheme_end as int) + 1,
        (u.host_end as int) == (u.scheme_end as int) + 1,
        u.host == super::HostInternal::None,
        u.port.is_none(),
        (u.query_start.is_some()) ==> (
            (u.query_start.unwrap() as int) >= (u.path_start as int)
            && (u.query_start.unwrap() as int)
                < (u.serialization.view().len() as int)
            && u.serialization.view().index(
                (u.query_start.unwrap() as int)) == 0x3Fu8
        ),
        (u.fragment_start.is_some()) ==> (
            (u.fragment_start.unwrap() as int) >= (u.path_start as int)
            && (u.fragment_start.unwrap() as int)
                < (u.serialization.view().len() as int)
            && u.serialization.view().index(
                (u.fragment_start.unwrap() as int)) == 0x23u8
        ),
        (u.query_start.is_some() && u.fragment_start.is_some())
            ==> ((u.fragment_start.unwrap() as int)
                > (u.query_start.unwrap() as int)),
        (opaque) ==> (
            (u.path_start as int) == (u.scheme_end as int) + 3
            && u.serialization.view().index((u.scheme_end as int) + 1)
                == 0x2Fu8
            && u.serialization.view().index((u.scheme_end as int) + 2)
                == 0x2Eu8
            && u.serialization.view().index(u.path_start as int)
                == 0x2Fu8
            && u.serialization.view().index((u.path_start as int) + 1)
                == 0x2Fu8
            && (u.path_start as int) + 2 <= super::path_end_view(u)
        ),
        (!opaque) ==> (
            (u.path_start as int) == (u.scheme_end as int) + 1
            && !super::has_authority_view(u)
        ),
    ensures
        super::url_invariant(u),
{
    if opaque {
        assert(!super::has_authority_view(u)) by {
            assert(u.serialization.view()
                .index((u.scheme_end as int) + 2) == 0x2Eu8);
        }
    }
}

/// The own-bytes copy of a byte vector (the Url build extracts the
/// serialized payload; the upstream moves `self` at with_query_and_fragment
/// while the mirror's &mut ledger needs the explicit copy face).
pub exec fn bytes_own(v: &Vec<u8>) -> (r: Vec<u8>)
    requires
        (v.view().len() as int) <= 0xFFFF_FFFF,
    ensures
        r.view() == v.view(),
{
    let ghost vv = v.view();
    let n = v.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            vv == v.view(),
            (n as int) == (v.view().len() as int),
            (out.view().len() as int) == (i as int),
            forall|j: int| 0 <= j < (i as int)
                ==> out.view().index(j) == vv.index(j),
        decreases n - i,
    {
        proof {
            assert((i as int) < (v.view().len() as int));
        }
        let x = v[i];
        let ghost preo = out.view();
        out.push(x);
        proof {
            assert(out.view() == preo.push(x));
            assert(out.view().index(i as int) == x);
        }
        i += 1;
    }
    proof {
        assert(out.view().len() == vv.len());
        assert(out.view() == vv);
    }
    out
}
/* ============================================================
 * The connective lemmas of the after-double-slash assembly (the
 * wqaf-cone facts over the write shapes of the host-port and
 * userinfo phases).
 * ============================================================ */

/// The port-region face of the authority record: the ':' + decimal
/// write of hap_host_port_tail is exactly the query/fragment-face
/// digits region with dec_val equal to the port value (the FACE-1 port
/// cone of with_query_and_fragment).
/// The port-region face of the authority record: the ':' + decimal
/// write of hap_host_port_tail is exactly the record's digits region
/// with dec_val equal to the port value (the FACE-1 port cone of
/// with_query_and_fragment).
pub proof fn host_port_region_face(
    ser: Seq<u8>,
    pre: Seq<u8>,
    pv: int,
)
    requires
        machine_domain(ser),
        machine_domain(pre),
        0 <= pv <= 65535,
        ser == pre + seq![0x3Au8] + dec_ascii_u32(pv),
    ensures
        ({
            let he = pre.len();
            &&& ser.index(he as int) == 0x3Au8
            &&& he + 2 <= ser.len()
            &&& (forall|j: int| (he as int) + 1 <= j && j < ser.len()
                ==> super::is_dec_digit(ser.index(j)))
            &&& pv == super::dec_val(ser.subrange((he as int) + 1,
                ser.len() as int))
        }),
{
    dec_ascii_digits(pv);
    let he = pre.len();
    let d = dec_ascii_u32(pv);
    assert(ser.len() as int == (he as int) + 1 + d.len());
    assert(d.len() >= 1);
    assert((he as int) + 2 <= ser.len() as int);
    assert(ser.index(he as int) == 0x3Au8) by {
        let x = seq![0x3Au8] + d;
        vstd::seq::lemma_seq_add_index2(pre, x, he as int);
        vstd::seq::lemma_seq_add_index1(seq![0x3Au8], d, 0);
    }
    assert(ser.subrange((he as int) + 1, ser.len() as int) == d) by {
        assert forall|j: int| 0 <= j && j < d.len()
            implies ser.index((he as int) + 1 + j) == d.index(j) by {
            let x = seq![0x3Au8] + d;
            vstd::seq::lemma_seq_add_index2(pre, x, (he as int) + 1 + j);
            vstd::seq::lemma_seq_add_index2(seq![0x3Au8], d, j as int + 1);
        }
    }
    assert(pv == super::dec_val(ser.subrange((he as int) + 1,
        ser.len() as int)));
    assert forall|j: int| he + 1 <= j && j < ser.len()
        implies super::is_dec_digit(ser.index(j)) by {
        let t = ser.subrange((he as int) + 1, ser.len() as int);
        vstd::seq::lemma_seq_subrange_index(ser, (he as int) + 1,
            ser.len() as int, j - (he as int) - 1);
    }
}

/* ============================================================
 * The file-host scan (Origin: parser.rs:1062-1092, pub fn
 * file_host).  On the transcription domain the tab/newline
 * ignore-tracking of upstream (has_ignored_chars, parser.rs:1072)
 * never fires and the char counter collapses to the byte length;
 * the Cow::Borrowed candidate is the owned region copy.
 * ============================================================ */

/// The owned copy of a byte region (the Cow::Borrowed(&input_str[..bytes])
/// shape of the scan's candidate).
pub exec fn bytes_region_own(s: &[u8], a: usize, b: usize)
    -> (r: Vec<u8>)
    requires
        0 <= a,
        (a as int) <= (b as int),
        (b as int) <= (s.view().len() as int),
    ensures
        r.view() == s.view().subrange(a as int, b as int),
{
    let ghost sv = s.view();
    let n = s.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = a;
    while i < b
        invariant
            0 <= a,
            (a as int) <= (i as int),
            (i as int) <= (b as int),
            (b as int) <= (n as int),
            (n as int) == (s.view().len() as int),
            sv == s.view(),
            (out.view().len() as int) == ((i as int) - (a as int)),
            forall|j: int| 0 <= j && j < ((i as int) - (a as int))
                ==> out.view().index(j)
                    == sv.index((a as int) + j),
        decreases b - i,
    {
        proof {
            assert((i as int) < (s.view().len() as int));
        }
        let c = s[i];
        let ghost before_push = out.view();
        out.push(c);
        proof {
            assert(out.view() == before_push.push(c));
            assert(before_push.push(c)
                == before_push + seq![c]);
            assert((out.view().len() as int)
                == (before_push.len() as int) + 1);
            assert forall|j: int|
                0 <= j && j < (out.view().len() as int)
                implies out.view().index(j)
                    == sv.index((a as int) + j) by {
                if j < (before_push.len() as int) {
                    vstd::seq::lemma_seq_add_index1(before_push,
                        seq![c], j);
                } else {
                    vstd::seq::lemma_seq_add_index2(before_push,
                        seq![c], j);
                    assert(sv.index(i as int) == c);
                }
            }
        }
        i += 1;
    }
    proof {
        let rseq = out.view();
        let tseq = sv.subrange(a as int, b as int);
        assert((rseq.len() as int) == (b as int) - (a as int));
        assert((tseq.len() as int) == (b as int) - (a as int));
        assert forall|j: int| 0 <= j && j < (tseq.len() as int)
            implies rseq.index(j) == tseq.index(j) by {
            vstd::seq::lemma_seq_subrange_index(sv, a as int,
                b as int, j);
        }
        vstd::seq::lemma_seq_ext_equal(rseq, tseq);
    }
    out
}

/// Origin Rust (parser.rs:1062-1092): pub fn file_host(input: Input<'_>)
///   -> ParseResult<(bool, Cow<'_, str>, Input<'_>)> -- the file-host
/// scan: walk to the first file wall byte ('/' | '\\' | '?' | '#'),
/// the candidate is the wall-free prefix remaining at the wall; a
/// candidate that is exactly a windows drive letter is not a host --
/// the empty candidate returns with the full input (parser.rs:1088-1090).
/// The Result layer of upstream never fails here (both arms are Ok,
/// parser.rs:1089 and 1091).
pub exec fn file_host<'i>(
    input: &Input<'i>,
) -> (r: Result<(bool, Vec<u8>, Input<'i>), ParseError>)
    requires
        input_wf(input),
    ensures
        ({
            let s = input_rem(input);
            &&& r.is_ok()
            &&& (r.is_ok() ==> ({
                let (is_sb, hstr, rem) = r.unwrap();
                let w = hstr.view().len() as int;
                &&& input_wf(&rem)
                &&& machine_domain(hstr.view())
                &&& hstr.view() == s.subrange(0, w)
                &&& (is_sb ==> (
                       file_wall_free(s, w)
                    && (w == (s.len() as int)
                        || file_wall_byte(s.index(w)))
                    && input_rem(&rem)
                        == s.subrange(w, s.len() as int)
                    && (input_rem(&rem).len() as int)
                        == (s.len() as int) - w))
                &&& (!is_sb ==> (
                       w == 0
                    && (s.len() as int) >= 2
                    && is_win_drive(s.subrange(0, 2))
                    && input_rem(&rem) == s))
            }))
        }),
{
    let sbuf = input.bytes;
    let ghost s0 = input_rem(input);
    let n = sbuf.len();
    let mut cur: usize = input.pos;
    while cur < n
        && sbuf[cur] != 0x2Fu8
        && sbuf[cur] != 0x5Cu8
        && sbuf[cur] != 0x3Fu8
        && sbuf[cur] != 0x23u8
        invariant
            input_wf(input),
            (input.pos as int) <= (cur as int),
            (cur as int) <= (n as int),
            (n as int) == (sbuf.view().len() as int),
            s0 == input_rem(input),
            forall|j: int|
                (input.pos as int) <= j && j < (cur as int)
                ==> !file_wall_byte(sbuf.view().index(j)),
        decreases (n as int) - (cur as int),
    {
        proof {
            assert(!file_wall_byte(sbuf.view().index(cur as int)));
        }
        cur += 1;
    }
    let w = cur - input.pos;
    if w == 2 && is_win_drive_at(sbuf, input.pos) {
        proof {
            // the drive digest: the empty candidate and the full,
            // unadvanced remaining input
            assert(Seq::<u8>::empty().len() == 0);
            assert(s0.subrange(0, 0) == Seq::empty());
            machine_domain_subrange(s0, 0, 0);
            let sub = sbuf.view().subrange(
                input.pos as int, input.pos as int + 2);
            assert(sub == s0.subrange(0, 2)) by {
                assert(sub.len() == 2);
                assert forall|j: int| 0 <= j && j < 2
                    implies sub.index(j) == s0.index(j) by {
                    vstd::seq::lemma_seq_subrange_index(sbuf.view(),
                        input.pos as int, input.pos as int + 2, j);
                    vstd::seq::lemma_seq_subrange_index(sbuf.view(),
                        input.pos as int, n as int, j);
                }
                vstd::seq::lemma_seq_ext_equal(sub, s0.subrange(0, 2));
            }
            assert(is_win_drive(s0.subrange(0, 2)));
            assert((s0.len() as int) >= 2);
            machine_domain_subrange(s0, 0, 0);
        }
        let rem2 = *input;
        let em: Vec<u8> = Vec::new();
        proof {
            assert(em.view() == Seq::empty());
        }
        Ok((false, em, rem2))
    } else {
        let hstr = bytes_region_own(sbuf, input.pos, cur);
        let rem2 = Input { bytes: sbuf, pos: cur };
        proof {
            // the candidate is the wall-free prefix, the remaining
            // input is its tail at the wall (or EOF)
            rem_shift(sbuf, input.pos as int, w as int);
            assert(input_rem(&rem2)
                == s0.subrange(w as int, s0.len() as int));
            file_wall_free_iff(s0, w as int);
            assert(file_wall_free(s0, w as int));
            if (w as int) < (s0.len() as int) {
                let bt = sbuf.view().index(cur as int);
                assert(s0.index(w as int) == bt);
                assert(file_wall_byte(s0.index(w as int)));
            }
            machine_domain_subrange(s0, 0, w as int);
            assert(machine_domain(hstr.view()));
            assert(hstr.view() == s0.subrange(0, w as int));
            // input_wf of the advanced cursor
            assert(rem2.pos <= sbuf.len());
            assert(machine_domain(input_rem(&rem2)));
            assert((input_rem(&rem2).len() as int)
                <= 0xFFFF_FFFF);
            assert((sbuf.view().len() as int) <= 0xFFFF_FFFF);
        }
        Ok((true, hstr, rem2))
    }
}

/// The "file://"(+"file:///") prefix write of the file state
/// (parser.rs:518/547/681: serialization.push_str("file://") and its
/// three-slash sibling).  Publishes the scheme grammar pins at the
/// write base (the "file" scheme bytes, the ':' delimiter, the two
/// authority slashes; the third '/' of the no-host arms).
pub exec fn push_file_prefix(ser: &mut Vec<u8>, triple: bool)
    requires
        machine_domain(old(ser).view()),
        (old(ser).view().len() as int) + 8 <= 0xFFFF_FFFF,
    ensures
        ({
            let o = old(ser).view();
            let f = final(ser).view();
            let base = o.len() as int;
            &&& machine_domain(f)
            &&& (forall|j: int| 0 <= j && j < base
                ==> f.index(j) == o.index(j))
            &&& f.index(base) == 0x66u8
            &&& f.index(base + 1) == 0x69u8
            &&& f.index(base + 2) == 0x6cu8
            &&& f.index(base + 3) == 0x65u8
            &&& f.index(base + 4) == 0x3Au8
            &&& f.index(base + 5) == 0x2Fu8
            &&& f.index(base + 6) == 0x2Fu8
            &&& (triple ==> ({
                    &&& (f.len() as int) == base + 8
                    &&& f.index(base + 7) == 0x2Fu8}))
            &&& (!triple ==> ((f.len() as int) == base + 7))
        }),
{
    let lit: Vec<u8> = vec![0x66u8, 0x69, 0x6c, 0x65, 0x3a, 0x2f, 0x2f];
    let ghost lv = lit.view();
    proof {
        assert(lv.len() == 7);
        assert(lv.index(0) == 0x66u8);
        assert(lv.index(1) == 0x69u8);
        assert(lv.index(2) == 0x6cu8);
        assert(lv.index(3) == 0x65u8);
        assert(lv.index(4) == 0x3au8);
        assert(lv.index(5) == 0x2fu8);
        assert(lv.index(6) == 0x2fu8);
        assert(machine_domain(lv)) by {
            assert forall|j: int| 0 <= j && j < 7
                implies machine_domain_byte(lv.index(j)) by {
                if j == 0 {
                    assert(lv.index(j) < 0x80u8);
                } else if j == 1 {
                    assert(lv.index(j) < 0x80u8);
                } else if j == 2 {
                    assert(lv.index(j) < 0x80u8);
                } else if j == 3 {
                    assert(lv.index(j) < 0x80u8);
                } else if j == 4 {
                    assert(lv.index(j) < 0x80u8);
                } else if j == 5 {
                    assert(lv.index(j) < 0x80u8);
                } else {
                    assert(lv.index(j) < 0x80u8);
                }
            }
        }
    }
    let ghost o0 = ser.view();
    vec_append_bytes(ser, &lit);
    let ghost after_lit = ser.view();
    if triple {
        proof {
            assert(machine_domain_byte(0x2Fu8));
        }
        ser.push(0x2Fu8);
        proof {
            assert(ser.view() == after_lit.push(0x2Fu8));
            assert(after_lit.push(0x2Fu8)
                == after_lit + seq![0x2Fu8]);
            machine_domain_add(after_lit, seq![0x2Fu8]);
        }
    }
    proof {
        let f = ser.view();
        let base = o0.len() as int;
        vstd::seq::lemma_seq_add_len(o0, lv);
        machine_domain_add(o0, lv);
        assert(f == o0 + lv || (triple
            && f == o0 + lv + seq![0x2Fu8]));
        assert(machine_domain(f));
        // the length at the write base
        if triple {
            vstd::seq::lemma_seq_add_len(o0 + lv, seq![0x2Fu8]);
            assert((f.len() as int) == base + 8);
        } else {
            assert((f.len() as int) == base + 7);
        }
        // the prefix below the write base survives
        assert forall|j: int| 0 <= j && j < base
            implies f.index(j) == o0.index(j) by {
            if triple {
                vstd::seq::lemma_seq_add_index1(o0 + lv,
                    seq![0x2Fu8], j);
            }
            vstd::seq::lemma_seq_add_index1(o0, lv, j);
        }
        // the base-relative content pins
        assert forall|t: int| 0 <= t && t < 7
            implies f.index(base + t) == lv.index(t) by {
            assert((lv.len() as int) == 7);
            vstd::seq::lemma_seq_add_len(o0, lv);
            assert((((o0 + lv).len() as int)
                == (o0.len() as int) + 7)
                && (o0.len() as int) == base);
            if triple {
                assert(f == (o0 + lv) + seq![0x2Fu8]);
                vstd::seq::lemma_seq_add_index1(o0 + lv,
                    seq![0x2Fu8], base + t);
            } else {
                assert(f == o0 + lv);
            }
            vstd::seq::lemma_seq_add_index2(o0, lv, base + t);
        }
        assert(f.index(base) == 0x66u8);
        assert(f.index(base + 4) == 0x3Au8);
        assert(f.index(base + 5) == 0x2Fu8);
        assert(f.index(base + 6) == 0x2Fu8);
        assert(super::is_ascii_alpha(f.index(base)));
        assert forall|j: int| base + 1 <= j && j < base + 4
            implies super::is_scheme_char(f.index(j)) by {
            if j == base + 1 {
                assert(f.index(j) == 0x69u8);
            } else if j == base + 2 {
                assert(f.index(j) == 0x6cu8);
            } else {
                assert(f.index(j) == 0x65u8);
            }
        }
        if triple {
            assert(f.index(base + 7) == 0x2Fu8) by {
                vstd::seq::lemma_seq_add_index2(o0 + lv,
                    seq![0x2Fu8], base + 7);
            }
        }
    }
}



/* ============================================================
 * The base-merge arms of the no-scheme state (Origin: parse_relative
 * and fragment_only, parser.rs:703-823 and 1605-1626): the base-input
 * cone of the relative resolution. The coning direction is the base's
 * own invariant -- every component pin the built record inherits sits
 * at or below the copy boundary, and the writes below only append
 * after it; no host scan ever runs on the base bytes (the host field
 * rides the record copy, the deep stub stays unconsumed here).
 * ============================================================ */

/// The before-fragment boundary of a base URL (the copy length of
/// `..fragment_start`, parser.rs:1607-1610): the whole serialization
/// when the base carries no fragment.
pub open spec fn base_before_len(b: &super::Url) -> int {
    if b.fragment_start.is_some() {
        b.fragment_start.unwrap() as int
    } else {
        (b.serialization.view().len() as int)
    }
}

/// The base-input cone of the base-merge arms: the base's structural
/// invariant over the machine byte domain, plus the userinfo-terminus
/// conjunct. The username_end match of url_invariant is vacuous
/// exactly when username_end sits at the serialization end of an
/// authority URL, yet the append arms below write the '#' slot right
/// at that boundary, where the wildcard match arm demands
/// scheme_end+3. Every parse-built base satisfies the conjunct (the
/// userinfo writer ends at the serialization end only when nothing
/// was written, i.e. at the very "//" of the scheme), so the
/// conjunct documents the input dogma of the record carries below
/// rather than excluding any base the parser can produce.
pub open spec fn base_url_face(b: &super::Url) -> bool {
    let n = b.serialization.view().len() as int;
    let se = b.scheme_end as int;
    &&& super::url_invariant(b)
    &&& machine_domain(b.serialization.view())
    &&& (!super::has_authority_view(b)
        || (b.username_end as int) != n
        || (b.username_end as int) == se + 3)
}

/// The '/'-head entry dogma of the slash arm of parse_relative (the
/// '/' | '\\' first byte, parser.rs:741-783): a "//"-prefix input
/// hands its suffix after the two bytes to the double-slash state (the
/// take-while clone and the split_prefix probe of parser.rs:756-769
/// route there whenever the first two bytes are both '/'), and any
/// '/'-or-'\\' run of length >= 2 hands its post-run suffix there
/// (the count route, parser.rs:758-769). Both routes must leave the
/// authority-entry class in effect; the run of length 1 takes the
/// single-slash branch (the fresh-path face below, no class needed).
pub open spec fn rel_slash_face(
    s: Seq<u8>,
    scheme_type: SchemeType,
) -> bool {
    &&& s.len() > 0
    &&& (s.index(0) == 0x2Fu8 || s.index(0) == 0x5Cu8)
    &&& ((s.len() >= 2 && s.index(0) == 0x2Fu8
            && s.index(1) == 0x2Fu8)
        ==> authority_entry_class(
            s.subrange(2, s.len() as int),
            is_special(scheme_type)))
    &&& (forall|c: int| 2 <= c && c <= s.len()
            && (forall|j: int| 0 <= j && j < c
                ==> (s.index(j) == 0x2Fu8
                    || s.index(j) == 0x5Cu8))
            && (c == s.len()
                || (s.index(c) != 0x2Fu8
                    && s.index(c) != 0x5Cu8))
        ==> authority_entry_class(
            s.subrange(c, s.len() as int),
            is_special(scheme_type)))
}

/// The default-head entry dogma of the pop/merge arm of
/// parse_relative (parser.rs:784-823): the head is a plain byte
/// (not one of the copy- or slash-arm heads), and the base's path
/// component is query/fragment-free (the parsed-shape dogma -- a
/// hand-built record could legally carry '?' inside the path region,
/// but the pop below and the query wrap-up read the region as path
/// bytes). Opaque-pinned anarchist bases stay OUTSIDE this cone:
/// their case-2 non-fire records keep the interior of a copied
/// "//"-headed path region, whose survival through the parse_path
/// crops is not carried by the current ensures -- the '/'-arm
/// handles their case-2 revival (always firing there), the pop/merge
/// face of such bases is upstream behavior outside this cone.
pub open spec fn rel_merge_face(b: &super::Url, s: Seq<u8>) -> bool {
    &&& s.len() > 0
    &&& (s.index(0) != 0x3Fu8
        && s.index(0) != 0x23u8
        && s.index(0) != 0x2Fu8
        && s.index(0) != 0x5Cu8)
    &&& (super::has_authority_view(b)
        || !super::opaque_path_double_slash(b))
    &&& (forall|j: int| (b.path_start as int) <= j
            && j < super::path_end_view(b)
        ==> (b.serialization.view().index(j) != 0x3Fu8
            && b.serialization.view().index(j) != 0x23u8))
}

impl Parser<'_> {

/// Origin Rust (parser.rs:1605-1626): fn fragment_only(mut self,
///   base_url: &Url, mut input: Input<'_>) -> ParseResult<Url> --
/// the '#' state of the no-scheme resolution: copy the base up to its
/// fragment boundary, place the '#', percent-encode the rest with the
/// FRAGMENT set. The upstream `input.next()` consumption
/// (parser.rs:1619-1620, the debug assert on Some('#')) is the cursor
/// stride of the Input model; the reserve (parser.rs:1614) and the
/// violation-logging arms of the fragment iterator are outside the
/// value surface. The debug assert on the empty serialization
/// (parser.rs:1613) rides the requires; the to_u32 of the fragment
/// boundary (parser.rs:1623) stays inside the u32 offset domain under
/// the length budget, so the record always succeeds -- the upstream
/// ParseResult is kept for the caller shape.
pub exec fn fragment_only<'i>(
    &mut self,
    base_url: &super::Url,
    input: Input<'i>,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        (input_rem(&input).len() as int) > 0,
        input_rem(&input).index(0) == 0x23u8,
        old(self).serialization.view().len() == 0,
        base_url_face(base_url),
        (base_url.serialization.view().len() as int)
            + 3 * (input_rem(&input).len() as int) + 8
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        r.is_ok(),
        ({
            let u = r.unwrap();
            &&& super::url_invariant(&u)
            &&& u.serialization.view()
                == base_url.serialization.view().subrange(
                    0, base_before_len(base_url))
                    + seq![0x23u8]
                    + enc_seq(
                        input_rem(&input).subrange(
                            1, input_rem(&input).len() as int),
                        EncodeSet::Fragment)
            &&& (u.fragment_start.unwrap() as int)
                == base_before_len(base_url)
            &&& (u.scheme_end as int)
                == (base_url.scheme_end as int)
            &&& (u.username_end as int)
                == (base_url.username_end as int)
            &&& (u.host_start as int) == (base_url.host_start as int)
            &&& (u.host_end as int) == (base_url.host_end as int)
            &&& u.host == base_url.host
            &&& u.port == base_url.port
            &&& (u.path_start as int) == (base_url.path_start as int)
            &&& u.query_start == base_url.query_start
        }),
{
    let ghost rem0 = input_rem(&input);
    let ghost bs = base_url.serialization.view();
    let ghost k0 = base_before_len(base_url);
    // the before-fragment boundary (parser.rs:1607-1610)
    let k0u: u32 = match base_url.fragment_start {
        Option::Some(fs) => {
            proof {
                assert((fs as int) < (bs.len() as int));
                assert((fs as int) == k0);
            }
            fs
        }
        Option::None => super::url_len32(&base_url.serialization),
    };
    proof {
        assert((k0u as int) == k0);
        assert(k0 <= (bs.len() as int));
    }
    // the trunk copy (parser.rs:1615)
    let before = super::bytes_slice(&base_url.serialization, 0, k0u);
    proof {
        assert(before.view() == bs.subrange(0, k0));
        machine_domain_subrange(bs, 0, k0);
    }
    vec_append_bytes(&mut self.serialization, &before);
    let ghost pre1 = self.serialization.view();
    proof {
        assert(pre1 == before.view());
        assert(machine_domain(pre1));
    }
    // the '#' placement (parser.rs:1616)
    self.serialization.push(0x23u8);
    let ghost pre2 = self.serialization.view();
    proof {
        assert(pre2 == pre1.push(0x23u8));
        assert(pre2 == pre1 + seq![0x23u8]);
        assert((pre2.len() as int) == k0 + 1);
        assert(machine_domain(pre2));
    }
    // the cursor stride past '#' (parser.rs:1619-1621): parse_fragment
    // receives the input after the '#'
    let after = Input { bytes: input.bytes, pos: input.pos + 1 };
    proof {
        // the '#' slot guarantees the stride stays inside the input
        assert((input.pos as int) + 1 <= (rem0.len() as int)
            + (input.pos as int));
        rem_shift(input.bytes, input.pos as int, 1);
        machine_domain_subrange(rem0, 1, rem0.len() as int);
        assert(input_rem(&after)
            == rem0.subrange(1, rem0.len() as int));
        assert(input_wf(&after));
        let alen = (rem0.len() as int) - 1;
        assert((pre2.len() as int) + 3 * alen <= 0xFFFF_FFFF);
    }
    self.parse_fragment(after);
    let ghost fin = self.serialization.view();
    proof {
        let enc = enc_seq(input_rem(&after), EncodeSet::Fragment);
        assert(fin == pre2 + enc);
        enc_seq_machine(input_rem(&after), EncodeSet::Fragment);
        machine_domain_add(pre2, enc);
        assert(machine_domain(fin));
        // the length stays inside the u32 offset domain
        vstd::seq::lemma_seq_add_len(pre2, enc);
        assert((fin.len() as int) == (k0 + 1) + (enc.len() as int));
        enc_seq_len_bound(input_rem(&after), EncodeSet::Fragment);
        assert((fin.len() as int) <= 0xFFFF_FFFF);
        // the prefix carry facts of the record digest
        assert forall|j: int| 0 <= j && j < k0
            implies fin.index(j) == bs.index(j) by {
            vstd::seq::lemma_seq_add_index1(pre2, enc, j);
            vstd::seq::lemma_seq_add_index1(pre1, seq![0x23u8], j);
            vstd::seq::lemma_seq_subrange_index(bs, 0, k0, j);
        }
        // the '#' slot at the boundary
        assert(fin.index(k0) == 0x23u8) by {
            vstd::seq::lemma_seq_add_index1(pre2, enc, k0);
            vstd::seq::lemma_seq_add_index2(pre1, seq![0x23u8], k0);
        }
    }
    // the record build: the byte copy, the base components, the slot
    let u = super::Url {
        serialization: bytes_own(&self.serialization),
        scheme_end: base_url.scheme_end,
        username_end: base_url.username_end,
        host_start: base_url.host_start,
        host_end: base_url.host_end,
        host: base_url.host,
        port: base_url.port,
        path_start: base_url.path_start,
        query_start: base_url.query_start,
        fragment_start: Option::Some(k0u),
    };
    proof {
        fragment_prolong_carry(base_url, &u, k0);
    }
    Ok(u)
}

}

/// The authority-branch digest of the record carry: the base holds an
/// authority, the record keeps it (the "//" domain is strictly below
/// the boundary), and every component index the branch reads rides
/// the preserved prefix -- the single touched slot is username_end ==
/// k, where the base byte is '#' (or the terminus conjunct at k == n)
/// and the wildcard arm of both matches settles on scheme_end+3.
pub proof fn frag_carry_authority(
    b: &super::Url,
    u: &super::Url,
    k: int,
)
    requires
        base_url_face(b),
        super::has_authority_view(b),
        k == base_before_len(b),
        (b.path_start as int) <= k,
        (u.serialization.view().len() as int) >= k + 1,
        (u.serialization.view().len() as int) <= 0xFFFF_FFFF,
        (u.scheme_end as int) == (b.scheme_end as int),
        (u.username_end as int) == (b.username_end as int),
        (u.host_start as int) == (b.host_start as int),
        (u.host_end as int) == (b.host_end as int),
        u.host == b.host,
        u.port == b.port,
        (u.path_start as int) == (b.path_start as int),
        u.query_start == b.query_start,
        u.fragment_start == Option::Some(k as u32),
        forall|j: int| 0 <= j && j < k
            ==> u.serialization.view().index(j)
                == b.serialization.view().index(j),
        u.serialization.view().index(k) == 0x23u8,
    ensures
        super::url_invariant(u),
{
    let bs = b.serialization.view();
    let s = u.serialization.view();
    let nb = bs.len() as int;
    let n = s.len() as int;
    let se = b.scheme_end as int;
    let ps = b.path_start as int;
    // the boundary placement and the base's own byte there
    if b.fragment_start.is_some() {
        assert((b.fragment_start.unwrap() as int) == k && k < nb);
        assert(bs.index(k) == 0x23u8);
    } else {
        assert(k == nb);
    }
    assert(k < n);
    // the scheme region sits fully below the boundary (the authority
    // branch pins path_start past the scheme_end colon)
    assert(s.subrange(0, se) == bs.subrange(0, se)) by {
        assert forall|j: int| 0 <= j && j < se
            implies s.subrange(0, se).index(j)
                == bs.subrange(0, se).index(j) by {
            vstd::seq::lemma_seq_subrange_index(s, 0, se, j);
            vstd::seq::lemma_seq_subrange_index(bs, 0, se, j);
            assert(s.index(j) == bs.index(j));
        }
        vstd::seq::lemma_seq_ext_equal(s.subrange(0, se),
            bs.subrange(0, se));
    }
    assert(scheme_type_of(s.subrange(0, se))
        == scheme_type_of(bs.subrange(0, se)));
    // the authority branch facts: se+3 <= every component offset to
    // path_start, and the record's slashes are the base's own
    assert(se + 3 <= ps);
    assert(super::has_authority_view(u)) by {
        assert(s.index(se + 1) == 0x2Fu8
            && s.index(se + 2) == 0x2Fu8);
        assert(se + 3 <= n);
    }
    let ue = u.username_end as int;
    let he = u.host_end as int;
    // the only component slot the prolong can touch is
    // username_end == k: the base byte there ('#') settles the
    // wildcard arm of its own match, the terminus conjunct takes
    // over at k == n
    if ue == k {
        if k == nb {
            assert(ue == se + 3);
        } else {
            assert(bs.index(ue) == 0x23u8);
            assert(ue == se + 3);
        }
    } else {
        assert(s.index(ue) == bs.index(ue));
    }
    // the port digit span rides the preserved prefix (the span only
    // exists when the record's region is a strict port region)
    if (he + 1) < ps {
        assert(s.subrange(he + 1, ps)
            == bs.subrange(he + 1, ps)) by {
            assert forall|j: int|
                #![trigger s.subrange(he + 1, ps).index(j)]
                0 <= j && j < (ps - (he + 1))
                implies s.subrange(he + 1, ps).index(j)
                    == bs.subrange(he + 1, ps).index(j) by {
                vstd::seq::lemma_seq_subrange_index(s, he + 1, ps, j);
                vstd::seq::lemma_seq_subrange_index(bs, he + 1, ps, j);
                assert(s.index(he + 1 + j) == bs.index(he + 1 + j));
            }
            vstd::seq::lemma_seq_ext_equal(s.subrange(he + 1, ps),
                bs.subrange(he + 1, ps));
        }
    }
    // the query/fragment wrap conjuncts: the '?' slot is a preserved
    // base byte, the '#' slot is the boundary
    if u.query_start.is_some() {
        let qs = u.query_start.unwrap() as int;
        if b.fragment_start.is_some() {
            assert(k == (b.fragment_start.unwrap() as int));
        } else {
            assert(qs < nb);
        }
        assert(bs.index(qs) == 0x3Fu8);
        assert(s.index(qs) == bs.index(qs));
    }
}

/// The anarchist-branch digest of the record carry: the base holds no
/// authority and the record keeps it (the '#' slot -- or a preserved
/// base byte -- keeps one of the two bytes behind the colon a
/// non-slash); the opaque "/." prefix and the "//" path-head pins sit
/// strictly below the boundary on the opaque arm, and the plain arm
/// keeps the path anchor at scheme_end+1.
pub proof fn frag_carry_anarchist(
    b: &super::Url,
    u: &super::Url,
    k: int,
)
    requires
        base_url_face(b),
        !super::has_authority_view(b),
        k == base_before_len(b),
        (b.path_start as int) <= k,
        (u.serialization.view().len() as int) >= k + 1,
        (u.serialization.view().len() as int) <= 0xFFFF_FFFF,
        (u.scheme_end as int) == (b.scheme_end as int),
        (u.username_end as int) == (b.username_end as int),
        (u.host_start as int) == (b.host_start as int),
        (u.host_end as int) == (b.host_end as int),
        u.host == b.host,
        u.port == b.port,
        (u.path_start as int) == (b.path_start as int),
        u.query_start == b.query_start,
        u.fragment_start == Option::Some(k as u32),
        forall|j: int| 0 <= j && j < k
            ==> u.serialization.view().index(j)
                == b.serialization.view().index(j),
        u.serialization.view().index(k) == 0x23u8,
    ensures
        super::url_invariant(u),
{
    let bs = b.serialization.view();
    let s = u.serialization.view();
    let nb = bs.len() as int;
    let se = b.scheme_end as int;
    let ps = b.path_start as int;
    // the boundary placement and the base's own byte there
    if b.fragment_start.is_some() {
        assert((b.fragment_start.unwrap() as int) == k && k < nb);
        assert(bs.index(k) == 0x23u8);
    } else {
        assert(k == nb);
    }
    // the record stays on the no-authority branch: at least one of
    // the two bytes behind the colon fails the "//" pin
    assert(!super::has_authority_view(u)) by {
        if k == se + 1 {
            assert(s.index(se + 1) == 0x23u8);
            assert(s.index(se + 1) != 0x2Fu8);
        } else if k == se + 2 {
            assert(s.index(se + 2) == 0x23u8);
            assert(s.index(se + 2) != 0x2Fu8);
        } else {
            assert(!(bs.index(se + 1) == 0x2Fu8
                && bs.index(se + 2) == 0x2Fu8));
        }
    }
    if ps == se + 3 {
        // the opaque base: the '/','.' prefix and the '//'
        // path-head pins are the base's own bytes
        assert(super::opaque_path_double_slash(b));
        assert(bs.index(se + 1) == 0x2Fu8
            && bs.index(se + 2) == 0x2Eu8);
        assert(bs.index(se + 3) == 0x2Fu8
            && bs.index(se + 4) == 0x2Fu8);
        // the '#' slot can not land on a pinned head byte, and the
        // record can not end inside the pinned head
        assert(k >= se + 5) by {
            if k == se + 3 {
                if b.fragment_start.is_some() {
                    assert(bs.index(se + 3) == 0x23u8);
                    assert(false);
                } else {
                    assert(k == nb);
                    if b.query_start.is_some() {
                        assert((b.query_start.unwrap() as int) < nb);
                        assert((b.query_start.unwrap() as int)
                            >= se + 3);
                        assert(false);
                    }
                    assert(k < se + 5);
                    assert(false);
                }
            } else if k == se + 4 {
                if b.fragment_start.is_some() {
                    assert(bs.index(se + 4) == 0x23u8);
                    assert(false);
                } else {
                    assert(k == nb);
                    if b.query_start.is_some() {
                        assert((b.query_start.unwrap() as int) < nb);
                        assert((b.query_start.unwrap() as int)
                            >= se + 3);
                        assert(false);
                    }
                    assert(k < se + 5);
                    assert(false);
                }
            }
        }
        // the head bytes and the region end carry
        assert(s.index(se + 3) == 0x2Fu8
            && s.index(se + 4) == 0x2Fu8);
        if u.query_start.is_some() {
            let qs = u.query_start.unwrap() as int;
            assert(bs.index(qs) == 0x3Fu8);
            assert(super::path_end_view(u) == qs);
            if qs == se + 3 {
                assert(bs.index(se + 3) == 0x2Fu8);
                assert(false);
            }
            if qs == se + 4 {
                assert(bs.index(se + 4) == 0x2Fu8);
                assert(false);
            }
            assert(super::opaque_path_double_slash(u));
        } else {
            assert(super::path_end_view(u) == k);
            assert(super::opaque_path_double_slash(u));
        }
        assert(s.index(se + 1) == 0x2Fu8
            && s.index(se + 2) == 0x2Eu8);
    } else {
        // the plain anarchist base: path_start == se+1 and the
        // record keeps the non-opacity (the head bytes and the
        // region end are the base's own below k)
        assert(ps == se + 1);
        assert(!super::opaque_path_double_slash(u)) by {
            if k <= se + 2 {
                let pend = super::path_end_view(u);
                assert(pend <= se + 2) by {
                    if u.query_start.is_some() {
                        assert(pend
                            == (u.query_start.unwrap() as int));
                        assert(pend < k);
                    } else {
                        assert(pend == k);
                    }
                }
                assert((se + 1) + 2 > pend);
            } else {
                assert(s.index(se + 1) == bs.index(se + 1));
                assert(s.index(se + 2) == bs.index(se + 2));
                if u.query_start.is_some() {
                    let qs = u.query_start.unwrap() as int;
                    assert(super::path_end_view(u) == qs
                        && super::path_end_view(b) == qs);
                } else {
                    assert(super::path_end_view(u) == k
                        && super::path_end_view(b) == k);
                }
                assert(super::opaque_path_double_slash(u)
                    == super::opaque_path_double_slash(b));
                assert(!super::opaque_path_double_slash(b));
            }
        }
        assert((u.path_start as int) == se + 1);
    }
    // the query/fragment wrap conjuncts: the '?' slot is a preserved
    // base byte, the '#' slot is the boundary
    if u.query_start.is_some() {
        let qs = u.query_start.unwrap() as int;
        if b.fragment_start.is_some() {
            assert(k == (b.fragment_start.unwrap() as int));
        } else {
            assert(qs < nb);
        }
        assert(bs.index(qs) == 0x3Fu8);
        assert(s.index(qs) == bs.index(qs));
    }
}

/// The record carry of the fragment-prolong arm (the wrap-up digest
/// of fragment_only above): the record copies every base component,
/// the serialization keeps the base prefix below the boundary k and
/// takes a '#' at k, the fragment sits at k; the two record branches
/// split into the authority and anarchist digests (the split keeps
/// each whole-fn check inside the solver budget).
pub proof fn fragment_prolong_carry(
    b: &super::Url,
    u: &super::Url,
    k: int,
)
    requires
        base_url_face(b),
        k == base_before_len(b),
        (b.path_start as int) <= k,
        (u.serialization.view().len() as int) >= k + 1,
        (u.serialization.view().len() as int) <= 0xFFFF_FFFF,
        (u.scheme_end as int) == (b.scheme_end as int),
        (u.username_end as int) == (b.username_end as int),
        (u.host_start as int) == (b.host_start as int),
        (u.host_end as int) == (b.host_end as int),
        u.host == b.host,
        u.port == b.port,
        (u.path_start as int) == (b.path_start as int),
        u.query_start == b.query_start,
        u.fragment_start == Option::Some(k as u32),
        forall|j: int| 0 <= j && j < k
            ==> u.serialization.view().index(j)
                == b.serialization.view().index(j),
        u.serialization.view().index(k) == 0x23u8,
    ensures
        super::url_invariant(u),
{
    if super::has_authority_view(b) {
        frag_carry_authority(b, u, k);
    } else {
        frag_carry_anarchist(b, u, k);
    }
}

impl Parser<'_> {

/// Origin Rust (parser.rs:708-722): the None first-char arm of
/// parse_relative -- copy everything except the fragment into the
/// fresh serialization, hand every base component to the record, drop
/// the fragment slot. The debug assert on the empty serialization
/// (parser.rs:707) rides the calling dispatcher's requires; the record
/// assembly cannot fail, the upstream ParseResult shape is kept for
/// the caller face.
pub exec fn rel_none_arm(
    &mut self,
    base_url: &super::Url,
) -> (r: Result<super::Url, ParseError>)
    requires
        old(self).serialization.view().len() == 0,
        base_url_face(base_url),
    ensures
        machine_domain(final(self).serialization.view()),
        r.is_ok(),
        ({
            let u = r.unwrap();
            &&& super::url_invariant(&u)
            &&& u.serialization.view()
                == base_url.serialization.view().subrange(
                    0, base_before_len(base_url))
            &&& u.fragment_start.is_none()
            &&& (u.scheme_end as int)
                == (base_url.scheme_end as int)
            &&& (u.username_end as int)
                == (base_url.username_end as int)
            &&& (u.host_start as int)
                == (base_url.host_start as int)
            &&& (u.host_end as int) == (base_url.host_end as int)
            &&& u.host == base_url.host
            &&& u.port == base_url.port
            &&& (u.path_start as int) == (base_url.path_start as int)
            &&& u.query_start == base_url.query_start
        }),
{
    let ghost bs = base_url.serialization.view();
    let ghost k0 = base_before_len(base_url);
    let k0u: u32 = match base_url.fragment_start {
        Option::Some(fs) => {
            proof {
                assert((fs as int) < (bs.len() as int));
                assert((fs as int) == k0);
            }
            fs
        }
        Option::None => super::url_len32(&base_url.serialization),
    };
    proof {
        assert((k0u as int) == k0);
        assert(k0 <= (bs.len() as int));
    }
    let before = super::bytes_slice(&base_url.serialization, 0, k0u);
    proof {
        assert(before.view() == bs.subrange(0, k0));
        machine_domain_subrange(bs, 0, k0);
    }
    vec_append_bytes(&mut self.serialization, &before);
    let ghost fin = self.serialization.view();
    proof {
        assert(fin == bs.subrange(0, k0));
        assert(machine_domain(fin));
        assert((fin.len() as int) == k0);
    }
    // the record: the copy plus the base components, fragment dropped
    // (parser.rs:716-722)
    let u = super::Url {
        serialization: bytes_own(&self.serialization),
        scheme_end: base_url.scheme_end,
        username_end: base_url.username_end,
        host_start: base_url.host_start,
        host_end: base_url.host_end,
        host: base_url.host,
        port: base_url.port,
        path_start: base_url.path_start,
        query_start: base_url.query_start,
        fragment_start: Option::None,
    };
    proof {
        if super::has_authority_view(base_url) {
            rel_carry_none_authority(base_url, &u, k0);
        } else {
            rel_carry_none_anarchist(base_url, &u, k0);
        }
    }
    Ok(u)
}

/// Origin Rust (parser.rs:723-740): the '?' first-char arm of
/// parse_relative -- copy the base up to the first of its query or
/// fragment boundary, then run the query/fragment scan over the input
/// (which still starts at the '?') and install the two scan positions
/// on the record. The upstream `..*base_url` field spread becomes the
/// explicit component copies; the scan's Overflow face is the only
/// error arm; the debug assert on the empty serialization
/// (parser.rs:707) rides the calling dispatcher's requires.
pub exec fn rel_query_arm<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
    base_url: &super::Url,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        (input_rem(&input).len() as int) > 0,
        input_rem(&input).index(0) == 0x3Fu8,
        old(self).serialization.view().len() == 0,
        self.context == Context::UrlParser,
        base_url_face(base_url),
        scheme_type
            == scheme_type_of(base_url.serialization.view()
                .subrange(0, base_url.scheme_end as int)),
        (base_url.serialization.view().len() as int)
            + 6 * (input_rem(&input).len() as int) + 12
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_err() ==> r == Err(ParseError::Overflow)),
        (r.is_ok() ==> ({
            let u = r.unwrap();
            let ks = base_before_query_len(base_url);
            &&& super::url_invariant(&u)
            &&& u.query_start == Option::Some(ks as u32)
            &&& u.fragment_start.is_some()
                ==> (((u.fragment_start.unwrap() as int) > ks)
                    && (u.fragment_start.unwrap() as int)
                        < u.serialization.view().len() as int
                    && u.serialization.view().index(
                        u.fragment_start.unwrap() as int) == 0x23u8)
            &&& (u.scheme_end as int)
                == (base_url.scheme_end as int)
            &&& (u.username_end as int)
                == (base_url.username_end as int)
            &&& (u.host_start as int)
                == (base_url.host_start as int)
            &&& (u.host_end as int) == (base_url.host_end as int)
            &&& u.host == base_url.host
            &&& u.port == base_url.port
            &&& (u.path_start as int) == (base_url.path_start as int)
        })),
{
    let ghost rem0 = input_rem(&input);
    let ghost bs = base_url.serialization.view();
    let ghost ks = base_before_query_len(base_url);
    // the copy boundary (parser.rs:726-733): the first of the base's
    // query / fragment positions, the whole serialization when both
    // are absent
    let ksu: u32 = match (base_url.query_start,
        base_url.fragment_start)
    {
        (Option::Some(qi), _) => {
            proof {
                assert((qi as int) == ks);
            }
            qi
        }
        (Option::None, Option::Some(fi)) => {
            proof {
                assert((fi as int) == ks);
            }
            fi
        }
        (Option::None, Option::None) => {
            super::url_len32(&base_url.serialization)
        }
    };
    proof {
        assert((ksu as int) == ks);
        assert(ks <= (bs.len() as int));
    }
    let before = super::bytes_slice(&base_url.serialization, 0, ksu);
    proof {
        assert(before.view() == bs.subrange(0, ks));
        machine_domain_subrange(bs, 0, ks);
    }
    vec_append_bytes(&mut self.serialization, &before);
    let ghost precopy = self.serialization.view();
    proof {
        assert(precopy == bs.subrange(0, ks));
        assert(machine_domain(precopy));
        // the scan budget over the copied prefix
        assert((precopy.len() as int)
            + 6 * (rem0.len() as int) + 10 <= 0xFFFF_FFFF);
        assert((base_url.scheme_end as int)
            <= (precopy.len() as int));
        assert((base_url.path_start as int) <= ks) by {
            if base_url.query_start.is_some() {
                assert((base_url.query_start.unwrap() as int)
                    >= (base_url.path_start as int));
            } else if base_url.fragment_start.is_some() {
                assert((base_url.fragment_start.unwrap() as int)
                    >= (base_url.path_start as int));
            } else {
                assert((base_url.path_start as int)
                    <= (bs.len() as int));
            }
        }
    }
    // the query/fragment scan (parser.rs:734-735): the input still
    // starts at the '?', the scan positions are installed on the
    // record below
    let scan = self.parse_query_and_fragment(scheme_type,
        base_url.scheme_end, input);
    match scan {
        Result::Err(e) => Err(e),
        Result::Ok((qs, fs)) => {
            proof {
                let fin = self.serialization.view();
                // the scan's pins: the '?' slot at the copy boundary,
                // the fragment slot strictly behind it
                assert(qs.is_some());
                assert((qs.unwrap() as int) == ks);
                assert(fin.index(ks) == 0x3Fu8);
                assert((fin.len() as int)
                    > (precopy.len() as int));
                if fs.is_some() {
                    assert((fs.unwrap() as int) > ks);
                    assert(fin.index(fs.unwrap() as int) == 0x23u8);
                    assert((fs.unwrap() as int)
                        < (fin.len() as int));
                }
                // the preserved prefix below the boundary
                assert forall|j: int| 0 <= j && j < ks
                    implies fin.index(j) == bs.index(j) by {
                    assert(fin.index(j) == precopy.index(j));
                    vstd::seq::lemma_seq_subrange_index(bs, 0, ks, j);
                }
                // the final length bound
                assert((fin.len() as int)
                    <= (precopy.len() as int)
                        + 6 * (rem0.len() as int) + 4);
                assert((fin.len() as int) <= 0xFFFF_FFFF);
            }
            // the record: the scan output plus the base components
            // (parser.rs:737-740)
            let u = super::Url {
                serialization: bytes_own(&self.serialization),
                scheme_end: base_url.scheme_end,
                username_end: base_url.username_end,
                host_start: base_url.host_start,
                host_end: base_url.host_end,
                host: base_url.host,
                port: base_url.port,
                path_start: base_url.path_start,
                query_start: qs,
                fragment_start: fs,
            };
            proof {
                if super::has_authority_view(base_url) {
                    rel_carry_query_authority(base_url, &u, ks);
                } else {
                    rel_carry_query_anarchist(base_url, &u, ks);
                }
            }
            Ok(u)
        }
    }
}

/// Origin Rust (parser.rs:741-783, the '/' | '\\' head of
/// parse_relative): the slash-arm state. A '/'-or-'\\' run of at
/// least two slashes hands off to the double-slash state over the
/// base scheme prefix (the ExpectedDoubleSlash violation log of
/// parser.rs:757-763 is a value no-op); the take-while clone and the
/// split_prefix("//") probe decide whether the suffix after the two
/// literal bytes or the post-run remainder is the entry. A single
/// slash copies the base up to its path_start, writes the fresh '/'
/// anchor, scans the relative path, and wraps up over the base
/// components (the FACE selection below: authority base -> FACE-1,
/// regular anarchist -> FACE-2, opaque-pinned anarchist -> FACE-3,
/// the case-2 revival surface).
/// The wrap-up entry digest of the single-slash branch of the slash
/// arm and of the pop/merge branch of the default arm: the scanned
/// record (base-preserved prefix below the '/' anchor, the relative
/// path above it) satisfies one of the three with_query_and_fragment
/// entry faces over the base components -- FACE-1 when the base has
/// authority, FACE-2 for the regular anarchist base, FACE-3 for the
/// opaque-pinned anarchist base (the case-2 revival surface). The
/// entry serialization enters only through its preservation of the
/// base bytes below the anchor (the arms prove the preservation from
/// their own write shapes).
pub proof fn rel_slash_carry(
    base_url: &super::Url,
    serf: Seq<u8>,
    entryser: Seq<u8>,
    scheme_type: SchemeType,
)
    requires
        base_url_face(base_url),
        machine_domain(serf),
        machine_domain(entryser),
        (forall|j: int| 0 <= j && j < (base_url.path_start as int)
            ==> entryser.index(j)
                == base_url.serialization.view().index(j)),
        (forall|j: int| 0 <= j && j < (base_url.path_start as int)
            ==> serf.index(j) == entryser.index(j)),
        (serf.len() as int) > (base_url.path_start as int),
        serf.index(base_url.path_start as int) == 0x2Fu8,
        scheme_type == scheme_type_of(base_url.serialization.view()
            .subrange(0, base_url.scheme_end as int)),
    ensures
        1 <= (base_url.scheme_end as int),
        (base_url.scheme_end as int) < (serf.len() as int),
        super::is_ascii_alpha(serf.index(0)),
        (forall|j: int| 1 <= j
            && j < (base_url.scheme_end as int)
            ==> super::is_scheme_char(serf.index(j))),
        serf.index(base_url.scheme_end as int) == 0x3Au8,
        scheme_type == scheme_type_of(serf.subrange(
            0, base_url.scheme_end as int)),
        (base_url.path_start as int) <= (serf.len() as int),
        (
            // FACE-1: the authority record
            (super::has_authority_view(base_url) && ({
                let se = base_url.scheme_end as int;
                let ue = base_url.username_end as int;
                let hs = base_url.host_start as int;
                let he = base_url.host_end as int;
                let ps = base_url.path_start as int;
                &&& se + 3 <= (serf.len() as int)
                &&& serf.index(se + 1) == 0x2Fu8
                &&& serf.index(se + 2) == 0x2Fu8
                &&& se + 3 <= ue
                &&& ue <= (serf.len() as int)
                &&& (ue == (serf.len() as int)
                    ==> ue == se + 3)
                &&& ((ue == (serf.len() as int))
                    || (serf.index(ue) == 0x3Au8
                        && hs >= ue + 2
                        && serf.index(hs - 1) == 0x40u8)
                    || (serf.index(ue) == 0x40u8
                        && hs == ue + 1)
                    || (ue == se + 3
                        && serf.index(ue) != 0x3Au8
                        && serf.index(ue) != 0x40u8))
                &&& ue <= hs
                &&& hs <= (serf.len() as int)
                &&& he >= hs
                &&& he <= (serf.len() as int)
                &&& ps >= he
                &&& ps <= (serf.len() as int)
                &&& ((base_url.host
                    == super::HostInternal::None)
                    == (hs == he))
                &&& (ps == he ==> base_url.port.is_none())
                &&& (ps > he ==> (
                    serf.index(he) == 0x3Au8
                    && he + 2 <= ps
                    && (forall|j: int| he + 1 <= j && j < ps
                        ==> super::is_dec_digit(
                            serf.index(j)))
                    && base_url.port.is_some()
                    && (base_url.port.unwrap() as int)
                        == super::dec_val(serf.subrange(
                            he + 1, ps))))
                &&& (ps < (serf.len() as int)
                    ==> (serf.index(ps) == 0x2Fu8
                        || serf.index(ps) == 0x23u8
                        || serf.index(ps) == 0x3Fu8))
            }))
            ||
            // FACE-2: the regular anarchist record
            (!super::has_authority_view(base_url)
                && (base_url.path_start as int)
                    == (base_url.scheme_end as int) + 1
                && base_url.username_end
                    == base_url.scheme_end + 1
                && base_url.host_start
                    == base_url.scheme_end + 1
                && base_url.host_end
                    == base_url.scheme_end + 1
                && base_url.host
                    == super::HostInternal::None
                && base_url.port.is_none())
            ||
            // FACE-3: the opaque-pinned anarchist entry
            (!super::has_authority_view(base_url)
                && (base_url.path_start as int)
                    == (base_url.scheme_end as int) + 3
                && base_url.username_end
                    == base_url.scheme_end + 1
                && base_url.host_start
                    == base_url.scheme_end + 1
                && base_url.host_end
                    == base_url.scheme_end + 1
                && base_url.host
                    == super::HostInternal::None
                && base_url.port.is_none()
                && (base_url.path_start as int)
                    < (serf.len() as int)
                && serf.index(
                    (base_url.scheme_end as int) + 1) == 0x2Fu8
                && serf.index(
                    (base_url.scheme_end as int) + 2) == 0x2Eu8
                && serf.index(
                    base_url.path_start as int) == 0x2Fu8)
        ),
{
    let bs = base_url.serialization.view();
    let se = base_url.scheme_end as int;
    let ue = base_url.username_end as int;
    let hs = base_url.host_start as int;
    let he = base_url.host_end as int;
    let ps = base_url.path_start as int;
    let n = serf.len() as int;
    // the entry prefix rides below the anchor (the entry carried the
    // base bytes there, the path scan preserved them)
    assert forall|j: int| 0 <= j && j < ps
        implies serf.index(j) == bs.index(j) by {
        assert(serf.index(j) == entryser.index(j));
        assert(entryser.index(j) == bs.index(j));
    }
    // the scheme byte range survived
    assert(serf.subrange(0, se) == bs.subrange(0, se)) by {
        assert forall|j: int| 0 <= j && j < se
            implies serf.subrange(0, se).index(j)
                == bs.subrange(0, se).index(j) by {
            vstd::seq::lemma_seq_subrange_index(serf, 0, se, j);
            vstd::seq::lemma_seq_subrange_index(bs, 0, se, j);
            assert(serf.index(j) == bs.index(j));
        }
        vstd::seq::lemma_seq_ext_equal(serf.subrange(0, se),
            bs.subrange(0, se));
    }
    if super::has_authority_view(base_url) {
        // FACE-1: every component pin sits below the anchor and
        // survives the path scan
        assert(se + 3 <= ps);
        assert(n > ps);
        assert(se < n);
        assert(serf.index(se + 1) == 0x2Fu8);
        assert(serf.index(se + 2) == 0x2Fu8);
        assert(se + 3 <= ue);
        assert(ue <= ps);
        assert(hs >= ue);
        assert(hs <= he);
        assert(he <= ps);
        if ue < ps {
            assert(serf.index(ue) == bs.index(ue));
            if hs - 1 < ps {
                assert(serf.index(hs - 1) == bs.index(hs - 1));
            }
        } else {
            // username_end sits at the anchor: the new byte is the
            // '/', which matches only the wildcard arm of the base
            // userinfo (the ':'/'@' arms push host_start past the
            // anchor, contradicting the base's own ordering), so
            // username_end was pinned to scheme_end + 3
            assert(ue == ps);
            assert(serf.index(ue) == 0x2Fu8);
            if (ue as int) == (bs.len() as int) {
                // the terminus conjunct of the base face
                assert(ue == se + 3);
            } else {
                assert(ue < (bs.len() as int));
                assert(bs.index(ue) == 0x2Fu8
                    || bs.index(ue) == 0x3Fu8
                    || bs.index(ue) == 0x23u8);
                if bs.index(ue) == 0x3Au8 {
                    assert(false);
                }
                if bs.index(ue) == 0x40u8 {
                    assert(false);
                }
                assert(ue == se + 3);
            }
        }
        // the port span and its value ride the preserved prefix
        if ps > he {
            assert(serf.index(he) == bs.index(he));
            assert(bs.index(he) == 0x3Au8);
            assert(he + 2 <= ps);
            assert forall|j: int| he + 1 <= j && j < ps
                implies super::is_dec_digit(serf.index(j)) by {
                assert(serf.index(j) == bs.index(j));
            }
            assert(serf.subrange(he + 1, ps)
                == bs.subrange(he + 1, ps)) by {
                assert forall|j: int|
                    #![trigger serf.subrange(he + 1, ps).index(j)]
                    0 <= j && j < ps - (he + 1)
                    implies serf.subrange(he + 1, ps).index(j)
                        == bs.subrange(he + 1, ps).index(j) by {
                    vstd::seq::lemma_seq_subrange_index(serf,
                        he + 1, ps, j);
                    vstd::seq::lemma_seq_subrange_index(bs,
                        he + 1, ps, j);
                    assert(serf.index(he + 1 + j)
                        == bs.index(he + 1 + j));
                }
                vstd::seq::lemma_seq_ext_equal(
                    serf.subrange(he + 1, ps),
                    bs.subrange(he + 1, ps));
            }
        }
    } else if ps == se + 1 {
        // FACE-2: the regular anarchist record
        assert(base_url.username_end == base_url.scheme_end + 1);
        assert(base_url.host_start == base_url.scheme_end + 1);
        assert(base_url.host_end == base_url.scheme_end + 1);
        assert(base_url.host == super::HostInternal::None);
        assert(base_url.port.is_none());
    } else {
        // FACE-3: the opaque-pinned anarchist base (the case-2
        // revival: the "/." sits below the anchor, the fresh path
        // head at the anchor feeds the inner probe)
        assert(super::opaque_path_double_slash(base_url));
        assert(ps == se + 3);
        assert(n > ps);
        assert(se < n);
        assert(bs.index(se + 1) == 0x2Fu8);
        assert(bs.index(se + 2) == 0x2Eu8);
        assert(serf.index(se + 1) == 0x2Fu8);
        assert(serf.index(se + 2) == 0x2Eu8);
        assert(serf.index(ps) == 0x2Fu8);
        assert(base_url.username_end == base_url.scheme_end + 1);
        assert(base_url.host_start == base_url.scheme_end + 1);
        assert(base_url.host_end == base_url.scheme_end + 1);
        assert(base_url.host == super::HostInternal::None);
        assert(base_url.port.is_none());
    }
}

/* [verus note: rlimit = the whole-fn check of the slash arm rides the
   frontier of the ut_read_api ambient: with the body of the single-slash
   wrap-up already extracted (rel_slash_carry) the check still exceeds the
   default budget in that ambient deterministically (two consecutive
   300-second runs), while the same fn content closes at the default
   budget in the parse_machine and coverage_props ambients -- an ambient
   flip of the incremental frontier, closed at 45.  The fn's own content
   is untouched by the raise.  */
#[verifier::rlimit(45)]
pub exec fn rel_slash_arm<'i>(
    &mut self,
    input: Input<'i>,
    after_first: Input<'i>,
    scheme_type: SchemeType,
    base_url: &super::Url,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        input_wf(&after_first),
        input_rem(&after_first)
            == input_rem(&input).subrange(
                1, input_rem(&input).len() as int),
        (input_rem(&input).len() as int) > 0,
        input_rem(&input).index(0) == 0x2Fu8
            || input_rem(&input).index(0) == 0x5Cu8,
        old(self).serialization.view().len() == 0,
        self.context == Context::UrlParser,
        base_url_face(base_url),
        !super::cannot_be_a_base_view(base_url),
        rel_slash_face(input_rem(&input), scheme_type),
        scheme_type
            == scheme_type_of(base_url.serialization.view()
                .subrange(0, base_url.scheme_end as int)),
        (base_url.serialization.view().len() as int)
            + 16 * (input_rem(&input).len() as int) + 74
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_err() ==> (r == Err(ParseError::Overflow)
            || r == Err(ParseError::EmptyHost)
            || r == Err(ParseError::InvalidPort))),
        (r.is_ok() ==> super::url_invariant(&r.unwrap())),
{
    let ghost rem0 = input_rem(&input);
    let ghost bs = base_url.serialization.view();
    // the slash-run count (parser.rs:756)
    let (c, run_rest) = input.count_matching_slash_bs();
    proof {
        assert(input_rem(&run_rest)
            == rem0.subrange(c as int, rem0.len() as int));
        if (c as int) == 0 {
            // the head byte contradicts the zero count
            if (rem0.len() as int) > 0 {
                assert(rem0.index(0) != 0x2Fu8);
                assert(rem0.index(0) != 0x5Cu8);
                assert(false);
            } else {
                assert(false);
            }
        }
        assert((c as int) >= 1);
    }
    if c >= 2 {
        // the double-slash handoff (parser.rs:757-769)
        let se = base_url.scheme_end;
        let before = super::bytes_slice(&base_url.serialization, 0,
            se + 1);
        proof {
            assert(before.view()
                == bs.subrange(0, (se as int) + 1));
            machine_domain_subrange(bs, 0, (se as int) + 1);
            assert(machine_domain(before.view()));
        }
        vec_append_bytes(&mut self.serialization, &before);
        proof {
            let pre2 = self.serialization.view();
            assert(pre2 == bs.subrange(0, (se as int) + 1));
            assert((pre2.len() as int) == (se as int) + 1);
            assert(machine_domain(pre2));
            // the scheme prefix survived the copy
            assert forall|j: int| 0 <= j && j < (se as int)
                implies pre2.index(j) == bs.index(j) by {
                vstd::seq::lemma_seq_subrange_index(bs, 0,
                    (se as int) + 1, j);
            }
            assert(pre2.subrange(0, se as int)
                == bs.subrange(0, se as int)) by {
                vstd::seq::lemma_seq_ext_equal(pre2.subrange(0,
                    se as int), bs.subrange(0, se as int));
            }
            assert(scheme_type == scheme_type_of(
                pre2.subrange(0, se as int)));
            // scan budgets over either entry (the entry remainder is
            // a suffix of the input)
            assert(((se as int) + 1)
                + 16 * (rem0.len() as int) + 74
                <= (bs.len() as int)
                    + 16 * (rem0.len() as int) + 74);
        }
        match input.split_prefix_slash2() {
            Option::Some(after_prefix) => {
                // the "//"-prefix route (parser.rs:763-764)
                proof {
                    assert(input_rem(&after_prefix)
                        == rem0.subrange(2, rem0.len() as int));
                    assert((input_rem(&after_prefix).len() as int)
                        <= (rem0.len() as int));
                    assert(rem0.index(0) == 0x2Fu8);
                    assert(rem0.index(1) == 0x2Fu8);
                    assert(authority_entry_class(
                        rem0.subrange(2, rem0.len() as int),
                        is_special(scheme_type)));
                    assert(authority_entry_class(
                        input_rem(&after_prefix),
                        is_special(scheme_type)));
                }
                self.after_double_slash(after_prefix, scheme_type, se)
            }
            Option::None => {
                // the count route (parser.rs:765, 769)
                proof {
                    // the run prefix and its maximality
                    if (c as int) < (rem0.len() as int) {
                        assert forall|j: int| 0 <= j && j < (c as int)
                            implies (rem0.index(j) == 0x2Fu8
                                || rem0.index(j) == 0x5Cu8) by {}
                        assert(rem0.index(c as int) != 0x2Fu8);
                        assert(rem0.index(c as int) != 0x5Cu8);
                    } else {
                        assert((c as int) == (rem0.len() as int));
                        assert forall|j: int| 0 <= j && j < (c as int)
                            implies (rem0.index(j) == 0x2Fu8
                                || rem0.index(j) == 0x5Cu8) by {}
                    }
                    assert(authority_entry_class(
                        rem0.subrange(c as int, rem0.len() as int),
                        is_special(scheme_type)));
                    assert(authority_entry_class(
                        input_rem(&run_rest),
                        is_special(scheme_type)));
                    assert((input_rem(&run_rest).len() as int)
                        <= (rem0.len() as int));
                }
                self.after_double_slash(run_rest, scheme_type, se)
            }
        }
    } else {
        // the single-slash branch (parser.rs:770-783)
        proof {
            assert((c as int) == 1);
        }
        let ps = base_url.path_start;
        let before = super::bytes_slice(&base_url.serialization, 0,
            ps);
        proof {
            assert(before.view() == bs.subrange(0, ps as int));
            machine_domain_subrange(bs, 0, ps as int);
            assert(machine_domain(before.view()));
        }
        vec_append_bytes(&mut self.serialization, &before);
        self.serialization.push(0x2Fu8);
        proof {
            let entry = self.serialization.view();
            let ghost prepush = bs.subrange(0, ps as int);
            assert(entry == prepush + seq![0x2Fu8]);
            machine_domain_add(prepush, seq![0x2Fu8]);
            assert(machine_domain(entry));
            assert((entry.len() as int) == (ps as int) + 1);
            vstd::seq::lemma_seq_add_index2(prepush, seq![0x2Fu8],
                ps as int);
            assert(entry.index(ps as int) == 0x2Fu8);
            assert((input_rem(&after_first).len() as int)
                <= (rem0.len() as int));
            // the parse_path budget: (ps+1) + 5*tail + 32 rides the
            // arm budget (the prefix is a base slice)
            assert(((ps as int) + 1)
                + 5 * (input_rem(&after_first).len() as int) + 32
                <= (bs.len() as int)
                    + 16 * (rem0.len() as int) + 74);
            assert((entry.len() as int)
                + 5 * (input_rem(&after_first).len() as int) + 32
                <= 0xFFFF_FFFF);
            assert(entry.subrange(0, ps as int)
                == bs.subrange(0, ps as int)) by {
                assert forall|j: int| 0 <= j && j < (ps as int)
                    implies entry.subrange(0, ps as int).index(j)
                        == bs.subrange(0, ps as int).index(j) by {
                    vstd::seq::lemma_seq_subrange_index(entry, 0,
                        ps as int, j);
                    vstd::seq::lemma_seq_subrange_index(bs, 0,
                        ps as int, j);
                    vstd::seq::lemma_seq_add_index1(prepush,
                        seq![0x2Fu8], j);
                }
                vstd::seq::lemma_seq_ext_equal(
                    entry.subrange(0, ps as int),
                    bs.subrange(0, ps as int));
            }
        }
        let ghost entryser = self.serialization.view();
        let mut has_host: bool = true;
        let rem_path = self.parse_path(scheme_type, ps as usize,
            &mut has_host, after_first);
        // the wrap-up over the base components (parser.rs:774-783):
        // the FACE selection (authority -> FACE-1, regular anarchist
        // -> FACE-2, opaque-pinned anarchist -> FACE-3) rides the
        // rel_slash_carry digest above; the budgets thread here
        proof {
            let serf = self.serialization.view();
            // the entry carried the base bytes below the anchor
            assert forall|j: int| 0 <= j
                && j < (base_url.path_start as int)
                implies entryser.index(j) == bs.index(j) by {
                vstd::seq::lemma_seq_add_index1(
                    bs.subrange(0, base_url.path_start as int),
                    seq![0x2Fu8], j);
                vstd::seq::lemma_seq_subrange_index(bs, 0,
                    base_url.path_start as int, j);
            }
            Self::rel_slash_carry(base_url, serf, entryser,
                scheme_type);
            // the wrap-up budget: the final length is bounded by the
            // entry plus the scan growth
            let ps = base_url.path_start as int;
            let n = serf.len() as int;
            let a = input_rem(&after_first).len() as int;
            assert((n) <= (ps + 1) + 5 * a + 6);
            assert((input_rem(&rem_path).len() as int) <= a);
            assert((n)
                + 6 * (input_rem(&rem_path).len() as int) + 12
                <= (bs.len() as int)
                    + 16 * (rem0.len() as int) + 74);
        }
        self.with_query_and_fragment(
            scheme_type,
            base_url.scheme_end,
            base_url.username_end,
            base_url.host_start,
            base_url.host_end,
            base_url.host,
            base_url.port,
            base_url.path_start,
            rem_path,
        )
    }
}

/// Origin Rust (parser.rs:784-823, the default arm of parse_relative):
/// the pop/merge state -- a relative reference without a copy or
/// slash head merges onto the base: copy the serialization up to the
/// before-query boundary, pop the last path segment (pop_path's rfind
/// premise derives from the rel_merge_face purity dogma -- the base's
/// path head pins '/', the purity rules the rest of the region a
/// path byte), re-anchor when the popped path region is empty
/// (origin's is_special || !input.is_empty() disjunct is constantly
/// true under the nonempty-input cone), scan the relative path over
/// the whole input (origin's Some('/') re-split at parser.rs:806-818
/// is provably absent -- the cone head is no slash), and wrap up over
/// the base components via the rel_slash_carry digest. The
/// opaque-pinned anarchist bases are outside this cone (rel_merge_face).
/// No host scan ever runs (the error surface is Overflow only).
/* [verus note: rlimit = the whole-fn check rides the frontier of the
   default budget under the ut_read_api and coverage_props ambient
   contexts once the deep-host batch's material entered the module's
   air context -- the identical fn content closed at the DEFAULT
   budget in the parse_machine ambient in the same sweeps (three
   consecutive default failures in each of the two ambients, the
   ambient-flip phenomenon and the same protocol as rel_slash_arm@45
   and parse_host_and_port@30); only the resource ceiling is raised,
   no obligation is relaxed, the fn's own content is untouched] */
#[verifier::rlimit(45)]
pub exec fn rel_merge_arm<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
    base_url: &super::Url,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        (input_rem(&input).len() as int) > 0,
        (input_rem(&input).index(0) != 0x3Fu8
            && input_rem(&input).index(0) != 0x23u8
            && input_rem(&input).index(0) != 0x2Fu8
            && input_rem(&input).index(0) != 0x5Cu8),
        old(self).serialization.view().len() == 0,
        self.context == Context::UrlParser,
        base_url_face(base_url),
        !super::cannot_be_a_base_view(base_url),
        rel_merge_face(base_url, input_rem(&input)),
        scheme_type
            == scheme_type_of(base_url.serialization.view()
                .subrange(0, base_url.scheme_end as int)),
        (base_url.serialization.view().len() as int)
            + 16 * (input_rem(&input).len() as int) + 74
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_err() ==> r == Err(ParseError::Overflow)),
        (r.is_ok() ==> super::url_invariant(&r.unwrap())),
{
    let ghost rem0 = input_rem(&input);
    let ghost bs = base_url.serialization.view();
    // (parser.rs:785-791): the before-query boundary
    let ksu: u32 = match (base_url.query_start,
        base_url.fragment_start)
    {
        (Option::Some(qi), _) => {
            proof {
                assert((qi as int)
                    == base_before_query_len(base_url));
            }
            qi
        }
        (Option::None, Option::Some(fi)) => {
            proof {
                assert((fi as int)
                    == base_before_query_len(base_url));
            }
            fi
        }
        (Option::None, Option::None) => {
            super::url_len32(&base_url.serialization)
        }
    };
    proof {
        assert((ksu as int) == base_before_query_len(base_url));
        assert(base_before_query_len(base_url)
            == super::path_end_view(base_url));
        assert((ksu as int) <= (bs.len() as int));
    }
    let before = super::bytes_slice(&base_url.serialization, 0, ksu);
    proof {
        assert(before.view() == bs.subrange(0, ksu as int));
        machine_domain_subrange(bs, 0, ksu as int);
        assert(machine_domain(before.view()));
        // a nonempty copied path region keeps its head '/' (the
        // invariant 3-way plus the purity dogma for authority bases;
        // the regular anarchist's head byte is the
        // !cannot_be_a_base pin)
        if (ksu as int) > (base_url.path_start as int) {
            if super::has_authority_view(base_url) {
                assert(bs.index(base_url.path_start as int)
                    == 0x2Fu8
                    || bs.index(base_url.path_start as int)
                        == 0x3Fu8
                    || bs.index(base_url.path_start as int)
                        == 0x23u8);
            } else {
                assert((base_url.path_start as int)
                    == (base_url.scheme_end as int) + 1);
                assert(bs.index(base_url.path_start as int)
                    == 0x2Fu8);
            }
            assert(bs.index(base_url.path_start as int) == 0x2Fu8);
        }
    }
    vec_append_bytes(&mut self.serialization, &before);
    proof {
        let o = self.serialization.view();
        assert(o == bs.subrange(0, ksu as int));
        assert(machine_domain(o));
        if (ksu as int) > (base_url.path_start as int) {
            vstd::seq::lemma_seq_subrange_index(bs, 0, ksu as int,
                base_url.path_start as int);
            vstd::seq::lemma_seq_subrange_index(
                o, 0, ksu as int, base_url.path_start as int);
            assert((base_url.path_start as int) < ksu as int);
            assert(o.index(base_url.path_start as int)
                == bs.index(base_url.path_start as int));
            assert(o.index(base_url.path_start as int) == 0x2Fu8);
        }
    }
    // (parser.rs:793): pop the last path segment; the guard mirrors
    // the internal length probe of origin pop_path
    if ksu > base_url.path_start {
        let is_file = scheme_type.is_file();
        let ghost pre_pop = self.serialization.view();
        pop_path(&mut self.serialization, is_file,
            base_url.path_start as usize);
        proof {
            let o = pre_pop;
            let f = self.serialization.view();
            // the cut kept a prefix of the copied bytes (machine
            // domain and the base facts ride the prefix), the anchor
            // is above the floor
            machine_domain_subrange(o, 0, f.len() as int);
            assert(machine_domain(f));
            assert((base_url.path_start as int)
                < (f.len() as int));
            assert((f.len() as int) <= (ksu as int));
            // every kept byte is a copied base byte
            assert forall|j: int| 0 <= j && j < (f.len() as int)
                implies f.index(j) == bs.index(j) by {
                vstd::seq::lemma_seq_subrange_index(o, 0,
                    f.len() as int, j);
                vstd::seq::lemma_seq_subrange_index(bs, 0,
                    ksu as int, j);
                assert(f.index(j) == o.index(j));
                assert(o.index(j) == bs.index(j));
            }
            assert(f.index(base_url.path_start as int) == 0x2Fu8);
        }
    }
    // (parser.rs:795-801): the re-anchor when the path region is
    // empty (is_special || !input.is_empty() holds by the cone)
    if self.serialization.len() == base_url.path_start as usize {
        let ghost pre_anchor = self.serialization.view();
        self.serialization.push(0x2Fu8);
        proof {
            let f = self.serialization.view();
            assert(pre_anchor == bs.subrange(0, ksu as int));
            assert(f == pre_anchor + seq![0x2Fu8]);
            machine_domain_add(pre_anchor, seq![0x2Fu8]);
            assert(machine_domain(f));
            assert((f.len() as int)
                == (base_url.path_start as int) + 1);
            vstd::seq::lemma_seq_add_index2(pre_anchor,
                seq![0x2Fu8], base_url.path_start as int);
            assert(f.index(base_url.path_start as int) == 0x2Fu8);
            assert forall|j: int| 0 <= j
                && j < (base_url.path_start as int)
                implies f.index(j) == bs.index(j) by {
                vstd::seq::lemma_seq_add_index1(pre_anchor,
                    seq![0x2Fu8], j);
                vstd::seq::lemma_seq_subrange_index(bs, 0,
                    ksu as int, j);
            }
        }
    } else {
        proof {
            let f = self.serialization.view();
            assert((f.len() as int)
                > (base_url.path_start as int));
        }
    }
    let ghost entryser = self.serialization.view();
    proof {
        // the entry state of the path scan: the anchor, the pure
        // region, and the base bytes below the anchor (whichever
        // path reached it, cut or anchor push, established those in
        // its own block)
        let f = entryser;
        assert((f.len() as int) > (base_url.path_start as int));
        assert(f.index(base_url.path_start as int) == 0x2Fu8);
        assert forall|j: int|
            (base_url.path_start as int) <= j
                && j < (f.len() as int)
            implies f.index(j) != 0x3Fu8
                && f.index(j) != 0x23u8
            by {
            if (ksu as int) > (base_url.path_start as int) {
                assert(f.index(j) == bs.index(j));
            }
        }
        assert forall|j: int| 0 <= j
            && j < (base_url.path_start as int)
            implies f.index(j) == bs.index(j) by {
            if (ksu as int) > (base_url.path_start as int) {
                // the cut path kept a base-byte prefix
                assert(f.index(j) == bs.index(j));
            }
            // the anchor path's block established it directly
        }
        // machine domain and the scan budget
        assert(machine_domain(f));
        assert((f.len() as int) <= (bs.len() as int) + 1);
        assert(((f.len() as int)
            + 5 * (input_rem(&input).len() as int) + 32)
            <= ((bs.len() as int)
                + 16 * (input_rem(&input).len() as int) + 74));
        assert((f.len() as int)
            + 5 * (input_rem(&input).len() as int) + 32
            <= 0xFFFF_FFFF);
    }
    let mut has_host: bool = true;
    // (parser.rs:802-818): the relative-path scan over the whole
    // input (the Some('/') re-split is absent by the cone head)
    let rem_path = self.parse_path(scheme_type,
        base_url.path_start as usize, &mut has_host, input);
    // (parser.rs:819-823): the wrap-up over the base components
    proof {
        let serf = self.serialization.view();
        assert forall|j: int| 0 <= j
            && j < (base_url.path_start as int)
            implies entryser.index(j) == bs.index(j) by {
            assert(serf.index(j) == entryser.index(j));
        }
        assert((serf.len() as int)
            > (base_url.path_start as int));
        assert(serf.index(base_url.path_start as int) == 0x2Fu8);
        Self::rel_slash_carry(base_url, serf, entryser,
            scheme_type);
        // the wrap-up budget: the final length is bounded by the
        // entry plus the scan growth
        let n = serf.len() as int;
        let a = input_rem(&input).len() as int;
        assert((n) <= (entryser.len() as int) + 5 * a + 6);
        assert((entryser.len() as int) <= (bs.len() as int) + 1);
        assert((input_rem(&rem_path).len() as int) <= a);
        assert((n)
            + 6 * (input_rem(&rem_path).len() as int) + 12
            <= (bs.len() as int)
                + 16 * (rem0.len() as int) + 74);
    }
    self.with_query_and_fragment(
        scheme_type,
        base_url.scheme_end,
        base_url.username_end,
        base_url.host_start,
        base_url.host_end,
        base_url.host,
        base_url.port,
        base_url.path_start,
        rem_path,
    )
}

/// Origin Rust (parser.rs:703-823): fn parse_relative(mut self, input,
///   scheme_type, base_url) -> ParseResult<Url> -- the relative
/// resolution dispatch on the first remaining byte: the empty input
/// and the '?'/'#'-head copy arms (parser.rs:709-741), the
/// '/'-or-'\\' head through the slash arm (parser.rs:742-783, the
/// double-slash handoff or the fresh-path wrap), and the default
/// pop/merge arm (parser.rs:784-823, the base-merge over the popped
/// path region). Every head routes to a landed arm state; the
/// remaining input dogmas (the authority entry classes of the
/// double-slash routes, the merge purity face) ride the requires.
/// The debug assert on the empty serialization (parser.rs:707)
/// rides the requires; the error surface widens by the
/// double-slash states (EmptyHost/InvalidPort) with the '/'-head
/// cone.
pub exec fn parse_relative<'i>(
    &mut self,
    input: Input<'i>,
    scheme_type: SchemeType,
    base_url: &super::Url,
) -> (r: Result<super::Url, ParseError>)
    requires
        input_wf(&input),
        self.context == Context::UrlParser,
        old(self).serialization.view().len() == 0,
        base_url_face(base_url),
        (input_rem(&input).len() == 0
            || input_rem(&input).index(0) == 0x3Fu8
            || input_rem(&input).index(0) == 0x23u8
            || ((input_rem(&input).index(0) == 0x2Fu8
                    || input_rem(&input).index(0) == 0x5Cu8)
                && !super::cannot_be_a_base_view(base_url)
                && rel_slash_face(input_rem(&input), scheme_type))
            || ((input_rem(&input).len() as int) > 0
                    && (input_rem(&input).index(0) != 0x3Fu8
                        && input_rem(&input).index(0) != 0x23u8
                        && input_rem(&input).index(0) != 0x2Fu8
                        && input_rem(&input).index(0) != 0x5Cu8)
                && !super::cannot_be_a_base_view(base_url)
                && rel_merge_face(base_url, input_rem(&input)))),
        scheme_type
            == scheme_type_of(base_url.serialization.view()
                .subrange(0, base_url.scheme_end as int)),
        (base_url.serialization.view().len() as int)
            + 16 * (input_rem(&input).len() as int) + 74
            <= 0xFFFF_FFFF,
    ensures
        machine_domain(final(self).serialization.view()),
        (r.is_err() ==> (r == Err(ParseError::Overflow)
            || r == Err(ParseError::EmptyHost)
            || r == Err(ParseError::InvalidPort))),
        (r.is_ok() ==> super::url_invariant(&r.unwrap())),
{
    let (c0o, after_first) = input.split_first();
    match c0o {
        Option::None => {
            // the empty-input copy arm (parser.rs:709-721)
            proof {
                assert(input_rem(&input).len() == 0);
            }
            self.rel_none_arm(base_url)
        }
        Option::Some(c0) => {
            if c0 == 0x3Fu8 {
                // the '?' copy arm (parser.rs:722-740): the whole
                // input, head included, feeds the scan
                self.rel_query_arm(input, scheme_type, base_url)
            } else if c0 == 0x23u8 {
                // the '#' arm (parser.rs:741) delegates to the
                // fragment face (the byte is the cone's third value)
                proof {
                    assert(c0 == input_rem(&input).index(0));
                    assert(c0 == 0x23u8);
                }
                self.fragment_only(base_url, input)
            } else if c0 == 0x2Fu8 || c0 == 0x5Cu8 {
                // the '/' | '\\' arm (parser.rs:742-783)
                proof {
                    assert(c0 == input_rem(&input).index(0));
                    assert(c0 == 0x2Fu8 || c0 == 0x5Cu8);
                    assert(input_rem(&after_first)
                        == input_rem(&input).subrange(
                            1, input_rem(&input).len() as int));
                    assert(input_rem(&after_first).len() as int >= 0);
                    assert(!super::cannot_be_a_base_view(base_url));
                    assert(rel_slash_face(input_rem(&input),
                        scheme_type));
                }
                self.rel_slash_arm(input, after_first, scheme_type,
                    base_url)
            } else {
                // the default pop/merge arm (parser.rs:784-823)
                proof {
                    assert(c0 == input_rem(&input).index(0));
                    assert(c0 != 0x3Fu8 && c0 != 0x23u8);
                    assert(c0 != 0x2Fu8 && c0 != 0x5Cu8);
                    assert((input_rem(&input).len() as int) > 0);
                    assert(!super::cannot_be_a_base_view(base_url));
                    assert(rel_merge_face(base_url,
                        input_rem(&input)));
                }
                self.rel_merge_arm(input, scheme_type, base_url)
            }
        }
    }
}

}

/// The before-query boundary of the base (the copy length of the
/// '?' arm of parse_relative): `..query_start` when the query exists,
/// else `..fragment_start`, else the whole serialization
/// (parser.rs:726-733).
pub open spec fn base_before_query_len(b: &super::Url) -> int {
    if b.query_start.is_some() {
        b.query_start.unwrap() as int
    } else if b.fragment_start.is_some() {
        b.fragment_start.unwrap() as int
    } else {
        (b.serialization.view().len() as int)
    }
}

/// The authority-branch digest of the None-arm record carry: the copy
/// ends the record serialization exactly at the boundary k (nothing
/// is appended), so every component slot the authority branch reads
/// is a preserved base byte and the username_end match stays vacuous
/// at the serialization end.
pub proof fn rel_carry_none_authority(
    b: &super::Url,
    u: &super::Url,
    k: int,
)
    requires
        base_url_face(b),
        super::has_authority_view(b),
        k == base_before_len(b),
        (b.path_start as int) <= k,
        (u.serialization.view().len() as int) == k,
        (u.serialization.view().len() as int) <= 0xFFFF_FFFF,
        (u.scheme_end as int) == (b.scheme_end as int),
        (u.username_end as int) == (b.username_end as int),
        (u.host_start as int) == (b.host_start as int),
        (u.host_end as int) == (b.host_end as int),
        u.host == b.host,
        u.port == b.port,
        (u.path_start as int) == (b.path_start as int),
        u.query_start == b.query_start,
        u.fragment_start == Option::None,
        forall|j: int| 0 <= j && j < k
            ==> u.serialization.view().index(j)
                == b.serialization.view().index(j),
    ensures
        super::url_invariant(u),
{
    let bs = b.serialization.view();
    let s = u.serialization.view();
    let nb = bs.len() as int;
    let n = s.len() as int;
    let se = b.scheme_end as int;
    let ps = b.path_start as int;
    assert(n == k);
    // the boundary placement and the base's own byte there
    if b.fragment_start.is_some() {
        assert((b.fragment_start.unwrap() as int) == k && k < nb);
        assert(bs.index(k) == 0x23u8);
    } else {
        assert(k == nb);
    }
    // the scheme region sits fully below the boundary
    assert(s.subrange(0, se) == bs.subrange(0, se)) by {
        assert forall|j: int| 0 <= j && j < se
            implies s.subrange(0, se).index(j)
                == bs.subrange(0, se).index(j) by {
            vstd::seq::lemma_seq_subrange_index(s, 0, se, j);
            vstd::seq::lemma_seq_subrange_index(bs, 0, se, j);
            assert(s.index(j) == bs.index(j));
        }
        vstd::seq::lemma_seq_ext_equal(s.subrange(0, se),
            bs.subrange(0, se));
    }
    assert(scheme_type_of(s.subrange(0, se))
        == scheme_type_of(bs.subrange(0, se)));
    // the authority branch facts: se+3 <= every component offset to
    // path_start, the record's slashes are the base's own
    assert(se + 3 <= ps);
    assert(super::has_authority_view(u)) by {
        assert(s.index(se + 1) == 0x2Fu8
            && s.index(se + 2) == 0x2Fu8);
        assert(se + 3 <= n);
    }
    let he = u.host_end as int;
    // the port digit span rides the preserved prefix (the span only
    // exists when the region is a strict port region)
    if (he + 1) < ps {
        assert(s.subrange(he + 1, ps)
            == bs.subrange(he + 1, ps)) by {
            assert forall|j: int|
                #![trigger s.subrange(he + 1, ps).index(j)]
                0 <= j && j < (ps - (he + 1))
                implies s.subrange(he + 1, ps).index(j)
                    == bs.subrange(he + 1, ps).index(j) by {
                vstd::seq::lemma_seq_subrange_index(s, he + 1, ps, j);
                vstd::seq::lemma_seq_subrange_index(bs, he + 1, ps, j);
                assert(s.index(he + 1 + j) == bs.index(he + 1 + j));
            }
            vstd::seq::lemma_seq_ext_equal(s.subrange(he + 1, ps),
                bs.subrange(he + 1, ps));
        }
    }
    // the query slot rides the preserved prefix (below either
    // boundary value)
    if u.query_start.is_some() {
        let qs = u.query_start.unwrap() as int;
        if b.fragment_start.is_some() {
            assert(k == (b.fragment_start.unwrap() as int));
        } else {
            assert(qs < nb);
        }
        assert(bs.index(qs) == 0x3Fu8);
        assert(s.index(qs) == bs.index(qs));
    }
}

/// The anarchist-branch digest of the None-arm record carry: the copy
/// ends the record serialization exactly at k, the head bytes behind
/// the colon are all preserved base bytes, and the path region end is
/// the base's own (query first, else the fragment boundary or the
/// serialization end, all == k on this arm), so the base's
/// opacity/non-opacity carries to the record unchanged.
pub proof fn rel_carry_none_anarchist(
    b: &super::Url,
    u: &super::Url,
    k: int,
)
    requires
        base_url_face(b),
        !super::has_authority_view(b),
        k == base_before_len(b),
        (b.path_start as int) <= k,
        (u.serialization.view().len() as int) == k,
        (u.serialization.view().len() as int) <= 0xFFFF_FFFF,
        (u.scheme_end as int) == (b.scheme_end as int),
        (u.username_end as int) == (b.username_end as int),
        (u.host_start as int) == (b.host_start as int),
        (u.host_end as int) == (b.host_end as int),
        u.host == b.host,
        u.port == b.port,
        (u.path_start as int) == (b.path_start as int),
        u.query_start == b.query_start,
        u.fragment_start == Option::None,
        forall|j: int| 0 <= j && j < k
            ==> u.serialization.view().index(j)
                == b.serialization.view().index(j),
    ensures
        super::url_invariant(u),
{
    let bs = b.serialization.view();
    let s = u.serialization.view();
    let nb = bs.len() as int;
    let n = s.len() as int;
    let se = b.scheme_end as int;
    let ps = b.path_start as int;
    assert(n == k);
    // the boundary placement and the base's own byte there
    if b.fragment_start.is_some() {
        assert((b.fragment_start.unwrap() as int) == k && k < nb);
        assert(bs.index(k) == 0x23u8);
    } else {
        assert(k == nb);
    }
    // the record stays on the no-authority branch: either the record
    // ends before the two-byte '//'-guard window, or both head bytes
    // are the base's own (which fail the // pin)
    assert(!super::has_authority_view(u)) by {
        if se + 3 <= k {
            assert(s.index(se + 1) == bs.index(se + 1));
            assert(s.index(se + 2) == bs.index(se + 2));
            assert(!(bs.index(se + 1) == 0x2Fu8
                && bs.index(se + 2) == 0x2Fu8));
        } else {
            assert(se + 3 > n);
        }
    }
    if ps == se + 3 {
        // the opaque base: the '/','.' prefix and the '//'
        // path-head pins are the base's own bytes, and the record
        // can not end inside the pinned head (the base's region end
        // is at or past the head)
        assert(super::opaque_path_double_slash(b));
        assert(bs.index(se + 1) == 0x2Fu8
            && bs.index(se + 2) == 0x2Eu8);
        assert(bs.index(se + 3) == 0x2Fu8
            && bs.index(se + 4) == 0x2Fu8);
        assert(super::path_end_view(b) <= nb);
        // the base's own region end dominates the pinned head
        assert(super::path_end_view(b) >= se + 5);
        assert(k >= se + 5) by {
            if b.query_start.is_some() {
                // the query slot can not sit on a pinned head byte
                assert(bs.index((b.query_start.unwrap() as int))
                    == 0x3Fu8);
                if k == se + 3 { assert(false); }
                if k == se + 4 { assert(false); }
            } else if b.fragment_start.is_some() {
                // the fragment slot can not sit on a pinned head byte
                assert(bs.index((b.fragment_start.unwrap() as int))
                    == 0x23u8);
                if k == se + 3 { assert(false); }
                if k == se + 4 { assert(false); }
            }
            // no query, no fragment: the boundary is the region end
        }
        // the record keeps the pinned head bytes and the region end
        assert(s.index(se + 3) == 0x2Fu8
            && s.index(se + 4) == 0x2Fu8);
        if u.query_start.is_some() {
            let qs = u.query_start.unwrap() as int;
            assert(super::path_end_view(u) == qs);
            assert(bs.index(qs) == 0x3Fu8);
            if qs == se + 3 { assert(false); }
            if qs == se + 4 { assert(false); }
            assert(super::opaque_path_double_slash(u));
        } else {
            assert(super::path_end_view(u) == k);
            assert(super::opaque_path_double_slash(u));
        }
        assert(s.index(se + 1) == 0x2Fu8
            && s.index(se + 2) == 0x2Eu8);
    } else {
        // the plain anarchist base: path_start == se+1, the record's
        // region end equals the base's own, so the base's
        // non-opacity carries
        assert(ps == se + 1);
        assert(!super::opaque_path_double_slash(u)) by {
            let pendu = super::path_end_view(u);
            if u.query_start.is_some() {
                assert(pendu == (u.query_start.unwrap() as int));
                assert(super::path_end_view(b) == pendu);
            } else {
                assert(pendu == k);
                assert(super::path_end_view(b) == k);
            }
            if pendu >= se + 3 {
                assert(s.index(se + 1) == bs.index(se + 1));
                assert(s.index(se + 2) == bs.index(se + 2));
                assert(super::opaque_path_double_slash(u)
                    == super::opaque_path_double_slash(b));
                assert(!super::opaque_path_double_slash(b));
            }
        }
        assert((u.path_start as int) == se + 1);
    }
    // the query slot rides the preserved prefix
    if u.query_start.is_some() {
        let qs = u.query_start.unwrap() as int;
        if b.fragment_start.is_some() {
            assert(k == (b.fragment_start.unwrap() as int));
        } else {
            assert(qs < nb);
        }
        assert(bs.index(qs) == 0x3Fu8);
        assert(s.index(qs) == bs.index(qs));
    }
}

/// The authority-branch digest of the '?'-arm record carry: the copy
/// ends at the base's first query/fragment boundary k, the scan
/// appends the '?'-headed region, the record's query slot sits at the
/// boundary with the fragment slot strictly behind it (the scan's own
/// pins); every other component slot is a preserved base byte -- the
/// only touched slot (username_end == k) settles through the base's
/// own wildcard match arm, whose byte there is the base's boundary
/// marker ('?' or '#'), or the terminus conjunct at k == n.
pub proof fn rel_carry_query_authority(
    b: &super::Url,
    u: &super::Url,
    k: int,
)
    requires
        base_url_face(b),
        super::has_authority_view(b),
        k == base_before_query_len(b),
        (b.path_start as int) <= k,
        (u.serialization.view().len() as int) >= k + 1,
        (u.serialization.view().len() as int) <= 0xFFFF_FFFF,
        (u.scheme_end as int) == (b.scheme_end as int),
        (u.username_end as int) == (b.username_end as int),
        (u.host_start as int) == (b.host_start as int),
        (u.host_end as int) == (b.host_end as int),
        u.host == b.host,
        u.port == b.port,
        (u.path_start as int) == (b.path_start as int),
        u.query_start == Option::Some(k as u32),
        u.fragment_start.is_none()
            || ((u.fragment_start.unwrap() as int) > k
                && (u.fragment_start.unwrap() as int)
                    < (u.serialization.view().len() as int)
                && u.serialization.view().index(
                    u.fragment_start.unwrap() as int) == 0x23u8),
        forall|j: int| 0 <= j && j < k
            ==> u.serialization.view().index(j)
                == b.serialization.view().index(j),
        u.serialization.view().index(k) == 0x3Fu8,
    ensures
        super::url_invariant(u),
{
    let bs = b.serialization.view();
    let s = u.serialization.view();
    let nb = bs.len() as int;
    let n = s.len() as int;
    let se = b.scheme_end as int;
    let ps = b.path_start as int;
    let ue = u.username_end as int;
    let hs = u.host_start as int;
    let he = u.host_end as int;
    // the boundary placement: the base's own byte there is its query
    // or fragment marker, or the serialization end (the base's match
    // below reads one of those, never ':' or '@')
    if b.query_start.is_some() {
        assert(k == (b.query_start.unwrap() as int));
        assert(k < nb);
        assert(bs.index(k) == 0x3Fu8);
    } else if b.fragment_start.is_some() {
        assert(k == (b.fragment_start.unwrap() as int));
        assert(k < nb);
        assert(bs.index(k) == 0x23u8);
    } else {
        assert(k == nb);
    }
    assert(k < n);
    // the scheme region sits fully below the boundary
    assert(s.subrange(0, se) == bs.subrange(0, se)) by {
        assert forall|j: int| 0 <= j && j < se
            implies s.subrange(0, se).index(j)
                == bs.subrange(0, se).index(j) by {
            vstd::seq::lemma_seq_subrange_index(s, 0, se, j);
            vstd::seq::lemma_seq_subrange_index(bs, 0, se, j);
            assert(s.index(j) == bs.index(j));
        }
        vstd::seq::lemma_seq_ext_equal(s.subrange(0, se),
            bs.subrange(0, se));
    }
    assert(scheme_type_of(s.subrange(0, se))
        == scheme_type_of(bs.subrange(0, se)));
    // the authority branch facts: se+3 <= every component offset to
    // path_start, and the record's slashes are the base's own
    assert(se + 3 <= ps);
    assert(super::has_authority_view(u)) by {
        assert(s.index(se + 1) == 0x2Fu8
            && s.index(se + 2) == 0x2Fu8);
        assert(se + 3 <= n);
    }
    // the only component slot the scan can touch is username_end == k
    if ue == k {
        if k == nb {
            // the terminus conjunct of the base face
            assert(ue == se + 3);
        } else {
            // the base's own match on its boundary marker ('?' or
            // '#') settles the wildcard arm
            assert(bs.index(ue) != 0x3Au8
                && bs.index(ue) != 0x40u8);
            assert(ue == se + 3);
        }
    } else {
        assert(s.index(ue) == bs.index(ue));
    }
    // the port digit span rides the preserved prefix (the span only
    // exists when the region is a strict port region)
    if (he + 1) < ps {
        assert(s.subrange(he + 1, ps)
            == bs.subrange(he + 1, ps)) by {
            assert forall|j: int|
                #![trigger s.subrange(he + 1, ps).index(j)]
                0 <= j && j < (ps - (he + 1))
                implies s.subrange(he + 1, ps).index(j)
                    == bs.subrange(he + 1, ps).index(j) by {
                vstd::seq::lemma_seq_subrange_index(s, he + 1, ps, j);
                vstd::seq::lemma_seq_subrange_index(bs, he + 1, ps, j);
                assert(s.index(he + 1 + j) == bs.index(he + 1 + j));
            }
            vstd::seq::lemma_seq_ext_equal(s.subrange(he + 1, ps),
                bs.subrange(he + 1, ps));
        }
    }
    // the wrap slots: the '?' query slot at the boundary, the '#'
    // fragment slot strictly behind it (the scan's own pins are the
    // premises; the boundary dominates path_start)
    assert(u.query_start.is_some());
    assert((u.query_start.unwrap() as int) >= ps);
    assert(u.fragment_start.is_some()
        ==> ((u.fragment_start.unwrap() as int) > ps));
}

/// The anarchist-branch digest of the '?'-arm record carry: the base
/// holds no authority and the record keeps it (the '?' slot at the
/// boundary -- or a preserved base byte -- keeps one of the two bytes
/// behind the colon a non-slash); the record's region end is the
/// query slot at the boundary, which equals the base's own region
/// end, so the base's opacity/non-opacity carries to the record
/// unchanged (the opaque pins sit strictly below the boundary, whose
/// base marker can not collide with a pinned head byte).
pub proof fn rel_carry_query_anarchist(
    b: &super::Url,
    u: &super::Url,
    k: int,
)
    requires
        base_url_face(b),
        !super::has_authority_view(b),
        k == base_before_query_len(b),
        (b.path_start as int) <= k,
        (u.serialization.view().len() as int) >= k + 1,
        (u.serialization.view().len() as int) <= 0xFFFF_FFFF,
        (u.scheme_end as int) == (b.scheme_end as int),
        (u.username_end as int) == (b.username_end as int),
        (u.host_start as int) == (b.host_start as int),
        (u.host_end as int) == (b.host_end as int),
        u.host == b.host,
        u.port == b.port,
        (u.path_start as int) == (b.path_start as int),
        u.query_start == Option::Some(k as u32),
        u.fragment_start.is_none()
            || ((u.fragment_start.unwrap() as int) > k
                && (u.fragment_start.unwrap() as int)
                    < (u.serialization.view().len() as int)
                && u.serialization.view().index(
                    u.fragment_start.unwrap() as int) == 0x23u8),
        forall|j: int| 0 <= j && j < k
            ==> u.serialization.view().index(j)
                == b.serialization.view().index(j),
        u.serialization.view().index(k) == 0x3Fu8,
    ensures
        super::url_invariant(u),
{
    let bs = b.serialization.view();
    let s = u.serialization.view();
    let nb = bs.len() as int;
    let n = s.len() as int;
    let se = b.scheme_end as int;
    let ps = b.path_start as int;
    // the boundary placement: the base's own byte there is its query
    // or fragment marker, or the serialization end
    if b.query_start.is_some() {
        assert(k == (b.query_start.unwrap() as int));
        assert(k < nb);
        assert(bs.index(k) == 0x3Fu8);
    } else if b.fragment_start.is_some() {
        assert(k == (b.fragment_start.unwrap() as int));
        assert(k < nb);
        assert(bs.index(k) == 0x23u8);
    } else {
        assert(k == nb);
    }
    // the record stays on the no-authority branch: the '?' slot at
    // the boundary -- or the preserved base pair -- fails the '//'
    // pin. The boundary dominates path_start, which on this branch is
    // se+1 or se+3, so se+1 is preserved whenever the record reads it
    assert(!super::has_authority_view(u)) by {
        if k == se + 1 {
            assert(s.index(se + 1) == 0x3Fu8);
            assert(s.index(se + 1) != 0x2Fu8);
        } else if k == se + 2 {
            assert(s.index(se + 2) == 0x3Fu8);
            assert(s.index(se + 2) != 0x2Fu8);
        } else {
            assert(k >= se + 3);
            assert(s.index(se + 1) == bs.index(se + 1));
            assert(s.index(se + 2) == bs.index(se + 2));
            assert(!(bs.index(se + 1) == 0x2Fu8
                && bs.index(se + 2) == 0x2Fu8));
        }
    }
    if ps == se + 3 {
        // the opaque base: the '/','.' prefix and the '//'
        // path-head pins are the base's own bytes; the boundary
        // (the base's region end) dominates the pinned head -- the
        // base markers '? '/' can not collide with the pinned bytes
        assert(super::opaque_path_double_slash(b));
        assert(bs.index(se + 1) == 0x2Fu8
            && bs.index(se + 2) == 0x2Eu8);
        assert(bs.index(se + 3) == 0x2Fu8
            && bs.index(se + 4) == 0x2Fu8);
        assert(k >= se + 5) by {
            if k == se + 3 {
                if b.query_start.is_some() {
                    assert(bs.index(se + 3) == 0x3Fu8);
                    assert(false);
                } else if b.fragment_start.is_some() {
                    assert(bs.index(se + 3) == 0x23u8);
                    assert(false);
                } else {
                    assert(k == nb);
                    assert(super::path_end_view(b) <= nb);
                    assert(super::path_end_view(b) >= se + 5);
                    assert(false);
                }
            } else if k == se + 4 {
                if b.query_start.is_some() {
                    assert(bs.index(se + 4) == 0x3Fu8);
                    assert(false);
                } else if b.fragment_start.is_some() {
                    assert(bs.index(se + 4) == 0x23u8);
                    assert(false);
                } else {
                    assert(k == nb);
                    assert(super::path_end_view(b) <= nb);
                    assert(super::path_end_view(b) >= se + 5);
                    assert(false);
                }
            }
        }
        // the record keeps the pinned head bytes below the boundary
        assert(s.index(se + 3) == 0x2Fu8
            && s.index(se + 4) == 0x2Fu8);
        // the record's region end is the query slot at the boundary
        assert(super::path_end_view(u) == k);
        assert(super::opaque_path_double_slash(u));
        assert(s.index(se + 1) == 0x2Fu8
            && s.index(se + 2) == 0x2Eu8);
    } else {
        // the plain anarchist base: path_start == se+1; the record's
        // region end (the query slot at the boundary) equals the
        // base's own region end, so the non-opacity carries (below
        // the boundary the head bytes are the base's own, and the
        // base's anarchist pair never holds two slashes)
        assert(ps == se + 1);
        assert(!super::opaque_path_double_slash(u)) by {
            // the record's region end equals the base's own
            if b.query_start.is_some() {
                assert(super::path_end_view(b) == k);
            } else if b.fragment_start.is_some() {
                assert(super::path_end_view(b) == k);
            } else {
                assert(super::path_end_view(b) == nb);
                assert(k == nb);
            }
            if k <= se + 2 {
                // the region ends before the two head bytes exist
                assert(k < (se + 1) + 2);
            } else {
                // both head bytes are preserved base bytes: the
                // base's own anarchist conjunct (no slashes at
                // se+1/se+2 pair on a boundary >= se+3) carries
                assert(se + 1 < k);
                assert(se + 2 < k);
                assert(s.index(se + 1) == bs.index(se + 1));
                assert(s.index(se + 2) == bs.index(se + 2));
                assert(super::opaque_path_double_slash(u)
                    == super::opaque_path_double_slash(b));
                assert(!super::opaque_path_double_slash(b));
            }
        }
        assert((u.path_start as int) == se + 1);
    }
    // the wrap slots: the fragment pin rides the premise (the '#'
    // byte strictly behind the query slot), the ordering follows
    if u.fragment_start.is_some() {
        assert((u.fragment_start.unwrap() as int)
            > (u.query_start.unwrap() as int));
    }
    assert((u.query_start.unwrap() as int) >= ps);
    assert(u.fragment_start.is_some()
        ==> ((u.fragment_start.unwrap() as int) > ps));

}

/* ============================================================
 * The set_query drop-step carry (Origin: the "remove any previous
 * query" truncate of the set_query write face, lib.rs:1642-1644):
 * the record drops its '?' slot (query_start set to None) with the
 * serialization cut exactly at the old query boundary k, every
 * other component kept. Below the cut every component pin the
 * invariant reads is a preserved base byte; the only slot that can
 * sit exactly at the cut boundary is username_end == k, where the
 * base's own '?' marker byte settles the wildcard arm of the base
 * record. The empty query/fragment slots make the wrap conjuncts
 * vacuous, so the digest is the two record branches alone.
 * ============================================================ */

/// The record carry of the query-drop step of set_query (also the
/// digest of the intermediate take-fragment state composed the same
/// way): b carries a query at the boundary k, u is the record whose
/// serialization ends exactly at k with both the query and the
/// fragment slots empty and every component field copied from b.
pub proof fn set_query_drop_carry(
    b: &super::Url,
    u: &super::Url,
    k: int,
)
    requires
        super::url_invariant(b),
        b.query_start.is_some(),
        k == (b.query_start.unwrap() as int),
        (b.path_start as int) <= k,
        (u.serialization.view().len() as int) == k,
        (k as int) <= 0xFFFF_FFFF,
        (u.scheme_end as int) == (b.scheme_end as int),
        (u.username_end as int) == (b.username_end as int),
        (u.host_start as int) == (b.host_start as int),
        (u.host_end as int) == (b.host_end as int),
        u.host == b.host,
        u.port == b.port,
        (u.path_start as int) == (b.path_start as int),
        u.query_start.is_none(),
        u.fragment_start.is_none(),
        forall|j: int| 0 <= j && j < k
            ==> u.serialization.view().index(j)
                == b.serialization.view().index(j),
    ensures
        super::url_invariant(u),
{
    let bs = b.serialization.view();
    let s = u.serialization.view();
    let nb = bs.len() as int;
    let n = s.len() as int;
    let se = b.scheme_end as int;
    let ue = b.username_end as int;
    let hs = b.host_start as int;
    let he = b.host_end as int;
    let ps = b.path_start as int;
    assert(n == k);
    assert(k < nb);
    assert(bs.index(k) == 0x3Fu8);
    // the scheme region sits fully below the cut
    assert(s.subrange(0, se) == bs.subrange(0, se)) by {
        assert forall|j: int| 0 <= j && j < se
            implies s.subrange(0, se).index(j)
                == bs.subrange(0, se).index(j) by {
            vstd::seq::lemma_seq_subrange_index(s, 0, se, j);
            vstd::seq::lemma_seq_subrange_index(bs, 0, se, j);
            assert(s.index(j) == bs.index(j));
        }
        vstd::seq::lemma_seq_ext_equal(s.subrange(0, se),
            bs.subrange(0, se));
    }
    assert(scheme_type_of(s.subrange(0, se))
        == scheme_type_of(bs.subrange(0, se)));
    if super::has_authority_view(b) {
        // the authority survives the cut: both slashes sit strictly
        // below every userinfo offset, hence below k
        assert(se + 3 <= ue);
        assert(se + 2 < k);
        assert(super::has_authority_view(u)) by {
            assert(s.index(se + 1) == bs.index(se + 1));
            assert(s.index(se + 2) == bs.index(se + 2));
            assert(se + 3 <= n);
        }
        // the userinfo match arm: the byte survives below the cut,
        // or the cut lands on the base's own '?' marker byte
        if ue == k {
            assert(bs.index(ue) == 0x3Fu8);
            assert(bs.index(ue) != 0x3Au8);
            assert(bs.index(ue) != 0x40u8);
            assert(ue == se + 3);
        } else {
            assert(ue < k);
            assert(s.index(ue) == bs.index(ue));
            if bs.index(ue) == 0x3Au8 {
                assert(hs >= ue + 2);
                assert(hs - 1 < k);
                assert(s.index(hs - 1) == bs.index(hs - 1));
                assert(s.index(hs - 1) == 0x40u8);
            } else if bs.index(ue) == 0x40u8 {
                assert(hs == ue + 1);
            } else {
                assert(ue == se + 3);
            }
        }
        // the region ordering and the tag ride the component copy
        assert(ue <= hs);
        assert(hs <= he);
        assert(he <= ps);
        assert(ps <= n);
        assert((u.host == super::HostInternal::None)
            == ((u.host_start as int) == (u.host_end as int)));
        // the port region: the byte pins below the cut are preserved
        if ps == he {
            assert(u.port.is_none());
        } else {
            assert(he < ps);
            assert(he < k);
            assert(s.index(he) == bs.index(he));
            assert(s.index(he) == 0x3Au8);
            assert(he + 2 <= ps);
            assert(s.subrange(he + 1, ps)
                == bs.subrange(he + 1, ps)) by {
                assert forall|j: int|
                    #![trigger s.subrange(he + 1, ps).index(j)]
                    0 <= j && j < ps - (he + 1)
                    implies s.subrange(he + 1, ps).index(j)
                        == bs.subrange(he + 1, ps).index(j) by {
                    vstd::seq::lemma_seq_subrange_index(s, he + 1, ps, j);
                    vstd::seq::lemma_seq_subrange_index(bs, he + 1, ps, j);
                    assert(s.index(he + 1 + j) == bs.index(he + 1 + j));
                }
                vstd::seq::lemma_seq_ext_equal(
                    s.subrange(he + 1, ps),
                    bs.subrange(he + 1, ps));
            }
            assert(u.port.is_some());
            assert((u.port.unwrap() as int)
                == super::dec_val(s.subrange(he + 1, ps)));
        }
        // the path anchor byte below the cut is the base's own
        if ps < n {
            assert(s.index(ps) == bs.index(ps));
            assert(s.index(ps) == 0x2Fu8
                || s.index(ps) == 0x23u8
                || s.index(ps) == 0x3Fu8);
        }
    } else {
        // the anarchist record: the cut keeps the no-authority
        // branch (both slashes of a surviving window would be base
        // bytes, and the base never pairs them; a region that ends
        // before the window cannot pair them either)
        assert(!super::has_authority_view(u)) by {
            if se + 3 <= n {
                assert(s.index(se + 1) == bs.index(se + 1));
                assert(s.index(se + 2) == bs.index(se + 2));
                assert(!(bs.index(se + 1) == 0x2Fu8
                    && bs.index(se + 2) == 0x2Fu8));
            }
        }
        assert((u.username_end as int) == se + 1);
        assert((u.host_start as int) == se + 1);
        assert((u.host_end as int) == se + 1);
        assert(u.host == super::HostInternal::None);
        assert(u.port.is_none());
        if ps == se + 3 {
            // the opaque-pinned anarchist: the '/','.' prefix and
            // the pinned path head are all strictly below the cut
            assert(super::opaque_path_double_slash(b));
            assert(bs.index(se + 1) == 0x2Fu8);
            assert(bs.index(se + 2) == 0x2Eu8);
            assert(super::path_end_view(b) == k) by {
                assert(b.query_start.is_some());
            }
            assert(ps + 2 <= k);
            assert(se + 4 < k);
            assert(s.index(se + 1) == 0x2Fu8);
            assert(s.index(se + 2) == 0x2Eu8);
            assert(s.index(ps) == 0x2Fu8);
            assert(s.index(ps + 1) == 0x2Fu8);
            assert(super::path_end_view(u) == n);
            assert(super::opaque_path_double_slash(u));
            assert((u.path_start as int) == se + 3);
        } else {
            // the plain anarchist: the base's own non-opacity of the
            // same region window carries (its end here is the cut
            // itself)
            assert(ps == se + 1);
            assert(!super::opaque_path_double_slash(b));
            assert(super::path_end_view(b) == k) by {
                assert(b.query_start.is_some());
            }
            assert(super::path_end_view(u) == n);
            assert(!super::opaque_path_double_slash(u)) by {
                if ps + 2 <= n {
                    assert(s.index(ps) == bs.index(ps));
                    assert(s.index(ps + 1) == bs.index(ps + 1));
                    assert(!(bs.index(ps) == 0x2Fu8
                        && bs.index(ps + 1) == 0x2Fu8));
                } else {
                    assert(ps + 2 > n);
                }
            }
            assert((u.path_start as int) == se + 1);
        }
    }
}

}
