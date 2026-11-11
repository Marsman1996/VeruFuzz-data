//! data-url 0.3.2 @ servo/rust-url 00a6ce58
//! Upstream source: data-url/src/mime.rs (pin tree code/data-url/src/mime.rs).
//! This file mirrors that upstream module, src zone (the library code proper).
//! Sections: A the spec model of the MIME Sniffing parse / serialize semantics;
//!   B the exec transcription (an Origin Rust note marks every divergence);
//!   C the fmt::Display serializer face. The in-file upstream UT
//!   (`test_basic_mime`, mime.rs:225-239) is transcribed as assertion theorems
//!   in verified/harness/ut_mime.rs.
//! Carrier note: upstream `Mime` fields are String / Vec<(String, String)>;
//! String has no vstd spec, so the carrier is byte payloads Vec<u8> with
//! Seq<u8> spec views. The Display-for-Mime face (fmt::Write has no vstd
//! spec) is carried by the byte serializer `serialize_bytes`.
//! Structural note: the piece iterators of upstream parse (`s.split(';')`
//! plus the quote-driven piece-consumption sub-machine, mime.rs:91-150) are
//! modeled as one position-advancing stage scan: a piece boundary is exactly
//! a ';' byte, and a backslash escaping a boundary, or a boundary crossed by
//! an unterminated quote scan, all coincide byte-wise with the upstream
//! iterator decisions (the ';' is content in each of those cases and the scan
//! resumes right after it), so the stage scan makes the same decisions with
//! all bounds syntactic.
//! Domain narrowing: inputs are ASCII (all bytes < 0x80). The char-based
//! upstream faces (trim over chars, the quoted-value `.chars()` scans,
//! valid_value's U+0080..U+00FF range) coincide with the byte face on that
//! domain; the narrowing only restricts the declared domain and never widens
//! a contract.

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

// ================= Section A: spec model =================

/// Origin Rust: fn http_whitespace(c: char) -> bool
///     { matches!(c, ' ' | '\t' | '\n' | '\r') }  (mime.rs:190-192)
pub open spec fn http_ws(b: u8) -> bool {
    b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D
}

/// One-byte face of str::to_ascii_lowercase (mime.rs:79, 81, 147).
pub open spec fn to_lower(b: u8) -> u8 {
    if b >= 0x41 && b <= 0x5A { (b + 0x20) as u8 } else { b }
}

/// The IS_HTTP_TOKEN byte map (mime.rs:206-223, copied in upstream from
/// hyperium/mime v0.3.5 parse.rs#L293) folded into a classifier: RFC 7230 tchar.
pub open spec fn token_byte(b: u8) -> bool {
    (b >= 0x41 && b <= 0x5A) || (b >= 0x61 && b <= 0x7A) || (b >= 0x30 && b <= 0x39)
        || b == 0x21 || b == 0x23 || b == 0x24 || b == 0x25 || b == 0x26 || b == 0x27
        || b == 0x2A || b == 0x2B || b == 0x2D || b == 0x2E || b == 0x5E || b == 0x5F
        || b == 0x60 || b == 0x7C || b == 0x7E
}

/// Origin Rust: fn valid_value(s: &str) -> bool (mime.rs:156-161), one-byte arm;
/// the U+0080..U+00FF range is unreachable on the declared ASCII domain.
pub open spec fn valid_value_byte(b: u8) -> bool {
    b == 0x09 || (b >= 0x20 && b <= 0x7E)
}

/// Whole-range token check over s[a..i) (the `.bytes().all` face of
/// only_http_token_code_points, mime.rs:194-196).
pub open spec fn all_token(s: Seq<u8>, a: int, i: int) -> bool
    decreases i - a
{
    if i <= a { true } else { token_byte(s[i - 1]) && all_token(s, a, i - 1) }
}

/// Whole-range valid-value check over s[a..i) (mime.rs:156-161).
pub open spec fn all_valid(s: Seq<u8>, a: int, i: int) -> bool
    decreases i - a
{
    if i <= a { true } else { valid_value_byte(s[i - 1]) && all_valid(s, a, i - 1) }
}

/// Validity of the RAW quoted value (mime.rs:133): the slice after the '='
/// through the end of its piece, i.e. up to the first ';' at or after a.
pub open spec fn valid_upto(s: Seq<u8>, j: int, b0: int) -> bool
    decreases b0 - j
{
    if j >= b0 { true } else if s[j] == 0x3B { true } else {
        valid_value_byte(s[j]) && valid_upto(s, j + 1, b0)
    }
}

/// s[a..b) as an owned Seq (the byte face of a &str slice).
pub open spec fn slice_seq(s: Seq<u8>, a: int, b: int) -> Seq<u8> {
    Seq::new((b - a) as nat, |j: int| s[a + j])
}

/// Origin Rust: s[a..b).to_ascii_lowercase() (mime.rs:79-81, 147).
pub open spec fn lower_span(s: Seq<u8>, a: int, i: int) -> Seq<u8>
    decreases i - a
{
    if i <= a { Seq::empty() } else { lower_span(s, a, i - 1) + seq![to_lower(s[i - 1])] }
}

/// Origin Rust: str::trim_matches(http_whitespace), forward arm (mime.rs:64, 95).
pub open spec fn ltrim(s: Seq<u8>, i: int, b: int) -> int
    decreases b - i
{
    if i < b && http_ws(s[i]) { ltrim(s, i + 1, b) } else { i }
}

/// str::trim_end_matches(http_whitespace) over s[a..i) (mime.rs:70, 138).
pub open spec fn rtrim(s: Seq<u8>, a: int, i: int) -> int
    decreases i - a
{
    if a < i && http_ws(s[i - 1]) { rtrim(s, a, i - 1) } else { i }
}

/// First index in [i, b) holding t; b when none (splitn(2, sep) scan face).
pub open spec fn find_byte(s: Seq<u8>, i: int, b: int, t: u8) -> int
    decreases b - i
{
    if i >= b { b } else if s[i] == t { i } else { find_byte(s, i + 1, b, t) }
}

/// Origin Rust: fn contains(parameters, name) -> bool (mime.rs:152-154).
/// The stored names are the already-lowercased ones (mime.rs:147); the query
/// is the raw piece, so the comparison is raw-vs-lower, as upstream.
pub open spec fn has_name(acc: Seq<(Seq<u8>, Seq<u8>)>, name: Seq<u8>, i: int) -> bool
    decreases acc.len() - i
{
    if i >= acc.len() { false } else { acc[i].0 == name || has_name(acc, name, i + 1) }
}

/// >= 0 conversion of an exec usize stage state (4294967295 is the -1 sentinel
/// of the piece-scan state machine).
pub open spec fn sent(x: usize) -> int {
    if x == 4294967295 { -1 } else { x as int }
}

/// First index in params whose name matches (the get_parameter scan face).
pub open spec fn find_param(params: Seq<(Seq<u8>, Seq<u8>)>, name: Seq<u8>, i: int) -> int
    decreases params.len() - i
{
    if i >= params.len() { -1 } else if params[i].0 == name { i } else { find_param(params, name, i + 1) }
}

/// Spec view of the exec parameter list.
pub open spec fn params_view(v: &Vec<(Vec<u8>, Vec<u8>)>) -> Seq<(Seq<u8>, Seq<u8>)> {
    Seq::new(v.len() as nat, |i: int| (v[i].0@, v[i].1@))
}

/// The unquoted-value push decision (mime.rs:137-146): right-trimmed value
/// kept when non-empty, all valid, and the name is a fresh non-empty token.
pub open spec fn unq_push(
    s: Seq<u8>,
    ns: int,
    eq: int,
    cel: int,
    acc: Seq<(Seq<u8>, Seq<u8>)>,
) -> Seq<(Seq<u8>, Seq<u8>)> {
    if ns < eq && eq + 1 < cel && all_token(s, ns, eq)
        && !has_name(acc, slice_seq(s, ns, eq), 0)
        && all_valid(s, eq + 1, cel)
    {
        let name = lower_span(s, ns, eq);
        acc + seq![(name, slice_seq(s, eq + 1, cel))]
    } else {
        acc
    }
}

/// The parameter-collection machine (mime.rs:91-150) as a position-advancing
/// stage scan over s[pos..b0):
/// - stage 0 (ns == -1): piece entry; skip HTTP whitespace, ';' ends an empty
///   piece, '=' opens an (invalid, empty-named) value, any other byte opens a
///   name at that position;
/// - stage 1 (ns set, eq == -1): name scan; ';' ends the piece with no push,
///   '=' opens the value at eq = pos, value scan starts at pos+1;
/// - stage 2 (eq set): unquoted value scan; its FIRST byte being '"'
///   switches to the quoted scan; ';' finalizes the trimmed value push via
///   unq_push; other bytes accumulate, advancing cel only for non-whitespace
///   (the trim_end_matches face);
/// - stage 4: the quoted-value scan (the backslash/piece-crossing machine of
///   mime.rs:106-132): '"' closes (push decided by the RAW value validity,
///   valid_upto through the piece end, then discard the rest of that piece),
///   '\' escapes its successor byte (the piece separator when the successor
///   is ';', the backslash itself at end of input), other bytes and piece
///   boundaries crossed unterminated contribute ';' as content, all into
///   qval; on input exhaustion the accumulated qval is pushed subject to the
///   same raw validity (mime.rs:133-136);
/// - stage 3: discard the remainder of the piece that contained the closing
///   quote (mime.rs:101-106: the value scan consumed those pieces), up to
///   and including its ';'.
/// Faithful points: the value-validity predicate of the quoted form applies
/// to the RAW value (quote included, through the piece end), parameters are
/// pushed even when the quote never closes, the unquoted form must be
/// non-empty after right-trimming, and duplicate detection compares the raw
/// name against the stored (lowercased) names.
pub open spec fn params_spec(
    s: Seq<u8>,
    pos: int,
    b0: int,
    ns: int,
    eq: int,
    cel: int,
    stage: int,
    qval: Seq<u8>,
    acc: Seq<(Seq<u8>, Seq<u8>)>,
) -> Seq<(Seq<u8>, Seq<u8>)>
    recommends
        0 <= pos <= b0 <= s.len()
        && (stage == 0 || stage == 1 || stage == 2 || stage == 3 || stage == 4)
        && (stage != 1 || ns >= 0)
        && (stage != 2
            || (ns >= 0 && eq >= 0 && ns <= eq && eq < pos && eq + 1 <= cel && cel <= pos))
        && (stage != 4 || (ns >= 0 && eq >= 0 && ns <= eq && eq < pos))
        && (stage != 0 && stage != 3 || (ns == -1 && eq == -1 && cel == -1))
    decreases b0 - pos
{
    if pos >= b0 {
        if stage == 2 {
            // value raw-ended at b0: finalize like the ';' arm
            unq_push(s, ns, eq, cel, acc)
        } else if stage == 4 {
            // unterminated quote scan consumed everything: the accumulated
            // value is pushed subject to the raw-value validity
            if ns < eq && all_token(s, ns, eq)
                && !has_name(acc, slice_seq(s, ns, eq), 0)
                && valid_upto(s, eq + 1, b0)
            {
                acc + seq![(lower_span(s, ns, eq), qval)]
            } else {
                acc
            }
        } else {
            acc
        }
    } else if stage == 3 {
        if s[pos] == 0x3B {
            params_spec(s, pos + 1, b0, -1, -1, -1, 0, Seq::empty(), acc)
        } else {
            params_spec(s, pos + 1, b0, -1, -1, -1, 3, Seq::empty(), acc)
        }
    } else if stage == 4 {
        if s[pos] == 0x22 {
            // closed: the raw-value push, then skip the rest of this piece
            let nm = ns < eq && all_token(s, ns, eq)
                && !has_name(acc, slice_seq(s, ns, eq), 0);
            let acc1 = if nm && valid_upto(s, eq + 1, b0) {
                acc + seq![(lower_span(s, ns, eq), qval)]
            } else {
                acc
            };
            params_spec(s, pos + 1, b0, -1, -1, -1, 3, Seq::empty(), acc1)
        } else if s[pos] == 0x5C {
            if pos + 1 >= b0 {
                // .unwrap_or('\\') (mime.rs:120): the backslash itself, at end
                params_spec(s, pos + 1, b0, ns, eq, -1, 4, qval + seq![0x5C], acc)
            } else {
                // the escaped successor byte (';' included, mime.rs:110-119)
                params_spec(s, pos + 2, b0, ns, eq, -1, 4, qval + seq![s[pos + 1]], acc)
            }
        } else {
            params_spec(s, pos + 1, b0, ns, eq, -1, 4, qval + seq![s[pos]], acc)
        }
    } else if stage == 2 {
        if pos == eq + 1 && s[pos] == 0x22 {
            // the quoted-value form (mime.rs:102)
            params_spec(s, pos + 1, b0, ns, eq, -1, 4, Seq::empty(), acc)
        } else if s[pos] == 0x3B {
            let acc1 = unq_push(s, ns, eq, cel, acc);
            params_spec(s, pos + 1, b0, -1, -1, -1, 0, Seq::empty(), acc1)
        } else {
            let cel2 = if http_ws(s[pos]) { cel } else { pos + 1 };
            params_spec(s, pos + 1, b0, ns, eq, cel2, 2, Seq::empty(), acc)
        }
    } else if stage == 1 {
        if s[pos] == 0x3B {
            // no '=' in this piece: nothing pushed (mime.rs:101-107)
            params_spec(s, pos + 1, b0, -1, -1, -1, 0, Seq::empty(), acc)
        } else if s[pos] == 0x3D {
            params_spec(s, pos + 1, b0, ns, pos, pos + 1, 2, Seq::empty(), acc)
        } else {
            params_spec(s, pos + 1, b0, ns, -1, -1, 1, Seq::empty(), acc)
        }
    } else {
        // stage 0: piece entry
        if s[pos] == 0x3B {
            params_spec(s, pos + 1, b0, -1, -1, -1, 0, Seq::empty(), acc)
        } else if http_ws(s[pos]) {
            // require!: piece leading HTTP whitespace (mime.rs:95)
            params_spec(s, pos + 1, b0, -1, -1, -1, 0, Seq::empty(), acc)
        } else if s[pos] == 0x3D {
            // '=' with an empty name (name_valid fails downstream, staged as
            // a value anyway: the quoted form may still consume pieces)
            params_spec(s, pos + 1, b0, pos, pos, pos + 1, 2, Seq::empty(), acc)
        } else {
            params_spec(s, pos + 1, b0, pos, -1, -1, 1, Seq::empty(), acc)
        }
    }
}

/// The whole-model spec of `parse` / `FromStr` (mime.rs:55-83):
/// Some((type, subtype, parameters)) or None.
pub open spec fn mime_parse_spec(
    s: Seq<u8>,
) -> Option<(Seq<u8>, Seq<u8>, Seq<(Seq<u8>, Seq<u8>)>)>
    decreases s.len() as int
{
    let a0 = ltrim(s, 0, s.len() as int);
    let b0 = rtrim(s, a0, s.len() as int);
    let sl = find_byte(s, a0, b0, 0x2F);
    if sl == b0 {
        // split2's rest face is None (no '/'): parse fails (mime.rs:66-69)
        None
    } else if a0 == sl || !all_token(s, a0, sl) {
        None
    } else {
        let semi = find_byte(s, sl + 1, b0, 0x3B);
        let sube = if semi == b0 { b0 } else { semi };
        let sub = rtrim(s, sl + 1, sube);
        if sl + 1 == sub || !all_token(s, sl + 1, sub) {
            None
        } else {
            let params = if semi < b0 {
                params_spec(s, semi + 1, b0, -1, -1, -1, 0, Seq::empty(), Seq::empty())
            } else {
                Seq::empty()
            };
            Some((lower_span(s, a0, sl), lower_span(s, sl + 1, sub), params))
        }
    }
}

/// Serialization of one parameter value (the fmt::Display arm, mime.rs:173-184):
/// raw when all-token and non-empty, else quoted with '\' escaping.
pub open spec fn ser_value(v: Seq<u8>) -> Seq<u8> {
    if v.len() > 0 && all_token(v, 0, v.len() as int) {
        v
    } else {
        seq![0x22] + ser_escape(v, v.len() as int) + seq![0x22]
    }
}

pub open spec fn ser_escape(v: Seq<u8>, i: int) -> Seq<u8>
    decreases i
{
    if i <= 0 {
        Seq::empty()
    } else {
        let c = v[i - 1];
        ser_escape(v, i - 1)
            + (if c == 0x22 || c == 0x5C { seq![0x5C, c] } else { seq![c] })
    }
}

/// The fmt::Display face of Mime (mime.rs:164-188), parameter fold.
pub open spec fn ser_params(params: Seq<(Seq<u8>, Seq<u8>)>, i: int) -> Seq<u8>
    decreases params.len() - i
{
    if i >= params.len() {
        Seq::empty()
    } else {
        let p = params[i];
        seq![0x3B] + p.0 + seq![0x3D] + ser_value(p.1) + ser_params(params, i + 1)
    }
}

/// The full serialization: type '/' subtype (';' name '=' value)*.
pub open spec fn ser_mime(m: (Seq<u8>, Seq<u8>, Seq<(Seq<u8>, Seq<u8>)>)) -> Seq<u8> {
    m.0 + seq![0x2F] + m.1 + ser_params(m.2, 0)
}

/// Spec view of the carrier triple (the byte face of the Mime fields).
pub open spec fn mime_view_of(m: &Mime) -> (Seq<u8>, Seq<u8>, Seq<(Seq<u8>, Seq<u8>)>) {
    (m.type_@, m.subtype@, params_view(&m.parameters))
}

// ================= Section B: exec transcription =================

/// Upstream doc (mime.rs:5-11):
///   <https://mimesniff.spec.whatwg.org/#mime-type-representation>
/// (upstream derives Clone, Debug, PartialEq, Eq at mime.rs:6; the Debug /
/// Eq faces are outside the verifier zone, the data clone is kept).
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone)]
pub struct Mime {
    pub type_: Vec<u8>,
    pub subtype: Vec<u8>,
    /// (name, value)
    pub parameters: Vec<(Vec<u8>, Vec<u8>)>,
}

/// Origin Rust: pub struct MimeParsingError(())  (mime.rs:42-43); the unit-field
/// tuple struct is outside verus and carried as the unit struct. The Display /
/// Error impls (mime.rs:45-52) are unverified faces (fmt has no vstd spec).
pub struct MimeParsingError;

/// Origin Rust: fn http_whitespace(c: char) (mime.rs:190-192), byte face.
pub exec fn http_ws_exec(b: u8) -> (r: bool)
    ensures
        r == http_ws(b),
{
    b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D
}

/// Origin Rust: fn only_http_token_code_points(s: &str) -> bool
/// (mime.rs:194-196), single-byte classifier of the IS_HTTP_TOKEN map
/// (mime.rs:206-223): the map is pure data and decoding it via a universal
/// table lookup is not tractable for the solver; this folded classifier
/// computes identical values by construction.
pub exec fn is_token(c: u8) -> (r: bool)
    ensures
        r == token_byte(c),
{
    (c >= 0x41 && c <= 0x5A) || (c >= 0x61 && c <= 0x7A) || (c >= 0x30 && c <= 0x39)
        || c == 0x21 || c == 0x23 || c == 0x24 || c == 0x25 || c == 0x26 || c == 0x27
        || c == 0x2A || c == 0x2B || c == 0x2D || c == 0x2E || c == 0x5E || c == 0x5F
        || c == 0x60 || c == 0x7C || c == 0x7E
}

/// exec face of str::to_ascii_lowercase per byte (mime.rs:79, 81, 147).
pub exec fn to_lower_exec(b: u8) -> (r: u8)
    ensures
        r == to_lower(b),
{
    if b >= 0x41 && b <= 0x5A { b + 0x20 } else { b }
}

/// Origin Rust: only_http_token_code_points over [a, i) (mime.rs:194-196).
pub exec fn all_token_exec(s: &[u8], a: usize, i: usize) -> (r: bool)
    requires
        a <= i <= s.len(),
    ensures
        r == all_token(s@, a as int, i as int),
    decreases i - a,
{
    if i == a {
        true
    } else {
        let prev = all_token_exec(s, a, i - 1);
        prev && is_token(s[i - 1])
    }
}

/// Origin Rust: fn valid_value(s: &str) -> bool (mime.rs:156-161) over [a, i).
pub exec fn all_valid_exec(s: &[u8], a: usize, i: usize) -> (r: bool)
    requires
        a <= i <= s.len(),
    ensures
        r == all_valid(s@, a as int, i as int),
    decreases i - a,
{
    if i == a {
        true
    } else {
        let prev = all_valid_exec(s, a, i - 1);
        prev && (s[i - 1] == 0x09 || (s[i - 1] >= 0x20 && s[i - 1] <= 0x7E))
    }
}

/// exec face of valid_upto (the raw quoted-value validity through the piece).
pub exec fn valid_upto_exec(s: &[u8], j: usize, b0: usize) -> (r: bool)
    requires
        j <= b0 <= s.len(),
    ensures
        r == valid_upto(s@, j as int, b0 as int),
    decreases b0 - j,
{
    if j >= b0 {
        true
    } else if s[j] == 0x3B {
        true
    } else {
        let b = s[j];
        valid_upto_exec(s, j + 1, b0)
            && (b == 0x09 || (b >= 0x20 && b <= 0x7E))
    }
}

/// exec face of s[a..b).to_ascii_lowercase().
pub exec fn lower_vec(s: &[u8], a: usize, b: usize) -> (v: Vec<u8>)
    requires
        a <= b <= s.len(),
    ensures
        v@ == lower_span(s@, a as int, b as int),
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = a;
    while i < b
        invariant
            a <= i <= b,
            b <= s.len(),
            v@ == lower_span(s@, a as int, i as int),
        decreases b - i,
    {
        let lo = to_lower_exec(s[i]);
        proof {
            assert(lower_span(s@, a as int, (i + 1) as int)
                == lower_span(s@, a as int, i as int) + seq![lo]);
        }
        v.push(lo);
        i += 1;
    }
    v
}

/// exec face of a byte-slice copy (s[a..b) as an owned payload).
pub exec fn sub_vec(s: &[u8], a: usize, b: usize) -> (v: Vec<u8>)
    requires
        a <= b <= s.len(),
    ensures
        v@ == slice_seq(s@, a as int, b as int),
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = a;
    while i < b
        invariant
            a <= i <= b,
            b <= s.len(),
            v@.len() == i - a,
            (forall|k: int| a <= k && k < i ==> v@[k - a] == s[k]),
        decreases b - i,
    {
        let x = s[i];
        proof {
            assert(v@.push(x).len() == (i + 1 - a) as int);
            assert forall|k: int| a <= k < i + 1 implies v@.push(x)[k - a] == s[k] by {
                if k < i {
                    assert(v@.push(x)[k - a] == v@[k - a]);
                    assert(v@[k - a] == s[k]);
                } else {
                    assert(k == i);
                    assert(v@.push(x)[k - a] == x);
                    assert(s[k] == x);
                }
            }
            let rhs = slice_seq(s@, a as int, (i + 1) as int);
            assert(rhs.len() == (i + 1 - a) as int);
            assert forall|k: int| 0 <= k < rhs.len() implies rhs[k] == s[a + k] by {};
            assert(v@.push(x) == rhs);
        }
        v.push(x);
        i += 1;
    }
    proof {
        let rhs = slice_seq(s@, a as int, b as int);
        assert(rhs.len() == (b - a) as int);
        assert(v@.len() == rhs.len());
        assert forall|k: int| 0 <= k < v@.len() implies v@[k] == rhs[k] by {};
        assert(v@ == rhs);
    }
    v
}

/// Origin Rust: str::trim_start_matches(http_whitespace) over [i, b)
/// (mime.rs:64, 95), transcribed as an index recursion.
pub exec fn ltrim_exec(s: &[u8], i: usize, b: usize) -> (r: usize)
    requires
        i <= b <= s.len(),
    ensures
        i <= r <= b,
        r as int == ltrim(s@, i as int, b as int),
    decreases b - i,
{
    if i < b && http_ws_exec(s[i]) {
        ltrim_exec(s, i + 1, b)
    } else {
        i
    }
}

/// str::trim_end_matches(http_whitespace) over [a, i) (mime.rs:70, 138).
pub exec fn rtrim_exec(s: &[u8], a: usize, i: usize) -> (r: usize)
    requires
        a <= i <= s.len(),
    ensures
        a <= r <= i,
        r as int == rtrim(s@, a as int, i as int),
    decreases i - a,
{
    if a < i && http_ws_exec(s[i - 1]) {
        rtrim_exec(s, a, i - 1)
    } else {
        i
    }
}

/// First t in [i, b); b when none (the splitn(2, t) scan face).
pub exec fn find_byte_exec(s: &[u8], i: usize, b: usize, t: u8) -> (r: usize)
    requires
        i <= b <= s.len(),
    ensures
        i <= r <= b,
        r as int == find_byte(s@, i as int, b as int, t as u8),
    decreases b - i,
{
    if i >= b {
        b
    } else if s[i] == t {
        i
    } else {
        find_byte_exec(s, i + 1, b, t)
    }
}

/// Origin Rust: fn split2(s: &str, separator: char) -> (&str, Option<&str>)
/// (mime.rs:85-89) over [a, b): end of the first part, plus Some(start-of-rest)
/// iff the separator occurs.
pub exec fn split2_exec(s: &[u8], a: usize, b: usize, t: u8) -> (r: (usize, Option<usize>))
    requires
        a <= b <= s.len(),
    ensures
        a <= r.0 <= b,
        r.0 as int == find_byte(s@, a as int, b as int, t as u8),
        r.1 == (if r.0 < b { Option::Some((r.0 + 1) as usize) } else { Option::None }),
{
    let p = find_byte_exec(s, a, b, t);
    if p < b {
        (p, Option::Some(p + 1))
    } else {
        (p, Option::None)
    }
}

/// equality of an owned payload against the s[lo..hi) span (the dedup face of
/// fn contains, mime.rs:153)
pub exec fn bytes_eq_span(a: &Vec<u8>, s: &[u8], lo: usize, hi: usize) -> (r: bool)
    requires
        lo <= hi <= s.len(),
    ensures
        r == (a@ == slice_seq(s@, lo as int, hi as int)),
{
    if a.len() != hi - lo {
        proof {
            assert(a@.len() != (hi - lo) as int);
            assert(slice_seq(s@, lo as int, hi as int).len() == (hi - lo) as int);
            assert(a@ != slice_seq(s@, lo as int, hi as int));
        }
        false
    } else {
        let mut i: usize = 0;
        let mut all = true;
        while i < hi - lo
            invariant
                i <= hi - lo,
                hi <= s.len(),
                a.len() == hi - lo,
                all ==> (forall|k: int| 0 <= k && k < i ==> a[k] == s[lo + k]),
            decreases hi - lo - i,
        {
            if a[i] != s[lo + i] {
                proof {
                    let lhs = a@;
                    let rhs = slice_seq(s@, lo as int, hi as int);
                    assert(lhs.len() == rhs.len());
                    assert(lhs[i as int] == a[i as int]);
                    assert(rhs[i as int] == s[lo + i]);
                    assert(lhs[i as int] != rhs[i as int]);
                    assert(lhs != rhs);
                }
                return false;
            }
            i += 1;
        }
        proof {
            let lhs = a@;
            let rhs = slice_seq(s@, lo as int, hi as int);
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                assert(lhs[k] == a[k]);
                assert(rhs[k] == s[lo + k]);
            }
            assert(lhs == rhs);
        }
        true
    }
}

/// Origin Rust: fn contains(parameters, name) -> bool (mime.rs:152-154):
/// a forward scan of the accumulated (lowercased) names, raw-vs-lower.
/// Transcribed as an index recursion mirroring has_name (the loop form of the
/// forward-scan needs no invariant in this mirror).
pub exec fn has_name_exec_go(
    parameters: &Vec<(Vec<u8>, Vec<u8>)>,
    s: &[u8],
    ns: usize,
    eq: usize,
    i: usize,
) -> (r: bool)
    requires
        ns <= eq <= s.len(),
        i <= parameters.len(),
    ensures
        r == has_name(params_view(parameters), slice_seq(s@, ns as int, eq as int), i as int),
    decreases parameters.len() - i,
{
    if i >= parameters.len() {
        proof {
            reveal_with_fuel(has_name, 2);
        }
        false
    } else if bytes_eq_span(&parameters[i].0, s, ns, eq) {
        proof {
            reveal_with_fuel(has_name, 2);
            assert(params_view(parameters)[i as int].0 == parameters[i as int].0@);
            assert(parameters[i as int].0@ == slice_seq(s@, ns as int, eq as int));
            assert(params_view(parameters)[i as int].0 == slice_seq(s@, ns as int, eq as int));
        }
        true
    } else {
        proof {
            reveal_with_fuel(has_name, 2);
            assert(params_view(parameters)[i as int].0 == parameters[i as int].0@);
            assert(parameters[i as int].0@ != slice_seq(s@, ns as int, eq as int));
            assert(params_view(parameters)[i as int].0 != slice_seq(s@, ns as int, eq as int));
        }
        has_name_exec_go(parameters, s, ns, eq, i + 1)
    }
}

pub exec fn has_name_exec(
    parameters: &Vec<(Vec<u8>, Vec<u8>)>,
    s: &[u8],
    ns: usize,
    eq: usize,
) -> (r: bool)
    requires
        ns <= eq <= s.len(),
    ensures
        r == has_name(params_view(parameters), slice_seq(s@, ns as int, eq as int), 0),
{
    has_name_exec_go(parameters, s, ns, eq, 0)
}

/// byte-slice equality exec face (the P: PartialEq<str> instantiations).
pub exec fn bytes_eq(a: &Vec<u8>, b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        proof {
            assert(a@.len() != b@.len());
            assert(a@ != b@);
        }
        false
    } else {
        let mut i: usize = 0;
        let mut all = true;
        while i < b.len()
            invariant
                i <= b.len(),
                a.len() == b.len(),
                all ==> (forall|k: int| 0 <= k && k < i ==> a[k] == b[k]),
            decreases b.len() - i,
        {
            if a[i] != b[i] {
                proof {
                    let lhs = a@;
                    let rhs = b@;
                    assert(lhs.len() == rhs.len());
                    assert(lhs[i as int] == a[i as int]);
                    assert(rhs[i as int] == b[i as int]);
                    assert(lhs[i as int] != rhs[i as int]);
                    assert(lhs != rhs);
                }
                return false;
            }
            i += 1;
            proof {
                assert(a@.len() == b@.len());
            }
        }
        proof {
            let lhs = a@;
            let rhs = b@;
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                assert(lhs[k] == a[k]);
                assert(rhs[k] == b[k]);
            }
            assert(lhs == rhs);
        }
        true
    }
}

impl Mime {
    /// Upstream doc (mime.rs:15-16):
    ///   Construct a new [`Mime`] with the given `type_` and `subtype` and an
    ///   empty parameter list.
    pub exec fn new(type_: &[u8], subtype: &[u8]) -> (m: Mime)
        ensures
            m.type_@ == type_@,
            m.subtype@ == subtype@,
            m.parameters@ == Seq::<(Vec<u8>, Vec<u8>)>::empty(),
    {
        /* Origin Rust: type_.into(), subtype.into() -- the String faces are
         * carried as byte vectors */
        Mime {
            type_: sub_vec(type_, 0, type_.len()),
            subtype: sub_vec(subtype, 0, subtype.len()),
            parameters: Vec::new(),
        }
    }

    /// Upstream doc (mime.rs:25-26):
    ///   Return true if this [`Mime`] matches a given type and subtype, regardless
    ///   of what parameters it has.
    pub exec fn matches(&self, t: &[u8], sub: &[u8]) -> (r: bool)
        ensures
            r == (self.type_@ == t@ && self.subtype@ == sub@),
    {
        bytes_eq(&self.type_, t) && bytes_eq(&self.subtype, sub)
    }

    /// Origin Rust: pub fn get_parameter<P>(&self, name: &P) -> Option<&str>
    /// where P: ?Sized + PartialEq<str>  (mime.rs:31-39). The byte face
    /// instantiates P at the raw-byte equality; the borrow surface is
    /// transcribed as an index result. The scan is an index recursion
    /// mirroring find_param.
    pub exec fn find_param_exec(
        params: &Vec<(Vec<u8>, Vec<u8>)>,
        name: &[u8],
        i: usize,
    ) -> (r: Option<usize>)
        requires
            i <= params.len(),
        ensures
            match r {
                Option::Some(k) => k < params.len()
                    && find_param(params_view(params), name@, i as int) == k as int,
                Option::None => find_param(params_view(params), name@, i as int) == -1,
            },
        decreases params.len() - i,
    {
        if i >= params.len() {
            proof {
                reveal_with_fuel(find_param, 2);
            }
            Option::None
        } else if bytes_eq(&params[i].0, name) {
            proof {
                reveal_with_fuel(find_param, 2);
                assert(params_view(params)[i as int].0 == params[i as int].0@);
                assert(params[i as int].0@ == name@);
                assert(params_view(params)[i as int].0 == name@);
            }
            Option::Some(i)
        } else {
            proof {
                reveal_with_fuel(find_param, 2);
                assert(params_view(params)[i as int].0 == params[i as int].0@);
                assert(params_view(params)[i as int].0 != name@);
            }
            Mime::find_param_exec(params, name, i + 1)
        }
    }

    pub exec fn get_parameter(&self, name: &[u8]) -> (r: Option<usize>)
        ensures
            match r {
                Option::Some(idx) => find_param(params_view(&self.parameters), name@, 0) == idx as int,
                Option::None => find_param(params_view(&self.parameters), name@, 0) == -1,
            },
    {
        Mime::find_param_exec(&self.parameters, name, 0)
    }
}

/// Upstream doc (mime.rs:97-98, the loop-head comment, kept for context):
///   We can not early return on an invalid name here, because the value
///   parsing later may consume more semicolon separated pieces.
///
/// Origin Rust: fn parse_parameters(s: &str, parameters: &mut Vec<(String, String)>)
/// (mime.rs:91-150). The `split(';')` piece iterator plus the quote-driven
/// piece-consumption sub-machine is transcribed as one position-advancing
/// stage scan (Section A note): one iteration below is one byte transition,
/// with stage / ns / eq / cel / qvalv mirroring the stage parameters of
/// params_spec (4294967295 is the -1 sentinel), and first_val marking that
/// the stage-2 value scan is still at its first byte (the spec guard
/// pos == eq + 1). fn contains (mime.rs:152-154) is carried by has_name_exec.
pub exec fn parse_parameters(
    s: &[u8],
    start: usize,
    b0: usize,
    parameters: &mut Vec<(Vec<u8>, Vec<u8>)>,
)
    requires
        start <= b0 <= s.len(),
        b0 < 4000000000,
    ensures
        params_view(final(parameters))
            == params_spec(
                s@,
                start as int,
                b0 as int,
                -1,
                -1,
                -1,
                0,
                Seq::empty(),
                params_view(old(parameters)),
            ),
{
    let mut pos: usize = start;
    let mut ns: usize = 4294967295usize;
    let mut eq: usize = 4294967295usize;
    let mut cel: usize = 4294967295usize;
    let mut stage: usize = 0;
    let mut first_val: bool = false;
    let mut qvalv: Vec<u8> = Vec::new();
    let ghost total = params_spec(
        s@,
        start as int,
        b0 as int,
        -1,
        -1,
        -1,
        0,
        Seq::empty(),
        params_view(parameters),
    );
    while pos < b0
        invariant
            start <= pos <= b0,
            b0 <= s.len(),
            b0 < 4000000000,
            stage == 0 || stage == 1 || stage == 2 || stage == 3 || stage == 4,
            stage == 1 || stage == 2 || stage == 4 ==> sent(ns) == (ns as int),
            stage == 2 || stage == 4 ==> sent(eq) == (eq as int),
            stage == 2 ==> sent(cel) == (cel as int),
            stage == 0 || stage == 3 ==> ns == 4294967295 && eq == 4294967295 && cel == 4294967295,
            stage == 1 ==> ns != 4294967295 && (ns as int) < pos as int,
            stage == 2 ==> ns != 4294967295 && eq != 4294967295 && ns <= eq
                && (eq as int) < pos as int && eq + 1 <= cel && (cel as int) <= pos as int
                && first_val == ((eq as int) + 1 == pos as int),
            stage == 4 ==> ns != 4294967295 && eq != 4294967295 && ns <= eq && (eq as int) < pos as int,
            stage != 4 ==> qvalv@.len() == 0,
            params_spec(
                s@,
                pos as int,
                b0 as int,
                sent(ns),
                sent(eq),
                sent(cel),
                stage as int,
                qvalv@,
                params_view(parameters),
            ) == total,
        decreases b0 - pos,
    {
        let ghost p0 = pos as int;
        let ghost ns0 = sent(ns);
        let ghost eq0 = sent(eq);
        let ghost cel0 = sent(cel);
        let ghost st0 = stage as int;
        let ghost qv0 = qvalv@;
        let ghost pv0 = params_view(parameters);
        let b = s[pos];
        if stage == 3 {
            // discard the rest of the piece that contained the closing quote
            if b == 0x3B {
                stage = 0;
                ns = 4294967295usize;
                eq = 4294967295usize;
                cel = 4294967295usize;
            }
            proof {
                reveal_with_fuel(params_spec, 2);
                assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                    == params_spec(
                        s@,
                        p0 + 1,
                        b0 as int,
                        sent(ns),
                        sent(eq),
                        sent(cel),
                        stage as int,
                        qvalv@,
                        params_view(parameters),
                    ));
            }
            pos += 1;
        } else if stage == 4 {
            if b == 0x22 {
                // closing quote: raw-value push decision, then the discard stage
                let name_ok = ns < eq && all_token_exec(s, ns, eq);
                let not_dup = !has_name_exec(parameters, s, ns, eq);
                let raw_ok = valid_upto_exec(s, eq + 1, b0);
                if name_ok && not_dup && raw_ok {
                    /* Origin Rust: parameters.push((name.to_ascii_lowercase(), value)) */
                    let lname = lower_vec(s, ns, eq);
                    parameters.push((lname, qvalv));
                    qvalv = Vec::new();
                    proof {
                        let ghost acc1 = pv0
                            + seq![(lower_span(s@, ns as int, eq as int), qv0)];
                        assert(params_view(parameters) == acc1);
                    }
                } else {
                    qvalv = Vec::new();
                    proof {
                        assert(params_view(parameters) == pv0);
                    }
                }
                stage = 3;
                ns = 4294967295usize;
                eq = 4294967295usize;
                cel = 4294967295usize;
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(
                            s@,
                            p0 + 1,
                            b0 as int,
                            -1,
                            -1,
                            -1,
                            3,
                            Seq::empty(),
                            params_view(parameters),
                        ));
                }
            } else if b == 0x5C && pos + 1 >= b0 {
                // Origin Rust: .unwrap_or('\\') at the very end of input
                proof {
                    assert(qvalv@ == qv0);
                }
                qvalv.push(0x5C);
                proof {
                    assert(qvalv@ == qv0 + seq![0x5Cu8]);
                }
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(
                            s@,
                            p0 + 1,
                            b0 as int,
                            ns0,
                            eq0,
                            -1,
                            4,
                            qvalv@,
                            params_view(parameters),
                        ));
                }
            } else if b == 0x5C {
                // the escaped successor byte (';' included, mime.rs:110-119)
                let x = s[pos + 1];
                proof {
                    assert(qvalv@ == qv0);
                }
                qvalv.push(x);
                proof {
                    assert(qvalv@ == qv0 + seq![x]);
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(
                            s@,
                            p0 + 2,
                            b0 as int,
                            ns0,
                            eq0,
                            -1,
                            4,
                            qvalv@,
                            params_view(parameters),
                        ));
                }
                pos += 1;
            } else {
                proof {
                    assert(qvalv@ == qv0);
                }
                qvalv.push(b);
                proof {
                    assert(qvalv@ == qv0 + seq![b]);
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(
                            s@,
                            p0 + 1,
                            b0 as int,
                            ns0,
                            eq0,
                            -1,
                            4,
                            qvalv@,
                            params_view(parameters),
                        ));
                }
            }
            pos += 1;
        } else if stage == 2 {
            if first_val && b == 0x22 {
                // the quoted-value form (mime.rs:102): qvalv starts empty
                stage = 4;
                cel = 4294967295usize;
                first_val = false;
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(pos as int == eq0 + 1);
                    assert(b == 0x22);
                    assert(qv0 == Seq::<u8>::empty());
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(
                            s@,
                            p0 + 1,
                            b0 as int,
                            ns0,
                            eq0,
                            -1,
                            4,
                            qvalv@,
                            params_view(parameters),
                        ));
                }
            } else if b == 0x3B {
                // piece boundary: finalize the trimmed unquoted value
                let name_ok = ns < eq && all_token_exec(s, ns, eq);
                let not_dup = !has_name_exec(parameters, s, ns, eq);
                let val_ok = eq + 1 < cel && all_valid_exec(s, eq + 1, cel);
                if name_ok && not_dup && val_ok {
                    /* Origin Rust: parameters.push((name.to_ascii_lowercase(), value)) */
                    let lname = lower_vec(s, ns, eq);
                    let valv = sub_vec(s, eq + 1, cel);
                    parameters.push((lname, valv));
                }
                proof {
                    let ghost pv1 = params_view(parameters);
                    assert(pv1 == unq_push(s@, ns0, eq0, cel0, pv0));
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(s@, p0 + 1, b0 as int, -1, -1, -1, 0, Seq::empty(), pv1));
                }
                stage = 0;
                ns = 4294967295usize;
                eq = 4294967295usize;
                cel = 4294967295usize;
                first_val = false;
            } else {
                // accumulate: cel advances only for non-whitespace
                // (the trim_end_matches face, mime.rs:138)
                if !http_ws_exec(b) {
                    cel = pos + 1;
                }
                proof {
                    reveal_with_fuel(params_spec, 2);
                    let ghost cel1 = sent(cel);
                    assert(qv0 == Seq::<u8>::empty());
                    assert(b == s@.index(p0));
                    assert(b != 0x3B);
                    assert(cel == cel0 || cel == pos + 1);
                    assert(cel != 4294967295);
                    assert(sent(cel) == cel as int);
                    assert(cel1 == sent(cel));
                    assert(cel0 != 4294967295);
                    assert(!http_ws(s@.index(p0)) == !http_ws(b));
                    assert(!http_ws(s@.index(p0)) ==> cel1 == p0 + 1);
                    assert(http_ws(s@.index(p0)) ==> cel1 == cel0);
                    assert(p0 < b0 as int);
                    assert(st0 == 2);
                    assert(p0 != eq0 + 1 || s@.index(p0) != 0x22);
                    assert(s@.index(p0) != 0x3B);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(s@, p0 + 1, b0 as int, ns0, eq0, cel1, 2, Seq::empty(), pv0));
                }
                first_val = false;
            }
            pos += 1;
        } else if stage == 1 {
            if b == 0x3B {
                // piece ends with no '=': nothing is pushed (mime.rs:101-107)
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(s@, p0 + 1, b0 as int, -1, -1, -1, 0, Seq::empty(), pv0));
                }
                stage = 0;
                ns = 4294967295usize;
                eq = 4294967295usize;
                cel = 4294967295usize;
            } else if b == 0x3D {
                // '=' found: the value scan opens
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(s@, p0 + 1, b0 as int, ns0, p0, p0 + 1, 2, Seq::empty(), pv0));
                }
                eq = pos;
                cel = pos + 1;
                stage = 2;
                first_val = true;
            } else {
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(s@, p0 + 1, b0 as int, ns0, -1, -1, 1, Seq::empty(), pv0));
                }
            }
            pos += 1;
        } else {
            // stage 0: piece entry
            if b == 0x3B {
                // an empty piece
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(s@, p0 + 1, b0 as int, -1, -1, -1, 0, Seq::empty(), pv0));
                }
            } else if http_ws_exec(b) {
                // require!: piece leading HTTP whitespace (mime.rs:95)
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(s@, p0 + 1, b0 as int, -1, -1, -1, 0, Seq::empty(), pv0));
                }
            } else if b == 0x3D {
                // '=' with an empty name (still staged as a value: the quoted
                // form may consume further pieces)
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(s@, p0 + 1, b0 as int, p0, p0, p0 + 1, 2, Seq::empty(), pv0));
                }
                ns = pos;
                eq = pos;
                cel = pos + 1;
                stage = 2;
                first_val = true;
            } else {
                // the name opens at this byte
                proof {
                    reveal_with_fuel(params_spec, 2);
                    assert(params_spec(s@, p0, b0 as int, ns0, eq0, cel0, st0, qv0, pv0)
                        == params_spec(s@, p0 + 1, b0 as int, p0, -1, -1, 1, Seq::empty(), pv0));
                }
                ns = pos;
                stage = 1;
            }
            pos += 1;
        }
    }
    // input exhausted: the base evaluation of params_spec pushes a pending
    // unquoted value (raw end b0) or a pending unclosed quoted value
    let ghost pv_exit = params_view(parameters);
    let ghost qv_exit = qvalv@;
    if stage == 2 {
        let ghost pv_pre = params_view(parameters);
        let name_ok = ns < eq && all_token_exec(s, ns, eq);
        let not_dup = !has_name_exec(parameters, s, ns, eq);
        let val_ok = eq + 1 < cel && all_valid_exec(s, eq + 1, cel);
        if name_ok && not_dup && val_ok {
            let lname = lower_vec(s, ns, eq);
            let valv = sub_vec(s, eq + 1, cel);
            parameters.push((lname, valv));
            proof {
                assert(params_view(parameters)
                    == pv_pre + seq![(lower_span(s@, ns as int, eq as int), slice_seq(s@, (eq + 1) as int, cel as int))]);
                assert(lower_span(s@, ns as int, eq as int) == lname@);
                assert(slice_seq(s@, (eq + 1) as int, cel as int) == valv@);
            }
        } else {
            proof {
                assert(params_view(parameters) == pv_pre);
            }
        }
        proof {
            reveal_with_fuel(params_spec, 2);
            assert(stage == 2);
            assert(ns != 4294967295);
            assert(eq != 4294967295);
            assert(cel != 4294967295);
            assert(sent(ns) == ns as int);
            assert(sent(eq) == eq as int);
            assert(sent(cel) == cel as int);
            // the base evaluation with the exit view is the mirrored push
            assert(unq_push(s@, sent(ns), sent(eq), sent(cel), pv_pre)
                == params_view(parameters));
        }
    } else if stage == 4 {
        let ghost pv_pre = params_view(parameters);
        let name_ok = ns < eq && all_token_exec(s, ns, eq);
        let not_dup = !has_name_exec(parameters, s, ns, eq);
        let raw_ok = valid_upto_exec(s, eq + 1, b0);
        if name_ok && not_dup && raw_ok {
            let lname = lower_vec(s, ns, eq);
            parameters.push((lname, qvalv));
            qvalv = Vec::new();
            proof {
                reveal_with_fuel(params_spec, 2);
                assert(stage == 4);
                assert(ns != 4294967295);
                assert(eq != 4294967295);
                assert(sent(ns) == ns as int);
                assert(sent(eq) == eq as int);
                assert(lower_span(s@, ns as int, eq as int) == lname@);
                assert(params_view(parameters) == pv_pre + seq![(lname@, qv_exit)]);
            }
        } else {
            proof {
                reveal_with_fuel(params_spec, 2);
                assert(stage == 4);
                assert(ns != 4294967295);
                assert(eq != 4294967295);
                assert(sent(ns) == ns as int);
                assert(sent(eq) == eq as int);
                assert(params_view(parameters) == pv_pre);
            }
        }
    }
    proof {
        reveal_with_fuel(params_spec, 2);
        reveal_with_fuel(unq_push, 1);
        // the base evaluation (against the loop-exit view) is the mirrored
        // pending-push state in every stage case
        assert(params_spec(
            s@,
            b0 as int,
            b0 as int,
            sent(ns),
            sent(eq),
            sent(cel),
            stage as int,
            qv_exit,
            pv_exit,
        ) == params_view(final(parameters)));
        // the invariant held at the exit position with the exit view
        assert(params_spec(
            s@,
            b0 as int,
            b0 as int,
            sent(ns),
            sent(eq),
            sent(cel),
            stage as int,
            qv_exit,
            pv_exit,
        ) == total);
        assert(params_view(final(parameters)) == total);
    }
}

/// Upstream doc (mime.rs:54-61):
///   <https://mimesniff.spec.whatwg.org/#parsing-a-mime-type>
/// Origin Rust: impl FromStr for Mime { type Err = MimeParsingError;
///   fn from_str(s: &str) -> ... parse(s).ok_or(...) } (mime.rs:55-61).
/// The from_str face returns the Option form of parse's result.
pub exec fn parse_bytes(s: &[u8]) -> (r: Option<Mime>)
    requires
        s.len() < 4000000000,
    ensures
        r.is_some() == mime_parse_spec(s@).is_some(),
        r.is_some() ==> mime_view_of(&r.unwrap()) == (mime_parse_spec(s@).unwrap()),
{
    let a0 = ltrim_exec(s, 0, s.len());
    let b0 = rtrim_exec(s, a0, s.len());
    let (sl, has_slash) = split2_exec(s, a0, b0, 0x2F);
    if has_slash.is_none() {
        // Origin Rust: split2(rest?, ';') -- the '?' early-returns None
        proof {
            assert(find_byte(s@, a0 as int, b0 as int, 0x2F) == b0 as int);
            assert(b0 as int == ltrim(s@, 0, s.len() as int) || true);
            assert(mime_parse_spec(s@) == None);
        }
        return None;
    }
    if a0 == sl || !all_token_exec(s, a0, sl) {
        proof {
            let ms = mime_parse_spec(s@);
            assert(find_byte(s@, a0 as int, b0 as int, 0x2F) < b0 as int);
            assert(!(a0 == sl || !all_token(s@, a0 as int, sl as int)) == false);
            assert(ms == None);
        }
        return None;
    }
    let (semi, has_semi) = split2_exec(s, sl + 1, b0, 0x3B);
    let sube = if has_semi.is_some() { semi } else { b0 };
    let sub = rtrim_exec(s, sl + 1, sube);
    if sl + 1 == sub || !all_token_exec(s, sl + 1, sub) {
        proof {
            let ms = mime_parse_spec(s@);
            assert(!(sl + 1 == sub || !all_token(s@, (sl + 1) as int, sub as int)) == false);
            assert(ms == None);
        }
        return None;
    }
    let mut parameters: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    if has_semi.is_some() {
        proof {
            assert(params_view(&parameters).len() == 0);
            assert(params_view(&parameters) == Seq::<(Seq<u8>, Seq<u8>)>::empty());
        }
        parse_parameters(s, semi + 1, b0, &mut parameters);
    }
    let m = Mime {
        type_: lower_vec(s, a0, sl),
        subtype: lower_vec(s, sl + 1, sub),
        parameters,
    };
    proof {
        let ms = mime_parse_spec(s@);
        assert(a0 as int == ltrim(s@, 0, s.len() as int));
        assert(b0 as int == rtrim(s@, a0 as int, s.len() as int));
        assert(sl as int == find_byte(s@, a0 as int, b0 as int, 0x2F));
        assert(semi as int == find_byte(s@, (sl + 1) as int, b0 as int, 0x3B));
        assert(ms.is_some());
        let g = ms.unwrap();
        assert(g.0 == lower_span(s@, a0 as int, sl as int));
        assert(g.1 == lower_span(s@, (sl + 1) as int, sub as int));
        assert(g.2 == if has_semi.is_some() {
            params_spec(s@, (semi + 1) as int, b0 as int, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        } else {
            Seq::<(Seq<u8>, Seq<u8>)>::empty()
        });
        assert(mime_view_of(&m) == g);
    }
    Some(m)
}

// ================= Section C: the fmt::Display serializer face =================

/// helper: append a whole payload (the f.write_str face)
pub exec fn append_all(a: &Vec<u8>, out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + a@,
{
    let mut i: usize = 0;
    let ghost init = old(out)@;
    while i < a.len()
        invariant
            i <= a.len(),
            out@.len() == init.len() + i as int,
            (forall|k: int| 0 <= k && k < init.len() ==> out[k] == init[k]),
            (forall|k: int| 0 <= k && k < i ==> out[init.len() + k] == a[k]),
        decreases a.len() - i,
    {
        let x = a[i];
        let ghost pre = out@;
        out.push(x);
        proof {
            assert(out@ == pre.push(a[i as int]));
            assert(out@.len() == init.len() + (i + 1) as int);
            assert forall|k: int| 0 <= k < init.len() as int implies out[k] == init[k] by {};
            assert(out[init.len() + i as int] == x);
            assert forall|k: int| 0 <= k < (i + 1) as int implies out[init.len() + k] == a[k] by {
                if k < i as int {
                    assert(out[init.len() + k] == pre[init.len() + k]);
                }
            }
        }
        i += 1;
    }
    proof {
        let lhs = out@;
        let rhs = init + a@;
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < init.len() as int {
                assert(lhs[k] == init[k]);
                assert(rhs[k] == init[k]);
            } else {
                let j = k - init.len();
                assert(lhs[k] == a[j]);
                assert(rhs[k] == a[j]);
            }
        }
        assert(lhs == rhs);
    }
}

/// Origin Rust: impl fmt::Display for Mime (mime.rs:164-188), byte-payload
/// face (the Formatter/String surface has no vstd spec); f.write_str calls
/// become sequential appends, the parameter arm (mime.rs:169-184) folds per
/// parameter: raw value when token-and-non-empty, else quoted with escapes.
pub exec fn serialize_bytes(m: &Mime) -> (v: Vec<u8>)
    ensures
        v@ == ser_mime(mime_view_of(m)),
{
    serialize_inner(m)
}

/// exec form taking the carrier by value: cross-module callers hit a mode
/// limitation with struct reference parameters in this build.
pub exec fn serialize_val(m: Mime) -> (v: Vec<u8>)
    ensures
        v@ == ser_mime((m.type_@, m.subtype@, params_view(&m.parameters))),
{
    serialize_inner(&m)
}

fn serialize_inner(m: &Mime) -> (v: Vec<u8>)
    ensures
        v@ == ser_mime(mime_view_of(m)),
{
    let mut out: Vec<u8> = Vec::new();
    append_all(&m.type_, &mut out);
    proof {
        assert(out@.len() == 0 + m.type_@.len() as int);
        assert(out@ == m.type_@);
    }
    out.push(0x2F);
    proof {
        assert(out@ == m.type_@.push(0x2F));
        assert(out@ == m.type_@ + seq![0x2F]);
    }
    append_all(&m.subtype, &mut out);
    proof {
        assert(out@ == (m.type_@ + seq![0x2F]) + m.subtype@);
        assert(out@ == m.type_@ + seq![0x2F] + m.subtype@);
    }
    let ghost mut S: Seq<u8> = Seq::empty();
    let mut k: usize = 0;
    while k < m.parameters.len()
        invariant
            k <= m.parameters.len(),
            ser_params(params_view(&m.parameters), 0)
                == S + ser_params(params_view(&m.parameters), k as int),
            out@ == m.type_@ + seq![0x2F] + m.subtype@ + S,
        decreases m.parameters.len() - k,
    {
        let (name, value) = &m.parameters[k];
        let ghost pre = out@;
        out.push(0x3B);
        proof {
            assert(out@ == pre + seq![0x3B]);
        }
        append_all(name, &mut out);
        proof {
            assert(out@ == pre + seq![0x3B] + name@);
        }
        out.push(0x3D);
        proof {
            assert(out@ == pre + seq![0x3B] + name@ + seq![0x3D]);
        }
        // value arm (mime.rs:173-184)
        let raw_ok = all_token_exec(value, 0, value.len());
        proof {
            assert(raw_ok == all_token(value@, 0, value.len() as int));
        }
        let ghost quoted_start = out@;
        if value.len() > 0 && raw_ok {
            append_all(value, &mut out);
            proof {
                assert(out@ == pre + seq![0x3B] + name@ + seq![0x3D] + value@);
                assert(ser_value(value@) == value@);
            }
        } else {
            out.push(0x22);
            proof {
                assert(out@ == quoted_start + seq![0x22]);
            }
            let ghost q0 = out@;
            let mut j: usize = 0;
            while j < value.len()
                invariant
                    j <= value.len(),
                    out@ == q0 + ser_escape(value@, j as int),
                decreases value.len() - j,
            {
                let c = value[j];
                if c == 0x22 || c == 0x5C {
                    proof {
                        assert(ser_escape(value@, (j + 1) as int)
                            == ser_escape(value@, j as int) + seq![0x5C, c]);
                    }
                    out.push(0x5C);
                    out.push(c);
                    proof {
                        assert(out@ == (q0 + ser_escape(value@, j as int)) + seq![0x5C, c]);
                    }
                } else {
                    proof {
                        assert(ser_escape(value@, (j + 1) as int)
                            == ser_escape(value@, j as int) + seq![c]);
                    }
                    out.push(c);
                    proof {
                        assert(out@ == (q0 + ser_escape(value@, j as int)) + seq![c]);
                    }
                }
                j += 1;
            }
            proof {
                assert(ser_escape(value@, value.len() as int) + Seq::empty()
                    == ser_escape(value@, value.len() as int));
            }
            out.push(0x22);
            proof {
                assert(out@ == (q0 + ser_escape(value@, value.len() as int)) + seq![0x22]);
                assert(q0 == quoted_start + seq![0x22]);
                assert(out@ == quoted_start + seq![0x22] + ser_escape(value@, value.len() as int) + seq![0x22]);
                assert(!(value.len() > 0 && all_token(value@, 0, value.len() as int)));
                assert(ser_value(value@)
                    == seq![0x22] + ser_escape(value@, value.len() as int) + seq![0x22]);
            }
        }
        proof {
            reveal_with_fuel(ser_params, 2);
            assert(params_view(&m.parameters)[k as int].0 == name@);
            assert(params_view(&m.parameters)[k as int].1 == value@);
            assert(ser_params(params_view(&m.parameters), k as int)
                == seq![0x3B] + name@ + seq![0x3D] + ser_value(value@)
                    + ser_params(params_view(&m.parameters), (k + 1) as int));
            S = S + seq![0x3B] + name@ + seq![0x3D] + ser_value(value@);
            assert(ser_params(params_view(&m.parameters), 0)
                == S + ser_params(params_view(&m.parameters), (k + 1) as int));
            assert(out@ == m.type_@ + seq![0x2F] + m.subtype@ + S);
        }
        k += 1;
    }
    proof {
        reveal_with_fuel(ser_params, 2);
        assert(ser_params(params_view(&m.parameters), m.parameters.len() as int)
            == Seq::empty());
        let lhs = out@;
        let rhs = ser_mime(mime_view_of(m));
        assert(rhs == m.type_@ + seq![0x2F] + m.subtype@ + ser_params(params_view(&m.parameters), 0));
        assert(lhs == rhs);
    }
    out
}

}

fn main() {}
