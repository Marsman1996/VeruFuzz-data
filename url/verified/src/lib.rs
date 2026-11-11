//! `url` crate mirror -- src/lib.rs (first verus batch subset)
//!
//! Upstream: https://github.com/servo/rust-url (pin 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a)
//! crate root at `code/url/` (SUBDIR=url; code/ tree untouched).
//! This file is the same-name mirror of `src/lib.rs`, restricted to the Url
//! data model (lib.rs:226-249), the structural-invariant model of the private
//! `check_invariants` face (lib.rs:686-808), and the core read API value
//! semantics (the `&self` query methods, lib.rs:633-1549). The mutation/write
//! face (set_fragment/set_query/set_path/set_port/set_host/set_username/
//! set_password/set_scheme and helpers, lib.rs:1551-2510), the parser entry
//! points (parse/join/make_relative), the file-path conversion face, the
//! Position/slicing face and the serde layer are later batches.
//!
//! Lossy-abstraction ledger (per item, verus vs upstream):
//! 1. `Url.serialization` is a std `String` upstream; String has no vstd spec,
//!    so the mirror carries the byte payload `Vec<u8>` with the Seq view as
//!    the token of content (same ruling as the form_urlencoded mirror). All
//!    `&str` returns become owned byte vectors whose content is the same;
//!    the `#[inline]`/borrow-copy free-of-charge aspects of the upstream
//!    returns are alloc-level properties outside the verus surface.
//! 2. The private `slice<R: RangeArg>` helper (lib.rs:2762-2767) is generic
//!    over the `RangeArg` trait; the mirror is a concrete
//!    `bytes_slice(v, a, b)` free fn (the trait layer is outside the verus
//!    surface, every call site names its range bounds).
//! 3. `url_invariant` below transcribes the *structural* portion of
//!    `check_invariants` (lib.rs:713-789): component bounds, delimiter bytes,
//!    the userinfo/host/port/tag consistency, and the query/fragment ordering.
//!    Host-serialization equality checks (`Ipv4`/`Ipv6` host string form,
//!    lib.rs:738-742) and the reparse round-trip (lib.rs:791-806) depend on
//!    the parser machine and the IP serializers and are deferred to the
//!    parser batch; no read-API obligation below uses them.
//! 4. `to_ascii_lowercase`/`Display`/`From<Url> for String`/`Index<Position>`
//!    are std/fmt-layer and outside this batch.
//!
//! Percent-encoding interplay: none of the read APIs percent-encode; the write
//! face that does (set_path/set_query/set_fragment + parser) belongs to later
//! batches and will mirror the percent-encoding set model in-tree (per the
//! form_urlencoded cross-crate precedent: literal mirror with source notes,
//! not a `#[path]` reference across database crates).

use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::seq;

#[path = "host.rs"]
pub mod host;

#[path = "parser.rs"]
pub mod parser;

pub use self::host::{Host, HostInternal};
pub use self::parser::{SchemeType};

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::std_specs::vec::group_vec_axioms};

/* ============================================================
 * Char-class helpers (the byte faces of the upstream checks)
 * ============================================================ */

/// 'A'..'Z' or 'a'..'z' (the ascii_alpha Pattern face of the scheme parser).
pub open spec fn is_ascii_alpha(b: u8) -> bool {
    (b >= 0x41u8 && b <= 0x5Au8) || (b >= 0x61u8 && b <= 0x7Au8)
}

/// 'a'..='z' | 'A'..='Z' | '0'..='9' | '+' | '-' | '.'
/// Origin Rust (lib.rs:716-718): matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '+' | '-' | '.')
pub open spec fn is_scheme_char(b: u8) -> bool {
    is_ascii_alpha(b) || (b >= 0x30u8 && b <= 0x39u8)
        || b == 0x2Bu8 || b == 0x2Du8 || b == 0x2Eu8
}

/// '0'..'9' (the digit face of the port region, lib.rs:756).
pub open spec fn is_dec_digit(b: u8) -> bool {
    0x30u8 <= b <= 0x39u8
}

/// Decimal value of a digit-string (the value face of `port_str.parse::<u16>()`,
/// lib.rs:756; empty did not occur there, the empty string is defined as 0
/// only to keep the fold total).
pub open spec fn dec_val(s: Seq<u8>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        dec_val(s.subrange(0, s.len() - 1)) * 10 + ((s.index(s.len() - 1) as int) - 0x30)
    }
}

/* ============================================================
 * Url data model (Origin: lib.rs:225-249)
 * ============================================================ */

/// Upstream doc (lib.rs:225-235):
///   A parsed URL record.
///   (the upstream pseudo-BNF comment, lib.rs:228-235:
///    url = scheme ":" [ hierarchical | non-hierarchical ] [ "?" query ]? [ "#" fragment ]?)
pub struct Url {
    /// Origin Rust: serialization: String  (lib.rs:237; byte payload per ledger 1)
    pub serialization: Vec<u8>,
    /// Origin Rust (lib.rs:240): scheme_end: u32,   // Before ':'
    pub scheme_end: u32,
    /// Origin Rust (lib.rs:241): username_end: u32, // Before ':' (if a password is given) or '@' (if not)
    pub username_end: u32,
    /// Origin Rust (lib.rs:242): host_start: u32,
    pub host_start: u32,
    /// Origin Rust (lib.rs:243): host_end: u32,
    pub host_end: u32,
    /// Origin Rust (lib.rs:244): host: HostInternal,
    pub host: HostInternal,
    /// Origin Rust (lib.rs:245): port: Option<u16>,
    pub port: Option<u16>,
    /// Origin Rust (lib.rs:246): path_start: u32,  // Before initial '/', if any
    pub path_start: u32,
    /// Origin Rust (lib.rs:247): query_start: Option<u32>,   // Before '?', unlike Position::QueryStart
    pub query_start: Option<u32>,
    /// Origin Rust (lib.rs:248): fragment_start: Option<u32>, // Before '#', unlike Position::FragmentStart
    pub fragment_start: Option<u32>,
}

/* ============================================================
 * Spec faces of the read API (the harness-facing value language;
 * the exec methods below are proven against exactly these definitions)
 * ============================================================ */

/// The `://` test of has_authority (lib.rs:957):
/// slice(scheme_end..).starts_with("://"), with byte scheme_end ':' from the invariant.
pub open spec fn has_authority_view(u: &Url) -> bool {
    let n = u.serialization.view().len() as int;
    let se = u.scheme_end as int;
    se + 3 <= n
        && u.serialization.view().index(se + 1) == 0x2Fu8
        && u.serialization.view().index(se + 2) == 0x2Fu8
}

/// Origin Rust (lib.rs:1028): !self.slice(self.scheme_end + 1..).starts_with('/')
pub open spec fn cannot_be_a_base_view(u: &Url) -> bool {
    let n = u.serialization.view().len() as int;
    let se = u.scheme_end as int;
    !(se + 2 <= n && u.serialization.view().index(se + 1) == 0x2Fu8)
}

/// The end offset of the path component (the match of path(), lib.rs:1391-1396):
/// (None, None) => serialization end; Some(next_component_start) for query first,
/// else fragment.
pub open spec fn path_end_view(u: &Url) -> int {
    if u.query_start.is_some() {
        u.query_start.unwrap() as int
    } else if u.fragment_start.is_some() {
        u.fragment_start.unwrap() as int
    } else {
        u.serialization.view().len() as int
    }
}

/// Origin Rust (lib.rs:1390-1397): pub fn path(&self) -> &str
pub open spec fn path_view(u: &Url) -> Seq<u8> {
    u.serialization.view().subrange(u.path_start as int, path_end_view(u))
}

/// Origin Rust (lib.rs:1470-1482): the content after '?' of query(),
/// cut at the fragment start when a fragment exists (lib.rs:1477-1480),
/// else to the serialization end (lib.rs:1473-1476).
/// (valid only when query_start is Some).
pub open spec fn query_content_view(u: &Url) -> Seq<u8> {
    let qs = u.query_start.unwrap() as int;
    let end = if u.fragment_start.is_some() {
        u.fragment_start.unwrap() as int
    } else {
        u.serialization.view().len() as int
    };
    u.serialization.view().subrange(qs + 1, end)
}

/// Origin Rust (lib.rs:1544-1549): the content after '#' of fragment()
/// (valid only when fragment_start is Some).
pub open spec fn fragment_content_view(u: &Url) -> Seq<u8> {
    let fs = u.fragment_start.unwrap() as int;
    u.serialization.view().subrange(fs + 1, u.serialization.view().len() as int)
}

/// Origin Rust (lib.rs:1053-1060): username(); "" when there is no userinfo.
pub open spec fn username_view(u: &Url) -> Seq<u8> {
    let se = u.scheme_end as int;
    if has_authority_view(u) && (u.username_end as int) > se + 3 {
        u.serialization.view().subrange(se + 3, u.username_end as int)
    } else {
        Seq::empty()
    }
}

/// Origin Rust (lib.rs:1086-1098): password(); None unless a ':'-separated
/// password follows the username inside the authority.
pub open spec fn password_view(u: &Url) -> Option<Seq<u8>> {
    if has_authority_view(u) && (u.username_end as int) < (u.serialization.view().len() as int)
        && u.serialization.view().index(u.username_end as int) == 0x3Au8
    {
        Option::Some(
            u.serialization.view()
                .subrange(u.username_end as int + 1, u.host_start as int - 1),
        )
    } else {
        Option::None
    }
}

/// Origin Rust (lib.rs:992-999): authority(); "" when it would be empty.
pub open spec fn authority_view(u: &Url) -> Seq<u8> {
    let se = u.scheme_end as int;
    if has_authority_view(u) && (u.path_start as int) > se + 3 {
        u.serialization.view().subrange(se + 3, u.path_start as int)
    } else {
        Seq::empty()
    }
}

/// Origin Rust (lib.rs:1161-1167): host_str(); Some only when a host exists.
pub open spec fn host_str_view(u: &Url) -> Option<Seq<u8>> {
    if (match u.host {
        HostInternal::None => false,
        HostInternal::Domain => true,
        HostInternal::Ipv4(_) => true,
        HostInternal::Ipv6(_) => true,
    }) {
        Option::Some(u.serialization.view().subrange(u.host_start as int, u.host_end as int))
    } else {
        Option::None
    }
}

/// Origin Rust (lib.rs:1268-1270): port() is the port field.
/// Origin Rust (lib.rs:1300-1302): port_or_known_default() = port.or_else(default_port):
pub open spec fn port_or_known_default_view(u: &Url) -> Option<u16> {
    if u.port.is_some() {
        u.port
    } else {
        parser::default_port_of(u.serialization.view().subrange(0, u.scheme_end as int))
    }
}

/* ============================================================
 * The structural invariant (Origin: check_invariants, lib.rs:686-808;
 * see header ledger 3 for the deferred portions)
 * ============================================================ */

/// path() starts with "//" (lib.rs:770), used by the opaque-path branch.
pub open spec fn opaque_path_double_slash(u: &Url) -> bool {
    (u.path_start as int) + 2 <= path_end_view(u)
        && u.serialization.view().index(u.path_start as int) == 0x2Fu8
        && u.serialization.view().index(u.path_start as int + 1) == 0x2Fu8
}

/// The byte-length bound of every Url: offsets are u32, so serializations are
/// at most 4 GB (the face of to_u32, parser.rs:1742, ParseError::Overflow).
pub open spec fn url_invariant(u: &Url) -> bool {
    let s = u.serialization.view();
    let n = s.len() as int;
    let se = u.scheme_end as int;
    // global bounds and the scheme region (lib.rs:713-719)
    &&& n <= 0xFFFF_FFFF
    &&& 1 <= se
    &&& se + 1 <= n
    &&& is_ascii_alpha(s.index(0))
    &&& (forall|i: int| 1 <= i < se ==> is_scheme_char(s.index(i)))
    &&& s.index(se) == 0x3Au8
    // the two-way split of the serialization (lib.rs:721 vs 763)
    && (if has_authority_view(u) {
        // URL with authority
        // userinfo region (lib.rs:723-733)
        &&& se + 3 <= (u.username_end as int)
        &&& (u.username_end as int) <= n
        &&& (u.username_end as int) != n ==> match s.index(u.username_end as int) {
            0x3Au8 => (
                (u.host_start as int) >= (u.username_end as int) + 2
                && s.index(u.host_start as int - 1) == 0x40u8),
            0x40u8 => ((u.host_start as int) == (u.username_end as int) + 1),
            _ => ((u.username_end as int) == se + 3),
        }
        // host region ordering (lib.rs:733-734)
        &&& (u.host_start as int) >= (u.username_end as int)
        &&& (u.host_start as int) <= n
        &&& (u.host_end as int) >= (u.host_start as int)
        &&& (u.host_end as int) <= n
        &&& (u.path_start as int) >= (u.host_end as int)
        &&& (u.path_start as int) <= n
        // host tag consistency (lib.rs:736-748): None <=> empty host string,
        // a Domain tag on a special scheme is non-empty (lib.rs:743-747)
        &&& (u.host == HostInternal::None) == ((u.host_start as int) == (u.host_end as int))
        && (u.host == HostInternal::Domain
            ==> ((
                parser::is_special(parser::scheme_type_of(s.subrange(0, se)))
                    ==> (u.host_start as int) < (u.host_end as int))))
        // port region (lib.rs:749-758): no explicit port <=> empty region,
        // explicit port <=> ':' + digit-string whose value is the port field
        && ((u.path_start as int) == (u.host_end as int)
            ==> u.port.is_none())
        && ((u.path_start as int) > (u.host_end as int)
            ==> (s.index(u.host_end as int) == 0x3Au8
                && (u.host_end as int) + 1 <= (u.path_start as int)
                && (u.host_end as int) + 1 < (u.path_start as int)
                && (forall|i: int| (u.host_end as int) + 1 <= i < u.path_start as int
                    ==> is_dec_digit(s.index(i)))
                && u.port.is_some()
                && (u.port.unwrap() as int)
                    == dec_val(s.subrange((u.host_end as int) + 1, u.path_start as int))))
        // path_start face (lib.rs:759-762)
        && ((u.path_start as int) < n
            ==> (s.index(u.path_start as int) == 0x2Fu8
                || s.index(u.path_start as int) == 0x23u8
                || s.index(u.path_start as int) == 0x3Fu8))
    } else {
        // Anarchist URL (no authority)
        &&& (u.username_end as int) == se + 1
        &&& (u.host_start as int) == se + 1
        &&& (u.host_end as int) == se + 1
        &&& u.host == HostInternal::None
        &&& u.port.is_none()
        && (if opaque_path_double_slash(u) {
            // special case when first path segment is empty (lib.rs:770-774):
            // the serialization pins a "/." prefix before the opaque "//" path
            &&& s.index(se + 1) == 0x2Fu8
            &&& s.index(se + 2) == 0x2Eu8
            &&& (u.path_start as int) == se + 3
        } else {
            (u.path_start as int) == se + 1
        })
    })
    // query/fragment wrap-up (lib.rs:779-789)
    && (u.query_start.is_some()
        ==> ((u.query_start.unwrap() as int) >= (u.path_start as int)
            && (u.query_start.unwrap() as int) < n
            && s.index(u.query_start.unwrap() as int) == 0x3Fu8))
    && (u.fragment_start.is_some()
        ==> ((u.fragment_start.unwrap() as int) >= (u.path_start as int)
            && (u.fragment_start.unwrap() as int) < n
            && s.index(u.fragment_start.unwrap() as int) == 0x23u8))
    && (u.query_start.is_some() && u.fragment_start.is_some()
        ==> (u.fragment_start.unwrap() as int) > (u.query_start.unwrap() as int))
}

/* ============================================================
 * Exec slicing helpers
 * ============================================================ */

/// Origin Rust: fn slice<R>(&self, range: R) -> &str where R: RangeArg
///   { range.slice_of(&self.serialization) }  (lib.rs:2762-2767)
/// relax (ledger 2): the RangeArg-generic helper becomes a concrete
/// bytes_slice over the byte payload; returns the owned bytes of the slice.
pub exec fn bytes_slice(v: &Vec<u8>, a: u32, b: u32) -> (r: Vec<u8>)
    requires
        0 <= a as int,
        a as int <= b as int,
        b as int <= v.view().len() as int,
    ensures
        r.view() == v.view().subrange(a as int, b as int),
{
    let ghost vseq = v.view();
    let mut out: Vec<u8> = Vec::new();
    let mut i: u32 = a;
    while i < b
        invariant
            vseq == v.view(),
            (vseq.len() as int) >= (b as int),
            a <= i,
            i <= b,
            out.view().len() == (i as int) - (a as int),
            out.view() == vseq.subrange(a as int, i as int),
        decreases b - i
    {
        proof {
            assert((i as int) < (b as int));
            assert((i as int) < (vseq.len() as int));
        }
        let x = v[i as usize];
        proof {
            assert(vseq[i as int] == x);
        }
        out.push(x);
        i += 1;
    }
    out
}

/// exec close-over of `serialization.len() as u32`, proof-pinning the
/// view-length bridge (the URL offset domain bound of url_invariant).
pub exec fn url_len32(v: &Vec<u8>) -> (n: u32)
    requires
        (v.view().len() as int) <= 0xFFFF_FFFF,
    ensures
        (n as int) == (v.view().len() as int),
{
    proof {
        assert(v.len() as int == v.view().len() as int);
    }
    v.len() as u32
}

/// exec guard for `a + 3 <= n` in u32 without a bare `+ 3` overflow check
/// (when a is near u32::MAX the comparison is necessarily false for any
/// n that fits u32, which is exactly the implicit caller-side bound).
pub exec fn u32_add3_fits(a: u32, n: u32) -> (r: bool)
    requires
        (n as int) <= 0xFFFF_FFFF,
    ensures
        r == (((a as int) + 3) <= (n as int)),
{
    if a <= 0xFFFF_FFFC {
        proof {
            assert((a as int) + 3 <= 0xFFFF_FFFF);
        }
        let r = a + 3 <= n;
        proof {
            assert(r == (((a as int) + 3) <= (n as int)));
        }
        r
    } else {
        proof {
            assert((a as int) >= 0xFFFF_FFFD);
            assert((a as int) + 3 >= 0x1_0000_0000);
            assert((n as int) <= 0xFFFF_FFFF);
            assert(!(((a as int) + 3) <= (n as int)));
        }
        false
    }
}

/// exec guard for `a + 2 <= n`, same shape as u32_add3_fits.
pub exec fn u32_add2_fits(a: u32, n: u32) -> (r: bool)
    requires
        (n as int) <= 0xFFFF_FFFF,
    ensures
        r == (((a as int) + 2) <= (n as int)),
{
    if a <= 0xFFFF_FFFD {
        proof {
            assert((a as int) + 2 <= 0xFFFF_FFFF);
        }
        let r = a + 2 <= n;
        proof {
            assert(r == (((a as int) + 2) <= (n as int)));
        }
        r
    } else {
        proof {
            assert((a as int) >= 0xFFFF_FFFE);
            assert((a as int) + 2 >= 0x1_0000_0000);
            assert((n as int) <= 0xFFFF_FFFF);
            assert(!(((a as int) + 2) <= (n as int)));
        }
        false
    }
}

/// Free-position twin of the has_host method (lib.rs:1121-1123):
/// the datatype-discrimination facts of a match on `self.host` discharge
/// in the free-fn position; the method delegates to keep its own
/// postcondition a one-step chain (mirror-shape note, see header).
pub exec fn url_has_host(u: &Url) -> (r: bool)
    requires
        url_invariant(u),
    ensures
        r == (!(u.host == HostInternal::None)),
{
    match u.host {
        HostInternal::None => false,
        HostInternal::Domain => true,
        HostInternal::Ipv4(_) => true,
        HostInternal::Ipv6(_) => true,
    }
}

/* ============================================================
 * The read API (Origin: the `&self` methods of impl Url)
 * ============================================================ */

impl Url {
    /// Origin Rust (lib.rs:340-342): pub fn parse(input: &str)
    ///   -> Result<Self, ParseError> { Self::options().parse(input) } --
    /// the Options::parse layer folded (upstream lib.rs:354-381: the
    /// Parser is built fresh -- serialization empty, base_url None,
    /// context UrlParser -- and drives parse_url); the &str face is the
    /// byte slice here (ledger 1), and the input face is the honest
    /// url_parse_entry_face cone: base-less, non-"file"-scheme inputs.
    pub exec fn parse(input: &[u8]) -> (r: Result<Url, parser::ParseError>)
        requires
            parser::machine_domain(input@),
            (input@.len() as int) <= 0xFFFF_FFFF,
            ((input@.len() as int) == 0
                || 0x20u8 < input@.index(0)),
            parser::url_parse_entry_face(input@),
        ensures
            (r.is_ok() ==> url_invariant(&r.unwrap())),
            (r.is_err() ==> (r == Err(parser::ParseError::EmptyHost)
                || r == Err(parser::ParseError::InvalidPort)
                || r == Err(parser::ParseError::Overflow)
                || r == Err(parser::ParseError::RelativeUrlWithoutBase))),
    {
        let mut p = parser::Parser {
            serialization: Vec::new(),
            base_url: Option::None,
            context: parser::Context::UrlParser,
        };
        p.parse_url(input)
    }

    /// Origin Rust: fn byte_at(&self, i: u32) -> u8
    ///   { self.serialization.as_bytes()[i as usize] }  (lib.rs:2769-2772)
    pub exec fn byte_at(&self, i: u32) -> (r: u8)
        requires
            (i as int) < (self.serialization.view().len() as int),
        ensures
            r == self.serialization.view().index(i as int),
    {
        self.serialization[i as usize]
    }

    /// Origin Rust (lib.rs:651-654): pub fn as_str(&self) -> &str { &self.serialization }
    /// Upstream doc (lib.rs:633-635):
    ///   Return the serialization of this URL.
    ///   This is fast since that serialization is already stored in the `Url` struct.
    /// relax (ledger 1): returns the byte content of the serialization.
    pub exec fn as_str(&self) -> (r: Vec<u8>)
        requires
            url_invariant(self),
        ensures
            r.view() == self.serialization.view(),
    {
        bytes_slice(&self.serialization, 0, url_len32(&self.serialization))
    }

    /// Origin Rust (lib.rs:901-904): pub fn scheme(&self) -> &str
    ///   { self.slice(..self.scheme_end) }
    /// Upstream doc (lib.rs:886-886):
    ///   Return the scheme of this URL, lower-cased, as an ASCII string without the ':' delimiter.
    pub exec fn scheme(&self) -> (r: Vec<u8>)
        requires
            url_invariant(self),
        ensures
            r.view() == self.serialization.view().subrange(0, self.scheme_end as int),
    {
        bytes_slice(&self.serialization, 0, self.scheme_end)
    }

    /// Origin Rust (lib.rs:922-925): pub fn is_special(&self) -> bool
    ///   { let scheme_type = SchemeType::from(self.scheme()); scheme_type.is_special() }
    /// Upstream doc (lib.rs:906-906):
    ///   Return whether the URL is special (has a special scheme)
    pub exec fn is_special(&self) -> (r: bool)
        requires
            url_invariant(self),
        ensures
            r == parser::is_special(parser::scheme_type_of(
                self.serialization.view().subrange(0, self.scheme_end as int))),
    {
        let scheme_bytes = self.scheme();
        let st = parser::scheme_type_from(&scheme_bytes);
        st.is_special()
    }

    /// Origin Rust (lib.rs:954-958): pub fn has_authority(&self) -> bool
    ///   { debug_assert!(self.byte_at(self.scheme_end) == b':');
    ///     self.slice(self.scheme_end..).starts_with("://") }
    /// Upstream doc (lib.rs:927-933):
    ///   Return whether the URL has an 'authority',
    ///   which can contain a username, password, host, and port number.
    ///   URLs that do *not* are either path-only like `unix:/run/foo.socket`
    ///   or cannot-be-a-base like `data:text/plain,Stuff`.
    ///   See also the `authority` method.
    pub exec fn has_authority(&self) -> (r: bool)
        requires
            url_invariant(self),
        ensures
            r == has_authority_view(self),
    {
        let n32 = url_len32(&self.serialization);
        let fit = u32_add3_fits(self.scheme_end, n32);
        fit && self.byte_at(self.scheme_end + 1) == 0x2Fu8
            && self.byte_at(self.scheme_end + 2) == 0x2Fu8
        // Origin Rust (lib.rs:957): self.slice(self.scheme_end..).starts_with("://")
    }

    /// Origin Rust (lib.rs:992-999): pub fn authority(&self) -> &str
    /// Upstream doc (lib.rs:960-969):
    ///   Return the authority of this URL as an ASCII string.
    ///   Non-ASCII domains are punycode-encoded per IDNA if this is the host
    ///   of a special URL, or percent encoded for non-special URLs.
    ///   IPv6 addresses are given between `[` and `]` brackets.
    ///   Ports are omitted if they match the well known port of a special URL.
    ///   Username and password are percent-encoded.
    ///   See also the `has_authority` method.
    pub exec fn authority(&self) -> (r: Vec<u8>)
        requires
            url_invariant(self),
        ensures
            r.view() == authority_view(self),
    {
        let n32 = url_len32(&self.serialization);
        let fit = u32_add3_fits(self.scheme_end, n32);
        let se3 = if fit { self.scheme_end + 3 } else { 0 };
        if self.has_authority() && self.path_start > se3 {
            bytes_slice(&self.serialization, se3, self.path_start)
        } else {
            Vec::new()
        }
    }

    /// Origin Rust (lib.rs:1026-1029): pub fn cannot_be_a_base(&self) -> bool
    ///   { !self.slice(self.scheme_end + 1..).starts_with('/') }
    /// Upstream doc (lib.rs:1001-1005):
    ///   Return whether this URL is a cannot-be-a-base URL,
    ///   meaning that parsing a relative URL string with this URL as the base will return an error.
    ///   This is the case if the scheme and `:` delimiter are not followed by a `/` slash,
    ///   as is typically the case of `data:` and `mailto:` URLs.
    pub exec fn cannot_be_a_base(&self) -> (r: bool)
        requires
            url_invariant(self),
        ensures
            r == cannot_be_a_base_view(self),
    {
        let n32 = url_len32(&self.serialization);
        let fit = u32_add2_fits(self.scheme_end, n32);
        !(fit && self.serialization[(self.scheme_end + 1) as usize] == 0x2Fu8)
    }

    /// Origin Rust (lib.rs:1053-1060): pub fn username(&self) -> &str
    /// Upstream doc (lib.rs:1031-1031):
    ///   Return the username for this URL (typically the empty string)
    ///   as a percent-encoded ASCII string.
    pub exec fn username(&self) -> (r: Vec<u8>)
        requires
            url_invariant(self),
        ensures
            r.view() == username_view(self),
    {
        let n32 = url_len32(&self.serialization);
        let fit = u32_add3_fits(self.scheme_end, n32);
        let se3 = if fit { self.scheme_end + 3 } else { 0 };
        if self.has_authority() && self.username_end > se3 {
            bytes_slice(&self.serialization, se3, self.username_end)
        } else {
            Vec::new()
        }
    }

    /// Origin Rust (lib.rs:1086-1098): pub fn password(&self) -> Option<&str>
    /// Upstream doc (lib.rs:1062-1062):
    ///   Return the password for this URL, if any, as a percent-encoded ASCII string.
    pub exec fn password(&self) -> (r: Option<Vec<u8>>)
        requires
            url_invariant(self),
        ensures
            r.is_some() == password_view(self).is_some(),
            r.is_some() ==> (r.unwrap().view() == password_view(self).unwrap()),
    {
        let has_auth = self.has_authority();
        let n = url_len32(&self.serialization);
        if has_auth && self.username_end != n
            && self.byte_at(self.username_end) == 0x3Au8
        {
            Option::Some(bytes_slice(&self.serialization, self.username_end + 1, self.host_start - 1))
        } else {
            Option::None
        }
    }

    /// Origin Rust (lib.rs:1121-1123): pub fn has_host(&self) -> bool
    ///   { !matches!(self.host, HostInternal::None) }
    /// Upstream doc (lib.rs:1100-1100):
    ///   Equivalent to `url.host().is_some()`.
    pub exec fn has_host(&self) -> (r: bool)
        requires
            url_invariant(self),
        ensures
            r == (!(self.host == HostInternal::None)),
    {
        // Origin Rust (lib.rs:1122): !matches!(self.host, HostInternal::None)
        url_has_host(self)
    }

    /// Origin Rust (lib.rs:1161-1167): pub fn host_str(&self) -> Option<&str>
    /// Upstream doc (lib.rs:1125-1134):
    ///   Return the string representation of the host (domain or IP address) for this URL, if any.
    ///   Non-ASCII domains are punycode-encoded per IDNA if this is the host
    ///   of a special URL, or percent encoded for non-special URLs.
    ///   IPv6 addresses are given between `[` and `]` brackets.
    ///   Cannot-be-a-base URLs (typical of `data:` and `mailto:`) and some `file:` URLs
    ///   don't have a host.
    ///   See also the `host` method.
    pub exec fn host_str(&self) -> (r: Option<Vec<u8>>)
        requires
            url_invariant(self),
        ensures
            r.is_some() == host_str_view(self).is_some(),
            r.is_some() ==> (r.unwrap().view() == host_str_view(self).unwrap()),
    {
        if self.has_host() {
            Option::Some(bytes_slice(&self.serialization, self.host_start, self.host_end))
        } else {
            Option::None
        }
    }

    /// Origin Rust (lib.rs:1200-1207): pub fn host(&self) -> Option<Host<&str>>
    /// Upstream doc (lib.rs:1169-1176):
    ///   Return the parsed representation of the host for this URL.
    ///   Non-ASCII domain labels are punycode-encoded per IDNA if this is the host
    ///   of a special URL, or percent encoded for non-special URLs.
    ///   Cannot-be-a-base URLs (typical of `data:` and `mailto:`) and some `file:` URLs
    ///   don't have a host.
    ///   See also the `host_str` method.
    pub exec fn host(&self) -> (r: Option<Host>)
        requires
            url_invariant(self),
        ensures
            (match r {
                Option::None => self.host == HostInternal::None,
                Option::Some(hk) => (match hk {
                    Host::Domain(d) => self.host == HostInternal::Domain
                        && (d.view()
                            == self.serialization.view().subrange(
                                self.host_start as int, self.host_end as int)),
                    Host::Ipv4(a) => self.host == HostInternal::Ipv4(a),
                    Host::Ipv6(a) => self.host == HostInternal::Ipv6(a),
                }),
            }),
    {
        match self.host {
            HostInternal::None => Option::None,
            HostInternal::Domain => Option::Some(Host::Domain(
                bytes_slice(&self.serialization, self.host_start, self.host_end),
            )),
            HostInternal::Ipv4(address) => Option::Some(Host::Ipv4(address)),
            HostInternal::Ipv6(address) => Option::Some(Host::Ipv6(address)),
        }
    }

    /// Origin Rust (lib.rs:1236-1241): pub fn domain(&self) -> Option<&str>
    /// Upstream doc (lib.rs:1209-1209):
    ///   If this URL has a host and it is a domain name (not an IP address), return it.
    ///   Non-ASCII domains are punycode-encoded per IDNA if this is the host
    ///   of a special URL, or percent encoded for non-special URLs.
    pub exec fn domain(&self) -> (r: Option<Vec<u8>>)
        requires
            url_invariant(self),
        ensures
            (match r {
                Option::None => self.host != HostInternal::Domain,
                Option::Some(d) => self.host == HostInternal::Domain
                    && (d.view()
                        == self.serialization.view().subrange(
                            self.host_start as int, self.host_end as int)),
            }),
    {
        match self.host {
            HostInternal::Domain => Option::Some(bytes_slice(
                &self.serialization,
                self.host_start,
                self.host_end,
            )),
            _ => Option::None,
        }
    }

    /// Origin Rust (lib.rs:1267-1270): pub fn port(&self) -> Option<u16> { self.port }
    /// Upstream doc (lib.rs:1243-1246):
    ///   Return the port number for this URL, if any.
    ///   Note that default port numbers are never reflected by the serialization,
    ///   use the `port_or_known_default()` method if you want a default port number returned.
    pub exec fn port(&self) -> (r: Option<u16>)
        requires
            url_invariant(self),
        ensures
            r == self.port,
    {
        self.port
    }

    /// Origin Rust (lib.rs:1299-1302): pub fn port_or_known_default(&self) -> Option<u16>
    ///   { self.port.or_else(|| parser::default_port(self.scheme())) }
    /// Upstream doc (lib.rs:1272-1278):
    ///   Return the port number for this URL, or the default port number if it is known.
    ///   This method only knows the default port number
    ///   of the `http`, `https`, `ws`, `wss` and `ftp` schemes.
    ///   For URLs in these schemes, this method always returns `Some(_)`.
    ///   For other schemes, it is the same as `Url::port()`.
    pub exec fn port_or_known_default(&self) -> (r: Option<u16>)
        requires
            url_invariant(self),
        ensures
            r == port_or_known_default_view(self),
    {
        match self.port {
            Option::Some(p) => Option::Some(p),
            Option::None => {
                let scheme_bytes = self.scheme();
                parser::default_port(&scheme_bytes)
            }
        }
    }

    /// Origin Rust (lib.rs:1390-1397): pub fn path(&self) -> &str
    /// Upstream doc (lib.rs:1367-1370):
    ///   Return the path for this URL, as a percent-encoded ASCII string.
    ///   For cannot-be-a-base URLs, this is an arbitrary string that doesn’t start with '/'.
    ///   For other URLs, this starts with a '/' slash
    ///   and continues with slash-separated path segments.
    pub exec fn path(&self) -> (r: Vec<u8>)
        requires
            url_invariant(self),
        ensures
            r.view() == path_view(self),
    {
        let n = url_len32(&self.serialization);
        match (self.query_start, self.fragment_start) {
            (Option::None, Option::None) => bytes_slice(&self.serialization, self.path_start, n),
            (Option::Some(q), _) => bytes_slice(&self.serialization, self.path_start, q),
            (Option::None, Option::Some(f)) => bytes_slice(&self.serialization, self.path_start, f),
        }
    }

    /// Origin Rust (lib.rs:1470-1482): pub fn query(&self) -> Option<&str>
    /// Upstream doc (lib.rs:1446-1446):
    ///   Return this URL’s query string, if any, as a percent-encoded ASCII string.
    pub exec fn query(&self) -> (r: Option<Vec<u8>>)
        requires
            url_invariant(self),
        ensures
            r.is_some() == self.query_start.is_some(),
            self.query_start.is_some()
                ==> r.unwrap().view() == query_content_view(self),
    {
        let n = url_len32(&self.serialization);
        match (self.query_start, self.fragment_start) {
            (Option::None, _) => Option::None,
            (Option::Some(qs), Option::None) => {
                Option::Some(bytes_slice(&self.serialization, qs + 1, n))
            }
            (Option::Some(qs), Option::Some(fs)) => {
                Option::Some(bytes_slice(&self.serialization, qs + 1, fs))
            }
        }
    }

    /// Origin Rust (lib.rs:1544-1549): pub fn fragment(&self) -> Option<&str>
    ///   { self.fragment_start.map(|start| { debug_assert!(self.byte_at(start) == b'#');
    ///     self.slice(start + 1..) }) }
    /// Upstream doc (lib.rs:1512-1524):
    ///   Return this URL’s fragment identifier, if any.
    ///   A fragment is the part of the URL after the `#` symbol.
    ///   The fragment is optional and, if present, contains a fragment identifier
    ///   that identifies a secondary resource, such as a section heading
    ///   of a document.
    ///   In HTML, the fragment identifier is usually the id attribute of a an element
    ///   that is scrolled to on load. Browsers typically will not send the fragment portion
    ///   of a URL to the server.
    ///   **Note:** the parser did *not* percent-encode this component,
    ///   but the input may have been percent-encoded already.
    pub exec fn fragment(&self) -> (r: Option<Vec<u8>>)
        requires
            url_invariant(self),
        ensures
            r.is_some() == self.fragment_start.is_some(),
            self.fragment_start.is_some()
                ==> r.unwrap().view() == fragment_content_view(self),
    {
        match self.fragment_start {
            Option::None => Option::None,
            Option::Some(fs) => {
                let n = url_len32(&self.serialization);
                Option::Some(bytes_slice(&self.serialization, fs + 1, n))
            }
        }
    }
}

/// The truncate + re-append model of std Vec::drain(a..b) over the
/// serialization payload (the port-removal arm of set_port_internal,
/// lib.rs:1910-1916, has no vstd drain spec): the kept prefix is
/// [0, a), the byte tail [b, n) re-lands at a, shifted down by b - a.
/// The model fixes the shape the port/query setters consume: pure
/// prefix preservation, a shifted tail, and the enclosed length
/// arithmetic of the u32 offset domain.
pub exec fn vec_drain_middle(ser: &mut Vec<u8>, a: u32, b: u32)
    requires
        parser::machine_domain(old(ser).view()),
        (a as int) <= (b as int),
        (b as int) <= (old(ser).view().len() as int),
        (old(ser).view().len() as int) <= 0xFFFF_FFFF,
    ensures
        ({
            let o = old(ser).view();
            let f = final(ser).view();
            let shift = (b as int) - (a as int);
            &&& parser::machine_domain(f)
            &&& (f.len() as int) == (o.len() as int) - shift
            &&& (forall|j: int| 0 <= j && j < (a as int)
                ==> f.index(j) == o.index(j))
            &&& (forall|j: int| (b as int) <= j
                && j < (o.len() as int)
                ==> f.index(j - shift) == o.index(j))
            &&& (f == o.subrange(0, a as int)
                + o.subrange(b as int, o.len() as int))
        }),
{
    let n = url_len32(ser);
    let ghost ov = ser.view();
    let mut tail = bytes_slice(ser, b, n);
    proof {
        assert(tail.view() == ov.subrange(b as int,
            ov.len() as int));
        parser::machine_domain_subrange(ov, b as int,
            ov.len() as int);
        assert(parser::machine_domain(tail.view()));
    }
    ser.truncate(a as usize);
    let ghost mid = ser.view();
    proof {
        assert(mid == ov.subrange(0, a as int));
        assert(parser::machine_domain(mid));
        assert(mid.len() + tail.view().len()
            <= ov.len());
    }
    parser::vec_append_bytes(ser, &tail);
    proof {
        let f = ser.view();
        let tv = tail.view();
        assert(f == mid + tv);
        let shift = (b as int) - (a as int);
        // the length arithmetic of the shift
        vstd::seq::lemma_seq_add_len(mid, tv);
        assert((f.len() as int)
            == (ov.len() as int) - shift);
        // the kept prefix is the untouched head
        assert forall|j: int| 0 <= j && j < (a as int)
            implies f.index(j) == ov.index(j) by {
            vstd::seq::lemma_seq_add_index1(mid, tv, j);
            vstd::seq::lemma_seq_subrange_index(ov, 0, a as int, j);
        }
        // the tail re-lands shifted down by b - a
        assert forall|j: int| (b as int) <= j
            && j < (ov.len() as int)
            implies f.index(j - shift) == ov.index(j) by {
            vstd::seq::lemma_seq_add_index2(mid, tv, j - shift);
            vstd::seq::lemma_seq_subrange_index(ov, b as int,
                ov.len() as int, j - (b as int));
            assert(mid.len() == (a as int));
            assert((j - shift) >= (a as int));
            assert(tv.index(j - shift - (a as int))
                == ov.index(j));
        }
    }
}

/* ============================================================
 * The write face (Origin: the set_* mutators of impl Url,
 * lib.rs:1551-2510): the fragment setter first (the lowest stratum --
 * a truncate plus the parse_fragment append); the port/query/scheme
 * setters follow on the drain algebra of later batches. Upstream
 * mutates through Parser::for_setter (mem::take of the serialization,
 * lib.rs:1553-1559): the mirror's ledger keeps the record in place
 * and gives the for-setter Parser a fresh buffer that receives only
 * the parsed payload, value-equal to the upstream moved-buffer parse.
 * ============================================================ */

impl Url {

/// The payload write of the Some arm of set_fragment (lib.rs:1586-1590,
/// split out so each whole-fn check stays inside the solver budget):
/// place the '#' at the fresh fragment slot and append the
/// FRAGMENT-encoded payload through the for-setter Parser face (the
/// mirror's ledger: the Parser's buffer receives the parsed payload,
/// value-equal to the upstream moved-buffer parse). The invariant
/// closes through the parser's fragment-prolong digest over the
/// caller's snapshot of the previous record.
pub exec fn set_fragment_payload_write(
    &mut self,
    snapshot: &Url,
    fb: &[u8],
)
    requires
        parser::base_url_face(snapshot),
        (self.serialization.view().len() as int)
            == parser::base_before_len(snapshot),
        (self.scheme_end as int)
            == (snapshot.scheme_end as int),
        (self.username_end as int)
            == (snapshot.username_end as int),
        (self.host_start as int)
            == (snapshot.host_start as int),
        (self.host_end as int) == (snapshot.host_end as int),
        self.host == snapshot.host,
        self.port == snapshot.port,
        (self.path_start as int) == (snapshot.path_start as int),
        self.query_start == snapshot.query_start,
        (self.fragment_start
            == Option::Some(
                parser::base_before_len(snapshot) as u32)),
        forall|j: int| 0 <= j
            && j < parser::base_before_len(snapshot)
            ==> self.serialization.view().index(j)
                == snapshot.serialization.view().index(j),
        parser::machine_domain(fb@),
        (self.serialization.view().len() as int)
            + 3 * (fb@.len() as int) + 8 <= 0xFFFF_FFFF,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(
            final(self).serialization.view()),
        (final(self).fragment_start
            == Option::Some(
                parser::base_before_len(snapshot) as u32)),
        (final(self).scheme_end as int)
            == (snapshot.scheme_end as int),
        (final(self).username_end as int)
            == (snapshot.username_end as int),
        (final(self).host_start as int)
            == (snapshot.host_start as int),
        (final(self).host_end as int)
            == (snapshot.host_end as int),
        final(self).host == snapshot.host,
        final(self).port == snapshot.port,
        (final(self).path_start as int)
            == (snapshot.path_start as int),
        final(self).query_start == snapshot.query_start,
        (final(self).serialization.view()
            == snapshot.serialization.view().subrange(
                0, parser::base_before_len(snapshot))
                + seq![0x23u8]
                + parser::enc_seq(fb@, parser::EncodeSet::Fragment)),
{
    let ghost pre_h = self.serialization.view();
    let k0 = url_len32(&self.serialization);
    proof {
        assert((k0 as int)
            == parser::base_before_len(snapshot));
        // the kept prefix is exactly the snapshot's own prefix
        assert(pre_h
            == snapshot.serialization.view().subrange(
                0, parser::base_before_len(snapshot))) by {
            let k = parser::base_before_len(snapshot);
            let sv = snapshot.serialization.view();
            assert((pre_h.len() as int) == (sv.subrange(
                0, k).len() as int));
            assert forall|j: int| 0 <= j && j < k
                implies pre_h.index(j) == sv.subrange(0, k).index(j) by {
                vstd::seq::lemma_seq_subrange_index(sv, 0, k, j);
            }
            vstd::seq::lemma_seq_ext_equal(pre_h,
                sv.subrange(0, k));
        }
    }
    self.serialization.push(0x23u8);
    proof {
        assert(self.serialization.view()
            == pre_h.push(0x23u8));
        assert(self.serialization.view()
            == pre_h + seq![0x23u8]);
        parser::machine_domain_byte(0x23u8);
        parser::machine_domain_add(pre_h, seq![0x23u8]);
        assert(parser::machine_domain(self.serialization.view()));
    }
    // the mutation face (lib.rs:1590): the fresh for-setter Parser
    // owns the parsed payload; the record takes it back through the
    // plain append
    let finp = parser::Input { bytes: fb, pos: 0 };
    let mut p = parser::Parser {
        serialization: Vec::new(),
        base_url: Option::None,
        context: parser::Context::Setter,
    };
    proof {
        assert((fb@.len() as int) == (fb.view().len() as int));
        assert(parser::machine_domain(fb@));
        assert(parser::input_rem(&finp) == fb@);
        assert(parser::input_wf(&finp));
        assert((self.serialization.view().len() as int)
            + 3 * (fb@.len() as int)
            <= 0xFFFF_FFFF);
        assert(p.serialization.view().len() == 0);
        assert(p.serialization.view().len()
            + 3 * (parser::input_rem(&finp).len() as int)
            <= 0xFFFF_FFFF);
    }
    p.parse_fragment(finp);
    proof {
        let penc = p.serialization.view();
        let enc = parser::enc_seq(fb@, parser::EncodeSet::Fragment);
        assert(penc == Seq::empty() + enc);
        assert(penc == enc);
        parser::enc_seq_machine(fb@, parser::EncodeSet::Fragment);
        assert(parser::machine_domain(penc));
        // the append closes inside the u32 offset domain
        parser::enc_seq_len_bound(fb@, parser::EncodeSet::Fragment);
        assert((p.serialization.view().len() as int)
            <= 3 * (fb@.len() as int));
        assert((self.serialization.view().len() as int)
            + (p.serialization.view().len() as int)
            <= 0xFFFF_FFFF);
    }
    parser::vec_append_bytes(&mut self.serialization,
        &p.serialization);
    proof {
        let fin = self.serialization.view();
        let enc = parser::enc_seq(fb@, parser::EncodeSet::Fragment);
        let sv = snapshot.serialization.view();
        assert(fin == (pre_h + seq![0x23u8]) + enc);
        assert(fin == sv.subrange(
            0, parser::base_before_len(snapshot))
            + seq![0x23u8] + enc);
        // the length stays in the u32 offset domain
        vstd::seq::lemma_seq_add_len(pre_h, seq![0x23u8]);
        vstd::seq::lemma_seq_add_len(pre_h + seq![0x23u8], enc);
        parser::enc_seq_len_bound(fb@, parser::EncodeSet::Fragment);
        assert((fin.len() as int) <= 0xFFFF_FFFF);
        assert((fin.len() as int) >= (k0 as int) + 1);
        // the prefix below the fragment slot is the snapshot's own
        assert forall|j: int| 0 <= j && j < (k0 as int)
            implies fin.index(j) == sv.index(j) by {
            vstd::seq::lemma_seq_add_index1(
                pre_h + seq![0x23u8], enc, j);
            vstd::seq::lemma_seq_add_index1(pre_h, seq![0x23u8], j);
            assert(fin.index(j) == pre_h.index(j));
            vstd::seq::lemma_seq_subrange_index(sv,
                0, parser::base_before_len(snapshot), j);
            assert(pre_h.index(j)
                == sv.subrange(
                    0, parser::base_before_len(snapshot)).index(j));
        }
        // the '#' slot at the fragment position
        assert(fin.index(k0 as int) == 0x23u8) by {
            vstd::seq::lemma_seq_add_index1(
                pre_h + seq![0x23u8], enc, k0 as int);
            vstd::seq::lemma_seq_add_index2(pre_h,
                seq![0x23u8], k0 as int);
        }
        // the record carry closes the whole invariant
        parser::fragment_prolong_carry(snapshot, self, k0 as int);
    }
}

/// Origin Rust (lib.rs:1569-1603): pub fn set_fragment(&mut self,
///   fragment: Option<&str>) -- drop any previous fragment, write the
/// '#' and the FRAGMENT-encoded payload (the Some face), or drop the
/// fragment slot and strip the trailing spaces of an opaque path (the
/// None face -- the whatwg "potentially strip trailing spaces from an
/// opaque path" step). The &str face is the byte slice (ledger 1);
/// the debug assert on the previous '#' (lib.rs:1582) is the
/// invariant's own byte pin; to_u32 on the serialization length
/// (lib.rs:1586) stays in the u32 offset domain under the budget. The
/// base-input cone is the parser's base_url_face: its terminus
/// conjunct documents the only slot the '#' placement reads (the
/// record-carry face shared with the base-merge arms).
pub exec fn set_fragment(&mut self, fragment: Option<&[u8]>)
    requires
        parser::base_url_face(self),
        (self.serialization.view().len() as int)
            + 3 * (match fragment {
                Option::Some(fb) => (fb@.len() as int),
                Option::None => 0int,
            }) + 8 <= 0xFFFF_FFFF,
        (match fragment {
            Option::Some(fb) => parser::machine_domain(fb@),
            Option::None => true,
        }),
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        (final(self).scheme_end as int)
            == (old(self).scheme_end as int),
        (final(self).username_end as int)
            == (old(self).username_end as int),
        (final(self).host_start as int)
            == (old(self).host_start as int),
        (final(self).host_end as int)
            == (old(self).host_end as int),
        final(self).host == old(self).host,
        final(self).port == old(self).port,
        (final(self).path_start as int)
            == (old(self).path_start as int),
        final(self).query_start == old(self).query_start,
        (fragment.is_some() ==> ({
            let fb = fragment.unwrap();
            &&& final(self).fragment_start
                == Option::Some(
                    parser::base_before_len(old(self)) as u32)
            &&& final(self).serialization.view()
                == old(self).serialization.view().subrange(
                    0, parser::base_before_len(old(self)))
                    + seq![0x23u8]
                    + parser::enc_seq(fb@, parser::EncodeSet::Fragment)
        })),
        (fragment.is_none() ==> ({
            let n = old(self).serialization.view().len() as int;
            let olfs = old(self).fragment_start;
            &&& final(self).fragment_start.is_none()
            &&& exists|cut: int| 0 <= cut && cut <= n
                && final(self).serialization.view()
                    == old(self).serialization.view().subrange(0, cut)
                && (forall|j: int| cut <= j && j < n
                    ==> (old(self).serialization.view().index(j)
                            == 0x20u8
                        || (olfs.is_some()
                            && (olfs.unwrap() as int) <= j)))
        })),
{
    let ghost old_view = self.serialization.view();
    // the decomposed snapshot of the previous record: every component
    // field is Copy, the byte payload rides its own copy (the record
    // carries below consume the snapshot against the final state)
    let snapshot = Url {
        serialization: parser::bytes_own(&self.serialization),
        scheme_end: self.scheme_end,
        username_end: self.username_end,
        host_start: self.host_start,
        host_end: self.host_end,
        host: self.host,
        port: self.port,
        path_start: self.path_start,
        query_start: self.query_start,
        fragment_start: self.fragment_start,
    };
    proof {
        assert(snapshot.serialization.view() == old_view);
        assert(url_invariant(&snapshot));
        assert(parser::base_url_face(&snapshot));
    }
    // drop any previous fragment (lib.rs:1581-1584)
    match self.fragment_start {
        Option::Some(fs) => {
            proof {
                assert((fs as int) < (old_view.len() as int));
                assert((fs as int)
                    == parser::base_before_len(&snapshot));
            }
            self.serialization.truncate(fs as usize);
            proof {
                let t1 = self.serialization.view();
                assert(t1 == old_view.subrange(0, fs as int));
                assert(parser::machine_domain(t1));
            }
        }
        Option::None => {}
    }
    let ghost mid_view = self.serialization.view();
    proof {
        assert((mid_view.len() as int)
            == parser::base_before_len(&snapshot));
        assert(mid_view.len() <= old_view.len());
        assert(mid_view
            == old_view.subrange(0, mid_view.len() as int));
    }
    match fragment {
        Option::Some(fb) => {
            // the fragment slot (lib.rs:1586), then the split-out
            // '#' + payload write over the snapshot
            let k0 = url_len32(&self.serialization);
            proof {
                assert((k0 as int)
                    == (mid_view.len() as int));
                assert((k0 as int)
                    == parser::base_before_len(&snapshot));
            }
            self.fragment_start = Option::Some(k0);
            self.set_fragment_payload_write(&snapshot, fb);
            proof {
                // the value face instantiates at the snapshot (whose
                // bytes and components are the entry record's own)
                assert(snapshot.serialization.view() == old_view);
                assert(snapshot.fragment_start
                    == old(self).fragment_start);
                assert(parser::base_before_len(&snapshot)
                    == parser::base_before_len(old(self)));
                assert(final(self).serialization.view()
                    == old_view.subrange(
                        0, parser::base_before_len(&snapshot))
                        + seq![0x23u8]
                        + parser::enc_seq(fb@,
                            parser::EncodeSet::Fragment));
                assert((final(self).fragment_start.unwrap() as int)
                    == parser::base_before_len(&snapshot));
            }
        }
        Option::None => {
            // the None face (lib.rs:1596-1598): drop the slot, then
            // the opaque-path trailing-space strip
            self.fragment_start = Option::None;
            proof {
                // the post-drop state keeps the invariant through
                // the none-arm record carry (the fragment drop is the
                // same copy boundary as the relative resolution's
                // None arm)
                assert forall|j: int|
                    0 <= j && j < (mid_view.len() as int)
                    implies self.serialization.view().index(j)
                        == old_view.index(j) by {
                    vstd::seq::lemma_seq_subrange_index(old_view,
                        0, mid_view.len() as int, j);
                }
                if has_authority_view(&snapshot) {
                    parser::rel_carry_none_authority(&snapshot,
                        self, mid_view.len() as int);
                } else {
                    parser::rel_carry_none_anarchist(&snapshot,
                        self, mid_view.len() as int);
                }
                assert(url_invariant(self));
            }
            self.strip_trailing_spaces_from_opaque_path();
            proof {
                // the composed cut witness: the strip ran on the
                // post-drop prefix, so its cut splits the old view
                // into [0, cut) kept bytes and a tail that is either
                // the strip's space run (below the drop boundary) or
                // the old fragment interior (at or above it)
                let ov = old_view;
                let nold = ov.len() as int;
                let k0 = parser::base_before_len(&snapshot);
                let cut_s = choose|c: int| 0 <= c && c <= k0
                    && self.serialization.view()
                        == ov.subrange(0, k0).subrange(0, c)
                    && (forall|j: int| c <= j && j < k0
                        ==> ov.subrange(0, k0).index(j) == 0x20u8);
                assert(self.serialization.view()
                    == ov.subrange(0, cut_s)) by {
                    vstd::seq::lemma_seq_subrange_composition(ov,
                        0, k0, 0, cut_s);
                }
                assert(forall|j: int| cut_s <= j && j < nold
                    ==> (ov.index(j) == 0x20u8
                        || (old(self).fragment_start.is_some()
                            && (old(self).fragment_start.unwrap()
                                as int) <= j))) by {
                    if old(self).fragment_start.is_some() {
                        assert(k0
                            == (old(self).fragment_start.unwrap()
                                as int));
                    } else {
                        assert(k0 == nold);
                    }
                }
                assert(final(self).fragment_start.is_none());
            }
        }
    }
}

/// The payload write of the Some arm of set_query (lib.rs:1645-1653,
/// split out so each whole-fn check stays inside the solver budget):
/// place the '?' at the fresh query slot and append the
/// QUERY/SPECIAL_QUERY-encoded payload through the for-setter Parser
/// face (the mirror's ledger: the Parser's buffer receives the parsed
/// payload, value-equal to the upstream moved-buffer parse). The
/// fragment slot stays empty (the entry face's take already removed
/// it); the caller's snapshot pins the entry record. The '#' stop of
/// the URL-parser context does not apply here (the QueryPartIter's
/// is_url_parser gate is false in the for-setter Parser), so the
/// payload encodes whole -- parse_query_setter is that face.
pub exec fn set_query_payload_write(
    &mut self,
    snapshot: &Url,
    qb: &[u8],
)
    requires
        parser::base_url_face(snapshot),
        (self.serialization.view().len() as int)
            == parser::base_before_query_len(snapshot),
        (self.scheme_end as int)
            == (snapshot.scheme_end as int),
        (self.username_end as int)
            == (snapshot.username_end as int),
        (self.host_start as int)
            == (snapshot.host_start as int),
        (self.host_end as int) == (snapshot.host_end as int),
        self.host == snapshot.host,
        self.port == snapshot.port,
        (self.path_start as int) == (snapshot.path_start as int),
        self.query_start == Option::Some(
            parser::base_before_query_len(snapshot) as u32),
        self.fragment_start.is_none(),
        forall|j: int| 0 <= j
            && j < parser::base_before_query_len(snapshot)
            ==> self.serialization.view().index(j)
                == snapshot.serialization.view().index(j),
        parser::machine_domain(qb@),
        (self.serialization.view().len() as int)
            + 3 * (qb@.len() as int) + 3 <= 0xFFFF_FFFF,
    ensures
        parser::machine_domain(
            final(self).serialization.view()),
        (final(self).serialization.view()
            == ({
                let k = parser::base_before_query_len(snapshot);
                let set = if parser::is_special(
                    parser::scheme_type_of(
                        snapshot.serialization.view().subrange(
                            0, snapshot.scheme_end as int))) {
                    parser::EncodeSet::SpecialQuery
                } else {
                    parser::EncodeSet::Query
                };
                snapshot.serialization.view().subrange(0, k)
                    + seq![0x3Fu8]
                    + parser::enc_seq(qb@, set)
            })),
        (final(self).serialization.view().index(
            parser::base_before_query_len(snapshot)) == 0x3Fu8),
        (final(self).scheme_end as int)
            == (snapshot.scheme_end as int),
        (final(self).username_end as int)
            == (snapshot.username_end as int),
        (final(self).host_start as int)
            == (snapshot.host_start as int),
        (final(self).host_end as int)
            == (snapshot.host_end as int),
        final(self).host == snapshot.host,
        final(self).port == snapshot.port,
        (final(self).path_start as int)
            == (snapshot.path_start as int),
        final(self).query_start == Option::Some(
            parser::base_before_query_len(snapshot) as u32),
        final(self).fragment_start.is_none(),
        (final(self).serialization.view().len() as int)
            <= 0xFFFF_FFFF,
{
    let ghost pre_h = self.serialization.view();
    let k0 = url_len32(&self.serialization);
    proof {
        assert((k0 as int)
            == parser::base_before_query_len(snapshot));
        // the kept prefix is exactly the snapshot's own prefix
        let k = parser::base_before_query_len(snapshot);
        let sv = snapshot.serialization.view();
        assert(pre_h == sv.subrange(0, k)) by {
            assert((pre_h.len() as int)
                == (sv.subrange(0, k).len() as int));
            assert forall|j: int| 0 <= j && j < k
                implies pre_h.index(j) == sv.subrange(0, k).index(j) by {
                vstd::seq::lemma_seq_subrange_index(sv, 0, k, j);
            }
            vstd::seq::lemma_seq_ext_equal(pre_h,
                sv.subrange(0, k));
        }
        parser::machine_domain_subrange(sv, 0, k);
        assert(parser::machine_domain(pre_h));
    }
    // the '?' slot (lib.rs:1645)
    self.serialization.push(0x3Fu8);
    proof {
        assert(self.serialization.view() == pre_h.push(0x3Fu8));
        assert(self.serialization.view()
            == pre_h + seq![0x3Fu8]);
        parser::machine_domain_byte(0x3Fu8);
        parser::machine_domain_add(pre_h, seq![0x3Fu8]);
        assert(parser::machine_domain(self.serialization.view()));
    }
    // lib.rs:1647: the record's own scheme picks the encode set
    let scheme_bytes = bytes_slice(&self.serialization, 0,
        self.scheme_end);
    let st = parser::scheme_type_from(&scheme_bytes);
    proof {
        assert(scheme_bytes.view()
            == snapshot.serialization.view().subrange(
                0, snapshot.scheme_end as int));
        assert(st == parser::scheme_type_of(
            snapshot.serialization.view().subrange(
                0, snapshot.scheme_end as int)));
    }
    // the mutation face (lib.rs:1648-1652): the fresh for-setter
    // Parser owns the parsed payload; the record takes it back
    // through the plain append
    let finp = parser::Input { bytes: qb, pos: 0 };
    let mut p = parser::Parser {
        serialization: Vec::new(),
        base_url: Option::None,
        context: parser::Context::Setter,
    };
    proof {
        assert((qb@.len() as int) == (qb.view().len() as int));
        assert(parser::machine_domain(qb@));
        assert(parser::input_rem(&finp) == qb@);
        assert(parser::input_wf(&finp));
        assert(p.serialization.view().len() == 0);
        assert(p.serialization.view().len()
            + 3 * (parser::input_rem(&finp).len() as int)
            <= 0xFFFF_FFFF);
    }
    p.parse_query_setter(st, finp);
    proof {
        let penc = p.serialization.view();
        let set = if parser::is_special(st) {
            parser::EncodeSet::SpecialQuery
        } else {
            parser::EncodeSet::Query
        };
        let enc = parser::enc_seq(qb@, set);
        assert(penc == Seq::empty() + enc);
        assert(penc == enc);
        parser::enc_seq_machine(qb@, set);
        assert(parser::machine_domain(penc));
        // the append closes inside the u32 offset domain
        parser::enc_seq_len_bound(qb@, set);
        assert((p.serialization.view().len() as int)
            <= 3 * (qb@.len() as int));
        assert((self.serialization.view().len() as int)
            + (p.serialization.view().len() as int)
            <= 0xFFFF_FFFF);
    }
    parser::vec_append_bytes(&mut self.serialization,
        &p.serialization);
    proof {
        let fin = self.serialization.view();
        let set = if parser::is_special(st) {
            parser::EncodeSet::SpecialQuery
        } else {
            parser::EncodeSet::Query
        };
        let enc = parser::enc_seq(qb@, set);
        assert(fin == (pre_h + seq![0x3Fu8]) + enc);
        // the length stays in the u32 offset domain
        vstd::seq::lemma_seq_add_len(pre_h, seq![0x3Fu8]);
        vstd::seq::lemma_seq_add_len(pre_h + seq![0x3Fu8], enc);
        parser::enc_seq_len_bound(qb@, set);
        assert((fin.len() as int) <= 0xFFFF_FFFF);
        assert((fin.len() as int) >= (k0 as int) + 1);
        // the '?' slot at the boundary
        assert(fin.index(k0 as int) == 0x3Fu8) by {
            vstd::seq::lemma_seq_add_index1(
                pre_h + seq![0x3Fu8], enc, k0 as int);
            vstd::seq::lemma_seq_add_index2(pre_h,
                seq![0x3Fu8], k0 as int);
        }
    }
}

/// The fragment-restore write of set_query (lib.rs:1606-1613,
/// restore_already_parsed_fragment, split out so each whole-fn check
/// stays inside the solver budget): re-place the '#' at the current
/// serialization end and re-append the already-parsed fragment content
/// verbatim (the entry face's take was a pure byte move, symmetric to
/// the plain '#' + payload append of restore's own debug assert at
/// lib.rs:1609).
pub exec fn set_query_restore_write(&mut self, fb: &[u8])
    requires
        parser::machine_domain(self.serialization.view()),
        self.fragment_start.is_none(),
        (self.serialization.view().len() as int)
            + (fb@.len() as int) + 1 <= 0xFFFF_FFFF,
        parser::machine_domain(fb@),
    ensures
        parser::machine_domain(
            final(self).serialization.view()),
        (final(self).serialization.view()
            == old(self).serialization.view()
                + seq![0x23u8] + fb@),
        (final(self).serialization.view().index(
            (old(self).serialization.view().len() as int))
            == 0x23u8),
        final(self).query_start == old(self).query_start,
        (final(self).fragment_start
            == Option::Some(
                (old(self).serialization.view().len() as int) as u32)),
        (final(self).scheme_end as int)
            == (old(self).scheme_end as int),
        (final(self).username_end as int)
            == (old(self).username_end as int),
        (final(self).host_start as int)
            == (old(self).host_start as int),
        (final(self).host_end as int)
            == (old(self).host_end as int),
        final(self).host == old(self).host,
        final(self).port == old(self).port,
        (final(self).path_start as int)
            == (old(self).path_start as int),
        (final(self).serialization.view().len() as int)
            <= 0xFFFF_FFFF,
        (forall|j: int| 0 <= j
            && j < (old(self).serialization.view().len() as int)
            ==> final(self).serialization.view().index(j)
                == old(self).serialization.view().index(j)),
{
    let ghost pre_h = self.serialization.view();
    let k0 = url_len32(&self.serialization);
    // lib.rs:1609: the slot at the current serialization end
    self.fragment_start = Option::Some(k0);
    self.serialization.push(0x23u8);
    proof {
        assert(self.serialization.view() == pre_h.push(0x23u8));
        assert(self.serialization.view()
            == pre_h + seq![0x23u8]);
        parser::machine_domain_byte(0x23u8);
        parser::machine_domain_add(pre_h, seq![0x23u8]);
        assert(parser::machine_domain(self.serialization.view()));
    }
    parser::vec_append_bytes(&mut self.serialization, fb);
    proof {
        let fin = self.serialization.view();
        assert(fin == (pre_h + seq![0x23u8]) + fb@);
        vstd::seq::lemma_seq_add_len(pre_h, seq![0x23u8]);
        vstd::seq::lemma_seq_add_len(pre_h + seq![0x23u8], fb@);
        assert((fin.len() as int) <= 0xFFFF_FFFF);
        assert forall|j: int| 0 <= j && j < (k0 as int)
            implies fin.index(j) == pre_h.index(j) by {
            vstd::seq::lemma_seq_add_index1(
                pre_h + seq![0x23u8], fb@, j);
            vstd::seq::lemma_seq_add_index1(pre_h, seq![0x23u8], j);
        }
        assert(fin.index(k0 as int) == 0x23u8) by {
            vstd::seq::lemma_seq_add_index1(
                pre_h + seq![0x23u8], fb@, k0 as int);
            vstd::seq::lemma_seq_add_index2(pre_h,
                seq![0x23u8], k0 as int);
        }
    }
}

/// The Some arm of set_query (lib.rs:1645-1653 plus the restore at
/// 1661-1665, split out so each whole-fn check stays inside the
/// solver budget): the fresh query slot plus the '?' and the
/// QUERY/SPECIAL_QUERY payload write, then the '#' + moved-bytes
/// restore when the entry record carried a fragment. The entry-face
/// facts ride the caller's snapshot; the take-tie premise carries the
/// moved fragment content.
pub exec fn set_query_some_arm(
    &mut self,
    snapshot: &Url,
    qb: &[u8],
    frag: &Option<Vec<u8>>,
)
    requires
        parser::base_url_face(snapshot),
        (self.serialization.view().len() as int)
            == parser::base_before_query_len(snapshot),
        (self.serialization.view().len() as int)
            <= 0xFFFF_FFFF,
        (self.scheme_end as int) == (snapshot.scheme_end as int),
        (self.username_end as int)
            == (snapshot.username_end as int),
        (self.host_start as int) == (snapshot.host_start as int),
        (self.host_end as int) == (snapshot.host_end as int),
        self.host == snapshot.host,
        self.port == snapshot.port,
        (self.path_start as int) == (snapshot.path_start as int),
        self.fragment_start.is_none(),
        parser::machine_domain(self.serialization.view()),
        forall|j: int| 0 <= j
            && j < parser::base_before_query_len(snapshot)
            ==> self.serialization.view().index(j)
                == snapshot.serialization.view().index(j),
        parser::machine_domain(qb@),
        (snapshot.serialization.view().len() as int)
            + 3 * (qb@.len() as int) + 8 <= 0xFFFF_FFFF,
        (frag.is_some()
            == snapshot.fragment_start.is_some()),
        (frag.is_some()
            ==> frag.unwrap().view()
                == fragment_content_view(snapshot)),
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        (final(self).scheme_end as int)
            == (snapshot.scheme_end as int),
        (final(self).username_end as int)
            == (snapshot.username_end as int),
        (final(self).host_start as int)
            == (snapshot.host_start as int),
        (final(self).host_end as int)
            == (snapshot.host_end as int),
        final(self).host == snapshot.host,
        final(self).port == snapshot.port,
        (final(self).path_start as int)
            == (snapshot.path_start as int),
        final(self).query_start == Option::Some(
            parser::base_before_query_len(snapshot) as u32),
        query_content_view(final(self))
            == ({
                let set = if parser::is_special(
                    parser::scheme_type_of(
                        snapshot.serialization.view().subrange(
                            0, snapshot.scheme_end as int))) {
                    parser::EncodeSet::SpecialQuery
                } else {
                    parser::EncodeSet::Query
                };
                parser::enc_seq(qb@, set)
            }),
        (snapshot.fragment_start.is_none()
            ==> final(self).fragment_start.is_none()),
        (snapshot.fragment_start.is_none()
            ==> final(self).serialization.view()
                == snapshot.serialization.view().subrange(
                    0, parser::base_before_query_len(snapshot))
                    + seq![0x3Fu8]
                    + ({
                        let set = if parser::is_special(
                            parser::scheme_type_of(
                                snapshot.serialization.view()
                                    .subrange(0,
                                        snapshot.scheme_end as int))) {
                            parser::EncodeSet::SpecialQuery
                        } else {
                            parser::EncodeSet::Query
                        };
                        parser::enc_seq(qb@, set)
                    })),
        (snapshot.fragment_start.is_some()
            ==> final(self).fragment_start
                == Option::Some((({
                    let set = if parser::is_special(
                        parser::scheme_type_of(
                            snapshot.serialization.view().subrange(
                                0, snapshot.scheme_end as int))) {
                        parser::EncodeSet::SpecialQuery
                    } else {
                        parser::EncodeSet::Query
                    };
                    let enc = parser::enc_seq(qb@, set);
                    (parser::base_before_query_len(snapshot) + 1
                        + (enc.len() as int)) as u32
                })))),
        (snapshot.fragment_start.is_some()
            ==> final(self).serialization.view()
                == snapshot.serialization.view().subrange(
                    0, parser::base_before_query_len(snapshot))
                    + seq![0x3Fu8]
                    + ({
                        let set = if parser::is_special(
                            parser::scheme_type_of(
                                snapshot.serialization.view()
                                    .subrange(0,
                                        snapshot.scheme_end as int))) {
                            parser::EncodeSet::SpecialQuery
                        } else {
                            parser::EncodeSet::Query
                        };
                        parser::enc_seq(qb@, set)
                    })
                    + seq![0x23u8]
                    + fragment_content_view(snapshot)),
        (snapshot.fragment_start.is_some()
            ==> fragment_content_view(final(self))
                == fragment_content_view(snapshot)),
{
    let ghost d0 = parser::base_before_query_len(snapshot);
    proof {
        assert((self.serialization.view().len() as int) == d0);
        assert(d0 + 3 * (qb@.len() as int) + 4
            <= 0xFFFF_FFFF);
    }
    // lib.rs:1645: the fresh query slot
    let k0 = url_len32(&self.serialization);
    proof {
        assert((k0 as int) == d0);
    }
    self.query_start = Option::Some(k0);
    self.set_query_payload_write(&snapshot, qb);
    // the fragment restore (lib.rs:1661-1665): '#' plus the moved
    // bytes, verbatim
    match frag {
        Option::Some(fb) => {
            let ghost d = parser::base_before_query_len(snapshot);
            let ghost sv = snapshot.serialization.view();
            let ghost set = if parser::is_special(
                parser::scheme_type_of(sv.subrange(
                    0, snapshot.scheme_end as int))) {
                parser::EncodeSet::SpecialQuery
            } else {
                parser::EncodeSet::Query
            };
            let ghost enc = parser::enc_seq(qb@, set);
            proof {
                // the payload budget closes through the fragment
                // span the take exposed
                parser::enc_seq_len_bound(qb@, set);
                let n = sv.len() as int;
                let fsv = snapshot.fragment_start.unwrap() as int;
                assert(d <= fsv);
                assert((fb.view().len() as int) == n - fsv - 1) by {
                    vstd::seq::lemma_seq_subrange_len(sv, fsv + 1,
                        n);
                }
                assert((self.serialization.view().len() as int)
                    + (fb.view().len() as int) + 1
                    <= 0xFFFF_FFFF);
                assert(parser::machine_domain(fb.view()));
            }
            self.set_query_restore_write(&fb);
            proof {
                let fb_view = fb.view();
                // the final serialization shape and the fragment
                // slot position
                let payload_len = d + 1 + (enc.len() as int);
                assert((self.fragment_start.unwrap() as int)
                    == payload_len) by {
                    vstd::seq::lemma_seq_subrange_len(sv, 0, d);
                    vstd::seq::lemma_seq_add_len(
                        sv.subrange(0, d), seq![0x3Fu8]);
                    vstd::seq::lemma_seq_add_len(
                        sv.subrange(0, d) + seq![0x3Fu8], enc);
                }
                vstd::seq::lemma_seq_add_len(
                    sv.subrange(0, d) + seq![0x3Fu8] + enc,
                    seq![0x23u8]);
                vstd::seq::lemma_seq_add_len(
                    sv.subrange(0, d) + seq![0x3Fu8] + enc
                        + seq![0x23u8], fb_view);
                let fin = self.serialization.view();
                assert((self.fragment_start.unwrap() as int)
                    < (fin.len() as int));
                assert(fin
                    == sv.subrange(0, d) + seq![0x3Fu8]
                        + enc + seq![0x23u8] + fb_view);
                // the prefix below the boundary is the entry's own
                // (the restore only appends)
                assert forall|j: int| 0 <= j && j < d
                    implies fin.index(j) == sv.index(j) by {
                    vstd::seq::lemma_seq_add_index1(
                        sv.subrange(0, d) + seq![0x3Fu8]
                            + enc + seq![0x23u8], fb_view, j);
                    vstd::seq::lemma_seq_add_index1(
                        sv.subrange(0, d) + seq![0x3Fu8] + enc,
                        seq![0x23u8], j);
                    vstd::seq::lemma_seq_add_index1(
                        sv.subrange(0, d) + seq![0x3Fu8], enc, j);
                    vstd::seq::lemma_seq_add_index1(
                        sv.subrange(0, d), seq![0x3Fu8], j);
                    vstd::seq::lemma_seq_add_index1(sv,
                        seq![0x3Fu8], j);
                }
                // the record carry: query at the boundary, the
                // fragment strictly behind it with the '#' pin
                if has_authority_view(&snapshot) {
                    parser::rel_carry_query_authority(
                        &snapshot, self, d);
                } else {
                    parser::rel_carry_query_anarchist(
                        &snapshot, self, d);
                }
                assert(url_invariant(self));
                // the value faces: the query content is the encoded
                // payload, the fragment content the moved bytes
                let pfx = sv.subrange(0, d) + seq![0x3Fu8];
                assert(query_content_view(self) == enc) by {
                    assert forall|j: int|
                        #![trigger query_content_view(self).index(j)]
                        0 <= j && j < (enc.len() as int)
                        implies query_content_view(self).index(j)
                            == enc.index(j) by {
                        let qs_u = d;
                        let s0 = self.serialization.view();
                        vstd::seq::lemma_seq_subrange_index(
                            s0, qs_u + 1,
                            qs_u + 1 + (enc.len() as int), j);
                        vstd::seq::lemma_seq_add_index2(pfx,
                            enc + seq![0x23u8] + fb_view,
                            qs_u + 1 + j);
                    }
                    vstd::seq::lemma_seq_ext_equal(
                        query_content_view(self), enc);
                };
                assert(fragment_content_view(self) == fb_view) by {
                    let fstart = self.fragment_start.unwrap() as int;
                    assert(fstart == d + 1 + (enc.len() as int));
                    assert forall|j: int|
                        #![trigger fragment_content_view(self).index(j)]
                        0 <= j && j < (fb_view.len() as int)
                        implies fragment_content_view(self).index(j)
                            == fb_view.index(j) by {
                        let s0 = self.serialization.view();
                        vstd::seq::lemma_seq_subrange_index(
                            s0, fstart + 1, s0.len() as int, j);
                        vstd::seq::lemma_seq_add_index2(
                            sv.subrange(0, d) + seq![0x3Fu8] + enc,
                            seq![0x23u8] + fb_view, fstart + 1 + j);
                        vstd::seq::lemma_seq_add_index2(
                            seq![0x23u8], fb_view, 1 + j);
                    }
                    vstd::seq::lemma_seq_ext_equal(
                        fragment_content_view(self), fb_view);
                };
            }
        }
        Option::None => {
            proof {
                let d = parser::base_before_query_len(snapshot);
                // the query carry with the empty fragment slot: the
                // record keeps the entry's own prefix below the
                // boundary
                let fin = self.serialization.view();
                let s1 = if parser::is_special(
                    parser::scheme_type_of(
                        snapshot.serialization.view().subrange(
                            0, snapshot.scheme_end as int))) {
                    parser::EncodeSet::SpecialQuery
                } else {
                    parser::EncodeSet::Query
                };
                let enc1 = parser::enc_seq(qb@, s1);
                assert forall|j: int| 0 <= j && j < d
                    implies fin.index(j)
                        == snapshot.serialization.view().index(j) by {
                    vstd::seq::lemma_seq_add_index1(
                        snapshot.serialization.view().subrange(
                            0, d) + seq![0x3Fu8], enc1, j);
                    vstd::seq::lemma_seq_add_index1(
                        snapshot.serialization.view().subrange(0, d),
                        seq![0x3Fu8], j);
                    vstd::seq::lemma_seq_subrange_index(
                        snapshot.serialization.view(), 0, d, j);
                }
                // the '?' slot at the boundary and the fragment
                // slot keep the carry's premises
                assert(fin.index(d) == 0x3Fu8);
                if has_authority_view(&snapshot) {
                    parser::rel_carry_query_authority(
                        &snapshot, self, d);
                } else {
                    parser::rel_carry_query_anarchist(
                        &snapshot, self, d);
                }
                assert(url_invariant(self));
                // the value face: the query content is the encoded
                // payload (the '?' at the boundary, the payload to
                // the end)
                assert(query_content_view(self) == enc1) by {
                    assert forall|j: int|
                        #![trigger query_content_view(self).index(j)]
                        0 <= j && j < (enc1.len() as int)
                        implies query_content_view(self).index(j)
                            == enc1.index(j) by {
                        let s0 = self.serialization.view();
                        let qsu = d;
                        let svq = snapshot.serialization.view();
                        assert(s0 == svq.subrange(0, qsu)
                            + seq![0x3Fu8] + enc1);
                        vstd::seq::lemma_seq_subrange_index(
                            s0, qsu + 1, s0.len() as int, j);
                        vstd::seq::lemma_seq_add_index2(
                            svq.subrange(0, qsu) + seq![0x3Fu8], enc1,
                            qsu + 1 + j);
                    }
                    vstd::seq::lemma_seq_ext_equal(
                        query_content_view(self), enc1);
                };
            }
        }
    }
}

/// The None arm of set_query (lib.rs:1654-1663 plus the restore at
/// 1665, split out so each whole-fn check stays inside the solver
/// budget): keep the query slot empty, restore the taken fragment at
/// the boundary when the entry record carried one, else run the
/// opaque-path strip over the drop-state record.
pub exec fn set_query_none_arm(
    &mut self,
    snapshot: &Url,
    frag: &Option<Vec<u8>>,
)
    requires
        parser::base_url_face(snapshot),
        (self.serialization.view().len() as int)
            == parser::base_before_query_len(snapshot),
        (self.serialization.view().len() as int)
            <= 0xFFFF_FFFF,
        (self.scheme_end as int) == (snapshot.scheme_end as int),
        (self.username_end as int)
            == (snapshot.username_end as int),
        (self.host_start as int) == (snapshot.host_start as int),
        (self.host_end as int) == (snapshot.host_end as int),
        self.host == snapshot.host,
        self.port == snapshot.port,
        (self.path_start as int) == (snapshot.path_start as int),
        self.query_start.is_none(),
        self.fragment_start.is_none(),
        parser::machine_domain(self.serialization.view()),
        forall|j: int| 0 <= j
            && j < parser::base_before_query_len(snapshot)
            ==> self.serialization.view().index(j)
                == snapshot.serialization.view().index(j),
        (frag.is_some()
            == snapshot.fragment_start.is_some()),
        (frag.is_some()
            ==> frag.unwrap().view()
                == fragment_content_view(snapshot)),
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        (final(self).scheme_end as int)
            == (snapshot.scheme_end as int),
        (final(self).username_end as int)
            == (snapshot.username_end as int),
        (final(self).host_start as int)
            == (snapshot.host_start as int),
        (final(self).host_end as int)
            == (snapshot.host_end as int),
        final(self).host == snapshot.host,
        final(self).port == snapshot.port,
        (final(self).path_start as int)
            == (snapshot.path_start as int),
        final(self).query_start.is_none(),
        (snapshot.fragment_start.is_some()
            ==> final(self).fragment_start
                == Option::Some(
                    parser::base_before_query_len(snapshot) as u32)),
        (snapshot.fragment_start.is_some()
            ==> final(self).serialization.view()
                == snapshot.serialization.view().subrange(
                    0, parser::base_before_query_len(snapshot))
                    + seq![0x23u8]
                    + fragment_content_view(snapshot)),
        (snapshot.fragment_start.is_some()
            ==> fragment_content_view(final(self))
                == fragment_content_view(snapshot)),
        (snapshot.fragment_start.is_none()
            ==> final(self).fragment_start.is_none()),
        (snapshot.fragment_start.is_none()
            ==> exists|cut: int| 0 <= cut
                && cut <= parser::base_before_query_len(snapshot)
                && final(self).serialization.view()
                    == snapshot.serialization.view().subrange(0, cut)
                && (forall|j: int| cut <= j
                    && j < parser::base_before_query_len(snapshot)
                    ==> snapshot.serialization.view().index(j)
                        == 0x20u8)),
{
    let ghost d = parser::base_before_query_len(snapshot);
    let ghost sv = snapshot.serialization.view();
    let ghost cur = self.serialization.view();
    proof {
        assert(cur == sv.subrange(0, d)) by {
            assert forall|j: int| 0 <= j && j < d
                implies cur.index(j) == sv.subrange(0, d).index(j) by {
                vstd::seq::lemma_seq_subrange_index(sv, 0, d, j);
            }
            vstd::seq::lemma_seq_ext_equal(cur, sv.subrange(0, d));
        }
        assert((snapshot.path_start as int) <= d);
    }
    match frag {
        Option::Some(fb) => {
            // lib.rs:1661-1663: a record whose fragment will be
            // restored takes no opaque strip; the restore is the
            // plain '#' + moved-bytes append
            let drop_url = Url {
                serialization: parser::bytes_own(
                    &self.serialization),
                scheme_end: self.scheme_end,
                username_end: self.username_end,
                host_start: self.host_start,
                host_end: self.host_end,
                host: self.host,
                port: self.port,
                path_start: self.path_start,
                query_start: Option::None,
                fragment_start: Option::None,
            };
            proof {
                assert(drop_url.serialization.view() == cur);
                assert((drop_url.serialization.view().len() as int)
                    == d);
                // the invariant of the post-drop record
                if snapshot.query_start.is_some() {
                    parser::set_query_drop_carry(&snapshot,
                        &drop_url, d);
                } else {
                    if has_authority_view(&snapshot) {
                        parser::rel_carry_none_authority(
                            &snapshot, &drop_url, d);
                    } else {
                        parser::rel_carry_none_anarchist(
                            &snapshot, &drop_url, d);
                    }
                }
                assert(url_invariant(&drop_url));
                // the base face of the post-drop record: the
                // terminus conjunct covers the one slot a username
                // can park at the boundary, where the entry record's
                // own '?' or '#' marker byte drove the wildcard arm
                assert(parser::base_url_face(&drop_url)) by {
                    let ue2 = drop_url.username_end as int;
                    if has_authority_view(&drop_url) && ue2 == d {
                        if snapshot.query_start.is_some() {
                            assert(sv.index(ue2) == 0x3Fu8);
                        } else {
                            assert(sv.index(ue2) == 0x23u8);
                        }
                        assert(ue2
                            == (snapshot.scheme_end as int) + 3);
                    }
                };
                // the restore budget: the moved span sits inside the
                // entry serialization's own tail
                let n = sv.len() as int;
                let fsv = snapshot.fragment_start.unwrap() as int;
                let fb_view = fb.view();
                assert((fb_view.len() as int) == n - fsv - 1) by {
                    vstd::seq::lemma_seq_subrange_len(sv, fsv + 1,
                        n);
                }
                assert(d <= fsv);
                assert((self.serialization.view().len() as int)
                    + (fb_view.len() as int) + 1
                    <= 0xFFFF_FFFF);
            }
            self.set_query_restore_write(&fb);
            proof {
                let fb_view = fb.view();
                let fin = self.serialization.view();
                assert(fin == cur + seq![0x23u8] + fb_view);
                assert(fin == sv.subrange(0, d)
                    + seq![0x23u8] + fb_view);
                // the fragment slot sits at the boundary
                assert((self.fragment_start.unwrap() as int)
                    == d);
                assert(fin.index(d) == 0x23u8);
                assert(parser::machine_domain(fb_view));
                assert(fb_view == fragment_content_view(snapshot));
                assert((fin.len() as int)
                    < 0xFFFF_FFFF + 1 ==> true);
                assert((fin.len() as int) <= 0xFFFF_FFFF);
                // the prolong carry over the post-drop record
                parser::fragment_prolong_carry(&drop_url, self, d);
                assert(url_invariant(self));
                // the value face: the restored fragment content
                assert(fragment_content_view(self) == fb_view) by {
                    let fstart = self.fragment_start.unwrap() as int;
                    assert(fstart == d);
                    assert forall|j: int|
                        #![trigger fragment_content_view(self).index(j)]
                        0 <= j && j < (fb_view.len() as int)
                        implies fragment_content_view(self).index(j)
                            == fb_view.index(j) by {
                        vstd::seq::lemma_seq_subrange_index(
                            fin, fstart + 1, fin.len() as int, j);
                        vstd::seq::lemma_seq_add_index2(
                            cur, seq![0x23u8] + fb_view,
                            fstart + 1 + j);
                        vstd::seq::lemma_seq_add_index2(
                            seq![0x23u8], fb_view, 1 + j);
                    }
                    vstd::seq::lemma_seq_ext_equal(
                        fragment_content_view(self), fb_view);
                };
            }
        }
        Option::None => {
            // lib.rs:1661-1663: without a fragment to restore the
            // record takes the opaque-path strip
            proof {
                if snapshot.query_start.is_some() {
                    // the query-drop record: the maintained prefix
                    // is the entry's own, both wrap slots are empty
                    parser::set_query_drop_carry(&snapshot, self, d);
                } else {
                    // neither the take nor the removal truncated:
                    // the record is the entry state with both wrap
                    // slots already empty
                    assert((self.serialization.view().len() as int)
                        == (sv.len() as int));
                    assert(self.serialization.view() == sv) by {
                        assert forall|j: int|
                            0 <= j && j < (self.serialization.view()
                                .len() as int)
                            implies self.serialization.view().index(j)
                                == sv.index(j) by {
                            vstd::seq::lemma_seq_subrange_index(sv,
                                0, d, j);
                        }
                        vstd::seq::lemma_seq_ext_equal(
                            self.serialization.view(), sv);
                    }
                }
                assert(url_invariant(self));
                assert(parser::machine_domain(
                    self.serialization.view()));
            }
            self.strip_trailing_spaces_from_opaque_path();
            proof {
                // the strip's cut splits the maintained d-prefix:
                // the witness composes over the truncation, the
                // removed bytes are the strip's space run inside
                // the prefix
                let cut_s = choose|c: int| 0 <= c && c <= d
                    && self.serialization.view()
                        == cur.subrange(0, c)
                    && (forall|j: int| c <= j && j < d
                        ==> cur.index(j) == 0x20u8);
                assert(self.serialization.view()
                    == sv.subrange(0, cut_s)) by {
                    vstd::seq::lemma_seq_subrange_composition(
                        sv, 0, d, 0, cut_s);
                };
                assert forall|j: int| cut_s <= j && j < d
                    implies sv.index(j) == 0x20u8 by {
                    assert(cur.index(j) == sv.index(j));
                };
            }
        }
    }
}

/// Origin Rust (lib.rs:1636-1666): pub fn set_query(&mut self,
///   query: Option<&str>) -- take the fragment away, drop any
/// previous query, write the '?' plus the QUERY/SPECIAL_QUERY-encoded
/// payload (the Some face), or drop the query slot and strip the
/// trailing spaces of an opaque path when no fragment exists to
/// restore (the None face), then re-append the taken fragment
/// verbatim ('#' + the moved bytes, the restore_already_parsed
/// fragment face). The &str face is the byte slice (ledger 1); the
/// debug assert on the previous '?' (lib.rs:1643) is the invariant's
/// own byte pin; the to_u32 boundary stays in the u32 offset domain.
/// CONE: the base-input face of the fragment setter (its userinfo
/// terminus conjunct documents the one slot the writes can park at
/// the boundary); the '#' payload byte encodes through the set
/// membership in the for-setter Parser (no terminator arm there).
pub exec fn set_query(&mut self, query: Option<&[u8]>)
    requires
        parser::base_url_face(self),
        (self.serialization.view().len() as int)
            + 3 * (match query {
                Option::Some(qb) => (qb@.len() as int),
                Option::None => 0int,
            }) + 8 <= 0xFFFF_FFFF,
        (match query {
            Option::Some(qb) => parser::machine_domain(qb@),
            Option::None => true,
        }),
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        (final(self).scheme_end as int)
            == (old(self).scheme_end as int),
        (final(self).username_end as int)
            == (old(self).username_end as int),
        (final(self).host_start as int)
            == (old(self).host_start as int),
        (final(self).host_end as int)
            == (old(self).host_end as int),
        final(self).host == old(self).host,
        final(self).port == old(self).port,
        (final(self).path_start as int)
            == (old(self).path_start as int),
        (query.is_some() ==> ({
            let qb = query.unwrap();
            let d = parser::base_before_query_len(old(self));
            let set = if parser::is_special(parser::scheme_type_of(
                old(self).serialization.view().subrange(
                    0, old(self).scheme_end as int))) {
                parser::EncodeSet::SpecialQuery
            } else {
                parser::EncodeSet::Query
            };
            let enc = parser::enc_seq(qb@, set);
            &&& final(self).query_start == Option::Some(d as u32)
            &&& query_content_view(final(self)) == enc
            &&& (old(self).fragment_start.is_none()
                ==> final(self).fragment_start.is_none())
            &&& (old(self).fragment_start.is_none()
                ==> final(self).serialization.view()
                    == old(self).serialization.view().subrange(
                        0, d) + seq![0x3Fu8] + enc)
            &&& (old(self).fragment_start.is_some()
                ==> final(self).fragment_start
                    == Option::Some(
                        ((d + 1 + (enc.len() as int)) as u32)))
            &&& (old(self).fragment_start.is_some()
                ==> final(self).serialization.view()
                    == old(self).serialization.view().subrange(
                        0, d) + seq![0x3Fu8] + enc
                        + seq![0x23u8]
                        + fragment_content_view(old(self)))
            &&& (old(self).fragment_start.is_some()
                ==> fragment_content_view(final(self))
                    == fragment_content_view(old(self)))
        })),
        (query.is_none() ==> ({
            let olfs = old(self).fragment_start;
            let d = parser::base_before_query_len(old(self));
            &&& final(self).query_start.is_none()
            &&& (olfs.is_some()
                ==> final(self).fragment_start
                    == Option::Some(d as u32))
            &&& (olfs.is_some()
                ==> final(self).serialization.view()
                    == old(self).serialization.view().subrange(
                        0, d) + seq![0x23u8]
                        + fragment_content_view(old(self)))
            &&& (olfs.is_some()
                ==> fragment_content_view(final(self))
                    == fragment_content_view(old(self)))
            &&& (olfs.is_none()
                ==> final(self).fragment_start.is_none())
            &&& (olfs.is_none()
                ==> exists|cut: int| 0 <= cut && cut <= d
                    && final(self).serialization.view()
                        == old(self).serialization.view().subrange(
                            0, cut)
                    && (forall|j: int| cut <= j && j < d
                        ==> old(self).serialization.view().index(j)
                            == 0x20u8))
        })),
{
    let ghost old_view = self.serialization.view();
    // the decomposed snapshot of the entry record (the take and the
    // carries below consume it)
    let snapshot = Url {
        serialization: parser::bytes_own(&self.serialization),
        scheme_end: self.scheme_end,
        username_end: self.username_end,
        host_start: self.host_start,
        host_end: self.host_end,
        host: self.host,
        port: self.port,
        path_start: self.path_start,
        query_start: self.query_start,
        fragment_start: self.fragment_start,
    };
    proof {
        assert(snapshot.serialization.view() == old_view);
        assert(url_invariant(&snapshot));
        assert(parser::base_url_face(&snapshot));
    }
    // take_fragment (lib.rs:1598-1604): move the fragment bytes out
    // of the record, drop the '#' slot
    let frag: Option<Vec<u8>> = match self.fragment_start {
        Option::Some(fs) => {
            proof {
                assert((fs as int) < (old_view.len() as int));
                assert((fs as int)
                    == parser::base_before_len(&snapshot));
            }
            let fb = bytes_slice(&self.serialization, fs + 1,
                url_len32(&self.serialization));
            proof {
                assert(fb.view() == old_view.subrange(
                    (fs as int) + 1, old_view.len() as int));
                assert(fb.view()
                    == fragment_content_view(&snapshot));
                parser::machine_domain_subrange(old_view,
                    (fs as int) + 1, old_view.len() as int);
                assert(parser::machine_domain(fb.view()));
            }
            self.serialization.truncate(fs as usize);
            proof {
                let t1 = self.serialization.view();
                assert(t1 == old_view.subrange(0, fs as int));
                assert(parser::machine_domain(t1));
                assert((t1.len() as int) == (fs as int));
            }
            self.fragment_start = Option::None;
            Option::Some(fb)
        }
        Option::None => Option::None,
    };
    // remove any previous query (lib.rs:1642-1644)
    match self.query_start {
        Option::Some(qs) => {
            proof {
                assert((qs as int) < (old_view.len() as int));
                if snapshot.fragment_start.is_some() {
                    assert((qs as int)
                        < (snapshot.fragment_start.unwrap() as int));
                }
                assert((qs as int)
                    == parser::base_before_query_len(&snapshot));
            }
            self.serialization.truncate(qs as usize);
            proof {
                // the query truncation lands on the qs-prefix of the
                // entry view: directly when no fragment was taken, or
                // through the fragment-prefix composition
                if snapshot.fragment_start.is_some() {
                    assert(self.serialization.view()
                        == old_view.subrange(0, qs as int)) by {
                        vstd::seq::lemma_seq_subrange_composition(
                            old_view, 0,
                            snapshot.fragment_start.unwrap() as int,
                            0, (qs as int));
                    }
                } else {
                    assert(self.serialization.view()
                        == old_view.subrange(0, qs as int));
                }
                let t2 = self.serialization.view();
                assert((t2.len() as int) == (qs as int));
                assert(parser::machine_domain(t2));
            }
            self.query_start = Option::None;
        }
        Option::None => {}
    }
    let ghost mid_view = self.serialization.view();
    proof {
        let d = parser::base_before_query_len(&snapshot);
        assert((mid_view.len() as int) == d);
        assert(mid_view.len() <= old_view.len());
        // the maintained prefix is the d-prefix of the entry view
        // (whichever truncations ran, the surviving bytes are the
        // entry's own below the boundary)
        if snapshot.query_start.is_some() {
            assert(mid_view == old_view.subrange(0, d));
        } else if snapshot.fragment_start.is_some() {
            assert(mid_view == old_view.subrange(0, d));
        } else {
            assert(mid_view == old_view);
            assert(old_view.subrange(0, d) == old_view) by {
                assert forall|j: int| 0 <= j && j < d
                    implies old_view.subrange(0, d).index(j)
                        == old_view.index(j) by {
                    vstd::seq::lemma_seq_subrange_index(old_view,
                        0, d, j);
                }
                vstd::seq::lemma_seq_ext_equal(
                    old_view.subrange(0, d), old_view);
            }
            assert(mid_view == old_view.subrange(0, d));
        }
        assert(parser::machine_domain(mid_view));
        assert forall|j: int| 0 <= j && j < d
            implies mid_view.index(j) == old_view.index(j) by {
            vstd::seq::lemma_seq_subrange_index(old_view, 0, d, j);
        };
        // the boundary dominates path_start (the entry record's own
        // query/fragment wraps)
        assert((snapshot.path_start as int) <= d);
    }
    // the dispatch (lib.rs:1645 vs 1654): the Some arm writes the
    // fresh query payload and restores the fragment; the None arm
    // restores the fragment or takes the opaque-path strip. Each is
    // a split-out face so the whole-fn checks stay inside the solver
    // budget.
    proof {
        assert(parser::machine_domain(mid_view));
        assert((mid_view.len() as int)
            == parser::base_before_query_len(&snapshot));
        assert(self.fragment_start.is_none());
        assert((snapshot.path_start as int)
            <= (mid_view.len() as int));
        if frag.is_some() {
            assert(snapshot.fragment_start.is_some());
            assert(frag.unwrap().view()
                == fragment_content_view(&snapshot));
        } else {
            assert(snapshot.fragment_start.is_none());
        }
    }
    match query {
        Option::Some(qb) => {
            proof {
                assert(parser::machine_domain(qb@));
            }
            self.set_query_some_arm(&snapshot, qb, &frag);
        }
        Option::None => {
            self.set_query_none_arm(&snapshot, &frag);
        }
    }
    proof {
        // the postcondition mirrors the entry record's own fields
        // through the snapshot tie
        assert(snapshot.fragment_start
            == old(self).fragment_start);
        assert(parser::base_before_query_len(&snapshot)
            == parser::base_before_query_len(old(self)));
        assert(snapshot.serialization.view()
            == old(self).serialization.view());
    }
}

/* ============================================================
 * set_scheme (lib.rs:2461-2510). Transcribed from the IMPLEMENTATION
 * (the adjudicated cone): the specialness gates and the folded file
 * gate at lib.rs:2466-2475, the remaining-empty/has_host gate at
 * lib.rs:2477, the index-shift write at lib.rs:2480-2499, and the
 * closing set_port(previous_port) call at lib.rs:2502-2508. The
 * document's five Err conditions (lib.rs:2354-2361) diverge from
 * these gates on the file faces -- the scheme transition matrix of
 * the file{with host} records and the folded file gate is the
 * adjudicated runtime record (the settled finding's evidence); the
 * SPEC-DOC MISMATCH therefore sits on the for-setter doc side and
 * the mirror pins the implementation's behavior.
 * ============================================================ */

/// The generic face of the index-shift write's position channel (the
/// aggregate single-equality carrier below): when the tail byte at
/// k+j is the entry byte at old_scheme_end+j, every entry subrange
/// at or above the scheme boundary re-lands as the same content at
/// the shifted offsets -- one lemma for the host, port, path, query
/// and fragment faces alike.
    proof fn subrange_shift_eq(
        fe: Seq<u8>,
        ov: Seq<u8>,
        kl: int,
        ose: int,
        a0: int,
        b0: int,
    )
        requires
            0 <= kl,
            0 <= ose,
            (forall|j: int| #![trigger fe.index(j)]
                kl <= j && j < fe.len() as int
                    ==> fe.index(j) == ov.index(ose + j - kl)),
            ((fe.len() as int)
                == kl + (ov.len() as int) - ose),
            ose <= a0,
            a0 <= b0,
            (b0 as int) <= (ov.len() as int),
        ensures
            fe.subrange(a0 + kl - ose, b0 + kl - ose)
                == ov.subrange(a0, b0),
    {
        let d = kl - ose;
        vstd::seq::lemma_seq_subrange_len(fe,
            a0 + d, b0 + d);
        vstd::seq::lemma_seq_subrange_len(ov, a0, b0);
        assert((fe.subrange(a0 + d, b0 + d).len() as int)
            == (ov.subrange(a0, b0).len() as int));
        assert forall|j: int| 0 <= j
            && j < fe.subrange(a0 + d, b0 + d).len() as int
            implies fe.subrange(a0 + d, b0 + d).index(j)
                == ov.subrange(a0, b0).index(j) by {
            vstd::seq::lemma_seq_subrange_index(fe,
                a0 + d, b0 + d, j);
            vstd::seq::lemma_seq_subrange_index(ov, a0, b0, j);
            assert(fe.index(a0 + d + j) == ov.index(ose + a0 + d + j - kl));
            assert(ose + a0 + d + j - kl == a0 + j);
        }
        vstd::seq::lemma_seq_ext_equal(
            fe.subrange(a0 + d, b0 + d), ov.subrange(a0, b0));
    }

/// The index-shift write of set_scheme (lib.rs:2480-2499, split out
/// so each whole-fn check stays inside the solver budget): every
/// component boundary moves by (k - old scheme_end) and the
/// serialization becomes the parsed scheme bytes (the for-setter
/// Parser's own payload, the lowercased scheme scan of parse_scheme)
/// followed by the entry tail after the old scheme. The proof's
/// position channel is the aggregate single equality the invariant
/// conjuncts read: the written byte at k + j is the entry byte at
/// old_scheme_end + j for every tail position.
/* [verifier note: rlimit = the whole-fn check rides past the default
   budget: the composed-tail postcondition clause (the flat
   pser@ + tail@ form below is the slice-param restructure of the
   scheme batch -- the earlier composed subrange clause blew past
   even 90) and the long Option-shift ensure shapes keep the final
   query above the default budget; the default limit fails
   deterministically and the site is ambient-sensitive: the scheme
   batch closed it at 90 across the three harness ambients, and the
   later userinfo setters grew the module enough that the
   ut-read-api ambient re-opened it (90/100/110/120/130/150 all
   fail that ambient, 150 also perturbs a neighboring site, 200
   closes; the other two ambients close at every probed value) --
   the ceiling now sits at 200; only the resource ceiling is
   raised, no obligation is relaxed, the fn's own content is
   untouched] */
#[verifier::rlimit(200)]
pub exec fn set_scheme_index_write(&mut self, pser: &[u8],
    tail: &[u8], k: u32)
    requires
        url_invariant(self),
        parser::machine_domain(self.serialization.view()),
        parser::machine_domain(pser@),
        parser::machine_domain(tail@),
        (pser@.len() as int) == (k as int),
        1 <= (k as int),
        is_ascii_alpha(pser@.index(0)),
        (forall|j: int| 1 <= j && j < (k as int)
            ==> is_scheme_char(pser@.index(j))),
        (parser::is_special(parser::scheme_type_of(pser@))
            ==> parser::is_special(parser::scheme_type_of(
                self.serialization.view().subrange(
                    0, self.scheme_end as int)))),
        (tail@ == self.serialization.view().subrange(
            self.scheme_end as int,
            self.serialization.view().len() as int)),
        ((self.serialization.view().len() as int)
            - (self.scheme_end as int) + (k as int)) <= 0xFFFF_FFFF,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(
            final(self).serialization.view()),
        ((final(self).serialization.view().len() as int)
            <= 0xFFFF_FFFF),
        (final(self).serialization.view() == pser@ + tail@),
        (final(self).scheme_end as int) == (k as int),
        (final(self).username_end as int)
            == (old(self).username_end as int)
                - (old(self).scheme_end as int) + (k as int),
        (final(self).host_start as int)
            == (old(self).host_start as int)
                - (old(self).scheme_end as int) + (k as int),
        (final(self).host_end as int)
            == (old(self).host_end as int)
                - (old(self).scheme_end as int) + (k as int),
        (final(self).path_start as int)
            == (old(self).path_start as int)
                - (old(self).scheme_end as int) + (k as int),
        (old(self).query_start.is_none()
            ==> final(self).query_start.is_none()),
        (old(self).query_start.is_some()
            ==> (final(self).query_start
                == Option::Some((((old(self).query_start.unwrap()
                    as int) - (old(self).scheme_end as int)
                    + (k as int)) as u32)))),
        (old(self).fragment_start.is_none()
            ==> final(self).fragment_start.is_none()),
        (old(self).fragment_start.is_some()
            ==> (final(self).fragment_start
                == Option::Some((((old(self).fragment_start.unwrap()
                    as int) - (old(self).scheme_end as int)
                    + (k as int)) as u32)))),
        final(self).host == old(self).host,
        final(self).port == old(self).port,
        (has_authority_view(final(self))
            == has_authority_view(old(self))),
{
    let ghost ov = self.serialization.view();
    let ose32 = self.scheme_end;
    let ghost ose = ose32 as int;
    let ghost kl = k as int;
    // the entry tail arrives as the slice parameter (lib.rs:2499:
    // self.slice(old_scheme_end..), extracted by the wrapper before
    // the call -- the upstream byte move, staged one phase earlier)
    let n32 = url_len32(&self.serialization);
    proof {
        assert((n32 as int) == ov.len() as int);
        assert((tail@.len() as int) == (n32 as int) - ose);
        assert(tail@ == ov.subrange(ose, ov.len() as int));
        assert(parser::machine_domain(tail@));
    }
    // the boundary shifts (lib.rs:2482-2496): -= old_scheme_end,
    // += new_scheme_end, applied to every component boundary
    proof {
        assert((self.username_end as int) >= (ose + 1));
        assert((self.host_start as int)
            >= (self.username_end as int));
        assert((self.host_end as int) >= (self.host_start as int));
        assert((self.path_start as int) >= (self.host_end as int));
        if self.query_start.is_some() {
            assert((self.query_start.unwrap() as int)
                >= (self.path_start as int));
        }
        if self.fragment_start.is_some() {
            assert((self.fragment_start.unwrap() as int)
                >= (self.path_start as int));
        }
        assert((self.username_end as int) - ose + kl <= 0xFFFF_FFFF);
        assert((self.host_start as int) - ose + kl <= 0xFFFF_FFFF);
        assert((self.host_end as int) - ose + kl <= 0xFFFF_FFFF);
        assert((self.path_start as int) - ose + kl <= 0xFFFF_FFFF);
    }
    self.scheme_end = k;
    self.username_end = self.username_end - ose32 + k;
    self.host_start = self.host_start - ose32 + k;
    self.host_end = self.host_end - ose32 + k;
    self.path_start = self.path_start - ose32 + k;
    match self.query_start {
        Option::Some(qs0) => {
            self.query_start = Option::Some(qs0 - ose32 + k);
        }
        Option::None => {}
    }
    match self.fragment_start {
        Option::Some(fs0) => {
            self.fragment_start = Option::Some(fs0 - ose32 + k);
        }
        Option::None => {}
    }
    // the serialization rebuild (lib.rs:2480/2499: the fresh Parser
    // payload plus the kept tail replaces the byte store)
    let ghost pv = pser@;
    self.serialization.truncate(0 as usize);
    proof {
        assert(self.serialization.view()
            == ov.subrange(0, 0));
        assert(self.serialization.view() == Seq::empty());
    }
    parser::vec_append_bytes(&mut self.serialization, pser);
    proof {
        assert(self.serialization.view()
            == Seq::empty() + pv);
        assert(Seq::empty() + pv == pv);
        assert(self.serialization.view() == pv);
    }
    parser::vec_append_bytes(&mut self.serialization, tail);
    proof {
        let fe = self.serialization.view();
        let tv = tail@;
        assert(fe == pv + tv);
        assert(fe == pv + ov.subrange(ose, ov.len() as int));
        parser::machine_domain_add(pv, tv);
        assert(parser::machine_domain(fe));
        assert((fe.len() as int)
            == kl + (ov.len() as int) - ose);
        assert((fe.len() as int) <= 0xFFFF_FFFF);
        // the aggregate position channel: the tail byte at kl + j is
        // the ose + j byte of the entry
        assert forall|j: int| 0 <= j && j < kl
            implies fe.index(j) == pv.index(j) by {
            vstd::seq::lemma_seq_add_index1(pv, tv, j);
        }
        assert forall|j: int| 1 <= j && j < kl
            implies is_scheme_char(fe.index(j)) by { }
        assert forall|j: int| kl <= j && j < fe.len() as int
            implies fe.index(j) == ov.index(ose + j - kl) by {
            vstd::seq::lemma_seq_add_index2(pv, tv, j);
            vstd::seq::lemma_seq_subrange_index(ov, ose,
                ov.len() as int, j - kl);
        }
        // the ':' terminator channels in from the entry pin
        assert(fe.index(kl) == ov.index(ose));
        assert(fe.index(kl) == 0x3Au8);
        assert(is_ascii_alpha(fe.index(0)));
        // the head subrange is the parsed scheme (the sentinel face
        // of the specialness conjuncts below)
        assert(has_authority_view(self)
            == has_authority_view(old(self))) by {
            if has_authority_view(old(self)) {
                assert(((ose as int) + 3)
                    <= (ov.len() as int));
                assert(fe.index(kl + 1) == ov.index(ose + 1));
                assert(fe.index(kl + 2) == ov.index(ose + 2));
                assert(fe.index(kl + 1) == 0x2Fu8);
                assert(fe.index(kl + 2) == 0x2Fu8);
            } else {
                if ((ose as int) + 3) <= (ov.len() as int) {
                    assert(!(ov.index(ose + 1) == 0x2Fu8
                        && ov.index(ose + 2) == 0x2Fu8));
                    if ((kl + 3) <= (fe.len() as int)) {
                        assert(fe.index(kl + 1) == ov.index(ose + 1));
                        assert(fe.index(kl + 2) == ov.index(ose + 2));
                    }
                } else {
                    // the length face: kl + 3 cannot land below
                    // fe.len (the tail planes the offsets)
                    assert(((kl as int) + 3)
                        > (fe.len() as int));
                }
            }
        }
        vstd::seq::lemma_seq_subrange_len(fe, 0, kl);
        assert(fe.subrange(0, kl) == pv) by {
            assert((fe.subrange(0, kl).len() as int) == (pv.len() as int));
            assert forall|j: int| 0 <= j && j < kl
                implies fe.subrange(0, kl).index(j)
                    == pv.index(j) by {
                vstd::seq::lemma_seq_subrange_index(fe, 0, kl, j);
            }
            vstd::seq::lemma_seq_ext_equal(fe.subrange(0, kl), pv);
        }
        assert(has_authority_view(self) == has_authority_view(old(self)));
        // the shifted subrange faces the invariant's port conjuncts
        // read (host, port region); the query/fragment content views
        // ride the same channel downstream and stay out of this
        // fn's postcondition (each query stays small)
        let dg = kl - ose;
        let ohs = old(self).host_start as int;
        let ohe = old(self).host_end as int;
        let ops32 = old(self).path_start;
        assert((self.host_start as int) == ohs + dg);
        assert((self.host_end as int) == ohe + dg);
        assert((self.path_start as int)
            == (ops32 as int) + dg);
        // the host region face: same content at the shifted offsets
        vstd::seq::lemma_seq_subrange_len(fe, ohs + dg,
            ohe + dg);
        vstd::seq::lemma_seq_subrange_len(ov, ohs, ohe);
        assert((fe.subrange(ohs + dg, ohe + dg).len() as int)
            == (ov.subrange(ohs, ohe).len() as int));
        {
            assert forall|mi0: int|
                #![trigger fe.subrange(ohs + dg, ohe + dg).index(mi0)]
                0 <= mi0
                && mi0 < fe.subrange(ohs + dg, ohe + dg).len() as int
                implies fe.subrange(ohs + dg, ohe + dg).index(mi0)
                    == ov.subrange(ohs, ohe).index(mi0) by {
                vstd::seq::lemma_seq_subrange_index(fe,
                    ohs + dg, ohe + dg, mi0);
                vstd::seq::lemma_seq_subrange_index(ov,
                    ohs, ohe, mi0);
                assert((ohs + dg + mi0) >= kl);
                assert(fe.index(ohs + dg + mi0)
                    == ov.index(ose + ohs + dg + mi0 - kl));
                assert(ose + ohs + dg + mi0 - kl == ohs + mi0);
            }
            vstd::seq::lemma_seq_ext_equal(
                fe.subrange(ohs + dg, ohe + dg),
                ov.subrange(ohs, ohe));
        }
        if (self.path_start as int) > (self.host_end as int) {
            let he1 = self.host_end as int;
            let ps1 = self.path_start as int;
            let ops = ops32 as int;
            assert(ps1 == ops + dg);
            assert(he1 == ohe + dg);
            // the port region face: same digit content, so the
            // dec_val conjunct of the invariant carries across
            vstd::seq::lemma_seq_subrange_len(fe, he1 + 1, ps1);
            vstd::seq::lemma_seq_subrange_len(ov, ohe + 1, ops);
            assert((fe.subrange(he1 + 1, ps1).len() as int)
                == (ov.subrange(ohe + 1, ops).len() as int));
            assert forall|mi0: int|
                #![trigger fe.subrange(he1 + 1, ps1).index(mi0)]
                0 <= mi0
                && mi0 < fe.subrange(he1 + 1, ps1).len() as int
                implies fe.subrange(he1 + 1, ps1).index(mi0)
                    == ov.subrange(ohe + 1, ops).index(mi0) by {
                vstd::seq::lemma_seq_subrange_index(fe,
                    he1 + 1, ps1, mi0);
                vstd::seq::lemma_seq_subrange_index(ov,
                    ohe + 1, ops, mi0);
                assert((he1 + 1 + mi0) >= kl);
                assert(fe.index(he1 + 1 + mi0)
                    == ov.index(ose + he1 + 1 + mi0 - kl));
                assert(ose + he1 + 1 + mi0 - kl
                    == ohe + 1 + mi0);
            }
            vstd::seq::lemma_seq_ext_equal(
                fe.subrange(he1 + 1, ps1),
                ov.subrange(ohe + 1, ops));
            assert(dec_val(fe.subrange(he1 + 1, ps1))
                == dec_val(ov.subrange(ohe + 1, ops)));
        }
        // the structural invariant itself closes off the channel and
        // the position threads (the port digits and dec_val conjuncts
        // of the authority branch ride the same shifted faces; the
        // anarchist double-slash face never carries a port region,
        // so no unconditional digit claim is made here)
        assert(url_invariant(self));
    }
}

/// Origin Rust (lib.rs:2461-2510): pub fn set_scheme(&mut self,
///   scheme: &str) -> Result<(), ()> -- scan the argument through the
/// for-setter Parser (the scheme grammar face, lowercased, the ':'
/// terminator stays with the remainder), then the three-gate Err
/// filter of lib.rs:2466-2475 (the WHATWG specialness pairing plus
/// the folded file gate), then the remaining-empty/has_host gate of
/// lib.rs:2477, then the index-shift write (set_scheme_index_write
/// above, the lib.rs:2480-2499 face) and the closing
/// set_port(previous_port) of lib.rs:2502-2508: an explicit port
/// equal to the new scheme's default drops (the port region drains,
/// the path anchor moves to the host end), every other face leaves
/// the port and region as the entry record's own.
/// The upstream set_port wrapper's gates (lib.rs:1893-1899) reduce
/// on this face: the scheme-is-file gate is dead (the folded gate
/// at 2472 keeps any file-scheme target off the Ok face -- on the Ok
/// face has_host pins the is-file target out), and the no-host /
/// empty-Domain faces skip the section below, matching the Err side
/// of that wrapper with no observable difference. The &str face is
/// the byte slice (ledger 1). CONE (the adjudicated SPEC-DOC
/// MISMATCH record): the ENTRY record is a base_url_face record of
/// the machine byte domain, and the runtime doc divergences of the
/// gate set (the file{with host} transitions the doc bullet 3
/// misrenders) are the implementation's own behavior -- the mirror
/// pins the gates, not the rustdoc bullets.
/* [verifier note: rlimit = the whole-fn check rides past the default
   budget: the Ok-face A/B port disjunction post (the shifts of all
   six boundaries and both Option anchors through the value-case port
   arithmetic) keeps the final query above default; the default limit
   fails deterministically; the scheme batch closed it at 30 on three
   consecutive identical sweeps, and the later userinfo setters grew
   the module enough that the parse-machine ambient re-opened it
   (30 fails, 45 closes all three ambients) -- the ambient-flip
   protocol of the parse_host_and_port/rel_slash ledger; only the
   resource ceiling is raised, no obligation is relaxed, the fn's
   own content is untouched] */
#[verifier::rlimit(45)]
pub exec fn set_scheme(&mut self, scheme: &[u8]) -> (r: Result<(), ()>)
    requires
        parser::base_url_face(self),
        parser::machine_domain(scheme@),
        1 <= (scheme@.len() as int),
        ((self.serialization.view().len() as int)
            + (scheme@.len() as int) + 8) <= 0xFFFF_FFFF,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(
            final(self).serialization.view()),
        (r.is_err() ==> ({
            // do-nothing face: every component of the entry record
            // survives untouched
            &&& (final(self).serialization.view()
                == old(self).serialization.view())
            &&& (final(self).scheme_end as int)
                == (old(self).scheme_end as int)
            &&& (final(self).username_end as int)
                == (old(self).username_end as int)
            &&& (final(self).host_start as int)
                == (old(self).host_start as int)
            &&& (final(self).host_end as int)
                == (old(self).host_end as int)
            &&& final(self).host == old(self).host
            &&& final(self).port == old(self).port
            &&& (final(self).path_start as int)
                == (old(self).path_start as int)
            &&& final(self).query_start == old(self).query_start
            &&& final(self).fragment_start
                == old(self).fragment_start
        })),
        (r.is_ok() ==> ({
            let os = old(self).serialization.view();
            let se = old(self).scheme_end as int;
            let k = final(self).scheme_end as int;
            let d = k - se;
            let P = parser::lowered_prefix(scheme@.subrange(0, k), k);
            let W = P + os.subrange(se, os.len() as int);
            &&& 1 <= k
            &&& k <= (scheme@.len() as int)
            &&& (k == (scheme@.len() as int)
                || (k + 1 == (scheme@.len() as int)
                    && scheme@.index(k) == 0x3Au8))
            &&& final(self).host == old(self).host
            &&& (final(self).username_end as int)
                == (old(self).username_end as int) + d
            &&& (final(self).host_start as int)
                == (old(self).host_start as int) + d
            &&& (final(self).host_end as int)
                == (old(self).host_end as int) + d
            &&& has_authority_view(final(self))
                == has_authority_view(old(self))
            &&& (({
                // A: the port rides (the set_port no-op pairs, or
                // the upstream wrapper-gate Err faces skip)
                &&& final(self).port == old(self).port
                &&& (final(self).path_start as int)
                    == (old(self).path_start as int) + d
                &&& (old(self).query_start.is_none()
                    ==> final(self).query_start.is_none())
                &&& (old(self).query_start.is_some()
                    ==> final(self).query_start
                        == Option::Some(((old(self).query_start.unwrap()
                            as int) + d) as u32))
                &&& (old(self).fragment_start.is_none()
                    ==> final(self).fragment_start.is_none())
                &&& (old(self).fragment_start.is_some()
                    ==> final(self).fragment_start
                        == Option::Some(((old(self).fragment_start.unwrap()
                            as int) + d) as u32))
                &&& final(self).serialization.view() == W
            }) || ({
                // B: the explicit port equals the new scheme's
                // default and drops (the port region drains, the
                // anchor moves to the host end)
                &&& old(self).port.is_some()
                &&& parser::default_port_of(P) == old(self).port
                &&& final(self).port.is_none()
                &&& (final(self).path_start as int)
                    == (old(self).host_end as int) + d
                &&& (old(self).query_start.is_none()
                    ==> final(self).query_start.is_none())
                &&& (old(self).query_start.is_some()
                    ==> final(self).query_start
                        == Option::Some(((old(self).query_start.unwrap()
                            as int) + d
                            - ((old(self).path_start as int)
                                - (old(self).host_end as int))) as u32))
                &&& (old(self).fragment_start.is_none()
                    ==> final(self).fragment_start.is_none())
                &&& (old(self).fragment_start.is_some()
                    ==> final(self).fragment_start
                        == Option::Some(((old(self).fragment_start.unwrap()
                            as int) + d
                            - ((old(self).path_start as int)
                                - (old(self).host_end as int))) as u32))
                &&& final(self).serialization.view()
                    == W.subrange(0, (old(self).host_end as int) + d)
                        + W.subrange((old(self).path_start as int) + d,
                            W.len() as int)
            }))
        })),
{
    // the for-setter scan (lib.rs:2462-2463)
    let finp = parser::Input { bytes: scheme, pos: 0 };
    let mut p = parser::Parser {
        serialization: Vec::new(),
        base_url: Option::None,
        context: parser::Context::Setter,
    };
    proof {
        assert((scheme@.len() as int) <= 0xFFFF_FFFF);
        assert(parser::input_rem(&finp) == scheme@);
        assert(parser::input_ok(&finp));
        assert(parser::machine_domain(parser::input_rem(&finp)));
        assert(parser::input_wf(&finp));
        assert(p.serialization.view().len() == 0);
    }
    let rem = p.parse_scheme(finp);
    match rem {
        Result::Err(()) => {
            // no record write happened (lib.rs:2463's `?`)
            return Result::Err(());
        }
        Result::Ok(rest) => {
            let ghost sl = scheme@;
            let ghost pv0 = p.serialization.view();
            let ghost ksk = choose|kk: int|
                1 <= kk
                && kk <= sl.len() as int
                && pv0 == parser::lowered_prefix(sl.subrange(0, kk), kk)
                && is_ascii_alpha(sl.index(0))
                && (forall|j: int| 1 <= j && j < kk
                    ==> is_scheme_char(sl.index(j)))
                && ((kk < (sl.len() as int)
                    && sl.index(kk) == 0x3Au8
                    && parser::input_rem(&rest)
                        == sl.subrange(kk + 1, sl.len() as int)
                    && parser::input_wf(&rest))
                    || (kk == (sl.len() as int)
                        && parser::input_rem(&rest).len() == 0
                        && parser::input_wf(&rest)));
            let k32 = p.serialization.len() as u32;
            proof {
                // the serialization length pins the witness
                assert((pv0.len() as int) == (k32 as int));
                assert(pv0.len() == parser::lowered_prefix(
                    sl.subrange(0, pv0.len() as int),
                    pv0.len() as int).len());
                assert((pv0.len() as int) == ksk);
                assert(pv0.len() <= 0xFFFF_FFFF);
                // the lowered scheme bytes stay on the machine domain
                assert(parser::machine_domain(pv0));
                assert(is_ascii_alpha(pv0.index(0)));
                assert forall|j: int| 1 <= j && j < (pv0.len() as int)
                    implies is_scheme_char(pv0.index(j)) by {
                    vstd::seq::lemma_seq_subrange_index(sl, 0,
                        pv0.len() as int, j);
                    assert(pv0.index(j)
                        == parser::lower_byte(sl.index(j)));
                    assert(is_scheme_char(sl.index(j)));
                }
            }
            let rest_nonempty = (rest.pos as usize)
                < rest.bytes.len();
            proof {
                assert((parser::input_rem(&rest).len() as int)
                    == ((rest.bytes.len() as int)
                        - (rest.pos as int)));
                assert(rest_nonempty
                    == ((parser::input_rem(&rest).len() as int) > 0));
            }
            // gate 1 (lib.rs:2466-2475): the specialness pairing plus
            // the folded file gate
            let oschemeb = self.scheme();
            let st_old = parser::scheme_type_from(&oschemeb);
            let st_new = parser::scheme_type_from(&p.serialization);
            let auth = self.has_authority();
            let hh = url_has_host(&self);
            proof {
                assert(st_old == parser::scheme_type_of(
                    self.serialization.view().subrange(
                        0, self.scheme_end as int)));
                assert(st_new == parser::scheme_type_of(pv0));
                assert(auth == has_authority_view(self));
            }
            if (st_new.is_special() && !st_old.is_special())
                || (!st_new.is_special() && st_old.is_special())
                || (st_new.is_file() && auth)
            {
                return Result::Err(());
            }
            // gate 2 (lib.rs:2477): empty remainder, and hosts for
            // special targets
            if rest_nonempty || (!hh && st_new.is_special()) {
                return Result::Err(());
            }
            // the file face is off the Ok path (the folded gate and
            // the has_host gate pair up: a file-scheme target with no
            // host to ride would have been stopped at gate 2, and any
            // host at all implies the authority the folded gate
            // stopped at gate 1)
            proof { assert(!parser::is_file(st_new)); }
            // the index-shift write (lib.rs:2480-2499), staged with
            // the tail slice hoisted out (upstream's own
            // self.slice(old_scheme_end..) checkout, one phase early)
            proof {
                assert((self.serialization.view().len() as int)
                    - (self.scheme_end as int)
                    + (k32 as int) <= 0xFFFF_FFFF);
                assert(pv0.len() == (k32 as int));
                // on the Ok path the remainder is empty: k32 ==
                // scheme@.len(), or the argument ends in the ':' the
                // scan peels (scheme@.index(k32) == 0x3A)
                assert(parser::input_rem(&rest).len() == 0);
                assert((k32 as int) == (sl.len() as int)
                    || ((k32 as int) + 1 == (sl.len() as int)
                        && sl.index((k32 as int)) == 0x3Au8));
            }
            let write_tail = bytes_slice(&self.serialization,
                self.scheme_end,
                url_len32(&self.serialization));
            proof {
                assert(write_tail.view()
                    == old(self).serialization.view().subrange(
                        old(self).scheme_end as int,
                        old(self).serialization.view().len() as int));
                parser::machine_domain_subrange(
                    old(self).serialization.view(),
                    old(self).scheme_end as int,
                    old(self).serialization.view().len() as int);
                assert(parser::machine_domain(write_tail.view()));
            }
            self.set_scheme_index_write(&p.serialization,
                &write_tail, k32);
            proof {
                let fe1 = self.serialization.view();
                assert(fe1 == pv0
                    + old(self).serialization.view().subrange(
                        old(self).scheme_end as int,
                        old(self).serialization.view().len() as int));
                parser::add_prefix_subrange(pv0,
                    old(self).serialization.view().subrange(
                        old(self).scheme_end as int,
                        old(self).serialization.view().len() as int),
                    k32 as int);
                assert(fe1.subrange(0, k32 as int) == pv0);
                assert(fe1.subrange(0, k32 as int)
                    == parser::lowered_prefix(
                        sl.subrange(0, k32 as int), k32 as int));
                assert(parser::default_port_of(fe1.subrange(
                    0, k32 as int))
                    == parser::default_port_of(pv0));
            }
            // the closing set_port(previous_port) of lib.rs:2502-2508
            match self.port {
                Option::Some(v) => {
                    let dp = parser::default_port(&p.serialization);
                    let dom_empty = match self.host {
                        HostInternal::Domain => {
                            self.host_start == self.host_end
                        }
                        _ => false,
                    };
                    if hh
                        && !dom_empty
                        && dp == Option::Some(v)
                    {
                        // the (Some, None) drain arm of
                        // set_port_internal (lib.rs:1904-1909)
                        let he1 = self.host_end;
                        let ps1 = self.path_start;
                        proof {
                            assert((ps1 as int) > (he1 as int));
                            assert((he1 as int) + 2 <= (ps1 as int));
                        }
                        vec_drain_middle(
                            &mut self.serialization, he1, ps1);
                        let offset = ps1 - he1;
                        self.path_start = he1;
                        match self.query_start {
                            Option::Some(qi) => {
                                self.query_start =
                                    Option::Some(qi - offset);
                            }
                            Option::None => {}
                        }
                        match self.fragment_start {
                            Option::Some(qi) => {
                                self.fragment_start =
                                    Option::Some(qi - offset);
                            }
                            Option::None => {}
                        }
                        self.port = Option::None;
                        proof {
                            assert(url_invariant(self));
                        }
                    } else {
                        // the equal-value no-op arm of
                        // set_port_internal (lib.rs:1913)
                    }
                }
                Option::None => {
                    // the (None, None) arm of set_port_internal
                    // (lib.rs:1901)
                }
            }
            return Result::Ok(());
        }
    }
}

/* ============================================================
 * set_password (lib.rs:2205-2261) and set_username
 * (lib.rs:2299-2348): the userinfo write faces. Both share the
 * entry gate (lib.rs:2207/2301): no host, the empty-Domain face,
 * or the file scheme. Under the structural invariant the
 * empty-Domain disjunct is dead (host None <=> empty host region,
 * lib.rs:736-748, so a Domain tag never sits on an empty region) --
 * the mirror keeps the literal gate and the disjunct never fires.
 * The debug asserts of the entry faces (the '@' at host_start - 1
 * of lib.rs:2239, the "://" at scheme_end of lib.rs:2305) are the
 * invariant's own pins (the ':' arm of the userinfo matcher at
 * lib.rs:725-727 places the '@'; the authority branch of
 * has_authority_view places the two slashes). The byte_at(username_end)
 * reads sit below the serialization end on the post-gate path:
 * has_host forces host_start < host_end <= len with
 * username_end <= host_start, so username_end < len (the gate is
 * also what keeps the after-checkout of lib.rs:2309 nonempty, which
 * is why the (false, no terminator) match arm of set_username never
 * appends a dangling '@' to a record that reached the write).
 * ============================================================ */

/// The append-slicing face used by the userinfo write faces: a
/// subrange that starts at or above the seam of a concatenation is
/// the tail's own subrange at the shifted offsets. The plain seq
/// algebra the drain/rebuild channels reduce to (no pointwise
/// quantifier in the consumers).
proof fn append_subrange(x: Seq<u8>, y: Seq<u8>, i: int, j: int)
    requires
        0 <= i,
        i <= j,
        (x.len() as int) <= i,
        j <= (x.len() as int) + (y.len() as int),
    ensures
        (x + y).subrange(i, j)
            == y.subrange(i - (x.len() as int),
                j - (x.len() as int)),
{
    vstd::seq::lemma_seq_subrange_len(x + y, i, j);
    vstd::seq::lemma_seq_subrange_len(y,
        i - (x.len() as int), j - (x.len() as int));
    assert(((x + y).subrange(i, j).len() as int)
        == (y.subrange(i - (x.len() as int),
            j - (x.len() as int)).len() as int));
    assert forall|k: int|
        #![trigger (x + y).subrange(i, j).index(k)]
        0 <= k && k < (x + y).subrange(i, j).len() as int
        implies (x + y).subrange(i, j).index(k)
            == y.subrange(i - (x.len() as int),
                j - (x.len() as int)).index(k) by {
        vstd::seq::lemma_seq_subrange_index(x + y, i, j, k);
        vstd::seq::lemma_seq_add_index2(x, y, i + k);
        vstd::seq::lemma_seq_subrange_index(y,
            i - (x.len() as int), j - (x.len() as int), k);
    }
    vstd::seq::lemma_seq_ext_equal((x + y).subrange(i, j),
        y.subrange(i - (x.len() as int), j - (x.len() as int)));
}

/// The write arm of set_password (lib.rs:2212-2235, split out so each
/// whole-fn check stays inside the solver budget): truncate at
/// username_end, write ':' plus the USERINFO-encoded payload plus '@',
/// shift every boundary at or above the host by the region move
/// (lib.rs:2221-2224's -= old_host_start, += new_host_start), and
/// re-append the entry tail from the old host_start (upstream's
/// host_and_after checkout of lib.rs:2212/2235, hoisted to a slice
/// parameter -- the slice restructure of the set_scheme write). The
/// userinfo matcher of the written record is rebuilt exactly (':'
/// at username_end, '@' at the fresh host_start - 1); the scheme
/// prefix is untouched, so the host-tag conjuncts ride the same tag.
/* [verifier note: rlimit = the whole-fn check rides past the default
   budget: the composed postcondition (the rebuilt region plus the
   boundary-shift Option clauses over the appended tail) keeps the
   final query above the default budget; the default limit fails
   deterministically (probed: default fails in the parse-machine
   ambient, 90 closes all three harness ambients); only the resource
   ceiling is raised, no obligation is relaxed, the fn's own content
   is untouched] */
#[verifier::rlimit(90)]
pub exec fn set_password_index_write(&mut self, pw: &[u8], tail: &[u8])
    requires
        url_invariant(self),
        has_authority_view(self),
        parser::machine_domain(self.serialization.view()),
        parser::machine_domain(pw@),
        parser::machine_domain(tail@),
        (pw@.len() as int) >= 1,
        (tail@ == self.serialization.view().subrange(
            self.host_start as int, self.serialization.view().len() as int)),
        ((self.serialization.view().len() as int)
            + 3 * (pw@.len() as int) + 8) <= 0xFFFF_FFFF,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        ((final(self).serialization.view().len() as int) <= 0xFFFF_FFFF),
        ({
            let ov = old(self).serialization.view();
            let ue = old(self).username_end as int;
            let hs = old(self).host_start as int;
            let enc = parser::enc_seq(pw@, parser::EncodeSet::Userinfo);
            let nhs = ue + 2 + (enc.len() as int);
            &&& (final(self).serialization.view()
                == ov.subrange(0, ue) + seq![0x3Au8] + enc
                    + seq![0x40u8] + tail@)
            &&& (final(self).username_end as int) == ue
            &&& (final(self).host_start as int) == nhs
            &&& (final(self).host_end as int)
                == (old(self).host_end as int) + nhs - hs
            &&& (final(self).path_start as int)
                == (old(self).path_start as int) + nhs - hs
            &&& (old(self).query_start.is_none()
                ==> final(self).query_start.is_none())
            &&& (old(self).query_start.is_some()
                ==> final(self).query_start
                    == Option::Some(((old(self).query_start.unwrap()
                        as int) + nhs - hs) as u32))
            &&& (old(self).fragment_start.is_none()
                ==> final(self).fragment_start.is_none())
            &&& (old(self).fragment_start.is_some()
                ==> final(self).fragment_start
                    == Option::Some(((old(self).fragment_start.unwrap()
                        as int) + nhs - hs) as u32))
            &&& final(self).host == old(self).host
            &&& final(self).port == old(self).port
        }),
{
    let ghost ov = self.serialization.view();
    let ue32 = self.username_end;
    let hs32 = self.host_start;
    let ghost ue = ue32 as int;
    let ghost hs = hs32 as int;
    // lib.rs:2212: the host_and_after checkout (hoisted above the
    // truncate as the tail parameter, exactly upstream's own bytes)
    let n32 = url_len32(&self.serialization);
    proof {
        assert((n32 as int) == ov.len() as int);
        assert(tail@ == ov.subrange(hs, ov.len() as int));
        assert(parser::machine_domain(tail@));
    }
    // lib.rs:2213: truncate at username_end
    self.serialization.truncate(ue32 as usize);
    proof {
        assert(self.serialization.view() == ov.subrange(0, ue));
        parser::machine_domain_subrange(ov, 0, ue);
        assert(parser::machine_domain(self.serialization.view()));
    }
    // lib.rs:2214: the ':' slot
    self.serialization.push(0x3Au8);
    proof {
        assert(self.serialization.view()
            == ov.subrange(0, ue) + seq![0x3Au8]);
        parser::machine_domain_byte(0x3Au8);
        parser::machine_domain_add(ov.subrange(0, ue), seq![0x3Au8]);
        vstd::seq::lemma_seq_add_len(ov.subrange(0, ue), seq![0x3Au8]);
    }
    // lib.rs:2215-2216: the USERINFO-encoded payload
    parser::extend_percent_encode_at(&mut self.serialization,
        pw, 0, pw.len(), parser::EncodeSet::Userinfo);
    proof {
        let enc = parser::enc_seq(pw@, parser::EncodeSet::Userinfo);
        // the encode reads the whole slice (the full-range subrange
        // of the payload is the payload itself)
        assert(pw@.subrange(0, pw@.len() as int) =~= pw@);
        assert(self.serialization.view()
            == (ov.subrange(0, ue) + seq![0x3Au8]) + enc);
        parser::enc_seq_machine(pw@, parser::EncodeSet::Userinfo);
        parser::enc_seq_len_bound(pw@, parser::EncodeSet::Userinfo);
        assert((self.serialization.view().len() as int)
            == ue + 1 + (enc.len() as int));
    }
    // lib.rs:2217: the '@' slot
    self.serialization.push(0x40u8);
    proof {
        let enc = parser::enc_seq(pw@, parser::EncodeSet::Userinfo);
        let pre4 = ov.subrange(0, ue) + seq![0x3Au8] + enc
            + seq![0x40u8];
        assert(self.serialization.view() == pre4);
        parser::machine_domain_byte(0x40u8);
        parser::machine_domain_add(
            (ov.subrange(0, ue) + seq![0x3Au8]) + enc, seq![0x40u8]);
        vstd::seq::lemma_seq_add_len(ov.subrange(0, ue), seq![0x3Au8]);
        vstd::seq::lemma_seq_add_len(
            ov.subrange(0, ue) + seq![0x3Au8], enc);
        vstd::seq::lemma_seq_add_len(
            (ov.subrange(0, ue) + seq![0x3Au8]) + enc, seq![0x40u8]);
        assert((pre4.len() as int) == ue + 2 + (enc.len() as int));
    }
    // the region move (lib.rs:2219-2233): new_host_start is the
    // fresh '@' slot plus one; every boundary at or above the old
    // host start rides the two-step -= old, += new arithmetic
    let nhs32 = url_len32(&self.serialization);
    proof {
        let enc = parser::enc_seq(pw@, parser::EncodeSet::Userinfo);
        assert((nhs32 as int) == ue + 2 + (enc.len() as int));
        // the u32 domain of the two-step boundary arithmetic
        assert((self.host_end as int) >= hs);
        assert((self.path_start as int) >= (self.host_end as int));
        if self.query_start.is_some() {
            assert((self.query_start.unwrap() as int)
                >= (self.path_start as int));
        }
        if self.fragment_start.is_some() {
            assert((self.fragment_start.unwrap() as int)
                >= (self.path_start as int));
        }
        assert((self.host_end as int) - hs + (nhs32 as int)
            == (self.host_end as int) + (nhs32 as int) - hs);
        assert((self.host_end as int) - hs + (nhs32 as int)
            <= 0xFFFF_FFFF);
        assert((self.path_start as int) - hs + (nhs32 as int)
            <= 0xFFFF_FFFF);
        if self.query_start.is_some() {
            assert((self.query_start.unwrap() as int) - hs
                + (nhs32 as int) <= 0xFFFF_FFFF);
        }
        if self.fragment_start.is_some() {
            assert((self.fragment_start.unwrap() as int) - hs
                + (nhs32 as int) <= 0xFFFF_FFFF);
        }
    }
    let old_host_start = self.host_start;
    self.host_start = nhs32;
    self.host_end = self.host_end - old_host_start + nhs32;
    self.path_start = self.path_start - old_host_start + nhs32;
    match self.query_start {
        Option::Some(qi) => {
            self.query_start = Option::Some(qi - old_host_start + nhs32);
        }
        Option::None => {}
    }
    match self.fragment_start {
        Option::Some(fi) => {
            self.fragment_start
                = Option::Some(fi - old_host_start + nhs32);
        }
        Option::None => {}
    }
    // lib.rs:2235: the tail re-lands above the fresh region
    parser::vec_append_bytes(&mut self.serialization, tail);
    proof {
        let enc = parser::enc_seq(pw@, parser::EncodeSet::Userinfo);
        let nhs = nhs32 as int;
        let pre4 = ov.subrange(0, ue) + seq![0x3Au8] + enc
            + seq![0x40u8];
        let fe = self.serialization.view();
        assert(fe == pre4 + tail@);
        parser::machine_domain_add(pre4, tail@);
        assert(parser::machine_domain(fe));
        vstd::seq::lemma_seq_add_len(pre4, tail@);
        assert((fe.len() as int) == nhs + (ov.len() as int) - hs);
        // the final length stays in the u32 offset domain
        assert((enc.len() as int) <= 3 * (pw@.len() as int));
        assert((fe.len() as int) <= (ov.len() as int)
            + 3 * (pw@.len() as int) + 8);
        assert((fe.len() as int) <= 0xFFFF_FFFF);
        // the aggregate position channel: the tail byte at nhs + j is
        // the hs + j byte of the entry
        assert forall|j: int| nhs <= j && j < fe.len() as int
            implies fe.index(j) == ov.index(hs + j - nhs) by {
            vstd::seq::lemma_seq_add_index2(pre4, tail@, j);
            vstd::seq::lemma_seq_subrange_index(ov, hs,
                ov.len() as int, j - nhs);
        }
        // the head bytes below username_end are the entry's own
        assert forall|j: int| 0 <= j && j < ue
            implies fe.index(j) == ov.index(j) by {
            vstd::seq::lemma_seq_add_index1(pre4, tail@, j);
            vstd::seq::lemma_seq_add_index1(
                ov.subrange(0, ue) + seq![0x3Au8], enc
                    + seq![0x40u8], j);
            vstd::seq::lemma_seq_add_index1(
                ov.subrange(0, ue), seq![0x3Au8], j);
            vstd::seq::lemma_seq_subrange_index(ov, 0, ue, j);
        }
        // the userinfo matcher of the written record: ':' at ue,
        // '@' at nhs - 1, nhs at least ue + 2
        assert(fe.index(ue) == 0x3Au8) by {
            vstd::seq::lemma_seq_add_index1(pre4, tail@, ue);
            vstd::seq::lemma_seq_add_index1(
                ov.subrange(0, ue) + seq![0x3Au8], enc
                    + seq![0x40u8], ue);
            vstd::seq::lemma_seq_add_index2(
                ov.subrange(0, ue), seq![0x3Au8], ue);
        }
        assert(nhs >= ue + 2);
        assert(fe.index(nhs - 1) == 0x40u8) by {
            vstd::seq::lemma_seq_add_index1(pre4, tail@, nhs - 1);
        }
        // the shifted host and port regions re-land as the entry's
        // own content at the moved offsets (the shift lemma)
        let ohe = old(self).host_end as int;
        let ops = old(self).path_start as int;
        assert((self.host_start as int) == nhs);
        assert((self.host_end as int) == ohe + nhs - hs);
        assert((self.path_start as int) == ops + nhs - hs);
        Self::subrange_shift_eq(fe, ov, nhs, hs, hs, ohe);
        if ops > ohe {
            // the port region: same digit content, so the dec_val
            // conjunct of the invariant carries across
            Self::subrange_shift_eq(fe, ov, nhs, hs, ohe + 1, ops);
        }
        // the scheme prefix is untouched
        assert(fe.subrange(0, self.scheme_end as int)
            == ov.subrange(0, self.scheme_end as int)) by {
            assert forall|j: int|
                0 <= j && j < self.scheme_end as int
                implies fe.subrange(0, self.scheme_end as int).index(j)
                    == ov.subrange(0, self.scheme_end as int).index(j) by {
                vstd::seq::lemma_seq_subrange_index(fe,
                    0, self.scheme_end as int, j);
                vstd::seq::lemma_seq_subrange_index(ov,
                    0, self.scheme_end as int, j);
            }
            vstd::seq::lemma_seq_ext_equal(
                fe.subrange(0, self.scheme_end as int),
                ov.subrange(0, self.scheme_end as int));
        }
        assert(url_invariant(self));
    }
}

/// The removal arm of set_password (lib.rs:2236-2259, split out so
/// each whole-fn check stays inside the solver budget): drain the
/// ':' plus the password payload (plus the '@' as well when the
/// username region is empty -- the end anchor of lib.rs:2243-2247)
/// through the truncate+re-append drain model, and move every
/// boundary at or above the drained span down by its length. The
/// debug_assert of lib.rs:2238-2239 is the invariant's own ':'-arm
/// pin (the '@' at host_start - 1 of lib.rs:725-727), so the assert
/// carries no runtime obligation on this face.
/* [verifier note: rlimit = the whole-fn check rides past the default
   budget: the invariant close over the drained channel keeps the
   final query above the default budget; the default limit fails
   deterministically. The channel's first form (a pointwise
   position-channel assert-forall feeding subrange_shift_eq)
   ambient-flipped hard: it closed the parse-machine and ut-read-api
   ambients at 90-110 while the coverage-props ambient re-opened at
   every probed value up to 200, and the four-block restructure
   flipped the failure into the parse-machine ambient at every value
   up to 300 -- the pointwise channel's trigger storm (the drain
   ensure's index foralls matching every derived index term) was the
   cause. The landed form replaces the pointwise channel with the
   plain append-slicing algebra (append_subrange plus the subrange
   composition: the tail plane, the shifted host/port regions, the
   dec_val carry), which closes all three ambients at 90; only the
   resource ceiling is raised, no obligation is relaxed, the fn's
   own obligations are untouched] */
#[verifier::rlimit(90)]
pub exec fn set_password_drop_write(&mut self)
    requires
        url_invariant(self),
        has_authority_view(self),
        parser::machine_domain(self.serialization.view()),
        ((self.username_end as int)
            < (self.serialization.view().len() as int)),
        (self.serialization.view().index(
            self.username_end as int) == 0x3Au8),
        // the host-first-byte dogma of the parser-reachable records
        // (the empty-username face re-lands the first host byte at
        // username_end, where the matcher's ':'/'@' arms would
        // otherwise misfire on hand-built host regions carrying a
        // ':' or '@' byte -- no host serialization starts with one)
        (((self.host_start as int)
            == (self.serialization.view().len() as int))
            || ((self.serialization.view().index(
                    self.host_start as int) != 0x3Au8)
                && (self.serialization.view().index(
                    self.host_start as int) != 0x40u8))),
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        ((final(self).serialization.view().len() as int)
            <= 0xFFFF_FFFF),
        ({
            let ov = old(self).serialization.view();
            let ue = old(self).username_end as int;
            let hs = old(self).host_start as int;
            let end = if (old(self).scheme_end as int) + 3 == ue {
                hs
            } else {
                hs - 1
            };
            let off = end - ue;
            &&& (final(self).serialization.view()
                == ov.subrange(0, ue)
                    + ov.subrange(end, ov.len() as int))
            &&& (final(self).username_end as int) == ue
            &&& (final(self).host_start as int) == hs - off
            &&& (final(self).host_end as int)
                == (old(self).host_end as int) - off
            &&& (final(self).path_start as int)
                == (old(self).path_start as int) - off
            &&& (old(self).query_start.is_none()
                ==> final(self).query_start.is_none())
            &&& (old(self).query_start.is_some()
                ==> final(self).query_start
                    == Option::Some(((old(self).query_start.unwrap()
                        as int) - off) as u32))
            &&& (old(self).fragment_start.is_none()
                ==> final(self).fragment_start.is_none())
            &&& (old(self).fragment_start.is_some()
                ==> final(self).fragment_start
                    == Option::Some(((old(self).fragment_start.unwrap()
                        as int) - off) as u32))
            &&& final(self).host == old(self).host
            &&& final(self).port == old(self).port
        }),
{
    let ghost ov = self.serialization.view();
    let se32 = self.scheme_end;
    let ue32 = self.username_end;
    let hs32 = self.host_start;
    let ghost ue = ue32 as int;
    let ghost hs = hs32 as int;
    // lib.rs:2240-2247: the drain span (the ':' always, the '@' too
    // when no username precedes it)
    let username_start = se32 + 3;
    let empty_username = username_start == ue32;
    let start = ue32;
    let end = if empty_username { hs32 } else { hs32 - 1 };
    proof {
        // the span sits inside the serialization (the invariant's
        // ':' arm: hs >= ue + 2, so both anchors are valid)
        if empty_username {
            assert((end as int) == hs);
            assert(ue <= hs);
        } else {
            assert((end as int) == hs - 1);
            assert(hs >= ue + 2);
        }
        assert((start as int) <= (end as int));
        assert((end as int) <= (ov.len() as int));
    }
    // lib.rs:2248: the drain (the truncate + re-append model)
    vec_drain_middle(&mut self.serialization, start, end);
    // lib.rs:2249-2258: the boundary move
    let offset = end - start;
    proof {
        assert((offset as int) == (end as int) - ue);
    }
    self.host_start = self.host_start - offset;
    self.host_end = self.host_end - offset;
    self.path_start = self.path_start - offset;
    match self.query_start {
        Option::Some(qi) => {
            self.query_start = Option::Some(qi - offset);
        }
        Option::None => {}
    }
    match self.fragment_start {
        Option::Some(fi) => {
            self.fragment_start = Option::Some(fi - offset);
        }
        Option::None => {}
    }
    // the drain face: the kept prefix [0, ue) plus the shifted tail
    // from the drain anchor
    proof {
        let fe = self.serialization.view();
        let endg = end as int;
        let off = offset as int;
        assert((fe.len() as int) == (ov.len() as int) - off);
        assert((fe.len() as int) <= 0xFFFF_FFFF);
        assert(fe == ov.subrange(0, ue)
            + ov.subrange(endg, ov.len() as int));
        // the tail plane: everything from the fresh host start on is
        // the entry's own content from the drain anchor on (the
        // plain append-slicing algebra, no pointwise channel)
        assert(fe.subrange(hs - off, fe.len() as int)
            == ov.subrange(hs, ov.len() as int)) by {
            Self::append_subrange(ov.subrange(0, ue),
                ov.subrange(endg, ov.len() as int),
                hs - off, fe.len() as int);
            vstd::seq::lemma_seq_subrange_composition(ov, endg,
                ov.len() as int, hs - off - ue,
                (ov.len() as int) - off - ue);
        }
    }
    // the shifted host and port regions re-land as the entry's own
    // content at the moved offsets
    proof {
        let fe = self.serialization.view();
        let endg = end as int;
        let off = offset as int;
        let ohe = old(self).host_end as int;
        let ops = old(self).path_start as int;
        assert((self.host_start as int) == hs - off);
        assert((self.host_end as int) == ohe - off);
        assert((self.path_start as int) == ops - off);
        assert(fe.subrange(hs - off, ohe - off)
            == ov.subrange(hs, ohe)) by {
            Self::append_subrange(ov.subrange(0, ue),
                ov.subrange(endg, ov.len() as int),
                hs - off, ohe - off);
            vstd::seq::lemma_seq_subrange_composition(ov, endg,
                ov.len() as int, hs - off - ue, ohe - off - ue);
        }
        if ops > ohe {
            // the port region: same digit content, so the dec_val
            // conjunct of the invariant carries across
            assert(fe.subrange(ohe - off + 1, ops - off)
                == ov.subrange(ohe + 1, ops)) by {
                Self::append_subrange(ov.subrange(0, ue),
                    ov.subrange(endg, ov.len() as int),
                    ohe - off + 1, ops - off);
                vstd::seq::lemma_seq_subrange_composition(ov, endg,
                    ov.len() as int, ohe - off + 1 - ue,
                    ops - off - ue);
            }
            assert(dec_val(fe.subrange(ohe - off + 1, ops - off))
                == dec_val(ov.subrange(ohe + 1, ops)));
        }
    }
    // the userinfo matcher of the written record: the byte at ue is
    // the entry's own byte at the drain anchor (the face is vacuous
    // exactly when the drain consumes the whole tail -- then ue is
    // the serialization end and the invariant's match is out of
    // scope)
    proof {
        let fe = self.serialization.view();
        let endg = end as int;
        if ue < fe.len() as int {
            assert(endg < ov.len() as int);
            assert(fe.index(ue) == ov.index(endg)) by {
                vstd::seq::lemma_seq_add_index2(
                    ov.subrange(0, ue),
                    ov.subrange(endg, ov.len() as int), ue);
                vstd::seq::lemma_seq_subrange_index(ov, endg,
                    ov.len() as int, 0);
            }
        }
    }
    proof {
        let fe = self.serialization.view();
        let endg = end as int;
        let off = offset as int;
        if empty_username {
            // the '@' went with the span: the first host byte
            // re-lands at username_end, a ':'/'@'-free byte by the
            // host-first-byte dogma, so the wildcard arm fires and
            // rides the empty-username pin (username_end ==
            // scheme_end + 3)
            assert(endg == hs);
            assert(ue == se32 as int + 3);
            if ue < fe.len() as int {
                assert(fe.index(ue) == ov.index(endg));
                assert(fe.index(ue) != 0x3Au8);
                assert(fe.index(ue) != 0x40u8);
            }
        } else {
            // the '@' stayed: the matcher's '@' arm re-lands exactly
            assert(endg == hs - 1);
            assert(ov.index(endg) == 0x40u8);
            assert((self.host_start as int) == ue + 1);
        }
    }
    // the query/fragment slots keep their pins at the moved offsets
    // (the tail plane's own bytes); the invariant closes off the
    // matcher faces above and the shifted regions
    proof {
        let fe = self.serialization.view();
        let off = offset as int;
        if self.query_start.is_some() {
            let qi = self.query_start.unwrap() as int;
            vstd::seq::lemma_seq_subrange_index(fe, hs - off,
                fe.len() as int, qi - (hs - off));
            vstd::seq::lemma_seq_subrange_index(ov, hs,
                ov.len() as int, qi - hs + off);
            assert(fe.index(qi) == ov.index(qi + off));
            assert(fe.index(qi) == 0x3Fu8);
        }
        if self.fragment_start.is_some() {
            let fi = self.fragment_start.unwrap() as int;
            vstd::seq::lemma_seq_subrange_index(fe, hs - off,
                fe.len() as int, fi - (hs - off));
            vstd::seq::lemma_seq_subrange_index(ov, hs,
                ov.len() as int, fi - hs + off);
            assert(fe.index(fi) == ov.index(fi + off));
            assert(fe.index(fi) == 0x23u8);
        }
        assert(url_invariant(self));
    }
}

/// Origin Rust (lib.rs:2205-2261): pub fn set_password(&mut self,
///   password: Option<&str>) -> Result<(), ()> -- the entry gate of
/// lib.rs:2207 (no host / the empty-Domain face / the file scheme,
/// all three Err with the record untouched), then the write arm
/// (the nonempty payload: set_password_index_write above) or the
/// removal arm (empty payload over a ':' at username_end:
/// set_password_drop_write above) or the nothing-to-do face (empty
/// payload, no ':' at username_end -- Ok with the record untouched).
/// The Option face of the argument is upstream's
/// unwrap_or_default(): None is the empty payload. CONE: the entry
/// record is a base_url_face record of the machine byte domain, and
/// the host region's first byte (when the host region exists) is
/// neither ':' nor '@' -- the parser-reachable host serializations
/// (Domain labels, IPv4, the bracketed IPv6) never open with either
/// byte, and the empty-username removal face re-lands that byte at
/// username_end where the invariant's userinfo matcher reads it.
pub exec fn set_password(&mut self,
    password: Option<&[u8]>) -> (r: Result<(), ()>)
    requires
        parser::base_url_face(self),
        ((self.serialization.view().len() as int)
            + 3 * (match password {
                Option::Some(p) => (p@.len() as int),
                Option::None => 0int,
            }) + 8) <= 0xFFFF_FFFF,
        (match password {
            Option::Some(p) => parser::machine_domain(p@),
            Option::None => true,
        }),
        (((self.host_start as int)
            == (self.serialization.view().len() as int))
            || ((self.serialization.view().index(
                    self.host_start as int) != 0x3Au8)
                && (self.serialization.view().index(
                    self.host_start as int) != 0x40u8))),
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        (r.is_err() ==> ({
            // do-nothing face: every component of the entry record
            // survives untouched
            &&& (final(self).serialization.view()
                == old(self).serialization.view())
            &&& (final(self).scheme_end as int)
                == (old(self).scheme_end as int)
            &&& (final(self).username_end as int)
                == (old(self).username_end as int)
            &&& (final(self).host_start as int)
                == (old(self).host_start as int)
            &&& (final(self).host_end as int)
                == (old(self).host_end as int)
            &&& final(self).host == old(self).host
            &&& final(self).port == old(self).port
            &&& (final(self).path_start as int)
                == (old(self).path_start as int)
            &&& final(self).query_start == old(self).query_start
            &&& final(self).fragment_start
                == old(self).fragment_start
        })),
        (r.is_ok() ==> ({
            let ov = old(self).serialization.view();
            let ue = old(self).username_end as int;
            let hs = old(self).host_start as int;
            let pwv = match password {
                Option::Some(p) => p@,
                Option::None => Seq::empty(),
            };
            let enc = parser::enc_seq(pwv, parser::EncodeSet::Userinfo);
            &&& (ue < (ov.len() as int))
            &&& ((pwv.len() as int) > 0 ==> ({
                // the write arm (lib.rs:2211-2235)
                let nhs = ue + 2 + (enc.len() as int);
                &&& (final(self).serialization.view()
                    == ov.subrange(0, ue) + seq![0x3Au8] + enc
                        + seq![0x40u8]
                        + ov.subrange(hs, ov.len() as int))
                &&& (final(self).username_end as int) == ue
                &&& (final(self).host_start as int) == nhs
                &&& (final(self).host_end as int)
                    == (old(self).host_end as int) + nhs - hs
                &&& (final(self).path_start as int)
                    == (old(self).path_start as int) + nhs - hs
                &&& (old(self).query_start.is_none()
                    ==> final(self).query_start.is_none())
                &&& (old(self).query_start.is_some()
                    ==> final(self).query_start
                        == Option::Some(((old(self).query_start.unwrap()
                            as int) + nhs - hs) as u32))
                &&& (old(self).fragment_start.is_none()
                    ==> final(self).fragment_start.is_none())
                &&& (old(self).fragment_start.is_some()
                    ==> final(self).fragment_start
                        == Option::Some(((old(self).fragment_start.unwrap()
                            as int) + nhs - hs) as u32))
                &&& final(self).host == old(self).host
                &&& final(self).port == old(self).port
            }))
            &&& ((pwv.len() as int) == 0
                && ov.index(ue) == 0x3Au8 ==> ({
                // the removal arm (lib.rs:2236-2259)
                let end = if (old(self).scheme_end as int) + 3 == ue {
                    hs
                } else {
                    hs - 1
                };
                let off = end - ue;
                &&& (final(self).serialization.view()
                    == ov.subrange(0, ue)
                        + ov.subrange(end, ov.len() as int))
                &&& (final(self).username_end as int) == ue
                &&& (final(self).host_start as int) == hs - off
                &&& (final(self).host_end as int)
                    == (old(self).host_end as int) - off
                &&& (final(self).path_start as int)
                    == (old(self).path_start as int) - off
                &&& (old(self).query_start.is_none()
                    ==> final(self).query_start.is_none())
                &&& (old(self).query_start.is_some()
                    ==> final(self).query_start
                        == Option::Some(((old(self).query_start.unwrap()
                            as int) - off) as u32))
                &&& (old(self).fragment_start.is_none()
                    ==> final(self).fragment_start.is_none())
                &&& (old(self).fragment_start.is_some()
                    ==> final(self).fragment_start
                        == Option::Some(((old(self).fragment_start.unwrap()
                            as int) - off) as u32))
                &&& final(self).host == old(self).host
                &&& final(self).port == old(self).port
            }))
            &&& ((pwv.len() as int) == 0
                && ov.index(ue) != 0x3Au8 ==> ({
                // the nothing-to-do face (lib.rs:2260)
                &&& (final(self).serialization.view()
                    == old(self).serialization.view())
                &&& (final(self).scheme_end as int)
                    == (old(self).scheme_end as int)
                &&& (final(self).username_end as int)
                    == (old(self).username_end as int)
                &&& (final(self).host_start as int)
                    == (old(self).host_start as int)
                &&& (final(self).host_end as int)
                    == (old(self).host_end as int)
                &&& final(self).host == old(self).host
                &&& final(self).port == old(self).port
                &&& (final(self).path_start as int)
                    == (old(self).path_start as int)
                &&& final(self).query_start == old(self).query_start
                &&& final(self).fragment_start
                    == old(self).fragment_start
            }))
        })),
{
    // the entry gate (lib.rs:2207): no host, the empty-Domain face
    // (dead under the invariant, kept literal), or the file scheme
    let hh = self.has_host();
    let dom_empty = match self.host {
        HostInternal::Domain => self.host_start == self.host_end,
        _ => false,
    };
    let sch = self.scheme();
    let is_file = sch.len() == 4usize
        && sch[0usize] == 0x66u8
        && sch[1usize] == 0x69u8
        && sch[2usize] == 0x6Cu8
        && sch[3usize] == 0x65u8;
    if !hh || dom_empty || is_file {
        return Result::Err(());
    }
    // the post-gate geometry: has_host forces the authority branch
    // (host None <=> the anarchist branch), so username_end sits
    // strictly below the serialization end
    proof {
        assert(has_authority_view(self));
        assert((self.username_end as int)
            <= (self.host_start as int));
        assert((self.host_start as int) < (self.host_end as int));
        assert((self.host_end as int)
            <= (self.serialization.view().len() as int));
        assert((self.username_end as int)
            < (self.serialization.view().len() as int));
    }
    let pwlen: usize = match password {
        Option::Some(p) => p.len(),
        Option::None => 0,
    };
    if pwlen > 0 {
        // lib.rs:2210-2216: the write arm with a nonempty payload
        let pw = password.unwrap();
        proof {
            assert(password.is_some());
            assert(pw@ == (match password {
                Option::Some(p) => p@,
                Option::None => Seq::empty(),
            }));
        }
        let tail = bytes_slice(&self.serialization, self.host_start,
            url_len32(&self.serialization));
        proof {
            assert(tail.view() == self.serialization.view().subrange(
                self.host_start as int,
                self.serialization.view().len() as int));
            parser::machine_domain_subrange(
                self.serialization.view(),
                self.host_start as int,
                self.serialization.view().len() as int);
            assert(parser::machine_domain(tail.view()));
        }
        self.set_password_index_write(pw, &tail);
        return Result::Ok(());
    }
    // the empty-payload faces (lib.rs:2236-2260): the removal arm
    // over a ':' at username_end, else the nothing-to-do face
    let ue_byte = self.byte_at(self.username_end);
    proof {
        assert(ue_byte
            == self.serialization.view().index(
                self.username_end as int));
    }
    if ue_byte == 0x3Au8 {
        self.set_password_drop_write();
        return Result::Ok(());
    }
    Result::Ok(())
}

/// The byte equality of the equal-value face (lib.rs:2306-2308's
/// str ==): the two runs are equal exactly when their lengths match
/// and every byte pair matches (the early faces: a length mismatch
/// kills ext-equality outright, a divergent byte witnesses it).
pub exec fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        proof {
            assert(a@.len() != b@.len());
            assert(a@ != b@);
        }
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a@.len() == b@.len(),
            forall|j: int| 0 <= j && j < i as int
                ==> a@.index(j) == b@.index(j),
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            proof {
                assert(a@.index(i as int) != b@.index(i as int));
                assert(a@ != b@);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(i == a.len());
        assert(forall|j: int| 0 <= j && j < a@.len() as int
            ==> a@.index(j) == b@.index(j));
        assert(a@ =~= b@);
    }
    true
}

/* ============================================================
 * set_username (lib.rs:2299-2348): the username write face. The
 * upstream match on (new_username_is_empty, after_username's first
 * char) reduces to three byte geometries over the after-checkout:
 * the push-through geometry (the (false,'@'), (_ ,':') and
 * (true,_) arms: the checkout re-lands whole behind the fresh
 * username), the '@'-drop geometry (the (true,'@') arm: the stale
 * '@' of an emptied userinfo goes with the old username), and the
 * '@'-insert geometry (the (false,_) arm: a fresh '@' separates the
 * new username from a checkout that carried no terminator). The
 * invariant's userinfo matcher drives which arm closes: the entry
 * byte at username_end is ':' or '@' or the region is empty
 * (username_end == scheme_end + 3), and the empty-region face with
 * a terminator-free checkout is exactly the face where the matcher
 * needs the userinfo-interior dogma (no bytes between the "://" and
 * the host region other than the username ':' password '@' run) --
 * the cone conjunct of the wrapper below. The chars().next() of the
 * upstream match is the first byte of the checkout (the '@' and ':'
 * faces are ASCII; a multi-byte char's lead byte is never either).
 * ============================================================ */

/// The push-through geometry of set_username (lib.rs:2310-2325's
/// (false,'@') / (_ ,':') / (true,_) arms, split out so each
/// whole-fn check stays inside the solver budget): truncate at the
/// userinfo start, write the USERINFO-encoded username, and re-land
/// the checkout whole; every boundary at or above the old
/// username_end moves by (fresh region length - old username_end).
/// The invariant's matcher closes on the entry terminator faces:
/// the checkout's own head byte at the fresh username_end is the
/// entry byte at username_end (':' / '@' / the empty-region
/// wildcard).
/* [verifier note: rlimit = the whole-fn check rides past the default
   budget: the invariant close over the pushed checkout (the entry
   terminator faces re-landed at the fresh username_end plus the
   shifted port-region dec_val conjunct) keeps the final query above
   the default budget; the default limit fails deterministically
   (probed: default fails in the parse-machine ambient, 90 closes
   all three harness ambients); only the resource ceiling is raised,
   no obligation is relaxed, the fn's own content is untouched] */
#[verifier::rlimit(90)]
pub exec fn set_username_push_write(&mut self, username: &[u8],
    after: &[u8])
    requires
        url_invariant(self),
        has_authority_view(self),
        parser::machine_domain(self.serialization.view()),
        parser::machine_domain(username@),
        parser::machine_domain(after@),
        (after@ == self.serialization.view().subrange(
            self.username_end as int,
            self.serialization.view().len() as int)),
        (after@.len() as int) >= 1,
        // the pushed checkout must open with an entry terminator
        // (or the fresh username must be empty over an empty
        // userinfo region -- the invariant's wildcard face)
        ((after@[0] == 0x3Au8) || (after@[0] == 0x40u8)
            || (username@.len() as int) == 0),
        ((self.serialization.view().len() as int)
            + 3 * (username@.len() as int) + 8) <= 0xFFFF_FFFF,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        ((final(self).serialization.view().len() as int)
            <= 0xFFFF_FFFF),
        ({
            let ov = old(self).serialization.view();
            let ue = old(self).username_end as int;
            let us = (old(self).scheme_end as int) + 3;
            let enc = parser::enc_seq(username@,
                parser::EncodeSet::Userinfo);
            let nue = us + (enc.len() as int);
            &&& (final(self).serialization.view()
                == ov.subrange(0, us) + enc + after@)
            &&& (final(self).username_end as int) == nue
            &&& (final(self).host_start as int)
                == (old(self).host_start as int) + nue - ue
            &&& (final(self).host_end as int)
                == (old(self).host_end as int) + nue - ue
            &&& (final(self).path_start as int)
                == (old(self).path_start as int) + nue - ue
            &&& (old(self).query_start.is_none()
                ==> final(self).query_start.is_none())
            &&& (old(self).query_start.is_some()
                ==> final(self).query_start
                    == Option::Some(((old(self).query_start.unwrap()
                        as int) + nue - ue) as u32))
            &&& (old(self).fragment_start.is_none()
                ==> final(self).fragment_start.is_none())
            &&& (old(self).fragment_start.is_some()
                ==> final(self).fragment_start
                    == Option::Some(((old(self).fragment_start.unwrap()
                        as int) + nue - ue) as u32))
            &&& final(self).host == old(self).host
            &&& final(self).port == old(self).port
        }),
{
    let ghost ov = self.serialization.view();
    let se32 = self.scheme_end;
    let ue32 = self.username_end;
    let hs32 = self.host_start;
    let ghost ue = ue32 as int;
    let ghost hs = hs32 as int;
    let ghost us = se32 as int + 3;
    let us_u32 = se32 + 3;
    // lib.rs:2309: the after-checkout (hoisted above the truncate)
    proof {
        assert((us_u32 as int) == us);
        assert((us_u32 as int) <= ov.len() as int);
        assert(after@ == ov.subrange(ue, ov.len() as int));
        assert(parser::machine_domain(after@));
    }
    // lib.rs:2310: truncate at the userinfo start
    self.serialization.truncate(us_u32 as usize);
    proof {
        assert(self.serialization.view() == ov.subrange(0, us));
        parser::machine_domain_subrange(ov, 0, us);
        assert(parser::machine_domain(self.serialization.view()));
    }
    // lib.rs:2311-2312: the USERINFO-encoded username
    parser::extend_percent_encode_at(&mut self.serialization,
        username, 0, username.len(), parser::EncodeSet::Userinfo);
    proof {
        let enc = parser::enc_seq(username@,
            parser::EncodeSet::Userinfo);
        assert(username@.subrange(0, username@.len() as int) =~= username@);
        assert(self.serialization.view()
            == ov.subrange(0, us) + enc);
        parser::enc_seq_machine(username@,
            parser::EncodeSet::Userinfo);
        parser::enc_seq_len_bound(username@,
            parser::EncodeSet::Userinfo);
    }
    // the fresh username_end (lib.rs:2315)
    let nue32 = url_len32(&self.serialization);
    proof {
        let enc = parser::enc_seq(username@,
            parser::EncodeSet::Userinfo);
        assert((nue32 as int) == us + (enc.len() as int));
    }
    self.username_end = nue32;
    // lib.rs:2319-2331: the push-through (the checkout re-lands
    // whole; removed is the old username_end, added the fresh end)
    parser::vec_append_bytes(&mut self.serialization, after);
    proof {
        let enc = parser::enc_seq(username@,
            parser::EncodeSet::Userinfo);
        let pre2 = ov.subrange(0, us) + enc;
        let fe = self.serialization.view();
        let nue = nue32 as int;
        assert(fe == pre2 + after@);
        parser::machine_domain_add(pre2, after@);
        assert(parser::machine_domain(fe));
        vstd::seq::lemma_seq_add_len(pre2, after@);
        assert((fe.len() as int) == nue
            + (ov.len() as int) - ue);
        assert((fe.len() as int) <= (ov.len() as int)
            + 3 * (username@.len() as int) + 8);
        assert((fe.len() as int) <= 0xFFFF_FFFF);
        // the position channel: the checkout byte at nue + j is the
        // entry byte at ue + j
        assert forall|j: int| #![trigger fe.index(j)]
            nue <= j && j < fe.len() as int
            implies fe.index(j) == ov.index(ue + j - nue) by {
            if nue <= j && j < fe.len() as int {
                vstd::seq::lemma_seq_add_index2(pre2, after@, j);
                vstd::seq::lemma_seq_subrange_index(ov, ue,
                    ov.len() as int, j - nue);
            }
        }
        // the matcher faces on the written record, by the entry
        // terminator at ue (the checkout's own head byte)
        assert(after@[0] == ov.index(ue)) by {
            vstd::seq::lemma_seq_add_index2(pre2, after@, nue);
            vstd::seq::lemma_seq_subrange_index(ov, ue,
                ov.len() as int, 0);
        }
        if after@[0] == 0x40u8 {
            // the entry matcher's '@' arm: the host starts exactly
            // one above the old username_end
            assert((hs as int) == ue + 1);
        }
        if after@[0] == 0x3Au8 {
            // the entry matcher's ':' arm: the '@' below the host
            // start re-lands above the fresh end
            assert((hs as int) >= ue + 2);
        }
        if after@[0] != 0x3Au8 && after@[0] != 0x40u8 {
            // the entry matcher's wildcard face: the userinfo
            // region was empty, so the fresh username is the empty
            // encode over the same slot (a pure no-op shift)
            assert(ue == us);
            assert((enc.len() as int) == 0);
            assert(nue == us);
        }
    }
    // lib.rs:2334-2346: the boundary move (two-step, upstream's own
    // -= removed_bytes += added_bytes)
    let removed32 = ue32;
    let added32 = nue32;
    proof {
        assert((self.host_start as int) >= ue);
        assert((self.host_end as int) >= (self.host_start as int));
        assert((self.path_start as int) >= (self.host_end as int));
        if self.query_start.is_some() {
            assert((self.query_start.unwrap() as int)
                >= (self.path_start as int));
        }
        if self.fragment_start.is_some() {
            assert((self.fragment_start.unwrap() as int)
                >= (self.path_start as int));
        }
        assert((self.host_start as int) - ue + (nue32 as int)
            <= 0xFFFF_FFFF);
        assert((self.host_end as int) - ue + (nue32 as int)
            <= 0xFFFF_FFFF);
        assert((self.path_start as int) - ue + (nue32 as int)
            <= 0xFFFF_FFFF);
        if self.query_start.is_some() {
            assert((self.query_start.unwrap() as int) - ue
                + (nue32 as int) <= 0xFFFF_FFFF);
        }
        if self.fragment_start.is_some() {
            assert((self.fragment_start.unwrap() as int) - ue
                + (nue32 as int) <= 0xFFFF_FFFF);
        }
    }
    self.host_start = self.host_start - removed32 + added32;
    self.host_end = self.host_end - removed32 + added32;
    self.path_start = self.path_start - removed32 + added32;
    match self.query_start {
        Option::Some(qi) => {
            self.query_start
                = Option::Some(qi - removed32 + added32);
        }
        Option::None => {}
    }
    match self.fragment_start {
        Option::Some(fi) => {
            self.fragment_start
                = Option::Some(fi - removed32 + added32);
        }
        Option::None => {}
    }
    proof {
        let enc = parser::enc_seq(username@,
            parser::EncodeSet::Userinfo);
        let pre2 = ov.subrange(0, us) + enc;
        let fe = self.serialization.view();
        let nue = nue32 as int;
        // the shifted host and port regions re-land as the entry's
        // own content at the moved offsets
        let ohe = old(self).host_end as int;
        let ops = old(self).path_start as int;
        assert((self.host_start as int) == hs + nue - ue);
        assert((self.host_end as int) == ohe + nue - ue);
        assert((self.path_start as int) == ops + nue - ue);
        Self::subrange_shift_eq(fe, ov, nue, ue, hs, ohe);
        assert(fe.subrange(hs + nue - ue, ohe + nue - ue)
            == ov.subrange(hs, ohe));
        if ops > ohe {
            // the port region: same digit content, so the dec_val
            // conjunct of the invariant carries across
            Self::subrange_shift_eq(fe, ov, nue, ue, ohe + 1, ops);
            assert(fe.subrange(ohe + nue - ue + 1,
                ops + nue - ue) == ov.subrange(ohe + 1, ops));
            assert(dec_val(fe.subrange(ohe + nue - ue + 1,
                ops + nue - ue))
                == dec_val(ov.subrange(ohe + 1, ops)));
        }
        // the query/fragment slots keep their pins at the moved
        // offsets (the channel's own bytes)
        if self.query_start.is_some() {
            let qi = self.query_start.unwrap() as int;
            assert(fe.index(qi) == ov.index(ue + qi - nue));
            assert(fe.index(qi) == 0x3Fu8);
        }
        if self.fragment_start.is_some() {
            let fi = self.fragment_start.unwrap() as int;
            assert(fe.index(fi) == ov.index(ue + fi - nue));
            assert(fe.index(fi) == 0x23u8);
        }
        assert(url_invariant(self));
    }
}

/// The '@'-drop geometry of set_username (lib.rs:2310-2322's
/// (true,'@') arm, split out so each whole-fn check stays inside
/// the solver budget): truncate at the userinfo start, write the
/// empty encode (the fresh username is empty), and re-land the
/// checkout minus its head -- the stale '@' of an emptied userinfo
/// goes with the old username; every boundary at or above the old
/// host start moves down by the dropped span (lib.rs:2321's
/// removed_bytes increment).
/* [verifier note: rlimit = the whole-fn check rides past the default
   budget: the invariant close over the stale-'@' drop (the wildcard
   matcher arm over the re-landed first host byte plus the shifted
   port-region dec_val conjunct) keeps the final query above the
   default budget; the default limit fails deterministically
   (probed: default fails in the parse-machine ambient, 90 closes
   all three harness ambients); only the resource ceiling is raised,
   no obligation is relaxed, the fn's own content is untouched] */
#[verifier::rlimit(90)]
pub exec fn set_username_dropat_write(&mut self, after: &Vec<u8>)
    requires
        url_invariant(self),
        has_authority_view(self),
        parser::machine_domain(self.serialization.view()),
        parser::machine_domain(after@),
        (after@ == self.serialization.view().subrange(
            self.username_end as int,
            self.serialization.view().len() as int)),
        (after@.len() as int) >= 1,
        (after@[0] == 0x40u8),
        // the host-first-byte dogma (the stale-'@' drop re-lands the
        // first host byte at the userinfo start, where the
        // invariant's matcher reads it)
        (((self.host_start as int)
            == (self.serialization.view().len() as int))
            || ((self.serialization.view().index(
                    self.host_start as int) != 0x3Au8)
                && (self.serialization.view().index(
                    self.host_start as int) != 0x40u8))),
        ((self.serialization.view().len() as int) + 8)
            <= 0xFFFF_FFFF,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        ((final(self).serialization.view().len() as int)
            <= 0xFFFF_FFFF),
        ({
            let ov = old(self).serialization.view();
            let ue = old(self).username_end as int;
            let hs = old(self).host_start as int;
            let us = (old(self).scheme_end as int) + 3;
            let shift = us - ue - 1;
            &&& (final(self).serialization.view()
                == ov.subrange(0, us)
                    + after@.subrange(1, after@.len() as int))
            &&& (final(self).username_end as int) == us
            &&& (final(self).host_start as int) == hs + shift
            &&& (final(self).host_end as int)
                == (old(self).host_end as int) + shift
            &&& (final(self).path_start as int)
                == (old(self).path_start as int) + shift
            &&& (old(self).query_start.is_none()
                ==> final(self).query_start.is_none())
            &&& (old(self).query_start.is_some()
                ==> final(self).query_start
                    == Option::Some(((old(self).query_start.unwrap()
                        as int) + shift) as u32))
            &&& (old(self).fragment_start.is_none()
                ==> final(self).fragment_start.is_none())
            &&& (old(self).fragment_start.is_some()
                ==> final(self).fragment_start
                    == Option::Some(((old(self).fragment_start.unwrap()
                        as int) + shift) as u32))
            &&& final(self).host == old(self).host
            &&& final(self).port == old(self).port
        }),
{
    let ghost ov = self.serialization.view();
    let se32 = self.scheme_end;
    let ue32 = self.username_end;
    let hs32 = self.host_start;
    let ghost ue = ue32 as int;
    let ghost hs = hs32 as int;
    let ghost us = se32 as int + 3;
    let us_u32 = se32 + 3;
    proof {
        assert((us_u32 as int) == us);
        assert((us_u32 as int) <= ov.len() as int);
        // the entry matcher's '@' arm (the checkout head is the
        // entry byte at username_end): the host starts right above
        assert(after@[0] == ov.index(ue));
        assert((hs as int) == ue + 1);
        assert(us <= ue);
    }
    // lib.rs:2310: truncate at the userinfo start
    self.serialization.truncate(us_u32 as usize);
    proof {
        assert(self.serialization.view() == ov.subrange(0, us));
        parser::machine_domain_subrange(ov, 0, us);
        assert(parser::machine_domain(self.serialization.view()));
    }
    // the fresh username_end is the userinfo start itself (the
    // empty encode wrote nothing; lib.rs:2315/2318)
    let nue32 = url_len32(&self.serialization);
    proof {
        assert((nue32 as int) == us);
    }
    self.username_end = nue32;
    // lib.rs:2322: the checkout minus its head ('@') re-lands
    let rest = bytes_slice(after, 1, url_len32(after));
    proof {
        assert(rest.view()
            == after@.subrange(1, after@.len() as int));
        parser::machine_domain_subrange(after@, 1,
            after@.len() as int);
        assert(parser::machine_domain(rest.view()));
    }
    parser::vec_append_bytes(&mut self.serialization, &rest);
    // lib.rs:2314/2316/2321: removed is ue + 1 (the '@' went too),
    // added is the fresh end (the userinfo start)
    let removed32 = ue32 + 1;
    let added32 = nue32;
    proof {
        assert((self.host_start as int) == ue + 1);
        assert((self.host_start as int) >= removed32 as int);
        assert((self.host_end as int) >= (self.host_start as int));
        assert((self.path_start as int) >= (self.host_end as int));
        if self.query_start.is_some() {
            assert((self.query_start.unwrap() as int)
                >= (self.path_start as int));
        }
        if self.fragment_start.is_some() {
            assert((self.fragment_start.unwrap() as int)
                >= (self.path_start as int));
        }
        assert((self.host_start as int) - (removed32 as int)
            + (added32 as int) <= 0xFFFF_FFFF);
        assert((self.host_end as int) - (removed32 as int)
            + (added32 as int) <= 0xFFFF_FFFF);
        assert((self.path_start as int) - (removed32 as int)
            + (added32 as int) <= 0xFFFF_FFFF);
        if self.query_start.is_some() {
            assert((self.query_start.unwrap() as int)
                - (removed32 as int) + (added32 as int)
                <= 0xFFFF_FFFF);
        }
        if self.fragment_start.is_some() {
            assert((self.fragment_start.unwrap() as int)
                - (removed32 as int) + (added32 as int)
                <= 0xFFFF_FFFF);
        }
    }
    self.host_start = self.host_start - removed32 + added32;
    self.host_end = self.host_end - removed32 + added32;
    self.path_start = self.path_start - removed32 + added32;
    match self.query_start {
        Option::Some(qi) => {
            self.query_start
                = Option::Some(qi - removed32 + added32);
        }
        Option::None => {}
    }
    match self.fragment_start {
        Option::Some(fi) => {
            self.fragment_start
                = Option::Some(fi - removed32 + added32);
        }
        Option::None => {}
    }
    proof {
        let fe = self.serialization.view();
        let shift = us - ue - 1;
        let pre2 = ov.subrange(0, us);
        assert(fe == pre2 + after@.subrange(1, after@.len() as int));
        vstd::seq::lemma_seq_add_len(pre2,
            after@.subrange(1, after@.len() as int));
        assert((fe.len() as int) == us
            + (ov.len() as int) - ue - 1);
        assert((fe.len() as int) <= (ov.len() as int));
        assert((fe.len() as int) <= 0xFFFF_FFFF);
        // the position channel: the kept tail byte at us + j is the
        // entry byte at ue + 1 + j
        assert forall|j: int| #![trigger fe.index(j)]
            us <= j && j < fe.len() as int
            implies fe.index(j) == ov.index(ue + 1 + j - us) by {
            if us <= j && j < fe.len() as int {
                vstd::seq::lemma_seq_add_index2(pre2,
                    after@.subrange(1, after@.len() as int), j);
                vstd::seq::lemma_seq_subrange_index(ov, ue + 1,
                    ov.len() as int, j - us);
            }
        }
        // the matcher face on the written record: the byte at the
        // fresh end is the first host byte (':'/'@'-free by the
        // host-first-byte dogma), so the wildcard arm fires and
        // rides the userinfo-start pin
        if us < fe.len() as int {
            assert(fe.index(us) == ov.index(ue + 1));
            assert(fe.index(us) == ov.index(hs));
            assert(fe.index(us) != 0x3Au8);
            assert(fe.index(us) != 0x40u8);
        }
        // the shifted host and port regions re-land as the entry's
        // own content at the moved offsets
        let ohe = old(self).host_end as int;
        let ops = old(self).path_start as int;
        assert((self.host_start as int) == hs + shift);
        assert((self.host_end as int) == ohe + shift);
        assert((self.path_start as int) == ops + shift);
        Self::subrange_shift_eq(fe, ov, us, ue + 1, hs, ohe);
        assert(fe.subrange(hs + shift, ohe + shift)
            == ov.subrange(hs, ohe));
        if ops > ohe {
            // the port region: same digit content, so the dec_val
            // conjunct of the invariant carries across
            Self::subrange_shift_eq(fe, ov, us, ue + 1, ohe + 1,
                ops);
            assert(fe.subrange(ohe + shift + 1, ops + shift)
                == ov.subrange(ohe + 1, ops));
            assert(dec_val(fe.subrange(ohe + shift + 1,
                ops + shift))
                == dec_val(ov.subrange(ohe + 1, ops)));
        }
        // the query/fragment slots keep their pins at the moved
        // offsets (the channel's own bytes)
        if self.query_start.is_some() {
            let qi = self.query_start.unwrap() as int;
            assert(fe.index(qi) == ov.index(ue + 1 + qi - us));
            assert(fe.index(qi) == 0x3Fu8);
        }
        if self.fragment_start.is_some() {
            let fi = self.fragment_start.unwrap() as int;
            assert(fe.index(fi) == ov.index(ue + 1 + fi - us));
            assert(fe.index(fi) == 0x23u8);
        }
        assert(url_invariant(self));
    }
}

/// The '@'-insert geometry of set_username (lib.rs:2310-2330's
/// (false,_) arm, split out so each whole-fn check stays inside the
/// solver budget): truncate at the userinfo start, write the
/// USERINFO-encoded username, then a fresh '@' and the whole
/// checkout -- the terminator the checkout lacked (the empty
/// userinfo region face, where the matcher's wildcard arm said the
/// region was empty); every boundary at or above the old
/// username_end moves by (fresh region length + 1 - old
/// username_end).
/* [verifier note: rlimit = the whole-fn check rides past the default
   budget: the invariant close over the '@'-insert rebuild (the
   fresh matcher arm at the fresh username_end plus the shifted
   port-region dec_val conjunct over the appended checkout) keeps
   the final query above the default budget; the default limit fails
   deterministically (probed: default fails in the parse-machine
   ambient, 90 closes all three harness ambients); only the resource
   ceiling is raised, no obligation is relaxed, the fn's own content
   is untouched] */
#[verifier::rlimit(90)]
pub exec fn set_username_insert_write(&mut self, username: &[u8],
    after: &[u8])
    requires
        url_invariant(self),
        has_authority_view(self),
        parser::machine_domain(self.serialization.view()),
        parser::machine_domain(username@),
        parser::machine_domain(after@),
        (username@.len() as int) >= 1,
        (after@ == self.serialization.view().subrange(
            self.username_end as int,
            self.serialization.view().len() as int)),
        (after@.len() as int) >= 1,
        (after@[0] != 0x3Au8 && after@[0] != 0x40u8),
        // the userinfo-interior dogma of the parser-reachable
        // records: with no terminator byte at username_end, the
        // userinfo region is empty, so the host starts exactly at
        // username_end (a hand-built record could carry interior
        // bytes between scheme_end + 3 and the host region; no
        // parser-built record does)
        ((self.host_start as int) == (self.username_end as int)),
        ((self.serialization.view().len() as int)
            + 3 * (username@.len() as int) + 8) <= 0xFFFF_FFFF,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        ((final(self).serialization.view().len() as int)
            <= 0xFFFF_FFFF),
        ({
            let ov = old(self).serialization.view();
            let ue = old(self).username_end as int;
            let us = (old(self).scheme_end as int) + 3;
            let enc = parser::enc_seq(username@,
                parser::EncodeSet::Userinfo);
            let nue = us + (enc.len() as int);
            &&& (final(self).serialization.view()
                == ov.subrange(0, us) + enc + seq![0x40u8] + after@)
            &&& (final(self).username_end as int) == nue
            &&& (final(self).host_start as int)
                == (old(self).host_start as int) + nue + 1 - ue
            &&& (final(self).host_end as int)
                == (old(self).host_end as int) + nue + 1 - ue
            &&& (final(self).path_start as int)
                == (old(self).path_start as int) + nue + 1 - ue
            &&& (old(self).query_start.is_none()
                ==> final(self).query_start.is_none())
            &&& (old(self).query_start.is_some()
                ==> final(self).query_start
                    == Option::Some(((old(self).query_start.unwrap()
                        as int) + nue + 1 - ue) as u32))
            &&& (old(self).fragment_start.is_none()
                ==> final(self).fragment_start.is_none())
            &&& (old(self).fragment_start.is_some()
                ==> final(self).fragment_start
                    == Option::Some(((old(self).fragment_start.unwrap()
                        as int) + nue + 1 - ue) as u32))
            &&& final(self).host == old(self).host
            &&& final(self).port == old(self).port
        }),
{
    let ghost ov = self.serialization.view();
    let se32 = self.scheme_end;
    let ue32 = self.username_end;
    let hs32 = self.host_start;
    let ghost ue = ue32 as int;
    let ghost hs = hs32 as int;
    let ghost us = se32 as int + 3;
    let us_u32 = se32 + 3;
    proof {
        assert((us_u32 as int) == us);
        assert((us_u32 as int) <= ov.len() as int);
        // the checkout head is the entry byte at username_end; no
        // terminator, so the invariant's wildcard face fires (the
        // userinfo region is empty) and the interior dogma pins the
        // host start onto it
        assert(after@[0] == ov.index(ue)) by {
            vstd::seq::lemma_seq_subrange_index(ov, ue,
                ov.len() as int, 0);
        }
        assert(ov.index(ue) != 0x3Au8);
        assert(ov.index(ue) != 0x40u8);
        assert(ue == us);
        assert(hs == ue);
    }
    // lib.rs:2310: truncate at the userinfo start
    self.serialization.truncate(us_u32 as usize);
    proof {
        assert(self.serialization.view() == ov.subrange(0, us));
        parser::machine_domain_subrange(ov, 0, us);
        assert(parser::machine_domain(self.serialization.view()));
    }
    // lib.rs:2311-2312: the USERINFO-encoded username
    parser::extend_percent_encode_at(&mut self.serialization,
        username, 0, username.len(), parser::EncodeSet::Userinfo);
    proof {
        let enc = parser::enc_seq(username@,
            parser::EncodeSet::Userinfo);
        assert(username@.subrange(0, username@.len() as int) =~= username@);
        assert(self.serialization.view()
            == ov.subrange(0, us) + enc);
        parser::enc_seq_machine(username@,
            parser::EncodeSet::Userinfo);
        parser::enc_seq_len_bound(username@,
            parser::EncodeSet::Userinfo);
    }
    // the fresh username_end (lib.rs:2315): the length after the
    // encode, before the '@' slot (the '@' lands ON the fresh end)
    let nue32 = url_len32(&self.serialization);
    proof {
        let enc = parser::enc_seq(username@,
            parser::EncodeSet::Userinfo);
        assert((nue32 as int) == us + (enc.len() as int));
    }
    self.username_end = nue32;
    // lib.rs:2328-2329: the fresh '@' slot, then the checkout
    self.serialization.push(0x40u8);
    proof {
        let enc = parser::enc_seq(username@,
            parser::EncodeSet::Userinfo);
        assert(self.serialization.view()
            == ov.subrange(0, us) + enc + seq![0x40u8]);
        parser::machine_domain_byte(0x40u8);
        parser::machine_domain_add(ov.subrange(0, us) + enc,
            seq![0x40u8]);
        vstd::seq::lemma_seq_add_len(ov.subrange(0, us), enc);
        vstd::seq::lemma_seq_add_len(
            ov.subrange(0, us) + enc, seq![0x40u8]);
    }
    parser::vec_append_bytes(&mut self.serialization, after);
    proof {
        let enc = parser::enc_seq(username@,
            parser::EncodeSet::Userinfo);
        let pre3 = ov.subrange(0, us) + enc + seq![0x40u8];
        let fe = self.serialization.view();
        let nue = nue32 as int;
        assert(fe == pre3 + after@);
        parser::machine_domain_add(pre3, after@);
        assert(parser::machine_domain(fe));
        vstd::seq::lemma_seq_add_len(pre3, after@);
        assert((fe.len() as int) == nue + 1
            + (ov.len() as int) - ue);
        assert((fe.len() as int) <= (ov.len() as int)
            + 3 * (username@.len() as int) + 8);
        assert((fe.len() as int) <= 0xFFFF_FFFF);
        // the position channel: the checkout byte at nue + 1 + j is
        // the entry byte at ue + j (the '@' slot sits at nue)
        assert forall|j: int| #![trigger fe.index(j)]
            nue + 1 <= j && j < fe.len() as int
            implies fe.index(j) == ov.index(ue + j - nue - 1) by {
            if nue + 1 <= j && j < fe.len() as int {
                vstd::seq::lemma_seq_add_index2(pre3, after@, j);
                vstd::seq::lemma_seq_subrange_index(ov, ue,
                    ov.len() as int, j - nue - 1);
            }
        }
        // the matcher face on the written record: the fresh '@'
        // sits at the fresh username_end, and the fresh host start
        // re-lands exactly one above it (the entry host start was
        // the entry username_end by the interior dogma)
        assert(fe.index(nue) == 0x40u8) by {
            vstd::seq::lemma_seq_add_index1(pre3, after@, nue);
        }
    }
    // lib.rs:2314/2316/2328/2334-2346: added is the fresh end plus
    // the '@' slot; the boundary move (two-step, upstream's own
    // -= removed_bytes += added_bytes)
    let removed32 = ue32;
    let added32 = nue32 + 1;
    proof {
        assert((self.host_start as int) >= ue);
        assert((self.host_end as int) >= (self.host_start as int));
        assert((self.path_start as int) >= (self.host_end as int));
        if self.query_start.is_some() {
            assert((self.query_start.unwrap() as int)
                >= (self.path_start as int));
        }
        if self.fragment_start.is_some() {
            assert((self.fragment_start.unwrap() as int)
                >= (self.path_start as int));
        }
        assert((self.host_start as int) - ue + (nue32 as int) + 1
            <= 0xFFFF_FFFF);
        assert((self.host_end as int) - ue + (nue32 as int) + 1
            <= 0xFFFF_FFFF);
        assert((self.path_start as int) - ue + (nue32 as int) + 1
            <= 0xFFFF_FFFF);
        if self.query_start.is_some() {
            assert((self.query_start.unwrap() as int) - ue
                + (nue32 as int) + 1 <= 0xFFFF_FFFF);
        }
        if self.fragment_start.is_some() {
            assert((self.fragment_start.unwrap() as int) - ue
                + (nue32 as int) + 1 <= 0xFFFF_FFFF);
        }
    }
    self.host_start = self.host_start - removed32 + added32;
    self.host_end = self.host_end - removed32 + added32;
    self.path_start = self.path_start - removed32 + added32;
    match self.query_start {
        Option::Some(qi) => {
            self.query_start
                = Option::Some(qi - removed32 + added32);
        }
        Option::None => {}
    }
    match self.fragment_start {
        Option::Some(fi) => {
            self.fragment_start
                = Option::Some(fi - removed32 + added32);
        }
        Option::None => {}
    }
    proof {
        let enc = parser::enc_seq(username@,
            parser::EncodeSet::Userinfo);
        let pre3 = ov.subrange(0, us) + enc + seq![0x40u8];
        let fe = self.serialization.view();
        let nue = nue32 as int;
        // the shifted host and port regions re-land as the entry's
        // own content at the moved offsets
        let ohe = old(self).host_end as int;
        let ops = old(self).path_start as int;
        assert((self.host_start as int) == hs + nue + 1 - ue);
        assert((self.host_end as int) == ohe + nue + 1 - ue);
        assert((self.path_start as int) == ops + nue + 1 - ue);
        Self::subrange_shift_eq(fe, ov, nue + 1, ue, hs, ohe);
        assert(fe.subrange(hs + nue + 1 - ue, ohe + nue + 1 - ue)
            == ov.subrange(hs, ohe));
        if ops > ohe {
            // the port region: same digit content, so the dec_val
            // conjunct of the invariant carries across
            Self::subrange_shift_eq(fe, ov, nue + 1, ue, ohe + 1,
                ops);
            assert(fe.subrange(ohe + nue + 2 - ue,
                ops + nue + 1 - ue) == ov.subrange(ohe + 1, ops));
            assert(dec_val(fe.subrange(ohe + nue + 2 - ue,
                ops + nue + 1 - ue))
                == dec_val(ov.subrange(ohe + 1, ops)));
        }
        // the query/fragment slots keep their pins at the moved
        // offsets (the channel's own bytes)
        if self.query_start.is_some() {
            let qi = self.query_start.unwrap() as int;
            assert(fe.index(qi) == ov.index(ue + qi - nue - 1));
            assert(fe.index(qi) == 0x3Fu8);
        }
        if self.fragment_start.is_some() {
            let fi = self.fragment_start.unwrap() as int;
            assert(fe.index(fi) == ov.index(ue + fi - nue - 1));
            assert(fe.index(fi) == 0x23u8);
        }
        assert(url_invariant(self));
    }
}

/// Origin Rust (lib.rs:2299-2348): pub fn set_username(&mut self,
///   username: &str) -> Result<(), ()> -- the entry gate of
/// lib.rs:2301 (the same three disjuncts as set_password: no host /
/// the empty-Domain face, dead under the invariant / the file
/// scheme), the equal-value face of lib.rs:2306-2308 (the current
/// username bytes equal the argument: Ok with the record untouched),
/// then the three write geometries (push-through / '@'-drop /
/// '@'-insert) dispatched on the empty face of the argument and the
/// terminator byte at username_end. CONE: the entry record is a
/// base_url_face record of the machine byte domain, plus the
/// userinfo-interior dogma (with no terminator at username_end the
/// host starts exactly at username_end -- the parser-reachable
/// shape; the '@'-insert face's matcher arm needs it).
pub exec fn set_username(&mut self,
    username: &[u8]) -> (r: Result<(), ()>)
    requires
        parser::base_url_face(self),
        parser::machine_domain(username@),
        ((self.serialization.view().len() as int)
            + 3 * (username@.len() as int) + 8) <= 0xFFFF_FFFF,
        // the userinfo-interior dogma (see the insert face above)
        ((self.host_start as int) == (self.username_end as int)
            || ((self.username_end as int)
                < (self.serialization.view().len() as int)
                && (self.serialization.view().index(
                        self.username_end as int) == 0x3Au8
                    || self.serialization.view().index(
                        self.username_end as int) == 0x40u8))),
        // the host-first-byte dogma (see the drop face above)
        (((self.host_start as int)
            == (self.serialization.view().len() as int))
            || ((self.serialization.view().index(
                    self.host_start as int) != 0x3Au8)
                && (self.serialization.view().index(
                    self.host_start as int) != 0x40u8))),
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        (r.is_err() ==> ({
            // do-nothing face: every component of the entry record
            // survives untouched
            &&& (final(self).serialization.view()
                == old(self).serialization.view())
            &&& (final(self).scheme_end as int)
                == (old(self).scheme_end as int)
            &&& (final(self).username_end as int)
                == (old(self).username_end as int)
            &&& (final(self).host_start as int)
                == (old(self).host_start as int)
            &&& (final(self).host_end as int)
                == (old(self).host_end as int)
            &&& final(self).host == old(self).host
            &&& final(self).port == old(self).port
            &&& (final(self).path_start as int)
                == (old(self).path_start as int)
            &&& final(self).query_start == old(self).query_start
            &&& final(self).fragment_start
                == old(self).fragment_start
        })),
        (r.is_ok() ==> ({
            let ov = old(self).serialization.view();
            let ue = old(self).username_end as int;
            let us = (old(self).scheme_end as int) + 3;
            let enc = parser::enc_seq(username@,
                parser::EncodeSet::Userinfo);
            let nue = us + (enc.len() as int);
            &&& (ue < (ov.len() as int))
            &&& (ov.subrange(us, ue) == username@ ==> ({
                // the equal-value face (lib.rs:2306-2308): untouched
                &&& (final(self).serialization.view()
                    == old(self).serialization.view())
                &&& (final(self).scheme_end as int)
                    == (old(self).scheme_end as int)
                &&& (final(self).username_end as int)
                    == (old(self).username_end as int)
                &&& (final(self).host_start as int)
                    == (old(self).host_start as int)
                &&& (final(self).host_end as int)
                    == (old(self).host_end as int)
                &&& final(self).host == old(self).host
                &&& final(self).port == old(self).port
                &&& (final(self).path_start as int)
                    == (old(self).path_start as int)
                &&& final(self).query_start == old(self).query_start
                &&& final(self).fragment_start
                    == old(self).fragment_start
            }))
            &&& (ov.subrange(us, ue) != username@ ==> ({
                let b0 = ov.index(ue);
                let shift = nue - ue;
                let shifti = nue + 1 - ue;
                let shiftd = us - ue - 1;
                &&& ((username@.len() as int) == 0 && b0 == 0x40u8
                    ==> ({
                    // the '@'-drop geometry (lib.rs:2320-2323)
                    &&& (final(self).serialization.view()
                        == ov.subrange(0, us)
                            + ov.subrange(ue + 1,
                                ov.len() as int))
                    &&& (final(self).username_end as int) == us
                    &&& (final(self).host_start as int)
                        == (old(self).host_start as int) + shiftd
                    &&& (final(self).host_end as int)
                        == (old(self).host_end as int) + shiftd
                    &&& (final(self).path_start as int)
                        == (old(self).path_start as int) + shiftd
                    &&& (old(self).query_start.is_none()
                        ==> final(self).query_start.is_none())
                    &&& (old(self).query_start.is_some()
                        ==> final(self).query_start
                            == Option::Some(
                                ((old(self).query_start.unwrap()
                                    as int) + shiftd) as u32))
                    &&& (old(self).fragment_start.is_none()
                        ==> final(self).fragment_start.is_none())
                    &&& (old(self).fragment_start.is_some()
                        ==> final(self).fragment_start
                            == Option::Some(
                                ((old(self).fragment_start.unwrap()
                                    as int) + shiftd) as u32))
                    &&& final(self).host == old(self).host
                    &&& final(self).port == old(self).port
                }))
                &&& ((b0 == 0x3Au8 || b0 == 0x40u8
                    || (username@.len() as int) == 0)
                    && !(b0 == 0x40u8
                        && (username@.len() as int) == 0) ==> ({
                    // the push-through geometry (lib.rs:2324-2326)
                    &&& (final(self).serialization.view()
                        == ov.subrange(0, us) + enc + ov.subrange(
                            ue, ov.len() as int))
                    &&& (final(self).username_end as int) == nue
                    &&& (final(self).host_start as int)
                        == (old(self).host_start as int) + shift
                    &&& (final(self).host_end as int)
                        == (old(self).host_end as int) + shift
                    &&& (final(self).path_start as int)
                        == (old(self).path_start as int) + shift
                    &&& (old(self).query_start.is_none()
                        ==> final(self).query_start.is_none())
                    &&& (old(self).query_start.is_some()
                        ==> final(self).query_start
                            == Option::Some(
                                ((old(self).query_start.unwrap()
                                    as int) + shift) as u32))
                    &&& (old(self).fragment_start.is_none()
                        ==> final(self).fragment_start.is_none())
                    &&& (old(self).fragment_start.is_some()
                        ==> final(self).fragment_start
                            == Option::Some(
                                ((old(self).fragment_start.unwrap()
                                    as int) + shift) as u32))
                    &&& final(self).host == old(self).host
                    &&& final(self).port == old(self).port
                }))
                &&& ((b0 != 0x3Au8 && b0 != 0x40u8
                    && (username@.len() as int) > 0) ==> ({
                    // the '@'-insert geometry (lib.rs:2327-2331)
                    &&& (final(self).serialization.view()
                        == ov.subrange(0, us) + enc + seq![0x40u8]
                            + ov.subrange(ue, ov.len() as int))
                    &&& (final(self).username_end as int) == nue
                    &&& (final(self).host_start as int)
                        == (old(self).host_start as int) + shifti
                    &&& (final(self).host_end as int)
                        == (old(self).host_end as int) + shifti
                    &&& (final(self).path_start as int)
                        == (old(self).path_start as int) + shifti
                    &&& (old(self).query_start.is_none()
                        ==> final(self).query_start.is_none())
                    &&& (old(self).query_start.is_some()
                        ==> final(self).query_start
                            == Option::Some(
                                ((old(self).query_start.unwrap()
                                    as int) + shifti) as u32))
                    &&& (old(self).fragment_start.is_none()
                        ==> final(self).fragment_start.is_none())
                    &&& (old(self).fragment_start.is_some()
                        ==> final(self).fragment_start
                            == Option::Some(
                                ((old(self).fragment_start.unwrap()
                                    as int) + shifti) as u32))
                    &&& final(self).host == old(self).host
                    &&& final(self).port == old(self).port
                }))
            }))
        })),
{
    let ghost ov = self.serialization.view();
    let ghost uv = username@;
    // the entry gate (lib.rs:2301)
    let hh = self.has_host();
    let dom_empty = match self.host {
        HostInternal::Domain => self.host_start == self.host_end,
        _ => false,
    };
    let sch = self.scheme();
    let is_file = sch.len() == 4usize
        && sch[0usize] == 0x66u8
        && sch[1usize] == 0x69u8
        && sch[2usize] == 0x6Cu8
        && sch[3usize] == 0x65u8;
    if !hh || dom_empty || is_file {
        return Result::Err(());
    }
    // the post-gate geometry: has_host forces the authority branch,
    // so username_end sits strictly below the serialization end
    proof {
        assert(has_authority_view(self));
        assert((self.username_end as int)
            <= (self.host_start as int));
        assert((self.host_start as int) < (self.host_end as int));
        assert((self.host_end as int)
            <= (self.serialization.view().len() as int));
        assert((self.username_end as int)
            < (self.serialization.view().len() as int));
        // the debug assert of lib.rs:2305 is the invariant's own
        // authority pin (the ':' at scheme_end plus the "//")
        assert((self.host_start as int) == (self.username_end as int)
            || self.serialization.view().index(
                    self.username_end as int) == 0x3Au8
            || self.serialization.view().index(
                    self.username_end as int) == 0x40u8);
    }
    let us32 = self.scheme_end + 3;
    // the equal-value face (lib.rs:2306-2308): the byte comparison
    // of the current username region against the argument
    let cur = bytes_slice(&self.serialization, us32,
        self.username_end);
    proof {
        assert(cur.view() == self.serialization.view().subrange(
            us32 as int, self.username_end as int));
        assert(cur.view() == ov.subrange(us32 as int,
            self.username_end as int));
    }
    let eq = Self::bytes_eq(&cur, username);
    proof {
        // the helper's contract, tied to the entry region
        assert(username@ == uv);
        assert(eq == (cur@ == username@));
        if eq {
            assert(ov.subrange(us32 as int,
                self.username_end as int) == username@);
        } else {
            assert(ov.subrange(us32 as int,
                self.username_end as int) != username@);
        }
    }
    if eq {
        return Result::Ok(());
    }
    // the after-checkout (lib.rs:2309), hoisted above the writes
    let after = bytes_slice(&self.serialization,
        self.username_end, url_len32(&self.serialization));
    proof {
        assert(after.view() == self.serialization.view().subrange(
            self.username_end as int,
            self.serialization.view().len() as int));
        parser::machine_domain_subrange(
            self.serialization.view(),
            self.username_end as int,
            self.serialization.view().len() as int);
        assert(parser::machine_domain(after.view()));
        assert((after.view().len() as int) >= 1);
    }
    let b0 = after[0usize];
    proof {
        assert(b0 == after.view().index(0));
        assert(b0 == self.serialization.view().index(
            self.username_end as int));
    }
    if username.len() == 0usize {
        if b0 == 0x40u8 {
            // lib.rs:2320-2323: the '@'-drop geometry
            self.set_username_dropat_write(&after);
        } else {
            // lib.rs:2324-2326's (true,_) face: push-through
            self.set_username_push_write(username, &after);
        }
    } else {
        if b0 == 0x40u8 || b0 == 0x3Au8 {
            // lib.rs:2324-2326's (false,'@') / (_,':') faces
            self.set_username_push_write(username, &after);
        } else {
            // lib.rs:2327-2331: the '@'-insert geometry
            self.set_username_insert_write(username, &after);
        }
    }
    Result::Ok(())
}


/// The payload write of the set_port write arm (lib.rs:1917-1922,
/// split out so each whole-fn check stays inside the solver budget):
/// the record keeps its head up to host_end, gains a fresh ':' plus
/// ASCII-decimal region (the fast_u16_to_str face), and re-appends the
/// path tail above the new path anchor; the query/fragment offsets
/// shift by the path_start move. The strict-host cone (the wrapper's
/// has_host gate on set_port) keeps the userinfo matcher of the
/// written record intact (the ':' lands strictly above every
/// userinfo pin). The caller's snapshot pins the entry record.
/* [verus note: rlimit = the whole-fn check rides the frontier of the
   default budget under the coverage-props harness ambient (the
   set_query write-face entry shifted the module's air context when it
   landed): the identical content closes at the default limit in the
   parse-machine and read-API ambients and failed deterministically at
   default in the coverage-props ambient on three consecutive sweeps,
   closing first at 12 -- the ambient-flip phenomenon of the
   parse_host_and_port/rel_slash/rel_merge ledger; only the resource
   ceiling is raised, no obligation is relaxed, the fn's own content
   is untouched] */
#[verifier::rlimit(20)]
pub exec fn set_port_payload_write(&mut self, snapshot: &Url,
    newv: u16)
    requires
        url_invariant(snapshot),
        parser::machine_domain(snapshot.serialization.view()),
        (snapshot.host_start as int) < (snapshot.host_end as int),
        (snapshot.serialization.view().len() as int) + 12
            <= 0xFFFF_FFFF,
        self.serialization.view()
            == snapshot.serialization.view(),
        (self.scheme_end as int) == (snapshot.scheme_end as int),
        (self.username_end as int)
            == (snapshot.username_end as int),
        (self.host_start as int) == (snapshot.host_start as int),
        (self.host_end as int) == (snapshot.host_end as int),
        self.host == snapshot.host,
        self.port == snapshot.port,
        (self.path_start as int) == (snapshot.path_start as int),
        self.query_start == snapshot.query_start,
        self.fragment_start == snapshot.fragment_start,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(
            final(self).serialization.view()),
        final(self).port == Option::Some(newv),
        (final(self).scheme_end as int)
            == (snapshot.scheme_end as int),
        (final(self).username_end as int)
            == (snapshot.username_end as int),
        (final(self).host_start as int)
            == (snapshot.host_start as int),
        (final(self).host_end as int)
            == (snapshot.host_end as int),
        final(self).host == snapshot.host,
        ({
            let o = snapshot.serialization.view();
            let nps = (snapshot.host_end as int) + 1
                + parser::dec_ascii_u32(newv as int).len() as int;
            &&& (final(self).serialization.view()
                == o.subrange(0, snapshot.host_end as int)
                    + seq![0x3Au8]
                    + parser::dec_ascii_u32(newv as int)
                    + o.subrange(snapshot.path_start as int,
                        o.len() as int))
            &&& (final(self).path_start as int) == nps
            &&& (final(self).query_start
                == (match snapshot.query_start {
                        Option::Some(i) => Option::Some(
                            (((i as int)
                                - (snapshot.path_start as int)
                                + nps) as u32)),
                        Option::None => Option::None,
                    }))
            &&& (final(self).fragment_start
                == (match snapshot.fragment_start {
                        Option::Some(i) => Option::Some(
                            (((i as int)
                                - (snapshot.path_start as int)
                                + nps) as u32)),
                        Option::None => Option::None,
                    }))
        }),
{
    let ghost o = self.serialization.view();
    let he = snapshot.host_end;
    let ps = snapshot.path_start;
    let n0 = url_len32(&self.serialization);
    let tail = bytes_slice(&self.serialization, ps, n0);
    proof {
        assert(tail.view()
            == o.subrange(ps as int, n0 as int));
        assert(parser::machine_domain(tail.view()));
        assert((snapshot.username_end as int) < (he as int));
        assert(has_authority_view(snapshot));
    }
    self.serialization.truncate(he as usize);
    let ghost head = self.serialization.view();
    proof {
        assert(head == o.subrange(0, he as int));
        parser::machine_domain_subrange(o, 0, he as int);
        assert(parser::machine_domain(head));
    }
    self.serialization.push(0x3Au8);
    let ghost headc = self.serialization.view();
    proof {
        assert(headc == head.push(0x3Au8));
        assert(headc == head + seq![0x3Au8]);
        assert(parser::machine_domain_byte(0x3Au8));
        parser::machine_domain_add(head, seq![0x3Au8]);
        assert(parser::machine_domain(headc));
        assert((headc.len() as int) <= (o.len() as int) + 1
            <= 0xFFFF_FFFF - 11);
    }
    parser::append_dec_port(&mut self.serialization, newv);
    let new_ps = url_len32(&self.serialization);
    proof {
        // the written region: head + ':' + the ASCII decimal, on
        // which the port-region bridge digest applies
        let dec = parser::dec_ascii_u32(newv as int);
        let mid = self.serialization.view();
        assert(mid == headc + dec);
        assert(mid == head + seq![0x3Au8] + dec);
        assert(0 <= newv as int && newv as int <= 65535);
        parser::dec_ascii_digits(newv as int);
        assert forall|j: int| 0 <= j && j < dec.len()
            implies parser::machine_domain_byte(dec.index(j)) by {
            assert(is_dec_digit(dec.index(j)));
        }
        assert(parser::machine_domain(dec));
        parser::machine_domain_add(headc, dec);
        assert(parser::machine_domain(mid));
        parser::host_port_region_face(mid, head, newv as int);
        assert((new_ps as int) == (mid.len() as int));
        assert((new_ps as int)
            == (he as int) + 1 + (dec.len() as int));
        // the re-append fits the u32 offset domain
        assert((n0 as int) + 6 <= 0xFFFF_FFFF);
        assert((mid.len() as int) + (tail.view().len() as int)
            <= 0xFFFF_FFFF);
    }
    self.path_start = new_ps;
    match self.query_start {
        Option::Some(i) => {
            proof {
                assert((i as int) >= (ps as int));
                assert(((i - ps) as int)
                    <= (n0 as int) - (ps as int));
                assert(((i - ps) + new_ps) as int
                    <= (n0 as int) + 6
                    <= 0xFFFF_FFFF);
            }
            self.query_start = Option::Some(i - ps + new_ps);
        }
        Option::None => {}
    }
    match self.fragment_start {
        Option::Some(i) => {
            proof {
                assert((i as int) >= (ps as int));
                assert(((i - ps) + new_ps) as int
                    <= (n0 as int) + 6
                    <= 0xFFFF_FFFF);
            }
            self.fragment_start =
                Option::Some(i - ps + new_ps);
        }
        Option::None => {}
    }
    parser::vec_append_bytes(&mut self.serialization, &tail);
    self.port = Option::Some(newv);
    proof {
        let f = self.serialization.view();
        let mid0 = head + seq![0x3Au8]
            + parser::dec_ascii_u32(newv as int);
        let mid = mid0;
        assert(parser::machine_domain(mid));
        parser::machine_domain_add(mid, tail.view());
        assert(parser::machine_domain(f));
        let ose = snapshot.scheme_end as int;
        let oue = snapshot.username_end as int;
        let ohs = snapshot.host_start as int;
        let nps = new_ps as int;
        let mid = head + seq![0x3Au8]
            + parser::dec_ascii_u32(newv as int);
        // the record: head preserved, the fresh port region, the
        // re-appended tail above the new path anchor
        assert(f.len() as int <= 0xFFFF_FFFF);
        assert(has_authority_view(self));
        assert(f.index(he as int) == 0x3Au8);
        assert(f.index(ose + 1) == o.index(ose + 1));
        assert(f.index(ose + 2) == o.index(ose + 2));
        assert(f.index(oue) == o.index(oue));
        assert(f.index(ohs - 1) == o.index(ohs - 1));
        // the mid bytes are unshifted below the tail
        assert forall|j: int| 0 <= j && j < nps
            implies f.index(j) == mid.index(j) by {
            vstd::seq::lemma_seq_add_index1(mid,
                tail.view(), j);
        }
        // the digits region: the pointwise preservation makes the
        // subrange the bridge digest already measured
        assert(f.subrange(he as int + 1, nps)
            == mid.subrange(he as int + 1, nps)) by {
            assert forall|j: int|
                #![trigger f.subrange(he as int + 1, nps).index(j)]
                0 <= j && j < nps - (he as int + 1)
                implies f.subrange(he as int + 1, nps).index(j)
                    == mid.subrange(he as int + 1, nps).index(j) by {
                vstd::seq::lemma_seq_subrange_index(f,
                    he as int + 1, nps, j);
                vstd::seq::lemma_seq_subrange_index(mid,
                    he as int + 1, nps, j);
                assert(f.index(he as int + 1 + j)
                    == mid.index(he as int + 1 + j));
            }
            vstd::seq::lemma_seq_ext_equal(
                f.subrange(he as int + 1, nps),
                mid.subrange(he as int + 1, nps));
        }
        assert forall|j: int| (he as int) + 1 <= j && j < nps
            implies is_dec_digit(f.index(j)) by {
            assert(f.index(j) == mid.index(j));
        }
        // the new path anchor byte is the old anchor byte
        if nps < (f.len() as int) {
            assert(f.index(nps) == o.index(ps as int));
        } else {
            assert(nps == (f.len() as int));
        }
        // the query/fragment slots: the tail carries the old bytes up
        if self.query_start.is_some() {
            let qi = self.query_start.unwrap() as int;
            assert((qi as int)
                == (snapshot.query_start.unwrap() as int)
                    - (ps as int) + nps);
            assert(f.index(qi) == o.index(
                (qi - nps + (ps as int)) as int));
            assert(f.index(qi) == 0x3Fu8);
        }
        if self.fragment_start.is_some() {
            let fi = self.fragment_start.unwrap() as int;
            assert((fi as int)
                == (snapshot.fragment_start.unwrap() as int)
                    - (ps as int) + nps);
            assert(f.index(fi) == o.index(
                (fi - nps + (ps as int)) as int));
            assert(f.index(fi) == 0x23u8);
        }
        assert(url_invariant(self));
    }
}

/// Origin Rust (lib.rs:1899-1924): fn set_port_internal(&mut self,
///   port: Option<u16>) -- the port-field write of the setter face:
/// the no-op pairs ((None, None) and the equal Some pair), the
/// removal arm (the std drain of the ":<digits>" region modeled by
/// the truncate+re-append drain probe vec_drain_middle, the
/// query/fragment offsets shifting down by the drained span), and
/// the write arm (truncate at host_end, write ':' plus the ASCII
/// decimal of the new port -- the fast_u16_to_str face -- then
/// re-append the path tail, the offsets shifting by the path_start
/// move). CONE: the strict host region (host_start < host_end) --
/// the wrapper's gate on set_port (has_host, not the empty Domain,
/// not the file scheme, lib.rs:1893-1899) filters exactly the
/// records where the region vanishes, and an empty host region
/// would break the userinfo matcher of the written record (the ':'
/// at host_end would land at the userinfo terminator). The debug
/// asserts of upstream (lib.rs:1904, 1917) ride the invariant's own
/// byte pins; the u32 offset arithmetic stays inside the budget.
pub exec fn set_port_internal(&mut self, port: Option<u16>)
    requires
        url_invariant(self),
        parser::machine_domain(self.serialization.view()),
        (self.host_start as int) < (self.host_end as int),
        (self.serialization.view().len() as int) + 12
            <= 0xFFFF_FFFF,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(
            final(self).serialization.view()),
        final(self).port == port,
        (final(self).scheme_end as int)
            == (old(self).scheme_end as int),
        (final(self).username_end as int)
            == (old(self).username_end as int),
        (final(self).host_start as int)
            == (old(self).host_start as int),
        (final(self).host_end as int)
            == (old(self).host_end as int),
        final(self).host == old(self).host,
{
    match (self.port, port) {
        (Option::None, Option::None) => {
            // the empty-region no-op (lib.rs:1901)
            self.port = port;
            proof {
                assert((self.path_start as int)
                    == (self.host_end as int));
                assert(url_invariant(self));
            }
        }
        (Option::Some(oldv), Option::None) => {
            // the removal arm (lib.rs:1904-1909): the drain of the
            // ':' + digits region, the offsets shift down by it
            let he = self.host_end;
            let ps = self.path_start;
            proof {
                assert((ps as int) > (he as int));
                assert((he as int) + 2 <= (ps as int));
                // every component pin the record reads sits below
                // the drained span's head
                assert((self.username_end as int) < (he as int));
            }
            vec_drain_middle(&mut self.serialization, he, ps);
            let offset = ps - he;
            self.path_start = he;
            match self.query_start {
                Option::Some(i) => {
                    proof {
                        assert((i as int) >= (ps as int));
                        assert((i as int) - (offset as int)
                            >= (he as int));
                    }
                    self.query_start = Option::Some(i - offset);
                }
                Option::None => {}
            }
            match self.fragment_start {
                Option::Some(i) => {
                    proof {
                        assert((i as int) >= (ps as int));
                        assert((i as int) - (offset as int)
                            >= (he as int));
                    }
                    self.fragment_start = Option::Some(i - offset);
                }
                Option::None => {}
            }
            self.port = port;
            proof {
                let o = old(self).serialization.view();
                let f = self.serialization.view();
                let ose = old(self).scheme_end as int;
                let shift = (ps as int) - (he as int);
                // the drained record: prefix kept, tail shifted down
                assert(self.port.is_none());
                assert((self.path_start as int) == (he as int));
                assert(has_authority_view(self));
                // the userinfo and host bytes survive below the drain
                assert(f.index(ose + 1) == o.index(ose + 1));
                assert(f.index(ose + 2) == o.index(ose + 2));
                assert(f.index((old(self).username_end) as int)
                    == o.index((old(self).username_end) as int));
                assert(f.index((old(self).host_start) as int - 1)
                    == o.index((old(self).host_start) as int - 1));
                // the new path head is the old byte at path_start
                if (ps as int) < (o.len() as int) {
                    assert(f.index(he as int) == o.index(ps as int));
                }
                if self.query_start.is_some() {
                    let qi = self.query_start.unwrap() as int;
                    assert(f.index(qi) == o.index(
                        (qi + shift) as int));
                    assert(f.index(qi) == 0x3Fu8);
                }
                if self.fragment_start.is_some() {
                    let fi = self.fragment_start.unwrap() as int;
                    assert(f.index(fi) == o.index(
                        (fi + shift) as int));
                    assert(f.index(fi) == 0x23u8);
                }
                assert(url_invariant(self));
            }
        }
        (Option::Some(oldv), Option::Some(newv))
            if oldv == newv => {
            // the equal-value no-op (lib.rs:1913)
            self.port = port;
            proof {
                assert(url_invariant(self));
            }
        }
        (_, Option::Some(newv)) => {
            // the write arm (lib.rs:1917-1922): delegated to the
            // payload write so each whole-fn check stays inside the
            // solver budget
            let snapshot = Url {
                serialization: parser::bytes_own(&self.serialization),
                scheme_end: self.scheme_end,
                username_end: self.username_end,
                host_start: self.host_start,
                host_end: self.host_end,
                host: self.host,
                port: self.port,
                path_start: self.path_start,
                query_start: self.query_start,
                fragment_start: self.fragment_start,
            };
            self.set_port_payload_write(&snapshot, newv);
        }
    }
}

/// Origin Rust (lib.rs:387-409): strip_trailing_spaces_from_opaque_path
///   -- the whatwg "potentially strip trailing spaces from an opaque
/// path" step of the None arm: only a cannot-be-a-base record with no
/// query and no fragment strips, and only the trailing 0x20 run of
/// the serialization goes (the ':' of the scheme stops the run, so no
/// component pin can sit inside the removed region; the cone's own
/// non-slash pin at scheme_end+1 keeps the plain-anarchist path
/// anchor). The upstream chars().rev() tail walk is the descending
/// byte probe here.
pub exec fn strip_trailing_spaces_from_opaque_path(&mut self)
    requires
        url_invariant(self),
        parser::machine_domain(self.serialization.view()),
        (self.serialization.view().len() as int)
            <= 0xFFFF_FFFF,
    ensures
        url_invariant(final(self)),
        parser::machine_domain(final(self).serialization.view()),
        (final(self).serialization.view().len() as int)
            <= (old(self).serialization.view().len() as int),
        (forall|j: int| 0 <= j
            && j < (final(self).serialization.view().len() as int)
            ==> final(self).serialization.view().index(j)
                == old(self).serialization.view().index(j)),
        (final(self).scheme_end as int)
            == (old(self).scheme_end as int),
        (final(self).username_end as int)
            == (old(self).username_end as int),
        (final(self).host_start as int)
            == (old(self).host_start as int),
        (final(self).host_end as int)
            == (old(self).host_end as int),
        final(self).host == old(self).host,
        final(self).port == old(self).port,
        (final(self).path_start as int)
            == (old(self).path_start as int),
        final(self).query_start == old(self).query_start,
        final(self).fragment_start == old(self).fragment_start,
        (exists|cut: int| 0 <= cut
            && cut <= (old(self).serialization.view().len() as int)
            && final(self).serialization.view()
                == old(self).serialization.view().subrange(0, cut)
            && (forall|j: int| cut <= j
                && j < (old(self).serialization.view().len() as int)
                ==> old(self).serialization.view().index(j)
                    == 0x20u8)),
{
    let ghost gv_old = self.serialization.view();
    // the guards (lib.rs:388-398): a record that is not a
    // cannot-be-a-base one, or one with a fragment or a query, never
    // strips. The exec homeland of the skip condition: an authority
    // record or a base-able path both read the two-byte window with
    // '/' right behind the scheme colon (the anarchist slash-led
    // cases are exactly what cannot_be_a_base denies).
    let n32 = url_len32(&self.serialization);
    let window = u32_add2_fits(self.scheme_end, n32);
    let mut guard_skip: bool = false;
    if window {
        let se_plus1 = (self.scheme_end + 1) as usize;
        guard_skip = self.serialization[se_plus1] == 0x2Fu8;
    }
    let empty_cut: () = proof {
        let n0 = (gv_old.len() as int);
        assert(0 <= n0 && n0 <= n0);
        assert(self.serialization.view() == gv_old);
        assert(forall|j: int| n0 <= j && j < n0
            ==> gv_old.index(j) == 0x20u8);
    };
    let _ = empty_cut;
    if guard_skip {
        proof {
            // the empty cut is the strip witness
            let n0 = (gv_old.len() as int);
            assert(0 <= n0 && n0 <= n0);
            assert(final(self).serialization.view()
                == old(self).serialization.view());
            assert(final(self).serialization.view()
                == old(self).serialization.view().subrange(0, n0));
            assert(forall|j: int| n0 <= j && j < n0
                ==> old(self).serialization.view().index(j)
                    == 0x20u8);
        }
        return;
    }
    if self.fragment_start.is_some() {
        proof {
            let n0 = (gv_old.len() as int);
            assert(0 <= n0 && n0 <= n0);
            assert(final(self).serialization.view()
                == old(self).serialization.view().subrange(0, n0));
            assert(forall|j: int| n0 <= j && j < n0
                ==> old(self).serialization.view().index(j)
                    == 0x20u8);
        }
        return;
    }
    if self.query_start.is_some() {
        proof {
            let n0 = (gv_old.len() as int);
            assert(0 <= n0 && n0 <= n0);
            assert(final(self).serialization.view()
                == old(self).serialization.view().subrange(0, n0));
            assert(forall|j: int| n0 <= j && j < n0
                ==> old(self).serialization.view().index(j)
                    == 0x20u8);
        }
        return;
    }
    // the descending space probe (lib.rs:400-405)
    let n = self.serialization.len();
    let mut cut: usize = n;
    proof {
        assert((self.scheme_end as int) + 1 <= (n as int));
        // the scheme ':' pin of the invariant, settled on the entry
        // view before the probe (the loop carries the view equality)
        assert(gv_old.index(self.scheme_end as int) == 0x3Au8);
        assert(self.fragment_start.is_none());
        assert(self.query_start.is_none());
    }
    while cut > 0 && self.serialization[cut - 1] == 0x20u8
        invariant
            self.scheme_end == old(self).scheme_end,
            (self.scheme_end as int) + 1 <= (cut as int),
            (cut as int) <= (n as int),
            (n as int)
                == (self.serialization.view().len() as int),
            forall|j: int| (cut as int) <= j && j < (n as int)
                ==> self.serialization.view().index(j) == 0x20u8,
            self.serialization.view() == gv_old,
            gv_old.index(self.scheme_end as int) == 0x3Au8,
            self.fragment_start.is_none(),
            self.query_start.is_none(),
        decreases cut,
    {
        proof {
            if ((cut as int) - 1) == (self.scheme_end as int) {
                // the ':' of the scheme halts the run below it
                let sn = self.serialization.view();
                assert(sn == gv_old);
                assert(sn.index((cut as int) - 1) == 0x3Au8);
                assert(sn.index((cut as int) - 1)
                    == self.serialization[cut - 1]);
                assert(false);
            }
        }
        cut = cut - 1;
    }
    if cut == n {
        // nothing to strip: the serialization ends on a non-space
        proof {
            let n0 = (gv_old.len() as int);
            assert(0 <= n0 && n0 <= n0);
            assert(self.serialization.view() == gv_old);
            assert(final(self).serialization.view()
                == old(self).serialization.view().subrange(0, n0));
            assert(forall|j: int| n0 <= j && j < n0
                ==> old(self).serialization.view().index(j)
                    == 0x20u8);
        }
        return;
    }
    // the truncate at the run start (lib.rs:407-409)
    self.serialization.truncate(cut);
    proof {
        let fin = self.serialization.view();
        let ov = gv_old;
        let se = self.scheme_end as int;
        // the pure-prefix fact, and the ':' pin that bounds the run
        assert(fin == ov.subrange(0, cut as int));
        assert((cut as int) >= se + 1);
        assert((cut as int) < (ov.len() as int));
        assert(ov.index(se) == 0x3Au8);
        assert(parser::machine_domain(fin));
        // the mutating branch read the whole guard window: the byte
        // behind the scheme colon is the non-slash the window denies
        assert(se + 2 <= (ov.len() as int));
        assert(ov.index(se + 1) != 0x2Fu8);
        assert(!has_authority_view(old(self)));
        // the invariant's opaque branch pins '/' at se+1 on this
        // window, which the mutating branch denies: the old record
        // sits on the plain path anchor, and so does the new one
        assert(!opaque_path_double_slash(old(self))) by {
            if opaque_path_double_slash(old(self)) {
                assert(old(self).serialization.view().index(
                    se + 1) == 0x2Fu8);
                assert(false);
            }
        }
        assert(self.path_start as int == se + 1);
        // the anarchist split: the head bytes below the cut are the
        // record's own, and the guard window pairs them
        assert(!has_authority_view(self)) by {
            if (cut as int) >= se + 3 {
                assert(fin.index(se + 1) == ov.index(se + 1));
                assert(fin.index(se + 2) == ov.index(se + 2));
                assert(!(ov.index(se + 1) == 0x2Fu8
                    && ov.index(se + 2) == 0x2Fu8));
            } else {
                // the record ends before the two-byte authority
                // guard window reads a second byte
                assert((fin.len() as int) <= se + 2);
            }
        }
        // the non-opacity: on either cut geometry the opaque guard
        // fails (the pair never holds two slashes on the window, or
        // the region ends before two head bytes exist)
        assert(!opaque_path_double_slash(self)) by {
            assert(path_end_view(self) == (cut as int));
            if (cut as int) >= se + 3 {
                assert(fin.index(se + 1) == ov.index(se + 1));
                assert(fin.index(se + 2) == ov.index(se + 2));
                assert((self.path_start as int) == se + 1);
                assert(!(ov.index(se + 1) == 0x2Fu8
                    && ov.index(se + 2) == 0x2Fu8));
            } else {
                assert((self.path_start as int) + 2 > (cut as int));
            }
        }
        // the strip witness: the removed suffix is the space run
        assert(forall|j: int| (cut as int) <= j
            && j < (ov.len() as int)
            ==> ov.index(j) == 0x20u8);
    }
}

}

}
