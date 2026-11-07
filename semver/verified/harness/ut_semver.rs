//! harness: the semver UT example-theorem library.
//!
//! Corresponding upstreams: tests/test_version.rs:14 test_parse (the
//! numeric-segment error-classification bank), the machine-level face of
//! parse.rs's dot/wildcard/op, the doc example chains of the lib.rs
//! Prerelease Total ordering ("alpha < alpha.1 < ... < 1.0.0" and
//! "alpha < alpha.85 < ... < beta"), the eval.rs Op semantics surface
//! (the doc equivalence instances of = and ^), and the cmp_precedence doc
//! examples.
//! Referencing organization: `#[path]` pulls in verified/src/lib.rs; its
//! specs are never duplicated.
//!
//! Consumption surface: only the machine-level function contracts already
//! verified inside the src tree are consumed (numeric_identifier / dot /
//! wildcard / op / pre_cmp / matches_comparator / cmp_precedence /
//! Version::new); the items with residual composition-level errors on the
//! src side (the Ok full-decomposition
//! synthesis of the identifier segment scan, the matches_req loop synthesis,
//! the version_req composition, the Prerelease/BuildMetadata FromStr chain)
//! carry no harness example theorems (the blocked ledger is in
//! out/bug-finder-summary.md).

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod semver;

use semver::impls::{pre_cmp, Ord2};
use semver::parse::{dot, numeric_identifier, op, wildcard};
use semver::{num_str_value, Comparator, Error, ErrorKind, Op, Position, Prerelease, Version};

fn main() {}

verus! {

/* ---------- helpers: constructing machine-level Prerelease / Version (byte model) ---------- */

fn mk_pre(bytes: &[u8]) -> (r: Prerelease)
    ensures
        r.bytes@ == bytes@,
{
    let mut out: Vec<u8> = Vec::new();
    let ghost s = bytes@;
    let mut i: usize = 0;
    while i < bytes.len()
        invariant
            0 <= i <= bytes@.len(),
            s == bytes@,
            out@.len() == i,
            forall|j: int| 0 <= j < out@.len() ==> out@[j] == s[j],
        decreases
            bytes.len() - i,
    {
        out.push(bytes[i]);
        i += 1;
    }
    proof {
        assert(out@.len() == s.len());
    }
    Prerelease { bytes: out }
}

fn mk_version(major: u64, minor: u64, patch: u64, pre: &[u8], build: &[u8]) -> (r: Version)
    ensures
        r.major == major && r.minor == minor && r.patch == patch && r.pre.bytes@ == pre@
            && r.build.bytes@ == build@,
{
    Version {
        major,
        minor,
        patch,
        pre: mk_pre(pre),
        build: semver::BuildMetadata {
            bytes: mk_pre(build).bytes,
        },
    }
}



/* ======================================================================
 * tests/test_version.rs:14 test_parse: the numeric-segment error bank
 * (the per-class classification of the Version::parse Errors doc, carried via
 * numeric_identifier)
 * ====================================================================== */

/// "123" => Ok(123) with an empty rest (the major numeric segment of "1.2.3").
exec fn ut_num_ok_123() {
    let ghost input_at_v = b"123"@;
    let r = numeric_identifier(b"123", Position::Major);
    match r {
        Ok((v, rest)) => {
            proof {
                // exists witness n=3: the empty-rest solution uniquely pins n
                assert(rest@.len() == 0);
                assert(num_str_value(input_at_v, 3) == 123);
            }
            assert(v == 123);
            assert(rest@.len() == 0);
        }
        Err(_) => assert(false),
    }
}

/// "07" => LeadingZero
/// Upstream doc (lib.rs:410-410):
///   - `1.0.01` &mdash; a numeric component has a leading zero.
exec fn ut_num_leading_zero() {
    let r = numeric_identifier(b"07", Position::Major);
    match r {
        Ok(_) => assert(false),
        Err(e) => {
            assert(semver::ek_num(e.kind) == semver::ek_num(ErrorKind::LeadingZero(Position::Major)));
            assert(semver::ek_pos(e.kind) == semver::pos_num(Position::Major));
        }
    }
}

/// The first 21 decimal digits => Overflow (18446744073709551616 = 2^64 is
/// just above the bound)
/// Upstream doc (lib.rs:421-421):
///   - `23456789999999999999.0.0` &mdash; overflow of a u64.
exec fn ut_num_overflow() {
    let r = numeric_identifier(b"18446744073709551616", Position::Major);
    match r {
        Ok(_) => assert(false),
        Err(e) => {
            assert(semver::ek_num(e.kind) == semver::ek_num(ErrorKind::Overflow(Position::Major)));
        }
    }
}

/// "a" => UnexpectedChar
/// Upstream doc (lib.rs:412-412):
///   - `1.0.unknown` &mdash; unexpected character in one of the components.
exec fn ut_num_unexpected_char() {
    let r = numeric_identifier(b"a", Position::Major);
    match r {
        Ok(_) => assert(false),
        Err(e) => {
            assert(semver::ek_num(e.kind) == semver::ek_num(ErrorKind::UnexpectedChar(
                Position::Major,
                0x61,
            )));
            assert(semver::ek_char(e.kind) == 0x61);
        }
    }
}

/// "" => UnexpectedEnd (the "1" face)
/// Upstream doc (lib.rs:405-408):
///   - `1.0` &mdash; too few numeric components. A SemVer version must have
///   exactly three. If you are looking at something that has fewer than
///   three numbers in it, it's possible it is a `VersionReq` instead (with
///   an implicit default `^` comparison operator).
exec fn ut_num_unexpected_end() {
    let r = numeric_identifier(b"", Position::Major);
    match r {
        Ok(_) => assert(false),
        Err(e) => {
            assert(semver::ek_num(e.kind) == semver::ek_num(ErrorKind::UnexpectedEnd(
                Position::Major,
            )));
        }
    }
}

/// "12x3" => Ok((12, "x3")) (truncation semantics: the prefix decomposition into value and rest)
exec fn ut_num_prefix_split() {
    let r = numeric_identifier(b"12x3", Position::Minor);
    match r {
        Ok((v, rest)) => {
            assert(v == 12);
            assert(rest@ == seq![0x78, 0x33]);
        }
        Err(_) => assert(false),
    }
}

/* ---------- machine-level examples for dot / wildcard / op ---------- */

exec fn ut_dot_cases() {
    match dot(b"", Position::Minor) {
        Ok(_) => assert(false),
        Err(e) => assert(semver::ek_num(e.kind) == semver::ek_num(ErrorKind::UnexpectedEnd(
            Position::Minor,
        ))),
    }
    match dot(b"x", Position::Patch) {
        Ok(_) => assert(false),
        Err(e) => {
            assert(semver::ek_num(e.kind) == semver::ek_num(ErrorKind::UnexpectedCharAfter(
                Position::Patch,
                0x78,
            )));
            assert(semver::ek_char(e.kind) == 0x78);
        }
    }
    match dot(b".5", Position::Minor) {
        Ok(rest) => assert(rest@ == seq![0x35]),
        Err(_) => assert(false),
    }
}

exec fn ut_wildcard_cases() {
    match wildcard(b"y") {
        Option::None => {}
        Option::Some(_) => assert(false),
    }
    match wildcard(b"*") {
        Option::None => assert(false),
        Option::Some((c, rest)) => {
            assert(c == 0x2a);
            assert(rest@.len() == 0);
        }
    }
    match wildcard(b"x2") {
        Option::None => assert(false),
        Option::Some((c, rest)) => {
            assert(c == 0x78);
            assert(rest@ == seq![0x32]);
        }
    }
}

/// op recognition (the machine-level face of the 8-way Op + the default ^; the two-character `>=`/`<=` side from the VersionReq doc)
/// Upstream doc (lib.rs:173-174):
///   - A [`Comparator`] is an operator ([`Op`]) and a partial version, separated
///   by optional whitespace. For example `>=1.0.0` or `>=1.0`.
exec fn ut_op_cases() {
    let (o1, t1, d1) = op(b"=1.0");
    assert(o1 == Op::Exact && t1@ == seq![0x31, 0x2e, 0x30] && !d1);

    let (o2, t2, d2) = op(b">=2.0");
    assert(o2 == Op::GreaterEq && t2@ == seq![0x32, 0x2e, 0x30] && !d2);

    let (o3, t3, d3) = op(b"<=1");
    assert(o3 == Op::LessEq && t3@ == seq![0x31] && !d3);

    let (o4, t4, d4) = op(b"<1");
    assert(o4 == Op::Less && t4@ == seq![0x31] && !d4);

    let (o5, t5, d5) = op(b">2");
    assert(o5 == Op::Greater && t5@ == seq![0x32] && !d5);

    let (o6, t6, d6) = op(b"~1.2.3");
    assert(o6 == Op::Tilde && t6@ == seq![0x31, 0x2e, 0x32, 0x2e, 0x33] && !d6);

    let (o7, t7, d7) = op(b"^1");
    assert(o7 == Op::Caret && t7@ == seq![0x31] && !d7);

    /* Op::DEFAULT (parse.rs:152-154 upstream const DEFAULT: Self = Self::Caret) */
    let (o8, t8, d8) = op(b"1.2.3");
    assert(o8 == Op::Caret && t8@ == seq![0x31, 0x2e, 0x32, 0x2e, 0x33] && d8);
}

/* ======================================================================
 * lib.rs Prerelease Total-ordering doc example chains (the impls.rs machine-level face = pre_cmp)
 * ====================================================================== */

/// Upstream doc (lib.rs:147-156):
///   - Identifiers consisting of only digits are compared
///   numerically:&ensp;`1.0.0-pre.8` is less than `1.0.0-pre.12`.
///   - Identifiers that contain a letter or hyphen are compared in ASCII sort
///   order:&ensp;`1.0.0-pre12` is less than `1.0.0-pre8`.
///   - Any numeric identifier is always less than any non-numeric
///   identifier:&ensp;`1.0.0-pre.1` is less than `1.0.0-pre.x`.
///   Example:&ensp;`1.0.0-alpha`&ensp;&lt;&ensp;`1.0.0-alpha.1`&ensp;&lt;&ensp;`1.0.0-alpha.beta`&ensp;&lt;&ensp;`1.0.0-beta`&ensp;&lt;&ensp;`1.0.0-beta.2`&ensp;&lt;&ensp;`1.0.0-beta.11`&ensp;&lt;&ensp;`1.0.0-rc.1`&ensp;&lt;&ensp;`1.0.0`
exec fn ut_pre_doc_chain_main() {
    let alpha = mk_pre(b"alpha");
    let alpha1 = mk_pre(b"alpha.1");
    let alphabeta = mk_pre(b"alpha.beta");
    let beta = mk_pre(b"beta");
    let beta2 = mk_pre(b"beta.2");
    let beta11 = mk_pre(b"beta.11");
    let rc1 = mk_pre(b"rc.1");
    let release = mk_pre(b"");

    let r = pre_cmp(&alpha, &alpha1);
    assert(r == Ord2::Less);
    let r = pre_cmp(&alpha1, &alphabeta);
    assert(r == Ord2::Less);
    let r = pre_cmp(&alphabeta, &beta);
    assert(r == Ord2::Less);
    let r = pre_cmp(&beta, &beta2);
    assert(r == Ord2::Less);
    // "beta.2 < beta.11": numeric comparison of digit segments (2 < 11 -- doc "compared numerically")
    let r = pre_cmp(&beta2, &beta11);
    assert(r == Ord2::Less);
    let r = pre_cmp(&beta11, &rc1);
    assert(r == Ord2::Less);
    // "a pre-release version is considered less than the ordinary release"
    let r = pre_cmp(&rc1, &release);
    assert(r == Ord2::Less);
    let r = pre_cmp(&release, &alpha);
    assert(r == Ord2::Greater);
    let rp = pre_cmp(&release, &mk_pre(b""));
    assert(rp == Ord2::Equal);
}

/// The Prerelease doc Example chain (the flat chain expanded into pairwise
/// assertions)
/// Upstream doc (lib.rs:301-307):
///   Pre-releases have a total order defined by the SemVer spec. It uses
///   lexicographic ordering of dot-separated components. Identifiers consisting
///   of only digits are compared numerically. Otherwise, identifiers are compared
///   in ASCII sort order. Any numeric identifier is always less than any
///   non-numeric identifier.
///   Example:&ensp;`alpha`&ensp;&lt;&ensp;`alpha.85`&ensp;&lt;&ensp;`alpha.90`&ensp;&lt;&ensp;`alpha.200`&ensp;&lt;&ensp;`alpha.0a`&ensp;&lt;&ensp;`alpha.1a0`&ensp;&lt;&ensp;`alpha.a`&ensp;&lt;&ensp;`beta`
exec fn ut_pre_doc_chain_example() {
    let a0 = mk_pre(b"alpha");
    let a85 = mk_pre(b"alpha.85");
    let a90 = mk_pre(b"alpha.90");
    let a200 = mk_pre(b"alpha.200");
    let a0a = mk_pre(b"alpha.0a");
    let a1a0 = mk_pre(b"alpha.1a0");
    let aa = mk_pre(b"alpha.a");
    let be = mk_pre(b"beta");
    let r = pre_cmp(&a0, &a85);
    assert(r == Ord2::Less);
    let r = pre_cmp(&a85, &a90);
    assert(r == Ord2::Less);
    // 90 < 200: three-digit vs two-digit digit-length tie-break
    let r = pre_cmp(&a90, &a200);
    assert(r == Ord2::Less);
    // 200 < 0a: a digit segment < a non-digit segment (the machine-level mirror
    //     of doc "Numeric identifiers always have lower precedence than non-numeric identifiers")
    let r = pre_cmp(&a200, &a0a);
    assert(r == Ord2::Less);
    let r = pre_cmp(&a0a, &a1a0);
    assert(r == Ord2::Less);
    let r = pre_cmp(&a1a0, &aa);
    assert(r == Ord2::Less);
    let r = pre_cmp(&aa, &be);
    assert(r == Ord2::Less);
}

/// pre12 < pre8
/// Upstream doc (lib.rs:150-155):
///   - Identifiers that contain a letter or hyphen are compared in ASCII sort
///   order:&ensp;`1.0.0-pre12` is less than `1.0.0-pre8`.
///   - Any numeric identifier is always less than any non-numeric
///   identifier:&ensp;`1.0.0-pre.1` is less than `1.0.0-pre.x`.
exec fn ut_pre_ascii_vs_numeric() {
    // doc: "1.0.0-pre.1 < 1.0.0-pre.x": digit segment < non-digit segment
    let p1 = mk_pre(b"pre.1");
    let px = mk_pre(b"pre.x");
    let r = pre_cmp(&p1, &px);
    assert(r == Ord2::Less);
    // doc: "1.0.0-pre12" < "1.0.0-pre8": lexicographic order of non-numeric segments ('1' < '8')
    let pre12 = mk_pre(b"pre12");
    let pre8 = mk_pre(b"pre8");
    let r = pre_cmp(&pre12, &pre8);
    assert(r == Ord2::Less);
}

/* ======================================================================
 * the eval.rs Op semantics surface (doc equivalence instances of = and ^), via matches_comparator
 * ====================================================================== */

fn mk_cmp(op: Op, major: u64, minor: Option<u64>, patch: Option<u64>, pre: &[u8]) -> (c: Comparator) {
    Comparator {
        op,
        major,
        minor,
        patch,
        pre: mk_pre(pre),
    }
}

/// "=1.2.3-alpha" <=> only equal mmp + equal pre match (Op::Exact plus the
///     pre gate; the UT face of "1.0.0-pre" not being matched by "=1.0.0")
/// Upstream doc (lib.rs:203-206):
///   # Op::Exact
///   - &ensp;**`=I.J.K`**&emsp;&mdash;&emsp;exactly the version I.J.K
///   - &ensp;**`=I.J`**&emsp;&mdash;&emsp;equivalent to `>=I.J.0, <I.(J+1).0`
///   - &ensp;**`=I`**&emsp;&mdash;&emsp;equivalent to `>=I.0.0, <(I+1).0.0`
exec fn ut_eval_exact_pre_gate() {
    let c = mk_cmp(Op::Exact, 1, Option::Some(2), Option::Some(3), b"alpha");
    let v_hit = mk_version(1, 2, 3, b"alpha", b"");
    let r = c.matches(&v_hit);
    assert(r);

    let v_other_pre = mk_version(1, 2, 3, b"beta", b"");
    let r = c.matches(&v_other_pre);
    assert(!r);

    let v_other_patch = mk_version(1, 2, 4, b"alpha", b"");
    let r = c.matches(&v_other_patch);
    assert(!r);

    /* "=1.0.0" never matches any pre-release version (the UT face of "1.0.0-pre") */
    let c0 = mk_cmp(Op::Exact, 1, Option::Some(0), Option::Some(0), b"");
    let rr_343 = c0.matches(&mk_version(1, 0, 0, b"pre", b""));
    assert(!rr_343);
}

/// The three shapes of the Op::Caret doc face
/// Upstream doc (lib.rs:234-241):
///   # Op::Caret&emsp;("compatible" updates)
///   *Caret requirements allow parts that are **right of the first nonzero** part of the semver version to increase.*
///   - &ensp;**`^I.J.K`**&ensp;(for I\>0)&emsp;&mdash;&emsp;equivalent to `>=I.J.K, <(I+1).0.0`
///   - &ensp;**`^0.J.K`**&ensp;(for J\>0)&emsp;&mdash;&emsp;equivalent to `>=0.J.K, <0.(J+1).0`
///   - &ensp;**`^0.0.K`**&emsp;&mdash;&emsp;equivalent to `=0.0.K`
///   - &ensp;**`^I.J`**&ensp;(for I\>0 or J\>0)&emsp;&mdash;&emsp;equivalent to `^I.J.0`
///   - &ensp;**`^0.0`**&emsp;&mdash;&emsp;equivalent to `=0.0`
///   - &ensp;**`^I`**&emsp;&mdash;&emsp;equivalent to `=I`
exec fn ut_eval_caret_doc() {
    /* ^1.2.3 hits 1.2.3 and 1.9.9; misses 2.0.0 and 1.2.2-absent?? (the caret lower bound is inclusive) */
    let c = mk_cmp(Op::Caret, 1, Option::Some(2), Option::Some(3), b"");
    let rr_351 = c.matches(&mk_version(1, 2, 3, b"", b""));
    assert(rr_351);
    let rr_352 = c.matches(&mk_version(1, 9, 9, b"", b""));
    assert(rr_352);
    let rr_353 = c.matches(&mk_version(2, 0, 0, b"", b""));
    assert(!rr_353);
    let rr_354 = c.matches(&mk_version(0, 9, 9, b"", b""));
    assert(!rr_354);

    /* ^0.2.3 hits 0.2.3 / 0.2.9; misses 0.3.0 */
    let c02 = mk_cmp(Op::Caret, 0, Option::Some(2), Option::Some(3), b"");
    let rr_358 = c02.matches(&mk_version(0, 2, 3, b"", b""));
    assert(rr_358);
    let rr_359 = c02.matches(&mk_version(0, 2, 9, b"", b""));
    assert(rr_359);
    let rr_360 = c02.matches(&mk_version(0, 3, 0, b"", b""));
    assert(!rr_360);

    /* ^0.0.3 <=> =0.0.3 */
    let c003 = mk_cmp(Op::Caret, 0, Option::Some(0), Option::Some(3), b"");
    let rr_364 = c003.matches(&mk_version(0, 0, 3, b"", b""));
    assert(rr_364);
    let rr_365 = c003.matches(&mk_version(0, 0, 4, b"", b""));
    assert(!rr_365);
    let rr_366 = c003.matches(&mk_version(0, 1, 0, b"", b""));
    assert(!rr_366);
}

/// Op::Greater face: ">=2.1.0-alpha2" hits 2.1.0-alpha3 (doc example), misses 2.1.0-alpha1;
///     pre gate: a comparator with equal mmp + nonempty pre activates its pre range.
/// Upstream doc (lib.rs:213-216):
///   # Op::GreaterEq
///   - &ensp;**`>=I.J.K`**
///   - &ensp;**`>=I.J`**&emsp;&mdash;&emsp;equivalent to `>=I.J.0`
///   - &ensp;**`>=I`**&emsp;&mdash;&emsp;equivalent to `>=I.0.0`
exec fn ut_eval_geq_pre_ordering() {
    let c = mk_cmp(Op::GreaterEq, 2, Option::Some(1), Option::Some(0), b"alpha2");
    let rr_373 = c.matches(&mk_version(2, 1, 0, b"alpha2", b""));
    assert(rr_373);
    let rr_374 = c.matches(&mk_version(2, 1, 0, b"alpha3", b""));
    assert(rr_374);
    let rr_375 = c.matches(&mk_version(3, 0, 0, b"", b""));
    assert(rr_375);
    let rr_376 = c.matches(&mk_version(2, 1, 0, b"alpha1", b""));
    assert(!rr_376);
    let rr_377 = c.matches(&mk_version(2, 0, 0, b"alpha2", b""));
    assert(!rr_377);
    let rr_378 = c.matches(&mk_version(2, 1, 0, b"", b""));
    assert(!rr_378);
}

/* ======================================================================
 * the lib.rs cmp_precedence doc examples ("disregarding build metadata")
 * ====================================================================== */

/// Upstream doc (lib.rs:426-429):
///   Compare the major, minor, patch, and pre-release value of two versions,
///   disregarding build metadata. Versions that differ only in build metadata
///   are considered equal. This comparison is what the SemVer spec refers to
///   as "precedence".
exec fn ut_cmp_precedence_build_ignored() {
    let a = mk_version(1, 20, 0, b"", b"c144a98");
    let b = mk_version(1, 20, 0, b"", b"");
    let c2 = mk_version(1, 20, 0, b"", b"bc17664");
    let cp = a.cmp_precedence(&b);
    assert(cp == Ord2::Equal);
    let cp = b.cmp_precedence(&c2);
    assert(cp == Ord2::Equal);
    let cp = a.cmp_precedence(&c2);
    assert(cp == Ord2::Equal);
}

/// Upstream doc (lib.rs:133-137):
///   - The major, minor, and patch number are compared numerically from left to
///   right, lexicographically ordered as a 3-tuple of integers. So for example
///   version `1.5.0` is less than version `1.19.0`, despite the fact that
///   "1.19.0" &lt; "1.5.0" as ASCIIbetically compared strings and 1.19 &lt; 1.5
///   as real numbers.
exec fn ut_cmp_precedence_ord() {
    let ten = mk_version(1, 19, 0, b"", b"");
    let five = mk_version(1, 5, 0, b"", b"");
    /* doc: "1.5.0" is less than "1.19.0"; ASCIIbetically "1.19.0" < "1.5.0" runs
     * the other way: the numeric order on the components gives 5 < 19 */
    let cp = five.cmp_precedence(&ten);
    assert(cp == Ord2::Less);
    let cp = ten.cmp_precedence(&five);
    assert(cp == Ord2::Greater);
    let pre = mk_version(1, 0, 0, b"alpha", b"");
    let rel = mk_version(1, 0, 0, b"", b"");
    let cp = pre.cmp_precedence(&rel);
    assert(cp == Ord2::Less);
}

/* ---------- the Version::new doc-doctest face ---------- */

/// The lib.rs Version::new doctest face
/// Upstream doc (lib.rs:372-388):
///   Create `Version` with an empty pre-release and build metadata.
///   Equivalent to:
///   # use semver::{BuildMetadata, Prerelease, Version};
///   #
///   # const fn new(major: u64, minor: u64, patch: u64) -> Version {
///   Version {
///   major,
///   minor,
///   patch,
///   pre: Prerelease::EMPTY,
///   build: BuildMetadata::EMPTY,
///   }
///   # }
exec fn ut_version_new_semantics() {
    let v = Version::new(1, 2, 3);
    assert(v.major == 1 && v.minor == 2 && v.patch == 3);
    assert(v.pre.bytes@.len() == 0);
    assert(v.build.bytes@.len() == 0);
}

} // verus!
