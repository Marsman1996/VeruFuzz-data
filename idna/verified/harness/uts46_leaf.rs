// Assertion-theorem harness for the verified uts46 leaf/skeleton face.
//
// Upstream pin: 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a (servo/rust-url,
// SUBDIR=idna). Consumption: includes verified/src/uts46.rs via #[path] as a
// module; no spec or proof content is copied here.
//
// The theorems below witness the test-relevant commitments of the leaf
// helpers: the ASCII fast-path scan tier of process_inner (byte-level defer
// points of the tests/tests.rs and tests/unitbis.rs punycode-prefix inputs),
// punycode-prefix detection, the label passthrough rules, the
// verify_dns_length accept/reject families used by tests/uts46.rs, the
// hyphen-position marking families of check_hyphens unit-test inputs, the
// punycode classification behind the tests/unit.rs examples, and the
// AsciiDenyList row semantics (up-case folding, URL deny rows).
//
// The upstream quoted characters in the char literals below (the sharp-s of
// the examples test, U+FFFD) are spelled with ASCII escapes and reproduce
// upstream test data (tests/unit.rs "BloSS" examples and the
// punycode-classification rules of uts46.rs:247-267).
//
// Deferred (follow-up batches, recorded in the ledger): the sink/pipeline
// harness obligations (Uts46::process and the idna_adapter-backed machinery)
// and the punycode vector roundtrips (their src contracts need the
// output-model and completeness extensions first).

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/uts46.rs"]
mod uts46_v;

use uts46_v::AsciiDenyList;
use uts46_v::FastPathScan;
use uts46_v::PunycodeClassification;
use uts46_v::apply_ascii_deny_list_to_lower_cased_unicode;
use uts46_v::apply_ascii_deny_list_to_potentially_upper_case_ascii;
use uts46_v::bit_is_set;
use uts46_v::check_hyphens;
use uts46_v::classify_for_punycode;
use uts46_v::deny_list_bits;
use uts46_v::defer_index_from;
use uts46_v::dns_scan_ok;
use uts46_v::first_non_fast;
use uts46_v::glyphless_pred;
use uts46_v::has_fffd_from;
use uts46_v::is_fast_byte;
use uts46_v::has_punycode_prefix;
use uts46_v::is_ascii;
use uts46_v::is_passthrough_ascii_label;
use uts46_v::ldh_pred;
use uts46_v::process_inner_ascii_scan;
use uts46_v::upper_case_pred;
use uts46_v::url_deny_pred;
use uts46_v::verify_dns_length;

verus! {

/* ============ ground inputs (the byte/char strings of the UT corpus) ============ */

/// "abc.def"
fn v_abc_dot() -> (r: Vec<u8>)
    ensures r@.len() == 7,
        r@ == seq![b'a', b'b', b'c', b'.', b'd', b'e', b'f']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'a');
    r.push(b'b');
    r.push(b'c');
    r.push(b'.');
    r.push(b'd');
    r.push(b'e');
    r.push(b'f');
    r
}

/// "ab1"
fn v_ab1() -> (r: Vec<u8>)
    ensures r@.len() == 3,
        r@ == seq![b'a', b'b', b'1']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'a');
    r.push(b'b');
    r.push(b'1');
    r
}

/// "A1"
fn v_upper1() -> (r: Vec<u8>)
    ensures r@.len() == 2,
        r@ == seq![b'A', b'1']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'A');
    r.push(b'1');
    r
}

/// "ab.c1"
fn v_ab_c1() -> (r: Vec<u8>)
    ensures r@.len() == 5,
        r@ == seq![b'a', b'b', b'.', b'c', b'1']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'a');
    r.push(b'b');
    r.push(b'.');
    r.push(b'c');
    r.push(b'1');
    r
}

/// "xn--tda"
fn v_xn_tda() -> (r: Vec<u8>)
    ensures r@.len() == 7,
        r@ == seq![b'x', b'n', b'-', b'-', b't', b'd', b'a']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'x');
    r.push(b'n');
    r.push(b'-');
    r.push(b'-');
    r.push(b't');
    r.push(b'd');
    r.push(b'a');
    r
}

/// "XN--tda"
fn v_XN_tda() -> (r: Vec<u8>)
    ensures r@.len() == 7,
        r@ == seq![b'X', b'N', b'-', b'-', b't', b'd', b'a']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'X');
    r.push(b'N');
    r.push(b'-');
    r.push(b'-');
    r.push(b't');
    r.push(b'd');
    r.push(b'a');
    r
}

/// "Xn--"
fn v_Xn_dd() -> (r: Vec<u8>)
    ensures r@.len() == 4,
        r@ == seq![b'X', b'n', b'-', b'-']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'X');
    r.push(b'n');
    r.push(b'-');
    r.push(b'-');
    r
}

/// "xx-r-" (prefix shape with a wrong byte in position 1 after masking)
fn v_xx_a() -> (r: Vec<u8>)
    ensures r@.len() == 6,
        r@ == seq![b'x', b'x', b'-', b'-', b'q', b'q']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'x');
    r.push(b'x');
    r.push(b'-');
    r.push(b'-');
    r.push(b'q');
    r.push(b'q');
    r
}

/// "xn-a-"
fn v_xn_a_d() -> (r: Vec<u8>)
    ensures r@.len() == 5,
        r@ == seq![b'x', b'n', b'-', b'a', b'-']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'x');
    r.push(b'n');
    r.push(b'-');
    r.push(b'a');
    r.push(b'-');
    r
}

/// "xn-" (too short)
fn v_xn3() -> (r: Vec<u8>)
    ensures r@.len() == 3,
        r@ == seq![b'x', b'n', b'-']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'x');
    r.push(b'n');
    r.push(b'-');
    r
}

/// "a1b"
fn v_a1b() -> (r: Vec<u8>)
    ensures r@.len() == 3,
        r@ == seq![b'a', b'1', b'b']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'a');
    r.push(b'1');
    r.push(b'b');
    r
}

/// "-ab"
fn v_dash_ab() -> (r: Vec<u8>)
    ensures r@.len() == 3,
        r@ == seq![b'-', b'a', b'b']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'-');
    r.push(b'a');
    r.push(b'b');
    r
}

/// "ab-"
fn v_ab_dash() -> (r: Vec<u8>)
    ensures r@.len() == 3,
        r@ == seq![b'a', b'b', b'-']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'a');
    r.push(b'b');
    r.push(b'-');
    r
}

/// "ab.cd" (a dot inside a would-be label)
fn v_ab_dot_cd() -> (r: Vec<u8>)
    ensures r@.len() == 5,
        r@ == seq![b'a', b'b', b'.', b'c', b'd']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'a');
    r.push(b'b');
    r.push(b'.');
    r.push(b'c');
    r.push(b'd');
    r
}

/// "1ab" (a leading digit cannot start a passthrough label)
fn v_one_ab() -> (r: Vec<u8>)
    ensures r@.len() == 3,
        r@ == seq![b'1', b'a', b'b']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'1');
    r.push(b'a');
    r.push(b'b');
    r
}

/// "abc"
fn v_abc() -> (r: Vec<u8>)
    ensures r@.len() == 3,
        r@ == seq![b'a', b'b', b'c']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'a');
    r.push(b'b');
    r.push(b'c');
    r
}

/// "example.com"
fn v_example_com() -> (r: Vec<u8>)
    ensures r@.len() == 11,
        r@ == seq![b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b'c', b'o', b'm']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'e');
    r.push(b'x');
    r.push(b'a');
    r.push(b'm');
    r.push(b'p');
    r.push(b'l');
    r.push(b'e');
    r.push(b'.');
    r.push(b'c');
    r.push(b'o');
    r.push(b'm');
    r
}

/// "example.com." (trailing root label dot)
fn v_example_com_dot() -> (r: Vec<u8>)
    ensures r@.len() == 12,
        r@ == seq![b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b'c', b'o', b'm', b'.']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'e');
    r.push(b'x');
    r.push(b'a');
    r.push(b'm');
    r.push(b'p');
    r.push(b'l');
    r.push(b'e');
    r.push(b'.');
    r.push(b'c');
    r.push(b'o');
    r.push(b'm');
    r.push(b'.');
    r
}

/// "a..b" (an empty middle label)
fn v_a_ddot_b() -> (r: Vec<u8>)
    ensures r@.len() == 4,
        r@ == seq![b'a', b'.', b'.', b'b']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'a');
    r.push(b'.');
    r.push(b'.');
    r.push(b'b');
    r
}

/// ".abc" (an empty leading label)
fn v_dot_abc() -> (r: Vec<u8>)
    ensures r@.len() == 4,
        r@ == seq![b'.', b'a', b'b', b'c']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'.');
    r.push(b'a');
    r.push(b'b');
    r.push(b'c');
    r
}

/// 63 'a' bytes (the per-label bound of the DNS length rule)
fn v_a63() -> (r: Vec<u8>)
    ensures r@.len() == 63,
        forall |p: int| 0 <= p < r@.len() ==> r@[p] == b'a'
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 63
        invariant i <= 63,
            r@.len() == i,
            forall |p: int| 0 <= p < r@.len() ==> r@[p] == b'a',
        decreases 63 - i
    {
        r.push(b'a');
        i = i + 1;
    }
    r
}

/// 64 'a' bytes (one past the per-label bound)
fn v_a64() -> (r: Vec<u8>)
    ensures r@.len() == 64,
        forall |p: int| 0 <= p < r@.len() ==> r@[p] == b'a'
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 64
        invariant i <= 64,
            r@.len() == i,
            forall |p: int| 0 <= p < r@.len() ==> r@[p] == b'a',
        decreases 64 - i
    {
        r.push(b'a');
        i = i + 1;
    }
    r
}

/* ============ ASCII fast-path scan tier (uts46.rs process_inner) ============ */

/// Lower-case letters and dots all the way (including a trailing dot and the
/// empty input): the whole input stays on the fast-path tier (upstream
/// returns (domain_name.len(), false, false)).
pub exec fn witness_fast_path_pass() -> (r: bool)
    ensures
        r,
{
    let v1 = v_abc_dot();
    let s1: &[u8] = v1.as_slice();
    assert(forall |p: int| 0 <= p < s1.len() ==> is_fast_byte(s1[p])) by {
        assert(is_fast_byte(s1[0]));
        assert(is_fast_byte(s1[1]));
        assert(is_fast_byte(s1[2]));
        assert(is_fast_byte(s1[3]));
        assert(is_fast_byte(s1[4]));
        assert(is_fast_byte(s1[5]));
        assert(is_fast_byte(s1[6]));
    }
    let a = process_inner_ascii_scan(s1);
    proof {
        assert(a == FastPathScan::FastPathPass);
    }
    // The empty input stays on the fast path (vacuous).
    let v2: Vec<u8> = Vec::new();
    let s2: &[u8] = v2.as_slice();
    assert(forall |p: int| 0 <= p < s2.len() ==> is_fast_byte(s2[p])) by {}
    let b = process_inner_ascii_scan(s2);
    proof {
        assert(b == FastPathScan::FastPathPass);
    }
    true
}

/// A non-fast byte in the first label defers from index 0 (the whole input
/// becomes the slow-path tail, as upstream's most_recent_label_start begins
/// at the iterator start).
pub exec fn witness_fast_path_defer_whole() -> (r: bool)
    ensures
        r,
{
    let v = v_ab1();
    let s: &[u8] = v.as_slice();
    assert(is_fast_byte(s[0]));
    assert(is_fast_byte(s[1]));
    assert(!is_fast_byte(s[2]));
    proof {
        unfold_first_non_fast_chain(s, 0, 2);
        assert(first_non_fast(s, 0) == 2);
        // Both label candidates below the offending byte are letters.
        assert(defer_index_from(s, 2) == defer_index_from(s, 1));
        assert(defer_index_from(s, 1) == defer_index_from(s, 0));
        assert(defer_index_from(s, 0) == 0);
    }
    let a = process_inner_ascii_scan(s);
    proof {
        assert(a == FastPathScan::FastPathDefer(0));
    }
    let vu = v_upper1();
    let su: &[u8] = vu.as_slice();
    assert(!is_fast_byte(su[0]));
    proof {
        assert(first_non_fast(su, 0) == 0);
        assert(defer_index_from(su, 0) == 0);
    }
    let b = process_inner_ascii_scan(su);
    proof {
        assert(b == FastPathScan::FastPathDefer(0));
    }
    true
}

/// After a dot, the deferral tail starts at the most recently started label:
/// for "ab.c1" the offending byte is the digit and the tail is "c1".
pub exec fn witness_fast_path_defer_tail_label() -> (r: bool)
    ensures
        r,
{
    let v = v_ab_c1();
    let s: &[u8] = v.as_slice();
    assert(is_fast_byte(s[0]));
    assert(is_fast_byte(s[1]));
    assert(is_fast_byte(s[2]));
    assert(is_fast_byte(s[3]));
    assert(!is_fast_byte(s[4]));
    proof {
        unfold_first_non_fast_chain(s, 0, 4);
        assert(first_non_fast(s, 0) == 4);
        // 'c' is not the dot: step once more; then the dot at index 2 pins
        // the deferral tail start to index 3.
        assert(s[3] != b'.');
        assert(defer_index_from(s, 4) == defer_index_from(s, 3));
        assert(s[2] == b'.');
        assert(defer_index_from(s, 3) == 3);
    }
    let a = process_inner_ascii_scan(s);
    proof {
        assert(a == FastPathScan::FastPathDefer(3));
    }
    true
}

/* ============ punycode prefix detection (uts46.rs has_punycode_prefix) ============ */

/// The "xn--" prefix matches case-insensitively on the xn part and requires
/// the exact hyphen-hyphen pair in positions 2-3.
pub exec fn witness_has_punycode_prefix() -> (r: bool)
    ensures
        r,
{
    let v1 = v_xn_tda();
    let v2 = v_XN_tda();
    let v3 = v_Xn_dd();
    let v4 = v_xn_a_d();
    let v5 = v_xx_a();
    let v6 = v_xn3();
    let t1 = has_punycode_prefix(v1.as_slice());
    let t2 = has_punycode_prefix(v2.as_slice());
    let t3 = has_punycode_prefix(v3.as_slice());
    let f1 = has_punycode_prefix(v4.as_slice());
    let f2 = has_punycode_prefix(v5.as_slice());
    let f3 = has_punycode_prefix(v6.as_slice());
    // The 0xDF folding of the byte pairs is bitwise and needs the BV engine
    // even on ground constants; the element facts come from the builders.
    // Covered fold rows: x/X (0x78, 0x58), n (0x6E), N/n-fold (0x4E).
    assert((0x78u32 & 0xDF) == 0x58) by (bit_vector);
    assert((0x58u32 & 0xDF) == 0x58) by (bit_vector);
    assert((0x6Eu32 & 0xDF) == 0x4E) by (bit_vector);
    assert((0x4Eu32 & 0xDF) == 0x4E) by (bit_vector);
    // v1 = "xn--tda": x and n fold onto the mask comparisons cleanly.
    assert(v1[0] as u32 == 0x78);
    assert(v1[1] as u32 == 0x6E);
    // v2 = "XN--tda": the fold keeps the already-in-case bytes.
    assert(v2[0] as u32 == 0x58);
    assert(v2[1] as u32 == 0x4E);
    // v3 = "Xn--": mixed case on the first two bytes.
    assert(v3[0] as u32 == 0x58);
    assert(v3[1] as u32 == 0x6E);
    (t1 && t2 && t3 && !f1 && !f2 && !f3)
}

/* ============ ASCII label passthrough (uts46.rs is_passthrough_ascii_label) ============ */

/// Pure lowercase LDH labels pass through; a punycode-prefix-shaped label,
/// leading/trailing hyphens, a leading digit, a dot inside the label, and
/// non-LDH bytes do not (the stricture rationale is at uts46.rs:149-160).
pub exec fn witness_is_passthrough_ascii_label() -> (r: bool)
    ensures
        r,
{
    let v0: Vec<u8> = Vec::new();
    let v1 = v_abc();
    let v2 = v_a1b();
    let v3 = v_xn_tda();
    let v4 = v_dash_ab();
    let v5 = v_ab_dash();
    let v6 = v_ab_dot_cd();
    let v7 = v_one_ab();
    let t1 = is_passthrough_ascii_label(v1.as_slice());
    let t2 = is_passthrough_ascii_label(v2.as_slice());
    let t3 = is_passthrough_ascii_label(v0.as_slice());
    let f1 = is_passthrough_ascii_label(v3.as_slice());
    let f2 = is_passthrough_ascii_label(v4.as_slice());
    let f3 = is_passthrough_ascii_label(v5.as_slice());
    let f4 = is_passthrough_ascii_label(v6.as_slice());
    let f5 = is_passthrough_ascii_label(v7.as_slice());
    // Per-element facts of the passing tails (the spec's inner range rule).
    assert(forall |i: int| 1 <= i < v1.len() ==> is_ldh_byte(v1[i])) by {
        assert(is_ldh_byte(v1[1]));
        assert(is_ldh_byte(v1[2]));
    }
    assert(forall |i: int| 1 <= i < v2.len() ==> is_ldh_byte(v2[i])) by {
        assert(is_ldh_byte(v2[1]));
        assert(is_ldh_byte(v2[2]));
    }
    (t1 && t2 && t3 && !f1 && !f2 && !f3 && !f4 && !f5)
}

/* ============ verify_dns_length (uts46.rs verify_dns_length) ============ */

/// Plain multi-label names within the rules verify; a 63-byte label is at
/// the accepted per-label boundary.
pub exec fn witness_verify_dns_length_accepts() -> (r: bool)
    ensures
        r,
{
    let v1 = v_abc();
    let s1: &[u8] = v1.as_slice();
    assert(forall |i: int| 0 <= i < s1.len() ==> s1[i] < 0x80) by {
        assert(s1[0] == b'a');
        assert(s1[1] == b'b');
        assert(s1[2] == b'c');
    }
    let a = verify_dns_length(s1, false);
    proof {
        unfold_scan_range(s1, 3, 0, 0, 3);
    }
    let v2 = v_example_com();
    let s2: &[u8] = v2.as_slice();
    assert(forall |i: int| 0 <= i < s2.len() ==> s2[i] < 0x80) by {
        assert(s2[0] == b'e');
        assert(s2[1] == b'x');
        assert(s2[2] == b'a');
        assert(s2[3] == b'm');
        assert(s2[4] == b'p');
        assert(s2[5] == b'l');
        assert(s2[6] == b'e');
        assert(s2[8] == b'c');
        assert(s2[9] == b'o');
        assert(s2[10] == b'm');
    }
    let b = verify_dns_length(s2, false);
    proof {
        // "example.com" scans clean: the two label segments are 7 and 3 bytes.
        unfold_scan_range(s2, 11, 0, 0, 7);
        assert(s2[7] == b'.');
        assert(dns_scan_ok(s2, 11, 0, 7) == (dns_scan_ok(s2, 11, 8, 8)));
        unfold_scan_range(s2, 11, 8, 8, 11);
    }
    let v3 = v_a63();
    let s3: &[u8] = v3.as_slice();
    assert(forall |i: int| 0 <= i < s3.len() ==> s3[i] < 0x80);
    let c = verify_dns_length(s3, false);
    proof {
        unfold_scan_range(s3, 63, 0, 0, 63);
    }
    (a && b && c)
}

/// The reject family: empty labels (a leading or doubled dot), an oversize
/// 64-byte label, and a trailing root label dot that the flag does not allow;
/// the trailing dot is accepted when the flag allows it.
pub exec fn witness_verify_dns_length_rejects() -> (r: bool)
    ensures
        r,
{
    let v1 = v_a_ddot_b();
    let s1: &[u8] = v1.as_slice();
    assert(forall |i: int| 0 <= i < s1.len() ==> s1[i] < 0x80) by {
        assert(s1[0] == b'a');
        assert(s1[1] == b'.');
        assert(s1[2] == b'.');
        assert(s1[3] == b'b');
    }
    let empty_label = verify_dns_length(s1, false);
    proof {
        unfold_scan_range(s1, 4, 0, 0, 1);
        assert(dns_scan_ok(s1, 4, 1, 1) == dns_scan_ok(s1, 4, 2, 2));
    }
    let v2 = v_dot_abc();
    let s2: &[u8] = v2.as_slice();
    assert(forall |i: int| 0 <= i < s2.len() ==> s2[i] < 0x80) by {
        assert(s2[0] == b'.');
        assert(s2[1] == b'a');
        assert(s2[2] == b'b');
        assert(s2[3] == b'c');
    }
    let leading_dot = verify_dns_length(s2, false);
    let v3 = v_a64();
    let s3: &[u8] = v3.as_slice();
    assert(forall |i: int| 0 <= i < s3.len() ==> s3[i] < 0x80);
    let oversize = verify_dns_length(s3, false);
    proof {
        unfold_scan_range(s3, 64, 0, 0, 64);
    }
    let v4 = v_example_com_dot();
    let s4: &[u8] = v4.as_slice();
    assert(forall |i: int| 0 <= i < s4.len() ==> s4[i] < 0x80);
    let trailing_dot_rejected = verify_dns_length(s4, false);
    let trailing_dot_allowed = verify_dns_length(s4, true);
    proof {
        unfold_scan_range(s4, 11, 0, 0, 7);
        let s2b: &[u8] = s4;
        assert(s2b[7] == b'.');
        assert(dns_scan_ok(s2b, 11, 0, 7) == dns_scan_ok(s2b, 11, 8, 8));
        unfold_scan_range(s2b, 11, 8, 8, 11);
    }
    (!empty_label
        && !leading_dot
        && !oversize
        && !trailing_dot_rejected
        && trailing_dot_allowed)
}

/* ============ hyphen-position marking (uts46.rs check_hyphens) ============ */

/// Fail-fast mode: a leading-hyphen label reports the early-return channel
/// without touching the label (upstream returns before any marking); a
/// clean label is a no-op.
pub exec fn witness_check_hyphens_fail_fast() -> (r: bool)
    ensures
        r,
{
    let mut v1: Vec<char> = Vec::new();
    v1.push('-');
    v1.push('a');
    proof { assert(v1@ == seq!['-', 'a']); }
    let mut he1: bool = false;
    let rf1 = check_hyphens(v1.as_mut_slice(), false, true, &mut he1);
    let kept1 = v1[0] == '-' && v1[1] == 'a';
    let mut v2: Vec<char> = Vec::new();
    v2.push('x');
    v2.push('y');
    proof { assert(v2@ == seq!['x', 'y']); }
    let mut he2: bool = false;
    let rf2 = check_hyphens(v2.as_mut_slice(), false, true, &mut he2);
    let kept2 = v2[0] == 'x' && v2[1] == 'y';
    (rf1 && !he1 && kept1 && !rf2 && !he2 && kept2)
}

/// Mark-errors mode on the length-4 label "xn--": the last-position
/// replacement happens first (the upstream check order is load-bearing, see
/// the src's check_hyphens order note), so index 3 becomes U+FFFD and the
/// third+fourth pair test no longer sees a hyphen at index 3.
pub exec fn witness_check_hyphens_xn_double_hyphen_marks_last() -> (r: bool)
    ensures
        r,
{
    let mut v: Vec<char> = Vec::new();
    v.push('x');
    v.push('n');
    v.push('-');
    v.push('-');
    proof { assert(v@ == seq!['x', 'n', '-', '-']); }
    let mut he: bool = false;
    let rf = check_hyphens(v.as_mut_slice(), false, false, &mut he);
    (rf == false
        && he
        && v[0] == 'x'
        && v[1] == 'n'
        && v[2] == '-'
        && v[3] == '\u{FFFD}')
}

/// Mark-errors mode on a length-5 label with the third+fourth hyphen pair:
/// both paired positions are marked (the length >= 5 case of the model).
pub exec fn witness_check_hyphens_third_fourth_marks_pair() -> (r: bool)
    ensures
        r,
{
    let mut v: Vec<char> = Vec::new();
    v.push('x');
    v.push('n');
    v.push('-');
    v.push('-');
    v.push('z');
    proof { assert(v@ == seq!['x', 'n', '-', '-', 'z']); }
    let mut he: bool = false;
    let rf = check_hyphens(v.as_mut_slice(), false, false, &mut he);
    (rf == false
        && he
        && v[0] == 'x'
        && v[1] == 'n'
        && v[2] == '\u{FFFD}'
        && v[3] == '\u{FFFD}'
        && v[4] == 'z')
}

/// With third+fourth hyphens allowed (the CheckFirstLast mode), "a--b" is
/// clean, while a leading hyphen still marks in the mark-errors mode.
pub exec fn witness_check_hyphens_first_last_only() -> (r: bool)
    ensures
        r,
{
    let mut v1: Vec<char> = Vec::new();
    v1.push('a');
    v1.push('-');
    v1.push('-');
    v1.push('b');
    proof { assert(v1@ == seq!['a', '-', '-', 'b']); }
    let mut he1: bool = false;
    let rf1 = check_hyphens(v1.as_mut_slice(), true, false, &mut he1);
    let clean1 = v1[0] == 'a' && v1[1] == '-' && v1[2] == '-' && v1[3] == 'b';
    let mut v2: Vec<char> = Vec::new();
    v2.push('-');
    v2.push('a');
    proof { assert(v2@ == seq!['-', 'a']); }
    let mut he2: bool = false;
    let rf2 = check_hyphens(v2.as_mut_slice(), true, false, &mut he2);
    (rf1 == false && !he1 && clean1 && rf2 == false && he2 && v2[0] == '\u{FFFD}')
}

/* ============ punycode classification (uts46.rs classify_for_punycode) ============ */

/// Three-way classification: ASCII-only labels are Ascii, a label with a
/// non-ASCII char and no U+FFFD is Unicode, and any U+FFFD is Error (the
/// sharp-s example of tests/unit.rs at the classification level).
pub exec fn witness_classify_for_punycode() -> (r: bool)
    ensures
        r,
{
    let mut v1: Vec<char> = Vec::new();
    v1.push('a');
    v1.push('b');
    proof { assert(v1@ == seq!['a', 'b']); }
    let mut v2: Vec<char> = Vec::new();
    v2.push('b');
    v2.push('l');
    v2.push('o');
    v2.push('\u{df}');
    proof { assert(v2@ == seq!['b', 'l', 'o', '\u{df}']); }
    let mut v3: Vec<char> = Vec::new();
    v3.push('a');
    v3.push('\u{FFFD}');
    proof { assert(v3@ == seq!['a', '\u{FFFD}']); }
    let mut v4: Vec<char> = Vec::new();
    v4.push('\u{FFFD}');
    proof { assert(v4@ == seq!['\u{FFFD}']); }
    let s1 = v1.as_slice();
    let s2 = v2.as_slice();
    let s3 = v3.as_slice();
    let s4 = v4.as_slice();
    let c1 = classify_for_punycode(s1);
    let c2 = classify_for_punycode(s2);
    let c3 = classify_for_punycode(s3);
    let c4 = classify_for_punycode(s4);
    proof {
        // c1: all ASCII.
        assert(forall |i: int| 0 <= i < s1.len() ==> (s1[i] as u32) < 0x80) by {
            assert((s1[0] as u32) < 0x80);
            assert((s1[1] as u32) < 0x80);
        }
        assert(c1 == PunycodeClassification::Ascii);
        // c2: the sharp-s makes it non-ASCII; no U+FFFD anywhere.
        assert((s2[3] as u32) == 0xDF);
        assert(!(forall |i: int| 0 <= i < s2.len() ==> (s2[i] as u32) < 0x80));
        assert(s2[0] != '\u{FFFD}');
        assert(s2[1] != '\u{FFFD}');
        assert(s2[2] != '\u{FFFD}');
        assert(s2[3] != '\u{FFFD}');
        assert(has_fffd_from(s2, 0) == has_fffd_from(s2, 1));
        assert(has_fffd_from(s2, 1) == has_fffd_from(s2, 2));
        assert(has_fffd_from(s2, 2) == has_fffd_from(s2, 3));
        assert(has_fffd_from(s2, 3) == has_fffd_from(s2, 4));
        assert(has_fffd_from(s2, 4) == false);
        assert(c2 == PunycodeClassification::Unicode);
        // c3: a U+FFFD at index 1 makes the classification Error.
        assert(s3[0] != '\u{FFFD}');
        assert(has_fffd_from(s3, 0) == has_fffd_from(s3, 1));
        assert(s3[1] == '\u{FFFD}');
        assert(has_fffd_from(s3, 1) == true);
        assert(c3 == PunycodeClassification::Error);
        // c4: a lone U+FFFD.
        assert(s4[0] == '\u{FFFD}');
        assert(has_fffd_from(s4, 0) == true);
        assert(c4 == PunycodeClassification::Error);
    }
    true
}

/// is_ascii over char slices (the ASCII quick test of the sink stage).
pub exec fn witness_is_ascii() -> (r: bool)
    ensures
        r,
{
    let mut v1: Vec<char> = Vec::new();
    v1.push('a');
    v1.push('Z');
    v1.push('0');
    proof { assert(v1@ == seq!['a', 'Z', '0']); }
    let mut v2: Vec<char> = Vec::new();
    v2.push('a');
    v2.push('\u{df}');
    proof { assert(v2@ == seq!['a', '\u{df}']); }
    (is_ascii(v1.as_slice()) && !is_ascii(v2.as_slice()))
}

/* ============ ASCII deny-list application (uts46.rs apply_ascii_deny_list_*) ============ */

/// An uppercase-denying bit (as every AsciiDenyList carries the upper-case
/// mask): a denied 'A' lower-cases to 'a' (code-unit view), an allowed
/// 'a'/'%' passes through, and a denied non-letter becomes U+FFFD. This is
/// the row-level behavior behind AsciiDenyList::URL's deny set.
pub exec fn witness_deny_list_upper_case_rows() -> (r: bool)
    ensures
        r,
{
    let mask_a: u128 = 1u128 << (b'A' as u128);
    let denied_upper = apply_ascii_deny_list_to_potentially_upper_case_ascii(b'A', mask_a);
    let allowed_lower = apply_ascii_deny_list_to_potentially_upper_case_ascii(b'a', mask_a);
    let allowed_punct = apply_ascii_deny_list_to_potentially_upper_case_ascii(b'%', mask_a);
    let mask_colon: u128 = 1u128 << (b':' as u128);
    let denied_colon = apply_ascii_deny_list_to_potentially_upper_case_ascii(b':', mask_colon);
    // Ground bit facts: the inline-literal BV steps eval the masks; the SSA
    // equality carries the value to the locals.
    assert((((1u128 << (b'A' as u128)) >> b'A') & 1) == 1) by (bit_vector);
    assert((((1u128 << (b'A' as u128)) >> b'a') & 1) == 0) by (bit_vector);
    assert((((1u128 << (b'A' as u128)) >> b'%') & 1) == 0) by (bit_vector);
    assert((((1u128 << (b':' as u128)) >> b':') & 1) == 1) by (bit_vector);
    assert(mask_a == 1u128 << (b'A' as u128));
    assert(mask_colon == 1u128 << (b':' as u128));
    (denied_upper == 'a'
        && allowed_lower == 'a'
        && allowed_punct == '%'
        && denied_colon == '\u{FFFD}')
}

/// The lower-cased-Unicode variant: a denied ASCII row becomes U+FFFD, an
/// allowed ASCII row passes, and non-ASCII passes through untouched.
pub exec fn witness_deny_list_lower_cased_unicode_rows() -> (r: bool)
    ensures
        r,
{
    let mask_a: u128 = 1u128 << (b'a' as u128);
    assert((((1u128 << (b'a' as u128)) >> b'a') & 1) == 1) by (bit_vector);
    assert((((1u128 << (b'a' as u128)) >> b'b') & 1) == 0) by (bit_vector);
    let denied = apply_ascii_deny_list_to_lower_cased_unicode('a', mask_a);
    let allowed = apply_ascii_deny_list_to_lower_cased_unicode('b', mask_a);
    let non_ascii = apply_ascii_deny_list_to_lower_cased_unicode('\u{df}', mask_a);
    assert(mask_a == 1u128 << (b'a' as u128));
    (denied == '\u{FFFD}' && allowed == 'b' && non_ascii == '\u{df}')
}

/* ============ AsciiDenyList constructors (uts46.rs AsciiDenyList::{new,empty,std3,url}) ============ */

/// Row-level theorems of the three built-in deny lists: EMPTY still denies
/// the upper-case rows (upstream folds UPPER_CASE_MASK into every list),
/// STD3 denies the underscore (documented) but not the LDH letters, and the
/// URL list additionally denies the deny-string rows and glyphless rows.
/// (The row predicates are asserted alongside so the constructor
/// postconditions' triggers instantiate.)
pub exec fn witness_ascii_deny_list_rows() -> (r: bool)
    ensures
        r,
{
    let e = AsciiDenyList::empty();
    let s = AsciiDenyList::std3();
    let u = AsciiDenyList::url();
    proof {
        assert(upper_case_pred(b'Q'));
        assert(bit_is_set(deny_list_bits(&e), b'Q'));
        assert(!upper_case_pred(b'q'));
        assert(!upper_case_pred(b'_'));
        assert(bit_is_set(deny_list_bits(&e), b'q') == false);
        assert(bit_is_set(deny_list_bits(&e), b'_') == false);
        assert(ldh_pred(b'_'));
        assert(bit_is_set(deny_list_bits(&s), b'_'));
        assert(!ldh_pred(b'a'));
        assert(bit_is_set(deny_list_bits(&s), b'a') == false);
        assert(!ldh_pred(b'0') && bit_is_set(deny_list_bits(&s), b'0') == false);
        assert(url_deny_pred(b'%'));
        assert(bit_is_set(deny_list_bits(&u), b'%'));
        assert(url_deny_pred(b':'));
        assert(bit_is_set(deny_list_bits(&u), b':'));
        assert(glyphless_pred(b' '));
        assert(bit_is_set(deny_list_bits(&u), b' '));
        assert(!url_deny_pred(b'a') && !glyphless_pred(b'a') && !upper_case_pred(b'a'));
        assert(bit_is_set(deny_list_bits(&u), b'a') == false);
    }
    true
}

/* ============================================================
 * Proof helpers (unfolding lemmas over the src's recursive spec
 * models; each just walks the definitional recursion of the src
 * model so concrete-input facts evaluate). Independent one-time
 * helpers, none weakening any obligation.
 * ============================================================ */

/// Definitional step of dns_scan_ok: no-dot bytes keep the label interval.
proof fn unfold_scan_step_no_dot(bytes: &[u8], lim: int, ls: int, cur: int)
    requires
        cur < lim,
        lim <= bytes.len() as int,
        bytes[cur as int] != b'.',
    ensures
        dns_scan_ok(bytes, lim, ls, cur) == dns_scan_ok(bytes, lim, ls, cur + 1),
    decreases lim - cur
{
}

/// Walks dns_scan_ok through a dot-free byte range [from, to).
proof fn unfold_scan_range(bytes: &[u8], lim: int, ls: int, from: int, to: int)
    requires
        from <= to,
        to <= lim,
        lim <= bytes.len() as int,
        forall |p: int| from <= p < to ==> bytes[p as int] != b'.',
    ensures
        dns_scan_ok(bytes, lim, ls, from) == dns_scan_ok(bytes, lim, ls, to),
    decreases to - from
{
    if from < to {
        assert(bytes[from] != b'.');
        unfold_scan_step_no_dot(bytes, lim, ls, from);
        unfold_scan_range(bytes, lim, ls, from + 1, to);
    }
}

/// Definitional step of first_non_fast on a fast byte.
proof fn unfold_first_non_fast_step(bytes: &[u8], j: int)
    requires
        j < bytes.len() as int,
        is_fast_byte(bytes[j as int]),
    ensures
        first_non_fast(bytes, j) == first_non_fast(bytes, j + 1),
    decreases bytes.len() as int - j
{
}

/// Walks first_non_fast through a run of fast bytes [from, to).
proof fn unfold_first_non_fast_chain(bytes: &[u8], from: int, to: int)
    requires
        from <= to,
        to <= bytes.len() as int,
        forall |p: int| from <= p < to ==> is_fast_byte(bytes[p as int]),
    ensures
        first_non_fast(bytes, from) == first_non_fast(bytes, to),
    decreases to - from
{
    if from < to {
        assert(is_fast_byte(bytes[from]));
        unfold_first_non_fast_step(bytes, from);
        unfold_first_non_fast_chain(bytes, from + 1, to);
    }
}

/// The passthrough label-body byte class used by the per-element facts above
/// (a local shorthand of the spec's inline range disjunction -- the same
/// predicate as spec_is_passthrough_ascii_label's tail rule, spelled out so
/// the by-block element facts stay short).
pub open spec fn is_ldh_byte(b: u8) -> bool {
    (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-'
}

} // verus!

fn main() {}
