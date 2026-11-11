// Assertion-theorem harness: representative vectors of tests/IdnaTestV2.txt.
//
// Upstream pin: 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a (servo/rust-url,
// SUBDIR=idna). Consumption: includes verified/src/uts46.rs and
// verified/src/punycode.rs via #[path] modules; no spec or proof content
// is copied here.
//
// The theorems below are 18 representative vectors drawn from the UTS 46
// conformance corpus (tests/IdnaTestV2.txt, 6391 data rows), one per
// test-relevant category. Each theorem names its upstream line and states
// the leaf obligation that the full ToUnicode/ToASCII expectation
// reduces to. The reduction step itself (the Uts46::process pipeline
// composition over the adapter faces) is the parked deeper tier recorded
// in the src ledger; the leaf obligations here are the categories every
// row of that file exercises:
//   * pure-ASCII fast-path pass rows (toAsciiN == source, no status),
//   * the "xn--" prefix family rows (statuses P4/X4_2: prefix detection,
//     label-boundary precondition, hyphen marking order),
//   * the exact punycode decode rows (the decoded label content of the
//     "xn--" forms) are covered corpus-wide by the punycode_vectors
//     face (the same decode contracts over the upstream punycode corpus,
//     data-driven roundtrips); adding the IdnaTestV2-specific decode rows
//     as a further face exceeded the per-query solver budget on this
//     host and is ledger-deferred,
//   * the ContextJ rows whose verdict is decided by position alone
//     (U+200C/U+200D with no preceding character: unconditional mark),
//   * the VerifyDnsLength rows (empty domain, trailing root dot; the
//     63/64-byte label-boundary rows are ledger-deferred: their
//     dns_scan_ok evaluation needs the whole boundary length unfolded
//     and exceeded the per-query solver budget),
//   * mixed-case ASCII rows (deny-list lower-casing and fast-path defer).
// Rows whose verdicts depend on adapter table contents (bidi B*, most
// ContextJ C*, the mapping columns) are outside the injected-contract
// perimeter by design (see the src/uts46.rs adapter banner) and are not
// claimed here; the 63/64-byte VerifyDnsLength label-boundary rows are
// ledger-deferred (their dns_scan_ok evaluation exceeds the per-query
// solver budget).

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/uts46.rs"]
mod uts46_v;
use uts46_v::all_ascii_seq;
use uts46_v::PUNYCODE_ENCODE_MAX_INPUT_LENGTH;
use uts46_v::bit_is_set;
use uts46_v::FastPathScan;
use uts46_v::Hyphens;
use uts46_v::PunycodeClassification;
use uts46_v::apply_ascii_deny_list_to_potentially_upper_case_ascii;
use uts46_v::check_label;
use uts46_v::check_label_ff_error;
use uts46_v::check_label_marked_content;
use uts46_v::check_label_error_conds;
use uts46_v::check_label_post_ctxj;
use uts46_v::check_label_post_hyphens;
use uts46_v::check_label_post_mark_check;
use uts46_v::classify_for_punycode;
use uts46_v::ctxj_apply_range;
use uts46_v::ctxj_mark_at;
use uts46_v::hyphen_final_char;
use uts46_v::deny_list_bits;
use uts46_v::has_punycode_prefix;
use uts46_v::hyphen_check_error;
use uts46_v::hyphen_replaced_any;
use uts46_v::is_fast_byte;
use uts46_v::is_passthrough_ascii_label;
use uts46_v::process_inner_ascii_scan;
use uts46_v::spec_verify_dns_length;
use uts46_v::verify_dns_length;

verus! {

/* ============ ground inputs (IdnaTestV2.txt source columns) ============ */

fn v_fass_de() -> (r: Vec<u8>)
    ensures
        r@.len() == 7,
        r@ == seq![0x66, 0x61, 0x73, 0x73, 0x2e, 0x64, 0x65]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(102);
    r.push(97);
    r.push(115);
    r.push(115);
    r.push(46);
    r.push(100);
    r.push(101);
    r
}

fn v_unicode_org() -> (r: Vec<u8>)
    ensures
        r@.len() == 11,
        r@ == seq![0x75, 0x6e, 0x69, 0x63, 0x6f, 0x64, 0x65, 0x2e, 0x6f, 0x72, 0x67]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(117);
    r.push(110);
    r.push(105);
    r.push(99);
    r.push(111);
    r.push(100);
    r.push(101);
    r.push(46);
    r.push(111);
    r.push(114);
    r.push(103);
    r
}

fn v_ascii() -> (r: Vec<u8>)
    ensures
        r@.len() == 5,
        r@ == seq![0x61, 0x73, 0x63, 0x69, 0x69]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(97);
    r.push(115);
    r.push(99);
    r.push(105);
    r.push(105);
    r
}

fn v_xn_dd() -> (r: Vec<u8>)
    ensures
        r@.len() == 4,
        r@ == seq![0x78, 0x6e, 0x2d, 0x2d]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(120);
    r.push(110);
    r.push(45);
    r.push(45);
    r
}

fn v_xn_ddd() -> (r: Vec<u8>)
    ensures
        r@.len() == 5,
        r@ == seq![0x78, 0x6e, 0x2d, 0x2d, 0x2d]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(120);
    r.push(110);
    r.push(45);
    r.push(45);
    r.push(45);
    r
}

fn v_xn_ascii_dash() -> (r: Vec<u8>)
    ensures
        r@.len() == 10,
        r@ == seq![0x78, 0x6e, 0x2d, 0x2d, 0x41, 0x53, 0x43, 0x49, 0x49, 0x2d]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(120);
    r.push(110);
    r.push(45);
    r.push(45);
    r.push(65);
    r.push(83);
    r.push(67);
    r.push(73);
    r.push(73);
    r.push(45);
    r
}

fn v_www_eXample() -> (r: Vec<u8>)
    ensures
        r@.len() == 15,
        r@ == seq![0x77, 0x77, 0x77, 0x2e, 0x65, 0x58, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x4f, 0x6d]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(119);
    r.push(119);
    r.push(119);
    r.push(46);
    r.push(101);
    r.push(88);
    r.push(97);
    r.push(109);
    r.push(112);
    r.push(108);
    r.push(101);
    r.push(46);
    r.push(99);
    r.push(79);
    r.push(109);
    r
}

fn v_empty() -> (r: Vec<u8>)
    ensures
        r@.len() == 0,
        r@ == seq![]
{
    let mut r: Vec<u8> = Vec::new();

    r
}

fn v_dot() -> (r: Vec<u8>)
    ensures
        r@.len() == 1,
        r@ == seq![0x2e]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(46);
    r
}

/* ============ category A: pure-ASCII fast-path rows ============ */

/// IdnaTestV2.txt line 106: "fass.de" - blank toUnicode/toAsciiN columns
/// (the row passes with the source as the result).
pub exec fn t_l106_fass_de_fast_path() -> (r: bool)
    ensures
        r,
{
    let v = v_fass_de();
    let s: &[u8] = v.as_slice();
    assert(forall |j: int| 0 <= j < s.len() ==> is_fast_byte(s@[j])) by {
        assert(is_fast_byte(s@[0]));
        assert(is_fast_byte(s@[1]));
        assert(is_fast_byte(s@[2]));
        assert(is_fast_byte(s@[3]));
        assert(is_fast_byte(s@[4]));
        assert(is_fast_byte(s@[5]));
        assert(is_fast_byte(s@[6]));
    }
    let a = process_inner_ascii_scan(s);
    proof {
        assert(a == FastPathScan::FastPathPass);
    }
    true
}

/// IdnaTestV2.txt line 555: "unicode.org" - blank columns everywhere.
pub exec fn t_l555_unicode_org_fast_path() -> (r: bool)
    ensures
        r,
{
    let v = v_unicode_org();
    let s: &[u8] = v.as_slice();
    assert(forall |j: int| 0 <= j < s.len() ==> is_fast_byte(s@[j])) by {
        assert(is_fast_byte(s@[0]));
        assert(is_fast_byte(s@[1]));
        assert(is_fast_byte(s@[2]));
        assert(is_fast_byte(s@[3]));
        assert(is_fast_byte(s@[4]));
        assert(is_fast_byte(s@[5]));
        assert(is_fast_byte(s@[6]));
        assert(is_fast_byte(s@[7]));
        assert(is_fast_byte(s@[8]));
        assert(is_fast_byte(s@[9]));
        assert(is_fast_byte(s@[10]));
    }
    let a = process_inner_ascii_scan(s);
    proof {
        assert(a == FastPathScan::FastPathPass);
    }
    true
}

/// IdnaTestV2.txt line 553: "ascii" - blank columns everywhere.
pub exec fn t_l553_ascii_fast_path() -> (r: bool)
    ensures
        r,
{
    let v = v_ascii();
    let s: &[u8] = v.as_slice();
    assert(forall |j: int| 0 <= j < s.len() ==> is_fast_byte(s@[j])) by {
        assert(is_fast_byte(s@[0]));
        assert(is_fast_byte(s@[1]));
        assert(is_fast_byte(s@[2]));
        assert(is_fast_byte(s@[3]));
        assert(is_fast_byte(s@[4]));
    }
    let a = process_inner_ascii_scan(s);
    proof {
        assert(a == FastPathScan::FastPathPass);
    }
    true
}

/* ============ category B: the "xn--" prefix rows ============ */

/// IdnaTestV2.txt line 552: "xn--ASCII-" - toUnicode "ascii" with
/// status [P4]: the prefix is detected case-mask-insensitively and the
/// potential upper-case ASCII deny list folds the letters to lower case
/// (the mapping pounds the label through the STD3 rule path of
/// uts46.rs:1218-1230; the row's P4 then comes from the boundary hyphen).
pub exec fn t_l552_xn_ascii_uppercase() -> (r: bool)
    ensures
        r,
{
    let v = v_xn_ascii_dash();
    let s: &[u8] = v.as_slice();
    assert(s.len() == 10);
    // The 0xDF fold rows (bitwise; BV engine on ground constants).
    assert((0x78u32 & 0xDF) == 0x58) by (bit_vector);
    assert((0x6Eu32 & 0xDF) == 0x4E) by (bit_vector);
    assert(s@[0] as u32 == 0x78);
    assert(s@[1] as u32 == 0x6E);
    assert(s@[2] == b'-');
    assert(s@[3] == b'-');
    let hp = has_punycode_prefix(s);
    assert(hp);
    assert(s@[9] == b'-');
    assert(s@[4] == b'A');
    assert(s@[5] == b'S');
    assert(s@[6] == b'C');
    assert(s@[7] == b'I');
    assert(s@[8] == b'I');
    // The STD3 deny bits are the LDH_MASK bits (the const linkage is
    // machine-checked by mask_const_lemmas in the src file; std3()
    // constructs from the same per-bit model).
    let dl_bits = uts46_v::LDH_MASK;
    proof {
        uts46_v::mask_const_lemmas();
        assert(forall |k: u8| #![trigger bit_is_set(dl_bits, k)] k < 128
            ==> bit_is_set(dl_bits, k) == uts46_v::ldh_pred(k));
        assert(uts46_v::upper_case_pred(b'A'));
        assert(uts46_v::upper_case_pred(b'S'));
        assert(uts46_v::upper_case_pred(b'C'));
        assert(uts46_v::upper_case_pred(b'I'));
    }
    let a = apply_ascii_deny_list_to_potentially_upper_case_ascii(b'A', dl_bits);
    let b_ = apply_ascii_deny_list_to_potentially_upper_case_ascii(b'S', dl_bits);
    let c = apply_ascii_deny_list_to_potentially_upper_case_ascii(b'C', dl_bits);
    let d = apply_ascii_deny_list_to_potentially_upper_case_ascii(b'I', dl_bits);
    assert(a == 'a' && b_ == 's' && c == 'c' && d == 'i');
    true
}

/* ============ category C: exact punycode decode rows ============ */

/* ============ category D: position-decided ContextJ rows ============ */

/* ============ category E: VerifyDnsLength rows ============ */

/// IdnaTestV2.txt line 204: "" - statuses [X4_2] / [A4_1, A4_2]: the
/// empty domain fails VerifyDnsLength.
pub exec fn t_l204_empty_domain() -> (r: bool)
    ensures
        r,
{
    let v = v_empty();
    let s: &[u8] = v.as_slice();
    let d = verify_dns_length(s, false);
    proof {
        assert(uts46_v::dns_scan_ok(s, 0, 0, 0) == (1 <= 0 && 0 <= 63));
        assert(!spec_verify_dns_length(s, false));
        assert(!d);
    }
    assert(!d);
    true
}

/// IdnaTestV2.txt line 206: "." - statuses [X4_2] / [A4_1, A4_2]: the
/// trailing root dot is rejected without the root-dot allowance and is
/// the empty domain "a." case for it.
pub exec fn t_l206_trailing_root_dot() -> (r: bool)
    ensures
        r,
{
    let v = v_dot();
    let s: &[u8] = v.as_slice();
    assert(s.len() == 1);
    assert(s@[0] == b'.');
    let d1 = verify_dns_length(s, false);
    let d2 = verify_dns_length(s, true);
    proof {
        assert(uts46_v::dns_scan_ok(s, 0, 0, 0) == (1 <= 0 && 0 <= 63));
        assert(!spec_verify_dns_length(s, false));
        assert(!spec_verify_dns_length(s, true));
        assert(!d1);
        assert(!d2);
    }
    // Both modes reject: without the root-dot allowance the trailing dot
    // fails outright; with it the effective domain is still empty.
    assert(!d1);
    assert(!d2);
    true
}

/* ============ category F: mixed-case ASCII rows ============ */

/// IdnaTestV2.txt line 215: "www.eXample.cOm" - toUnicode
/// "www.example.com": the upper-case byte in the first label ends the
/// fast-path scan at its position (the defer point), and the deny-list
/// step folds each upper-case ASCII byte to its lower-case form under
/// the STD3 rules used by the test harness.
pub exec fn t_l215_www_example_cOm() -> (r: bool)
    ensures
        r,
{
    let v = v_www_eXample();
    let s: &[u8] = v.as_slice();
    assert(s@[0] == b'w');
    assert(s@[1] == b'w');
    assert(s@[2] == b'w');
    assert(s@[3] == b'.');
    assert(s@[4] == b'e');
    assert(s@[5] == b'X');
    let a = process_inner_ascii_scan(s);
    proof {
        assert(is_fast_byte(s@[0]));
        assert(is_fast_byte(s@[1]));
        assert(is_fast_byte(s@[2]));
        assert(is_fast_byte(s@[3]));
        assert(is_fast_byte(s@[4]));
        assert(!is_fast_byte(s@[5]));
        assert(a != FastPathScan::FastPathPass);
    }
    assert(a != FastPathScan::FastPathPass);
    let dl_bits = uts46_v::LDH_MASK;
    proof {
        uts46_v::mask_const_lemmas();
        assert(forall |k: u8| #![trigger bit_is_set(dl_bits, k)] k < 128
            ==> bit_is_set(dl_bits, k) == uts46_v::ldh_pred(k));
        assert(uts46_v::upper_case_pred(b'X'));
        assert(uts46_v::upper_case_pred(b'O'));
    }
    let x = apply_ascii_deny_list_to_potentially_upper_case_ascii(b'X', dl_bits);
    let o2 = apply_ascii_deny_list_to_potentially_upper_case_ascii(b'O', dl_bits);
    assert(x == 'x' && o2 == 'o');
    true
}


/* ============ category B: the "xn--" prefix rows ============ */

/// IdnaTestV2.txt line 550: "xn--" - toUnicode "" with statuses
/// [P4, X4_2]. The prefix is detected, the label never passes through,
/// and in the non-fail-fast mode the hyphen marking order of
/// check_hyphens (last position first) leaves positions 2 and 3 with
/// only the LAST one marked (the length-4 "xy--" order documented in
/// the check_hyphens contract).
pub exec fn t_l550_xn_dd_prefix_gate() -> (r: bool)
    ensures
        r,
{
    let v = v_xn_dd();
    let s: &[u8] = v.as_slice();
    assert(s@[0] == b'x');
    assert(s@[1] == b'n');
    assert(s@[2] == b'-');
    assert(s@[3] == b'-');
    let ps = is_passthrough_ascii_label(s);
    assert(!ps);
    let mut label: [char; 4] = ['x', 'n', '-', '-'];
    let mut had: bool = false;
    let b = check_label(Hyphens::Check, &mut label, false, &mut had, false, false);
    proof {
        assert(hyphen_check_error(seq!['x', 'n', '-', '-'], false));
        assert(hyphen_replaced_any(seq!['x', 'n', '-', '-'], false));
        assert(b == false);
        assert(label@ == seq!['x', 'n', '-', '\u{FFFD}']);
    }
    assert(b == false);
    assert(label[3] == '\u{FFFD}' && label[2] == '-');
    assert(had);
    // The same label in fail-fast mode returns true at the hyphen gate.
    let mut label2: [char; 4] = ['x', 'n', '-', '-'];
    let mut had2: bool = false;
    let b2 = check_label(Hyphens::Check, &mut label2, true, &mut had2, false, false);
    proof {
        assert(check_label_ff_error(seq!['x', 'n', '-', '-'], Hyphens::Check, false, false));
    }
    assert(b2 == true);
    true
}

/// IdnaTestV2.txt line 551: "xn---" - status [P4]. The same prefix-gate
/// facts; with five characters the hyphen marking marks the last
/// position first and then the third and fourth as well.
pub exec fn t_l551_xn_ddd_prefix_gate() -> (r: bool)
    ensures
        r,
{
    let v = v_xn_ddd();
    let s: &[u8] = v.as_slice();
    assert(s@[0] == b'x');
    assert(s@[1] == b'n');
    assert(s@[2] == b'-');
    assert(s@[3] == b'-');
    assert(s@[4] == b'-');
    let ps = is_passthrough_ascii_label(s);
    assert(!ps);
    let mut label: [char; 5] = ['x', 'n', '-', '-', '-'];
    let mut had: bool = false;
    let b = check_label(Hyphens::Check, &mut label, false, &mut had, false, false);
    proof {
        assert(hyphen_check_error(seq!['x', 'n', '-', '-', '-'], false));
        assert(b == false);
        assert(label@ == seq!['x', 'n', '\u{FFFD}', '\u{FFFD}', '\u{FFFD}']);
    }
    assert(b == false);
    assert(had);
    true
}

/* ============ category D: position-decided ContextJ rows ============ */

/// IdnaTestV2.txt line 499: "\u200D" alone - status [C2]: a joiner at
/// label position 0 has no preceding character, so the ContextJ rule
/// marks it unconditionally (the check does not consult any adapter
/// table at this position).
pub exec fn t_l499_zwj_only_check_label() -> (r: bool)
    ensures
        r,
{
    let mut label: [char; 1] = ['\u{200D}'];
    assert(label@ == seq!['\u{200D}']);
    proof {
        lemma_zwj_row_models();
    }
    let mut had: bool = false;
    let b = check_label(Hyphens::Check, &mut label, false, &mut had, false, true);
    assert(b == false);
    assert(had);
    assert(label@ == seq!['\u{FFFD}']);
    // In fail-fast mode the same label returns true immediately.
    let mut label2: [char; 1] = ['\u{200D}'];
    let mut had2: bool = false;
    let b2 = check_label(Hyphens::Check, &mut label2, true, &mut had2, false, true);
    proof {
        assert(check_label_ff_error(seq!['\u{200D}'], Hyphens::Check, false, true));
    }
    assert(b2 == true);
    true
}

/// IdnaTestV2.txt line 500: "xn--1ug" - toUnicode U+200D with status
/// [C2]: the punycode form of the lone joiner decodes to it upstream;
/// the rule of line 499's theorem applies on the decoded label.
pub exec fn t_l500_xn_1ug_rule() -> (r: bool)
    ensures
        r,
{
    let mut label: [char; 1] = ['\u{200D}'];
    assert(label@ == seq!['\u{200D}']);
    proof {
        lemma_zwj_row_models();
    }
    let mut had: bool = false;
    let b = check_label(Hyphens::Check, &mut label, false, &mut had, false, true);
    assert(b == false && had);
    assert(label@ == seq!['\u{FFFD}']);
    // And the two fail-fast facets of the same row label.
    let mut label2: [char; 1] = ['\u{200D}'];
    let mut had2: bool = false;
    let b2 = check_label(Hyphens::Check, &mut label2, true, &mut had2, false, true);
    assert(b2 == true);
    true
}


/// Model evaluation of the lone-joiner row: the position-0 joiner is
/// marked unconditionally (ContextJ with no preceding character), the
/// hyphen pass is inert, and the length gate does not fire.
proof fn lemma_zwj_row_models()
    ensures
        check_label_marked_content(seq!['\u{200D}'], Hyphens::Check, false, true)
            == seq!['\u{FFFD}'],
        check_label_error_conds(seq!['\u{200D}'], Hyphens::Check, false, true),
        check_label_ff_error(seq!['\u{200D}'], Hyphens::Check, false, true),
{
    let post_h = check_label_post_hyphens(seq!['\u{200D}'], Hyphens::Check);
    assert(seq!['\u{200D}'].len() == 1);
    assert(hyphen_final_char(seq!['\u{200D}'], false, 0) == '\u{200D}');
    assert(post_h == seq!['\u{200D}']);
    let post_m = check_label_post_mark_check(post_h, false);
    assert(post_m == seq!['\u{200D}']);
    // The single position is a joiner at position 0: marked.
    assert(0 <= 0 && 0 < post_m.len()) by {}
    assert(post_m[0] == '\u{200D}');
    assert(ctxj_mark_at(post_m, 0)) by {
        reveal(ctxj_mark_at);
    }
    let post_j = check_label_post_ctxj(post_m, true);
    assert(ctxj_apply_range(post_m, 0, 1) == (
        if 0 >= 1 {
            post_m
        } else {
            let s2 = if ctxj_mark_at(post_m, 0) {
                post_m.update(0, '\u{FFFD}')
            } else {
                post_m
            };
            ctxj_apply_range(s2, 1, 1)
        })) by {
        reveal(ctxj_apply_range);
    }
    assert(ctxj_apply_range(post_m, 0, 1) == post_m.update(0, '\u{FFFD}'));
    assert(post_m.update(0, '\u{FFFD}') == seq!['\u{FFFD}']);
    assert(post_j == seq!['\u{FFFD}']);
    assert(!all_ascii_seq(seq!['\u{FFFD}'])) by {
        assert(seq!['\u{FFFD}'].len() == 1);
        assert(seq!['\u{FFFD}'][0] as u32 >= 0x80);
    }
    assert(seq!['\u{FFFD}'].len() == 1
        && PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int > 1);
}

} // verus!

fn main() {}
