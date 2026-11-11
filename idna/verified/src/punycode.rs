//! idna punycode library-code mirror (single-file verification deliverable)
//!
//! Upstream: code/idna/src/punycode.rs, servo/rust-url, pin 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a
//! (RFC 3492 punycode). This file carries the library-code transcription; harness files
//! under ../harness/ consume it via #[path].
//!
//! Transcription ledger (what is verified, what is external, what is deferred):
//! 1. Scope: both caller paths. The `PunycodeCaller` marker trait
//!    (punycode.rs:71-98, EXTERNAL_CALLER const) is monomorphized away: the
//!    external path carries the EXTERNAL_CALLER = true meaning (overflow
//!    checks in encode, base-ASCII check and 'A'..='Z' digit acceptance in
//!    decode) and is refined to the model per this file's exec entries; the
//!    internal uts46 caller is carried by decode_bytes_internal (u8 form:
//!    lower-cased basic code units through the byte face), decode_char_internal
//!    (char form: the lower-case-only digit table), and
//!    encode_into_chars_internal (the one-shot RFC 3492 section 6.4 length
//!    product; the no-overflow-in-the-unchecked-loop claim is machine-checked
//!    at the model level - the checked channels cannot fire under the one-shot
//!    product, so the unchecked loop performs the same state updates).
//!    Upstream doc (punycode.rs:71-83), the marker trait's contract, reproduced here:
//!      Marker for internal vs. external caller to retain old API behavior
//!      while tweaking behavior for internal callers.
//!      External callers need overflow checks when encoding, but internal
//!      callers don't, because `PUNYCODE_ENCODE_MAX_INPUT_LENGTH` is set
//!      to 1000, and per RFC 3492 section 6.4, the integer variable does
//!      not need to be able to represent values larger than
//!      (char::MAX - INITIAL_N) * (PUNYCODE_ENCODE_MAX_INPUT_LENGTH + 1),
//!      which is less than u32::MAX.
//!      External callers need to handle upper-case ASCII when decoding,
//!      but internal callers don't, because the internal code calls the
//!      decoder only with lower-case inputs.
//! 2. Storage rewrites: `smallvec::SmallVec<[(usize, char); 59]>` (a capacity
//!    optimization) -> `Vec<(usize, char)>`; the `Decoder`/`Decode` structs and the
//!    `Iterator`/`ExactSizeIterator` impls (punycode.rs:159-316) are transcribed as the
//!    phased functions decode_split / decode_build / decode_merge / decode_bytes, which
//!    carry the same internal seams (delimiter split, delta build, position merge).
//! 3. Iterator consumers (`iter().rposition()`, `iter.next()`, encode's
//!    `input.clone().map().filter().min().unwrap()` re-scans) are rewritten as index
//!    loops over `&[u8]` / `&[char]` slices; the `.unwrap()` on the encode min-scan is
//!    proven by a nonempty-scan argument (the obligation stays live, discharged from
//!    the handled-count invariant).
//! 4. `u32::checked_mul` / `checked_add` are transcribed as u64-wide computations
//!    compared against u32::MAX (same accept/reject boundary); the plain additions that
//!    upstream leaves unchecked (`k += BASE`, `delta += 1`, `code_point += 1`, and
//!    `i - previous_i` in decode) keep their plain form so their overflow obligations
//!    stay live at the original sites.
//! 5. The output sink trait `core::fmt::Write` (encode_into) is modeled as `&mut Vec<char>`
//!    pushes, which never fail: `PunycodeEncodeError::Sink` is declared for API fidelity
//!    but is unreachable through the Vec sink; the `From<core::fmt::Error>` impl at
//!    punycode.rs:351-355 is likewise sink-tied and not transcribed.
//! 6. `std::char::from_u32` is the single external std contract, via assume_specification
//!    below (its documented contract: Some iff a valid scalar value).
//! 7. The str/String layer (`decode_to_string`, `decode(&str)`, `encode_str`, and
//!    `encode`'s String return, punycode.rs:42-69 and 318-344) is not re-verified: the
//!    verified cores are decode_bytes (over bytes) and encode_into_chars/encode_chars
//!    (over chars); the String wrappers are the upstream's thin collect/with_capacity
//!    plumbing over these cores.
//! 8. The `huge_encode` inline test (punycode.rs:466-477) is not transcribed: its
//!    property (input-length overflow -> Err with an empty buffer) is subsumed by the
//!    input-length guard and the overflow channels of encode_into_chars below.
//! 9. Deferred: full RFC-3492 delta-semantics output models (which delta string
//!    produces which insertion), and the basics-order content anchoring of encode's
//!    first segment (the basics block is carried with its algebraic invariants: exact
//!    ASCII count and ASCII-membership of the block).

use vstd::arithmetic::div_mod::{lemma_div_by_multiple, lemma_div_is_ordered};
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::lemma_seq_new_len;

verus! {
broadcast use vstd::seq::group_seq_axioms;


// Bootstring parameters for Punycode (punycode.rs:22-28).
// Visibility opened to pub for the pub open spec models below and harness
// (../harness/) consumption; upstream visibility of this module is `pub`.
pub const BASE: u32 = 36;
pub const T_MIN: u32 = 1;
pub const T_MAX: u32 = 26;
pub const SKEW: u32 = 38;
pub const DAMP: u32 = 700;
pub const INITIAL_BIAS: u32 = 72;
pub const INITIAL_N: u32 = 0x80;

/* ============================================================
 * Spec models
 * ============================================================ */

/// Spec model of the u8 digit table (punycode.rs:115-123): the digit value 0..35,
/// or -1 for a non-digit byte (external-caller alphabet: '0'..='9', 'A'..='Z',
/// 'a'..='z').
pub open spec fn digit_val(b: u8) -> int {
    if 0x30 <= b <= 0x39 {
        (b as int) - 0x30 + 26
    } else if 0x41 <= b <= 0x5A {
        (b as int) - 0x41
    } else if 0x61 <= b <= 0x7A {
        (b as int) - 0x61
    } else {
        -1
    }
}

/// Spec model of std::char::from_u32 validity: 0..=0xD7FF or 0xE000..=0x10FFFF
/// (surrogates excluded), the contract documented on std::char::from_u32.
pub open spec fn is_valid_code_point(u: int) -> bool {
    (0 <= u <= 0xD7FF) || (0xE000 <= u <= 0x10FFFF)
}

/// Exponentiation for the loop-bound arguments (weight growth by >= 10 per digit
/// step in decode/encode; delta shrinkage by /35 in adapt).
pub open spec fn powi(b: int, n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        b * powi(b, n - 1)
    }
}

/// Count of elements of s in the half-open interval [lo, hi).
pub open spec fn count_in(s: Seq<int>, lo: int, hi: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let rest = count_in(s.subrange(0, s.len() - 1), lo, hi);
        if lo <= s[s.len() - 1] < hi {
            rest + 1
        } else {
            rest
        }
    }
}

/// The code unit positions of a decode insertion vector (spec view for counting).
pub open spec fn ins_positions(ins: Seq<(usize, char)>) -> Seq<int> {
    Seq::new(ins.len(), |j: int| ins[j].0 as int)
}

/// Index of the insertion placed at output position p, or -1 when none sits there
/// (uniqueness is a consequence of the pairwise-distinctness invariant).
pub open spec fn ins_pos_index(ins: Seq<(usize, char)>, p: int) -> int
    decreases ins.len()
{
    if ins.len() == 0 {
        -1
    } else if (ins[ins.len() - 1].0 as int) == p {
        ins.len() - 1
    } else {
        ins_pos_index(ins.subrange(0, ins.len() - 1), p)
    }
}

/// Spec model of the merged decode output (the `Decode` Next semantics,
/// punycode.rs:283-303): at output position p the insertion placed at p, if any,
/// else the next base code unit. Valid for pairwise-distinct positions within
/// [0, base.len + ins.len): the base index at p is p minus the insertions placed
/// strictly before p.
pub open spec fn merged_char_at(base: Seq<u8>, ins: Seq<(usize, char)>, p: int) -> char {
    let j = ins_pos_index(ins, p);
    if j >= 0 {
        ins[j].1
    } else {
        base[p - count_in(ins_positions(ins), 0, p)] as char
    }
}

/// The digit alphabet of the emittable encoding: 'a'..='z' and '0'..='9'
/// (the value_to_digit table domain).
pub open spec fn is_digit_char(c: char) -> bool {
    ((c as int) >= 0x61 && (c as int) <= 0x7A) || ((c as int) >= 0x30 && (c as int) <= 0x39)
}

/// Number of ASCII chars among the first n (spec model of encode's basic count).
pub open spec fn count_ascii_prefix(s: Seq<char>, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else if (s[n - 1] as int) < 128 {
        1 + count_ascii_prefix(s, n - 1)
    } else {
        count_ascii_prefix(s, n - 1)
    }
}

/// Number of chars among the first n whose code is < cp
/// (spec model of encode's handled count).
pub open spec fn count_lt_code(s: Seq<char>, n: int, cp: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else if (s[n - 1] as int) < cp {
        1 + count_lt_code(s, n - 1, cp)
    } else {
        count_lt_code(s, n - 1, cp)
    }
}

/// Number of chars in positions [lo, n) whose code is < cp
/// (spec model of encode's post-reset unit-increments).
pub open spec fn count_lt_between(s: Seq<char>, lo: int, n: int, cp: int) -> int
    decreases n - lo
{
    if n <= lo {
        0
    } else {
        let rest = count_lt_between(s, lo, n - 1, cp);
        if (s[n - 1] as int) < cp {
            rest + 1
        } else {
            rest
        }
    }
}

/// Number of chars among the first n equal to a given code
/// (the multiplicity handled at one code point in encode's inner scan).
pub open spec fn count_eq_prefix(s: Seq<char>, n: int, cp: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else if (s[n - 1] as int) == cp {
        1 + count_eq_prefix(s, n - 1, cp)
    } else {
        count_eq_prefix(s, n - 1, cp)
    }
}

/// The last '-' (0x2D) index at-or-after m, or -1 when none (spec model of the
/// rposition delimiter split, punycode.rs:173).
pub open spec fn last_delim_from(s: Seq<u8>, m: int) -> int
    decreases s.len() - m
{
    if m >= s.len() {
        -1
    } else {
        let t = last_delim_from(s, m + 1);
        if t >= 0 {
            t
        } else if s[m] == 0x2D {
            m
        } else {
            -1
        }
    }
}

pub open spec fn last_delim(s: Seq<u8>) -> int {
    last_delim_from(s, 0)
}

/* ============================================================
 * RFC-3492 functional models (int-code space)
 *
 * Full-precision functional models of the bootstring encode/decode
 * semantics, over integer code points. They mirror the transcribed
 * exec faces step by step (same accept/reject boundaries at the u32
 * checked channels) so that each exec face can be tied to its model
 * by a refinement clause, and concrete inputs can be evaluated
 * (assert_by_compute / fuel) in the vector harness. Compute-friendly
 * formulation notes: no exists in evaluated bodies, index recursion
 * instead of Seq::subrange recursion, no tuple-field projections in
 * evaluated positions.
 * ============================================================ */

/// The bias-dependent digit threshold (RFC 3492 section 6.1 terrain):
/// k <= bias -> T_MIN; k >= bias + T_MAX -> T_MAX; else k - bias.
pub open spec fn t_for(k: int, bias: int) -> int {
    if k <= bias {
        T_MIN as int
    } else if k >= bias + T_MAX as int {
        T_MAX as int
    } else {
        k - bias
    }
}

/// Digit-symbol code of a value 0..=35 ('a'..'z' then '0'..'9'),
/// the value_to_digit table viewed as codes.
pub open spec fn digit_char(v: int) -> int {
    if v <= 25 {
        v + 0x61
    } else {
        v - 26 + 0x30
    }
}

/// Spec model of the adapt shrink loop (delta / 35 while > 455).
pub open spec fn adapt_loop_model(d: int, k: int) -> int
    decreases d
{
    if d > ((BASE - T_MIN) * T_MAX) as int / 2 {
        adapt_loop_model(d / 35, k + 36)
    } else {
        k + (36 * d) / (d + 38)
    }
}

/// Spec model of adapt (RFC 3492 section 6.1) over unbounded integers,
/// mirroring the transcribed division order of the exec face.
pub open spec fn adapt_model(delta: int, num_points: int, first_time: bool) -> int {
    let d0 = if first_time { delta / 700 } else { delta / 2 };
    let d1 = d0 + d0 / num_points;
    adapt_loop_model(d1, 0)
}

/// Spec model of the delta-digit emission of encode_into's inner scan
/// (the loop plus trailing final digit at punycode.rs:429-445, extracted
/// into encode_digits below): emits the digit symbols of qv under the
/// bootstring threshold schedule, appending to acc.
pub open spec fn emit_digits_model(qv: int, k: int, bias: int, acc: Seq<int>) -> (r: Seq<int>)
    decreases qv
{
    let t = t_for(k, bias);
    if qv >= t {
        emit_digits_model(
            (qv - t) / (36 - t),
            k + 36,
            bias,
            acc.push(digit_char(t + (qv - t) % (36 - t))),
        )
    } else {
        acc.push(digit_char(qv))
    }
}

/// The least code >= n occurring in the input codes at or after j, or -1.
pub open spec fn min_ge(input: Seq<int>, n: int, j: int) -> int
    decreases input.len() - j
{
    if j >= input.len() {
        -1
    } else {
        let rest = min_ge(input, n, j + 1);
        let c = input[j];
        if rest < 0 {
            if c >= n { c } else { -1 }
        } else if c >= n && c < rest {
            c
        } else {
            rest
        }
    }
}

/// min_ge is -1 or the value of an element of the range [j, len) that is
/// at least n.
proof fn lemma_min_ge_lb(input: Seq<int>, n: int, j: int)
    requires
        0 <= j <= input.len(),
    ensures
        min_ge(input, n, j) == -1
            || (exists |w: int| j <= w < input.len()
                && min_ge(input, n, j) == input[w]
                && min_ge(input, n, j) >= n),
    decreases input.len() - j
{
    if j >= input.len() {
        assert(min_ge(input, n, j) == -1) by {
            reveal_with_fuel(min_ge, 1);
        };
    } else {
        lemma_min_ge_lb(input, n, j + 1);
        let rest = min_ge(input, n, j + 1);
        let c = input[j];
        let here = min_ge(input, n, j);
        assert(here == (if rest < 0 {
            (if c >= n { c } else { -1 })
        } else if c >= n && c < rest {
            c
        } else {
            rest
        })) by {
            reveal_with_fuel(min_ge, 1);
        };
        if c < n {
            if rest < 0 {
                assert(here == -1);
            } else {
                assert(here == rest);
            }
        } else if rest < 0 {
            assert(here == c);
            assert(input[j] == c);
            assert(input[j] >= n);
        } else if c < rest {
            assert(here == c);
            assert(input[j] == c);
            assert(input[j] >= n);
        } else {
            assert(here == rest);
        }
    }
}

/// One full encode scan pass (the j2 loop of encode_into_chars):
/// walks the input once, raising delta for codes below cp and, at each
/// occurrence of cp, emitting the pending delta digits, rebiasing, and
/// advancing the handled count. Mirrors the exec accept/reject boundary
/// at the delta+1 checked channel. Returns the pass-end
/// (delta, bias, handled, output-so-far).
pub open spec fn enc_scan_model(
    input: Seq<int>,
    cp: int,
    j: int,
    delta: int,
    bias: int,
    h: int,
    b: int,
    out: Seq<int>,
) -> Option<(int, int, int, Seq<int>)>
    decreases input.len() - j
{
    if j >= input.len() {
        Option::Some((delta, bias, h, out))
    } else {
        let c = input[j];
        if c < cp {
            if delta + 1 > 0xFFFF_FFFF {
                Option::None
            } else {
                enc_scan_model(input, cp, j + 1, delta + 1, bias, h, b, out)
            }
        } else if c == cp {
            let out2 = emit_digits_model(delta, 36, bias, out);
            let bias2 = adapt_model(delta, h + 1, h == b);
            enc_scan_model(input, cp, j + 1, 0, bias2, h + 1, b, out2)
        } else {
            enc_scan_model(input, cp, j + 1, delta, bias, h, b, out)
        }
    }
}

/// The outer encode recursion: one enc_scan_model pass per distinct
/// ascending code point until every input char is handled.
pub open spec fn enc_outer_model(
    input: Seq<int>,
    n: int,
    h: int,
    delta: int,
    bias: int,
    b: int,
    out: Seq<int>,
) -> Option<Seq<int>>
    decreases (0x110001 - n)
{
    decreases_by(enc_outer_dec);
    if h >= input.len() {
        Option::Some(out)
    } else {
        let mg = min_ge(input, n, 0);
        // Scalar-domain clamp: punycode code points are <= 0x10FFFF, so on
        // every real run this equals mg; it keeps the recursion measure
        // well-founded definitionally.
        let m = if mg < 0 || mg >= 0x110000 { -1 } else { mg };
        if m < 0 {
            Option::None
        } else {
            let d = delta + (m - n) * (h + 1);
            if d > 0xFFFF_FFFF {
                Option::None
            } else {
                match enc_scan_model(input, m, 0, d, bias, h, b, out) {
                    Option::None => Option::None,
                    Option::Some((dend, biasend, hend, outend)) => {
                        let d2 = dend + 1;
                        if d2 > 0xFFFF_FFFF {
                            Option::None
                        } else {
                            enc_outer_model(input, m + 1, hend, d2, biasend, b, outend)
                        }
                    }
                }
            }
        }
    }
}

/// With a witnessed occurrence and a lower bound over all qualifying
/// codes, min_ge returns exactly that code.
proof fn lemma_min_ge_value(input: Seq<int>, n: int, mv: int, widx: int)
    requires
        0 <= widx < input.len(),
        0 <= n,
        input[widx] == mv,
        mv >= n,
        forall |k: int| #![trigger input[k]] 0 <= k < input.len()
            ==> (!(n <= input[k] < mv)),
    ensures
        min_ge(input, n, 0) == mv,
    decreases input.len() - widx
{
    lemma_min_ge_value_from(input, n, mv, widx, 0);
}

proof fn lemma_min_ge_value_from(
    input: Seq<int>,
    n: int,
    mv: int,
    widx: int,
    j: int,
)
    requires
        0 <= j <= widx,
        0 <= n,
        widx < input.len(),
        input[widx] == mv,
        mv >= n,
        forall |k: int| #![trigger input[k]] j <= k < input.len()
            ==> (!(n <= input[k] < mv)),
    ensures
        min_ge(input, n, j) == mv,
    decreases widx - j
{
    if j == widx {
        // all qualifying entries at or after j are at least mv, and mv itself
        // occurs here
        lemma_min_ge_last(input, n, mv, j);
    } else {
        let c = input[j];
        let rest = min_ge(input, n, j + 1);
        let here = min_ge(input, n, j);
        assert(here == (if rest < 0 {
            (if c >= n { c } else { -1 })
        } else if c >= n && c < rest {
            c
        } else {
            rest
        })) by {
            reveal_with_fuel(min_ge, 1);
        };
        // the witness qualifies, so the tail minimum is a real value
        assert(input[widx] >= n);
        assert(mv >= n);
        assert(n >= 0);
        assert(widx >= j + 1);
        lemma_min_ge_nonneg(input, n, j + 1);
        assert(rest >= 0);
        assert forall |k: int| #![trigger input[k]]
            j + 1 <= k < input.len()
            implies (input[k] >= n ==> input[k] >= mv) by {
            assert(!(n <= input[k] < mv));
        };
        lemma_min_ge_ge(input, n, j + 1, mv);
        if c >= n {
            assert(!(n <= c < mv));
            assert(c >= mv);
            if c < rest {
                assert(here == c);
            } else {
                assert(here == rest);
            }
        } else {
            assert(here == rest);
        }
        assert(rest == mv) by {
            lemma_min_ge_value_from(input, n, mv, widx, j + 1);
        };
        assert(here == mv);
    }
}

proof fn lemma_min_ge_last(input: Seq<int>, n: int, mv: int, j: int)
    requires
        0 <= j < input.len(),
        0 <= n,
        input[j] == mv,
        mv >= n,
        forall |k: int| #![trigger input[k]] j <= k < input.len()
            ==> (!(n <= input[k] < mv)),
    ensures
        min_ge(input, n, j) == mv,
    decreases input.len() - j
{
    let rest = min_ge(input, n, j + 1);
    let c = input[j];
    let here = min_ge(input, n, j);
    assert(here == (if rest < 0 {
        (if c >= n { c } else { -1 })
    } else if c >= n && c < rest {
        c
    } else {
        rest
    })) by {
        reveal_with_fuel(min_ge, 1);
    };
    if rest < 0 {
        assert(c >= n);
        assert(here == c);
        assert(here == mv);
    } else {
        assert(c >= n);
        assert forall |k: int| #![trigger input[k]]
            j + 1 <= k < input.len()
            implies (input[k] >= n ==> input[k] >= mv) by {
            assert(!(n <= input[k] < mv));
        };
        lemma_min_ge_ge(input, n, j + 1, mv);
        assert(rest >= mv);
        assert(here == mv);
    }
}

/// With at least one qualifying entry, the tail minimum is a real value.
proof fn lemma_min_ge_nonneg(input: Seq<int>, n: int, j: int)
    requires
        0 <= j <= input.len(),
        0 <= n,
        exists |w: int| j <= w < input.len() && input[w] >= n,
    ensures
        min_ge(input, n, j) >= 0,
    decreases input.len() - j
{
    if j < input.len() {
        let c = input[j];
        let rest = min_ge(input, n, j + 1);
        let here = min_ge(input, n, j);
        assert(here == (if rest < 0 {
            (if c >= n { c } else { -1 })
        } else if c >= n && c < rest {
            c
        } else {
            rest
        })) by {
            reveal_with_fuel(min_ge, 1);
        };
        if c >= n {
        } else {
            assert(exists |w: int| j + 1 <= w < input.len() && input[w] >= n) by {
                let w: int = choose |w: int| j <= w < input.len() && input[w] >= n;
                assert(w >= j + 1);
            };
            lemma_min_ge_nonneg(input, n, j + 1);
        }
    }
}

/// min_ge, when not -1, is at least lo over the qualifying tail.
proof fn lemma_min_ge_ge(input: Seq<int>, n: int, j: int, lo: int)
    requires
        0 <= j <= input.len(),
        forall |k: int| #![trigger input[k]] j <= k < input.len()
            ==> (input[k] >= n ==> input[k] >= lo),
    ensures
        min_ge(input, n, j) != -1 ==> min_ge(input, n, j) >= lo,
    decreases input.len() - j
{
    if j < input.len() {
        lemma_min_ge_ge(input, n, j + 1, lo);
        let rest = min_ge(input, n, j + 1);
        let c = input[j];
        let here = min_ge(input, n, j);
        assert(here == (if rest < 0 {
            (if c >= n { c } else { -1 })
        } else if c >= n && c < rest {
            c
        } else {
            rest
        })) by {
            reveal_with_fuel(min_ge, 1);
        };
        if c >= n {
            assert(c >= lo);
        }
    }
}

/// The char-view basic total equals the code-view suffix count at 0
/// (the count_ascii_prefix model counts the bottom-up prefix, the codes
/// model counts the top-down suffix; both total the ASCII count).
proof fn lemma_count_basic_total(s: Seq<char>, j: int)
    requires
        0 <= j <= s.len(),
    ensures
        count_basic_codes(codes_of(s), j) + count_ascii_prefix(s, j)
            == count_ascii_prefix(s, s.len() as int),
    decreases s.len() as int - j
{
    lemma_codes_of_len(s);
    assert(codes_of(s).len() == s.len());
    if j < s.len() {
        lemma_count_basic_total(s, j + 1);
        codeofs_len_left(s, j);
        lemma_codes_of_index(s, j);
        assert(codes_of(s)[j] == s[j] as int);
        assert(count_basic_codes(codes_of(s), j)
            == (if codes_of(s)[j] < 128 { 1int } else { 0int })
                + count_basic_codes(codes_of(s), j + 1)) by {
            reveal_with_fuel(count_basic_codes, 1);
            assert(j < codes_of(s).len());
        };
        assert(count_ascii_prefix(s, j + 1)
            == (if (s[j] as int) < 128 {
                1 + count_ascii_prefix(s, j)
            } else {
                count_ascii_prefix(s, j)
            })) by {
            reveal_with_fuel(count_ascii_prefix, 1);
            assert(s[(j + 1) - 1] == s[j]);
        };
    }
}

/// codes_of preserves length (helper used by the split-count induction).
proof fn codeofs_len_left(s: Seq<char>, j: int)
    requires
        0 <= j < s.len(),
    ensures
        codes_of(s).len() == s.len(),
        0 <= j < codes_of(s).len(),
{
    lemma_codes_of_len(s);
}

/// gen_int_model's returned position stays inside the unread window.
proof fn lemma_gen_int_pos(input: Seq<u8>, pos: int, byte: u8, i: int, weight: int, k: int, bias: int)
    requires
        0 <= pos <= input.len(),
    ensures
        gen_int_model(input, pos, byte, i, weight, k, bias) matches Option::Some((_, gp))
            ==> gp >= pos,
        gen_int_model(input, pos, byte, i, weight, k, bias) matches Option::Some((_, gp))
            ==> gp <= input.len(),
    decreases input.len() - pos
{
    reveal_with_fuel(gen_int_model, 1);
    let dv = digit_val(byte);
    if 0 <= dv
        && dv * weight <= 0xFFFF_FFFF
        && i + dv * weight <= 0xFFFF_FFFF
    {
        let t = t_for(k, bias);
        if dv >= t
            && weight * (BASE as int - t) <= 0xFFFF_FFFF
            && pos < input.len()
        {
            lemma_gen_int_pos(input, pos + 1, input[pos], i + dv * weight,
                weight * (BASE as int - t), k + BASE as int, bias);
        }
    }
}

#[verifier::decreases_by]
proof fn enc_outer_dec(
    input: Seq<int>,
    n: int,
    h: int,
    delta: int,
    bias: int,
    b: int,
    out: Seq<int>,
) {
    lemma_min_ge_lb(input, n, 0);
    let mg = min_ge(input, n, 0);
    let m = if mg < 0 || mg >= 0x110000 { -1 } else { mg };
    if m >= 0 {
        assert(m >= n);
    }
}

/// Char sequence -> code-point sequence view (the int-code models read
/// input through this view; elementwise facts are established by the
/// codes_of lemmas below, kept usable at every needed index).
pub open spec fn codes_of(s: Seq<char>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        codes_of(s.subrange(0, (s.len() - 1) as int)).push(s[s.len() as int - 1] as int)
    }
}

/// codes_of is elementwise: pointwise index correspondence.
pub proof fn lemma_codes_of_index(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        codes_of(s)[i] == s[i] as int,
    decreases s.len()
{
    vstd::seq::lemma_seq_subrange_len(s, 0, (s.len() - 1) as int);
    let sub0 = s.subrange(0, (s.len() - 1) as int);
    lemma_codes_of_len(sub0);
    if i == s.len() as int - 1 {
        let sub = s.subrange(0, (s.len() - 1) as int);
        assert(codes_of(s) == codes_of(sub).push(s[s.len() as int - 1] as int));
        lemma_codes_of_len(sub);
        vstd::seq::lemma_seq_push_index_same(
            codes_of(sub),
            s[s.len() as int - 1] as int,
            sub.len() as int,
        );
        assert(codes_of(sub).push(s[s.len() as int - 1] as int)[i]
            == s[s.len() as int - 1] as int);
    } else {
        let sub = s.subrange(0, (s.len() - 1) as int);
        assert(codes_of(s) == codes_of(sub).push(s[s.len() as int - 1] as int));
        lemma_codes_of_len(sub);
        vstd::seq::lemma_seq_push_index_different(
            codes_of(sub),
            s[s.len() as int - 1] as int,
            i,
        );
        assert(codes_of(s)[i] == codes_of(sub)[i]);
        vstd::seq::lemma_seq_subrange_index(s, 0, (s.len() - 1) as int, i);
        lemma_codes_of_index(sub, i);
        assert(sub[i] == s[i]);
    }
}

/// codes_of preserves length.
pub proof fn lemma_codes_of_len(s: Seq<char>)
    ensures
        codes_of(s).len() == s.len(),
    decreases s.len()
{
    if s.len() > 0 {
        let sub = s.subrange(0, (s.len() - 1) as int);
        vstd::seq::lemma_seq_subrange_len(s, 0, (s.len() - 1) as int);
        lemma_codes_of_len(sub);
    }
}

/// codes_of passes through pushes (value-wise).
proof fn lemma_codes_of_push(s: Seq<char>, c: char)
    ensures
        codes_of(s.push(c)) == codes_of(s).push(c as int),
{
    reveal_with_fuel(codes_of, 1);
    let n = s.len();
    let sp = s.push(c);
    let sub = sp.subrange(0, n as int);
    assert(sp.len() == n + 1);
    assert(codes_of(sp) == codes_of(sub).push(c as int));
    assert(sub.len() == n) by {
        vstd::seq::lemma_seq_subrange_len(sp, 0, n as int);
    }
    assert forall |i: int| 0 <= i < n as int implies (sub[i] == s[i]) by {
        vstd::seq::lemma_seq_subrange_index(sp, 0, n as int, i);
        vstd::seq::lemma_seq_push_index_different(s, c, i);
        assert(sub[i] == sp[i]);
        assert(sp[i] == s[i]);
    }
    vstd::seq::lemma_seq_ext_equal(sub, s);
    assert(codes_of(sub) == codes_of(s));
    assert(codes_of(sp) == codes_of(s).push(c as int));
}

/// Number of ASCII codes among the first j entries.
pub open spec fn count_basic_codes(input: Seq<int>, j: int) -> int
    decreases input.len() - j
{
    if j >= input.len() {
        0
    } else {
        (if input[j] < 128 { 1int } else { 0int }) + count_basic_codes(input, j + 1)
    }
}

/// The basic-code-point accumulation of the encode head loop: the ASCII
/// codes are copied to the output in input order.
pub open spec fn ascii_prefix_model(input: Seq<int>, j: int, acc: Seq<int>) -> (r: Seq<int>)
    decreases input.len() - j
{
    if j >= input.len() {
        acc
    } else {
        let acc2 = if input[j] < 128 { acc.push(input[j]) } else { acc };
        ascii_prefix_model(input, j + 1, acc2)
    }
}

/// Full encode model over code-point codes: basics, delimiter, then the
/// extended part (one delta group per remaining distinct code point).
/// Carries upstream encode's input-length guard (encode, punycode.rs:336).
pub open spec fn encode_model_codes(input: Seq<int>) -> (r: Option<Seq<int>>) {
    if input.len() as int > 0xFFFF_FFFF {
        Option::None
    } else {
        let b = count_basic_codes(input, 0);
        let out0 = ascii_prefix_model(input, 0, Seq::empty());
        let out1 = if b > 0 { out0.push(0x2D) } else { out0 };
        enc_outer_model(input, INITIAL_N as int, b, 0, INITIAL_BIAS as int, b, out1)
    }
}

/// Full encode model over a char input (the str/char layer views through
/// codes_of; ledger item 7 wrappers stay unverified).
pub open spec fn encode_model(input: Seq<char>) -> (r: Option<Seq<int>>) {
    encode_model_codes(codes_of(input))
}

/// The anchored full-encode model: encode_model with the emission
/// accumulated over an existing buffer anchor (its per-index refinement
/// ties encode_into_chars to the appended content; the empty anchor is
/// encode_model itself).
pub open spec fn encode_full_model(input: Seq<char>, anchor: Seq<char>) -> (r: Option<Seq<int>>) {
    let cs = codes_of(input);
    let b = count_basic_codes(cs, 0);
    let out0 = ascii_prefix_model(cs, 0, codes_of(anchor));
    let out1 = (if b > 0 { out0.push(0x2D) } else { out0 });
    enc_outer_model(
        cs,
        INITIAL_N as int,
        b,
        0,
        INITIAL_BIAS as int,
        b,
        out1,
    )
}

/// The empty-anchored model is encode_model.
proof fn lemma_encode_model_empty(input: Seq<char>)
    requires
        input.len() as int <= 0xFFFF_FFFF,
    ensures
        encode_model(input) == encode_full_model(input, Seq::empty()),
{
    reveal(encode_model);
    reveal(encode_model_codes);
    reveal(encode_full_model);
    lemma_codes_of_len(input);
    assert(input.len() as int <= 0xFFFF_FFFF);
    assert((codes_of(input)).len() == input.len());
    assert(!(((codes_of(input)).len() as int) > 0xFFFF_FFFF));
    assert(codes_of(Seq::empty()) == Seq::empty()) by {
        reveal_with_fuel(codes_of, 1);
    };
}

/* ============================================================
 * RFC-3492 decode models (byte in, code out)
 * ============================================================ */

/// Spec model of the generalized-integer inner scan of Decoder::decode
/// (RFC 3492 section 3.3, the inner loop of decode_build below):
/// consumes `byte` (the just-fetched digit), accumulating weight-scaled
/// digit values into i, and returns (i, next-unread-index) on the
/// threshold digit, recursing on the next byte otherwise. The None
/// conditions mirror the transcribed checked channels exactly.
pub open spec fn gen_int_model(
    input: Seq<u8>,
    pos: int,
    byte: u8,
    i: int,
    weight: int,
    k: int,
    bias: int,
) -> Option<(int, int)>
    decreases input.len() - pos
{
    let dv = digit_val(byte);
    if dv < 0 {
        Option::None
    } else if dv * weight > 0xFFFF_FFFF {
        Option::None
    } else if i + dv * weight > 0xFFFF_FFFF {
        Option::None
    } else {
        let t = t_for(k, bias);
        if dv < t {
            Option::Some((i + dv * weight, pos))
        } else {
            let w2 = weight * (36 - t);
            if w2 > 0xFFFF_FFFF {
                Option::None
            } else if pos >= input.len() {
                Option::None
            } else {
                gen_int_model(input, pos + 1, input[pos], i + dv * weight, w2, k + 36, bias)
            }
        }
    }
}

/// Insertion code placed exactly at output position p, or -1 when none
/// (index recursion, last-first, aligned with ins_pos_index).
pub open spec fn ins_at_end(posns: Seq<int>, codes: Seq<int>, hi: int, p: int) -> int
    decreases hi
{
    if hi <= 0 {
        -1
    } else if posns[hi - 1] == p {
        codes[hi - 1]
    } else {
        ins_at_end(posns, codes, hi - 1, p)
    }
}

/// Number of insertions among the first hi placed strictly below p.
pub open spec fn ins_below(posns: Seq<int>, hi: int, p: int) -> int
    decreases hi
{
    if hi <= 0 {
        0
    } else {
        (if posns[hi - 1] < p { 1int } else { 0int }) + ins_below(posns, hi - 1, p)
    }
}

/// The merged decode output code at position p: the insertion placed at
/// p, if any, else the next base code unit (parallel-view model).
pub open spec fn merged_codes_at(base: Seq<u8>, posns: Seq<int>, codes: Seq<int>, p: int) -> int {
    let c = ins_at_end(posns, codes, posns.len() as int, p);
    if c >= 0 {
        c
    } else {
        base[p - ins_below(posns, posns.len() as int, p)] as int
    }
}

/// Full merged output, front-to-back explicit recursion.
pub open spec fn merge_all_codes(
    base: Seq<u8>,
    posns: Seq<int>,
    codes: Seq<int>,
    p: int,
    acc: Seq<int>,
) -> (r: Seq<int>)
    decreases (base.len() as int + posns.len() as int) - p
{
    let total = base.len() as int + posns.len() as int;
    if p >= total {
        acc
    } else {
        let acc2 = acc.push(merged_codes_at(base, posns, codes, p));
        merge_all_codes(base, posns, codes, p + 1, acc2)
    }
}

/// The position-bump of one decode step over the position view (the
/// `if *idx >= i as usize { *idx += 1 }` pass of decode_build).
pub open spec fn bump_positions_model(posns: Seq<int>, iv: int, k: int) -> (r: Seq<int>)
    decreases posns.len() as int - k
{
    if k >= posns.len() as int {
        posns
    } else {
        let posns2 = posns.update(k, (if posns[k] >= iv { posns[k] + 1 } else { posns[k] }));
        bump_positions_model(posns2, iv, k + 1)
    }
}

/// Position view of the insertion vector (recursive: elementwise facts
/// are established by the ins_posns lemmas below).
pub open spec fn ins_posns(ins: Seq<(usize, char)>) -> Seq<int>
    decreases ins.len()
{
    if ins.len() == 0 {
        Seq::empty()
    } else {
        ins_posns(ins.subrange(0, (ins.len() - 1) as int)).push(
            ins[ins.len() as int - 1].0 as int,
        )
    }
}

/// Code view of the insertion vector.
pub open spec fn ins_codes(ins: Seq<(usize, char)>) -> Seq<int>
    decreases ins.len()
{
    if ins.len() == 0 {
        Seq::empty()
    } else {
        ins_codes(ins.subrange(0, (ins.len() - 1) as int)).push(
            ins[ins.len() as int - 1].1 as int,
        )
    }
}

/// ins_posns preserves length.
proof fn lemma_ins_posns_len(ins: Seq<(usize, char)>)
    ensures
        ins_posns(ins).len() == ins.len(),
    decreases ins.len()
{
    if ins.len() > 0 {
        let sub = ins.subrange(0, (ins.len() - 1) as int);
        vstd::seq::lemma_seq_subrange_len(ins, 0, (ins.len() - 1) as int);
        reveal_with_fuel(ins_posns, 1);
        lemma_ins_posns_len(sub);
    }
}

/// ins_posns is elementwise.
proof fn lemma_ins_posns_index(ins: Seq<(usize, char)>, q: int)
    requires
        0 <= q < ins.len(),
    ensures
        ins_posns(ins)[q] == ins[q].0 as int,
        ins_posns(ins).len() == ins.len(),
    decreases ins.len()
{
    lemma_ins_posns_len(ins);
    let sub = ins.subrange(0, (ins.len() - 1) as int);
    vstd::seq::lemma_seq_subrange_len(ins, 0, (ins.len() - 1) as int);
    lemma_ins_posns_len(sub);
    reveal_with_fuel(ins_posns, 1);
    assert(ins_posns(ins) == ins_posns(sub)
        .push(ins[ins.len() as int - 1].0 as int));
    if q == ins.len() as int - 1 {
        vstd::seq::lemma_seq_push_index_same(
            ins_posns(sub),
            ins[ins.len() as int - 1].0 as int,
            sub.len() as int,
        );
    } else {
        vstd::seq::lemma_seq_push_index_different(
            ins_posns(sub),
            ins[ins.len() as int - 1].0 as int,
            q,
        );
        lemma_ins_posns_index(sub, q);
        vstd::seq::lemma_seq_subrange_index(ins, 0, (ins.len() - 1) as int, q);
    }
}

/// ins_codes preserves length.
proof fn lemma_ins_codes_len(ins: Seq<(usize, char)>)
    ensures
        ins_codes(ins).len() == ins.len(),
    decreases ins.len()
{
    if ins.len() > 0 {
        let sub = ins.subrange(0, (ins.len() - 1) as int);
        vstd::seq::lemma_seq_subrange_len(ins, 0, (ins.len() - 1) as int);
        reveal_with_fuel(ins_codes, 1);
        lemma_ins_codes_len(sub);
    }
}

/// ins_codes is elementwise.
proof fn lemma_ins_codes_index(ins: Seq<(usize, char)>, q: int)
    requires
        0 <= q < ins.len(),
    ensures
        ins_codes(ins)[q] == ins[q].1 as int,
        ins_codes(ins).len() == ins.len(),
    decreases ins.len()
{
    lemma_ins_codes_len(ins);
    let sub = ins.subrange(0, (ins.len() - 1) as int);
    vstd::seq::lemma_seq_subrange_len(ins, 0, (ins.len() - 1) as int);
    lemma_ins_codes_len(sub);
    reveal_with_fuel(ins_codes, 1);
    assert(ins_codes(ins) == ins_codes(sub)
        .push(ins[ins.len() as int - 1].1 as int));
    if q == ins.len() as int - 1 {
        vstd::seq::lemma_seq_push_index_same(
            ins_codes(sub),
            ins[ins.len() as int - 1].1 as int,
            sub.len() as int,
        );
    } else {
        vstd::seq::lemma_seq_push_index_different(
            ins_codes(sub),
            ins[ins.len() as int - 1].1 as int,
            q,
        );
        lemma_ins_codes_index(sub, q);
        vstd::seq::lemma_seq_subrange_index(ins, 0, (ins.len() - 1) as int, q);
    }
}

/// The bump pass over the position view, characterized pointwise
/// (positions below k already final, positions at or above k still
/// pending one conditional increment).
proof fn lemma_bump_view(X: Seq<int>, iv: int, k: int)
    requires
        0 <= k <= X.len() as int,
    ensures
        (bump_positions_model(X, iv, k)).len() == X.len(),
        forall |q: int| 0 <= q < (X.len() as int) ==>
            ((bump_positions_model(X, iv, k))[q]
                == (if q < k {
                    X[q]
                } else if X[q] >= iv {
                    X[q] + 1
                } else {
                    X[q]
                })),
    decreases (X.len() as int) - k
{
    if k == X.len() as int {
        assert(bump_positions_model(X, iv, k) == X) by {
            reveal_with_fuel(bump_positions_model, 1);
        };
    } else {
        let tr = (if X[k] >= iv { X[k] + 1 } else { X[k] });
        let X1 = X.update(k, tr);
        reveal_with_fuel(bump_positions_model, 1);
        assert(bump_positions_model(X, iv, k) == bump_positions_model(X1, iv, k + 1));
        lemma_bump_view(X1, iv, k + 1);
        assert forall |q: int| 0 <= q < X.len() as int implies
            ((bump_positions_model(X, iv, k))[q]
                == (if q < k {
                    X[q]
                } else if X[q] >= iv {
                    X[q] + 1
                } else {
                    X[q]
                })) by {
            vstd::seq::lemma_seq_update_len(X, k, tr);
            assert(X1.len() == X.len());
            if q == k {
                vstd::seq::lemma_seq_update_same(X, k, tr);
            } else {
                vstd::seq::lemma_seq_update_different(X, q, k, tr);
            }
        };
    }
}

/// The exec bump pass (positions at or above iv shift by one, codes stay
/// put) is exactly the position-view image of the model bump over the same
/// pre-state, with the code view untouched.
proof fn lemma_views_bump_bridge(
    pre: Seq<(usize, char)>,
    post: Seq<(usize, char)>,
    iv: int,
)
    requires
        pre.len() == post.len(),
        forall |q: int| 0 <= q < pre.len()
            ==> (if (pre[q].0 as int) >= iv {
                ((post[q].0 as int) == (pre[q].0 as int + 1))
            } else {
                (post[q] == pre[q])
            }),
        forall |q: int| 0 <= q < pre.len()
            ==> ((post[q].1 as int) == (pre[q].1 as int)),
    ensures
        ins_posns(post) == bump_positions_model(ins_posns(pre), iv, 0),
        ins_codes(post) == ins_codes(pre),
{
    lemma_ins_posns_len(pre);
    lemma_ins_posns_len(post);
    lemma_bump_view(ins_posns(pre), iv, 0);
    assert forall |q: int| 0 <= q < pre.len()
        implies (ins_posns(post)[q]
            == bump_positions_model(ins_posns(pre), iv, 0)[q]) by {
        lemma_ins_posns_index(post, q);
        lemma_ins_posns_index(pre, q);
        if (pre[q].0 as int) >= iv {
            assert(ins_posns(post)[q] == post[q].0 as int);
            assert(ins_posns(pre)[q] == pre[q].0 as int);
            assert(bump_positions_model(ins_posns(pre), iv, 0)[q]
                == ins_posns(pre)[q] + 1);
        } else {
            assert(post[q] == pre[q]);
            assert(ins_posns(post)[q] == pre[q].0 as int);
            assert(bump_positions_model(ins_posns(pre), iv, 0)[q]
                == ins_posns(pre)[q]);
        }
    };
    vstd::seq::lemma_seq_ext_equal(
        ins_posns(post),
        bump_positions_model(ins_posns(pre), iv, 0),
    );
    // the code view is elementwise constant across the bump
    lemma_ins_codes_len(pre);
    lemma_ins_codes_len(post);
    assert(ins_codes(post).len() == post.len());
    assert(ins_codes(post).len() == ins_codes(pre).len());
    assert forall |q: int| 0 <= q < pre.len()
        implies (ins_codes(post)[q] == ins_codes(pre)[q]) by {
        lemma_ins_codes_index(post, q);
        lemma_ins_codes_index(pre, q);
    };
    vstd::seq::lemma_seq_ext_equal(ins_codes(post), ins_codes(pre));
}

/// ins_posns passes through pushes.
proof fn lemma_ins_posns_push(ins: Seq<(usize, char)>, pc: (usize, char))
    ensures
        ins_posns(ins.push(pc)) == ins_posns(ins).push(pc.0 as int),
{
    reveal_with_fuel(ins_posns, 1);
    let n = ins.len();
    let sp = ins.push(pc);
    let sub = sp.subrange(0, n as int);
    vstd::seq::lemma_seq_subrange_len(sp, 0, n as int);
    assert(sub.len() == n);
    assert forall |i: int| 0 <= i < n as int implies (sub[i] == ins[i]) by {
        vstd::seq::lemma_seq_subrange_index(sp, 0, n as int, i);
        vstd::seq::lemma_seq_push_index_different(ins, pc, i);
    }
    vstd::seq::lemma_seq_ext_equal(sub, ins);
    assert(ins_posns(sp) == ins_posns(sub).push(pc.0 as int));
    assert(ins_posns(sub) == ins_posns(ins));
}

/// ins_codes passes through pushes.
proof fn lemma_ins_codes_push(ins: Seq<(usize, char)>, pc: (usize, char))
    ensures
        ins_codes(ins.push(pc)) == ins_codes(ins).push(pc.1 as int),
{
    reveal_with_fuel(ins_codes, 1);
    let n = ins.len();
    let sp = ins.push(pc);
    let sub = sp.subrange(0, n as int);
    vstd::seq::lemma_seq_subrange_len(sp, 0, n as int);
    assert(sub.len() == n);
    assert forall |i: int| 0 <= i < n as int implies (sub[i] == ins[i]) by {
        vstd::seq::lemma_seq_subrange_index(sp, 0, n as int, i);
        vstd::seq::lemma_seq_push_index_different(ins, pc, i);
    }
    vstd::seq::lemma_seq_ext_equal(sub, ins);
    assert(ins_codes(sp) == ins_codes(sub).push(pc.1 as int));
    assert(ins_codes(sub) == ins_codes(ins));
}

/// Spec model of the decode insertion build (the outer loop of
/// decode_build): decodes one generalized-integer delta per step into a
/// (position, code) insertion, bumping earlier positions. Parallel
/// position/code views (the tuple seq of the exec carries the same data).
pub open spec fn build_model(
    input: Seq<u8>,
    pos: int,
    length: int,
    cp: int,
    bias: int,
    i: int,
    posns: Seq<int>,
    codes: Seq<int>,
) -> Option<(Seq<int>, Seq<int>)>
    decreases input.len() - pos
{
    if pos >= input.len() {
        Option::Some((posns, codes))
    } else {
        match gen_int_model(input, pos + 1, input[pos], i, 1, BASE as int, bias) {
            Option::None => Option::None,
            Option::Some((gi, gp_raw)) => {
                // Positional clamp: a delta always consumes at least one
                // byte and never reads past the input, so on every real
                // run this equals gp_raw; it keeps the measure
                // well-founded definitionally.
                let gpos = if gp_raw <= pos {
                    pos + 1
                } else if gp_raw > input.len() {
                    input.len() as int
                } else {
                    gp_raw
                };
                let bias2 = adapt_model(gi - i, length + 1, i == 0);
                let cp2 = cp + gi / (length + 1);
                if !is_valid_code_point(cp2) {
                    Option::None
                } else {
                    let bumped = bump_positions_model(posns, gi % (length + 1), 0);
                    build_model(
                        input,
                        gpos,
                        length + 1,
                        cp2,
                        bias2,
                        (gi % (length + 1)) + 1,
                        bumped.push(gi % (length + 1)),
                        codes.push(cp2),
                    )
                }
            }
        }
    }
}

/// Compute-friendly base prefix copy (avoids Seq::subrange materialization
/// in evaluated bodies).
pub open spec fn prefix_u8(input: Seq<u8>, up: int, j: int, acc: Seq<u8>) -> (r: Seq<u8>)
    decreases up - j
{
    if j >= up {
        acc
    } else {
        let acc2 = acc.push(input[j]);
        prefix_u8(input, up, j + 1, acc2)
    }
}

/// Compute-friendly all-ASCII check over the base prefix [0, up).
pub open spec fn base_ascii_ok(input: Seq<u8>, up: int, j: int) -> bool
    decreases up - j
{
    if j >= up {
        true
    } else {
        (input[j] < 0x80) && base_ascii_ok(input, up, j + 1)
    }
}

/// Full decode model (the external-caller byte core): split, reject a
/// non-ASCII base, build the insertion vector, merge with the base.
pub open spec fn decode_model(input: Seq<u8>) -> (r: Option<Seq<int>>) {
    let p = last_delim(input);
    if p >= 1 && !base_ascii_ok(input, p, 0) {
        Option::None
    } else {
        let bl = if p >= 1 { p } else { 0 };
        let es = if p >= 1 { p + 1 } else { 0 };
        let base_s = prefix_u8(input, bl, 0, Seq::empty());
        match build_model(input, es, bl, INITIAL_N as int, INITIAL_BIAS as int, 0,
            Seq::empty(), Seq::empty()) {
            Option::None => Option::None,
            Option::Some((posns, codes)) => Option::Some(
                merge_all_codes(base_s, posns, codes, 0, Seq::empty())),
        }
    }
}

/* ============================================================
 * External std contract: std::char::from_u32
 * ============================================================ */

// The only external std contract of this file. This verus build resolves the
// `char::from_u32` call through the module-level re-export `std::char::from_u32`
// (probed on this toolchain); the ensures is the function's documented contract:
// Some(<the char of that value>) iff the value is a valid scalar value
// (no surrogates). Ledger item 6.
#[allow(deprecated)]
pub assume_specification[std::char::from_u32](_0: u32) -> (res: Option<char>)
    ensures
        res.is_some() <==> is_valid_code_point(_0 as int),
        res matches Some(c) ==> c as u32 == _0,
;

/* ============================================================
 * adapt (punycode.rs:30-40)
 * ============================================================ */

/// Origin: punycode.rs:31-40 `adapt` -- RFC 3492 section 6.1 bias adaption.
/// (No upstream rustdoc.) Fully verified: with num_points >= 1 the division is
/// safe, the while loop terminates (delta shrinks by the factor 35 while > 455),
/// every intermediate value stays within u32, and the result is bounded.
fn adapt(delta: u32, num_points: u32, first_time: bool) -> (r: u32)
    requires
        1 <= num_points,
    ensures
        r as int <= 252,
        r as int == adapt_model(delta as int, num_points as int, first_time),
{
    /* Origin Rust: delta /= if first_time { DAMP } else { 2 };
       delta += delta / num_points; */
    let mut d = if first_time { delta / DAMP } else { delta / 2 };
    proof {
        assert(d as int <= 2147483647);
        assert(d as int / num_points as int <= d as int);
        assert(d as int + d as int / num_points as int <= 4294967295);
    }
    d = d + d / num_points;
    let ghost alg = adapt_loop_model(d as int, 0);
    proof {
        // u32 division on nonnegative operands is the integer division of
        // the model; adapt_model's entry performs the same two divisions.
        if first_time {
            assert((delta / DAMP) as int == (delta as int) / (DAMP as int));
        } else {
            assert((delta / 2) as int == (delta as int) / 2);
        }
        reveal(adapt_model);
        assert((d / num_points) as int == (d as int) / (num_points as int));
        assert(alg == adapt_model(delta as int, num_points as int, first_time));
    }
    let mut k: u32 = 0;
    let ghost mut it: int = 0;
    let ghost mut d_in: int = d as int;
    let ghost mut k_in: int = 0;
    /* Origin Rust: while delta > ((BASE - T_MIN) * T_MAX) / 2 {
       delta /= BASE - T_MIN; k += BASE; } */
    while d > ((BASE - T_MIN) * T_MAX) / 2
        invariant
            0 <= it <= 5,
            k as int == 36 * it,
            powi(35, it) * (d as int) <= 4294967295,
            d as int >= 0,
            adapt_loop_model(d as int, k as int) == alg,
            alg == adapt_model(delta as int, num_points as int, first_time),
        decreases d
    {
        proof {
            // entering with d >= 456: an it >= 5 would give
            // powi(35,5)*456 <= powi(35,it)*d <= u32::MAX, impossible;
            // the product invariant is preserved because (d/35)*35 <= d
            lemma_powi_step(35, it + 1);
            if it == 0 {
                assert(powi(35, it) == 1);
            } else {
                lemma_powi_pos(35, it);
            }
            assert(1 <= powi(35, it));
            assert(powi(35, it + 1) == 35 * powi(35, it));
            lemma_adapt_enter_bound(d, it);
            assert(it <= 4);
            assert(456 <= d as int);
            let dd = d as int / 35;
            let p = powi(35, it);
            let dd35 = dd * 35;
            assert(dd * 35 <= d as int);
            vstd::arithmetic::mul::lemma_mul_is_associative(35, p, dd);
            vstd::arithmetic::mul::lemma_mul_is_commutative(p, dd);
            vstd::arithmetic::mul::lemma_mul_is_associative(35, dd, p);
            vstd::arithmetic::mul::lemma_mul_is_commutative(35, dd);
            vstd::arithmetic::mul::lemma_mul_is_commutative(dd35, p);
            assert(powi(35, it + 1) * dd == powi(35, it) * (dd * 35));
            vstd::arithmetic::mul::lemma_mul_inequality(dd35, d as int, p);
            vstd::arithmetic::mul::lemma_mul_is_commutative(dd35, p);
            vstd::arithmetic::mul::lemma_mul_is_commutative(d as int, p);
            assert(powi(35, it + 1) * dd <= powi(35, it) * (d as int));
            assert(powi(35, it + 1) * dd <= 4294967295);
            // model step: one adapt_loop_model unfold through this body
            d_in = d as int;
            k_in = k as int;
        }
        d /= BASE - T_MIN;
        k += BASE;
        proof {
            it = it + 1;
            assert(d_in / 35 == d as int);
            assert(k_in + 36 == k as int);
            assert(adapt_loop_model(d_in, k_in)
                == adapt_loop_model(d_in / 35, k_in + 36)) by {
                reveal_with_fuel(adapt_loop_model, 1);
                assert(35 == (BASE - T_MIN) as int);
                assert(d_in > ((BASE - T_MIN) * T_MAX) as int / 2);
            };
            assert(adapt_loop_model(d as int, k as int) == alg);
        }
    }
    proof {
        // at loop exit d <= 455, k <= 36*5 = 180, and the bias term
        // (36*d)/(d+38) <= 36 since 36*d < 36*(d+38)
        assert(adapt_loop_model(d as int, k as int)
            == (k as int) + ((36 * d as int) / (d as int + 38))) by {
            reveal_with_fuel(adapt_loop_model, 1);
            assert((d as int) <= ((BASE - T_MIN) * T_MAX) as int / 2);
        };
        assert((36 * d as int) / (d as int + 38)
            == (((BASE - T_MIN + 1) * d) / (d + SKEW)) as int);
        lemma_powers();
        assert(d as int <= 455);
        assert(k as int <= 180);
        assert(d as int + 38 >= 38);
        assert(36 * d as int <= 36 * (d as int + 38));
        lemma_div_is_ordered(
            36 * d as int,
            36 * (d as int + 38),
            d as int + 38,
        );
        assert((36 * d as int) / (d as int + 38) <= (36 * (d as int + 38))
            / (d as int + 38));
        lemma_div_by_multiple(36, d as int + 38);
        assert((36 * (d as int + 38)) / (d as int + 38) == 36);
        assert((36 * d as int) / (d as int + 38) <= 36);
        assert(k as int + ((36 * d as int) / (d as int + 38)) <= 252);
    }
    /* Origin Rust: k + (((BASE - T_MIN + 1) * delta) / (delta + SKEW)) */
    k + (((BASE - T_MIN + 1) * d) / (d + SKEW))
}

/* ============================================================
 * Code-unit helpers (the u8 PunycodeCodeUnit impl, punycode.rs:108-130;
 * monomorphized for the file, ledger item 1)
 * ============================================================ */

/// Origin: punycode.rs:109-111 `PunycodeCodeUnit::is_delimiter` for u8.
/// (No upstream rustdoc on the trait methods.)
fn is_delimiter(byte: u8) -> (r: bool)
    ensures
        r == (byte == 0x2D),
{
    byte == b'-'
}

/// Origin: punycode.rs:112-114 `PunycodeCodeUnit::is_ascii` for u8.
fn is_ascii_u8(byte: u8) -> (r: bool)
    ensures
        r == ((byte as int) < 0x80),
{
    byte < 0x80
}

/// Origin: punycode.rs:115-123 `PunycodeCodeUnit::digit` for u8 -- the
/// external-caller alphabet accepts the upper-case digits 'A'..='Z'.
fn digit_u8(byte: u8) -> (r: Option<u32>)
    ensures
        r.is_some() == (digit_val(byte) >= 0),
        r.is_some() ==> ((r->0) as int) == digit_val(byte),
        r.is_some() ==> (r->0) < 36,
{
    /* Origin Rust: Some(match byte {
       byte @ b'0'..=b'9' => byte - b'0' + 26,
       byte @ b'A'..=b'Z' => byte - b'A',
       byte @ b'a'..=b'z' => byte - b'a',
       _ => return None, } as u32) */
    if 0x30 <= byte && byte <= 0x39 {
        Option::Some((byte - 0x30 + 26) as u32)
    } else if 0x41 <= byte && byte <= 0x5A {
        Option::Some((byte - 0x41) as u32)
    } else if 0x61 <= byte && byte <= 0x7A {
        Option::Some((byte - 0x61) as u32)
    } else {
        Option::None
    }
}

/// Origin: punycode.rs:124-126 `PunycodeCodeUnit::char` for u8.
fn u8_to_char(byte: u8) -> (r: char)
    ensures
        r as int == byte as int,
{
    byte as char
}

/* ============================================================
 * value_to_digit (punycode.rs:457-464)
 * ============================================================ */

/// Origin: punycode.rs:458-464 `value_to_digit` -- the value-to-symbol table.
/// The upstream panic!() arm for values outside 0..=35 is kept verbatim; the
/// panic obligation is carried by the requires, so every caller must prove
/// value <= 35 (both call sites of encode_into_chars do).
/// (No upstream rustdoc.)
fn value_to_digit(value: u32) -> (r: char)
    requires
        value <= 35,
    ensures
        is_digit_char(r),
        r as int == digit_char(value as int),
{
    match value {
        0..=25 => (value as u8 + b'a') as char,       // a..z
        26..=35 => (value as u8 - 26 + b'0') as char, // 0..9
        /* Origin Rust: _ => panic!(),
           (the unreachable arm for values > 35, excluded by the requires) */
        _ => panic!(),
    }
}

/* ============================================================
 * Decode phase 1: the delimiter split + base-ASCII check
 * (punycode.rs:171-190 of Decoder::decode, external-caller semantics)
 * ============================================================ */

/// Origin: punycode.rs:164-190, `Decoder::decode` head -- the
/// `input.iter().rposition(|c| c.is_delimiter())` basic/extended split
/// (rewritten as an index scan) plus the external-caller base-ASCII check
/// (`if C::EXTERNAL_CALLER && !base.iter().all(|c| c.is_ascii())`).
/// Returns (base_len, ext_start): base = input[..base_len],
/// extended = input[ext_start..].
/// Upstream doc (punycode.rs:165-165):
///   Split the input iterator and return a Vec with insertions of encoded characters
fn decode_split(input: &[u8]) -> (r: Result<(usize, usize), ()>)
    ensures
        ({
            let p = last_delim(input@);
            (r.is_ok()
                ==> ({
                    let bl = (r->Ok_0).0 as int;
                    let es = (r->Ok_0).1 as int;
                    (bl >= 0)
                        && (bl <= input@.len())
                        && (es <= input@.len())
                        && (p >= 1 ==> (bl == p && es == p + 1))
                        && (p <= 0 ==> (bl == 0 && es == 0))
                        && (forall |m: int| 0 <= m < bl ==> input@[m] < 0x80)
                }))
                && (r.is_err()
                    ==> (exists |m: int|
                        0 <= m < p && input@[m] >= 0x80))
        })
{
    /* Origin Rust: let (base, input) = if let Some(position) =
       input.iter().rposition(|c| c.is_delimiter()) {
           (&input[..position], if position > 0 { &input[position + 1..] } else { input })
       } else { (&input[..0], input) };
       -- scanned from the back; the first hit is the rposition result.
       fd == usize::MAX is the "no hit yet" sentinel; the ghost loc mirrors it
       as the spec last_delim_from view (-1 = none). */
    let mut fd: usize = usize::MAX;
    let ghost mut loc: int = -1;
    let mut pos = input.len();
    while pos > 0
        invariant
            pos <= input.len(),
            loc == last_delim_from(input@, pos as int),
            fd == usize::MAX <==> loc == -1,
            fd != usize::MAX ==> loc == fd as int,
        decreases pos
    {
        proof {
            // one-step unfold of last_delim_from at pos - 1, stated before the
            // sentinel update so the branch facts line up with the definition
            let t = last_delim_from(input@, pos as int);
            assert(loc == t);
            assert((fd == usize::MAX) == (t == -1));
            assert(last_delim_from(input@, pos as int - 1) == (if t >= 0 {
                t
            } else if input@[pos as int - 1] == 0x2D {
                pos as int - 1
            } else {
                -1
            }));
        }
        if fd == usize::MAX && is_delimiter(input[pos - 1]) {
            fd = pos - 1;
            proof {
                // the no-hit-so-far case with a delimiter here
                loc = pos as int - 1;
                assert(last_delim_from(input@, pos as int - 1) == loc);
            }
        } else {
            proof {
                // unchanged sentinel: either an earlier hit persists, or still none
                let t = last_delim_from(input@, pos as int);
                let nx = last_delim_from(input@, pos as int - 1);
                if fd != usize::MAX {
                    assert(t >= 0);
                    assert(nx == t);
                    assert(loc == nx);
                } else {
                    assert(t == -1);
                    assert(input@[pos as int - 1] != 0x2D);
                    assert(nx == -1);
                    assert(loc == nx);
                }
            }
        }
        pos -= 1;
    }
    proof {
        assert(loc == last_delim(input@));
    }
    if fd != usize::MAX && fd >= 1 {
        let base_len = fd;
        proof {
            assert(base_len as int == loc);
        }
        /* Origin Rust: if C::EXTERNAL_CALLER && !base.iter().all(|c| c.is_ascii()) {
           return Err(()); } (rewritten as a first-violation scan, same Err) */
        proof {
            lemma_last_delim_range(input@);
            assert(loc < input@.len());
            assert(base_len < input.len());
        }
        let mut m = 0usize;
        while m < base_len
            invariant
                m <= base_len,
                base_len <= input.len(),
                base_len as int == loc,
                loc == last_delim(input@),
                loc >= 1,
                forall |q: int| 0 <= q < m ==> input@[q] < 0x80,
            decreases base_len - m
        {
            if !is_ascii_u8(input[m]) {
                proof {
                    let wit = m as int;
                    let p = last_delim(input@);
                    assert(loc == p);
                    assert(input@[wit] >= 0x80);
                    assert(0 <= wit);
                    assert(wit < loc);
                    assert(wit < p);
                    assert(exists |q: int|
                        0 <= q < p && input@[q] >= 0x80) by {
                        assert(0 <= wit < p && input@[wit] >= 0x80);
                    }
                }
                return Result::Err(());
            }
            m += 1;
        }
        proof {
            assert(loc == last_delim(input@));
            assert(loc >= 1);
            assert((base_len as int) == loc);
            assert(((base_len + 1) as int) == loc + 1);
            assert(m == base_len);
        }
        Result::Ok((base_len, base_len + 1))
    } else {
        // no delimiter, or the delimiter at position 0 (the base is empty and
        // the whole input is the extended part)
        proof {
            assert(loc == last_delim(input@));
            assert(loc == -1 || loc == 0);
            assert(last_delim(input@) <= 0);
        }
        Result::Ok((0usize, 0usize))
    }
}

/* ============================================================
 * Decode phase 2: the generalized-integer delta build loop
 * (punycode.rs:196-253 of Decoder::decode)
 * ============================================================ */

/// Origin: punycode.rs:196-265, the main delta-decoding loop of
/// `Decoder::decode`: decoding generalized variable-length integers (RFC 3492
/// section 3.3) into (position, char) insertions moved outward by the bump
/// loop of punycode.rs:244-249. Rewrites: bytes by index (iter.next()), the
/// checked u32 ops as u64-wide comparisons (same accept/reject boundary).
/// Upstream doc (punycode.rs:165-165):
///   Split the input iterator and return a Vec with insertions of encoded characters
#[allow(deprecated)]
fn decode_build(input: &[u8], base_len: usize, ext_start: usize)
    -> (r: Result<Vec<(usize, char)>, ()>)
    requires
        input.len() <= u32::MAX as usize,
        (base_len == 0 && ext_start == 0)
            || (ext_start == base_len + 1 && base_len < input.len()),
    ensures
        r.is_ok() ==> ({
            let ins = (r->Ok_0)@;
            ((ins.len() <= (input@.len() - ext_start as int))
                && (forall |a: int, b: int|
                    0 <= a < b < ins.len() ==> ((ins[a].0 as int) != (ins[b].0 as int)))
                && (forall |j: int|
                    0 <= j < ins.len()
                        ==> (0 <= ins[j].0 as int
                            && (ins[j].0 as int) < base_len as int + ins.len())))
        }),
        ({
            // the full-precision insertion model over the views (the tuple
            // seq of the exec carries the same data)
            let bm = build_model(
                input@,
                ext_start as int,
                base_len as int,
                INITIAL_N as int,
                INITIAL_BIAS as int,
                0,
                Seq::empty(),
                Seq::empty(),
            );
            (r.is_err() <==> bm.is_none())
                && (r matches Ok(out) ==> (
                    (ins_posns(out@) == (bm->0).0)
                        && (ins_codes(out@) == (bm->0).1)))
        }),
{
    /* Origin Rust: self.insertions.clear(); -- the SmallVec buffer is
       represented by a fresh Vec (decode phases have no caller-visible
       buffer state of their own here) */
    let mut insertions: Vec<(usize, char)> = Vec::new();
    let ghost pbm = build_model(
        input@,
        ext_start as int,
        base_len as int,
        INITIAL_N as int,
        INITIAL_BIAS as int,
        0,
        Seq::empty(),
        Seq::empty(),
    );
    let mut pos: usize = ext_start; // byte cursor over input[ext_start..]
    let mut length: u32 = base_len as u32;
    let mut code_point: u32 = INITIAL_N;
    let mut bias: u32 = INITIAL_BIAS;
    let mut i: u32 = 0;
    while pos < input.len()
        invariant
            pos <= input.len(),
            ext_start <= pos,
            (base_len == 0 && ext_start == 0)
                || (ext_start == base_len + 1 && base_len < input.len()),
            input.len() <= u32::MAX as usize,
            // the fn-entry binding stays live only through this invariant:
            // without it the loop cut erases the pbm defining equation
            pbm == build_model(
                input@,
                ext_start as int,
                base_len as int,
                INITIAL_N as int,
                INITIAL_BIAS as int,
                0,
                Seq::empty(),
                Seq::empty(),
            ),
            pbm == build_model(
                input@,
                pos as int,
                length as int,
                code_point as int,
                bias as int,
                i as int,
                ins_posns(insertions@),
                ins_codes(insertions@),
            ),
            (length as int) == (base_len as int + insertions@.len() as int),
            (insertions@.len() as int) <= (pos as int - ext_start as int),
            (length as int) <= (base_len as int + pos as int - ext_start as int),
            forall |a: int, b: int|
                0 <= a < b < insertions@.len()
                    ==> ((insertions@[a].0 as int) != (insertions@[b].0 as int)),
            forall |j: int|
                0 <= j < insertions@.len()
                    ==> (0 <= insertions@[j].0 as int
                        && (insertions@[j].0 as int) < length as int),
            (i as int) <= (length as int),
            (bias as int) <= 614,
        decreases input.len() - pos
    {
        let ghost pos_head = pos;
        let ob_pos_e: usize = pos;
        let ob_length_e: u32 = length;
        let ob_cp_e: u32 = code_point;
        let ob_bias_e: u32 = bias;
        let ob_i_e: u32 = i;
        let ghost ob_pin_p = ins_posns(insertions@);
        let ghost ob_pin_c = ins_codes(insertions@);
        proof {
            assert(ob_pin_p == ins_posns(insertions@));
            assert(ob_pin_c == ins_codes(insertions@));
            assert(build_model(input@, ob_pos_e as int, ob_length_e as int,
                ob_cp_e as int, ob_bias_e as int, ob_i_e as int, ob_pin_p, ob_pin_c)
                == build_model(input@, pos as int, length as int,
                    code_point as int, bias as int, i as int,
                    ins_posns(insertions@), ins_codes(insertions@)));
            assert(build_model(input@, pos as int, length as int,
                code_point as int, bias as int, i as int,
                ins_posns(insertions@), ins_codes(insertions@)) == pbm);
        }
        /* Origin Rust: let previous_i = i; let mut weight = 1;
           let mut k = BASE; let mut byte = match iter.next() { None => break,
           Some(byte) => byte }; */
        let previous_i = i;
        let mut weight: u32 = 1;
        let mut k: u32 = BASE;
        let mut byte = input[pos];
        pos += 1;
        let gi_pos_e: usize = pos;
        let gi_byte_e: u8 = byte;
        let gi_i_e: u32 = i;
        let gi_bias_e: u32 = bias;
        proof {
            assert(gi_pos_e == pos_head + 1);
            assert(gi_byte_e == input@[pos_head as int]);
            assert(gen_int_model(input@, gi_pos_e as int, gi_byte_e, gi_i_e as int,
                1, 36, gi_bias_e as int)
                == gen_int_model(input@, pos_head as int + 1, input@[pos_head as int],
                    ob_i_e as int, 1, 36, ob_bias_e as int));
        }
        let ghost mut it: int = 0;
        /* Origin Rust: loop { ... } -- the generalized-integer decode loop */
        loop
            invariant_except_break gen_int_model(input@, pos as int, byte, i as int, weight as int, k as int, bias as int) == gen_int_model(input@, gi_pos_e as int, gi_byte_e, gi_i_e as int, 1, 36, gi_bias_e as int)
            invariant
                pos <= input.len(),
                (pos_head + 1) <= pos,
                it >= 0,
                gi_pos_e == pos_head + 1,
                ob_pos_e == pos_head,
                ob_i_e == gi_i_e,
                ob_bias_e == gi_bias_e,
                ob_length_e == length,
                ob_cp_e == code_point,
                (previous_i as int) == (ob_i_e as int),
                ob_bias_e == bias,
                gi_byte_e == input@[pos_head as int],
                ob_pin_p == ins_posns(insertions@),
                ob_pin_c == ins_codes(insertions@),
                pbm == build_model(
                    input@,
                    ext_start as int,
                    base_len as int,
                    INITIAL_N as int,
                    INITIAL_BIAS as int,
                    0,
                    Seq::empty(),
                    Seq::empty(),
                ),
                pbm == build_model(input@, ob_pos_e as int, ob_length_e as int,
                    ob_cp_e as int, ob_bias_e as int, ob_i_e as int,
                    ob_pin_p, ob_pin_c),
                (powi(10, it) <= (weight as int)) && ((weight as int) <= 4294967295),
                (k as int) == 36 + 36 * it,
                (previous_i as int) <= (i as int) && ((i as int) <= 4294967295),
                (bias as int) <= 614,
                (length as int) == (base_len as int + insertions@.len() as int),
                (insertions@.len() as int) <= (pos as int - ext_start as int),
                (insertions@.len() as int) <= (pos_head as int - ext_start as int),
                forall |a: int, b: int|
                    0 <= a < b < insertions@.len()
                        ==> ((insertions@[a].0 as int) != (insertions@[b].0 as int)),
                forall |j: int|
                    0 <= j < insertions@.len()
                        ==> (0 <= insertions@[j].0 as int
                            && (insertions@[j].0 as int) < length as int),
            ensures (gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                gi_i_e as int, 1, 36, gi_bias_e as int)
                == Option::Some((i as int, pos as int))),
                code_point == ob_cp_e,
                length == ob_length_e,
                ob_pin_p == ins_posns(insertions@),
                ob_pin_c == ins_codes(insertions@),
                pos <= input.len(),
                (previous_i as int) == (ob_i_e as int),
                bias == ob_bias_e,
            decreases (4294967295int) - (weight as int)
        {
            let ghost fvp_pos = pos;
            let ghost fvp_byte = byte;
            let ghost fvp_i = i;
            let ghost fvp_w = weight;
            let ghost fvp_k = k;
            /* Origin Rust: let digit = if let Some(digit) = byte.digit() { digit }
               else { return Err(()) }; */
            let digit = match digit_u8(byte) {
                Option::Some(d) => d,
                Option::None => {
                    proof {
                        // the model's invalid-digit arm: the pass is None
                        reveal_with_fuel(gen_int_model, 1);
                        assert(digit_val(fvp_byte) == -1);
                        assert(gen_int_model(input@, fvp_pos as int, fvp_byte,
                            fvp_i as int, fvp_w as int, fvp_k as int, bias as int)
                            == Option::None) by {
                            reveal_with_fuel(gen_int_model, 1);
                            assert(digit_val(fvp_byte) == -1);
                        };
                    }
                    return Result::Err(());
                }
            };
            {
                proof {
                    // head fact of this frame: the model of the frame args
                    // equals the pass-anchored entry value
                    assert(gen_int_model(input@, fvp_pos as int, fvp_byte,
                        fvp_i as int, fvp_w as int, fvp_k as int, bias as int)
                        == gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                            gi_i_e as int, 1, 36, gi_bias_e as int));
                }
            }
            proof {
                // digit < 36 (digit_u8's table domain): digit * weight fits u64
                assert((digit as int) < 36);
                assert((digit as int) >= 0);
                assert((weight as int) <= 4294967295);
                vstd::arithmetic::mul::lemma_mul_upper_bound(
                    digit as int,
                    35,
                    weight as int,
                    4294967295,
                );
                assert(((digit as u64) * (weight as u64)) <= 35 * 4294967295);
                assert(35 * 4294967295 < 18446744073709551615);
            }
            /* Origin Rust: let product = digit.checked_mul(weight).ok_or(())?;
               -- widened to u64, compared against u32 bounds */
            let product64 = (digit as u64) * (weight as u64);
            if product64 > u32::MAX as u64 {
                proof {
                    assert((digit_val(fvp_byte) as int) * (fvp_w as int)
                        > 0xFFFF_FFFF);
                    assert(gen_int_model(input@, fvp_pos as int, fvp_byte,
                        fvp_i as int, fvp_w as int, fvp_k as int, bias as int)
                        == Option::None) by {
                        reveal_with_fuel(gen_int_model, 1);
                        assert(product64 as int
                            == (digit_val(fvp_byte)) * (fvp_w as int));
                        assert((digit_val(fvp_byte)) * (fvp_w as int) > 0xFFFF_FFFF);
                    };
                
                assert(gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                    gi_i_e as int, 1, 36, gi_bias_e as int) == Option::None);
                assert(build_model(input@, ob_pos_e as int, ob_length_e as int,
                    ob_cp_e as int, ob_bias_e as int, ob_i_e as int, ob_pin_p,
                    ob_pin_c) == Option::None) by {
                    reveal_with_fuel(build_model, 1);
                    assert((ob_pos_e as int) < (input@.len() as int));
                    assert(gen_int_model(input@, ob_pos_e as int + 1,
                        input@[ob_pos_e as int], ob_i_e as int, 1, 36,
                        ob_bias_e as int)
                        == gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                            gi_i_e as int, 1, 36, gi_bias_e as int));
                };
                assert(pbm == Option::None);
                }
                return Result::Err(());
            }
            /* Origin Rust: i = i.checked_add(product).ok_or(())?; */
            proof {
                assert(product64 <= 4294967295);
                assert((i as u64) <= 4294967295);
                assert(((i as u64) + product64) < 18446744073709551615);
            }
            let i64 = (i as u64) + product64;
            if i64 > u32::MAX as u64 {
                proof {
                    assert((fvp_i as int) + (digit_val(fvp_byte)) * (fvp_w as int)
                        > 0xFFFF_FFFF);
                    assert(gen_int_model(input@, fvp_pos as int, fvp_byte,
                        fvp_i as int, fvp_w as int, fvp_k as int, bias as int)
                        == Option::None) by {
                        reveal_with_fuel(gen_int_model, 1);
                        assert(product64 as int
                            == (digit_val(fvp_byte)) * (fvp_w as int));
                    };
                
                assert(gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                    gi_i_e as int, 1, 36, gi_bias_e as int) == Option::None);
                assert(build_model(input@, ob_pos_e as int, ob_length_e as int,
                    ob_cp_e as int, ob_bias_e as int, ob_i_e as int, ob_pin_p,
                    ob_pin_c) == Option::None) by {
                    reveal_with_fuel(build_model, 1);
                    assert((ob_pos_e as int) < (input@.len() as int));
                    assert(gen_int_model(input@, ob_pos_e as int + 1,
                        input@[ob_pos_e as int], ob_i_e as int, 1, 36,
                        ob_bias_e as int)
                        == gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                            gi_i_e as int, 1, 36, gi_bias_e as int));
                };
                assert(pbm == Option::None);
                }
                return Result::Err(());
            }
            i = i64 as u32;
            let t = if k <= bias {
                T_MIN
            } else if k >= bias + T_MAX {
                T_MAX
            } else {
                k - bias
            };
            if digit < t {
                proof {
                    // the model's break: cpp frame value is Some((i, pos))
                    assert(i as int == fvp_i as int
                        + (digit_val(fvp_byte)) * (fvp_w as int)) by {
                        assert(product64 as int
                            == (digit_val(fvp_byte)) * (fvp_w as int));
                        assert(i as int == fvp_i as int + product64 as int);
                        assert(product64
                            == (digit as u64) * (weight as u64));
                        assert(digit as int == digit_val(fvp_byte));
                        assert(fvp_w as int == weight as int);
                    };
                    assert(t as int == t_for(fvp_k as int, bias as int)) by {
                        reveal(t_for);
                    };
                    assert(digit_val(fvp_byte) < t as int);
                    assert(gen_int_model(input@, fvp_pos as int, fvp_byte,
                        fvp_i as int, fvp_w as int, fvp_k as int, bias as int)
                        == Option::Some((i as int, fvp_pos as int))) by {
                        reveal_with_fuel(gen_int_model, 1);
                        assert(digit_val(fvp_byte) < t as int);
                        assert(i as int
                            == fvp_i as int + (digit_val(fvp_byte)) * (fvp_w as int));
                    };
                    assert(gen_int_model(input@, fvp_pos as int, fvp_byte,
                        fvp_i as int, fvp_w as int, fvp_k as int, bias as int)
                        == gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                            gi_i_e as int, 1, 36, gi_bias_e as int));
                    // value form that persists past the loop
                    assert(gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                        gi_i_e as int, 1, 36, gi_bias_e as int)
                        == Option::Some((i as int, pos as int)));
                }
                break;
            }
            /* Origin Rust: weight = weight.checked_mul(BASE - t).ok_or(())?; */
            let ghost weight_pre = weight;
            proof {
                assert((t as int) <= 26);
                assert((t as int) >= T_MIN as int);
                assert(((BASE - t) as int) >= 10);
                vstd::arithmetic::mul::lemma_mul_upper_bound(
                    weight_pre as int,
                    4294967295,
                    (BASE - t) as int,
                    35,
                );
                assert(((weight_pre as u64) * ((BASE - t) as u64))
                    <= 4294967295 * 35);
                assert(4294967295 * 35 < 18446744073709551615);
            }
            let w64 = (weight as u64) * ((BASE - t) as u64);
            if w64 > u32::MAX as u64 {
                proof {
                    assert(t as int == t_for(fvp_k as int, bias as int)) by {
                        reveal(t_for);
                    };
                    assert(digit_val(fvp_byte) >= t as int);
                    assert((fvp_w as int) * (36 - t as int) > 0xFFFF_FFFF);
                    assert(gen_int_model(input@, fvp_pos as int, fvp_byte,
                        fvp_i as int, fvp_w as int, fvp_k as int, bias as int)
                        == Option::None) by {
                        reveal_with_fuel(gen_int_model, 1);
                        assert(digit_val(fvp_byte) >= t as int);
                        assert((fvp_w as int) * (36 - t as int) > 0xFFFF_FFFF);
                    };
                
                assert(gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                    gi_i_e as int, 1, 36, gi_bias_e as int) == Option::None);
                assert(build_model(input@, ob_pos_e as int, ob_length_e as int,
                    ob_cp_e as int, ob_bias_e as int, ob_i_e as int, ob_pin_p,
                    ob_pin_c) == Option::None) by {
                    reveal_with_fuel(build_model, 1);
                    assert((ob_pos_e as int) < (input@.len() as int));
                    assert(gen_int_model(input@, ob_pos_e as int + 1,
                        input@[ob_pos_e as int], ob_i_e as int, 1, 36,
                        ob_bias_e as int)
                        == gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                            gi_i_e as int, 1, 36, gi_bias_e as int));
                };
                assert(pbm == Option::None);
                }
                return Result::Err(());
            }
            weight = w64 as u32;
            /* Origin Rust: k += BASE; -- the unchecked add, bounded via it */
            proof {
                if it >= 10 {
                    lemma_powers();
                    lemma_powi_mono(10, 10, it);
                    assert(powi(10, 10) <= powi(10, it));
                    assert(powi(10, it) <= weight_pre as int);
                    assert(powi(10, it) <= 4294967295);
                    assert(powi(10, 10) <= 4294967295);
                    assert(false);
                }
                assert(it <= 9);
                assert(k as int == 36 + 36 * it);
                assert(k as int <= 36 + 36 * 9);
                assert(k as int + 36 <= 4294967295);
            }
            k += BASE;
            /* Origin Rust: byte = match iter.next() { None => return Err(()),
               Some(byte) => byte }; -- end of input before the end of this delta */
            if pos >= input.len() {
                proof {
                    assert(t as int == t_for(fvp_k as int, bias as int)) by {
                        reveal(t_for);
                    };
                    assert(digit_val(fvp_byte) >= t as int);
                    assert(pos as int >= input@.len() as int);
                    assert(gen_int_model(input@, fvp_pos as int, fvp_byte,
                        fvp_i as int, fvp_w as int, fvp_k as int, bias as int)
                        == Option::None) by {
                        reveal_with_fuel(gen_int_model, 1);
                        assert(digit_val(fvp_byte) >= t as int);
                        assert(fvp_pos as int >= input@.len() as int);
                    };
                
                assert(gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                    gi_i_e as int, 1, 36, gi_bias_e as int) == Option::None);
                assert(build_model(input@, ob_pos_e as int, ob_length_e as int,
                    ob_cp_e as int, ob_bias_e as int, ob_i_e as int, ob_pin_p,
                    ob_pin_c) == Option::None) by {
                    reveal_with_fuel(build_model, 1);
                    assert((ob_pos_e as int) < (input@.len() as int));
                    assert(gen_int_model(input@, ob_pos_e as int + 1,
                        input@[ob_pos_e as int], ob_i_e as int, 1, 36,
                        ob_bias_e as int)
                        == gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                            gi_i_e as int, 1, 36, gi_bias_e as int));
                };
                assert(pbm == Option::None);
                }
                return Result::Err(());
            }
            byte = input[pos];
            pos += 1;
            proof {
                // powi(10, it + 1) <= weight (>= 10x growth), for the loop head
                lemma_powi_step(10, it + 1);
                assert(powi(10, it + 1) == 10 * powi(10, it));
                vstd::arithmetic::mul::lemma_mul_inequality(
                    powi(10, it),
                    weight_pre as int,
                    10,
                );
                assert(powi(10, it) * 10 <= weight_pre as int * 10);
                vstd::arithmetic::mul::lemma_mul_is_commutative(powi(10, it), 10);
                vstd::arithmetic::mul::lemma_mul_is_commutative(weight_pre as int, 10);
                assert(10 * powi(10, it) <= 10 * weight_pre as int);
                vstd::arithmetic::mul::lemma_mul_inequality(
                    10,
                    (BASE - t) as int,
                    weight_pre as int,
                );
                vstd::arithmetic::mul::lemma_mul_is_commutative(10, weight_pre as int);
                vstd::arithmetic::mul::lemma_mul_is_commutative(
                    (BASE - t) as int,
                    weight_pre as int,
                );
                assert(10 * weight_pre as int
                    <= (BASE - t) as int * weight_pre as int);
                assert((w64 as u32) as int == w64 as int);
                assert(w64 as int == (weight_pre as int) * (BASE - t) as int);
                assert(powi(10, it + 1) <= w64 as int);
                assert(powi(10, it + 1) <= weight as int);
                // the decrease witness: weight grew (factor >= 10 >= 2)
                if it == 0 {
                    assert(powi(10, 0) == 1);
                } else {
                    lemma_powi_pos(10, it);
                }
                assert(1 <= powi(10, it));
                assert(1 <= weight_pre as int);
                vstd::arithmetic::mul::lemma_mul_strict_inequality(
                    1,
                    10,
                    weight_pre as int,
                );
                assert((1 * (weight_pre as int)) < (10 * (weight_pre as int)));
                assert((weight_pre as int) < (10 * (weight_pre as int)));
                assert((10 * (weight_pre as int))
                    <= ((BASE - t) as int * (weight_pre as int)));
                assert((weight_pre as int) < weight as int);
                // it bookkeeping
                it = it + 1;
                assert(k as int == 36 + 36 * it);
            }
        }
        proof {
            // the pass digest breaks the gen model on this delta
            assert(gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                gi_i_e as int, 1, 36, gi_bias_e as int)
                == Option::Some((i as int, pos as int)));
            // k/weight bookkeeping at the loop head held it <= 9, so the tail
            // expression k + ... stays far below u32::MAX; also reestablish
            // the outer invariants around the i/length arithmetic
            assert(previous_i <= i);
            assert(insertions@.len() <= pos - ext_start);
            assert((insertions@.len() + 1) <= pos - ext_start);
        }
        /* Origin Rust: bias = adapt(i - previous_i, length + 1, previous_i == 0); */
        proof {
            // length + 1 fits u32 on both split domains; also num_points >= 1
            assert((pos_head as int) < input@.len() as int);
            assert((insertions@.len() as int) <= (pos_head as int - ext_start as int));
            if ext_start == 0 {
                assert(base_len == 0);
                assert((length as int) == insertions@.len() as int);
                assert((length as int) + 1 <= pos_head as int + 1);
                assert((length as int) + 1 <= input@.len() as int);
            } else {
                assert(ext_start == base_len + 1);
                assert((length as int) + 1
                    <= base_len as int + pos_head as int - ext_start as int + 1);
                assert((length as int) + 1 <= pos_head as int);
                assert((length as int) + 1 <= input@.len() as int);
            }
            assert((length + 1) as int <= 4294967295);
            assert(1 <= length + 1);
        }
        bias = adapt(i - previous_i, length + 1, previous_i == 0);
        /* Origin Rust: code_point = code_point.checked_add(i / (length + 1)).ok_or(())?; */
        proof {
            // length + 1 fits u32 (already shown for adapt above: split domains)
            assert((pos_head as int) < input@.len() as int);
            assert((insertions@.len() as int) <= (pos_head as int - ext_start as int));
            if ext_start == 0 {
                assert(base_len == 0);
                assert((length as int) == insertions@.len() as int);
                assert((length as int) + 1 <= pos_head as int + 1);
                assert((length as int) + 1 <= input@.len() as int);
            } else {
                assert(ext_start == base_len + 1);
                assert((length as int) + 1
                    <= base_len as int + pos_head as int - ext_start as int + 1);
                assert((length as int) + 1 <= pos_head as int);
                assert((length as int) + 1 <= input@.len() as int);
            }
            assert((length + 1) as int <= 4294967295);
            assert((i as u64) <= 4294967295);
        }
        let cp64 = (code_point as u64) + ((i as u64) / ((length as u64) + 1));
        if cp64 > u32::MAX as u64 {
            proof {
                // overflow is invalid-code-point territory in the model
                let gi = i as int;
                let cp2 = ob_cp_e as int + gi / (ob_length_e as int + 1);
                assert(cp2 == cp64 as int);
                assert(!is_valid_code_point(cp2));
                let bias2 = adapt_model(gi - ob_i_e as int, ob_length_e as int + 1,
                    ob_i_e as int == 0);
                assert(bias2 == bias as int);
                let gpos = if pos as int <= ob_pos_e as int {
                    ob_pos_e as int + 1
                } else if (pos as int) > (input@.len() as int) {
                    input@.len() as int
                } else {
                    pos as int
                };
                assert(build_model(input@, ob_pos_e as int, ob_length_e as int,
                    ob_cp_e as int, ob_bias_e as int, ob_i_e as int, ob_pin_p,
                    ob_pin_c) == Option::None) by {
                    reveal_with_fuel(build_model, 1);
                    assert(gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                        gi_i_e as int, 1, 36, gi_bias_e as int)
                        == Option::Some((gi, pos as int)));
                    assert(adapt_model(gi - ob_i_e as int, ob_length_e as int + 1,
                        ob_i_e as int == 0) == bias);
                    assert(i as int - previous_i as int
                        == gi - (ob_i_e as int));
                    assert(((length as u64) + 1) == ((ob_length_e as u64) + 1));
                };
                assert(pbm == Option::None);
            }
            return Result::Err(());
        }
        code_point = cp64 as u32;
        // a dead exec snapshot of the pre-modulo i: the reject arm below
        // reasons about the recursion state before `i %= length + 1` fires
        let i_prem = i;
        /* Origin Rust: i %= length + 1; */
        i %= length + 1;
        /* Origin Rust: let c = match char::from_u32(code_point) { Some(c) => c,
           None => return Err(()) }; */
        let c = match std::char::from_u32(code_point) {
            Option::Some(c) => c,
            Option::None => {
                proof {
                    // the surrogate-range arm: the model's validity reject
                    let gi = i_prem as int;
                    let cp2 = ob_cp_e as int + gi / (ob_length_e as int + 1);
                    assert(cp2 == cp64 as int);
                    assert(cp2 == code_point as int);
                    assert(!is_valid_code_point(cp2));
                    let bias2 = adapt_model(gi - ob_i_e as int, ob_length_e as int + 1,
                        ob_i_e as int == 0);
                    assert(bias2 == bias as int);
                    let gpos = if pos as int <= ob_pos_e as int {
                        ob_pos_e as int + 1
                    } else if (pos as int) > (input@.len() as int) {
                        input@.len() as int
                    } else {
                        pos as int
                    };
                    assert(build_model(input@, ob_pos_e as int, ob_length_e as int,
                        ob_cp_e as int, ob_bias_e as int, ob_i_e as int, ob_pin_p,
                        ob_pin_c) == Option::None) by {
                        reveal_with_fuel(build_model, 1);
                        assert(gen_int_model(input@, gi_pos_e as int, gi_byte_e,
                            gi_i_e as int, 1, 36, gi_bias_e as int)
                            == Option::Some((gi, pos as int)));
                        assert(adapt_model(gi - ob_i_e as int, ob_length_e as int + 1,
                            ob_i_e as int == 0) == bias);
                        assert(i_prem as int - previous_i as int
                            == gi - (ob_i_e as int));
                        assert(((length as u64) + 1) == ((ob_length_e as u64) + 1));
                    };
                    assert(pbm == Option::None);
                }
                return Result::Err(());
            }
        };
        proof {
            // after the modulo, i <= length (needed for the bump bounds)
            assert((i as int) <= (length as int));
        }
        /* Origin Rust: for (idx, _) in &mut self.insertions {
           if *idx >= i as usize { *idx += 1 } } --
           rewritten as an index loop with a pre-snapshot spec anchor */
        proof {
            // frame pins for the bump pass below: asserted here and carried
            // by the t2 loop invariants, so the tail reestablishment below
            // can still refer to the pre-bump frame state
            assert(gen_int_model(input@, ob_pos_e as int + 1,
                input@[ob_pos_e as int], ob_i_e as int, 1, 36,
                ob_bias_e as int) == Option::Some((i_prem as int, pos as int)));
            assert(bias as int
                == adapt_model((i_prem as int) - (ob_i_e as int),
                    ob_length_e as int + 1, ob_i_e as int == 0));
            assert(code_point as int
                == ob_cp_e as int + (i_prem as int) / (ob_length_e as int + 1));
            assert(is_valid_code_point(code_point as int));
            assert((i as int) == (i_prem as int) % (ob_length_e as int + 1));
            assert(ob_length_e as int == length as int);
            assert(ob_pin_p == ins_posns(insertions@));
            assert(ob_pin_c == ins_codes(insertions@));
        }
        let ghost ins_pre = insertions@;
        let ghost pos_pre = pos;
        let mut t2: usize = 0;
        while t2 < insertions.len()
            invariant
                ins_pre.len() == insertions@.len(),
                pos == pos_pre,
                t2 <= insertions.len(),
                (i as int) <= (length as int),
                (insertions@.len() as int) <= (pos as int - ext_start as int),
                (length as int) == (base_len as int + insertions@.len() as int),
                forall |j: int|
                    0 <= j < ins_pre.len()
                        ==> ((ins_pre[j].0 as int) < length as int),
                forall |a: int, b: int|
                    0 <= a < b < ins_pre.len()
                        ==> ((ins_pre[a].0 as int) != (ins_pre[b].0 as int)),
                forall |q: int|
                    0 <= q < t2
                        ==> (if (ins_pre[q].0 as int) >= (i as int) {
                        ((insertions@[q].0 as int) == (ins_pre[q].0 as int + 1))
                    } else {
                        insertions@[q] == ins_pre[q]
                    }),
                forall |q: int|
                    t2 <= q < ins_pre.len() ==> insertions@[q] == ins_pre[q],
                // the bump leaves the code components alone
                forall |q: int|
                    0 <= q < ins_pre.len()
                        ==> ((insertions@[q].1 as int) == (ins_pre[q].1 as int)),
                // pre-bump view anchors and the recursion-frame equations
                ob_pin_p == ins_posns(ins_pre),
                ob_pin_c == ins_codes(ins_pre),
                ob_length_e == length,
                pbm == build_model(
                    input@,
                    ext_start as int,
                    base_len as int,
                    INITIAL_N as int,
                    INITIAL_BIAS as int,
                    0,
                    Seq::empty(),
                    Seq::empty(),
                ),
                pbm == build_model(input@, ob_pos_e as int, ob_length_e as int,
                    ob_cp_e as int, ob_bias_e as int, ob_i_e as int,
                    ob_pin_p, ob_pin_c),
                gen_int_model(input@, ob_pos_e as int + 1,
                    input@[ob_pos_e as int], ob_i_e as int, 1, 36,
                    ob_bias_e as int)
                    == Option::Some((i_prem as int, pos as int)),
                bias as int
                    == adapt_model((i_prem as int) - (ob_i_e as int),
                        ob_length_e as int + 1, ob_i_e as int == 0),
                code_point as int
                    == ob_cp_e as int + (i_prem as int) / (ob_length_e as int + 1),
                is_valid_code_point(code_point as int),
                (i as int) == (i_prem as int) % (ob_length_e as int + 1),
            decreases insertions.len() - t2
        {
            proof {
                assert((t2 as int) < ins_pre.len());
                assert((ins_pre[t2 as int].0 as int) < length as int);
                assert((i as int) <= length as int);
            }
            let (idx0, c0) = insertions[t2];
            if idx0 >= i as usize {
                proof {
                    // idx0 and idx0 + 1 both stay under length (non-overflowing)
                    assert((idx0 as int) < length as int);
                    assert((i as int) <= length as int);
                    assert(idx0 as int + 1 <= length as int);
                    assert((idx0 as int) + 1 <= 4294967295);
                    if (ins_pre[t2 as int].0 as int) < (i as int) {
                        assert(insertions@[t2 as int] == ins_pre[t2 as int]);
                        assert((ins_pre[t2 as int].0 as int) >= (i as int));
                        assert(false);
                    }
                }
                insertions.set(t2, (idx0 + 1, c0));
            }
            t2 += 1;
        }
        proof {
            // exit bookkeeping: the bump pass ran to the sequence end (put
            // before the push, which grows the sequence underneath this fact)
            assert(!(t2 < insertions.len()));
            assert((t2 as int) == (insertions.len() as int));
            assert((insertions.len() as int) == (ins_pre.len() as int));
            assert((t2 as int) == (ins_pre.len() as int));
        }
        proof {
            // the bump preserves pairwise distinctness: bumped entries all had
            // position >= i, untouched ones < i; the pushed entry at i is then
            // distinct from both groups and inside the length bound
            let ins2 = insertions@;
            assert(ins_pre.len() == ins2.len());
            assert forall |j: int| 0 <= j < ins_pre.len() implies
                ((if (ins_pre[j].0 as int) >= (i as int) {
                    ((ins2[j].0 as int) == (ins_pre[j].0 as int + 1))
                } else {
                    (ins2[j] == ins_pre[j])
                })) by {}
            assert forall |a: int, b: int| 0 <= a < b < ins2.len() implies
                ((ins2[a].0 as int) != (ins2[b].0 as int)) by {
                if (ins_pre[a].0 as int) >= (i as int) {
                    if (ins_pre[b].0 as int) >= (i as int) {
                        assert((ins2[a].0 as int) == (ins_pre[a].0 as int + 1));
                        assert((ins2[b].0 as int) == (ins_pre[b].0 as int + 1));
                        if (ins_pre[a].0 as int) < (ins_pre[b].0 as int) {
                            assert((ins2[a].0 as int) < (ins2[b].0 as int));
                        } else {
                            assert((ins_pre[b].0 as int) < (ins_pre[a].0 as int));
                            assert((ins2[b].0 as int) < (ins2[a].0 as int));
                        }
                    } else {
                        assert((ins2[a].0 as int) >= (i as int + 1));
                        assert(ins2[b] == ins_pre[b]);
                        assert((ins2[b].0 as int) < (i as int));
                    }
                } else {
                    if (ins_pre[b].0 as int) >= (i as int) {
                        assert(ins2[a] == ins_pre[a]);
                        assert((ins2[b].0 as int) >= (i as int + 1));
                        assert((ins2[a].0 as int) < (i as int));
                    } else {
                        assert(ins2[a] == ins_pre[a]);
                        assert(ins2[b] == ins_pre[b]);
                    }
                }
            }
            assert forall |j: int| 0 <= j < ins2.len() implies
                ((ins2[j].0 as int) >= 0 && (ins2[j].0 as int) <= length as int) by {
                if (ins_pre[j].0 as int) >= (i as int) {
                    assert(ins2[j].0 as int == ins_pre[j].0 as int + 1);
                    assert((ins_pre[j].0 as int) < length as int);
                    assert(ins2[j].0 as int <= length as int);
                } else {
                    assert(ins2[j] == ins_pre[j]);
                }
            }
        }
        // post-bump, pre-push snapshots: the tail model glue below needs the
        // bumped state plus this iteration's pre-increment i as its index
        let ghost ins_bumped = insertions@;
        let i_postm = i;
        /* Origin Rust: self.insertions.push((i as usize, c)); */
        insertions.push((i as usize, c));
        proof {
            // after the push: all positions are under the (new) length, the new
            // entry sits at i <= length, distinct from every bumped/untouched
            // entry, and the insertions-consume-byte bound still holds
            let ins2 = insertions@;
            assert(ins2.len() == ins_pre.len() + 1);
            assert(ins2[ins2.len() - 1] == (i as usize, c));
            assert((i as int) <= length as int);
            assert(((i as usize) as int) == i as int);
            assert((pos as int) >= (pos_head as int) + 1);
            assert((ins2.len()) <= (pos as int - ext_start as int));
            assert forall |a: int, b: int| 0 <= a < b < ins2.len() implies
                ((ins2[a].0 as int) != (ins2[b].0 as int)) by {
                if b < ins2.len() - 1 {
                } else {
                    assert(a < ins2.len() - 1);
                    // the new last entry against each bumped/untouched older one
                    if (ins_pre[a].0 as int) >= (i as int) {
                        assert((ins2[a].0 as int) == ins_pre[a].0 as int + 1);
                        assert((ins2[a].0 as int) > (i as int));
                    } else {
                        assert(ins2[a] == ins_pre[a]);
                        assert((ins2[a].0 as int) < (i as int));
                    }
                }
            }
            assert forall |j: int| 0 <= j < ins2.len() implies
                ((ins2[j].0 as int) >= 0
                    && (ins2[j].0 as int) < length as int + 1) by {
                if j < ins2.len() - 1 {
                    assert(ins2[j].0 as int <= length as int);
                } else {
                    assert(ins2[j].0 as int == i as int);
                }
            }
        }
        /* Origin Rust: length += 1; i += 1; */
        proof {
            assert(length + 1 <= 4294967295);
        }
        length += 1;
        i += 1;
        proof {
            // outer-tail maintenance of the model pin: the recursion folds one
            // frame down from the ob_*_e snapshot to the current tail state
            let gi = i_prem as int;
            let iv = gi % (ob_length_e as int + 1);
            assert((pos as int) > (ob_pos_e as int));
            assert((pos as int) <= (input@.len() as int));
            assert((i_postm as int) == iv);
            assert((i as int) == iv + 1);
            assert(length as int == ob_length_e as int + 1);
            // t2 is at the end of the bumped seq (anchored right after the
            // bump pass), so the bridge lemma turns the clauses into view form
            assert((t2 as int) == (ins_pre.len() as int));
            lemma_views_bump_bridge(ins_pre, ins_bumped, iv);
            assert(ins_bumped.len() as int == ins_pre.len() as int);
            // the push appends (iv, c) to the bumped state
            assert(insertions@ == ins_bumped.push((i_postm as usize, c)));
            lemma_ins_posns_push(ins_bumped, (i_postm as usize, c));
            lemma_ins_codes_push(ins_bumped, (i_postm as usize, c));
            assert((c as u32) as int == code_point as int);
            assert((c as int) == code_point as int);
            assert(ins_posns(insertions@)
                == bump_positions_model(ob_pin_p, iv, 0).push(iv));
            assert(ins_codes(insertions@) == ob_pin_c.push(code_point as int));
            // one recursion frame of the model, from the pinned digest
            assert(build_model(input@, ob_pos_e as int, ob_length_e as int,
                ob_cp_e as int, ob_bias_e as int, ob_i_e as int, ob_pin_p,
                ob_pin_c)
                == build_model(input@, pos as int,
                    ob_length_e as int + 1, code_point as int, bias as int,
                    iv + 1, bump_positions_model(ob_pin_p, iv, 0).push(iv),
                    ob_pin_c.push(code_point as int))) by {
                reveal_with_fuel(build_model, 1);
                assert((ob_pos_e as int) < (input@.len() as int));
                assert(gen_int_model(input@, ob_pos_e as int + 1,
                    input@[ob_pos_e as int], ob_i_e as int, 1, 36,
                    ob_bias_e as int) == Option::Some((gi, pos as int)));
            };
            // chain into the tail-state frame (congruent arguments)
            assert(pbm == build_model(input@, pos as int, length as int,
                code_point as int, bias as int, i as int,
                ins_posns(insertions@), ins_codes(insertions@)));
        }
    }
    Result::Ok(insertions)
}

/* ============================================================
 * Decode phase 3: the position merge (punycode.rs:255 + 280-310)
 * ============================================================ */

/// Origin: punycode.rs:285, the per-position lookup `self.insertions.get(self.inserted)`
/// inside `Decode::next` -- rewritten as a fresh scan for the insertion placed
/// exactly at the output position (upstream first sorts by position, so its scan
/// is a two-pointer walk; with pairwise-distinct positions the position-by-position
/// semantics are order-independent, which makes the fresh scan its faithful form).
fn merge_find(ins: &[(usize, char)], pos: usize) -> (r: Option<usize>)
    ensures
        r matches Some(j) ==> (j < ins@.len()
            && ((ins@[j as int].0 as int) == pos as int)),
        r matches None ==> (forall |k: int|
            0 <= k < ins@.len() ==> ((ins@[k].0 as int) != pos as int)),
{
    let mut j: usize = 0;
    while j < ins.len()
        invariant
            j <= ins.len(),
            forall |k: int| 0 <= k < j ==> ((ins@[k].0 as int) != pos as int),
        decreases ins.len() - j
    {
        let (p0, _) = ins[j];
        if p0 == pos {
            proof {
                assert((ins@[j as int].0 as int) == pos as int);
            }
            return Option::Some(j);
        }
        j += 1;
    }
    Option::None
}

/// Origin: punycode.rs:280-310, the merge iterator `Decode::next` rewritten as a
/// loop building the output Vec (collect() target): at each output position the
/// insertion placed there, if any, else the next base code unit; the upstream
/// `sort_by_key` (punycode.rs:255) is dropped (see merge_find's Origin note).
/// Upstream doc (punycode.rs:165-165 of Decoder::decode):
///   Split the input iterator and return a Vec with insertions of encoded characters
fn decode_merge(base: &[u8], ins: &[(usize, char)]) -> (r: Vec<char>)
    requires
        forall |a: int, b: int|
            0 <= a < b < ins@.len() ==> ((ins@[a].0 as int) != (ins@[b].0 as int)),
        forall |j: int|
            0 <= j < ins@.len()
                ==> ((ins@[j].0 as int) >= 0
                    && (ins@[j].0 as int) < base@.len() as int + ins@.len() as int),
        (base@.len() as int + ins@.len() as int) <= 0x1_0000_0000 - 1,
    ensures
        r@.len() == (base@.len() as int + ins@.len() as int),
        forall |p: int|
            0 <= p < (base@.len() as int + ins@.len() as int)
                ==> (r@[p] == merged_char_at(base@, ins@, p)),
{
    let total = base.len() + ins.len();
    let mut base_idx: usize = 0;
    let mut pos: usize = 0;
    let mut out: Vec<char> = Vec::new();
    proof {
        // a zero-length interval counts nothing (entry state: pos == 0)
        let s = ins_positions(ins@);
        lemma_count_in_empty(s, 0);
        assert(count_in(s, 0, 0) == 0);
    }
    while pos < total
        invariant
            pos <= total,
            (total as int) == (base@.len() as int + ins@.len() as int),
            out@.len() == pos as int,
            forall |a: int, b: int|
                0 <= a < b < ins@.len() ==> ((ins@[a].0 as int) != (ins@[b].0 as int)),
            forall |j: int|
                0 <= j < ins@.len()
                    ==> ((ins@[j].0 as int) >= 0
                        && (ins@[j].0 as int) < base@.len() as int + ins@.len() as int),
            (base_idx as int)
                == (pos as int - count_in(ins_positions(ins@), 0, pos as int)),
            forall |q: int|
                0 <= q < pos ==> (out@[q] == merged_char_at(base@, ins@, q)),
        decreases total - pos
    {
        let found = merge_find(ins, pos);
        match found {
            Option::Some(j) => {
                proof {
                    let s = ins_positions(ins@);
                    lemma_seq_new_len(ins@.len(), |jj: int| ins@[jj].0 as int);
                    assert(s.len() == ins@.len());
                    vstd::seq::lemma_seq_new_index(
                        ins@.len(),
                        |jj: int| ins@[jj].0 as int,
                        j as int,
                    );
                    assert(s[j as int] == ins@[j as int].0 as int);
                    assert(s[j as int] == pos as int);
                    // the found insertion is exactly the merge entry at pos
                    lemma_pos_index_some(ins@, pos as int, j as int);
                    assert(ins_pos_index(ins@, pos as int) == j);
                    assert(merged_char_at(base@, ins@, pos as int)
                        == ins@[j as int].1);
                    // count step: the hit is the sole member of [pos, pos+1)
                    lemma_count_in_epi_one(
                        s,
                        pos as int,
                        j as int,
                    );
                    assert(count_in(s, pos as int, pos as int + 1) == 1);
                    lemma_sep_split(s, 0, pos as int, pos as int + 1);
                    assert(count_in(s, 0, pos as int + 1)
                        == count_in(s, 0, pos as int) + 1);
                    assert(merged_char_at(base@, ins@, pos as int)
                        == merged_char_at(base@, ins@, pos as int));
                }
                out.push(ins[j].1);
                pos += 1;
            }
            Option::None => {
                proof {
                    let s = ins_positions(ins@);
                    lemma_seq_new_len(ins@.len(), |jj: int| ins@[jj].0 as int);
                    assert(s.len() == ins@.len());
                    // no insertion sits at pos
                    assert forall |k: int| 0 <= k < s.len() implies
                        (s[k] != pos as int) by {
                        if 0 <= k && k < s.len() {
                            vstd::seq::lemma_seq_new_index(
                                ins@.len(),
                                |jj: int| ins@[jj].0 as int,
                                k,
                            );
                            assert(s[k] == ins@[k].0 as int);
                            assert((ins@[k].0 as int) != pos as int);
                        }
                    }
                    lemma_count_in_epi(s, pos as int);
                    assert(count_in(s, pos as int, pos as int + 1) == 0);
                    lemma_sep_split(s, 0, pos as int, pos as int + 1);
                    assert(count_in(s, 0, pos as int + 1)
                        == count_in(s, 0, pos as int) + 0);
                    // the pigeonhole availability of the next base char
                    lemma_sep_split(s, 0, pos as int, total as int);
                    lemma_sep_split(s, pos as int, pos as int + 1, total as int);
                    assert(count_in(s, 0, total as int)
                        == count_in(s, 0, pos as int)
                            + count_in(s, pos as int, pos as int + 1)
                            + count_in(s, pos as int + 1, total as int));
                    assert forall |k: int| 0 <= k < s.len() implies
                        (0 <= s[k] && s[k] < total as int) by {
                        if 0 <= k && k < s.len() {
                            vstd::seq::lemma_seq_new_index(
                                ins@.len(),
                                |jj: int| ins@[jj].0 as int,
                                k,
                            );
                            assert(s[k] == ins@[k].0 as int);
                            assert(0 <= (ins@[k].0 as int));
                            assert(((ins@[k].0 as int))
                                < (base@.len() as int + ins@.len() as int));
                            assert(s.len() == ins@.len());
                            assert(s[k] < total as int);
                        }
                    }
                    lemma_count_in_full(s, 0, total as int);
                    assert(count_in(s, 0, total as int) == s.len());
                    lemma_count_in_pigeonhole(s, pos as int + 1, total as int);
                    assert(count_in(s, pos as int + 1, total as int)
                        <= total as int - pos as int - 1);
                    assert(count_in(s, 0, pos as int) == pos as int - base_idx as int);
                    assert(s.len()
                        <= (pos as int - base_idx as int)
                            + (total as int - pos as int - 1));
                    assert(base@.len() as int == total as int - s.len());
                    assert(base_idx as int <= base@.len() as int - 1);
                    assert(base_idx < base.len());
                    // the merge entry at pos is the base char at base_idx
                    lemma_pos_index_none(ins@, pos as int);
                    assert(ins_pos_index(ins@, pos as int) == -1);
                    assert(merged_char_at(base@, ins@, pos as int)
                        == base@[pos as int - count_in(s, 0, pos as int)] as char);
                    assert(pos as int - count_in(s, 0, pos as int)
                        == base_idx as int);
                    assert(merged_char_at(base@, ins@, pos as int)
                        == base@[base_idx as int] as char);
                }
                out.push(u8_to_char(base[base_idx]));
                proof {
                    let bh = base[base_idx as int];
                    assert(base[base_idx as int] == base@[base_idx as int]);
                    assert(merged_char_at(base@, ins@, pos as int)
                        == base@[base_idx as int] as char);
                    assert((bh as char) == base@[base_idx as int] as char);
                }
                base_idx += 1;
                pos += 1;
            }
        }
    }
    out
}


/* ---------------------------------------------------------------
 * count_in / ins_pos_index lemmas (the merge machinery)
 * --------------------------------------------------------------- */

/// Two-way interval split: [lo, hi) = [lo, m) + [m, hi).
proof fn lemma_sep_split(s: Seq<int>, lo: int, m: int, hi: int)
    requires
        lo <= m <= hi,
    ensures
        count_in(s, lo, hi) == count_in(s, lo, m) + count_in(s, m, hi),
    decreases s.len()
{
    if s.len() == 0 {
        assert(count_in(s, lo, hi) == 0);
        assert(count_in(s, lo, m) == 0);
        assert(count_in(s, m, hi) == 0);
    } else {
        let sub = s.subrange(0, s.len() - 1);
        lemma_sep_split(sub, lo, m, hi);
        assert(count_in(s, lo, hi) == count_in(sub, lo, hi) + (if lo
            <= s[s.len() - 1]
            < hi
        { 1int } else { 0int }));
        assert(count_in(s, lo, m) == count_in(sub, lo, m) + (if lo
            <= s[s.len() - 1]
            < m
        { 1int } else { 0int }));
        assert(count_in(s, m, hi) == count_in(sub, m, hi) + (if m
            <= s[s.len() - 1]
            < hi
        { 1int } else { 0int }));
        // case balance on the position of the last element
        if s[s.len() - 1] < lo {
        } else if s[s.len() - 1] < m {
            assert(lo <= s[s.len() - 1] < hi);
        } else {
            assert(!(lo <= s[s.len() - 1] < m));
        }
    }
}

/// No element equal to m means count_in(s, m, m+1) is zero.
proof fn lemma_count_in_epi(s: Seq<int>, m: int)
    requires
        forall |k: int| 0 <= k < s.len() ==> s[k] != m,
    ensures
        count_in(s, m, m + 1) == 0,
    decreases s.len()
{
    if s.len() == 0 {
        assert(count_in(s, m, m + 1) == 0);
    } else {
        let sub = s.subrange(0, s.len() - 1);
        assert forall |k: int| 0 <= k < sub.len() implies (sub[k] != m) by {
            vstd::seq::lemma_seq_subrange_index(s, 0, s.len() - 1, k);
            assert(sub[k] == s[k]);
        }
        lemma_count_in_epi(sub, m);
        assert(count_in(s, m, m + 1) == count_in(sub, m, m + 1)
            + (if m <= s[s.len() - 1] < m + 1 { 1int } else { 0int }));
        assert(!(m <= s[s.len() - 1] < m + 1));
    }
}

/// If some element equals m then count_in(s, m, m+1) is one.
proof fn lemma_count_in_epi_one(s: Seq<int>, m: int, k: int)
    requires
        0 <= k < s.len(),
        s[k] == m,
        forall |a: int, b: int| 0 <= a < b < s.len() ==> s[a] != s[b],
    ensures
        count_in(s, m, m + 1) == 1,
    decreases s.len()
{
    if s.len() == 0 {
        assert(false);
    } else {
        let sub = s.subrange(0, s.len() - 1);
        assert(sub.len() == s.len() - 1);
        assert(count_in(s, m, m + 1) == count_in(sub, m, m + 1)
            + (if m <= s[s.len() - 1] < m + 1 { 1int } else { 0int }));
        if k == s.len() - 1 {
            assert(s[s.len() - 1] == m);
            assert(m <= s[s.len() - 1] < m + 1);
            assert(count_in(sub, m, m + 1) == 0) by {
                assert forall |q: int| 0 <= q < sub.len() implies (sub[q] != m) by {
                    vstd::seq::lemma_seq_subrange_index(s, 0, s.len() - 1, q);
                    assert(sub[q] == s[q]);
                    assert(q < s.len() - 1);
                    assert(s[q] != s[s.len() - 1]);
                    assert(s[q] != m);
                }
                lemma_count_in_epi(sub, m);
            }
            assert(count_in(s, m, m + 1) == 0 + 1);
        } else {
            assert(k < s.len() - 1);
            assert(k < sub.len());
            vstd::seq::lemma_seq_subrange_index(s, 0, s.len() - 1, k);
            assert(sub[k] == s[k]);
            assert(sub[k] == m);
            lemma_count_in_epi_one(sub, m, k);
            assert(count_in(sub, m, m + 1) == 1);
            assert(!(m <= s[s.len() - 1] < m + 1)) by {
                // s[k] == m with k < last, so the last element differs from m
                assert(s[k] != s[s.len() - 1]);
                assert(s[s.len() - 1] != m);
                assert(!(m <= s[s.len() - 1] < m + 1));
            }
            assert(count_in(s, m, m + 1) == 1);
        }
    }
}

/// A zero-length interval counts nothing.
proof fn lemma_count_in_empty(s: Seq<int>, lo: int)
    ensures
        count_in(s, lo, lo) == 0,
    decreases s.len()
{
    if s.len() == 0 {
        assert(count_in(s, lo, lo) == 0);
    } else {
        let sub = s.subrange(0, s.len() - 1);
        assert(sub.len() == s.len() - 1);
        lemma_count_in_empty(sub, lo);
        assert(count_in(s, lo, lo) == count_in(sub, lo, lo)
            + (if lo <= s[s.len() - 1] < lo { 1int } else { 0int }));
        assert(count_in(s, lo, lo) == count_in(sub, lo, lo));
    }
}

/// Pigeonhole: pairwise-distinct elements fill an interval of length hi-lo
/// with at most hi-lo members.
proof fn lemma_count_in_pigeonhole(s: Seq<int>, lo: int, hi: int)
    requires
        forall |a: int, b: int| 0 <= a < b < s.len() ==> s[a] != s[b],
        lo <= hi,
    ensures
        count_in(s, lo, hi) <= hi - lo,
    decreases s.len()
{
    if s.len() == 0 {
        assert(count_in(s, lo, hi) == 0);
    } else {
        let sub = s.subrange(0, s.len() - 1);
        assert(sub.len() == s.len() - 1);
        assert forall |a: int, b: int| 0 <= a < b < sub.len() ==> (sub[a] != sub[b]) by {
            if 0 <= a && a < b && b < sub.len() {
                vstd::seq::lemma_seq_subrange_index(s, 0, s.len() - 1, a);
                vstd::seq::lemma_seq_subrange_index(s, 0, s.len() - 1, b);
                assert(sub[a] == s[a]);
                assert(sub[b] == s[b]);
                assert(0 <= a < b < s.len());
                assert(s[a] != s[b]);
            }
        }
        if lo <= s[s.len() - 1] < hi {
            let m = s[s.len() - 1];
            assert(lo <= m < hi);
            // sub contributes no element equal to m
            assert forall |q: int| 0 <= q < sub.len() implies (sub[q] != m) by {
                vstd::seq::lemma_seq_subrange_index(s, 0, s.len() - 1, q);
                assert(sub[q] == s[q]);
                assert(q < s.len() - 1);
                assert(s[q] != s[s.len() - 1]);
                assert(s[q] != m);
            }
            lemma_count_in_epi(sub, m);
            lemma_sep_split(sub, lo, m, hi);
            lemma_count_in_pigeonhole(sub, lo, m);
            lemma_count_in_pigeonhole(sub, m + 1, hi);
            lemma_sep_split(s, lo, m, hi);
            lemma_sep_split(s, m, m + 1, hi);
            lemma_count_in_epi_one(s, m, s.len() - 1);
            // the last element sits outside [lo, m) and [m+1, hi)
            assert(count_in(s, lo, m) == count_in(sub, lo, m)
                + (if lo <= m < m { 1int } else { 0int }));
            assert(count_in(s, lo, m) == count_in(sub, lo, m));
            assert(count_in(s, m + 1, hi) == count_in(sub, m + 1, hi)
                + (if m + 1 <= m < hi { 1int } else { 0int }));
            assert(count_in(s, m + 1, hi) == count_in(sub, m + 1, hi));
            assert(count_in(s, lo, hi)
                == count_in(s, lo, m) + count_in(s, m, m + 1)
                    + count_in(s, m + 1, hi));
            assert(count_in(s, lo, m) <= m - lo);
            assert(count_in(s, m + 1, hi) <= hi - (m + 1));
            assert(count_in(s, lo, hi) <= (m - lo) + 1 + (hi - m - 1));
        } else {
            lemma_count_in_pigeonhole(sub, lo, hi);
            assert(count_in(s, lo, hi) == count_in(sub, lo, hi)
                + (if lo <= s[s.len() - 1] < hi { 1int } else { 0int }));
            assert(count_in(s, lo, hi) == count_in(sub, lo, hi));
        }
    }
}

/// When every element lies in [lo, hi), the count is the length.
proof fn lemma_count_in_full(s: Seq<int>, lo: int, hi: int)
    requires
        forall |k: int| #![trigger s[k]] 0 <= k < s.len() ==> (lo <= s[k] < hi),
    ensures
        count_in(s, lo, hi) == s.len(),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let sub = s.subrange(0, s.len() - 1);
        assert forall |k: int| #![trigger sub[k]] 0 <= k < sub.len() implies
            (lo <= sub[k] < hi) by {
            vstd::seq::lemma_seq_subrange_index(s, 0, s.len() - 1, k);
            assert(sub[k] == s[k]);
        }
        lemma_count_in_full(sub, lo, hi);
        assert(count_in(s, lo, hi) == count_in(sub, lo, hi)
            + (if lo <= s[s.len() - 1] < hi { 1int } else { 0int }));
        assert(lo <= s[s.len() - 1] < hi);
    }
}

/// ins_pos_index: no insertion at p yields -1.
proof fn lemma_pos_index_none(ins: Seq<(usize, char)>, p: int)
    requires
        forall |k: int| 0 <= k < ins.len() ==> ((ins[k].0 as int) != p),
    ensures
        ins_pos_index(ins, p) == -1,
    decreases ins.len()
{
    if ins.len() == 0 {
        assert(ins_pos_index(ins, p) == -1);
    } else {
        let sub = ins.subrange(0, ins.len() - 1);
        assert forall |k: int| 0 <= k < sub.len() implies
            ((sub[k].0 as int) != p) by {
            if 0 <= k && k < sub.len() {
                vstd::seq::lemma_seq_subrange_index(ins, 0, ins.len() - 1, k);
                assert(sub[k] == ins[k]);
                assert((ins[k].0 as int) != p);
            }
        }
        lemma_pos_index_none(sub, p);
        assert((ins[ins.len() - 1].0 as int) != p);
        assert(ins_pos_index(ins, p) == ins_pos_index(sub, p));
        assert(ins_pos_index(sub, p) == -1);
    }
}

/// ins_pos_index: with pairwise-distinct positions, the insertion at p is
/// found at exactly its unique index.
proof fn lemma_pos_index_some(ins: Seq<(usize, char)>, p: int, j: int)
    requires
        0 <= j < ins.len(),
        (ins[j].0 as int) == p,
        forall |a: int, b: int|
            0 <= a < b < ins.len() ==> ((ins[a].0 as int) != (ins[b].0 as int)),
    ensures
        ins_pos_index(ins, p) == j,
    decreases ins.len()
{
    if ins.len() == 0 {
        assert(false);
    } else {
        let last = ins.len() - 1;
        if (ins[last].0 as int) == p {
            assert(ins[last].0 as int == p);
            assert(ins_pos_index(ins, p) == last);
            if j == last {
            } else {
                assert(j < last);
                assert((ins[j].0 as int) != (ins[last].0 as int));
                assert(p != p);
                assert(false);
            }
        } else {
            let sub = ins.subrange(0, ins.len() - 1);
            assert forall |a: int, b: int| 0 <= a < b < sub.len() ==>
                ((sub[a].0 as int) != (sub[b].0 as int)) by {
                if 0 <= a && a < b && b < sub.len() {
                    vstd::seq::lemma_seq_subrange_index(ins, 0, ins.len() - 1, a);
                    vstd::seq::lemma_seq_subrange_index(ins, 0, ins.len() - 1, b);
                    assert(sub[a] == ins[a]);
                    assert(sub[b] == ins[b]);
                    assert((ins[a].0 as int) != (ins[b].0 as int));
                }
            }
            assert(j < ins.len() - 1);
            vstd::seq::lemma_seq_subrange_index(ins, 0, ins.len() - 1, j);
            assert(sub[j] == ins[j]);
            assert((sub[j].0 as int) == p);
            lemma_pos_index_some(sub, p, j);
            assert(ins_pos_index(ins, p) == ins_pos_index(sub, p));
        }
    }
}

/* ---------------------------------------------------------------
 * decode_bytes completeness glue lemmas (split/build/merge to the
 * full-precision decode model)
 * --------------------------------------------------------------- */

/// base_ascii_ok over [j, up) is exactly the pointwise all-ASCII fact.
proof fn lemma_base_ascii_from(input: Seq<u8>, up: int, j: int)
    requires
        0 <= j <= up,
    ensures
        base_ascii_ok(input, up, j)
            <==> (forall |m: int| j <= m < up ==> (input[m] < 0x80)),
    decreases up - j
{
    if j >= up {
        assert(base_ascii_ok(input, up, j)) by {
            reveal_with_fuel(base_ascii_ok, 1);
        }
        assert forall |m: int| j <= m < up implies (input[m] < 0x80) by {}
    } else {
        lemma_base_ascii_from(input, up, j + 1);
        assert(base_ascii_ok(input, up, j)
            == ((input[j] < 0x80) && base_ascii_ok(input, up, j + 1))) by {
            reveal_with_fuel(base_ascii_ok, 1);
        }
        // both directions by cases (propositionally, no unconditional
        // pointwise fact holds at a non-ASCII byte)
        if base_ascii_ok(input, up, j) {
            assert((input[j] < 0x80) && base_ascii_ok(input, up, j + 1));
            assert((input[j] < 0x80) && (forall |k: int|
                j + 1 <= k < up ==> (input[k] < 0x80)));
        } else {
            if (input[j] < 0x80) {
                assert(!(forall |k: int| j + 1 <= k < up
                    ==> (input[k] < 0x80)));
            }
        }
    }
}

/// The compute-friendly prefix copy equals the subrange view.
proof fn lemma_prefix_subrange(input: Seq<u8>, up: int, j: int, acc: Seq<u8>)
    requires
        0 <= j <= up,
        up <= (input.len() as int),
        (acc.len() as int) == j,
        forall |q: int| 0 <= q < j ==> (acc[q] == input[q]),
    ensures
        prefix_u8(input, up, j, acc) == (input.subrange(0, up)),
    decreases up - j
{
    if j >= up {
        assert(acc == (input.subrange(0, up))) by {
            vstd::seq::lemma_seq_subrange_len(input, 0, up);
            assert forall |q: int| 0 <= q < up
                implies (acc[q] == (input.subrange(0, up))[q]) by {
                vstd::seq::lemma_seq_subrange_index(input, 0, up, q);
            }
            vstd::seq::lemma_seq_ext_equal(acc, input.subrange(0, up));
        }
        assert(prefix_u8(input, up, j, acc) == acc) by {
            reveal_with_fuel(prefix_u8, 1);
        }
    } else {
        lemma_prefix_subrange(input, up, j + 1, acc.push(input[j]));
        assert(prefix_u8(input, up, j, acc)
            == prefix_u8(input, up, j + 1, acc.push(input[j]))) by {
            reveal_with_fuel(prefix_u8, 1);
        }
    }
}

/// The prefix-copy length bookkeeping for the merge lemmas.
proof fn lemma_prefix_u8_len(input: Seq<u8>, up: int, j: int, acc: Seq<u8>)
    requires
        0 <= j <= up,
        (acc.len() as int) == j,
    ensures
        ((prefix_u8(input, up, j, acc)).len() as int)
            == ((acc.len() as int) + (up - j)),
    decreases up - j
{
    if j >= up {
        assert(prefix_u8(input, up, j, acc) == acc) by {
            reveal_with_fuel(prefix_u8, 1);
        }
    } else {
        lemma_prefix_u8_len(input, up, j + 1, acc.push(input[j]));
        assert(prefix_u8(input, up, j, acc)
            == prefix_u8(input, up, j + 1, acc.push(input[j]))) by {
            reveal_with_fuel(prefix_u8, 1);
        }
    }
}

/// count_in over [0, p) on a subrange prefix equals ins_below over the
/// tail-index recursion (for non-negative positions both count entries
/// strictly below p).
proof fn lemma_count_below_hi(s: Seq<int>, hi: int, p: int)
    requires
        0 <= hi <= (s.len() as int),
        forall |m: int| 0 <= m < (s.len() as int) ==> (s[m] >= 0),
    ensures
        count_in(s.subrange(0, hi), 0, p) == ins_below(s, hi, p),
    decreases hi
{
    if hi == 0 {
        assert(count_in(s.subrange(0, 0), 0, p) == 0) by {
            reveal_with_fuel(count_in, 1);
        }
        assert(ins_below(s, 0, p) == 0) by {
            reveal_with_fuel(ins_below, 1);
        }
    } else {
        lemma_count_below_hi(s, hi - 1, p);
        let pre = s.subrange(0, hi - 1);
        let pre_pre = (s.subrange(0, hi)).subrange(0, hi - 1);
        vstd::seq::lemma_seq_subrange_len(s, 0, hi);
        vstd::seq::lemma_seq_subrange_len(s, 0, hi - 1);
        assert(pre_pre == pre) by {
            assert((pre_pre.len() as int) == hi - 1);
            assert((pre.len() as int) == hi - 1);
            assert forall |q: int| 0 <= q < hi - 1
                implies (pre_pre[q] == pre[q]) by {
                vstd::seq::lemma_seq_subrange_index(s, 0, hi, q);
                vstd::seq::lemma_seq_subrange_index(s, 0, hi - 1, q);
                vstd::seq::lemma_seq_subrange_index(
                    s.subrange(0, hi),
                    0,
                    hi - 1,
                    q,
                );
            }
            vstd::seq::lemma_seq_ext_equal(pre_pre, pre);
        }
        assert(count_in(s.subrange(0, hi), 0, p)
            == (count_in(pre_pre, 0, p)
                + (if 0 <= (s.subrange(0, hi))[hi - 1] < p { 1int } else { 0int }))) by {
            reveal_with_fuel(count_in, 1);
            vstd::seq::lemma_seq_subrange_index(s, 0, hi, hi - 1);
        }
        assert(ins_below(s, hi, p)
            == ((if s[hi - 1] < p { 1int } else { 0int }) + ins_below(s, hi - 1, p))) by {
            reveal_with_fuel(ins_below, 1);
        }
        vstd::seq::lemma_seq_subrange_index(s, 0, hi, hi - 1);
        // non-negativity makes the two membership tests agree
        if s[hi - 1] < p {
            assert(0 <= s[hi - 1] < p);
        } else {
            assert(!(0 <= s[hi - 1] < p));
        }
    }
}

/// The Seq::new positions view coincides with the ins_posns view.
proof fn lemma_positions_view(ins: Seq<(usize, char)>)
    ensures
        ins_positions(ins) == ins_posns(ins),
{
    lemma_ins_posns_len(ins);
    assert forall |q: int| 0 <= q < (ins.len() as int)
        implies (ins_positions(ins)[q] == ins_posns(ins)[q]) by {
        lemma_ins_posns_index(ins, q);
        assert(ins_positions(ins)[q] == (ins[q].0 as int));
    }
    vstd::seq::lemma_seq_ext_equal(ins_positions(ins), ins_posns(ins));
}

/// Align the fixed-view at_end scan with the tuple subrange scan (with
/// pairwise-distinct positions both find the same unique entry at p, and
/// both report -1 when none sits there).
proof fn lemma_at_end_rel(ins: Seq<(usize, char)>, hi: int, p: int)
    requires
        0 <= hi <= (ins.len() as int),
        forall |a: int, b: int| 0 <= a < b < (ins.len() as int)
            ==> ((ins[a].0 as int) != (ins[b].0 as int)),
    ensures
        ins_at_end(ins_posns(ins), ins_codes(ins), hi, p)
            == (if ins_pos_index(ins.subrange(0, hi), p) >= 0 {
                ins[ins_pos_index(ins.subrange(0, hi), p)].1 as int
            } else {
                -1
            }),
    decreases hi
{
    if hi == 0 {
        assert(ins_at_end(ins_posns(ins), ins_codes(ins), 0, p) == -1) by {
            reveal_with_fuel(ins_at_end, 1);
        }
        assert(ins_pos_index(ins.subrange(0, 0), p) == -1) by {
            reveal_with_fuel(ins_pos_index, 1);
            vstd::seq::lemma_seq_subrange_len(ins, 0, 0);
        }
    } else {
        let last = hi - 1;
        let pre = ins.subrange(0, last);
        vstd::seq::lemma_seq_subrange_len(ins, 0, hi);
        vstd::seq::lemma_seq_subrange_index(ins, 0, hi, last);
        assert((ins.subrange(0, hi))[last] == ins[last]);
        lemma_ins_posns_index(ins, last);
        lemma_ins_codes_index(ins, last);
        if (ins[last].0 as int) == p {
            // both scans stop at `last`
            assert(ins_at_end(ins_posns(ins), ins_codes(ins), hi, p)
                == ins_codes(ins)[last]) by {
                reveal_with_fuel(ins_at_end, 1);
            }
            assert(ins_pos_index(ins.subrange(0, hi), p) == last) by {
                assert forall |a: int, b: int| 0 <= a < b < hi
                    implies (((ins.subrange(0, hi))[a].0 as int)
                        != ((ins.subrange(0, hi))[b].0 as int)) by {
                    vstd::seq::lemma_seq_subrange_index(ins, 0, hi, a);
                    vstd::seq::lemma_seq_subrange_index(ins, 0, hi, b);
                }
                lemma_pos_index_some(ins.subrange(0, hi), p, last);
            }
        } else {
            // both scans step down one entry
            assert(ins_at_end(ins_posns(ins), ins_codes(ins), hi, p)
                == ins_at_end(ins_posns(ins), ins_codes(ins), last, p)) by {
                reveal_with_fuel(ins_at_end, 1);
            }
            lemma_at_end_rel(ins, last, p);
            assert(ins_pos_index(ins.subrange(0, hi), p)
                == ins_pos_index((ins.subrange(0, hi)).subrange(0, last), p)) by {
                reveal_with_fuel(ins_pos_index, 1);
                vstd::seq::lemma_seq_subrange_len(ins, 0, hi);
                // (ins.subrange(0, hi))[last] == ins[last] and its position is
                // not p, so the scan steps into the (0, last) prefix
            }
            assert((ins.subrange(0, hi)).subrange(0, last) == pre) by {
                vstd::seq::lemma_seq_subrange_len(ins, 0, last);
                assert(((ins.subrange(0, hi)).subrange(0, last)).len() as int == last);
                assert((pre.len() as int) == last);
                assert forall |q: int| 0 <= q < last
                    implies ((ins.subrange(0, hi)).subrange(0, last))[q] == pre[q] by {
                    vstd::seq::lemma_seq_subrange_index(ins, 0, hi, q);
                    vstd::seq::lemma_seq_subrange_index(ins, 0, last, q);
                    vstd::seq::lemma_seq_subrange_index(
                        ins.subrange(0, hi),
                        0,
                        last,
                        q,
                    );
                }
                vstd::seq::lemma_seq_ext_equal(
                    (ins.subrange(0, hi)).subrange(0, last),
                    pre,
                );
            }
        }
    }
}

/// At one output position the char-view merge and the int-view merge give
/// the same character (for pairwise-distinct insertions inside bounds).
proof fn lemma_merged_views_point(
    base: Seq<u8>,
    ins: Seq<(usize, char)>,
    p: int,
)
    requires
        0 <= p < (base.len() as int + ins.len() as int),
        forall |a: int, b: int| 0 <= a < b < (ins.len() as int)
            ==> ((ins[a].0 as int) != (ins[b].0 as int)),
        forall |j: int| 0 <= j < (ins.len() as int)
            ==> (0 <= (ins[j].0 as int)
                && ((ins[j].0 as int)
                    < (base.len() as int + ins.len() as int))),
    ensures
        ((merged_char_at(base, ins, p) as int)
            == merged_codes_at(base, ins_posns(ins), ins_codes(ins), p)),
{
    lemma_ins_posns_len(ins);
    lemma_ins_codes_len(ins);
    lemma_positions_view(ins);
    lemma_at_end_rel(ins, ins.len() as int, p);
    assert(ins.subrange(0, ins.len() as int) == ins) by {
        assert(ins.subrange(0, ins.len() as int).len() as int == ins.len() as int);
        assert forall |q: int| 0 <= q < (ins.len() as int)
            implies (ins.subrange(0, ins.len() as int))[q] == ins[q] by {
            vstd::seq::lemma_seq_subrange_index(ins, 0, ins.len() as int, q);
        }
        vstd::seq::lemma_seq_ext_equal(ins.subrange(0, ins.len() as int), ins);
    }
    let j = ins_pos_index(ins, p);
    assert(merged_char_at(base, ins, p)
        == (if j >= 0 { ins[j].1 } else { base[p
            - count_in(ins_positions(ins), 0, p)] as char })) by {
        reveal_with_fuel(merged_char_at, 1);
    }
    assert(merged_codes_at(base, ins_posns(ins), ins_codes(ins), p)
        == (if ins_at_end(ins_posns(ins), ins_codes(ins), ins.len() as int, p)
            >= 0 {
            ins_at_end(ins_posns(ins), ins_codes(ins), ins.len() as int, p)
        } else {
            base[p - ins_below(ins_posns(ins), ins.len() as int, p)] as int
        })) by {
        reveal_with_fuel(merged_codes_at, 1);
    }
    if j >= 0 {
        // the unique insertion at p on both sides
        assert(ins_at_end(ins_posns(ins), ins_codes(ins), ins.len() as int, p)
            == ins[j].1 as int);
        assert((ins[j].1 as int)
            == ins_at_end(ins_posns(ins), ins_codes(ins), ins.len() as int, p));
    } else {
        // no insertion at p anywhere in the tuple
        assert forall |k: int| 0 <= k < (ins.len() as int)
            implies ((ins[k].0 as int) != p) by {
            if (ins[k].0 as int) == p {
                lemma_pos_index_some(ins, p, k);
                assert(false);
            }
        }
        assert(ins_at_end(ins_posns(ins), ins_codes(ins), ins.len() as int, p)
            == -1);
        // the base positions coincide: count_in [0, p) == ins_below < p
        assert(count_in(ins_positions(ins), 0, p)
            == ins_below(ins_posns(ins), ins.len() as int, p)) by {
            lemma_count_below_hi(ins_posns(ins), ins.len() as int, p);
            assert(count_in(ins_posns(ins), 0, p)
                == count_in(
                    ins_posns(ins).subrange(0, ins.len() as int),
                    0,
                    p,
                )) by {
                assert(ins_posns(ins).subrange(0, ins.len() as int)
                    == ins_posns(ins)) by {
                    assert(ins_posns(ins).subrange(0, ins.len() as int).len() as int
                        == ins.len() as int);
                    assert forall |q: int| 0 <= q < (ins.len() as int)
                        implies (ins_posns(ins).subrange(0, ins.len() as int))[q]
                            == ins_posns(ins)[q] by {
                        vstd::seq::lemma_seq_subrange_index(
                            ins_posns(ins),
                            0,
                            ins.len() as int,
                            q,
                        );
                    }
                    vstd::seq::lemma_seq_ext_equal(
                        ins_posns(ins).subrange(0, ins.len() as int),
                        ins_posns(ins),
                    );
                }
            }
        }
    }
}

/// The merged length bookkeeping (the index lemma below needs it).
proof fn lemma_merge_all_len(
    base: Seq<u8>,
    posns: Seq<int>,
    codes: Seq<int>,
    p: int,
    acc: Seq<int>,
)
    requires
        0 <= p,
        p <= (base.len() as int + posns.len() as int),
        (acc.len() as int) == p,
    ensures
        ((merge_all_codes(base, posns, codes, p, acc)).len() as int)
            == (base.len() as int + posns.len() as int),
    decreases (base.len() as int + posns.len() as int) - p
{
    let total = (base.len() as int + posns.len() as int);
    if p >= total {
        assert(merge_all_codes(base, posns, codes, p, acc) == acc) by {
            reveal_with_fuel(merge_all_codes, 1);
        }
    } else {
        let acc2 = acc.push(merged_codes_at(base, posns, codes, p));
        lemma_merge_all_len(base, posns, codes, p + 1, acc2);
        assert(merge_all_codes(base, posns, codes, p, acc)
            == merge_all_codes(base, posns, codes, p + 1, acc2)) by {
            reveal_with_fuel(merge_all_codes, 1);
        }
    }
}

/// Positions already accumulated stay put across the recursion (the
/// untouched prefix of the final result equals the current accumulator).
proof fn lemma_merge_all_untouched(
    base: Seq<u8>,
    posns: Seq<int>,
    codes: Seq<int>,
    p: int,
    acc: Seq<int>,
    q: int,
)
    requires
        0 <= p,
        p <= (base.len() as int + posns.len() as int),
        (acc.len() as int) == p,
        0 <= q < (acc.len() as int),
    ensures
        (merge_all_codes(base, posns, codes, p, acc))[q] == acc[q],
    decreases (base.len() as int + posns.len() as int) - p
{
    let total = (base.len() as int + posns.len() as int);
    if p >= total {
        assert(merge_all_codes(base, posns, codes, p, acc) == acc) by {
            reveal_with_fuel(merge_all_codes, 1);
        }
    } else {
        let acc2 = acc.push(merged_codes_at(base, posns, codes, p));
        assert(merge_all_codes(base, posns, codes, p, acc)
            == merge_all_codes(base, posns, codes, p + 1, acc2)) by {
            reveal_with_fuel(merge_all_codes, 1);
        }
        vstd::seq::lemma_seq_push_index_different(
            acc,
            merged_codes_at(base, posns, codes, p),
            q,
        );
        assert(acc2[q] == acc[q]);
        lemma_merge_all_untouched(base, posns, codes, p + 1, acc2, q);
    }
}

/// Position q of the merged output is merged_codes_at at q.
proof fn lemma_merge_all_index(
    base: Seq<u8>,
    posns: Seq<int>,
    codes: Seq<int>,
    p: int,
    acc: Seq<int>,
    q: int,
)
    requires
        0 <= p,
        p <= q,
        q < (base.len() as int + posns.len() as int),
        (acc.len() as int) == p,
    ensures
        (merge_all_codes(base, posns, codes, p, acc))[q]
            == merged_codes_at(base, posns, codes, q),
    decreases (base.len() as int + posns.len() as int) - p
{
    let total = (base.len() as int + posns.len() as int);
    if p >= total {
        assert(false);
    } else {
        let acc2 = acc.push(merged_codes_at(base, posns, codes, p));
        assert(merge_all_codes(base, posns, codes, p, acc)
            == merge_all_codes(base, posns, codes, p + 1, acc2)) by {
            reveal_with_fuel(merge_all_codes, 1);
        }
        if q == p {
            assert(merge_all_codes(base, posns, codes, p, acc)[q]
                == merge_all_codes(base, posns, codes, p + 1, acc2)[q]) by {
                reveal_with_fuel(merge_all_codes, 1);
            }
            lemma_merge_all_untouched(base, posns, codes, p + 1, acc2, q);
            vstd::seq::lemma_seq_push_index_same(
                acc,
                merged_codes_at(base, posns, codes, p),
                q,
            );
        } else {
            // beyond position p, the recursion output is taken unchanged
            lemma_merge_all_index(base, posns, codes, p + 1, acc2, q);
            assert((merge_all_codes(base, posns, codes, p, acc))[q]
                == (merge_all_codes(base, posns, codes, p + 1, acc2))[q]);
        }
    }
}


/// Origin: punycode.rs:48-69 `decode_to_string`/`decode` for the external caller
/// (the str/String plumbing is ledger item 7), monomorphized to the byte core:
/// decode_split -> decode_build -> decode_merge, mirroring upstream's
/// `Decoder::default().decode::<u8, ExternalCaller>(input.as_bytes()).ok()?.collect()`.
/// Upstream doc (punycode.rs:42-46):
///   Convert Punycode to an Unicode String.
///   Return None on malformed input or overflow.
///   Overflow can only happen on inputs that take more than
///   63 encoded bytes, the DNS limit on domain name labels.
/// Upstream doc (punycode.rs:57-61):
///   Convert Punycode to Unicode.
///   Return None on malformed input or overflow.
///   Overflow can only happen on inputs that take more than
///   63 encoded bytes, the DNS limit on domain name labels.
/// (The input-length requires is the transcription of upstream's implicit
/// domain: punycode lengths are u32-based, and a base_len beyond u32::MAX
/// would silently truncate in upstream's `base_len as u32`; see the ledger.)
#[allow(deprecated)]
// Visibility opened to pub for harness (../harness/) consumption via #[path];
// upstream visibility of the underlying API is `pub` at the punycode module level.
pub fn decode_bytes(input: &[u8]) -> (r: Option<Vec<char>>)
    requires
        input.len() <= u32::MAX as usize,
    ensures
        r.is_some() ==> (exists |bl: int, ins: Seq<(usize, char)>|
            #![trigger (bl + ins.len())]
            (((bl >= 1 && last_delim(input@) == bl)
                || (last_delim(input@) <= 0 && bl == 0))
                && (forall |m: int| 0 <= m < bl ==> input@[m] < 0x80)
                && (ins.len() <= input@.len() - if bl >= 1 { bl + 1 } else { 0 })
                && (forall |a: int, b: int|
                    0 <= a < b < ins.len()
                        ==> ((ins[a].0 as int) != (ins[b].0 as int)))
                && (forall |j: int| 0 <= j < ins.len()
                    ==> (0 <= ins[j].0 as int
                        && (ins[j].0 as int) < bl + ins.len()))
                && ((r->0)@.len() == bl + ins.len())
                && (forall |p: int|
                    0 <= p < bl + ins.len()
                        ==> ((r->0)@[p]
                            == merged_char_at(input@.subrange(0, bl), ins, p))))),
        ({
            // existence and content completeness against the full decode
            // model (split reject, build reject, merged content)
            match decode_model(input@) {
                Option::None => r.is_none(),
                Option::Some(codesv) => (r.is_some()
                    && ((r->0)@.len() == codesv.len())
                    && (forall |q: int|
                        0 <= q < codesv.len()
                            ==> (((r->0)@[q] as int) == codesv[q]))),
            }
        }),
{
    let split = decode_split(input);
    match split {
        Result::Err(()) => {
            proof {
                // a non-ASCII base: the model's first reject arm
                let p_d = last_delim(input@);
                assert(p_d >= 1) by {
                    // the reject witness lives strictly below the
                    // delimiter position, so the split was not trivial
                }
                assert(!base_ascii_ok(input@, p_d, 0)) by {
                    lemma_base_ascii_from(input@, p_d, 0);
                }
                assert(decode_model(input@) == Option::None) by {
                    reveal(decode_model);
                }
            }
            Option::None
        }
        Result::Ok((base_len, ext_start)) => {
            let built = decode_build(input, base_len, ext_start);
            match built {
                Result::Err(()) => {
                    proof {
                        // build-model reject: the model's second arm
                        let p_d = last_delim(input@);
                        let bl = base_len as int;
                        assert(base_ascii_ok(input@, bl, 0)) by {
                            lemma_base_ascii_from(input@, bl, 0);
                        }
                        let bm = build_model(
                            input@,
                            ext_start as int,
                            bl,
                            INITIAL_N as int,
                            INITIAL_BIAS as int,
                            0,
                            Seq::empty(),
                            Seq::empty(),
                        );
                        assert(bm == Option::None);
                        assert(decode_model(input@) == Option::None) by {
                            reveal(decode_model);
                            if p_d >= 1 {
                                assert(bl == p_d);
                                assert(base_ascii_ok(input@, p_d, 0));
                            } else {
                                assert(bl == 0);
                            }
                        }
                    }
                    Option::None
                }
                Result::Ok(ins) => {
                    /* Origin Rust: decode(...).ok()?.collect() -- the merge of base
                       and insertions into the output vector */
                    let base = &input[..base_len];
                    let out = decode_merge(base, &ins);
                    proof {
                        let bl = base_len as int;
                        let insv = ins@;
                        assert(base@ == input@.subrange(0, bl));
                        assert(last_delim(input@) >= 1
                            ==> (bl == last_delim(input@)));
                        assert(last_delim(input@) <= 0 ==> bl == 0);
                        if bl >= 1 {
                            assert(ext_start == base_len + 1);
                            assert(insv.len() <= input@.len() - ext_start as int);
                            assert(insv.len() <= input@.len() - bl - 1);
                        } else {
                            assert(ext_start == 0);
                            assert(insv.len() <= input@.len());
                        }
                        // full-model completeness glue:
                        // split all-ASCII, build views, merge content
                        let p_d = last_delim(input@);
                        assert(base_ascii_ok(input@, bl, 0)) by {
                            lemma_base_ascii_from(input@, bl, 0);
                        }
                        lemma_prefix_subrange(
                            input@,
                            bl,
                            0,
                            Seq::empty(),
                        );
                        lemma_prefix_u8_len(input@, bl, 0, Seq::empty());
                        let base_s = prefix_u8(input@, bl, 0, Seq::empty());
                        assert(base_s == input@.subrange(0, bl));
                        assert((base_s.len() as int) == bl);
                        let P = ins_posns(insv);
                        let C = ins_codes(insv);
                        let bm = build_model(
                            input@,
                            ext_start as int,
                            bl,
                            INITIAL_N as int,
                            INITIAL_BIAS as int,
                            0,
                            Seq::empty(),
                            Seq::empty(),
                        );
                        assert(bm == Option::Some((P, C)));
                        let M = merge_all_codes(base_s, P, C, 0, Seq::empty());
                        assert(decode_model(input@) == Option::Some(M)) by {
                            reveal(decode_model);
                            if p_d >= 1 {
                                assert(bl == p_d);
                                assert(base_ascii_ok(input@, p_d, 0));
                            } else {
                                assert(bl == 0);
                            }
                        }
                        // lengths match through the merge bookkeeping
                        lemma_ins_posns_len(insv);
                        lemma_ins_codes_len(insv);
                        lemma_merge_all_len(base_s, P, C, 0, Seq::empty());
                        assert((M.len() as int) == bl + insv.len());
                        assert((out@.len() as int) == (M.len() as int));
                        // per-index content through the views bridge
                        assert forall |q: int|
                            0 <= q < (M.len() as int)
                            implies ((out@[q] as int) == M[q]) by {
                            assert(out@[q] == merged_char_at(base@, insv, q));
                            assert((merged_char_at(base@, insv, q) as int)
                                == merged_codes_at(base@, P, C, q)) by {
                                lemma_merged_views_point(base@, insv, q);
                            }
                            lemma_merge_all_index(
                                base_s,
                                P,
                                C,
                                0,
                                Seq::empty(),
                                q,
                            );
                        }
                    }
                    Option::Some(out)
                }
            }
        }
    }
}

/* ============================================================
 * Internal-caller decode (punycode.rs:71-157, u8 and char code units)
 *
 * Ledger (upstream doc of the marker trait, punycode.rs:75-83):
 * "Internal callers don't need [the base-ASCII] check, because the
 * internal code calls the decoder only with lower-case inputs"; the u8
 * code unit still accepts the upper-case digit alphabet (digit() is on
 * the code-unit type, not the caller), and outputs basic code units
 * ASCII-lower-cased (char_ascii_lower_case of the u8 unit is
 * to_ascii_lowercase); the char code unit is the lower-case-only
 * variant (punycode.rs:132-157: digit accepts '0'..='9' and 'a'..='z'
 * only, is_ascii is statically true, char_ascii_lower_case is the
 * identity).
 *
 * Consumption sites: uts46.rs:1156 (u8 form over the ASCII punycode
 * prefix payload of an ASCII label) and uts46.rs:1310 (char form over
 * the mapped label content after an "xn--" prefix; the preceding pass
 * at uts46.rs:1264-1273 has already turned every non-ASCII char into
 * U+FFFD, so the char-form domain is ASCII). The requires below
 * transcribe exactly those caller-side domains (the u8-form input is
 * the ASCII prefix segment by construction; the char-form input has
 * passed the ASCII marking pass).
 * ============================================================ */

/// ASCII lower-casing on int code values: a strict no-op outside the
/// upper-case letter range [0x41, 0x5A]. (Punycode insertion code points
/// are always >= INITIAL_N = 0x80, so this map only ever rewrites basic
/// code-unit positions.)
pub open spec fn lower_ascii_letter(v: int) -> int {
    if 0x41 <= v <= 0x5A {
        v + 0x20
    } else {
        v
    }
}

/// The byte view of an all-ASCII char sequence (used to state the
/// char-form contract in terms of the byte-space decode model; on the
/// ASCII domain the code units carry the same values).
pub open spec fn ascii_view(s: Seq<char>) -> (r: Seq<u8>) {
    Seq::new(s.len(), |j: int| (s[j] as u32) as u8)
}

/// The code-unit-level difference of the char form on the ASCII domain:
/// an upper-case ASCII letter after the last '-' (the char unit's
/// digit() rejects exactly those in the extended region; every other
/// ASCII byte has the same digit verdict on both code units).
pub open spec fn ext_has_upper(v: Seq<u8>) -> bool {
    let ld = last_delim(v);
    exists |k: int| ld < k < v.len() && 0x41 <= v[k] as int && v[k] as int <= 0x5A
}

/// Origin: punycode.rs:159-264 Decoder::decode monomorphized to
/// `<u8, InternalCaller>` as consumed at uts46.rs:1156: the base-ASCII
/// branch cannot fire on this domain (the requires), and the merged
/// basic code units are ASCII-lower-cased (u8 char_ascii_lower_case);
/// the extended-part behavior (digit table, delimiter split, insertions)
/// is caller-independent. Executed as the external decode phases plus
/// the lower-casing map on the result.
pub fn decode_bytes_internal(input: &[u8]) -> (r: Option<Vec<char>>)
    requires
        input.len() <= u32::MAX as usize,
        forall |i: int| #![trigger input[i]] 0 <= i < input.len() ==>
            (input[i] as int) < 0x80,
    ensures
        match decode_model(input@) {
            Option::None => r.is_none(),
            Option::Some(codes) => (r.is_some()
                && (r->0)@.len() == codes.len()
                && (forall |q: int| 0 <= q < codes.len()
                    ==> (((r->0)@[q] as int) == lower_ascii_letter(codes[q])))),
        },
{
    let ext = decode_bytes(input);
    match ext {
        Option::None => Option::None,
        Option::Some(mut out) => {
            proof {
                assert(decode_model(input@).is_some());
                assert(match decode_model(input@) {
                    Option::None => false,
                    Option::Some(codes) => (out@.len() == codes.len()
                        && (forall |q: int| 0 <= q < codes.len()
                            ==> ((out@[q] as int) == codes[q]))),
                });
            }
            let ghost codes = decode_model(input@)->0;
            let mut q: usize = 0;
            while q < out.len()
                invariant
                    q <= out.len(),
                    codes.len() == out@.len() as int,
                    forall |j: int| 0 <= j < q ==>
                        (out@[j] as int) == lower_ascii_letter(codes[j]),
                    forall |j: int| q <= j < out@.len() ==>
                        (out@[j] as int) == codes[j],
                decreases out.len() - q
            {
                let cv = out[q] as u32;
                if 0x41 <= cv && cv <= 0x5A {
                    assert(cv + 0x20 <= 0x7A);
                    let lo = (cv + 0x20) as u8 as char;
                    assert(lo as u32 == cv + 0x20);
                    assert(cv + 0x20 <= 0x5A + 0x20);
                    assert((lo as int) == (out@[q as int] as int) + 0x20);
                    assert((lo as int) == lower_ascii_letter(codes[q as int]));
                    out.set(q, lo);
                } else {
                    assert((out@[q as int] as int)
                        == lower_ascii_letter(codes[q as int])) by {
                        assert(!(0x41 <= codes[q as int] && codes[q as int] <= 0x5A));
                    }
                }
                q += 1;
            }
            Option::Some(out)
        }
    }
}

/// Origin: punycode.rs:159-264 Decoder::decode monomorphized to
/// `<char, InternalCaller>` as consumed at uts46.rs:1310: the char code
/// unit's digit() is the lower-case-only table (punycode.rs:143-147; the
/// upper-case branch is commented out upstream with "not needed if no
/// public input"), is_ascii is statically true (the base-ASCII branch of
/// the decode cannot fire on this code-unit type), and
/// char_ascii_lower_case is the identity (basic code units pass through
/// verbatim). On the ASCII domain (the uts46 call site: the marking pass
/// at uts46.rs:1264-1273 has replaced every non-ASCII char before the
/// decode), the char-unit behavior equals the byte-unit external decode
/// of the byte view exactly when the extended part (after the last
/// delimiter) contains no upper-case ASCII letter; otherwise the first
/// upper-case letter fails digit() and the decode is an error.
pub fn decode_char_internal(input: &[char]) -> (r: Option<Vec<char>>)
    requires
        input.len() <= u32::MAX as usize,
        forall |i: int| #![trigger input[i]] 0 <= i < input.len() ==>
            ((input[i] as u32) < 0x80),
    ensures
    ({
        let v = ascii_view(input@);
        if ext_has_upper(v) {
            r.is_none()
        } else {
            match decode_model(v) {
                Option::None => r.is_none(),
                Option::Some(codes) => (r.is_some()
                    && (r->0)@.len() == codes.len()
                    && (forall |q: int| 0 <= q < codes.len()
                        ==> (((r->0)@[q] as int) == codes[q]))),
            }
        }
    }),
{
    proof {
        // View facts from the Seq::new definition: the byte view has
        // the input length and per-index byte values.
        lemma_seq_new_len(input@.len(), |j: int| (input@[j] as u32) as u8);
        let v = ascii_view(input@);
        assert(v.len() == input@.len() as int);
        assert forall |k: int| #![trigger v[k]] 0 <= k < v.len()
            implies (v[k] == (input@[k] as u32) as u8) by {
            vstd::seq::lemma_seq_new_index(
                input@.len(),
                |j: int| (input@[j] as u32) as u8,
                k,
            );
        }
        assert(v.len() == input.len() as int);
    }
    // Pre-scan pass 1: the last '-' index (usize sentinel = len when
    // none).
    let v_len = input.len();
    let mut ld: usize = v_len;
    let mut k = 0usize;
    while k < v_len
        invariant
            k <= v_len,
            v_len == input.len(),
            ld <= v_len,
            ld < v_len ==> input@[ld as int] == '-',
            ld != v_len ==> (ld as int) < k,
            forall |j: int| 0 <= j < k ==>
                ((input@[j] == '-') ==> (ld != v_len)
                    && (j as int) <= (ld as int)),
        decreases v_len - k
    {
        if input[k] == '-' {
            ld = k;
        }
        k += 1;
    }
    proof {
        let v = ascii_view(input@);
        // last_delim(v) is the maximal '-' index (or -1 with no dash at
        // all): bridge the scan sentinel to the model's position.
        lemma_last_delim_max(v);
        lemma_last_delim_range(v);
        if ld < v_len {
            assert(input@[ld as int] == '-');
            assert(v[ld as int] == (input@[ld as int] as u32) as u8);
            assert(v[ld as int] == 0x2D);
            assert((ld as int) < v.len());
            // Case analysis on the max-lemma's two arms:
            // a dash exists (at ld), so the no-dash arm is impossible.
            if last_delim(v) == -1 {
                assert(v[ld as int] != 0x2D);
                assert(false);
            }
            assert(last_delim(v) >= 0);
            assert(v[last_delim(v)] == 0x2D);
            assert(last_delim(v) < v.len());
            assert(v[last_delim(v)] == (input@[last_delim(v)] as u32) as u8);
            // the scan found no dash beyond ld, so the model's position
            // cannot be past ld;
            if (last_delim(v) as int) > (ld as int) {
                assert(input@[last_delim(v)] == '-');
                assert(last_delim(v) <= ld as int);
                assert(false);
            }
            // and the model's position is a dash, so it cannot be
            // before ld (the scan would have set ld beyond it).
            assert(last_delim(v) == ld as int);
        } else {
            // ld == v_len: the scan found no dash anywhere.
            assert forall |j: int| 0 <= j < v.len()
                implies (!(input@[j] == '-')) by {
                assert(ld == v_len);
            }
            assert forall |j: int| #![trigger v[j]] 0 <= j < v.len()
                implies (v[j] != 0x2D) by {
                assert(v[j] == (input@[j] as u32) as u8);
                assert(!(input@[j] == '-'));
                assert((input@[j] as u32) != 0x2D);
            }
            if last_delim(v) >= 0 {
                assert(v[last_delim(v)] == 0x2D);
                assert(false);
            }
            assert(last_delim(v) == -1);
        }
    }
    let ext_from: usize = if ld < v_len { ld + 1 } else { 0 };
    proof {
        // The region scanned below is exactly the model's extended
        // region (strictly after the last delimiter, or the whole
        // input when the model sees none).
        let v = ascii_view(input@);
        assert forall |k: int| #![trigger v[k]] 0 <= k < v.len() implies
            (last_delim(v) < k <==> ext_from as int <= k) by {
            if ld < v_len {
                assert(last_delim(v) == ld as int);
                assert(ext_from as int == ld as int + 1);
            } else {
                assert(last_delim(v) == -1);
                assert(ext_from == 0);
            }
        }
    }
    // Pre-scan pass 2: the first upper-case ASCII letter in the
    // extended region (usize sentinel = v_len when none), which the
    // char code unit's digit() rejects; every other ASCII byte has
    // the same digit verdict on both code units.
    let ghost v0 = ascii_view(input@);
    let mut uh: usize = v_len;
    let mut k2 = ext_from;
    while k2 < v_len
        invariant
            ext_from <= k2 <= v_len,
            v_len == input.len(),
            v0 == ascii_view(input@),
            v0.len() == v_len as int,
            forall |i: int| #![trigger input[i]] 0 <= i < input.len()
                ==> ((input[i] as u32) < 0x80),
            uh <= v_len,
            uh < v_len ==> (ext_from as int) <= (uh as int),
            uh < v_len ==> (0x41 <= v0[uh as int] as int
                && v0[uh as int] as int <= 0x5A),
            uh < v_len ==> (uh as int) <= ext_from as int
                || forall |j: int| ext_from as int <= j < uh as int
                    ==> (!(0x41 <= v0[j] as int && v0[j] as int <= 0x5A)),
            uh == v_len ==> (forall |j: int| ext_from as int <= j < k2 as int
                ==> (!(0x41 <= v0[j] as int && v0[j] as int <= 0x5A))),
        decreases v_len - k2
    {
        let cv = input[k2] as u32;
        if uh == v_len && 0x41 <= cv && cv <= 0x5A {
            proof {
                assert(0x41 <= input@[k2 as int] as int
                    && input@[k2 as int] as int <= 0x5A);
                assert(v0[k2 as int] == (input@[k2 as int] as u32) as u8);
                assert(0x41 <= v0[k2 as int] as int
                    && v0[k2 as int] as int <= 0x5A);
            }
            uh = k2;
        } else {
            proof {
                if uh != v_len {
                    // already found: the no-upper clause up to uh is
                    // carried over; nothing to re-establish
                } else {
                    assert(!(0x41 <= cv && cv <= 0x5A));
                    assert((input@[k2 as int] as u32) < 0x100);
                    assert(v0[k2 as int] == (input@[k2 as int] as u32) as u8);
                    assert((v0[k2 as int] as int)
                        == (input@[k2 as int] as u32));
                    assert(!(0x41 <= (v0[k2 as int] as int)
                        && (v0[k2 as int] as int) <= 0x5A));
                }
            }
        }
        k2 += 1;
    }
    proof {
        // The scan sentinel uh decides ext_has_upper, through the region
        // equivalence proved above.
        let v = ascii_view(input@);
        assert(v == v0);
        if uh < v_len {
            assert((ext_from as int) <= (uh as int));
            assert(last_delim(v) < uh as int) by {
                if ld < v_len {
                    assert(last_delim(v) == ld as int);
                    assert(last_delim(v) < uh as int);
                } else {
                    assert(last_delim(v) == -1);
                    assert(last_delim(v) < uh as int);
                }
            }
            assert(0x41 <= v[uh as int] as int && v[uh as int] as int <= 0x5A);
            assert(ext_has_upper(v));
        } else {
            assert forall |k: int| last_delim(v) < k < v.len()
                implies (!(0x41 <= v[k] as int && v[k] as int <= 0x5A)) by {
                assert(ext_from as int <= k);
                assert(ext_from as int <= k && k < v.len());
            }
            assert(!ext_has_upper(v));
        }
    }
    if uh < v_len {
        return Option::None;
    }
    // Byte view construction: input is all-ASCII, so the byte view is
    // value-faithful, and the external decode core over the view is
    // the char-unit behavior on this domain (the base passes through
    // verbatim - char_ascii_lower_case is the identity on char - and
    // the lower-case digits have byte-unit-agreeing verdicts).
    let mut view: Vec<u8> = Vec::new();
    let mut k3 = 0usize;
    while k3 < v_len
        invariant
            k3 <= v_len,
            v_len == input.len(),
            view@.len() == k3 as int,
            forall |i: int| #![trigger input[i]] 0 <= i < input.len()
                ==> ((input[i] as u32) < 0x80),
            forall |j: int| 0 <= j < k3 ==>
                (view@[j] == (input@[j] as u32) as u8),
        decreases v_len - k3
    {
        proof {
            assert((input@[k3 as int] as u32) < 0x80);
            assert(k3 < input.len());
        }
        view.push((input[k3] as u32) as u8);
        proof {
            let ghost pre = view@.subrange(0, view@.len() as int - 1);
            assert(view@[k3 as int] == (input@[k3 as int] as u32) as u8);
        }
        k3 += 1;
    }
    proof {
        let v = ascii_view(input@);
        assert(view@ == v) by {
            assert(view@.len() == v.len());
            assert forall |j: int| 0 <= j < v.len() implies
                (view@[j] == v[j]) by {
                assert(view@[j] == (input@[j] as u32) as u8);
                assert(v[j] == (input@[j] as u32) as u8);
            }
        }
        assert(view@ == ascii_view(input@));
    }
    proof {
        // decode_bytes over the view carries length and the model
        // contract of the byte face; view@ == v makes the outer
        // ensures the same contract stated on v.
        assert(view.len() == input.len());
        assert(view.len() <= u32::MAX as usize);
    }
    decode_bytes(&view)
}
/* ============================================================
 * Encode (punycode.rs:346-455, the external-caller path)
 * ============================================================ */

/// Origin: punycode.rs:346-349 `PunycodeEncodeError`. The Sink variant is
/// declared for API fidelity but is unreachable through the Vec<char> sink
/// (ledger item 5); the From<core::fmt::Error> impl (punycode.rs:351-355) is
/// tied to the fmt::Write sink that is not modeled.
pub enum PunycodeEncodeError {
    Overflow,
    Sink,
}

/// Origin: punycode.rs:429-445, the delta-digit emission loop of
/// encode_into's inner scan (`let mut q = delta; let mut k = BASE; loop { ... }`
/// plus the trailing final digit at punycode.rs:445), extracted as a helper so
/// the emission has a single verified location: every appended char is a
/// value_to_digit symbol, and all earlier positions are untouched.
fn encode_digits(qv0: u32, bias: u32, output: &mut Vec<char>)
    requires
        (bias as int) <= 614,
    ensures
        (forall |q: int| 0 <= q < old(output)@.len()
            ==> (final(output)@[q] == old(output)@[q])),
        (final(output)@.len() >= old(output)@.len()),
        (forall |p: int|
            old(output)@.len() <= p < final(output)@.len()
                ==> is_digit_char(final(output)@[p])),
        ({
            let em = emit_digits_model(
                qv0 as int,
                36,
                bias as int,
                codes_of(old(output)@),
            );
            ((final(output)@.len() as int == em.len())
                && (forall |p: int| 0 <= p < em.len()
                    ==> ((final(output)@[p] as int) == em[p])))
        }),
{
    let ghost emc =
        emit_digits_model(qv0 as int, 36, bias as int, codes_of(old(output)@));
    let mut qv = qv0;
    let mut k: u32 = BASE;
    let mut t: u32 = if k <= bias {
        T_MIN
    } else if k >= bias + T_MAX {
        T_MAX
    } else {
        k - bias
    };
    let ghost mut kit: int = 0;
    while qv >= t
        invariant
            (bias as int) <= 614,
            (t as int) == t_for(k as int, bias as int),
            1 <= (t as int) <= 26,
            (qv as int) >= 0,
            kit >= 0,
            (k as int) == 36 + 36 * kit,
            (powi(10, kit) * (qv as int) <= 4294967295),
            (output@.len() as int) >= old(output)@.len() as int,
            emit_digits_model(qv as int, k as int, bias as int, codes_of(output@)) == emc,
            (forall |q2: int| 0 <= q2 < old(output)@.len() as int
                ==> (output@[q2] == old(output)@[q2])),
            (forall |p: int|
                old(output)@.len() as int <= p < output@.len()
                    ==> is_digit_char(output@[p])),
        decreases (qv as int)
    {
        let ghost t_pre_g = t as int;
        proof {
            // value = t + ((q - t) % (BASE - t)) stays within 0..=35, so
            // value_to_digit's panic arm is dead at this call
            assert((qv as int) >= (t as int));
            assert((t as int) >= 1);
            assert(((BASE - t) as int) >= 10);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                (qv - t) as int,
                (BASE - t) as int,
            );
            assert(0 <= ((qv - t) as int) % ((BASE - t) as int));
            assert(((qv - t) as int) % ((BASE - t) as int) < ((BASE - t) as int));
            assert((t as int) + (((qv - t) as int) % ((BASE - t) as int)) <= 35);
        }
        let value = t + ((qv - t) % (BASE - t));
        /* Origin Rust: output.write_char(value_to_digit(value))?; */
        let dch = value_to_digit(value);
        let ghost qv_pre = qv;
        let ghost k_pre = k;
        let ghost pre_push = output@;
        proof {
            // the model threshold schedule is the exec's own t recompute
            assert(t as int == t_for(k as int, bias as int)) by {
                reveal(t_for);
                assert(T_MIN as int == 1);
                assert(T_MAX as int == 26);
                assert((bias + T_MAX) as int == bias as int + 26);
                assert((k + 0) as int == k as int);
            };
            assert(value as int
                == t_for(k as int, bias as int)
                    + (qv as int - t_for(k as int, bias as int))
                        % (36 - t_for(k as int, bias as int)));
            // one unfold of the emission model through this iteration
            lemma_codes_of_push(pre_push, dch);
            assert(emit_digits_model(qv as int, k as int, bias as int, codes_of(pre_push))
                == emit_digits_model(
                    (qv as int - t as int) / (36 - t as int),
                    k as int + 36,
                    bias as int,
                    codes_of(pre_push).push(digit_char(value as int)),
                )) by {
                reveal_with_fuel(emit_digits_model, 1);
                assert((qv as int) >= t as int);
                assert((value as int) == t as int
                    + ((qv as int - t as int) % (36 - t as int)));
                assert(dch as int == digit_char(value as int));
            };
        }
        output.push(dch);
        proof {
            assert(output@ == pre_push.push(dch));
            assert(is_digit_char(dch));
            assert(dch == output@[pre_push.len() as int]);
            assert(output@.len() == pre_push.len() + 1);
            assert(output@ == pre_push.push(dch));
            assert(dch as int == digit_char(value as int));
            assert(codes_of(output@) == codes_of(pre_push).push(digit_char(value as int)));
            assert(emit_digits_model(qv_pre as int, k_pre as int, bias as int, codes_of(pre_push))
                == emit_digits_model(
                    (qv_pre as int - t_pre_g) / (36 - t_pre_g),
                    k_pre as int + 36,
                    bias as int,
                    codes_of(output@),
                ));
            assert forall |p: int|
                old(output)@.len() as int <= p < output@.len() implies
                is_digit_char(output@[p]) by {
                if p == pre_push.len() as int {
                    assert(output@[p] == dch);
                } else {
                    assert(0 <= p);
                    assert(p < pre_push.len());
                    vstd::seq::lemma_seq_push_index_different(pre_push, dch, p);
                    assert(output@[p] == pre_push[p]);
                }
            }
            assert forall |q2: int| 0 <= q2 < old(output)@.len() as int implies
                (output@[q2] == old(output)@[q2]) by {
                vstd::seq::lemma_seq_push_index_different(pre_push, dch, q2);
                assert(output@[q2] == pre_push[q2]);
            }
            // kit bookkeeping: kit <= 9 bounds k, and qv only shrinks
            if kit >= 10 {
                lemma_powers();
                lemma_powi_mono(10, 10, kit);
                assert(powi(10, 10) <= powi(10, kit));
                assert(qv_pre as int >= t as int);
                assert(1 <= qv_pre as int);
                assert(powi(10, kit) * (qv_pre as int) <= 4294967295);
                vstd::arithmetic::mul::lemma_mul_is_commutative(
                    powi(10, kit),
                    qv_pre as int,
                );
                assert((qv_pre as int) * powi(10, kit) <= 4294967295);
                vstd::arithmetic::mul::lemma_mul_inequality(
                    1,
                    qv_pre as int,
                    powi(10, kit),
                );
                assert(1 * powi(10, kit) <= (qv_pre as int) * powi(10, kit));
                assert(powi(10, kit) <= 4294967295);
                assert(powi(10, 10) <= 4294967295);
                assert(false);
            }
            assert(kit <= 9);
            assert((k as int) + 36 <= 396);
        }
        qv = (qv - t) / (BASE - t);
        proof {
            lemma_emit_step(kit, qv_pre as int, t as int, qv as int);
            assert(powi(10, kit + 1) * (qv as int) <= 4294967295);
            lemma_emit_dec(qv_pre as int, t as int, qv as int);
            assert((qv as int) < (qv_pre as int));
        }
        k += BASE;
        proof {
            kit = kit + 1;
            assert(k as int == k_pre + 36);
            assert(qv as int == (qv_pre as int - t_pre_g) / (36 - t_pre_g));
            assert(emit_digits_model(qv as int, k as int, bias as int, codes_of(output@)) == emc);
        }
        /* Origin Rust: the loop's own t recomputation, hoisted to the tail */
        t = if k <= bias {
            T_MIN
        } else if k >= bias + T_MAX {
            T_MAX
        } else {
            k - bias
        };
    }
    // the final digit: qv < t <= 26, still inside the digit domain
    proof {
        assert((qv as int) < (t as int));
        assert((t as int) <= 26);
        assert((qv as int) <= 35);
        assert(t as int == t_for(k as int, bias as int)) by {}
    }
    /* Origin Rust: output.write_char(value_to_digit(q))?; */
    let dch2 = value_to_digit(qv);
    let ghost pre_push2 = output@;
    output.push(dch2);
    proof {
        assert(output@ == pre_push2.push(dch2));
        assert(is_digit_char(dch2));
        assert(output@.len() == pre_push2.len() + 1);
        assert(dch2 as int == digit_char(qv as int));
        // the model's final digit: one last unfold of emc (evaluated at the
        // pre-push buffer, reached through the push congruence)
        assert(emit_digits_model(qv as int, k as int, bias as int, codes_of(pre_push2))
            == codes_of(pre_push2).push(digit_char(qv as int))) by {
            reveal_with_fuel(emit_digits_model, 1);
            assert((qv as int) < t as int);
        };
        assert(emit_digits_model(qv as int, k as int, bias as int, codes_of(pre_push2)) == emc);
        lemma_codes_of_push(pre_push2, dch2);
        assert(codes_of(output@) == codes_of(pre_push2).push(digit_char(qv as int)));
        assert(codes_of(output@) == emc);
        lemma_codes_of_len(output@);
        assert(output@.len() as int == emc.len());
        assert forall |p: int| 0 <= p < emc.len() implies
            ((output@[p] as int) == emc[p]) by {
            lemma_codes_of_index(output@, p);
            assert(codes_of(output@)[p] == output@[p] as int);
            assert(output@[p] as int == codes_of(output@)[p]);
            vstd::seq::lemma_seq_ext_equal(codes_of(output@), emc);
        }
        assert forall |p: int|
            old(output)@.len() as int <= p < output@.len() implies
            is_digit_char(output@[p]) by {
            if p == pre_push2.len() as int {
                assert(output@[p] == dch2);
            } else {
                assert(0 <= p);
                assert(p < pre_push2.len());
                vstd::seq::lemma_seq_push_index_different(pre_push2, dch2, p);
                assert(output@[p] == pre_push2[p]);
            }
        }
        assert forall |q2: int| 0 <= q2 < old(output)@.len() as int implies
            (output@[q2] == old(output)@[q2]) by {
            vstd::seq::lemma_seq_push_index_different(pre_push2, dch2, q2);
            assert(output@[q2] == pre_push2[q2]);
        }
    }
}

/// Origin: punycode.rs:357-455 `encode_into<I, W, C>`, monomorphized for the
/// external caller (C = ExternalCaller: the overflow checks below), the
/// `&[char]` input (upstream `I: Iterator<Item = char> + Clone` is used only
/// through full re-scans, so a slice index loop is its faithful form), and the
/// Vec<char> sink in place of `W: core::fmt::Write` (pushes never fail).
/// (No upstream rustdoc on encode_into itself.)
fn encode_into_chars(
    input: &[char],
    output: &mut Vec<char>,
) -> (r: Result<(), PunycodeEncodeError>)
    requires
        input.len() <= u32::MAX as usize,
    ensures
        (forall |q: int| #![trigger final(output)@[q]] 0 <= q < old(output)@.len()
            ==> (final(output)@[q] == old(output)@[q])),
        (final(output)@.len() >= old(output)@.len()),
        (r.is_ok() || (r matches Err(PunycodeEncodeError::Overflow))),
        ({
            // The full-precision emit model, anchored at the initial buffer:
            // the exec appends exactly the model's emission.
            let m = encode_full_model(input@, old(output)@);
            (r.is_err() <==> m.is_none())
                && (r.is_ok() ==> ({
                    let em = m->0;
                    ((final(output)@.len() as int == em.len())
                        && (forall |p: int| 0 <= p < em.len()
                            ==> ((final(output)@[p] as int) == em[p])))
                }))
        }),
{
    let ghost O = old(output)@.len();
    let ghost cs_m = codes_of(input@);
    let ghost O0c = codes_of(old(output)@);
    let ghost apc = ascii_prefix_model(cs_m, 0, O0c);
    /* Origin Rust: let (mut input_length, mut basic_length) = (0u32, 0);
       for c in input.clone() { input_length = input_length.checked_add(1)...;
       if c.is_ascii() { output.write_char(c)?; basic_length += 1 } }
       -- input_length is the slice length (guaranteed <= u32::MAX by the
       requires, so upstream's checked_add loop would count exactly it) */
    let input_length = input.len() as u32;
    let mut basic_length: u32 = 0;
    let mut q = 0usize;
    while q < input.len()
        invariant
            q <= input.len(),
            input.len() <= u32::MAX as usize,
            (O == old(output)@.len()),
            (O >= 0),
            (output@.len() as int) == (O + count_ascii_prefix(input@, q as int)),
            (basic_length as int) == count_ascii_prefix(input@, q as int),
            (basic_length as int) <= q as int,
            forall |p: int| 0 <= p < O ==> (output@[p] == old(output)@[p]),
            forall |p: int| O <= p < output@.len() ==> ((output@[p] as int) < 128),
            cs_m == codes_of(input@),
            O0c == codes_of(old(output)@),
            apc == ascii_prefix_model(cs_m, 0, O0c),
            ascii_prefix_model(cs_m, q as int, codes_of(output@)) == apc,
        decreases input.len() - q
    {
        let ghost bout_pre = output@;
        let c = input[q];
        /* Origin Rust: if c.is_ascii() { output.write_char(c)?; basic_length += 1 } */
        if (c as u32) < 128 {
            proof {
                assert((input@[q as int] as int) < 128);
                lemma_count_ascii_step(input@, q as int);
            }
            output.push(c);
            proof {
                // the model's basics accumulation passes through the push
                lemma_codes_of_push(bout_pre, c);
                reveal_with_fuel(ascii_prefix_model, 1);
                lemma_codes_of_index(input@, q as int);
                lemma_codes_of_len(input@);
                assert(input@.len() == input.len());
                assert(0 <= q as int && (q as int) < input@.len());
                assert((codes_of(input@))[q as int] == input@[q as int] as int);
                assert(cs_m == codes_of(input@));
                assert(cs_m[q as int] == (codes_of(input@))[q as int]);
                assert(input@[q as int] == c);
                assert(cs_m[q as int] == c as int);
                assert(cs_m[q as int] < 128);
                assert(cs_m.len() == input@.len());
                assert((q as int) < cs_m.len());
                assert(ascii_prefix_model(cs_m, q as int, codes_of(bout_pre))
                    == ascii_prefix_model(
                        cs_m,
                        q as int + 1,
                        codes_of(bout_pre).push(c as int),
                    ));
            }
            basic_length += 1;
        } else {
            proof {
                assert(!((input@[q as int] as int) < 128));
                lemma_count_ascii_step(input@, q as int);
                reveal_with_fuel(ascii_prefix_model, 1);
                lemma_codes_of_index(input@, q as int);
                lemma_codes_of_len(input@);
                assert(input@.len() == input.len());
                assert(0 <= q as int && (q as int) < input@.len());
                assert((codes_of(input@))[q as int] == input@[q as int] as int);
                assert(cs_m == codes_of(input@));
                assert(cs_m[q as int] == (codes_of(input@))[q as int]);
                assert(input@[q as int] == c);
                assert(cs_m[q as int] == c as int);
                assert(!(cs_m[q as int] < 128));
                assert(cs_m.len() == input@.len());
                assert((q as int) < cs_m.len());
                assert(ascii_prefix_model(cs_m, q as int, codes_of(output@))
                    == ascii_prefix_model(cs_m, q as int + 1, codes_of(output@)));
            }
        }
        q += 1;
    }
    proof {
        assert((basic_length as int) == count_ascii_prefix(input@, input@.len() as int));
        // the model's basics accumulation is complete: the buffer codes
        // equal apc
        reveal_with_fuel(ascii_prefix_model, 1);
        assert(cs_m == codes_of(input@));
        lemma_codes_of_len(input@);
        assert(q == input.len());
        assert(q >= input.len());
        assert(input@.len() == input.len());
        assert(cs_m.len() == input@.len());
        assert(q as int >= cs_m.len());
        assert(apc == codes_of(output@));
        // count parity: the code-view count equals the char-view count
        lemma_count_basic_total(input@, 0);
        assert(count_basic_codes(cs_m, 0) == count_ascii_prefix(input@, input@.len() as int));
    }
    /* Origin Rust: if !C::EXTERNAL_CALLER { ... len_plus_one.checked_mul(...)
       } -- the internal caller's one-time sanity product, out of scope
       (ledger item 1) */
    /* Origin Rust: if basic_length > 0 { output.write_char('-')?; } */
    let ghost del_pre = output@;
    if basic_length > 0 {
        output.push('-');
    }
    let ghost b_m = count_basic_codes(cs_m, 0);
    let ghost out1c = (if b_m > 0 { apc.push(0x2D) } else { apc });
    let ghost mc = enc_outer_model(
        cs_m,
        INITIAL_N as int,
        b_m,
        0,
        INITIAL_BIAS as int,
        b_m,
        out1c,
    );
    proof {
        if b_m > 0 {
            lemma_codes_of_push(del_pre, '-');
            assert(('-' as int) == 0x2D);
            assert(codes_of(output@) == apc.push(0x2D));
        } else {
            assert(codes_of(output@) == apc);
        }
        assert(codes_of(output@) == out1c);
        assert(b_m == basic_length as int);
    }
    let mut code_point: u32 = INITIAL_N;
    let mut delta: u32 = 0;
    let mut bias: u32 = INITIAL_BIAS;
    let mut processed: u32 = basic_length;
    let ghost ba = count_ascii_prefix(input@, input@.len() as int);
    let ghost delim = (if ba > 0 { 1int } else { 0int });
    let ghost dg_f = O + ba + delim;
    proof {
        // all outer-loop entry clauses, made explicit
        assert((basic_length as int) == ba);
        assert(ba >= 0);
        lemma_count_ascii_is_lt(input@, input@.len() as int);
        assert(ba == count_lt_code(input@, input@.len() as int, 128));
        if ba > 0 {
            assert(output@.len() as int == O + ba + 1);
            assert(output@[O + ba] == '-');
            assert(('-' as int) == 0x2D);
        } else {
            assert(output@.len() as int == O + ba);
        }
        assert((processed as int) == ba);
    }
    while processed < input_length
        invariant
            input_length == input.len() as u32,
            (input@.len() as int == input_length as int),
            input.len() <= u32::MAX as usize,
            (O == old(output)@.len()),
            (ba >= 0),
            (dg_f >= O),
            (dg_f == O + ba + delim),
            ((ba > 0) ==> (delim == 1)),
            ((ba == 0) ==> (delim == 0)),
            processed <= input_length,
            (basic_length as int) == ba,
            (basic_length as int) <= (processed as int),
            ((processed as int)
                == count_lt_code(input@, input@.len() as int, code_point as int)),
            0 <= (code_point as int) <= 0x110000,
            (bias as int) <= 614,
            forall |p: int| 0 <= p < O ==> (output@[p] == old(output)@[p]),
            (output@.len() as int) >= dg_f,
            forall |j: int| #![trigger output@[O + j]] 0 <= j < ba
                ==> (output@[O + j] < 128),
            (ba > 0) ==> ((output@[O + ba] as int) == 0x2D),
            (forall |p: int|
                dg_f <= p < output@.len() ==> is_digit_char(output@[p])),
            cs_m == codes_of(input@),
            O0c == codes_of(old(output)@),
            apc == ascii_prefix_model(cs_m, 0, O0c),
            b_m == count_basic_codes(cs_m, 0),
            b_m == basic_length as int,
            out1c == (if b_m > 0 { apc.push(0x2D) } else { apc }),
            mc == enc_outer_model(
                cs_m,
                INITIAL_N as int,
                b_m,
                0,
                INITIAL_BIAS as int,
                b_m,
                out1c,
            ),
            enc_outer_model(
                cs_m,
                code_point as int,
                processed as int,
                delta as int,
                bias as int,
                b_m,
                codes_of(output@),
            ) == mc,
        decreases (input_length as int) - (processed as int)
    {
        let oh_n_e: u32 = code_point;
        let oh_h_e: u32 = processed;
        let oh_delta_e: u32 = delta;
        let oh_bias_e: u32 = bias;
        let ghost oh_out = codes_of(output@);
        proof {
            // anchored-call fact: the full model at this call equals mc
            // (component pins from the outer invariant; decomposed for the
            // solver to fuse each component)
            assert(cs_m == codes_of(input@));
            assert(codes_of(input@) == cs_m);
            assert(O0c == codes_of(old(output)@));
            assert(codes_of(old(output)@) == O0c);
            assert(count_basic_codes(codes_of(input@), 0) == b_m);
            assert(ascii_prefix_model(codes_of(input@), 0, codes_of(old(output)@))
                == apc);
            assert(enc_outer_model(cs_m, INITIAL_N as int, b_m, 0,
                INITIAL_BIAS as int, b_m, out1c) == mc);
            assert(encode_full_model(input@, old(output)@) == mc);
        }
        /* Origin Rust: let min_code_point = input.clone().map(|c| c as u32)
           .filter(|&c| c >= code_point).min().unwrap(); -- the scan argument
           for the .unwrap(): with processed < input_length some char is
           >= code_point (the handled-count invariant), so the filtered
           re-scan is nonempty (a live obligation, discharged here) */
        let mut got = false;
        let mut mcp: u32 = 0;
        let mut mcp_idx: usize = 0;
        let mut j = 0usize;
        while j < input.len()
            invariant
                j <= input.len(),
                cs_m == codes_of(input@),
                O0c == codes_of(old(output)@),
                apc == ascii_prefix_model(cs_m, 0, O0c),
                out1c == (if b_m > 0 { apc.push(0x2D) } else { apc }),
                b_m == count_basic_codes(cs_m, 0),
                b_m == basic_length as int,
                encode_full_model(input@, old(output)@) == mc,
                ((processed as int)
                    == count_lt_code(input@, input@.len() as int, code_point as int)),
                (processed as int) < (input_length as int),
                input_length == input.len() as u32,
                got ==> (mcp_idx < j
                    && ((input@[mcp_idx as int] as int) == mcp as int)
                    && (mcp as int >= code_point as int)),
                got ==> (forall |k: int| 0 <= k < j
                    ==> ((input@[k] as int) >= code_point as int
                        ==> ((input@[k] as int) >= mcp as int))),
                !got ==> (forall |k: int| 0 <= k < j
                    ==> ((input@[k] as int) < code_point as int)),
            decreases input.len() - j
        {
            let cv = input[j] as u32;
            if cv >= code_point && (!got || cv < mcp) {
                got = true;
                mcp = cv;
                mcp_idx = j;
            }
            j += 1;
        }
        proof {
            // the nonempty-scan discharge of the upstream .unwrap()
            if !got {
                assert forall |k: int| 0 <= k < input@.len() implies
                    ((input@[k] as int) < code_point as int) by {}
                lemma_count_lt_all(input@, input@.len() as int, code_point as int);
                assert(count_lt_code(input@, input@.len() as int, code_point as int)
                    == input@.len() as int);
                assert((processed as int) == input@.len() as int);
                assert((processed as int) == (input_length as int));
                assert(false);
            }
            assert(got);
            assert((input@[mcp_idx as int] as int) == mcp as int);
            assert((mcp as int) <= 0x10FFFF);
            // no char lies in [code_point, mcp): the min scan's own
            // guarantee, so the handled counts match at code_point == mcp
            assert forall |k: int| #![trigger input@[k]] 0 <= k < input@.len() implies
                (!((code_point as int) <= (input@[k] as int) < (mcp as int))) by {
                assert((input@[k] as int) >= code_point as int
                    ==> ((input@[k] as int) >= mcp as int));
            }
            lemma_count_lt_mono_gap(
                input@,
                input@.len() as int,
                code_point as int,
                mcp as int,
            );
            assert(count_lt_code(input@, input@.len() as int, mcp as int)
                == count_lt_code(input@, input@.len() as int, code_point as int));
            // tie this pass to the model: min_ge over the code view is the
            // exec min-scan result, inside the scalar clamp interval
            assert(cs_m == codes_of(input@));
            lemma_codes_of_len(input@);
            assert((codes_of(input@)).len() == input@.len());
            assert forall |k: int| #![trigger (codes_of(input@))[k]]
                0 <= k < (codes_of(input@)).len()
                implies (!(((code_point as int)) <= ((codes_of(input@))[k]) < (mcp as int))) by {
                assert(0 <= k && k < input@.len());
                lemma_codes_of_index(input@, k);
                assert((codes_of(input@))[k] == input@[k] as int);
                assert(!(((code_point as int)) <= ((input@[k]) as int) < (mcp as int)));
            };
            lemma_codes_of_index(input@, mcp_idx as int);
            assert((codes_of(input@))[mcp_idx as int] == input@[mcp_idx as int] as int);
            assert(input@[mcp_idx as int] == mcp);
            assert((codes_of(input@))[mcp_idx as int] == mcp as int);
            lemma_min_ge_value(codes_of(input@), code_point as int, mcp as int, mcp_idx as int);
            assert(min_ge(codes_of(input@), code_point as int, 0) == mcp as int);
            assert(0 <= mcp as int);
            assert(mcp as int <= 0x10FFFF);
        }
        /* Origin Rust: let product = (min_code_point - code_point)
           .checked_mul(processed + 1).ok_or(...)?; delta =
           delta.checked_add(product).ok_or(...)?; */
        proof {
            assert((mcp as int) >= (code_point as int));
            assert(((processed as u64) + 1) <= 4294967296);
            vstd::arithmetic::mul::lemma_mul_upper_bound(
                (mcp - code_point) as int,
                0x10FFFF,
                (processed + 1) as int,
                4294967296,
            );
            assert((((mcp - code_point) as u64) * ((processed as u64) + 1))
                <= 0x10FFFF * 4294967296);
            assert(0x10FFFF * 4294967296 < 18446744073709551615);
            assert(delta as u64 <= 4294967295);
            assert(((delta as u64)
                + (((mcp - code_point) as u64) * ((processed as u64) + 1)))
                < 18446744073709551615);
        }
        proof {
            // the outer model's single-step unfold at the pass-entry state:
            // the checked channels agree boundary-for-boundary; the residual
            // chain is pinned through the inner loop by the invariant below
            reveal_with_fuel(enc_outer_model, 1);
            let mg = min_ge(codes_of(input@), oh_n_e as int, 0);
            assert(mg == mcp as int);
            assert(0 <= mg && mg < 0x110000);
            let m_clamped = if mg < 0 || mg >= 0x110000 { -1 } else { mg };
            assert(m_clamped == mcp as int);
            let d_m = oh_delta_e as int + (m_clamped - oh_n_e as int) * (oh_h_e as int + 1);
            assert(d_m == (delta as u64 as int)
                + ((mcp as int) - (oh_n_e as int)) * ((oh_h_e as int) + 1));
            assert(enc_outer_model(
                cs_m,
                oh_n_e as int,
                oh_h_e as int,
                oh_delta_e as int,
                oh_bias_e as int,
                b_m,
                oh_out,
            ) == (if d_m > 0xFFFF_FFFF {
                Option::None
            } else {
                match enc_scan_model(
                    cs_m,
                    m_clamped,
                    0,
                    d_m,
                    oh_bias_e as int,
                    oh_h_e as int,
                    b_m,
                    oh_out,
                ) {
                    Option::None => Option::None,
                    Option::Some((dend_m, biasend_m, hend_m, outend_m)) => {
                        if dend_m + 1 > 0xFFFF_FFFF {
                            Option::None
                        } else {
                            enc_outer_model(cs_m, m_clamped + 1, hend_m,
                                dend_m + 1, biasend_m, b_m, outend_m)
                        }
                    }
                }
            }));
            assert(enc_outer_model(cs_m, oh_n_e as int, oh_h_e as int,
                oh_delta_e as int, oh_bias_e as int, b_m, oh_out) == mc);
        }
        let product64 = (mcp - code_point) as u64 * ((processed as u64) + 1);
        if product64 > u32::MAX as u64 {
            proof {
                // product overflow implies the model's delta-overflow channel:
                // the pass result is None, so the model is None
                assert((mcp as u64 - code_point as u64)
                    == ((mcp as int) - oh_n_e as int) as u64);
                assert(delta as int == oh_delta_e as int);
                assert((processed as u64) + 1 == (oh_h_e as int + 1) as u64);
                assert((product64 as int)
                    == ((mcp as int) - (oh_n_e as int)) * (oh_h_e as int + 1));
                assert((delta as int) >= 0);
                assert((oh_delta_e as int
                    + ((mcp as int) - (oh_n_e as int)) * (oh_h_e as int + 1))
                    >= ((mcp as int) - (oh_n_e as int)) * (oh_h_e as int + 1));
                assert((oh_delta_e as int
                    + ((mcp as int) - (oh_n_e as int)) * (oh_h_e as int + 1))
                    > 0xFFFF_FFFF);
                                assert(encode_full_model(input@, old(output)@) == mc);
                assert(mc == Option::None);
            }
            return Result::Err(PunycodeEncodeError::Overflow);
        }
        let d64 = (delta as u64) + product64;
        if d64 > u32::MAX as u64 {
            proof {
                assert(d64 == (oh_delta_e as int
                    + (mcp as int - oh_n_e as int) * (oh_h_e as int + 1)) as u64);
                assert((oh_delta_e as int
                    + (mcp as int - oh_n_e as int) * (oh_h_e as int + 1)) > 0xFFFF_FFFF);
                // the unfolded outer residual takes the overflow arm: mc is None
                                assert(encode_full_model(input@, old(output)@) == mc);
                assert(mc == Option::None);
            }
            return Result::Err(PunycodeEncodeError::Overflow);
        }
        delta = d64 as u32;
        code_point = mcp;
        let ghost sc = enc_scan_model(
            cs_m,
            code_point as int,
            0,
            delta as int,
            oh_bias_e as int,
            processed as int,
            b_m,
            codes_of(output@),
        );
        proof {
            // the residual outer chain, expressed through sc: this is the
            // invariant the inner loop pins (all components constant in the
            // pass, sc tracked by the inner invariant)
            let d_m = oh_delta_e as int
                + ((mcp as int) - (oh_n_e as int)) * ((oh_h_e as int) + 1);
            assert(d_m == delta as int);
            assert(min_ge(codes_of(input@), oh_n_e as int, 0) == mcp as int);
            assert(mc == (if d_m > 0xFFFF_FFFF {
                Option::None
            } else {
                match sc {
                    Option::None => Option::None,
                    Option::Some((dx, bx, hx, ox)) => {
                        if dx + 1 > 0xFFFF_FFFF {
                            Option::None
                        } else {
                            enc_outer_model(
                                cs_m,
                                (mcp as int) + 1,
                                hx,
                                dx + 1,
                                bx,
                                b_m,
                                ox,
                            )
                        }
                    }
                }
            }));
        }
        /* Origin Rust: for c in input.clone() { let c = c as u32;
           if c < code_point { delta += 1 (checked) }
           if c == code_point { ...emit delta digits...; bias = adapt(delta,
           processed + 1, processed == basic_length); delta = 0; processed += 1 } }
           -- the two ifs are disjoint, transcribed as if/else-if */
        let ghost processed_entry = processed;
        let ghost delta_start = delta;
        let ghost mut m: int = -1;
        let mut j2 = 0usize;
        while j2 < input.len()
            invariant
                j2 <= input.len(),
                input_length == input.len() as u32,
                (input@.len() as int == input_length as int),
                O == old(output)@.len(),
                (processed as int) <= (input_length as int),
                (code_point as int) <= 0x10FFFF,
                (basic_length as int) == ba,
                (ba >= 0 && processed_entry >= 0),
                (dg_f >= O),
                (dg_f == O + ba + delim),
                ((ba > 0) ==> (delim == 1)),
                ((ba == 0) ==> (delim == 0)),
                (bias as int) <= 614,
                ((processed as int)
                    == (processed_entry as int)
                        + count_eq_prefix(input@, j2 as int, code_point as int)),
                ((processed_entry as int)
                    == count_lt_code(input@, input@.len() as int, code_point as int)),
                (m == -1) ==> (delta as int
                    == delta_start as int
                        + count_lt_code(input@, j2 as int, code_point as int)),
                (m >= 0) ==> (0 <= m < j2
                    && ((input@[m] as int) == code_point as int)
                    && (delta as int
                        == count_lt_between(input@, m + 1, j2 as int, code_point as int))),
                (m >= 0) ==> (forall |k: int| m < k < j2
                    ==> ((input@[k] as int) != code_point as int)),
                (m >= -1),
                (m == -1) ==> (forall |k: int| 0 <= k < j2
                    ==> ((input@[k] as int) != code_point as int)),
                (mcp_idx as int) < input@.len()
                    && ((input@[mcp_idx as int] as int) == code_point as int),
                forall |p: int| 0 <= p < O ==> (output@[p] == old(output)@[p]),
                (output@.len() as int) >= dg_f,
                forall |j3: int| #![trigger output@[O + j3]] 0 <= j3 < ba
                    ==> (output@[O + j3] < 128),
                (ba > 0) ==> ((output@[O + ba] as int) == 0x2D),
                (forall |p: int|
                    dg_f <= p < output@.len() ==> is_digit_char(output@[p])),
                cs_m == codes_of(input@),
                b_m == count_basic_codes(cs_m, 0),
                b_m == basic_length as int,
                O0c == codes_of(old(output)@),
                encode_full_model(input@, old(output)@) == mc,
                (min_ge(codes_of(input@), oh_n_e as int, 0)) == (mcp as int),
                mc == ({
                    let d_m = oh_delta_e as int
                        + ((mcp as int) - (oh_n_e as int)) * ((oh_h_e as int) + 1);
                    if d_m > 0xFFFF_FFFF {
                        Option::None
                    } else {
                        match sc {
                            Option::None => Option::None,
                            Option::Some((dx, bx, hx, ox)) => {
                                if dx + 1 > 0xFFFF_FFFF {
                                    Option::None
                                } else {
                                    enc_outer_model(
                                        cs_m,
                                        (mcp as int) + 1,
                                        hx,
                                        dx + 1,
                                        bx,
                                        b_m,
                                        ox,
                                    )
                                }
                            }
                        }
                    }
                }),
                sc == enc_scan_model(
                    cs_m,
                    code_point as int,
                    j2 as int,
                    delta as int,
                    bias as int,
                    processed as int,
                    b_m,
                    codes_of(output@),
                ),
            decreases input.len() - j2
        {
            let cv = input[j2] as u32;
            let ghost arm_j2 = j2 as int;
            let ghost arm_delta = delta as int;
            let ghost arm_bias = bias as int;
            let ghost arm_h = processed as int;
            let ghost arm_out = codes_of(output@);
            proof {
                lemma_codes_of_index(input@, j2 as int);
                lemma_codes_of_len(input@);
                assert(cs_m == codes_of(input@));
                assert(input@[j2 as int] == cv);
                assert(cs_m[arm_j2] == cv as int);
                assert(cs_m.len() == input@.len());
                assert(0 <= arm_j2 && arm_j2 < cs_m.len());
            }
            if cv < code_point {
                /* Origin Rust: delta = delta.checked_add(1).ok_or(...)?; */
                proof {
                    // the model's below-branch and None condition
                    reveal_with_fuel(enc_scan_model, 1);
                }
                let d2 = (delta as u64) + 1;
                if d2 > u32::MAX as u64 {
                    proof {
                        assert(arm_delta + 1 > 0xFFFF_FFFF);
                        assert(enc_scan_model(cs_m, code_point as int, arm_j2,
                            arm_delta, arm_bias, arm_h, b_m, arm_out)
                            == Option::None);
                        assert(sc == Option::None);
                        assert(mc == Option::None);
                    }
                    return Result::Err(PunycodeEncodeError::Overflow);
                }
                delta = d2 as u32;
                proof {
                    assert(arm_delta + 1 <= 0xFFFF_FFFF);
                    assert(arm_delta + 1 == delta as int);
                    assert(enc_scan_model(cs_m, code_point as int, arm_j2,
                        arm_delta, arm_bias, arm_h, b_m, arm_out)
                        == enc_scan_model(cs_m, code_point as int, arm_j2 + 1,
                            arm_delta + 1, arm_bias, arm_h, b_m, arm_out));
                    assert(sc == enc_scan_model(cs_m, code_point as int,
                        arm_j2 + 1, arm_delta + 1, arm_bias, arm_h, b_m, arm_out));
                }
                proof {
                    // count-step: position j2 joins the < code_point count
                    if m >= 0 {
                        assert((input@[j2 as int] as int) < code_point as int);
                        assert(count_lt_between(input@, m + 1, j2 as int + 1, code_point as int)
                            == count_lt_between(input@, m + 1, j2 as int, code_point as int) + 1);
                    } else {
                        assert((input@[j2 as int] as int) < code_point as int);
                        assert(count_lt_code(input@, j2 as int + 1, code_point as int)
                            == count_lt_code(input@, j2 as int, code_point as int) + 1);
                    }
                }
                j2 += 1;
            } else if cv == code_point {
                /* Origin Rust: let mut q = delta; let mut k = BASE; loop { ... }
                   output.write_char(value_to_digit(q))?;
                   -- the whole delta-digit emission (loop plus final digit),
                   extracted into the single verified encode_digits helper */
                let ghost pre_digits = output@;
                encode_digits(delta, bias, output);
                proof {
                    // stitch the helper's contract into the c-loop clauses:
                    // earlier positions are untouched, and the appended region
                    // consists only of digit symbols
                    assert(output@.len() >= pre_digits.len());
                    assert(pre_digits.len() >= dg_f);
                    assert(0 <= O);
                    assert forall |j3: int| #![trigger output@[O + j3]] 0 <= j3 < ba implies
                        (output@[O + j3] < 128) by {
                        assert(0 <= O + j3);
                        if ba > 0 {
                            assert(delim == 1);
                        } else {
                            assert(0 <= j3);
                            assert(j3 < ba);
                            assert(ba == 0);
                            assert(false);
                        }
                        assert(j3 <= ba - 1);
                        assert(O + j3 <= O + ba - 1);
                        assert(dg_f >= O + ba + 1);
                        assert(O + j3 < dg_f);
                        assert(O + j3 < pre_digits.len());
                        assert(output@[O + j3] == pre_digits[O + j3]);
                    }
                    if ba > 0 {
                        assert((output@[O + ba] as int) == 0x2D) by {
                            assert(0 <= O + ba);
                            assert(ba > 0);
                            assert(delim == 1);
                            assert(dg_f == O + ba + delim);
                            assert(O + ba < dg_f);
                            assert(O + ba < pre_digits.len());
                            assert(output@[O + ba] == pre_digits[O + ba]);
                        }
                    }
                    assert forall |p4: int| 0 <= p4 < O implies
                        (output@[p4] == old(output)@[p4]) by {
                        if 0 <= p4 && p4 < O {
                            assert(p4 < dg_f);
                            assert(p4 < pre_digits.len());
                            assert(output@[p4] == pre_digits[p4]);
                        }
                    }
                    assert forall |p: int| #![trigger output@[p]] dg_f <= p
                        < output@.len() implies is_digit_char(output@[p]) by {
                        if p < pre_digits.len() {
                            assert(dg_f <= p < pre_digits.len());
                        } else {
                            assert(pre_digits.len() <= p);
                        }
                    }
                    assert(output@.len() >= dg_f);
                }
                /* Origin Rust: bias = adapt(delta, processed + 1,
                   processed == basic_length); delta = 0; processed += 1; */
                proof {
                    // this very char (at j2) equals code_point and is not yet
                    // counted in the multiplicity prefix: processed + 1 fits
                    assert((input@[j2 as int] as int) == code_point as int);
                    assert(input@.len() as int == input_length as int);
                    assert((j2 as int) < input@.len() as int);
                    lemma_count_eq_step(input@, j2 as int, code_point as int);
                    assert(count_eq_prefix(input@, j2 as int + 1, code_point as int)
                        == 1 + count_eq_prefix(input@, j2 as int, code_point as int));
                    lemma_count_eq_mono(
                        input@,
                        j2 as int + 1,
                        input@.len() as int,
                        code_point as int,
                    );
                    assert(count_eq_prefix(input@, input@.len() as int, code_point as int)
                        >= count_eq_prefix(input@, j2 as int + 1, code_point as int));
                    assert(count_eq_prefix(input@, input@.len() as int, code_point as int)
                        >= 1 + count_eq_prefix(input@, j2 as int, code_point as int));
                    lemma_count_lt_eq_le_len(input@, input@.len() as int, code_point as int);
                    assert(count_lt_code(input@, input@.len() as int, code_point as int)
                        + count_eq_prefix(input@, input@.len() as int, code_point as int)
                        <= input@.len() as int);
                    assert((processed as int)
                        == (processed_entry as int)
                            + count_eq_prefix(input@, j2 as int, code_point as int));
                    assert((processed_entry as int)
                        == count_lt_code(input@, input@.len() as int, code_point as int));
                    assert((processed as int) + 1
                        <= (processed_entry as int)
                            + count_eq_prefix(input@, input@.len() as int, code_point as int));
                    assert((processed as int) + 1 <= input@.len() as int);
                    assert((processed as int) < (input_length as int));
                    assert(processed + 1 >= 1);
                }
                bias = adapt(delta, processed + 1, processed == basic_length);
                proof {
                    // the emission helper flushed the model's digit chain,
                    // and the adapt recompute matches the model's rebias
                    assert(codes_of(pre_digits) == arm_out);
                    assert(processed as int == arm_h);
                    assert(delta as int == arm_delta);
                    assert(bias as int == adapt_model(arm_delta, arm_h + 1, arm_h == b_m));
                    assert(arm_h == b_m <==> (processed as int) == (basic_length as int));
                    assert((processed == basic_length) == (arm_h == b_m));
                    let emd = emit_digits_model(arm_delta, 36, arm_bias, arm_out);
                    lemma_codes_of_len(output@);
                    assert(output@.len() as int == emd.len());
                    assert((codes_of(output@)).len() as int == emd.len());
                    assert forall |pi: int| 0 <= pi < emd.len() implies
                        (((codes_of(output@))[pi]) == emd[pi]) by {
                        assert(0 <= pi < (codes_of(output@)).len());
                        lemma_codes_of_index(output@, pi);
                        assert(((output@[pi]) as int) == emd[pi]);
                    };
                    vstd::seq::lemma_seq_ext_equal(codes_of(output@), emd);
                    assert(codes_of(output@) == emd);
                    assert(cs_m[arm_j2] == code_point as int);
                    assert(enc_scan_model(cs_m, code_point as int, arm_j2,
                        arm_delta, arm_bias, arm_h, b_m, arm_out)
                        == enc_scan_model(cs_m, code_point as int, arm_j2 + 1,
                            0, adapt_model(arm_delta, arm_h + 1, arm_h == b_m),
                            arm_h + 1, b_m, emd)) by {
                        reveal_with_fuel(enc_scan_model, 1);
                    };
                }
                delta = 0;
                proof {
                    m = j2 as int;
                    // post-reset bookkeeping: empty tail count at the new m
                    assert((input@[j2 as int] as int) == code_point as int);
                    assert(count_lt_between(
                        input@,
                        m + 1,
                        j2 as int + 1,
                        code_point as int,
                    ) == 0);
                    assert(count_eq_prefix(input@, j2 as int + 1, code_point as int)
                        == 1 + count_eq_prefix(input@, j2 as int, code_point as int));
                }
                processed += 1;
                proof {
                    assert(sc == enc_scan_model(cs_m, code_point as int,
                        (j2 as int) + 1, 0, bias as int, processed as int,
                        b_m, codes_of(output@)));
                }
                j2 += 1;
            } else {
                proof {
                    // a char above code_point: no delta change, no reset
                    assert(!(cs_m[arm_j2] < code_point as int));
                    assert(!(cs_m[arm_j2] == code_point as int));
                    assert(enc_scan_model(cs_m, code_point as int, arm_j2,
                        arm_delta, arm_bias, arm_h, b_m, arm_out)
                        == enc_scan_model(cs_m, code_point as int, arm_j2 + 1,
                            arm_delta, arm_bias, arm_h, b_m, arm_out)) by {
                        reveal_with_fuel(enc_scan_model, 1);
                    };
                    assert(sc == enc_scan_model(cs_m, code_point as int,
                        (j2 as int) + 1, delta as int, bias as int,
                        processed as int, b_m, codes_of(output@)));
                    assert((input@[j2 as int] as int) > code_point as int);
                    if m >= 0 {
                        assert(count_lt_between(input@, m + 1, j2 as int + 1, code_point as int)
                            == count_lt_between(input@, m + 1, j2 as int, code_point as int));
                    } else {
                        assert(count_lt_code(input@, j2 as int + 1, code_point as int)
                            == count_lt_code(input@, j2 as int, code_point as int));
                    }
                }
                j2 += 1;
            }
        }
        proof {
            // the min-scan witness guarantees a c == code_point occurrence,
            // so the last-seen m is set, the outer processed grew, and delta
            // is bounded by the post-reset tail count
            assert(j2 as int == input@.len() as int);
            lemma_min_occurs(
                input@,
                mcp_idx as int,
                code_point as int,
                m,
                j2 as int,
            );
            assert(m >= 0);
            // the multiplicity at code_point is nonzero, so processed grew
            lemma_count_eq_witness(
                input@,
                input@.len() as int,
                code_point as int,
                mcp_idx as int,
            );
            assert(count_eq_prefix(input@, input@.len() as int, code_point as int)
                >= 1);
            assert(count_eq_prefix(input@, input@.len() as int, code_point as int)
                == (processed as int) - (processed_entry as int));
            assert((processed as int) >= (processed_entry as int) + 1);
            assert(0 <= m);
            assert(m < input@.len() as int);
            lemma_count_between_bound(input@, m + 1, input@.len() as int, code_point as int);
            assert(count_lt_between(input@, m + 1, input@.len() as int, code_point as int)
                <= input@.len() as int - m - 1);
            assert(delta as int <= input@.len() as int - m - 1);
            assert((delta as int) < input@.len() as int);
        }
        /* Origin Rust: delta += 1; code_point += 1; -- the unchecked adds,
           proven in bounds by the post-reset unit-increment argument */
        delta += 1;
        proof {
            // the handled-count shift across the newly-finished code point
            assert((processed as int)
                == (processed_entry as int)
                    + count_eq_prefix(input@, input@.len() as int, code_point as int));
            assert((processed_entry as int)
                == count_lt_code(input@, input@.len() as int, code_point as int));
            lemma_count_lt_shift(input@, input@.len() as int, code_point as int);
            assert(count_lt_code(input@, input@.len() as int, code_point as int + 1)
                == (processed as int));
            assert(code_point as int <= 0x10FFFF);
        }
        code_point += 1;
    }
    proof {
        // at the exit every char is handled: the model turns Some with the
        // buffer codes as accumulated content
        assert((processed as int) >= (cs_m.len() as int));
        assert(enc_outer_model(cs_m, code_point as int, processed as int,
            delta as int, bias as int, b_m, codes_of(output@))
            == ({
                if (processed as int) >= (cs_m.len() as int) {
                    Option::Some(codes_of(output@))
                } else {
                    enc_outer_model(cs_m, code_point as int, processed as int,
                        delta as int, bias as int, b_m, codes_of(output@))
                }
            })) by {
            reveal_with_fuel(enc_outer_model, 1);
        };
        assert(enc_outer_model(cs_m, code_point as int, processed as int,
            delta as int, bias as int, b_m, codes_of(output@)) == mc);
        assert(mc == Option::Some(codes_of(output@)));
        assert(encode_full_model(input@, old(output)@) == mc);
        // the model output is the final buffer content, per index
        let em_fin = (mc->0);
        assert(final(output)@ == output@);
        lemma_codes_of_len(output@);
        assert((codes_of(output@)).len() == output@.len());
        assert(final(output)@.len() as int == em_fin.len());
        assert forall |p: int| 0 <= p < em_fin.len() implies
            ((final(output)@[p] as int) == em_fin[p]) by {
            lemma_codes_of_index(output@, p);
            assert(final(output)@[p] as int == (codes_of(output@))[p]);
            assert(((codes_of(output@))[p]) == em_fin[p]);
        };
    }
    Result::Ok(())
}


/* ============================================================
 * Encode entry: the external-caller char core
 * (punycode.rs:318-344 encode / encode_str minus the String layer)
 * ============================================================ */

/// Origin: punycode.rs:336-344 `encode` for the external caller (the String return
/// and `encode_str` (punycode.rs:322-330) are the str/String layer, ledger item 7):
/// the verified char core returning the emitted chars of a fresh buffer.
/// Upstream doc (punycode.rs:318-320):
///   Convert an Unicode `str` to Punycode.
///   This is a convenience wrapper around `encode`.
/// Upstream doc (punycode.rs:332-335):
///   Convert Unicode to Punycode.
///   Return None on overflow, which can only happen on inputs that would take more than
///   63 encoded bytes, the DNS limit on domain name labels.
// Visibility opened to pub for harness (../harness/) consumption via #[path];
// upstream visibility of the underlying API is `pub` at the punycode module level.
pub fn encode_chars(input: &[char]) -> (r: Option<Vec<char>>)
    ensures
        (input.len() > u32::MAX as usize) ==> r.is_none(),
        r.is_some() <==> encode_model(input@).is_some(),
        r matches Some(v) ==> ({
            let m = encode_model(input@);
            m matches Some(em)
                && ((v@.len() as int == em.len())
                    && (forall |p: int| 0 <= p < em.len()
                        ==> ((v@[p] as int) == em[p])))
        }),
{
    /* Origin Rust: if input.len() > u32::MAX as usize { return None; } */
    if input.len() > u32::MAX as usize {
        proof {
            // the model carries the same input-length guard
            lemma_codes_of_len(input@);
            assert(input.len() as int > 0xFFFF_FFFF);
            assert(input@.len() == input.len());
            assert((codes_of(input@)).len() as int > 0xFFFF_FFFF);
            reveal(encode_model);
            reveal(encode_model_codes);
            assert(encode_model(input@).is_none());
        }
        return Option::None;
    }
    /* Origin Rust: let mut buf = String::with_capacity(input.len());
       encode_into::<_, _, ExternalCaller>(input.iter().copied(), &mut buf).ok()
       .map(|()| buf) -- char vector instead of String (ledger item 7) */
    let mut buf: Vec<char> = Vec::new();
    proof {
        // bridging facts: the entry buffer is empty, and encode_model is
        // encode_model_codes over the code view
        assert(buf@ == Seq::empty());
        assert(codes_of(Seq::empty()) == Seq::empty()) by {
            reveal_with_fuel(codes_of, 1);
        };
        reveal(encode_model);
        assert(encode_model(input@)
            == encode_model_codes(codes_of(input@)));
    }
    let ghost pre_buf = buf@;
    match encode_into_chars(input, &mut buf) {
        Result::Ok(()) => {
            proof {
                // with the empty anchor, encode_into_chars' refined model
                // IS the encode_model assembly
                let cs_x = codes_of(input@);
                let b_x = count_basic_codes(cs_x, 0);
                let out0_x = ascii_prefix_model(cs_x, 0, Seq::empty());
                let out1_x = (if b_x > 0 { out0_x.push(0x2D) } else { out0_x });
                let m_anch = enc_outer_model(
                    cs_x,
                    INITIAL_N as int,
                    b_x,
                    0,
                    INITIAL_BIAS as int,
                    b_x,
                    out1_x,
                );
                lemma_codes_of_len(input@);
                assert(input.len() as int <= 0xFFFF_FFFF);
                assert((codes_of(input@)).len() == input@.len());
                assert(input@.len() == input.len());
                assert(encode_model(input@)
                    == m_anch) by {
                    reveal(encode_model);
                    reveal(encode_model_codes);
                    assert(encode_model(input@)
                        == encode_model_codes(codes_of(input@)));
                    assert(!(((codes_of(input@)).len() as int) > 0xFFFF_FFFF));
                };
                // the refined m-form at this call (empty-anchored) equals the
                // same assembly, so the model reaches us through the bridge
                assert(m_anch.is_some());
                let em_pre = m_anch->0;
                assert(encode_model(input@) == Option::Some(em_pre));
                assert((encode_model(input@)->0) == em_pre);
                // spell the ensured model form at the call site (old buffer
                // captured as pre_buf, known empty) and fuse it with m_anch
                let m_form = encode_full_model(input@, pre_buf);
                assert(codes_of(pre_buf) == Seq::empty());
                assert(m_form == m_anch);
                let em_ens = m_form->0;
                assert(em_ens.len() == em_pre.len());
                assert(buf@.len() as int == em_pre.len());
                assert forall |p: int| 0 <= p < em_ens.len() implies
                    ((buf@[p] as int) == em_pre[p]) by {
                    assert(0 <= p < em_ens.len());
                    assert((buf@[p] as int) == em_ens[p]);
                    vstd::seq::lemma_seq_ext_equal(em_ens, em_pre);
                    assert(em_ens[p] == em_pre[p]);
                };
            }
            Option::Some(buf)
        }
        Result::Err(_) => {
            proof {
                assert(encode_model(input@).is_none());
                assert(encode_model(input@) == encode_model_codes(codes_of(input@)));
            }
            Option::None
        }
    }
}

/* ============================================================
 * Internal-caller encode (uts46 path)
 *
 * Origin: punycode.rs:375-414, the `C = InternalCaller` branch of
 * encode_into: the one-time RFC 3492 section 6.4 sanity product
 * (len_plus_one.checked_mul(char::MAX - INITIAL_N), punycode.rs:380-385)
 * guards the whole loop, and the in-loop delta arithmetic proceeds
 * unchecked (delta += (min_code_point - code_point) * (processed + 1)
 * and delta += 1, punycode.rs:413/422).
 *
 * Verification route (the RFC claim is machine-checked at model level):
 * lemma_encode_chars_model_no_overflow proves that under the one-shot
 * product the u32 overflow guards of the external-caller refinement
 * model (the delta+1 and accumulated-delta None channels of
 * enc_scan_model/enc_outer_model) cannot fire at any reachable state,
 * so the external-caller exec (encode_into_chars, which re-computes the
 * same state through checked ops) returns Ok and emits exactly the
 * full model's output; the unchecked in-loop operations of the internal
 * caller perform the same state updates with the same values (the
 * checked ops are no-ops on non-overflowing values).
 * ============================================================ */

pub const RFC_ONE_SHOT_LIMIT: u64 = 0x10FFFF - (INITIAL_N as u64);

/// Upstream punycode.rs:375-386 + encode_into body monomorphized to the
/// internal caller for the Vec<char> sink; the ensured content equals the
/// external-caller refinement model (encode_full_model).
pub fn encode_into_chars_internal(input: &[char], output: &mut Vec<char>)
    -> (r: Result<(), PunycodeEncodeError>)
    requires
        input.len() <= u32::MAX as usize,
    ensures
        (forall |q: int| #![trigger final(output)@[q]] 0 <= q < old(output)@.len()
            ==> (final(output)@[q] == old(output)@[q])),
        (final(output)@.len() >= old(output)@.len()),
        // The length guard fires before anything is written, so the error
        // channel leaves the sink exactly as it was.
        (r.is_err() ==> final(output)@ == old(output)@),
        (r matches Err(PunycodeEncodeError::Overflow))
            <== (((input.len() as u64) + 1) * RFC_ONE_SHOT_LIMIT
                > (u32::MAX as u64)),
        ({
            // the one-shot product decides: on violation the internal
            // caller errors (its own RFC 3492 6.4-length cap, which is
            // independent of the external-caller's delta channels),
            // otherwise the emission is the full model's
            let m = encode_full_model(input@, old(output)@);
            if (((input.len() as u64) + 1) * RFC_ONE_SHOT_LIMIT
                > (u32::MAX as u64))
            {
                r.is_err()
            } else {
                (r.is_ok()
                    && ({
                        let em = m->0;
                        ((final(output)@.len() as int == em.len())
                            && (forall |p: int| 0 <= p < em.len()
                                ==> ((final(output)@[p] as int) == em[p])))
                    }))
            }
        }),
{
    /* Origin Rust: let len_plus_one = input_length
       .checked_add(1).ok_or(PunycodeEncodeError::Overflow)?;
       len_plus_one.checked_mul(u32::from(char::MAX) - INITIAL_N)
       .ok_or(PunycodeEncodeError::Overflow)?; */
    let len64 = (input.len() as u64) + 1;
    assert((input.len() as u64) <= 4294967295);
    assert(len64 <= 4294967296);
    assert(len64 as int * 1113983 <= 4294967296 * 1113983) by {
        vstd::arithmetic::mul::lemma_mul_inequality(
            len64 as int, 4294967296, 1113983);
    }
    assert(4294967296 * 1113983 < 18446744073709551616) by (bit_vector);
    if len64 * RFC_ONE_SHOT_LIMIT > (u32::MAX as u64) {
        return Result::Err(PunycodeEncodeError::Overflow);
    }
    proof {
        lemma_encode_chars_model_no_overflow(input@, old(output)@);
    }
    encode_into_chars(input, output)
}

// ===========================================================================
// Proof lemmas (independent proof functions; each is a one-time helper for a
// single arithmetic or counting obligation of the exec faces above/below)
// ===========================================================================

/// One-step unfold of powi (isolated so callers spend no definition fuel).
proof fn lemma_powi_step(b: int, n: int)
    requires
        1 <= n,
    ensures
        powi(b, n) == b * powi(b, n - 1),
{
}

/// Positivity of powi for base >= 1.
proof fn lemma_powi_pos(b: int, n: int)
    requires
        1 <= n,
        1 <= b,
    ensures
        1 <= powi(b, n),
    decreases n
{
    lemma_powi_step(b, n);
    if n == 1 {
        assert(powi(b, 1 - 1) == 1);
        assert(powi(b, 1) == b * powi(b, 0));
    } else {
        assert(powi(b, n) == b * powi(b, n - 1));
        lemma_powi_pos(b, n - 1);
        assert(1 <= powi(b, n - 1));
        vstd::arithmetic::mul::lemma_mul_inequality(1, b, powi(b, n - 1));
        assert(1 * powi(b, n - 1) == powi(b, n - 1));
        assert(powi(b, n - 1) <= b * powi(b, n - 1));
        assert(1 <= powi(b, n));
    }
}

/// Monotonicity of powi in the exponent (for the >= 10 / >= 35 multipliers).
proof fn lemma_powi_mono(b: int, n: int, m: int)
    requires
        1 <= b,
        0 <= n <= m,
    ensures
        powi(b, n) <= powi(b, m),
    decreases m
{
    if n == m {
    } else {
        assert(1 <= m);
        lemma_powi_mono(b, n, m - 1);
        let q = powi(b, m - 1);
        if m - 1 == 0 {
            assert(q == 1);
        } else {
            lemma_powi_pos(b, m - 1);
            assert(1 <= q);
        }
        lemma_powi_step(b, m);
        vstd::arithmetic::mul::lemma_mul_inequality(1, b, q);
        assert(1 * q == q);
        assert(q <= b * q);
        assert(powi(b, m) == b * q);
        assert(powi(b, m - 1) <= powi(b, m));
    }
}

/// A loop-entry bound for adapt: entering the shrink loop requires
/// d >= 456 while powi(35, it) * d <= u32::MAX, which forces it <= 4
/// (powi(35, 5) * 456 exceeds u32::MAX already).
proof fn lemma_adapt_enter_bound(d: u32, it: int)
    requires
        456 <= d as int,
        powi(35, it) * (d as int) <= 4294967295,
        0 <= it,
    ensures
        it <= 4,
{
    if it >= 5 {
        lemma_powers();
        lemma_powi_mono(35, 5, it);
        lemma_powi_pos(35, 5);
        assert(1 <= powi(35, 5));
        assert(powi(35, 5) <= powi(35, it));
        vstd::arithmetic::mul::lemma_mul_inequality(powi(35, 5), powi(35, it), 456);
        vstd::arithmetic::mul::lemma_mul_inequality(456, d as int, powi(35, it));
        vstd::arithmetic::mul::lemma_mul_is_commutative(456, powi(35, 5));
        vstd::arithmetic::mul::lemma_mul_is_commutative(456, powi(35, it));
        vstd::arithmetic::mul::lemma_mul_is_commutative(d as int, powi(35, it));
        assert(powi(35, 5) * 456 <= powi(35, it) * 456);
        assert(powi(35, it) * 456 <= powi(35, it) * (d as int));
        assert(powi(35, it) * (d as int) <= 4294967295);
        assert(powi(35, 5) * 456 <= 4294967295);
        assert(false);
    }
}


/* ---------------------------------------------------------------
 * Encode-side count lemmas (the basics/handled/multiplicity models)
 * --------------------------------------------------------------- */

/// Step relation for the basic-count model.
proof fn lemma_count_ascii_step(s: Seq<char>, n: int)
    requires
        0 <= n < s.len(),
{
    assert(count_ascii_prefix(s, n + 1) == if (s[n] as int) < 128 {
        1 + count_ascii_prefix(s, n)
    } else {
        count_ascii_prefix(s, n)
    });
}

/// The basic count equals the count of chars below code point 0x80.
proof fn lemma_count_ascii_is_lt(s: Seq<char>, n: int)
    ensures
        count_ascii_prefix(s, n) == count_lt_code(s, n, 128),
    decreases n
{
    if n > 0 {
        lemma_count_ascii_is_lt(s, n - 1);
        assert(count_ascii_prefix(s, n) == if (s[n - 1] as int) < 128 {
            1 + count_ascii_prefix(s, n - 1)
        } else {
            count_ascii_prefix(s, n - 1)
        });
        assert(count_lt_code(s, n, 128) == if (s[n - 1] as int) < 128 {
            1 + count_lt_code(s, n - 1, 128)
        } else {
            count_lt_code(s, n - 1, 128)
        });
    }
}

/// Every char below cp means the full count is the length.
proof fn lemma_count_lt_all(s: Seq<char>, n: int, cp: int)
    requires
        0 <= n,
        forall |k: int| #![trigger s[k]] 0 <= k < n ==> ((s[k] as int) < cp),
    ensures
        count_lt_code(s, n, cp) == n,
    decreases n
{
    if n > 0 {
        let sub_cp = count_lt_code(s, n - 1, cp);
        assert((s[n - 1] as int) < cp);
        assert(count_lt_code(s, n, cp) == 1 + sub_cp);
        assert forall |k: int| 0 <= k < n - 1 implies ((s[k] as int) < cp) by {}
        assert(sub_cp == n - 1) by {
            lemma_count_lt_all(s, n - 1, cp);
        }
        assert(sub_cp == n - 1);
        assert(count_lt_code(s, n, cp) == n);
    } else {
        assert(count_lt_code(s, n, cp) == 0);
        assert(n == 0);
    }
}

/// The handled-count shift across one code point:
/// count(< cp + 1) = count(< cp) + count(== cp).
proof fn lemma_count_lt_shift(s: Seq<char>, n: int, cp: int)
    ensures
        count_lt_code(s, n, cp + 1)
            == count_lt_code(s, n, cp) + count_eq_prefix(s, n, cp),
    decreases n
{
    if n > 0 {
        lemma_count_lt_shift(s, n - 1, cp);
        assert(count_lt_code(s, n, cp + 1) == if (s[n - 1] as int) < cp + 1 {
            1 + count_lt_code(s, n - 1, cp + 1)
        } else {
            count_lt_code(s, n - 1, cp + 1)
        });
        assert(count_lt_code(s, n, cp) == if (s[n - 1] as int) < cp {
            1 + count_lt_code(s, n - 1, cp)
        } else {
            count_lt_code(s, n - 1, cp)
        });
        assert(count_eq_prefix(s, n, cp) == if (s[n - 1] as int) == cp {
            1 + count_eq_prefix(s, n - 1, cp)
        } else {
            count_eq_prefix(s, n - 1, cp)
        });
        // three-way element membership: < cp, == cp, > cp
        if (s[n - 1] as int) < cp {
            assert(count_lt_code(s, n, cp + 1)
                == count_lt_code(s, n, cp) + count_eq_prefix(s, n, cp));
        } else if (s[n - 1] as int) == cp {
            assert((s[n - 1] as int) >= cp);
            assert((s[n - 1] as int) < cp + 1);
            assert(count_lt_code(s, n, cp + 1)
                == count_lt_code(s, n, cp) + count_eq_prefix(s, n, cp));
        } else {
            assert(!((s[n - 1] as int) < cp + 1));
            assert(count_eq_prefix(s, n, cp) == count_eq_prefix(s, n - 1, cp));
            assert(count_lt_code(s, n, cp + 1)
                == count_lt_code(s, n, cp) + count_eq_prefix(s, n, cp));
        }
    }
}

/// Sub-range count totality: handled (< cp) plus multiplicity (== cp)
/// never exceeds the prefix length.
proof fn lemma_count_lt_eq_le_len(s: Seq<char>, n: int, cp: int)
    requires
        0 <= n,
    ensures
        count_lt_code(s, n, cp) + count_eq_prefix(s, n, cp) <= n,
    decreases n
{
    if n > 0 {
        lemma_count_lt_eq_le_len(s, n - 1, cp);
        assert(count_lt_code(s, n, cp) == if (s[n - 1] as int) < cp {
            1 + count_lt_code(s, n - 1, cp)
        } else {
            count_lt_code(s, n - 1, cp)
        });
        assert(count_eq_prefix(s, n, cp) == if (s[n - 1] as int) == cp {
            1 + count_eq_prefix(s, n - 1, cp)
        } else {
            count_eq_prefix(s, n - 1, cp)
        });
        if (s[n - 1] as int) < cp {
            assert(!((s[n - 1] as int) == cp));
        } else if (s[n - 1] as int) == cp {
        } else {
            assert(count_lt_code(s, n, cp) + count_eq_prefix(s, n, cp)
                == count_lt_code(s, n - 1, cp)
                    + count_eq_prefix(s, n - 1, cp));
        }
    }
}

/// The scan witness guarantees an occurrence: m cannot still be -1.
proof fn lemma_min_occurs(s: Seq<char>, mcp_idx: int, cq: int, m: int, j2: int)
    requires
        0 <= j2 <= s.len(),
        0 <= mcp_idx < s.len(),
        mcp_idx < j2,
        (s[mcp_idx] as int) == cq,
        m >= -1,
        m == -1
            ==> (forall |k: int| #![trigger s[k]]
                0 <= k < j2 ==> ((s[k] as int) != cq)),
    ensures
        m >= 0,
{
    if m == -1 {
        assert((s[mcp_idx] as int) == cq);
        assert(!((s[mcp_idx] as int) != cq));
        assert(false);
    }
}

/// A witnessed == cp position makes the total multiplicity count positive.
proof fn lemma_count_eq_witness(s: Seq<char>, n: int, cp: int, k: int)
    requires
        0 <= n <= s.len(),
        0 <= k < n,
        (s[k] as int) == cp,
    ensures
        count_eq_prefix(s, n, cp) >= 1,
{
    lemma_count_nonneg_eq(s, k, cp);
    lemma_count_eq_step(s, k, cp);
    assert(count_eq_prefix(s, k + 1, cp) == 1 + count_eq_prefix(s, k, cp));
    assert(count_eq_prefix(s, k + 1, cp) >= 1);
    lemma_count_eq_mono(s, k + 1, n, cp);
    assert(count_eq_prefix(s, n, cp) >= count_eq_prefix(s, k + 1, cp));
}

/// Nonnegativity of the multiplicity count.
proof fn lemma_count_nonneg_eq(s: Seq<char>, n: int, cp: int)
    ensures
        count_eq_prefix(s, n, cp) >= 0,
    decreases n
{
    if n > 0 {
        lemma_count_nonneg_eq(s, n - 1, cp);
        assert(count_eq_prefix(s, n, cp) == if (s[n - 1] as int) == cp {
            1 + count_eq_prefix(s, n - 1, cp)
        } else {
            count_eq_prefix(s, n - 1, cp)
        });
    }
}

/// One-step relation for the multiplicity count at a matching char.
proof fn lemma_count_eq_step(s: Seq<char>, n: int, cp: int)
    requires
        0 <= n < s.len(),
        (s[n] as int) == cp,
    ensures
        count_eq_prefix(s, n + 1, cp) == 1 + count_eq_prefix(s, n, cp),
{
    assert(count_eq_prefix(s, n + 1, cp) == if (s[n] as int) == cp {
        1 + count_eq_prefix(s, n, cp)
    } else {
        count_eq_prefix(s, n, cp)
    });
}

/// The == cp prefix count is monotone in the prefix length.
proof fn lemma_count_eq_mono(s: Seq<char>, a: int, b: int, cp: int)
    requires
        0 <= a <= b,
    ensures
        count_eq_prefix(s, a, cp) <= count_eq_prefix(s, b, cp),
    decreases b - a
{
    if a == b {
    } else {
        assert(b >= 1);
        lemma_count_eq_mono(s, a, b - 1, cp);
        assert(count_eq_prefix(s, b, cp) == if (s[b - 1] as int) == cp {
            1 + count_eq_prefix(s, b - 1, cp)
        } else {
            count_eq_prefix(s, b - 1, cp)
        });
    }
}

/// The span-emptiness count lemma: with no char in [cp, cp_hi), the two
/// below-counts agree (the min-scan's guarantee preserves the handled count
/// across the code_point move).
proof fn lemma_count_lt_mono_gap(s: Seq<char>, n: int, cp: int, cp_hi: int)
    requires
        0 <= n,
        cp <= cp_hi,
        forall |k: int| #![trigger s[k]]
            0 <= k < n ==> (!((cp <= (s[k] as int)) && ((s[k] as int) < cp_hi))),
    ensures
        count_lt_code(s, n, cp_hi) == count_lt_code(s, n, cp),
    decreases n
{
    if n > 0 {
        lemma_count_lt_mono_gap(s, n - 1, cp, cp_hi);
        assert(!((cp <= (s[n - 1] as int)) && ((s[n - 1] as int) < cp_hi)));
        assert(count_lt_code(s, n, cp_hi) == if (s[n - 1] as int) < cp_hi {
            1 + count_lt_code(s, n - 1, cp_hi)
        } else {
            count_lt_code(s, n - 1, cp_hi)
        });
        assert(count_lt_code(s, n, cp) == if (s[n - 1] as int) < cp {
            1 + count_lt_code(s, n - 1, cp)
        } else {
            count_lt_code(s, n - 1, cp)
        });
        if (s[n - 1] as int) < cp {
            assert((s[n - 1] as int) < cp_hi);
        } else {
            assert(!((s[n - 1] as int) < cp_hi) || (cp_hi <= (s[n - 1] as int)));
        }
    }
}

/// The post-reset increment count bounded by the interval length.
proof fn lemma_count_between_bound(s: Seq<char>, lo: int, n: int, cp: int)
    requires
        lo <= n,
    ensures
        count_lt_between(s, lo, n, cp) <= n - lo,
    decreases n - lo
{
    if n > lo {
        assert(count_lt_between(s, lo, n, cp)
            == count_lt_between(s, lo, n - 1, cp)
                + (if (s[n - 1] as int) < cp { 1int } else { 0int }));
        lemma_count_between_bound(s, lo, n - 1, cp);
        assert(count_lt_between(s, lo, n - 1, cp) <= n - 1 - lo);
    }
}

/// The last-discovered delimiter index is either -1 or a valid index of s.
proof fn lemma_last_delim_range(s: Seq<u8>)
    ensures
        last_delim(s) == -1 || (0 <= last_delim(s) < s.len()),
    decreases s.len()
{
    lemma_last_delim_from_range(s, 0);
}

proof fn lemma_last_delim_from_range(s: Seq<u8>, m: int)
    requires
        0 <= m <= s.len(),
    ensures
        last_delim_from(s, m) == -1 || (m <= last_delim_from(s, m) < s.len()),
    decreases s.len() - m
{
    if m >= s.len() {
    } else {
        lemma_last_delim_from_range(s, m + 1);
        let t = last_delim_from(s, m + 1);
        if t >= 0 {
            assert(last_delim_from(s, m) == t);
        } else {
            // leave it to the definition: either m (a valid index) or -1
            if s[m] == 0x2D {
                assert(last_delim_from(s, m) == m);
            } else {
                assert(last_delim_from(s, m) == -1);
            }
        }
    }
}

/// Evaluations of the exponent tables used by the loop-bound arguments
proof fn lemma_powers()
    ensures
        powi(35, 0) == 1,
        powi(35, 1) == 35,
        powi(35, 2) == 1225,
        powi(35, 3) == 42875,
        powi(35, 4) == 1500625,
        powi(35, 5) == 52521875,
        powi(10, 0) == 1,
        powi(10, 1) == 10,
        powi(10, 2) == 100,
        powi(10, 3) == 1000,
        powi(10, 4) == 10000,
        powi(10, 5) == 100000,
        powi(10, 6) == 1000000,
        powi(10, 7) == 10000000,
        powi(10, 8) == 100000000,
        powi(10, 9) == 1000000000,
        powi(10, 10) == 10000000000,
        powi(10, 10) > 4294967295,
        powi(35, 5) * 456 > 4294967295,
{
    assert(powi(35, 0) == 1);
    assert(powi(35, 1) == 35);
    assert(powi(35, 2) == 35 * 35);
    assert(powi(35, 3) == 35 * 1225);
    assert(powi(35, 4) == 35 * 42875);
    assert(powi(35, 5) == 35 * 1500625);
    assert(35 * 1500625 == 52521875);
    assert(powi(10, 0) == 1);
    assert(powi(10, 1) == 10);
    assert(powi(10, 2) == 10 * 10);
    assert(powi(10, 3) == 10 * 100);
    assert(powi(10, 4) == 10 * 1000);
    assert(powi(10, 5) == 10 * 10000);
    assert(powi(10, 6) == 10 * 100000);
    assert(powi(10, 7) == 10 * 1000000);
    assert(powi(10, 8) == 10 * 10000000);
    assert(powi(10, 9) == 10 * 100000000);
    assert(powi(10, 10) == 10 * 1000000000);
    assert(10 * 1000000000 == 10000000000);
    assert(10000000000 > 4294967295);
    assert(52521875 * 456 > 4294967295);
}


/// Emission step bookkeeping: the digit chunk shrinks q by the factor
/// (BASE - t) >= 10 while k grows by BASE, keeping the k-bound invariant.
proof fn lemma_emit_step(kit: int, qv_pre: int, t: int, qv_new: int)
    requires
        kit >= 0,
        1 <= t <= 26,
        qv_new == (qv_pre - t) / (36 - t),
        0 <= qv_new,
        powi(10, kit) * qv_pre <= 4294967295,
    ensures
        powi(10, kit + 1) * qv_new <= 4294967295,
{
    let f = 36int - t;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(qv_pre - t, f);
    assert((qv_pre - t) == qv_new * f + (qv_pre - t) % f);
    assert(0 <= (qv_pre - t) % f);
    assert(qv_new * f <= qv_pre - t);
    assert(10 <= f);
    // 10 * qv_new <= qv_new * f <= qv_pre - t
    vstd::arithmetic::mul::lemma_mul_inequality(10, f, qv_new);
    vstd::arithmetic::mul::lemma_mul_is_commutative(10, qv_new);
    assert(10 * qv_new <= qv_new * f);
    assert(10 * qv_new <= qv_pre - t);
    assert(10 * qv_new <= qv_pre);
    // powi(10, kit+1) * qv_new == powi(10, kit) * (10 * qv_new)
    lemma_powi_step(10, kit + 1);
    assert(powi(10, kit + 1) == 10 * powi(10, kit));
    lemma_powi_pos(10, kit + 1);
    assert(1 <= powi(10, kit));
    vstd::arithmetic::mul::lemma_mul_is_associative(10, powi(10, kit), qv_new);
    vstd::arithmetic::mul::lemma_mul_is_associative(powi(10, kit), 10, qv_new);
    vstd::arithmetic::mul::lemma_mul_is_commutative(10, powi(10, kit));
    assert(powi(10, kit + 1) * qv_new
        == powi(10, kit) * (10 * qv_new));
    vstd::arithmetic::mul::lemma_mul_is_commutative(10 * qv_new, powi(10, kit));
    vstd::arithmetic::mul::lemma_mul_is_commutative(qv_pre, powi(10, kit));
    vstd::arithmetic::mul::lemma_mul_inequality(
        10 * qv_new,
        qv_pre,
        powi(10, kit),
    );
    assert((10 * qv_new) * powi(10, kit) <= qv_pre * powi(10, kit));
    assert((10 * qv_new) * powi(10, kit) == powi(10, kit) * (10 * qv_new));
    assert(qv_pre * powi(10, kit) == powi(10, kit) * qv_pre);
    assert(powi(10, kit) * (10 * qv_new) <= powi(10, kit) * qv_pre);
    assert(powi(10, kit + 1) * qv_new <= 4294967295);
}

/// The emission digit chunk strictly shrinks (the loop termination witness).
proof fn lemma_emit_dec(qv_pre: int, t: int, qv_new: int)
    requires
        1 <= t <= 26,
        0 <= qv_new,
        qv_pre >= t,
        qv_new == (qv_pre - t) / (36 - t),
    ensures
        qv_new < qv_pre,
{
    let f = 36int - t;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(qv_pre - t, f);
    assert((qv_pre - t) == qv_new * f + (qv_pre - t) % f);
    assert(0 <= (qv_pre - t) % f);
    assert(qv_new * f <= qv_pre - t);
    assert(10 <= f);
    vstd::arithmetic::mul::lemma_mul_is_commutative(qv_new, f);
    assert(qv_new * f <= qv_pre - t < qv_pre);
    vstd::arithmetic::mul::lemma_mul_strict_inequality(qv_new, qv_pre, f);
    assert(qv_new < qv_pre);
}

/* ============================================================
 * Internal-caller (uts46 path) support lemmas
 * ============================================================ */

/// The model's last-delimiter position is either -1 (no '-' at all) or
/// a '-' position with no '-' strictly after it (the maximal one).
/// Needed to bridge an exec last-dash scan over a byte sequence to
/// the last_delim spec model (decode_char_internal).
proof fn lemma_last_delim_max(v: Seq<u8>)
    ensures
        (last_delim(v) == -1
            && (forall |j: int| 0 <= j < v.len() ==> v[j] != 0x2D))
            || (last_delim(v) >= 0 && v[last_delim(v)] == 0x2D
                && (forall |j: int| last_delim(v) < j < v.len()
                    ==> v[j] != 0x2D)),
{
    lemma_last_delim_from_max(v, 0);
    if last_delim(v) == -1 {
        assert forall |j: int| 0 <= j < v.len() implies
            (v[j] != 0x2D) by {}
    }
}

proof fn lemma_last_delim_from_max(v: Seq<u8>, m: int)
    requires
        0 <= m <= v.len(),
    ensures
        (last_delim_from(v, m) == -1
            && (forall |j: int| m <= j < v.len() ==> v[j] != 0x2D))
            || (last_delim_from(v, m) >= 0
                && m <= last_delim_from(v, m)
                && v[last_delim_from(v, m)] == 0x2D
                && (forall |j: int| last_delim_from(v, m) < j < v.len()
                    ==> v[j] != 0x2D)),
    decreases v.len() - m
{
    if m < v.len() {
        lemma_last_delim_from_max(v, m + 1);
        assert(last_delim_from(v, m) == (if last_delim_from(v, m + 1) >= 0 {
            last_delim_from(v, m + 1)
        } else if v[m] == 0x2D {
            m
        } else {
            -1
        })) by {
            reveal_with_fuel(last_delim_from, 1);
        };
        if last_delim_from(v, m + 1) >= 0 {
            // the tail found the last dash; pass its arm through
        } else {
            // tail found none: the verdict depends on v[m] alone
            if v[m] == 0x2D {
                assert(last_delim_from(v, m) == m);
            } else {
                assert(last_delim_from(v, m) == -1);
                assert forall |j: int| m <= j < v.len() implies
                    (v[j] != 0x2D) by {
                    if j == m {
                        assert(v[m] != 0x2D);
                    } else {
                        assert(m + 1 <= j);
                        assert(v[j] != 0x2D);
                    }
                }
            }
        }
    }
}

/* ============================================================
 * Internal-caller encode: the RFC 3492 section 6.4 no-overflow lemmas.
 * Under the one-shot product
 *   (len + 1) * (char::MAX - INITIAL_N) <= u32::MAX,
 * none of the u32 guards of the external refinement model
 * (enc_outer_model / enc_scan_model) can fire at any reachable state,
 * so the internal caller's unchecked delta arithmetic carries the same
 * values as the external checked loop and the encode output is the
 * full model's emission.
 * ============================================================ */

// ---- int-code counting helpers (the char-typed count models of the
// ---- encode face cover char inputs only; this induction runs over the
// ---- int-code space of enc_outer_model).

/// Number of positions in [0, j) whose code is < cp.
pub open spec fn cnt_lt_codes(s: Seq<int>, j: int, cp: int) -> int
    decreases j
{
    if j <= 0 {
        0
    } else if s[j - 1] < cp {
        1 + cnt_lt_codes(s, j - 1, cp)
    } else {
        cnt_lt_codes(s, j - 1, cp)
    }
}

/// Number of positions in [lo, j) whose code is < cp.
pub open spec fn cnt_lt_codes_between(s: Seq<int>, lo: int, j: int, cp: int) -> int
    decreases j - lo
{
    if j <= lo {
        0
    } else if s[j - 1] < cp {
        1 + cnt_lt_codes_between(s, lo, j - 1, cp)
    } else {
        cnt_lt_codes_between(s, lo, j - 1, cp)
    }
}

/// Number of positions in [lo, j) whose code equals cp.
pub open spec fn cnt_eq_codes_between(s: Seq<int>, lo: int, j: int, cp: int) -> int
    decreases j - lo
{
    if j <= lo {
        0
    } else if s[j - 1] == cp {
        1 + cnt_eq_codes_between(s, lo, j - 1, cp)
    } else {
        cnt_eq_codes_between(s, lo, j - 1, cp)
    }
}

/// Inductive "no position in [lo, j) equals m" view of the scan's
/// entry phase (a structural replacement for a quantified no-m
/// premise; the recursion unfolds deterministically).
pub open spec fn no_eq_below(input: Seq<int>, lo: int, j: int, m: int) -> bool
    decreases j - lo
{
    if j <= lo {
        true
    } else {
        input[j - 1] != m && no_eq_below(input, lo, j - 1, m)
    }
}

/// One-position step of no_eq_below at the high end.
proof fn lemma_no_eq_step(input: Seq<int>, lo: int, j: int, m: int)
    requires
        lo < j,
    ensures
        no_eq_below(input, lo, j, m)
            <==> (no_eq_below(input, lo, j - 1, m) && input[j - 1] != m),
{
    reveal_with_fuel(no_eq_below, 1);
}

/// Witness extraction: no position in [lo, j) equals m.
proof fn lemma_no_eq_witness(input: Seq<int>, lo: int, j: int, m: int, w: int)
    requires
        lo <= w < j,
        no_eq_below(input, lo, j, m),
    ensures
        input[w] != m,
    decreases j - lo
{
    if j > lo {
        reveal_with_fuel(no_eq_below, 1);
        if w == j - 1 {
            // the exposed conjunct is the witness position
            assert(input[j - 1] != m);
        } else {
            assert(lo <= w < j - 1);
            lemma_no_eq_witness(input, lo, j - 1, m, w);
        }
    }
}

/// Definitional step of the below-count on a scrolling range end.
proof fn lemma_cnt_lt_bt_step(s: Seq<int>, lo: int, j: int, cp: int)
    requires
        lo < j <= s.len() as int,
    ensures
        cnt_lt_codes_between(s, lo, j, cp)
            == (cnt_lt_codes_between(s, lo, j - 1, cp)
                + (if s[j - 1] < cp { 1int } else { 0int })),
{
    reveal_with_fuel(cnt_lt_codes_between, 1);
}

/// Definitional step of the eq-count on a scrolling range end.
proof fn lemma_cnt_eq_bt_step(s: Seq<int>, lo: int, j: int, cp: int)
    requires
        lo < j <= s.len() as int,
    ensures
        cnt_eq_codes_between(s, lo, j, cp)
            == (cnt_eq_codes_between(s, lo, j - 1, cp)
                + (if s[j - 1] == cp { 1int } else { 0int })),
{
    reveal_with_fuel(cnt_eq_codes_between, 1);
}

/// A between-count is at most the number of positions it spans.
proof fn lemma_cnt_lt_bt_bound(s: Seq<int>, lo: int, j: int, cp: int)
    requires
        lo <= j <= s.len() as int,
    ensures
        cnt_lt_codes_between(s, lo, j, cp) <= j - lo,
    decreases j - lo
{
    if j > lo {
        lemma_cnt_lt_bt_bound(s, lo, j - 1, cp);
        lemma_cnt_lt_bt_step(s, lo, j, cp);
    }
}

/// The between-count is nonnegative.
proof fn lemma_cnt_lt_bt_nonneg(s: Seq<int>, lo: int, j: int, cp: int)
    requires
        lo <= j <= s.len() as int,
    ensures
        0 <= cnt_lt_codes_between(s, lo, j, cp),
    decreases j - lo
{
    if j > lo {
        lemma_cnt_lt_bt_nonneg(s, lo, j - 1, cp);
    }
}

/// Shrinking the range start can only shrink the between-count.
proof fn lemma_cnt_lt_bt_subrange(s: Seq<int>, lo1: int, lo2: int, j: int, cp: int)
    requires
        lo1 <= lo2 <= j <= s.len() as int,
    ensures
        cnt_lt_codes_between(s, lo2, j, cp)
            <= cnt_lt_codes_between(s, lo1, j, cp),
    decreases j - lo1
{
    if j <= lo2 {
        // the [lo2, j) range is empty
        assert(cnt_lt_codes_between(s, lo2, j, cp) == 0) by {
            reveal_with_fuel(cnt_lt_codes_between, 1);
        }
        lemma_cnt_lt_bt_nonneg(s, lo1, j, cp);
    } else {
        lemma_cnt_lt_bt_step(s, lo2, j, cp);
        lemma_cnt_lt_bt_step(s, lo1, j, cp);
        lemma_cnt_lt_bt_subrange(s, lo1, lo2, j - 1, cp);
    }
}

/// The full-prefix below-count equals the between-count from zero.
proof fn lemma_cnt_lt_bt_zero(s: Seq<int>, j: int, cp: int)
    requires
        0 <= j <= s.len() as int,
    ensures
        cnt_lt_codes_between(s, 0, j, cp) == cnt_lt_codes(s, j, cp),
    decreases j
{
    if j > 0 {
        lemma_cnt_lt_bt_zero(s, j - 1, cp);
        lemma_cnt_lt_bt_step(s, 0, j, cp);
        if s[j - 1] < cp {
            assert(cnt_lt_codes(s, j, cp) == 1 + cnt_lt_codes(s, j - 1, cp)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
        } else {
            assert(cnt_lt_codes(s, j, cp) == cnt_lt_codes(s, j - 1, cp)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
        }
    }
}

/// Number of positions in [0, j) whose code equals cp (full-prefix
/// eq-count).
pub open spec fn cnt_eq_codes(s: Seq<int>, j: int, cp: int) -> int
    decreases j
{
    if j <= 0 {
        0
    } else if s[j - 1] == cp {
        1 + cnt_eq_codes(s, j - 1, cp)
    } else {
        cnt_eq_codes(s, j - 1, cp)
    }
}

/// The eq-count between 0 and j equals the full-prefix eq-count.
proof fn lemma_cnt_eq_zero(s: Seq<int>, j: int, cp: int)
    requires
        0 <= j <= s.len() as int,
    ensures
        cnt_eq_codes_between(s, 0, j, cp) == cnt_eq_codes(s, j, cp),
    decreases j
{
    if j > 0 {
        lemma_cnt_eq_zero(s, j - 1, cp);
        lemma_cnt_eq_bt_step(s, 0, j, cp);
        if s[j - 1] == cp {
            assert(cnt_eq_codes(s, j, cp) == 1 + cnt_eq_codes(s, j - 1, cp)) by {
                reveal_with_fuel(cnt_eq_codes, 1);
            }
        } else {
            assert(cnt_eq_codes(s, j, cp) == cnt_eq_codes(s, j - 1, cp)) by {
                reveal_with_fuel(cnt_eq_codes, 1);
            }
        }
    }
}

/// Pointwise split of the below-count under a gap premise: with no codes
/// in [gap_lo, gap_hi) (and gap_lo <= gap_hi), the count below gap_hi+1
/// is the count below gap_lo plus the count equal to gap_hi (the only
/// surviving value in [gap_lo, gap_hi+1)).
proof fn lemma_cnt_lt_split(s: Seq<int>, j: int, gap_lo: int, gap_hi: int)
    requires
        0 <= j <= s.len() as int,
        gap_lo <= gap_hi,
        forall |k: int| #![trigger s[k]] 0 <= k < s.len() as int
            ==> (!(gap_lo <= s[k] && s[k] < gap_hi)),
    ensures
        cnt_lt_codes(s, j, gap_hi + 1)
            == cnt_lt_codes(s, j, gap_lo) + cnt_eq_codes(s, j, gap_hi),
    decreases j
{
    if j > 0 {
        lemma_cnt_lt_split(s, j - 1, gap_lo, gap_hi);
        if s[j - 1] < gap_lo {
            assert(cnt_lt_codes(s, j, gap_hi + 1)
                == 1 + cnt_lt_codes(s, j - 1, gap_hi + 1)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
            assert(cnt_lt_codes(s, j, gap_lo)
                == 1 + cnt_lt_codes(s, j - 1, gap_lo)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
            assert(cnt_eq_codes(s, j, gap_hi)
                == cnt_eq_codes(s, j - 1, gap_hi)) by {
                reveal_with_fuel(cnt_eq_codes, 1);
            }
        } else if s[j - 1] == gap_hi {
            assert(cnt_lt_codes(s, j, gap_hi + 1)
                == 1 + cnt_lt_codes(s, j - 1, gap_hi + 1)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
            assert(cnt_lt_codes(s, j, gap_lo)
                == cnt_lt_codes(s, j - 1, gap_lo)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
            assert(cnt_eq_codes(s, j, gap_hi)
                == 1 + cnt_eq_codes(s, j - 1, gap_hi)) by {
                reveal_with_fuel(cnt_eq_codes, 1);
            }
        } else {
            // s[j-1] >= gap_hi + 1 (the [gap_lo, gap_hi) range is empty
            // of codes by the premise)
            assert(cnt_lt_codes(s, j, gap_hi + 1)
                == cnt_lt_codes(s, j - 1, gap_hi + 1)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
            assert(cnt_lt_codes(s, j, gap_lo)
                == cnt_lt_codes(s, j - 1, gap_lo)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
            assert(cnt_eq_codes(s, j, gap_hi)
                == cnt_eq_codes(s, j - 1, gap_hi)) by {
                reveal_with_fuel(cnt_eq_codes, 1);
            }
        }
    }
}

/// If every position is below cp, the full-prefix count is the length.
proof fn lemma_cnt_lt_all(s: Seq<int>, j: int, cp: int)
    requires
        0 <= j <= s.len() as int,
        forall |k: int| #![trigger s[k]] 0 <= k < j ==> s[k] < cp,
    ensures
        cnt_lt_codes(s, j, cp) == j,
    decreases j
{
    if j > 0 {
        lemma_cnt_lt_all(s, j - 1, cp);
        assert(s[j - 1] < cp);
        assert(cnt_lt_codes(s, j, cp) == 1 + cnt_lt_codes(s, j - 1, cp)) by {
            reveal_with_fuel(cnt_lt_codes, 1);
        }
    }
}

/// If the prefix count below cp drops under the prefix length, some
/// position below the prefix end is at or above cp.
proof fn lemma_cnt_lt_some_ge_frontier(s: Seq<int>, j: int, cp: int)
    requires
        0 <= j <= s.len() as int,
        cnt_lt_codes(s, j, cp) < j,
    ensures
        exists |w: int| 0 <= w < j && s[w] >= cp,
    decreases j
{
    if j > 0 {
        if s[j - 1] >= cp {
            assert(exists |w: int| 0 <= w < j && s[w] >= cp) by {
                assert(s[j - 1] >= cp);
            }
        } else {
            lemma_cnt_lt_some_ge_frontier(s, j - 1, cp);
            assert(cnt_lt_codes(s, j, cp) == 1 + cnt_lt_codes(s, j - 1, cp)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
                assert(s[j - 1] < cp);
            }
            assert(cnt_lt_codes(s, j - 1, cp) < j - 1);
            assert(exists |w: int| 0 <= w < j && s[w] >= cp) by {
                assert(exists |w: int| 0 <= w < j - 1 && s[w] >= cp);
            }
        }
    }
}

/// count_basic_codes over the int codes equals the below-0x80 prefix count.
proof fn lemma_count_basics_is_lt(s: Seq<int>)
    ensures
        count_basic_codes(s, 0) == cnt_lt_codes(s, s.len() as int, 128),
{
    lemma_count_basics_is_lt_from(s, 0);
}

proof fn lemma_count_basics_is_lt_from(s: Seq<int>, j: int)
    requires
        0 <= j <= s.len() as int,
    ensures
        count_basic_codes(s, j) + cnt_lt_codes(s, j, 128)
            == cnt_lt_codes(s, s.len() as int, 128),
    decreases s.len() as int - j
{
    if j < s.len() as int {
        lemma_count_basics_is_lt_from(s, j + 1);
        assert(count_basic_codes(s, j)
            == ((if s[j] < 128 { 1int } else { 0int })
                + count_basic_codes(s, j + 1))) by {
            reveal_with_fuel(count_basic_codes, 1);
        }
        if s[j] < 128 {
            assert(cnt_lt_codes(s, j + 1, 128)
                == 1 + cnt_lt_codes(s, j, 128)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
        } else {
            assert(cnt_lt_codes(s, j + 1, 128)
                == cnt_lt_codes(s, j, 128)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
        }
    }
}

/// min_ge is -1 exactly when every position from the start on is below n.
proof fn lemma_min_ge_neg_iff(input: Seq<int>, n: int, j: int)
    requires
        0 <= j <= input.len() as int,
        0 <= n,
        forall |k: int| #![trigger input[k]] 0 <= k < input.len() as int
            ==> 0 <= input[k],
    ensures
        (min_ge(input, n, j) == -1)
            <==> (forall |k: int| j <= k < input.len() as int
                ==> input[k] < n),
    decreases input.len() as int - j
{
    if j < input.len() as int {
        lemma_min_ge_neg_iff(input, n, j + 1);
        let rest = min_ge(input, n, j + 1);
        let here = min_ge(input, n, j);
        assert(here == (if rest < 0 {
            (if input[j] >= n { input[j] } else { -1 })
        } else if input[j] >= n && input[j] < rest {
            input[j]
        } else {
            rest
        })) by {
            reveal_with_fuel(min_ge, 1);
        }
        if rest >= 0 {
            assert(here == rest || here == input[j]);
        } else {
            assert(here == input[j] || here == -1);
        }
    }
}

/// The positive min_ge value is the minimum of the positions at or
/// above n: nothing straddles [n, min_ge).
proof fn lemma_min_ge_unstraddled(input: Seq<int>, n: int, j: int)
    requires
        0 <= j <= input.len() as int,
        0 <= n,
        forall |k: int| #![trigger input[k]] 0 <= k < input.len() as int
            ==> 0 <= input[k],
        min_ge(input, n, j) >= 0,
    ensures
        forall |k: int| #![trigger input[k]] j <= k < input.len() as int
            ==> (!(n <= input[k] && input[k] < min_ge(input, n, j))),
    decreases input.len() as int - j
{
    if j < input.len() as int {
        let rest = min_ge(input, n, j + 1);
        let here = min_ge(input, n, j);
        assert(here == (if rest < 0 {
            (if input[j] >= n { input[j] } else { -1 })
        } else if input[j] >= n && input[j] < rest {
            input[j]
        } else {
            rest
        })) by {
            reveal_with_fuel(min_ge, 1);
        };
        if rest < 0 {
            // no position at or above n in the tail
            lemma_min_ge_neg_iff(input, n, j + 1);
            assert(forall |k: int| #![trigger input[k]] j + 1 <= k
                < input.len() as int ==> (input[k] < n));
            assert(input[j] >= n);
            assert(here == input[j]);
        } else {
            lemma_min_ge_unstraddled(input, n, j + 1);
            if input[j] >= n && input[j] < rest {
                assert(here == input[j]);
                // the tail is covered against rest > here
            } else {
                assert(here == rest);
            }
        }
    }
}

/// The one-shot arithmetic: from (len+1)*M <= u32::MAX (M = 0x10FFFF-0x80)
/// derive the lengths and guard slack used by the inductions.
proof fn lemma_one_shot_arith(len: int)
    requires
        0 <= len,
        (len + 1) * 1113983 <= 4294967295,
    ensures
        len <= 3854,
        len * 1113984 + len + 1 <= 4294967295,
{
    // 3856 * M already exceeds u32::MAX; 3855 * M does not.
    assert(1113983 * 3855 == 4294404465) by (bit_vector);
    assert(1113983 * 3856 == 4295518448) by (bit_vector);
    assert(1113983 * 3856 > 4294967295);
    assert(1113983 * 3855 <= 4294967295);
    if len >= 3855 {
        assert((len + 1) * 1113983 >= 3856 * 1113983) by {
            vstd::arithmetic::mul::lemma_mul_inequality(3856, len + 1, 1113983);
        }
        assert((len + 1) * 1113983 > 4294967295);
        assert(false);
    }
    assert(len <= 3854);
    assert(len * 1113983 <= 4294967295 - 1113983) by {
        assert((len + 1) * 1113983 == len * 1113983 + 1113983);
    }
    assert(len * 1113984 == len * 1113983 + len);
    assert(len * 1113984 + len + 1
        == len * 1113983 + 2 * len + 1);
    assert(2 * len + 2 <= 7710);
    assert(len * 1113983 + 2 * len + 1 + 1
        <= len * 1113983 + 7710);
    assert(len * 1113984 + len + 1 <= 4294967295) by {
        assert(len * 1113983 + 2 * len + 1
            <= (4294967295 - 1113983) + 2 * len + 1);
        assert(2 * len + 1 <= 7709 <= 1113983 - 1273);
    }
}

/// The full-prefix below-count is at most the number of positions.
proof fn lemma_cnt_lt_bound(s: Seq<int>, j: int, cp: int)
    requires
        0 <= j <= s.len() as int,
    ensures
        0 <= cnt_lt_codes(s, j, cp) <= j,
    decreases j
{
    if j > 0 {
        lemma_cnt_lt_bound(s, j - 1, cp);
        reveal_with_fuel(cnt_lt_codes, 1);
    }
}

/// The scan induction of the internal-caller no-overflow argument:
/// staged exact-value tracking of the two delta phases along the inner
/// scan of encode_into (the pre-first-emit phase carries the entry
/// delta plus the below-counts so far; the post-emit phase carries the
/// below-counts since the last emit). Conclusions: none of the scan's
/// delta+1 guards can fire; the exit handled-count is the entry count
/// plus all emitted positions; the exit delta is either the
/// entry-plus-below-counts value (when no emit ever fired, i.e. no
/// position equals the scan code point) or the below-counts since the
/// last emit (capped by the full prefix count).
proof fn lemma_scan_guarded(
    input: Seq<int>,
    m: int,
    j: int,
    delta: int,
    bias: int,
    h: int,
    b: int,
    out: Seq<int>,
    hh0: int,
    delta0: int,
    p: int,
)
    requires
        forall |k: int| #![trigger input[k]] 0 <= k < input.len() as int
            ==> (0 <= input[k] && input[k] <= 0x10FFFF),
        0 <= j <= input.len() as int,
        0 <= m && m <= 0x10FFFF,
        hh0 >= 0,
        0 <= b,
        h == hh0 + cnt_eq_codes_between(input, 0, j, m),
        hh0 + cnt_eq_codes_between(input, 0, input.len() as int, m)
            <= input.len() as int,
        (input.len() as int + 1) * 1113983 <= 4294967295,
        delta0 <= input.len() as int * 1113984,
        ((delta == delta0 + cnt_lt_codes_between(input, 0, j, m)
                && p == -1
                && no_eq_below(input, 0, j, m))
            || (p >= 0 && p < j && input[p] == m
                && delta == cnt_lt_codes_between(input, p + 1, j, m))),
    ensures
        match enc_scan_model(input, m, j, delta, bias, h, b, out) {
            Option::None => false,
            Option::Some((dend, _b2, h2, _o2)) => (
                h2 == hh0 + cnt_eq_codes_between(
                        input, 0, input.len() as int, m)
                    && (
                        (dend == delta0
                                + cnt_lt_codes_between(
                                    input, 0, input.len() as int, m)
                            && no_eq_below(
                                input, 0, input.len() as int, m)
                            && dend <= delta0 + input.len() as int)
                        || (exists |pp: int| 0 <= pp < input.len() as int
                            && input[pp] == m
                            && dend == cnt_lt_codes_between(
                                input, pp + 1, input.len() as int, m)
                            && dend
                                <= cnt_lt_codes(
                                    input, input.len() as int, m))
                    )),
        },
    decreases input.len() as int - j
{
    if j >= input.len() as int {
        // base: the scan model returns the current state unchanged
        assert(enc_scan_model(input, m, j, delta, bias, h, b, out)
            == Option::Some((delta, bias, h, out))) by {
            reveal_with_fuel(enc_scan_model, 1);
        }
        if p == -1 {
            // still in the entry phase: no emit ever fired; every
            // position seen differs from m
            assert(delta == delta0 + cnt_lt_codes_between(input, 0, j, m));
            assert(j == input.len() as int);
            assert(no_eq_below(input, 0, input.len() as int, m)) by {}
            lemma_cnt_lt_bt_bound(input, 0, j, m);
            assert(cnt_lt_codes_between(input, 0, j, m) <= j);
        } else {
            // post-emit: the exit delta counts below-codes past p
            assert(delta == cnt_lt_codes_between(input, p + 1, j, m));
            assert(j == input.len() as int);
            lemma_cnt_lt_bt_bound(input, p + 1, j, m);
            lemma_cnt_lt_bt_subrange(input, 0, p + 1, j, m);
            lemma_cnt_lt_bt_zero(input, j, m);
            assert(cnt_lt_codes_between(input, p + 1, j, m)
                <= cnt_lt_codes(input, j, m));
            assert(exists |pp: int| 0 <= pp < input.len() as int
                && input[pp] == m
                && delta == cnt_lt_codes_between(
                    input, pp + 1, input.len() as int, m)) by {
                assert(0 <= p);
                assert(p < input.len() as int);
                assert(input[p] == m);
                assert(delta == cnt_lt_codes_between(
                    input, p + 1, input.len() as int, m));
            }
            assert(delta <= cnt_lt_codes(input, input.len() as int, m));
        }
    } else {
        let c = input[j as int];
        if c < m {
            // below the code point: the delta+1 guard cannot fire
            if p == -1 {
                assert(delta == delta0
                    + cnt_lt_codes_between(input, 0, j, m));
                lemma_one_shot_arith(input.len() as int);
                lemma_cnt_lt_bt_bound(input, 0, j, m);
                lemma_cnt_lt_bt_step(input, 0, j + 1, m);
                assert(delta + 1
                    <= delta0 + input.len() as int + 1);
                assert(delta + 1 <= 4294967295);
                assert(cnt_lt_codes_between(input, 0, j + 1, m)
                    == cnt_lt_codes_between(input, 0, j, m) + 1);
                assert(cnt_eq_codes_between(input, 0, j + 1, m)
                    == cnt_eq_codes_between(input, 0, j, m)) by {
                    lemma_cnt_eq_bt_step(input, 0, j + 1, m);
                }
                lemma_no_eq_step(input, 0, j + 1, m);
                assert(!(input[j as int] == m));
                assert(no_eq_below(input, 0, j + 1, m)) by {
                    assert(no_eq_below(input, 0, j, m));
                }
            } else {
                assert(delta == cnt_lt_codes_between(input, p + 1, j, m));
                lemma_one_shot_arith(input.len() as int);
                lemma_cnt_lt_bt_bound(input, p + 1, j, m);
                lemma_cnt_lt_bt_step(input, p + 1, j + 1, m);
                assert(cnt_lt_codes_between(input, p + 1, j + 1, m)
                    == cnt_lt_codes_between(input, p + 1, j, m) + 1);
                assert(delta + 1 <= input.len() as int + 1);
                assert(delta + 1 <= 4294967295);
                assert(cnt_eq_codes_between(input, 0, j + 1, m)
                    == cnt_eq_codes_between(input, 0, j, m)) by {
                    lemma_cnt_eq_bt_step(input, 0, j + 1, m);
                }
            }
            // sub-scan and model equality
            lemma_scan_guarded(
                input, m, j + 1, delta + 1, bias, h, b, out,
                hh0, delta0, p,
            );
            assert(enc_scan_model(input, m, j, delta, bias, h, b, out)
                == enc_scan_model(
                    input, m, j + 1, delta + 1, bias, h, b, out)) by {
                reveal_with_fuel(enc_scan_model, 1);
            }
        } else if c == m {
            // emit at this position: delta resets, handled count grows
            if p == -1 {
                assert(delta == delta0
                    + cnt_lt_codes_between(input, 0, j, m));
                lemma_one_shot_arith(input.len() as int);
                lemma_cnt_lt_bt_bound(input, 0, j, m);
                assert(delta + 1 <= 4294967295);
            } else {
                assert(delta == cnt_lt_codes_between(input, p + 1, j, m));
                lemma_cnt_lt_bt_bound(input, p + 1, j, m);
                assert(delta + 1 <= 4294967295);
            }
            let out2 = emit_digits_model(delta, 36, bias, out);
            let bias2 = adapt_model(delta, h + 1, h == b);
            lemma_cnt_eq_bt_step(input, 0, j + 1, m);
            assert(cnt_eq_codes_between(input, 0, j + 1, m)
                == cnt_eq_codes_between(input, 0, j, m) + 1);
            // the empty post-reset range at the emit position
            assert(cnt_lt_codes_between(input, j + 1, j + 1, m) == 0) by {
                reveal_with_fuel(cnt_lt_codes_between, 1);
            }
            lemma_scan_guarded(
                input, m, j + 1, 0, bias2, h + 1, b, out2,
                hh0, delta0, j as int,
            );
            assert(enc_scan_model(input, m, j, delta, bias, h, b, out)
                == enc_scan_model(
                    input, m, j + 1, 0, bias2, h + 1, b, out2)) by {
                reveal_with_fuel(enc_scan_model, 1);
            }
        } else {
            // above the code point: state unchanged
            lemma_scan_guarded(
                input, m, j + 1, delta, bias, h, b, out,
                hh0, delta0, p,
            );
            assert(enc_scan_model(input, m, j, delta, bias, h, b, out)
                == enc_scan_model(
                    input, m, j + 1, delta, bias, h, b, out)) by {
                reveal_with_fuel(enc_scan_model, 1);
            }
            lemma_cnt_eq_bt_step(input, 0, j + 1, m);
            assert(cnt_eq_codes_between(input, 0, j + 1, m)
                == cnt_eq_codes_between(input, 0, j, m)) by {
                assert(!(input[j as int] == m));
            }
            if p == -1 {
                lemma_no_eq_step(input, 0, j + 1, m);
                assert(!(input[j as int] == m));
                assert(no_eq_below(input, 0, j + 1, m)) by {
                    assert(no_eq_below(input, 0, j, m));
                }
                assert(cnt_lt_codes_between(input, 0, j + 1, m)
                    == cnt_lt_codes_between(input, 0, j, m)) by {
                    lemma_cnt_lt_bt_step(input, 0, j + 1, m);
                    assert(!(input[j as int] < m));
                }
            } else {
                assert(delta == cnt_lt_codes_between(input, p + 1, j, m));
                assert(cnt_lt_codes_between(input, p + 1, j + 1, m)
                    == cnt_lt_codes_between(input, p + 1, j, m)) by {
                    lemma_cnt_lt_bt_step(input, p + 1, j + 1, m);
                    assert(!(input[j as int] < m));
                }
            }
        }
    }
}

/// The below-count is monotone in the threshold.
proof fn lemma_cnt_lt_mono(s: Seq<int>, j: int, cp1: int, cp2: int)
    requires
        0 <= j <= s.len() as int,
        cp1 <= cp2,
    ensures
        cnt_lt_codes(s, j, cp1) <= cnt_lt_codes(s, j, cp2),
    decreases cp2 - cp1
{
    if cp1 < cp2 {
        lemma_cnt_lt_mono(s, j, cp1, cp2 - 1);
        lemma_cnt_lt_mono_step(s, j, cp2 - 1);
    }
}

/// One-threshold step of the below-count monotonicity: each position
/// below cpm is below cpm+1.
proof fn lemma_cnt_lt_mono_step(s: Seq<int>, j: int, cpm: int)
    requires
        0 <= j <= s.len() as int,
    ensures
        cnt_lt_codes(s, j, cpm) <= cnt_lt_codes(s, j, cpm + 1),
    decreases j
{
    if j > 0 {
        lemma_cnt_lt_mono_step(s, j - 1, cpm);
        if s[j - 1] == cpm {
            assert(cnt_lt_codes(s, j, cpm + 1)
                == 1 + cnt_lt_codes(s, j - 1, cpm + 1)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
            assert(cnt_lt_codes(s, j, cpm)
                == cnt_lt_codes(s, j - 1, cpm)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
        } else if s[j - 1] < cpm {
            assert(cnt_lt_codes(s, j, cpm)
                == 1 + cnt_lt_codes(s, j - 1, cpm)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
            assert(cnt_lt_codes(s, j, cpm + 1)
                == 1 + cnt_lt_codes(s, j - 1, cpm + 1)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
        } else {
            assert(cnt_lt_codes(s, j, cpm)
                == cnt_lt_codes(s, j - 1, cpm)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
            // s[j-1] >= cpm holds and s[j-1] is not below cpm+1,
            // so the threshold count does not advance
            assert(cnt_lt_codes(s, j, cpm + 1)
                == cnt_lt_codes(s, j - 1, cpm + 1)) by {
                reveal_with_fuel(cnt_lt_codes, 1);
            }
        }
    }
}

/// The outer induction of the internal-caller no-overflow argument: at
/// every reachable outer state (handled-count equals the below-n
/// count, entry delta below handled-count-plus-one), the
/// accumulated-delta and trailing guards of enc_outer_model cannot
/// fire, the min scan finds a code point in range, and the recursive
/// next state satisfies the same premises.
proof fn lemma_outer_no_overflow(
    input: Seq<int>,
    n: int,
    h: int,
    delta: int,
    bias: int,
    b: int,
    out: Seq<int>,
)
    requires
        forall |k: int| #![trigger input[k]] 0 <= k < input.len() as int
            ==> (0 <= input[k] && input[k] <= 0x10FFFF),
        0x80 <= n,
        0 <= h < input.len() as int,
        delta <= h + 1,
        h == cnt_lt_codes(input, input.len() as int, n),
        0 <= b,
        (input.len() as int + 1) * 1113983 <= 4294967295,
    ensures
        enc_outer_model(input, n, h, delta, bias, b, out).is_some(),
    decreases 0x110001 - n
{
    let len_i = input.len() as int;
    lemma_one_shot_arith(len_i);
    lemma_cnt_lt_bound(input, len_i, n);
    // the min over handled-below codes exists
    let mg = min_ge(input, n, 0);
    if mg < 0 {
        // every position is below n: the handled count is the length,
        // contradicting h < len
        lemma_min_ge_neg_iff(input, n, 0);
        assert(forall |k: int| #![trigger input[k]] 0 <= k < len_i
            ==> (input[k] < n));
        lemma_cnt_lt_all(input, len_i, n);
        assert(cnt_lt_codes(input, len_i, n) == len_i);
        assert(false) by {}
    }
    assert(mg >= 0);
    // mg is a real code in range [n, 0x10FFFF]
    lemma_min_ge_lb(input, n, 0);
    assert(exists |w: int|
        (0 <= w < len_i && mg == input[w] && mg >= n));
    assert(mg <= 0x10FFFF) by {}
    // no code straddles [n, mg)
    lemma_min_ge_unstraddled(input, n, 0);
    assert(forall |k: int| #![trigger input[k]] 0 <= k < len_i
        ==> (!(n <= input[k] && input[k] < mg)));
    // count split at the gap [n, mg)
    lemma_cnt_lt_split(input, len_i, n, mg);
    assert(cnt_lt_codes(input, len_i, mg + 1)
        == cnt_lt_codes(input, len_i, n) + cnt_eq_codes(input, len_i, mg));
    lemma_cnt_lt_bound(input, len_i, mg + 1);
    // the between-form of the emit count
    lemma_cnt_eq_zero(input, len_i, mg);
    assert(cnt_eq_codes_between(input, 0, len_i, mg)
        == cnt_eq_codes(input, len_i, mg));
    // accumulated delta bound of this outer state
    let d_m = delta + (mg - n) * (h + 1);
    assert(mg - n <= 1113983) by {
        assert(mg <= 0x10FFFF);
        assert(n >= 0x80);
    }
    assert(h + 1 <= len_i);
    vstd::arithmetic::mul::lemma_mul_inequality(mg - n, 1113983, h + 1);
    assert((mg - n) * (h + 1) <= 1113983 * (h + 1));
    assert(1113983 * (h + 1) + (h + 1) == 1113984 * (h + 1)) by {
        assert(1113983 + 1 == 1113984);
        vstd::arithmetic::mul::lemma_mul_is_commutative(h + 1, 1113983);
        assert((1113983 + 1) * (h + 1)
            == 1113983 * (h + 1) + 1 * (h + 1)) by {}
    }
    assert(d_m <= (h + 1) * 1113984) by {
        assert(delta <= h + 1);
        assert(d_m == delta + (mg - n) * (h + 1));
    }
    assert(d_m <= len_i * 1113984);
    assert(!(d_m > 4294967295)) by {
        assert(len_i * 1113984 + len_i + 1 <= 4294967295);
    }
    // the clamped model code point is mg itself
    assert((if mg < 0 || mg >= 0x110000 { -1 } else { mg }) == mg) by {}
    // one outer unfold
    assert(enc_outer_model(input, n, h, delta, bias, b, out)
        == (if d_m > 4294967295 {
            Option::None
        } else {
            match enc_scan_model(input, mg, 0, d_m, bias, h, b, out) {
                Option::None => Option::None,
                Option::Some((dend, biasend, hend, outend)) => {
                    let d2 = dend + 1;
                    if d2 > 4294967295 {
                        Option::None
                    } else {
                        enc_outer_model(
                            input, mg + 1, hend, d2, biasend, b, outend)
                    }
                }
            }
        })) by {
        reveal_with_fuel(enc_outer_model, 1);
    }
    // scan handles the h correspondence premise at this call
    assert(h == h + cnt_eq_codes_between(input, 0, 0, mg)) by {
        assert(cnt_eq_codes_between(input, 0, 0, mg) == 0) by {
            reveal_with_fuel(cnt_eq_codes_between, 1);
        }
    }
    assert(h + cnt_eq_codes_between(input, 0, len_i, mg) <= len_i) by {
        assert(h == cnt_lt_codes(input, len_i, n));
        assert(cnt_eq_codes_between(input, 0, len_i, mg)
            == cnt_eq_codes(input, len_i, mg));
        assert(cnt_lt_codes(input, len_i, mg + 1)
            == cnt_lt_codes(input, len_i, n)
                + cnt_eq_codes(input, len_i, mg));
        lemma_cnt_lt_bound(input, len_i, mg + 1);
    }
    lemma_scan_guarded(input, mg, 0, d_m, bias, h, b, out, h, d_m, -1);
    match enc_scan_model(input, mg, 0, d_m, bias, h, b, out) {
        Option::Some((dend, biasend, hend, outend)) => {
            // the scan guarantees the handled count and the exit delta
            assert(hend == h + cnt_eq_codes_between(input, 0, len_i, mg));
            assert(hend == cnt_lt_codes(input, len_i, mg + 1)) by {
                assert(h == cnt_lt_codes(input, len_i, n));
                assert(cnt_eq_codes_between(input, 0, len_i, mg)
                    == cnt_eq_codes(input, len_i, mg));
            }
            // kill the no-emit exit form with the min witness: the
            // m-position w contradicts no_eq_below
            assert(!(no_eq_below(input, 0, len_i, mg))) by {
                assert(exists |w: int|
                    (0 <= w < len_i && mg == input[w] && mg >= n));
                assert forall |w: int| #![trigger input[w]] 0 <= w < len_i
                    implies (input[w] != mg || !(no_eq_below(input, 0, len_i, mg))) by {
                    if 0 <= w < len_i && no_eq_below(input, 0, len_i, mg) {
                        lemma_no_eq_witness(input, 0, len_i, mg, w);
                    }
                }
            }
            // hence the exit delta takes the since-last-emit value,
            // capped by the full prefix count and by hend
            assert(dend <= cnt_lt_codes(input, len_i, mg)) by {}
            lemma_cnt_lt_bound(input, len_i, mg);
            let d2 = dend + 1;
            assert(d2 <= len_i + 1) by {
                assert(cnt_lt_codes(input, len_i, mg) <= len_i);
            }
            assert(!(d2 > 4294967295)) by {
                assert(len_i <= 3854);
            }
            if hend >= len_i {
                // every position handled: the next outer call returns
                assert(hend == len_i) by {
                    assert(hend == cnt_lt_codes(input, len_i, mg + 1));
                    lemma_cnt_lt_bound(input, len_i, mg + 1);
                }
                assert(enc_outer_model(
                    input, mg + 1, hend, d2, biasend, b, outend)
                    == Option::Some(outend)) by {
                    reveal_with_fuel(enc_outer_model, 1);
                }
            } else {
                // recursive state premises: handled-count
                // correspondence at n' = mg+1, entry delta below
                // handled-count-plus-one
                assert(mg + 1 >= 0x80) by {
                    assert(mg >= n);
                    assert(n >= 0x80);
                }
                lemma_cnt_lt_mono(input, len_i, mg, mg + 1);
                assert(d2 <= hend + 1) by {
                    assert(dend <= cnt_lt_codes(input, len_i, mg));
                    assert(cnt_lt_codes(input, len_i, mg)
                        <= cnt_lt_codes(input, len_i, mg + 1));
                    assert(hend == cnt_lt_codes(input, len_i, mg + 1));
                }
                assert(0 <= hend < len_i);
                assert(d2 <= hend + 1);
                assert(mg + 1 >= 0x80);
                lemma_outer_no_overflow(
                    input, mg + 1, hend, d2, biasend, b, outend);
            }
        }
        Option::None => {
            assert(false) by {}
        }
    }
}

/// Top-level no-overflow statement for the internal encode: under the
/// one-shot product the full anchored model is Some, so the
/// external-caller's checked loop cannot take an error channel and the
/// internal caller's unchecked loop performs the same state updates
/// with the same emitted output.
proof fn lemma_encode_chars_model_no_overflow(input: Seq<char>, anchor: Seq<char>)
    requires
        input.len() <= u32::MAX as usize,
        (input.len() as int + 1) * 1113983 <= 4294967295,
    ensures
        encode_full_model(input, anchor).is_some(),
{
    let cs = codes_of(input);
    lemma_codes_of_len(input);
    assert(cs.len() as int == input.len() as int);
    assert forall |k: int| 0 <= k < cs.len() as int
        implies (0 <= cs[k] && cs[k] <= 0x10FFFF) by {
        lemma_codes_of_index(input, k);
    }
    let b0 = count_basic_codes(cs, 0);
    lemma_count_basics_is_lt(cs);
    assert(b0 == cnt_lt_codes(cs, cs.len() as int, 128));
    let out0 = ascii_prefix_model(cs, 0, codes_of(anchor));
    let out1 = (if b0 > 0 { out0.push(0x2D) } else { out0 });
    assert(encode_full_model(input, anchor)
        == enc_outer_model(cs, 0x80, b0, 0, 72, b0, out1)) by {
        reveal(encode_full_model);
    }
    if b0 >= cs.len() as int {
        assert(b0 == cs.len() as int) by {
            lemma_cnt_lt_bound(cs, cs.len() as int, 128);
        }
        assert(enc_outer_model(cs, 0x80, b0, 0, 72, b0, out1)
            == Option::Some(out1)) by {
            reveal_with_fuel(enc_outer_model, 1);
        }
    } else {
        assert(0 <= b0 < cs.len() as int) by {
            lemma_cnt_lt_bound(cs, cs.len() as int, 128);
        }
        assert(b0 == cnt_lt_codes(cs, cs.len() as int, 128));
        assert((cs.len() as int + 1) * 1113983 <= 4294967295) by {}
        assert(forall |k: int| #![trigger cs[k]] 0 <= k < cs.len() as int
            ==> (0 <= cs[k] && cs[k] <= 0x10FFFF));
        lemma_outer_no_overflow(cs, 128, b0, 0, 72, b0, out1);
    }
}

} // verus!

fn main() {}
