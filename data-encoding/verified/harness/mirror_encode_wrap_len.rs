//! harness: spec-mirror of the wrap length machinery (BASE64
//! monomorphization: bit = 6, enc(6) = 3, dec(6) = 4, pad arm), plus the
//! doc-face witness for the wrap-extension doc sentence.
//!
//! Small practical face: the mirror samples `ilen <= 1024` with
//! `8 <= col <= 1024` (the doc's own wrap face, width 8 separator " ")
//! -- no usize-shuffle bound reasoning is mixed in here; the
//! full-domain wrap postcondition is already covered by verified/src's
//! `encode_wrap_len` (0 expected error).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs and
//! transcriptions are never duplicated here.
//!
//! Faces and their roles:
//!   - `pre_ok` mirrors the requires-domain predicate (the runtime
//!     differential driver samples only inside it);
//!   - `mirror_encode_wrap_len` mirrors the upstream length math as an
//!     exec transcription tied to the src spec (`encode_wrap_len_spec`);
//!     the MIRROR-marked span is the plain-Rust token source for the
//!     runtime differential driver (proof blocks are stripped by the
//!     extraction script, so the extracted form is plain rustc code);
//!   - `doc_ends_with_separator_face` mirrors the doc sentence's length
//!     face `r >= end_len`;
//!   - `doc_anchor_empty_input` is the witness face: at `ilen == 0` the
//!     doc sentence is false on the face (the empty output is 0 long,
//!     shorter than the separator);
//!   - `doc_control_nonempty_input` proves the sentence's face holds on
//!     every nonempty input -- the domain where the doc wording is true.
//!
//! The doc sentence under test (code/lib/src/lib.rs:1185, section
//! "Extensions / Wrap output when encoding"): "Note that the output
//! always ends with the separator." -- unconditionally, hence also for
//! empty input; the witness face shows that is false on the face.
//! Runtime ground truth: upstream's own test suite pins
//! `encode(b"") == ""` (no separator appended).

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod data_encoding;

use data_encoding::{
    dec_of_bit_spec, div_ceil_spec, enc_of_bit_spec, encode_pad_len_spec,
    encode_wrap_len_spec,
};

verus! {

/* ---------- BASE64-mono precondition domain (the sampling domain) ---------- */

pub open spec fn spec_pre_mono(ilen: int, col: int, end_len: int) -> bool {
    0 <= ilen && ilen <= 1024
        && 8 <= col && col <= 1024
        && 1 <= end_len && end_len <= 8
}

/// Spec-level pack of the doc sentence's length face (the wrapped
/// output is at least as long as the nonempty separator). Exec faces
/// mirror it; the control/witness faces reference this pack directly.
pub open spec fn doc_face_spec(ilen: int, col: int, end_len: int) -> bool {
    encode_wrap_len_spec(6int, true, ilen, col, end_len) >= end_len
}

/// Precondition mirror: mirrors the requires-domain predicate so the
/// runtime differential driver can sample honestly (out-of-domain
/// inputs never fed). The ensures ties the runtime-side domain test
/// back to the spec face.
pub exec fn pre_ok(ilen: usize, col: usize, end_len: usize) -> (b: bool)
    ensures
        b == spec_pre_mono(ilen as int, col as int, end_len as int),
{
    /* MIRROR-BEGIN (pre_ok: common-syntax, extracted verbatim) */
    ilen <= 1024usize
        && 8 <= col && col <= 1024usize
        && 1 <= end_len && end_len <= 8usize
    /* MIRROR-END */
}

/* ---------- ceil facts (mono-domain only; shared by both faces) ---------- */

proof fn div_ceil_ge1(x: int, m: int)
    requires
        1 <= x,
        1 <= m,
    ensures
        (x + m - 1) / m >= 1,
{
    let y: int = x + m - 1;
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(y, m);
    assert(0 <= y / m);
    if y / m == 0 {
        vstd::arithmetic::div_mod::lemma_small_div_converse(y, m);
        assert(y < m);
        assert(x + m - 1 < m);
        assert(x < 1);
        assert(false);
    }
    assert(y / m >= 1);
}

proof fn div_ceil_le(x: int, m: int)
    requires
        0 <= x,
        1 <= m,
    ensures
        (x + m - 1) / m <= x / m + 1,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x + m - 1int, x + m, m);
    vstd::arithmetic::div_mod::lemma_div_plus_one(x, m);
}

/* ---------- functional-output mirror ---------- */

/// Functional-output mirror of the wrap length math on the BASE64 face
/// (`encode_wrap_len`, wrap-present arm: olen + end_len * ceil(olen,
/// col) with the pad arm olen = ceil(ilen, 3) * 4). The small domain
/// keeps every arithmetic step inside usize (olen <= 1028, products
/// bounded, no overflow face).
pub exec fn mirror_encode_wrap_len(ilen: usize, col: usize, end_len: usize) -> (r: usize)
    requires
        spec_pre_mono(ilen as int, col as int, end_len as int),
    ensures
        (r as int) == encode_wrap_len_spec(6int, true, ilen as int, col as int, end_len as int),
{
    /* MIRROR-BEGIN (mirror_encode_wrap_len: common-syntax; the runtime
       differential driver reuses this span verbatim after stripping
       proof blocks) */
    let olen: usize = (ilen + 2usize) / 3usize * 4usize;
    proof {
        /* olen == ceil(ilen, 3) * 4 == encode_pad_len_spec(6, true, ilen) */
        assert(olen as int == (ilen as int + 2) / 3 * 4);
        assert((ilen as int + 2) / 3 == (ilen as int + 3 - 1) / 3);
        assert(enc_of_bit_spec(6int) == 3int);
        assert(dec_of_bit_spec(6int) == 4int);
        /* overflow faces for the wrap arm below (small domain keeps
           everything linear): olen <= 4 * ilen + 4, so olen + col - 1
           fits and the separator product is below 8 * (olen + 1) */
        assert((ilen as int + 2) / 3 <= ilen as int + 1);
        assert(olen as int <= 4 * (ilen as int) + 4);
        assert(olen as int + col as int - 1 >= 0);
        assert(olen as int + col as int - 1 <= usize::MAX as int);
        div_ceil_le(olen as int, col as int);
        assert(olen as int / col as int <= olen as int);
        assert(div_ceil_spec(olen as int, col as int) == (olen as int + col as int - 1) / col as int);
        assert(div_ceil_spec(olen as int, col as int) <= olen as int + 1);
        vstd::arithmetic::mul::lemma_mul_inequality(
            div_ceil_spec(olen as int, col as int), olen as int + 1, end_len as int);
        vstd::arithmetic::mul::lemma_mul_inequality(end_len as int, 8int, olen as int + 1);
        assert(end_len as int * div_ceil_spec(olen as int, col as int)
            <= 8int * (olen as int + 1));
        assert(olen as int <= 4int * 1024int + 4int);
        assert(4int * 1024int + 4int + 8int * (4int * 1024int + 5int) <= usize::MAX as int);
        assert(olen as int + end_len as int * div_ceil_spec(olen as int, col as int)
            <= usize::MAX as int);
    }
    let r: usize = olen + end_len * ((olen + col - 1usize) / col);
    r
    /* MIRROR-END */
}

/* ---------- doc-face mirror + witness ---------- */

/// Mirror of the doc sentence's length face: "the output always ends
/// with the separator" needs the wrapped output to carry the (nonempty)
/// separator, i.e. the wrapped length r >= end_len. The mirror
/// evaluates the face formula on the spec-side value delivered by the
/// machine-checked mirror above.
pub exec fn doc_ends_with_separator_face(ilen: usize, col: usize, end_len: usize) -> (b: bool)
    requires
        spec_pre_mono(ilen as int, col as int, end_len as int),
    ensures
        b == doc_face_spec(ilen as int, col as int, end_len as int),
{
    let r = mirror_encode_wrap_len(ilen, col, end_len);
    r >= end_len
}

/// [FINDING ANCHOR] The empty-input witness: doc promises the wrapped
/// output always ends with the separator; at `ilen == 0` the face says
/// it does not (wrapped output is 0 long, below the separator length).
/// Runtime ground truth: upstream's own test suite pins `encode(b"") ==
/// ""` (no separator appended). Runtime differential driver: out/
/// verus-bugfinder/spec-mirror/encode-wrap-len/.
pub exec fn doc_anchor_empty_input(end_len: usize) -> (b: bool)
    requires
        0 < end_len && end_len <= 8,
    ensures
        !b,
{
    let s = mirror_encode_wrap_len(0usize, 8usize, end_len);
    proof {
        /* witness eval: empty input gives a zero-length wrapped output
           (pad arm 0; the separator term contributes ceil(0, col) == 0) */
        assert(s == 0usize);
        assert(end_len >= 1usize);
        assert(doc_face_spec(0int, 8int, end_len as int) == false);
    }
    s >= end_len
}

/// Control twin: the doc sentence holds on every nonempty input -- the
/// domain where the doc wording is true (and what the suggested doc fix
/// carves out).
pub exec fn doc_control_nonempty_input(ilen: usize, col: usize, end_len: usize) -> (b: bool)
    requires
        0 < ilen && ilen <= 1024
            && 8 <= col && col <= 1024
            && 1 <= end_len && end_len <= 8,
    ensures
        doc_face_spec(ilen as int, col as int, end_len as int),
{
    let r = mirror_encode_wrap_len(ilen, col, end_len);
    proof {
        let olen = div_ceil_spec(ilen as int, 3int) * 4;
        /* olen >= 4: the pad arm is ceil(ilen, 3) * 4 with ceil >= 1 */
        assert(olen >= 4int) by {
            div_ceil_ge1(ilen as int, 3int);
        }
        /* ceil(olen, col) >= 1, so the separator contributes end_len or
           more, pushing the face past end_len */
        assert(r as int >= olen + end_len as int) by {
            div_ceil_ge1(olen, col as int);
            vstd::arithmetic::mul::lemma_mul_inequality(
                1int, div_ceil_spec(olen, col as int), end_len as int);
            assert(end_len as int * div_ceil_spec(olen, col as int) >= end_len as int);
        }
        assert(r as int >= end_len as int);
    }
    r >= end_len
}

}

fn main() {}
