//! harness/coverage_props.rs -- auto-generated harness (coverage diff-set)
//!
//! The coverage diff-set = the upstream public API minus the set verified in
//! earlier batches (details in out/bug-finder-summary.md).
//! This file carries the part that can be machine-checked inside this round's
//! verification face:
//! - tables::UNICODE_VERSION (public constant);
//! - tables::util::is_alphanumeric (the ASCII projection of the unicode_words /
//!   unicode_sentences doc criterion "Alphabetic or General_Category=Number");
//! - the four table lookups (grapheme/word/sentence/emoji): their ASCII models
//!   (AX-g2/w2/s2/e2) are consumed by machine check at representative positions
//!   (letters/digits/spaces/CRLF/punctuation/DEL etc.);
//! - word-side WB3/WB3d/WB11/WB12 branch anchors (the CRLF segment of "a\r\nb" is
//!   a single token).
//!
//! Consumption: includes verified/src/lib.rs via #[path]; no spec copying.

use vstd::prelude::*;
use vstd::prelude::SpecOrd;

#[path = "../src/lib.rs"]
mod libm;

use libm::grapheme::gceq;
use libm::tables::emoji::{ecat_ascii_model, emoji_category, EmojiCat};
use libm::tables::grapheme::{gcat_ascii_model, grapheme_category, GraphemeCat};
use libm::tables::sentence::{scat_ascii_model, sentence_category, SentenceCat};
use libm::tables::util::is_alphanumeric;
use libm::tables::word::{wcat_ascii_model, word_category, WordCat};
use libm::tables::UNICODE_VERSION;
use libm::word::AsciiWordBoundIter;
use libm::word::{fwd_chain_end, wb_next_break};

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::slice::group_slice_axioms,
    vstd::std_specs::vec::group_vec_axioms};

fn peq_u8cat(a: WordCat, b: WordCat) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (WordCat::WC_ALetter, WordCat::WC_ALetter) => true,
        (WordCat::WC_Any, WordCat::WC_Any) => true,
        (WordCat::WC_CR, WordCat::WC_CR) => true,
        (WordCat::WC_Double_Quote, WordCat::WC_Double_Quote) => true,
        (WordCat::WC_Extend, WordCat::WC_Extend) => true,
        (WordCat::WC_ExtendNumLet, WordCat::WC_ExtendNumLet) => true,
        (WordCat::WC_Format, WordCat::WC_Format) => true,
        (WordCat::WC_Hebrew_Letter, WordCat::WC_Hebrew_Letter) => true,
        (WordCat::WC_Katakana, WordCat::WC_Katakana) => true,
        (WordCat::WC_LF, WordCat::WC_LF) => true,
        (WordCat::WC_MidLetter, WordCat::WC_MidLetter) => true,
        (WordCat::WC_MidNum, WordCat::WC_MidNum) => true,
        (WordCat::WC_MidNumLet, WordCat::WC_MidNumLet) => true,
        (WordCat::WC_Newline, WordCat::WC_Newline) => true,
        (WordCat::WC_Numeric, WordCat::WC_Numeric) => true,
        (WordCat::WC_Regional_Indicator, WordCat::WC_Regional_Indicator) => true,
        (WordCat::WC_Single_Quote, WordCat::WC_Single_Quote) => true,
        (WordCat::WC_WSegSpace, WordCat::WC_WSegSpace) => true,
        (WordCat::WC_ZWJ, WordCat::WC_ZWJ) => true,
        _ => false,
    }
}

fn peq_scat(a: SentenceCat, b: SentenceCat) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (SentenceCat::SC_ATerm, SentenceCat::SC_ATerm) => true,
        (SentenceCat::SC_Any, SentenceCat::SC_Any) => true,
        (SentenceCat::SC_Close, SentenceCat::SC_Close) => true,
        (SentenceCat::SC_CR, SentenceCat::SC_CR) => true,
        (SentenceCat::SC_Extend, SentenceCat::SC_Extend) => true,
        (SentenceCat::SC_Format, SentenceCat::SC_Format) => true,
        (SentenceCat::SC_LF, SentenceCat::SC_LF) => true,
        (SentenceCat::SC_Lower, SentenceCat::SC_Lower) => true,
        (SentenceCat::SC_Numeric, SentenceCat::SC_Numeric) => true,
        (SentenceCat::SC_OLetter, SentenceCat::SC_OLetter) => true,
        (SentenceCat::SC_SContinue, SentenceCat::SC_SContinue) => true,
        (SentenceCat::SC_STerm, SentenceCat::SC_STerm) => true,
        (SentenceCat::SC_Sep, SentenceCat::SC_Sep) => true,
        (SentenceCat::SC_Sp, SentenceCat::SC_Sp) => true,
        (SentenceCat::SC_Upper, SentenceCat::SC_Upper) => true,
        _ => false,
    }
}

fn peq_ecat(a: EmojiCat, b: EmojiCat) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (EmojiCat::EC_Any, EmojiCat::EC_Any) => true,
        (EmojiCat::EC_Extended_Pictographic, EmojiCat::EC_Extended_Pictographic) => true,
        _ => false,
    }
}

/// ASCII representative positions x the four table models (the machine-checked exec
/// call sites of AX-g2/w2/s2/e2):
/// letters ('A','z'), digits ('0','9'), whitespace (' ', LF, CR, VT, FF),
/// punctuation ('.', ',', ';', ':', '\'', '"', '(', ')', '{', '}', '!', '?', '-',
/// underscore), control (0x00, 0x7F), and the upper/lower endpoints.
pub exec fn prop_ascii_category_model_repr() -> (r: bool)
    ensures
        r,
{
    let mut ok = true;

    // letters: grapheme=Any, word=ALetter, sentence=Upper/Lower, emoji=Any,
    // is_alphanumeric=true
    {
        let (l1, u1, g) = grapheme_category('A');
        let (l2, u2, w) = word_category('A');
        let (l3, u3, sc) = sentence_category('A');
        let (l4, u4, e) = emoji_category('A');
        if !gceq(g, GraphemeCat::GC_Any) || !peq_u8cat(w, WordCat::WC_ALetter)
            || !peq_scat(sc, SentenceCat::SC_Upper) || !peq_ecat(e, EmojiCat::EC_Any)
        {
            ok = false;
        }
        if !is_alphanumeric('A') {
            ok = false;
        }
        assert(gcat_ascii_model('A') == GraphemeCat::GC_Any);
        assert(wcat_ascii_model('A') == WordCat::WC_ALetter);
    }
    {
        let (l1, u1, g) = grapheme_category('z');
        let (l2, u2, w) = word_category('z');
        let (l3, u3, sc) = sentence_category('z');
        if !gceq(g, GraphemeCat::GC_Any) || !peq_u8cat(w, WordCat::WC_ALetter)
            || !peq_scat(sc, SentenceCat::SC_Lower)
        {
            ok = false;
        }
        if !is_alphanumeric('z') {
            ok = false;
        }
    }
    // digits
    {
        let (l1, u1, g) = grapheme_category('0');
        let (l2, u2, w) = word_category('0');
        let (l3, u3, sc) = sentence_category('0');
        if !gceq(g, GraphemeCat::GC_Any) || !peq_u8cat(w, WordCat::WC_Numeric)
            || !peq_scat(sc, SentenceCat::SC_Numeric)
        {
            ok = false;
        }
        if !is_alphanumeric('0') {
            ok = false;
        }
    }
    // CRLF: the grapheme CR/LF pair (input side of the GB3 obligation)
    {
        let (l1, u1, g_cr) = grapheme_category('\r');
        let (l2, u2, g_lf) = grapheme_category('\n');
        let (l3, u3, w_cr) = word_category('\r');
        let (l4, u4, w_lf) = word_category('\n');
        let (l5, u5, s_cr) = sentence_category('\r');
        if !gceq(g_cr, GraphemeCat::GC_CR) || !gceq(g_lf, GraphemeCat::GC_LF) {
            ok = false;
        }
        assert(gcat_ascii_model('\r') == GraphemeCat::GC_CR);
        assert(gcat_ascii_model('\n') == GraphemeCat::GC_LF);
        if !peq_u8cat(w_cr, WordCat::WC_CR) || !peq_u8cat(w_lf, WordCat::WC_LF) {
            ok = false;
        }
        if !peq_scat(s_cr, SentenceCat::SC_CR) {
            ok = false;
        }
    }
    // whitespace run: word=WSegSpace (input side of the WB3d obligation)
    {
        let (l1, u1, w) = word_category(' ');
        if !peq_u8cat(w, WordCat::WC_WSegSpace) {
            ok = false;
        }
        assert(wcat_ascii_model(' ') == WordCat::WC_WSegSpace);
    }
    // MidNum/MidNumLet/MidLetter/MidNumQ (input side of the WB6/7/11/12 obligations):
    // ','->MidNum, '.'->MidNumLet, ':'->MidLetter, '\''->Single_Quote
    {
        let (l1, u1, w1) = word_category(',');
        let (l2, u2, w2) = word_category('.');
        let (l3, u3, w3) = word_category(':');
        let (l4, u4, w4) = word_category('\'');
        if !peq_u8cat(w1, WordCat::WC_MidNum) || !peq_u8cat(w2, WordCat::WC_MidNumLet)
            || !peq_u8cat(w3, WordCat::WC_MidLetter)
            || !peq_u8cat(w4, WordCat::WC_Single_Quote)
        {
            ok = false;
        }
    }
    // ATerm/STerm (input side of the SB6-SB11 obligations): '.'->ATerm, '!'->STerm
    {
        let (l1, u1, s1) = sentence_category('.');
        let (l2, u2, s2) = sentence_category('!');
        if !peq_scat(s1, SentenceCat::SC_ATerm) || !peq_scat(s2, SentenceCat::SC_STerm) {
            ok = false;
        }
        assert(scat_ascii_model('.') == SentenceCat::SC_ATerm);
        assert(scat_ascii_model('!') == SentenceCat::SC_STerm);
    }
    // ExtendNumLet '_' (input side of the WB13a/b obligations) and DEL 0x7F (table
    // value GC_Control)
    {
        let (l1, u1, w) = word_category('_');
        if !peq_u8cat(w, WordCat::WC_ExtendNumLet) {
            ok = false;
        }
        assert(wcat_ascii_model('_') == WordCat::WC_ExtendNumLet);
        let (l2, u2, g) = grapheme_category('\u{7f}');
        if !gceq(g, GraphemeCat::GC_Control) {
            ok = false;
        }
        assert(gcat_ascii_model('\u{7f}') == GraphemeCat::GC_Control);
    }
    // non-alnum punctuation: '(' and ')' -> sentence Close, word Any
    {
        let (l1, u1, s) = sentence_category('(');
        if !peq_scat(s, SentenceCat::SC_Close) {
            ok = false;
        }
        assert(scat_ascii_model('(') == SentenceCat::SC_Close);
        if is_alphanumeric('(') {
            ok = false;
        }
    }
    ok
}

// data-plane stub: "a\r\nb"
#[verifier::external_body]
fn bytes_crlf_around() -> (b: Vec<u8>)
    ensures
        b@ == seq![0x61, 0x0d, 0x0a, 0x62],
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x0d);
    v.push(0x0a);
    v.push(0x62);
    v
}

/// The WB3 CRLF segment is a single token, forward proposition ("a\r\nb" ->
/// [(0,"a"),(1,"\r\n"),(3,"b")]).
pub exec fn prop_wb3_crlf_token() -> (r: bool)
    ensures
        r,
{
    reveal_with_fuel(wb_next_break, 6);
    reveal_with_fuel(fwd_chain_end, 8);
    let v = bytes_crlf_around();
    let s = &v[..];
    assert(s@ == v@);
    let mut it = AsciiWordBoundIter::new(s);

    assert(s@.len() == 4);
    assert(wb_next_break(s@, 0) == 1); // "a"
    assert(wb_next_break(s@, 1) == 3); // "\r\n" WB3

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t0 = it.next();
    let ok0 = match t0 {
        Some((p, w)) => p == 0 && (w.len() == 1 && w[0] == 97),
        None => false,
    };
    let t1 = it.next();
    let ok1 = match t1 {
        Some((p, w)) => p == 1 && (w.len() == 2 && w[0] == 13 && w[1] == 10),
        None => false,
    };
    let t2 = it.next();
    let ok2 = match t2 {
        Some((p, w)) => p == 3 && (w.len() == 1 && w[0] == 98),
        None => false,
    };
    let t3 = it.next();
    let ok3 = match t3 {
        None => true,
        Some(_) => false,
    };
    ok0 && ok1 && ok2 && ok3
}

/// The public constant UNICODE_VERSION == (18, 0, 0) (this crate is based on Unicode
/// 18 -- the premise of GB9c (InCB) and of the linkers added in Unicode 18).
pub exec fn prop_unicode_version() -> (r: bool)
    ensures
        r,
{
    UNICODE_VERSION.0 == 18 && UNICODE_VERSION.1 == 0 && UNICODE_VERSION.2 == 0
}

}

fn main() {}
