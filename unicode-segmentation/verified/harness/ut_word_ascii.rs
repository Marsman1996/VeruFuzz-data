//! harness/ut_word_ascii.rs -- witnesses of the transcribable face of the word.rs inline UTs
//!
//! Covers the ASCII fast-path obligations of the inventory (4 word.rs UTs + 2
//! proptests):
//! - W3 test_ascii_word_bound_indices_various_cases (word.rs:1068-1079): the 5-token
//!   segment sequence of "Hello, world!", aligned token by token with the upstream
//!   expectation via the verified AsciiWordBoundIter::next (positions + byte
//!   contents).
//! - W3 rev (the rev assertion of the upstream proptest): next_back aligned call by
//!   call with wb_prev_break, the token sequence exactly the reverse of the forward
//!   one, offset globally consistent.
//! - W4 test_ascii_word_indices_various_cases (word.rs:1082-1098), its anchor segment:
//!   "a'b 1,2" (WB7a quote joining letters + WB11 comma joining digits + WB3d
//!   whitespace).
//!
//! The input data constructors (bytes_*) are **data-plane stubs** (external_body;
//! their ensures are factual statements of the literal data); the obligations
//! themselves live in the witness theorems and the src mirror.
//! Consumption: includes verified/src/lib.rs via #[path]; no spec copying.

use vstd::prelude::*;
use vstd::prelude::SpecOrd;

#[path = "../src/lib.rs"]
mod libm;

use libm::word::AsciiWordBoundIter;
use libm::word::{back_chain_start, fwd_chain_end, wb_next_break, wb_prev_break};

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::slice::group_slice_axioms,
    vstd::std_specs::vec::group_vec_axioms};

// data-plane stub: its ensures are the factual statement of the literal data
// "Hello, world!".
#[verifier::external_body]
fn bytes_hello_world() -> (b: Vec<u8>)
    ensures
        b@ == seq![
            0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21,
        ],
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x48);
    v.push(0x65);
    v.push(0x6c);
    v.push(0x6c);
    v.push(0x6f);
    v.push(0x2c);
    v.push(0x20);
    v.push(0x77);
    v.push(0x6f);
    v.push(0x72);
    v.push(0x6c);
    v.push(0x64);
    v.push(0x21);
    v
}

// data-plane stub: "a'b 1,2"
#[verifier::external_body]
fn bytes_infix_cases() -> (b: Vec<u8>)
    ensures
        b@ == seq![0x61, 0x27, 0x62, 0x20, 0x31, 0x2c, 0x32],
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x27);
    v.push(0x62);
    v.push(0x20);
    v.push(0x31);
    v.push(0x2c);
    v.push(0x32);
    v
}

/// W3 witness: the forward segment sequence of "Hello, world!" ==
/// [(0,"Hello"),(5,","),(6," "),(7,"world"),(12,"!")] then exhausted.
pub exec fn witness_hello_world_forward() -> (r: bool)
    ensures
        r,
{
    reveal_with_fuel(wb_next_break, 6);
    reveal_with_fuel(fwd_chain_end, 8);
    let v = bytes_hello_world();
    let s = &v[..];
    assert(s@ == v@);
    let mut it = AsciiWordBoundIter::new(s);

    assert(s@.len() == 13);
    // model values first (steps for the solver):
    assert(wb_next_break(s@, 0) == 5); // "Hello"
    assert(wb_next_break(s@, 5) == 6); // ","
    assert(wb_next_break(s@, 6) == 7); // " "
    assert(wb_next_break(s@, 7) == 12); // "world"

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t0 = it.next();
    let ok0 = match t0 {
        Some((p, w)) => p == 0 && (w.len() == 5 && w[0] == 72 && w[1] == 101
            && w[2] == 108 && w[3] == 108 && w[4] == 111),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t1 = it.next();
    let ok1 = match t1 {
        Some((p, w)) => p == 5 && (w.len() == 1 && w[0] == 44),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t2 = it.next();
    let ok2 = match t2 {
        Some((p, w)) => p == 6 && (w.len() == 1 && w[0] == 32),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t3 = it.next();
    let ok3 = match t3 {
        Some((p, w)) => p == 7 && (w.len() == 5 && w[0] == 119 && w[1] == 111
            && w[2] == 114 && w[3] == 108 && w[4] == 100),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t4 = it.next();
    let ok4 = match t4 {
        Some((p, w)) => p == 12 && (w.len() == 1 && w[0] == 33),
        None => false,
    };

    let t5 = it.next();
    let ok5 = match t5 {
        None => true,
        Some(_) => false,
    };
    ok0 && ok1 && ok2 && ok3 && ok4 && ok5
}

/// W3 rev witness: the backward segment sequence of "Hello, world!" ==
/// [(12,"!"),(7,"world"),(6," "),(5,","),(0,"Hello")] then exhausted, positions
/// same as forward (offset globally consistent).
pub exec fn witness_hello_world_backward() -> (r: bool)
    ensures
        r,
{
    reveal_with_fuel(wb_prev_break, 6);
    reveal_with_fuel(back_chain_start, 8);
    let v = bytes_hello_world();
    let s = &v[..];
    assert(s@ == v@);
    let mut it = AsciiWordBoundIter::new(s);

    assert(s@.len() == 13);
    // model values first:
    assert(wb_prev_break(s@, 13) == 12); // "!"
    assert(wb_prev_break(s@, 12) == 7); // "world"
    assert(wb_prev_break(s@, 7) == 6); // " "
    assert(wb_prev_break(s@, 6) == 5); // ","
    assert(wb_prev_break(s@, 5) == 0); // "Hello"

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t4 = it.next_back();
    let ok4 = match t4 {
        Some((p, w)) => p == 12 && (w.len() == 1 && w[0] == 33),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t3 = it.next_back();
    let ok3 = match t3 {
        Some((p, w)) => p == 7 && (w.len() == 5 && w[0] == 119 && w[1] == 111
            && w[2] == 114 && w[3] == 108 && w[4] == 100),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t2 = it.next_back();
    let ok2 = match t2 {
        Some((p, w)) => p == 6 && (w.len() == 1 && w[0] == 32),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t1 = it.next_back();
    let ok1 = match t1 {
        Some((p, w)) => p == 5 && (w.len() == 1 && w[0] == 44),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t0 = it.next_back();
    let ok0 = match t0 {
        Some((p, w)) => p == 0 && (w.len() == 5 && w[0] == 72 && w[1] == 101
            && w[2] == 108 && w[3] == 108 && w[4] == 111),
        None => false,
    };

    let t5 = it.next_back();
    let ok5 = match t5 {
        None => true,
        Some(_) => false,
    };
    ok4 && ok3 && ok2 && ok1 && ok0 && ok5
}

/// W4 witness: infix joining (WB7a quote joining letters, WB11 comma joining
/// digits, WB3d whitespace):
/// "a'b 1,2" -> [(0,"a'b"),(3," "),(4,"1,2")] then exhausted.
pub exec fn witness_infix_cases() -> (r: bool)
    ensures
        r,
{
    reveal_with_fuel(wb_next_break, 6);
    reveal_with_fuel(fwd_chain_end, 8);
    let v = bytes_infix_cases();
    let s = &v[..];
    assert(s@ == v@);
    let mut it = AsciiWordBoundIter::new(s);

    assert(s@.len() == 7);
    // model values first:
    assert(wb_next_break(s@, 0) == 3); // "a'b"
    assert(wb_next_break(s@, 3) == 4); // " "
    assert(wb_next_break(s@, 4) == 7); // "1,2"

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t0 = it.next();
    let ok0 = match t0 {
        Some((p, w)) => p == 0 && (w.len() == 3 && w[0] == 97 && w[1] == 39 && w[2] == 98),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t1 = it.next();
    let ok1 = match t1 {
        Some((p, w)) => p == 3 && (w.len() == 1 && w[0] == 32),
        None => false,
    };

    assert(it.offset + (it.rest@.len() as usize) <= usize::MAX);
    let t2 = it.next();
    let ok2 = match t2 {
        Some((p, w)) => p == 4 && (w.len() == 3 && w[0] == 49 && w[1] == 44 && w[2] == 50),
        None => false,
    };

    let t3 = it.next();
    let ok3 = match t3 {
        None => true,
        Some(_) => false,
    };
    ok0 && ok1 && ok2 && ok3
}

}

fn main() {}
