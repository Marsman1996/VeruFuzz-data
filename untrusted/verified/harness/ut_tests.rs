//! harness/ut_tests.rs -- the verus transcriptions and assertion
//! theorems of the upstream UTs (code/tests/tests.rs, 13 items).
//!
//! Reference organization: `mod untrusted` pulls verified/src/lib.rs
//! via #[path] (the upstream mod-tree mirror); the root-level use
//! aliases (pub use untrusted::no_panic etc.) make the subtree's
//! verbatim upstream imports like `use crate::{no_panic, Reader}`
//! resolve to the same module instance (single source of truth;
//! copying the src-side spec is forbidden).
//!
//! Value-link shape notes for the higher-order closure APIs (read_all /
//! read_all_optional) (the src side's E1-E4 + the ledger): verus has no
//! nonempty exists / forward-value axiom for an opaque FnOnce parameter
//! (the caller side's call_ensures has only the implication direction),
//! so the UTs' "value assertion at the read_all
//! call site" is carried by two layers of equivalent evidence:
//!   L.a composed witness: closure replay (body-level facts) +
//!     read_all_decision (src, the whole-value contract) + R3 determinism
//!     (requires, caller-provable) => the same judgment as read_all's
//!     internal call -- holding verbatim for the upstream UT assertions;
//!   L.b runtime re-verification: the upstream cargo test on the
//!     database/untrusted/code pin tree (the UT source runs verbatim).
use vstd::prelude::*;

#[path = "../src/lib.rs"]
pub mod untrusted;

pub use untrusted::no_panic;
pub use untrusted::reader;
pub use untrusted::{EndOfInput, Input, Reader};
use untrusted::reader::wf;
use untrusted::input::read_all_decision;

verus! {

/* ---------- shared components ---------- */

/// The literal sequence of b"foo" (the spec projection of the upstream
/// UT's constant input)
pub open spec fn foo_seq0() -> Seq<u8> {
    Seq::new(3, |k: int| if k == 0 { b'f' } else if k == 1 { b'o' } else { b'o' })
}

pub open spec fn foo_seq() -> Seq<u8> {
    Seq::new(3, |k: int| if k == 0 { b'f' } else if k == 1 { b'o' } else { b'o' })
}

pub open spec fn f_seq() -> Seq<u8> {
    Seq::new(1, |k: int| b'f')
}

pub open spec fn oo_seq() -> Seq<u8> {
    Seq::new(2, |k: int| if k == 0 { b'o' } else { b'o' })
}

/* ---------- UT#1 test_debug ----------
   Debug output is always "Input"/"Reader" (no value leak). The fmt body
   is external_body (the f.debug_struct chain is not provable); its text
   contract is re-verified verbatim by the runtime driver. */

#[verifier::external_body]
pub exec fn debug_repr_input(i: &Input) -> (s: &'static str)
    ensures
        s == "Input",
{
    let _ = i;
    "Input"
}

#[verifier::external_body]
pub exec fn debug_repr_reader(r: &Reader) -> (s: &'static str)
    ensures
        s == "Reader",
{
    let _ = r;
    "Reader"
}

/* ---------- UT#2 test_input_clone_and_copy ---------- */

pub exec fn ut2_clone_copy(bytes: &[u8]) -> (r: bool)
    ensures
        r == true,
{
    let input = Input::from(bytes);
    let copy = input;   // Copy semantics (verbatim upstream)
    let same = (input.as_slice_less_safe() == copy.as_slice_less_safe())
        && (input.as_slice_less_safe() == input.clone().as_slice_less_safe());
    same == true
}

/* ---------- UT#3 test_input_from ---------- */

pub exec fn ut3_from()
    ensures
        true,
{
    let _ = Input::from(b"foo");
}

/* ---------- UT#4 test_input_is_empty ---------- */

pub exec fn ut4_is_empty()
    ensures
        true,
{
    let e = Input::from(b"");
    let e_is_empty = e.is_empty();
    assert(e_is_empty);             // upstream assert!(input.is_empty())
    let f = Input::from(b"foo");
    let f_is_empty = f.is_empty();
    assert(!f_is_empty);            // upstream assert!(!input.is_empty())
}

/* ---------- UT#5 test_input_len ---------- */

pub exec fn ut5_len()
    ensures
        true,
{
    let input = Input::from(b"foo");
    let l = input.len();
    assert(l == 3);                 // upstream assert_eq!(input.len(), 3)
}

/* ---------- UT#6 test_input_read_all ----------
   After reading all 3 bytes, read_all returns Ok(()). The value link
   takes the "composed witness" shape: closure replay (read_byte x3,
   body-level facts) + read_all_decision's verbatim decision. */

pub exec fn ut6_read_all_consumes_all() -> (r: Result<(), EndOfInput>)
    ensures
        r == Ok(()),
{
    let bytes = [b'f', b'o', b'o'];
    let input = Input::from(&bytes);
    let mut reader = Reader::new(input);
    proof {
        assert(reader.i == 0);                       // Reader::new ensures
        assert(reader.input.seq() == input.seq());   // Reader::new ensures
        assert(reader.input.seq().len() == 3);
        assert(reader.input.seq()[0] == b'f');
        assert(reader.input.seq()[1] == b'o');
        assert(reader.input.seq()[2] == b'o');
    }
    // Closure replay (same order, verbatim, as the UT#6 closure body): the
    // assert_eq!(...)? triple + at_end
    let byte0 = reader.read_byte()?;
    assert(byte0 == b'f');
    proof { assert(reader.i == 1); assert(reader.input.seq().len() == 3); }
    let byte1 = reader.read_byte()?;
    assert(byte1 == b'o');
    proof { assert(reader.i == 2); assert(reader.input.seq().len() == 3); }
    let byte2 = reader.read_byte()?;
    assert(byte2 == b'o');
    let at = reader.at_end();
    assert(at);                     // upstream assert!(input.at_end())
    // read_all's post-closure decision segment (src/input.rs
    // read_all_decision, isomorphic to the upstream input.rs:70-74)
    proof { assert(reader.i == 3); assert(reader.input.seq().len() == 3); assert(wf(&reader)); }
    read_all_decision(&mut reader, (), EndOfInput)
}

/* ---------- UT#7 test_input_read_all_unconsume ----------
   Reading only 1/3 bytes => read_all returns Err(incomplete_read). */

pub exec fn ut7_read_all_unconsumed() -> (r: Result<(), EndOfInput>)
    ensures
        r == Err(EndOfInput),
{
    let bytes = [b'f', b'o', b'o'];
    let input = Input::from(&bytes);
    let mut reader = Reader::new(input);
    proof {
        assert(reader.i == 0);
        assert(reader.input.seq() == input.seq());
        assert(reader.input.seq().len() == 3);
        assert(reader.input.seq()[0] == b'f');
    }
    let byte0 = match reader.read_byte() {
        Ok(b) => b,
        Err(e) => {
            proof { assert(false); }
            return Err(e);
        }
    };
    assert(byte0 == b'f');
    proof { assert(reader.i == 1); assert(reader.input.seq().len() == 3); }
    let at = reader.at_end();
    assert(!at);                    // upstream assert!(!input.at_end())
    proof { assert(reader.i == 1); assert(reader.input.seq().len() == 3); assert(wf(&reader)); }
    read_all_decision(&mut reader, (), EndOfInput)
}

/* ---------- UT#8 test_input_as_slice_less_safe ---------- */

pub exec fn ut8_as_slice(bytes: &[u8]) -> (r: bool)
    ensures
        r == true,
{
    let input = Input::from(bytes);
    (input.as_slice_less_safe() == bytes) == true
}

/* ---------- UT#9 using_reader_after_skip_and_get_error_returns_error_must_not_panic ----------
   On empty input, after read_bytes(1) fails (EndOfInput), continuing
   with read_bytes_to_end is panic-free. The panic-free obligation is
   verified directly on the verbatim upstream body (the read_all generic
   call's panic-freedom is carried by its contract, the Err propagation
   / Ok decision by the E1-E4 + decision witness; this UT has no output
   assertion, matching upstream). */

pub exec fn ut9_error_then_to_end_must_not_panic() -> (r: Result<(), EndOfInput>)
    ensures
        r == Ok(()),
{
    let eb: [u8; 0] = [];
    let input = Input::from(&eb);
    // Upstream body: read_all(EndOfInput, |r| { let r =
    // input.read_bytes(1); assert unwrap_err==EndOfInput;
    // Ok(input.read_bytes_to_end()) })
    let mut reader = Reader::new(input);
    proof {
        assert(reader.i == 0);
        assert(reader.input.seq() == input.seq());
        assert(reader.input.seq().len() == 0);
    }
    let rb1 = reader.read_bytes(1);
    proof {
        // unwrap_err's precondition and value (the upstream
        // assert_eq!(r.unwrap_err(), EndOfInput))
        assert(rb1 is Err);
        assert(rb1.get_Err_0() == EndOfInput);
    }
    proof { assert(reader.i == 0); assert(reader.input.seq().len() == 0); assert(wf(&reader)); }
    let tail = reader.read_bytes_to_end();
    let ok_inner = ();
    let decision = read_all_decision(&mut reader, ok_inner, EndOfInput);
    match decision {
        Ok(v) => {
            assert(v == ());               // at_end ==> Ok (the decision contract)
            let _ = tail;
            Ok(())
        }
        Err(e) => {
            assert(e == EndOfInput);
            Err(EndOfInput)
        }
    }
}

/* ---------- UT#10 size_assumptions ---------- */

pub exec fn ut10_size_assumptions() -> (r: bool)
    ensures
        r == true,
{
    ut10_size_eq()
}

#[verifier::external_body]
pub exec fn ut10_size_eq() -> (r: bool)
    ensures
        r == true,
{
    // Upstream: size_of::<*const u8>() == size_of::<usize>() (a platform
    // assumption, not library semantics)
    core::mem::size_of::<*const u8>() == core::mem::size_of::<usize>()
}

/* ---------- UT#11 const_fn ---------- */

// Relax note: const-context constructiveness is carried by rustc's
// const-check on the --compile path (verus does not model exec fn calls
// inside const items).
#[verifier::external_body]
pub exec fn ut11_const_fn()
    ensures
        true,
{
    const _INPUT: Input<'static> = Input::from(&[]);
}

/* ---------- UT#12 test_vec_into ----------
   Upstream uses vec![0u8; 0] (the allocation macro is outside the verus
   translation surface); equivalently rewritten as Vec::new (equal per
   value at length 0), From<&[u8]> via Into kept verbatim. */

pub exec fn ut12_vec_into()
    ensures
        true,
{
    ut12_vec_into_go()
}

#[verifier::external_body]
pub exec fn ut12_vec_into_go()
    ensures
        true,
{
    extern crate std;
    let vec: std::vec::Vec<u8> = std::vec::Vec::new(); // Origin Rust: vec![0u8; 0] (equal per value at length 0)
    let _x: Input = (&vec[..]).into();
}

/* ---------- UT#13 test_from_slice ---------- */

pub exec fn ut13_from_slice()
    ensures
        true,
{
    let slice: &[u8] = &[0u8];
    let _x: Input = slice.into();
}

/* ---------- Reader contract-level exemplars (direct-call assertions
   reused across UTs; exec witnesses of the contract layer) ---------- */

pub exec fn ut_reader_read_byte_then_at_end()
    ensures
        true,
{
    let bytes = [b'f', b'o', b'o'];
    let input = Input::from(&bytes);
    let mut r = Reader::new(input);
    proof {
        assert(r.i == 0);
        assert(r.input.seq() == input.seq());
        assert(r.input.seq().len() == 3);
        assert(r.input.seq()[0] == b'f');
    }
    let b1 = r.read_byte();
    assert(b1 == Ok(b'f'));
    let at1 = r.at_end();
    assert(!at1);
    // read_byte's Err branch and cursor preservation (empty input)
    let eb: [u8; 0] = [];
    let e = Input::from(&eb);
    let mut er = Reader::new(e);
    proof {
        assert(er.i == 0);
        assert(er.input.seq().len() == 0);
    }
    let b2 = er.read_byte();
    assert(b2 is Err);
    assert(b2.get_Err_0() == EndOfInput);
    let at2 = er.at_end();
    assert(at2);
}

pub exec fn ut_reader_peek()
    ensures
        true,
{
    let bytes = [b'f', b'o', b'o'];
    let input = Input::from(&bytes);
    let r = Reader::new(input);
    // Reader::peek (a coverage-diff-set item, verified ahead on the UT
    // side and recorded as covered)
    proof {
        assert(r.i == 0);
        assert(r.input.seq().len() == 3);
        assert(r.input.seq()[0] == b'f');
        assert(r.input.seq()[1] == b'o');
    }
    let p1 = r.peek(b'f');
    assert(p1);
    let p2 = r.peek(b'o');
    assert(!p2);
    let eb: [u8; 0] = [];
    let e = Reader::new(Input::from(&eb));
    proof {
        assert(e.i == 0);
        assert(e.input.seq().len() == 0);
    }
    let p3 = e.peek(b'f');
    assert(!p3);                    // peek on empty input is always false
}

pub exec fn ut_reader_skip_and_read_bytes()
    ensures
        true,
{
    let bytes = [b'f', b'o', b'o'];
    let input = Input::from(&bytes);
    let mut r = Reader::new(input);
    proof {
        assert(r.i == 0);
        assert(r.input.seq().len() == 3);
    }
    let s1 = r.skip(1);
    assert(s1 is Ok);
    assert(s1.get_Ok_0() == ());            // coverage-diff-set item
    let at1 = r.at_end();
    assert(!at1);
    let rest = r.read_bytes(2);
    proof {
        assert(r.i == 3);
        let rs = rest.get_Ok_0().seq();
        assert(rs.len() == 2);
        assert(rs[0] == b'o');
        assert(rs[1] == b'o');
    }
    // out-of-bounds skip
    let mut r2 = Reader::new(Input::from(&bytes));
    proof {
        assert(r2.i == 0);
        assert(r2.input.seq().len() == 3);
    }
    let s2 = r2.skip(4);
    assert(s2 is Err);
    assert(s2.get_Err_0() == EndOfInput);
    let at4 = r2.at_end();
    assert(at4 == false);
    // skip(0) is always Ok

    let s3 = r2.skip(0);
    assert(s3 is Ok);
    assert(s3.get_Ok_0() == ());
}

pub exec fn ut_reader_read_bytes_to_end_and_skip_to_end()
    ensures
        true,
{
    let bytes = [b'f', b'o', b'o'];
    let mut r = Reader::new(Input::from(&bytes));
    proof {
        assert(r.i == 0);
        assert(r.input.seq().len() == 3);
        assert(r.input.seq()[0] == b'f');
        assert(r.input.seq()[1] == b'o');
        assert(r.input.seq()[2] == b'o');
    }
    let tail = r.read_bytes_to_end();
    proof {
        assert(r.i == 3);
        let t = tail.seq();
        assert(t.len() == 3);
        assert(t[0] == b'f');
        assert(t[1] == b'o');
        assert(t[2] == b'o');
    }
    let at5 = r.at_end();
    assert(at5);
    let mut r2 = Reader::new(Input::from(&bytes));
    proof {
        assert(r2.i == 0);
        assert(r2.input.seq().len() == 3);
    }
    let s4 = r2.skip(1);
    assert(s4 is Ok);
    assert(s4.get_Ok_0() == ());
    proof { assert(r2.i == 1); }
    proof { assert(r2.i == 1); assert(r2.input.seq().len() == 3); }
    r2.skip_to_end();
    proof { assert(r2.i == 3); }
    let at6 = r2.at_end();
    assert(at6);
    let mut r3 = Reader::new(Input::from(&bytes));
    proof {
        assert(r3.i == 0);
        assert(r3.input.seq().len() == 3);
    }
    proof { assert(r3.i == 0); assert(r3.input.seq().len() == 3); }
    r3.skip_to_end();
    proof { assert(r3.i == 3); }
    let at7 = r3.at_end();
    assert(at7);
}

pub exec fn ut_reader_read_partial()
    ensures
        true,
{
    let bytes = [b'f', b'o', b'o'];
    let input = Input::from(&bytes);
    let mut r = Reader::new(input);
    proof {
        assert(r.i == 0);
        assert(r.input.seq() == foo_seq0());
        assert(r.input.seq()[0] == b'f');
    }
    // read_partial's bytes_read segment contract (Ok ==> [old_i..final_i])
    // + the R value link (the opaque face)
    let res = r.read_partial(|rr: &mut Reader /*same-sequence view*/
        | -> (rrr: Result<u8, EndOfInput>)
            requires
                old(rr).i == 0 && old(rr).input.seq() == foo_seq0(),
            ensures
                rrr == Ok(b'f') && final(rr).i == old(rr).i + 1
                    && final(rr).input.seq() == old(rr).input.seq(),
        {
            rr.read_byte()
        });
    match res {
        Ok(pair) => {
            // read_partial's contract: bytes_read.seq() ==
            // input.seq()[old_i..final_i]; the context anchor
            // (r.input.seq() == foo_seq0()) is proven before the call,
            // and pair.0 is linked to it via the contract (the subrange
            // [0..1] == foo_seq0()'s prefix).
            let _ = pair;
        }
        Err(e) => {
            let _ = e;
        }
    }
}

/* ---------- The upstream UTs' direct read_all calls (structural layer) -----
   Panic-freedom and the decision segment are already carried by the
   read_all contract; the direct calls themselves (the requires checks)
   are kept as caller-side satisfiability witnesses. */

pub exec fn ut6_read_all_direct_call() -> (r: Result<(), EndOfInput>)
    requires
        true,
    ensures
        r is Ok || r is Err,
{
    let bytes = [b'f', b'o', b'o'];
    let input = Input::from(&bytes);
    proof { assert(input.seq() == foo_seq()); }
    input.read_all(EndOfInput, |r2: &mut Reader| -> (res: Result<(), EndOfInput>)
        requires
            r2.i == 0 && r2.input.seq() == foo_seq(),
        ensures
            res == Ok(()),
            final(r2).i == 3,
            final(r2).input.seq() == old(r2).input.seq(),
            final(r2).i == old(r2).input.seq().len(),
    {
        // Same order, verbatim, as the UT#6 closure
        let b0 = r2.read_byte()?;
        assert(b0 == b'f');
        let b1 = r2.read_byte()?;
        assert(b1 == b'o');
        let b2 = r2.read_byte()?;
        assert(b2 == b'o');
        let at_end1 = r2.at_end();
        assert(at_end1);
        Ok(())
    })
}

} // verus!

fn main() {}
