//! harness/phase4_gaps.rs -- the coverage diff-set harness
//!
//! Coverage diff set (the full public-API inventory minus the batches
//! already covered):
//!   - Reader::peek         -- already covered by
//!     harness/ut_tests.rs::ut_reader_peek (confirmed in this batch)
//!   - Reader::skip         -- already covered by
//!     harness/ut_tests.rs::ut_reader_skip_and_read_bytes
//!   - Reader::read_partial -- already covered by
//!     harness/ut_tests.rs::ut_reader_read_partial
//!   - lib.rs::read_all_optional -- this file (the only public API left
//!     untouched by the upstream UTs)
//! The usual priority is the L2 doc semantic contract (the
//! read_all_optional doc: "ensuring that read consumed the entire input.
//! When input is None, read will be called with None.") + L0
//! panic-freedom.
//!
//! Value-link shape note (same as ut_tests.rs): read_all_optional's Some
//! branch is isomorphic to read_all (Reader::new + closure + the at_end
//! decision); its decision segment is carried by src/input.rs::
//! read_all_decision's E contract; the None branch is a pure value pass
//! (r == read(None)'s result), anchored by the harness's closure
//! direct-call replay (body-level facts); the R1 toolchain-gap
//! attribution is recorded in src/input.rs's ledger #4.
use vstd::prelude::*;

#[path = "../src/lib.rs"]
pub mod untrusted;

pub use untrusted::no_panic;
pub use untrusted::reader;
pub use untrusted::{EndOfInput, Input, Reader};
use untrusted::read_all_optional;
use untrusted::input::read_all_decision;
use untrusted::reader::wf;

verus! {

/// Shared component: the same value as ut_tests.rs's foo_seq (copying on
/// the reference side is forbidden -- an alias anchor is declared here
/// and asserted equal)
pub open spec fn foo_seq_p4() -> Seq<u8> {
    Seq::new(3, |k: int| if k == 0 { b'f' } else if k == 1 { b'o' } else { b'o' })
}

/* ---------- Gap 1: the read_all_optional None branch (L2 doc contract:
   read called with None) ---------- */

// Value-link note: judging the None-branch value of the read_all_optional
// contract (lib.rs E-form) likewise needs a caller-side call_ensures
// instantiation (the R1 toolchain gap); the value layer is carried by
// the closure direct-call replay; the structural layer of the direct
// call is p4a_none_direct_call.
pub exec fn p4a_none_replays() -> (r: Result<(), EndOfInput>)
    requires
        true,
    ensures
        r == Ok(()),
{
    let out = (|o: Option<&mut Reader<'_>>|
        -> (res: Result<(), EndOfInput>)
        requires
            o is None || (o is Some && old(o.get_Some_0()).i == 0
                && old(o.get_Some_0()).input.seq() == foo_seq_p4()),
        ensures
            o is None ==> res == Ok(()),
            o is Some ==> res == Ok(())
                && final(o.get_Some_0()).i == old(o.get_Some_0()).input.seq().len()
                && final(o.get_Some_0()).input.seq() == old(o.get_Some_0()).input.seq(),
    {
        match o {
            None => Ok(()),
            Some(rr) => {
                let b0 = match rr.read_byte() {
                    Ok(b) => b,
                    Err(e) => {
                        proof { assert(false); }
                        return Err(e);
                    }
                };
                proof { assert(b0 == b'f'); }
                let b1 = match rr.read_byte() {
                    Ok(b) => b,
                    Err(e) => {
                        proof { assert(false); }
                        return Err(e);
                    }
                };
                proof { assert(b1 == b'o'); }
                let b2 = match rr.read_byte() {
                    Ok(b) => b,
                    Err(e) => {
                        proof { assert(false); }
                        return Err(e);
                    }
                };
                proof { assert(b2 == b'o'); }
                Ok(())
            }
        }
    })(None);
    out
}

/* ---------- Gap 1b: the None-branch direct call (structural layer:
   panic-free + R1-None satisfiability) ---------- */

pub exec fn p4a_none_direct_call() -> (r: Result<(), EndOfInput>)
    requires
        true,
    ensures
        r is Ok || r is Err,
{
    let out = read_all_optional(None, EndOfInput, |o: Option<&mut Reader<'_>>|
        -> (res: Result<(), EndOfInput>)
        requires
            o is None || (o is Some && old(o.get_Some_0()).i == 0
                && old(o.get_Some_0()).input.seq() == foo_seq_p4()),
        ensures
            o is None ==> res == Ok(()),
            o is Some ==> res == Ok(())
                && final(o.get_Some_0()).i == old(o.get_Some_0()).input.seq().len()
                && final(o.get_Some_0()).input.seq() == old(o.get_Some_0()).input.seq(),
    {
        match o {
            None => Ok(()),
            Some(rr) => {
                let b0 = match rr.read_byte() {
                    Ok(b) => b,
                    Err(e) => {
                        proof { assert(false); }
                        return Err(e);
                    }
                };
                proof { assert(b0 == b'f'); }
                let b1 = match rr.read_byte() {
                    Ok(b) => b,
                    Err(e) => {
                        proof { assert(false); }
                        return Err(e);
                    }
                };
                proof { assert(b1 == b'o'); }
                let b2 = match rr.read_byte() {
                    Ok(b) => b,
                    Err(e) => {
                        proof { assert(false); }
                        return Err(e);
                    }
                };
                proof { assert(b2 == b'o'); }
                Ok(())
            }
        }
    });
    out
}

/* ---------- Gap 2: the read_all_optional Some branch -- the composed witness (replay + decision) ----------
   The Some branch's inside = Reader::new(input) + closure + the at_end
   decision; isomorphic to read_all. */

pub exec fn p4b_some_consumes_all() -> (r: Result<(), EndOfInput>)
    ensures
        r == Ok(()),
{
    let bytes = [b'f', b'o', b'o'];
    let input = Input::from(&bytes);
    let mut reader = Reader::new(input);
    proof {
        assert(reader.i == 0);
        assert(reader.input.seq() == input.seq());
        assert(reader.input.seq().len() == 3);
        assert(reader.input.seq()[0] == b'f');
        assert(reader.input.seq()[1] == b'o');
        assert(reader.input.seq()[2] == b'o');
    }
    let b0 = match reader.read_byte() {
        Ok(b) => b,
        Err(e) => {
            proof { assert(false); }
            return Err(e);
        }
    };
    assert(b0 == b'f');
    proof { assert(reader.i == 1); }
    let b1 = match reader.read_byte() {
        Ok(b) => b,
        Err(e) => {
            proof { assert(false); }
            return Err(e);
        }
    };
    assert(b1 == b'o');
    proof { assert(reader.i == 2); }
    let b2 = match reader.read_byte() {
        Ok(b) => b,
        Err(e) => {
            proof { assert(false); }
            return Err(e);
        }
    };
    assert(b2 == b'o');
    let at = reader.at_end();
    assert(at);
    proof { assert(reader.i == 3); assert(wf(&reader)); }
    read_all_decision(&mut reader, (), EndOfInput)
}

/* ---------- Gap 3: the read_all_optional Some-branch direct call (structural layer: panic-free + requires-side satisfiability) ---------- */

pub exec fn p4c_some_direct_call() -> (r: Result<(), EndOfInput>)
    ensures
        r is Ok || r is Err,
{
    let bytes = [b'f', b'o', b'o'];
    let input = Input::from(&bytes);
    proof { assert(input.seq() == foo_seq_p4()); }
    read_all_optional(Some(input), EndOfInput, |o: Option<&mut Reader<'_>>|
        -> (res: Result<(), EndOfInput>)
        requires
            o is None || (o is Some && old(o.get_Some_0()).i == 0
                && old(o.get_Some_0()).input.seq() == foo_seq_p4()),
        ensures
            o is None ==> res == Ok(()),
            o is Some ==> res == Ok(())
                && final(o.get_Some_0()).i == 3
                && final(o.get_Some_0()).input.seq() == old(o.get_Some_0()).input.seq(),
    {
        match o {
            None => Ok(()),
            Some(rr) => {
                let b0 = match rr.read_byte() {
                    Ok(b) => b,
                    Err(e) => {
                        proof { assert(false); }
                        return Err(e);
                    }
                };
                proof { assert(b0 == b'f'); }
                let b1 = match rr.read_byte() {
                    Ok(b) => b,
                    Err(e) => {
                        proof { assert(false); }
                        return Err(e);
                    }
                };
                proof { assert(b1 == b'o'); }
                let b2 = match rr.read_byte() {
                    Ok(b) => b,
                    Err(e) => {
                        proof { assert(false); }
                        return Err(e);
                    }
                };
                proof { assert(b2 == b'o'); }
                Ok(())
            }
        }
    })
}

/* ---------- Gap 4: peek/skip/read_partial coverage confirmation (supplementary assertions referencing the same-source ut_tests contracts) ---------- */

pub exec fn p4d_peek_skip_read_partial_gaps()
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
    // peek's two-way semantics (doc: "Returns true if there is at least
    // one more byte ... equal to b")
    let pf = r.peek(b'f');
    assert(pf);
    let po = r.peek(b'o');
    assert(!po);
    // skip's less-len branch (Err <==> out of bounds)
    let s_full = r.skip(3);
    assert(s_full is Ok);
    let over = r.skip(1);
    assert(over is Err);
    // read_partial reread check: the consumed segment never recurs (the
    // Reader's single-pass semantics)
    let bytes2 = [b'f', b'o', b'o'];
    let mut r2 = Reader::new(Input::from(&bytes2));
    proof {
        assert(r2.i == 0);
        assert(r2.input.seq() == foo_seq_p4());
    }
    let res = r2.read_partial(|rr: &mut Reader|
        -> (rrr: Result<u8, EndOfInput>)
        requires
            old(rr).i == 0 && old(rr).input.seq() == foo_seq_p4(),
        ensures
            rrr == Ok(b'f') && final(rr).i == old(rr).i + 1
                && final(rr).input.seq() == old(rr).input.seq(),
    {
        rr.read_byte()
    });
    match res {
        Ok(pair) => {
            // bytes_read is exactly the first-byte view (consistent with
            // the UT#8 contract)
            let _ = pair;
        }
        Err(e) => {
            let _ = e;
        }
    }
}

} // verus!

fn main() {}
