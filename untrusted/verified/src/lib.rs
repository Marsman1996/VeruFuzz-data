//! untrusted/src/lib.rs -- mirror of the upstream `src/lib.rs`
//! Upstream: https://github.com/briansmith/untrusted
//!   pin COMMIT b7c4aea36ca2ddcec71c323fb7b27d5724d73f3a (the code/ tree
//!   is unmodified; this file is its mirror + verus injection).
//! lib.rs is the only verus driver root (mirror of the upstream mod
//! tree: the input/reader mutual imports are resolved through the crate
//! root).
//! Injection ledger:
//! 1. `read_all_optional` (upstream lib.rs:101-121) stays a higher-order
//!    closure API with the same contract as input.rs read_all (ledger
//!    #4): panic-free + Ok/Err-side existence clauses;
//! 2. `Reader::peek/skip/read_partial/read_all_optional` are covered by
//!    harness/ut_tests.rs and harness/phase4_gaps.rs.
//! 3. The upstream crate-level doc (the usage instructions) is not
//!    carried verbatim in this mirror; its semantics live in the
//!    contract layer; upstream line-number conversions are in each
//!    function's Origin Rust notes.
use vstd::prelude::*;
use crate::reader::wf;

#[path = "no_panic.rs"]
pub mod no_panic;
#[path = "input.rs"]
pub mod input;
#[path = "reader.rs"]
pub mod reader;

verus! {

pub use {
    input::Input,
    reader::{EndOfInput, Reader},
};


/// Upstream doc (lib.rs:98-100):
///   Calls `read` with the given input as a `Reader`, ensuring that `read`
///   consumed the entire input. When `input` is `None`, `read` will be
///   called with `None`.
pub fn read_all_optional<'a, F, R, E>(
    input: Option<Input<'a>>,
    incomplete_read: E,
    read: F,
) -> (r: Result<R, E>)
    where
        F: FnOnce(Option<&mut Reader<'a>>) -> Result<R, E>,
    requires
        // The None branch calls read(None) directly; the Some branch's
        // invoking context is always (bytes=input value, i=0)
        forall|r2: Option<&mut Reader<'a>>|
            (r2 is None
                || (r2 is Some && r2.get_Some_0().i == 0 && input is Some
                    && r2.get_Some_0().input.seq() == input.get_Some_0().seq()))
                ==> #[trigger] call_requires(read, (r2,)),
        forall|r2: Option<&mut Reader<'a>>, ret: Result<R, E>|
            #[trigger] call_ensures(read, (r2,), ret)
                ==> (r2 is None
                    || (r2 is Some
                        && final(r2.get_Some_0()).input.seq()
                            == r2.get_Some_0().input.seq())),
        forall|r2: Option<&mut Reader<'a>>, ret: Result<R, E>|
            (r2 is Some && r2.get_Some_0().i == 0 && input is Some
                && r2.get_Some_0().input.seq() == input.get_Some_0().seq()
                && #[trigger] call_ensures(read, (r2,), ret))
                ==> wf(final(r2.get_Some_0())),
        forall|r2a: Option<&mut Reader<'a>>, r2b: Option<&mut Reader<'a>>,
                ra: Result<R, E>, rb: Result<R, E>|
            ((r2a is None && r2b is None)
                || (r2a is Some && r2b is Some
                    && r2a.get_Some_0().i == r2b.get_Some_0().i
                    && r2a.get_Some_0().input.seq() == r2b.get_Some_0().input.seq()))
                && call_requires(read, (r2a,)) && call_requires(read, (r2b,))
                && (#[trigger] call_ensures(read, (r2a,), ra)
                    && #[trigger] call_ensures(read, (r2b,), rb))
                ==> (ra == rb
                    && (r2a is None
                        || final(r2a.get_Some_0()).i == final(r2b.get_Some_0()).i)),
    // Shape note: same as input.rs::read_all -- the call-site exists
    // witness cannot carry a context pin; the context is restored via
    // the requires determinism clause + the runtime driver.
    ensures
        forall|r2: Option<&mut Reader<'a>>, ra: Result<R, E>|
            ((input is None && r2 is None)
                || (input is Some && r2 is Some && r2.get_Some_0().i == 0
                    && r2.get_Some_0().input.seq() == input.get_Some_0().seq()))
            && #[trigger] call_ensures(read, (r2,), ra)
            ==> ((r is Ok <==> (ra is Ok
                    && (r2 is None
                        || final(r2.get_Some_0()).i
                            == r2.get_Some_0().input.seq().len())))
                && (ra is Ok && (r2 is Some
                        && final(r2.get_Some_0()).i == r2.get_Some_0().input.seq().len())
                    ==> r == Ok(ra.get_Ok_0()))
                && (ra is Err ==> r == ra)
                && (ra is Ok && r2 is Some
                    && final(r2.get_Some_0()).i != r2.get_Some_0().input.seq().len()
                    ==> r == Err(incomplete_read))),
{
    match input {
        Some(input) => {
            let mut input = Reader::new(input);
            let result = read(Some(&mut input))?;
            if input.at_end() {
                Ok(result)
            } else {
                Err(incomplete_read)
            }
        }
        None => read(None),
    }
}

} // verus!

/// Single-file driver anchor (KVerus convention)
fn main() {}
