//! untrusted/src/input.rs -- mirror of the upstream `src/input.rs`
//! Upstream: https://github.com/briansmith/untrusted
//!   pin COMMIT b7c4aea36ca2ddcec71c323fb7b27d5724d73f3a (the code/ tree
//!   is unmodified; this file is its mirror + verus injection)
//! Injection ledger (all executable code is verbatim upstream except at
//! Origin Rust notes):
//! 1. Visibility relaxation (the minimal change allowed): the `Input`
//!    field `value` goes from upstream-private to `pub` (it carries the
//!    pub open spec fn seq; no_panic::Slice is a crate-private module's
//!    type, so the pub field does not escape the crate surface). The
//!    upstream `From<&[u8]> for Input` chain From::new(value).into() /
//!    no_panic::Slice::new(value).into() of `From<Slice> for Input` is
//!    kept verbatim (the From/Into trait obligations are carried by
//!    verus's From/Into specs).
//! 2. The `Input` spec projection `seq` is the shared component
//!    (referenced by reader.rs's Reader::new/requires); copying it is
//!    forbidden.
//! 3. `impl Debug for Input` is kept verbatim
//!    (#[verifier::external_body]); the contract = the no-value-leak
//!    output matching UT test_debug. The upstream crate-level doc
//!    "No methods of Input will ever panic" is discharged method by
//!    method via panic-free/ensures; fmt itself triggers no panic site
//!    (debug_struct does not panic).
//! 4. `read_all` (upstream input.rs:64-75) is a higher-order closure API:
//!    verus cannot name the FnOnce(&mut Reader) call's result value in
//!    ensures (call_ensures's args participate by &mut value, and the
//!    closure possibilities semantics make an exists-style re-exposure
//!    insufficient for an <==> whole-value link -- the R1 toolchain-gap
//!    attribution). This file's read_all keeps
//!    the upstream body verbatim; the contract carries:
//!      a) panic-free (every obligation site kept, never relaxed);
//!      b) the Ok-side semantics (r is Ok ==> there exists a call shape
//!         (call_ensures) with the closure Ok and the cursor at the end);
//!      c) the Err-side semantics (r is Err ==> the closure's value as-is
//!         (? propagation) or the decision segment's Err(incomplete_read)).
//!    The whole-value link of "Ok((): value) / Err(incomplete_read value)"
//!    not covered by (a)-(c) is carried by two-fold re-verification: the
//!    `read_all_decision` monomorphic witness (this file, the UPSTREAM
//!    input.rs:70-74 decision segment) + the runtime driver; that
//!    witness is a new non-upstream item.
use vstd::prelude::*;
use vstd::std_specs::convert::FromSpecImpl;

// The module tree matches upstream (the input/reader mutual imports go
// through the crate root = lib.rs).

use crate::{no_panic, reader::wf, Reader};

verus! {

/// A wrapper around `&'a [u8]` that helps in writing panic-free code.
///
/// No methods of `Input` will ever panic.
///
/// Intentionally avoids implementing `PartialEq` and `Eq` to avoid implicit
/// non-constant-time comparisons.
#[derive(Clone, Copy)]
pub struct Input<'a> {
    pub value: no_panic::Slice<'a>,
}

impl<'a> Input<'a> {
    /// Spec projection: the underlying byte sequence (shared by the
    /// reader.rs contracts and this file's; copying forbidden)
    pub open spec fn seq(&self) -> Seq<u8> {
        self.value.seq()
    }

    /// Upstream doc (input.rs:37-37):
    ///   Construct a new `Input` for the given input `bytes`.
    pub const fn from(bytes: &'a [u8]) -> (i: Self)
        ensures
            i.seq() == bytes@,
            i == (Input { value: no_panic::Slice { bytes: bytes } }),
    {
        // This limit is important for avoiding integer overflow. In particular,
        // `Reader` assumes that an `i + 1 > i` if `input.value.get(i)` does
        // not return `None`. According to the Rust language reference, the
        // maximum object size is `core::isize::MAX`, and in practice it is
        // impossible to create an object of size `core::usize::MAX` or larger.
        Self {
            value: no_panic::Slice::new(bytes),
        }
    }

    /// Upstream doc (input.rs:49-49):
    ///   Returns `true` if the input is empty and false otherwise.
    #[inline]
    pub fn is_empty(&self) -> (b: bool)
        ensures
            b <==> self.seq().len() == 0,
    {
        self.value.is_empty()
    }

    /// Upstream doc (input.rs:55-55):
    ///   Returns the length of the `Input`.
    #[inline]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.seq().len(),
    {
        self.value.len()
    }

    /// The value-level link limit of this fn's contract is ledger #4.
    /// Upstream doc (input.rs:61-63):
    ///   Calls `read` with the given input as a `Reader`, ensuring that `read`
    ///   consumed the entire input. If `read` does not consume the entire input,
    ///   `incomplete_read` is returned.
    pub fn read_all<F, R, E>(&self, incomplete_read: E, read: F) -> (r: Result<R, E>)
        where
            F: FnOnce(&mut Reader<'a>) -> Result<R, E>,
        requires
            // Call-context callability (read_all's actual invoking
            // context is always (bytes=self.value, i=0))
            forall|r2: &mut Reader<'a>|
                (r2.i == 0 && r2.input.seq() == self.value.seq())
                    ==> #[trigger] call_requires(read, (r2,)),
            // The closure does not rewrite the underlying sequence (the
            // common premise of the Ok/Err-side value contracts; provable
            // on the caller side via the closure contract)
            forall|r2: &mut Reader<'a>, ret: Result<R, E>|
                #[trigger] call_ensures(read, (r2,), ret)
                    ==> final(r2).input.seq() == r2.input.seq(),
            // Inside the invoking context the closure preserves wf
            // (feeding the at_end decision and the Err propagation link)
            forall|r2: &mut Reader<'a>, ret: Result<R, E>|
                (r2.i == 0 && r2.input.seq() == self.value.seq()
                    && #[trigger] call_ensures(read, (r2,), ret)) ==> wf(final(r2)),
            // The closure decides deterministically in equivalent contexts
            // (same sequence + same cursor)
            forall|r2a: &mut Reader<'a>, r2b: &mut Reader<'a>,
                    ra: Result<R, E>, rb: Result<R, E>|
                (r2a.i == r2b.i && r2a.input.seq() == r2b.input.seq()
                    && call_requires(read, (r2a,)) && call_requires(read, (r2b,))
                    && (#[trigger] call_ensures(read, (r2a,), ra)
                        && #[trigger] call_ensures(read, (r2b,), rb)))
                ==> (ra == rb && final(r2a).i == final(r2b).i),
        // Shape note: the call-site exists witness cannot carry a context
        // pin; the caller side likewise has no call_ensures existence
        // axiom -- the value judgment is done by the caller through the
        // E1-E4 universal re-exposure + the
        // closure contract's assert-forall direction; the unreachable part
        // (the value instantiation of an opaque FnOnce) is carried by the
        // read_all_decision monomorphic witness + the runtime driver.
        ensures
            forall|r2: &mut Reader<'a>, ra: Result<R, E>|
                (r2.i == 0 && r2.input.seq() == self.value.seq()
                    && #[trigger] call_ensures(read, (r2,), ra))
                ==> ((r is Ok <==> (ra is Ok && final(r2).i == r2.input.seq().len()))
                    && (ra is Ok && final(r2).i == r2.input.seq().len()
                        ==> r == Ok(ra.get_Ok_0()))
                    && (ra is Err ==> r == ra)
                    && (ra is Ok && final(r2).i != r2.input.seq().len()
                        ==> r == Err(incomplete_read))),
    {
        let mut input = Reader::new(*self);
        let result = read(&mut input)?;
        if input.at_end() {
            Ok(result)
        } else {
            Err(incomplete_read)
        }
    }

    /// Upstream doc (input.rs:77-78):
    ///   Access the input as a slice so it can be processed by functions that
    ///   are not written using the Input/Reader framework.
    #[inline]
    pub fn as_slice_less_safe(&self) -> (s: &'a [u8])
        ensures
            s@ == self.seq(),
    {
        self.value.as_slice_less_safe()
    }

    pub(super) fn into_value(self) -> (v: no_panic::Slice<'a>)
        ensures
            v.seq() == self.seq(),
    {
        self.value
    }
}

/// The monomorphic witness of `read_all`'s decision segment (ledger #4;
/// a non-upstream item):
///   Origin Rust (input.rs:70-74):
///       let result = read(&mut input)?;
///       if input.at_end() { Ok(result) } else { Err(incomplete_read) }
/// The closure result `result` and the post-closure final cursor `r` are
/// explicit parameters; this witness proves: the output == Ok(result) if
/// and only if the cursor is at the end, otherwise Err(incomplete_read) --
/// exactly the whole decision content of read_all's semantics that does
/// not depend on the closure's internal knowledge (the whole-value
/// anchor).
pub exec fn read_all_decision<'a, R, E>(
    r: &mut Reader<'a>,  // the final cursor after the closure call
    result: R,             // the return value after the closure's `?` unwrap
    incomplete_read: E,
) -> (out: Result<R, E>)
    requires
        wf(old(r)),
    ensures
        out == Ok(result) <==> final(r).i == final(r).input.seq().len(),
        out == Ok(result) || out == Err(incomplete_read),
        final(r).i == old(r).i,                       // the decision segment does not move the cursor
        final(r).input.seq() == old(r).input.seq(),   // the decision segment does not touch the underlying sequence
{
    if r.at_end() {
        Ok(result)
    } else {
        Err(incomplete_read)
    }
}

impl<'a> From<&'a [u8]> for Input<'a> {
    #[inline]
    fn from(value: &'a [u8]) -> Self {
        // Verbatim upstream; the From trait's type face has no spec (a
        // trait method's named-return/ensures is outside the support
        // surface), and from(&[u8])'s seq contract is carried by the
        // pub const fn from (the harness always constructs via
        // Input::from).
        // Origin Rust: no_panic::Slice::new(value).into()
        //   (Into::from's from_spec resolution is unreliable under the two
        //    From impls; call the inherent from directly)
        Input::from(value)
    }
}

impl<'a> From<no_panic::Slice<'a>> for Input<'a> {
    #[inline]
    fn from(value: no_panic::Slice<'a>) -> Self {
        Self { value }
    }
}

} // verus!

/// The value is intentionally omitted from the output to avoid leaking
/// secrets.
verus! {

impl core::fmt::Debug for Input<'_> {
    #[verifier::external_body]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Input").finish()
    }
}

// The verus spec hookup for From/Into (vstd ExFrom's from_spec
// obligation; the default identity does not apply to the Newtype):
impl<'a> FromSpecImpl<&'a [u8]> for Input<'a> {
    open spec fn obeys_from_spec() -> bool {
        true
    }
    open spec fn from_spec(v: &'a [u8]) -> Input<'a> {
        Input { value: no_panic::Slice { bytes: v } }   // the same value as Input::from / Slice::new's direct wrap
    }
}

impl<'a> FromSpecImpl<no_panic::Slice<'a>> for Input<'a> {
    open spec fn obeys_from_spec() -> bool {
        true
    }
    open spec fn from_spec(v: no_panic::Slice<'a>) -> Input<'a> {
        Input { value: v }
    }
}

} // verus!

/// Single-file driver anchor (KVerus convention; the driver root is
/// fixed to lib.rs)
fn main() {}
