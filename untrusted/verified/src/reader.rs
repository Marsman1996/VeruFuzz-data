//! untrusted/src/reader.rs -- mirror of the upstream `src/reader.rs`
//! Upstream: https://github.com/briansmith/untrusted
//!   pin COMMIT b7c4aea36ca2ddcec71c323fb7b27d5724d73f3a (the code/ tree
//!   is unmodified; this file is its mirror + verus injection)
//! Injection ledger (all executable code is verbatim upstream except at
//! Origin Rust notes):
//! 1. Visibility relaxation (the minimal change allowed): the Reader
//!    fields input/i go from upstream-private to `pub` to carry the pub
//!    open spec fn wf (the formalized invariant of the upstream
//!    reader.rs:40 comment "safe from overflow; see Input::from()" and
//!    input.rs:39-45's "Reader assumes i+1 > i"). The no-panic contract
//!    continues to be carried by each method's ensures/panic-free
//!    obligations.
//! 2. EndOfInput keeps the upstream derive(Clone, Copy, Debug, Eq,
//!    PartialEq) (a single empty struct, carriable by verus; Debug is
//!    needed by read_bytes_to_end's .unwrap() Debug bound).
//! 3. fn-as-value / Option::map paths are equivalently rewritten (marked
//!    by Origin Rust notes).
//! 4. impl Debug for Reader is kept verbatim
//!    (#[verifier::external_body]); it carries the UT test_debug text
//!    contract.
//! 5. `wf`/`input_seq` are the spec shared components, referenced by
//!    input.rs/harness; copying is forbidden.
//! 6. The trailing `fn main() {}` is the single-file driver anchor; the
//!    driver root is fixed to lib.rs (mutual imports go through the
//!    crate root, matching the upstream mod tree).
use vstd::prelude::*;
use crate::{no_panic, Input};

// The module tree matches upstream (the input/reader mutual imports go
// through the crate root = lib.rs, the only verus driver root;
// no_panic.rs can additionally be driven as a single file).

verus! {

#[derive(Clone, Copy)]
pub struct Reader<'a> {
    pub input: no_panic::Slice<'a>,
    pub i: usize,
}

/// Cursor invariant: the Reader's cursor never passes the end of the
/// sequence (0 <= i <= len). The formalization object = the upstream
/// comment "safe from overflow; see Input::from()" (reader.rs:40) and
/// input.rs:39-45 ("Reader assumes that i + 1 > i if input.value.get(i)
/// does not return None").
pub open spec fn wf(r: &Reader) -> bool {
    r.i <= r.input.seq().len()
}

/// The error type used to indicate the end of the input was reached before the
/// operation could be completed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct EndOfInput;

impl<'a> Reader<'a> {
    /// Upstream doc (reader.rs:41-42):
    ///   Construct a new Reader for the given input. Use `read_all` or
    ///   `read_all_optional` instead of `Reader::new` whenever possible.
    #[inline]
    pub fn new(input: Input<'a>) -> (r: Self)
        ensures
            r.input.seq() == input.seq(),   // input.seq(): input.rs injection ledger #2
            r.i == 0,
            wf(&r),
    {
        Self {
            input: input.into_value(),
            i: 0,
        }
    }

    /// Upstream doc (reader.rs:51-52):
    ///   Returns `true` if the reader is at the end of the input, and `false`
    ///   otherwise.
    #[inline]
    pub fn at_end(&self) -> (b: bool)
        ensures
            b <==> self.i == self.input.seq().len(),  // &self: no mutation surface
    {
        self.i == self.input.len()
    }

    /// Upstream doc (reader.rs:58-59):
    ///   Returns `true` if there is at least one more byte in the input and that
    ///   byte is equal to `b`, and false otherwise.
    #[inline]
    pub fn peek(&self, b: u8) -> (r: bool)
        ensures
            r <==> (self.i < self.input.seq().len() && self.input.seq()[self.i as int] == b),  // &self
    {
        match self.input.get(self.i) {
            Some(actual_b) => b == *actual_b,
            None => false,
        }
    }

    /// Upstream doc (reader.rs:68-71):
    ///   Reads the next input byte.
    ///   Returns `Ok(b)` where `b` is the next input byte, or `Err(EndOfInput)`
    ///   if the `Reader` is at the end of the input.
    #[inline]
    pub fn read_byte(&mut self) -> (r: Result<u8, EndOfInput>)
        ensures
            r is Ok <==> old(self).i < old(self).input.seq().len(),
            r is Ok ==> {
                &&& r.get_Ok_0() == old(self).input.seq()[old(self).i as int]
                &&& final(self).i == old(self).i + 1
            },
            r is Err <==> old(self).i >= old(self).input.seq().len(),
            r is Err ==> final(self).i == old(self).i,
            final(self).input.seq() == old(self).input.seq(),   // verbatim upstream: read_byte does not touch the underlying sequence
    {
        match self.input.get(self.i) {
            Some(b) => {
                // Some <==> i < len (the get contract) => i+1 stays inside
                // the usize bound (the upstream comment "safe from
                // overflow")
                let l = self.input.len();
                proof {
                    assert(self.i < l);
                }
                self.i += 1; // safe from overflow; see Input::from().
                Ok(*b)
            }
            None => Err(EndOfInput),
        }
    }

    /// Upstream doc (reader.rs:83-87):
    ///   Skips `num_bytes` of the input, returning the skipped input as an
    ///   `Input`.
    ///   Returns `Ok(i)` if there are at least `num_bytes` of input remaining,
    ///   and `Err(EndOfInput)` otherwise.
    #[inline]
    pub fn read_bytes(&mut self, num_bytes: usize) -> (r: Result<Input<'a>, EndOfInput>)
        requires
            wf(old(self)),
        ensures
            r is Ok <==> old(self).i as int + num_bytes as int <= old(self).input.seq().len(),
            r is Ok ==> {
                &&& final(self).i == old(self).i as int + num_bytes as int
                &&& r.get_Ok_0().seq() == old(self).input.seq()[old(self).i as int..final(self).i as int]
            },
            r is Err <==> old(self).i as int + num_bytes as int > old(self).input.seq().len(),
            r is Err ==> final(self).i == old(self).i,
            final(self).input.seq() == old(self).input.seq(),
    {
        // Origin Rust: let new_i = self.i.checked_add(num_bytes).ok_or(EndOfInput)?;
        //   usize::checked_add has no verus spec: equivalent rewrite (Some
        //   <==> n <= usize::MAX - i); the else branch returns Err early,
        //   the cursor unmoved, matching the upstream `?` propagation
        //   semantics.
        let seq_len = self.input.len(); // usize-domain fold anchor (Slice::len ensures ==> seq().len() same value)
        proof {
            assert(self.input.seq().len() == seq_len as int);
            assert(seq_len <= usize::MAX);
        }
        let new_i = if num_bytes <= usize::MAX - self.i {
            self.i + num_bytes
        } else {
            return Err(EndOfInput);
        };
        // Origin Rust: let ret = self.input.subslice(self.i..new_i).map(From::from).ok_or(EndOfInput)?;
        //   Option map + From::from fn-as-value are outside the verus
        //   translation surface: None returns Err early (matching
        //   ok_or(?)), the Some branch constructs equivalently via
        //   Input::from(Slice::as_slice_less_safe()) (the Newtype of
        //   From<Slice> for Input, equal per value; see input.rs ledger #1
        //   and input.rs's FromSpecImpl specs).
        let ret = match self.input.subslice(self.i..new_i) {
            Some(s) => Input::from(s.as_slice_less_safe()),
            None => return Err(EndOfInput),
        };
        self.i = new_i;
        Ok(ret)
    }

    /// The doc's semantic contract enters requires/ensures.
    /// Upstream doc (reader.rs:100-101):
    ///   Skips the reader to the end of the input, returning the skipped input
    ///   as an `Input`.
    #[inline]
    pub fn read_bytes_to_end(&mut self) -> (r: Input<'a>)
        requires
            wf(old(self)),
        ensures
            final(self).i == old(self).input.seq().len(),   // upstream doc "Skips the reader to the end"
            r.seq() == old(self).input.seq()[old(self).i as int..final(self).i as int],
            final(self).input.seq() == old(self).input.seq(),
    {
        let to_skip = self.input.len() - self.i; // wf guarantees no self-overflow; upstream relies on the Reader invariant
        self.read_bytes(to_skip).unwrap()
    }

    /// The closure is an opaque higher-order parameter: requires only asks
    /// the closure to be callable on every wf reader (at the invoking point
    /// old(self) satisfies wf, hence callee.requires is satisfiable), that
    /// the closure preserves wf, and that the cursor only moves forward (the
    /// unwrap consumes this fact); the whole-value link between the output
    /// and the closure's return value is handled centrally by the read_all
    /// family's higher-order value-contract ledger (src/input.rs ledger #4).
    /// Upstream doc (reader.rs:108-110):
    ///   Calls `read()` with the given input as a `Reader`. On success, returns a
    ///   pair `(bytes_read, r)` where `bytes_read` is what `read()` consumed and
    ///   `r` is `read()`'s return value.
    pub fn read_partial<F, R, E>(&mut self, read: F) -> (r: Result<(Input<'a>, R), E>)
        where
            F: FnOnce(&mut Reader<'a>) -> Result<R, E>,
        requires
            wf(old(self)),
            // Call-context callability (read_partial's actual invoking
            // point = (bytes=old(self).input, i=old(self).i))
            forall|r2: &mut Reader<'a>|
                (r2.i == old(self).i && r2.input.seq() == old(self).input.seq())
                    ==> #[trigger] call_requires(read, (r2,)),
            // Everything below is a closure behavior contract inside the
            // invoking context (the closure is responsible for the
            // in-context reader)
            forall|r2: &mut Reader<'a>, ret: Result<R, E>|
                (r2.i == old(self).i && r2.input.seq() == old(self).input.seq()
                    && #[trigger] call_ensures(read, (r2,), ret)) ==> {
                    &&& wf(final(r2))
                    &&& r2.i <= final(r2).i
                    &&& final(r2).input.seq() == r2.input.seq()
                },
        ensures
            r is Ok ==> {
                &&& r.get_Ok_0().0.seq()
                    == old(self).input.seq()[old(self).i as int..final(self).i as int]
                &&& final(self).i >= old(self).i
            },
    {
        let start = self.i;
        let r = read(self)?;
        // Origin Rust: let bytes_read = self.input.subslice(start..self.i).unwrap().into();
        //   (Into::from resolution is restricted; equivalent rewrite
        //    calling the inherent from)
        let bytes_read = Input::from(self.input.subslice(start..self.i).unwrap().as_slice_less_safe());
        Ok((bytes_read, r))
    }

    /// Upstream doc (reader.rs:121-124):
    ///   Skips `num_bytes` of the input.
    ///   Returns `Ok(i)` if there are at least `num_bytes` of input remaining,
    ///   and `Err(EndOfInput)` otherwise.
    #[inline]
    pub fn skip(&mut self, num_bytes: usize) -> (r: Result<(), EndOfInput>)
        requires
            wf(old(self)),
        ensures
            r is Ok <==> old(self).i as int + num_bytes as int <= old(self).input.seq().len(),
            r is Ok ==> final(self).i == old(self).i as int + num_bytes as int,
            r is Err <==> old(self).i as int + num_bytes as int > old(self).input.seq().len(),
            r is Err ==> final(self).i == old(self).i,
            final(self).input.seq() == old(self).input.seq(),
            final(self).input.seq() == old(self).input.seq(),
    {
        // Origin Rust: self.read_bytes(num_bytes).map(|_| ())
        let _ = self.read_bytes(num_bytes)?;
        Ok(())
    }

    /// Upstream doc (reader.rs:130-130):
    ///   Skips the reader to the end of the input.
    #[inline]
    pub fn skip_to_end(&mut self)
        requires
            wf(old(self)),
        ensures
            final(self).i == old(self).input.seq().len(),
            final(self).input.seq() == old(self).input.seq(),
    {
        let _ = self.read_bytes_to_end();
    }
}

} // verus!

verus! {

impl core::fmt::Debug for Reader<'_> {
    #[verifier::external_body]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Reader").finish()
    }
}

} // verus!

/// Single-file driver anchor (KVerus convention; consumers reference it
/// via #[path] in the harness files)
fn main() {}
