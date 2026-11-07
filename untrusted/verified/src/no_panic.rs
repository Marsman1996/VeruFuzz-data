//! `untrusted/src/no_panic.rs` mirror
//!
//! Upstream: https://github.com/briansmith/untrusted
//!   pin COMMIT b7c4aea36ca2ddcec71c323fb7b27d5724d73f3a (the code/ tree is
//!   unmodified; this file is its byte-level mirror + verus injection)
//!
//! Injection ledger (except where marked below, the executable code is
//! verbatim upstream):
//! 1. (visibility) `Slice::seq` spec projection: the Seq view of the pub
//!    field `bytes`; the cross-file (reader/input) contract shared
//!    component.
//! 2. `get`/`subslice`'s None/Some semantic contract is carried directly
//!    by vstd `assume_specification[SliceIndex::get]` (the usize and
//!    Range<usize> instances); the struct side restates it as a Seq-domain
//!    contract via ensures.
//! 3. `#[derive(Clone, Copy)]` kept (the `&[u8]` field is Copy, no side
//!    effects).
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
pub struct Slice<'a> {
    pub bytes: &'a [u8],
}

impl<'a> Slice<'a> {
    /// Spec projection: the underlying byte sequence (the shared
    /// component; the reader/input contracts reference this definition,
    /// copying forbidden)
    pub open spec fn seq(&self) -> Seq<u8> {
        self.bytes@
    }

    #[inline]
    pub const fn new(bytes: &'a [u8]) -> (s: Self)
        ensures
            s.seq() == bytes@,
            s.bytes == bytes,
    {
        Self { bytes }
    }

    #[inline]
    pub fn get(&self, i: usize) -> (r: Option<&u8>)
        ensures
            r is Some <==> i < self.seq().len(),
            r is Some ==> *r.get_Some_0() == self.seq()[i as int],
    {
        self.bytes.get(i)
    }

    #[inline]
    pub fn subslice(&self, r: core::ops::Range<usize>) -> (ret: Option<Self>)
        ensures
            ret is Some <==> (r.start <= r.end && r.end <= self.seq().len()),
            ret is Some ==> ret.get_Some_0().seq() == self.seq()[r.start as int..r.end as int],
    {
        // Origin Rust: self.bytes.get(r).map(|bytes| Self { bytes })
        //   (the Option::map closure path rewritten as an equivalent
        //    match, semantically verbatim)
        match self.bytes.get(r) {
            Some(bytes) => Some(Self { bytes }),
            None => None,
        }
    }

    #[inline]
    pub fn is_empty(&self) -> (b: bool)
        ensures
            b <==> self.seq().len() == 0,
    {
        self.bytes.is_empty()
    }

    #[inline]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.seq().len(),
    {
        self.bytes.len()
    }

    #[inline]
    pub fn as_slice_less_safe(&self) -> (s: &'a [u8])
        ensures
            s@ == self.seq(),
    {
        self.bytes
    }
}

} // verus!

/// Single-file driver tail anchor (KVerus convention; the harness side
/// references this file via #[path])
fn main() {}
