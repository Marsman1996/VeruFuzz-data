//! tpm-core 0.1.4 read-only parsing cursor family (src/cursor.rs) --
//! Verus translation.
//!
//! The byte/word decode anchors of the batch live here (upstream
//! cursor.rs:45 read_u8 and the be16/be32 cousins), together with the
//! position-discipline faces: every read_*/skip either advances by
//! exactly the field width or fails with the position unchanged.

use vstd::prelude::*;

verus! {

use super::endian::{be16_of, be16_of_exec, be32_of, be32_of_exec};

// ------------------------------------------------------------------
// Byte-encoding helpers (cursor.rs:2-8)
// ------------------------------------------------------------------

/// Big-endian byte encoding of a u16, as a spec face.
pub open spec fn be16_bytes_spec(v: u16) -> Seq<u8> {
    seq![(v / 256) as u8, (v % 256) as u8]
}

/// Big-endian byte encoding of a u32, as a spec face.
pub open spec fn be32_bytes_spec(v: u32) -> Seq<u8> {
    seq![
        (v / 16777216) as u8,
        (v / 65536 % 256) as u8,
        (v / 256 % 256) as u8,
        (v % 256) as u8,
    ]
}

/// Origin Rust: /// Integer to big-endian bytes. This is the inverse of `spec_be16_at`.
/// pub(crate) fn be16_bytes(v: u16) -> [u8; 2] {
///     v.to_be_bytes()
/// } (src/cursor.rs:1-4; to_be_bytes lowered to the spelled quotient
/// pair, same bytes).
pub(crate) exec fn be16_bytes(v: u16) -> (r: [u8; 2])
    ensures
        r@ == be16_bytes_spec(v),
{
    [(v / 256u16) as u8, (v % 256u16) as u8]
}

/// Origin Rust: /// Integer to big-endian bytes. This is the inverse of `spec_be32_at`.
/// pub(crate) fn be32_bytes(v: u32) -> [u8; 4] {
///     v.to_be_bytes()
/// } (src/cursor.rs:5-8; to_be_bytes lowered to the spelled quotient
/// quadruple).
pub(crate) exec fn be32_bytes(v: u32) -> (r: [u8; 4])
    ensures
        r@ == be32_bytes_spec(v),
{
    [
        (v / 16777216u32) as u8,
        (v / 65536u32 % 256u32) as u8,
        (v / 256u32 % 256u32) as u8,
        (v % 256u32) as u8,
    ]
}

// ------------------------------------------------------------------
// Cursor (cursor.rs:11-105)
// ------------------------------------------------------------------

/// Origin Rust: /// Read-only parsing cursor. `pos` is private; progress can only happen through `read_*`/`skip`, and
/// /// external code can read the current position via [`Cursor::pos`].
/// pub struct Cursor {
///     pos: usize,
/// } (src/cursor.rs:9-13)
pub struct Cursor {
    pub pos: usize,
}

impl Cursor {
    /// Origin Rust: pub fn new() -> Cursor {
    ///     Cursor { pos: 0 }
    /// } (src/cursor.rs:15-17)
    pub exec fn new() -> (c: Cursor)
        ensures
            c.pos == 0,
    {
        Cursor { pos: 0 }
    }

    /// Origin Rust: /// Current parsing position. The parser uses this to record the start of each field (for example,
    /// parameter area offsets or nonce offsets).
    /// pub fn pos(&self) -> usize (src/cursor.rs:18-20)
    pub exec fn pos(&self) -> (p: usize)
        ensures
            p == self.pos,
    {
        self.pos
    }
}

impl Default for Cursor {
    /// Origin Rust: impl Default for Cursor {
    ///     fn default() -> Self {
    ///         Self::new()
    ///     }
    /// } (src/cursor.rs:25-29)
    fn default() -> (c: Self)
        ensures
            c.pos == 0,
    {
        Self::new()
    }
}

impl Cursor {
    /// Origin Rust: /// Parse starting at a specified offset (for skipping fixed prefixes that were already validated by a
    /// higher layer).
    /// pub fn at(pos: usize) -> Cursor {
    ///     Cursor { pos }
    /// } (src/cursor.rs:32-36; upstream doc glyphs converted ASCII:
    /// "for skipping fixed prefixes that were already validated by
    /// a higher layer")
    pub exec fn at(pos: usize) -> (c: Cursor)
        ensures
            c.pos == pos,
    {
        Cursor { pos }
    }

    /// Origin Rust: pub fn remaining(&self, data: &[u8]) -> usize {
    ///     data.len() - self.pos
    /// } (src/cursor.rs:37-39)
    /// The subtraction is unchecked upstream: a Cursor::at(pos) with
    /// pos above the slice length makes this panic in a checked build.
    /// The requires encodes the at-doc's higher-layer validation
    /// discipline (suspects row in the out/ ledger, not a filed
    /// mismatch).
    pub exec fn remaining(&self, data: &[u8]) -> (r: usize)
        requires
            self.pos <= data.len(),
        ensures
            (r as int) == (data.len() as int) - (self.pos as int),
    {
        data.len() - self.pos
    }

    /// Origin Rust: /// Whether the remaining bytes are exactly exhausted. Used for checks such as "the response tail must
    /// contain no extra data."
    /// pub fn is_exhausted(&self, data: &[u8]) -> bool {
    ///     self.pos == data.len()
    /// } (src/cursor.rs:40-44)
    pub exec fn is_exhausted(&self, data: &[u8]) -> (r: bool)
        ensures
            r == (self.pos == data.len()),
    {
        self.pos == data.len()
    }

    /// Origin Rust: pub fn read_u8(&mut self, data: &[u8]) -> Option<u8> {
    ///     if self.pos < data.len() { ... } else { None }
    /// } (src/cursor.rs:45-53)
    /// Position discipline: Some advances by exactly one, None leaves
    /// the position untouched.
    pub exec fn read_u8(&mut self, data: &[u8]) -> (r: Option<u8>)
        ensures
            r.is_Some() == (old(self).pos < data.len()),
            r.is_Some() ==> final(self).pos == old(self).pos + 1 && r == Option::Some(data@[(old(self).pos) as int]),
            r.is_None() ==> final(self).pos == old(self).pos,
    {
        if self.pos < data.len() {
            let v = data[self.pos];
            self.pos += 1;
            Some(v)
        } else {
            None
        }
    }

    /// Origin Rust: pub fn read_be16(&mut self, data: &[u8]) -> Option<u16> {
    ///     let n = data.len();
    ///     if n >= 2 && self.pos <= n - 2 { ... } else { None }
    /// } (src/cursor.rs:54-63)
    pub exec fn read_be16(&mut self, data: &[u8]) -> (r: Option<u16>)
        ensures
            r.is_Some() == (data.len() >= 2 && old(self).pos + 2 <= data.len()),
            r.is_Some() ==> final(self).pos == old(self).pos + 2
                && (r.unwrap() as int)
                    == be16_of(
                        data@[(old(self).pos) as int],
                        data@[(old(self).pos + 1) as int],
                    ),
            r.is_None() ==> final(self).pos == old(self).pos,
    {
        let n = data.len();
        if n >= 2 && self.pos <= n - 2 {
            let v = be16_of_exec(data[self.pos], data[self.pos + 1]);
            self.pos += 2;
            Some(v)
        } else {
            None
        }
    }

    /// Origin Rust: pub fn read_be32(&mut self, data: &[u8]) -> Option<u32> {
    ///     let n = data.len();
    ///     if n >= 4 && self.pos <= n - 4 { ... } else { None }
    /// } (src/cursor.rs:64-78)
    pub exec fn read_be32(&mut self, data: &[u8]) -> (r: Option<u32>)
        ensures
            r.is_Some() == (data.len() >= 4 && old(self).pos + 4 <= data.len()),
            r.is_Some() ==> final(self).pos == old(self).pos + 4
                && (r.unwrap() as int)
                    == be32_of(
                        data@[(old(self).pos) as int],
                        data@[(old(self).pos + 1) as int],
                        data@[(old(self).pos + 2) as int],
                        data@[(old(self).pos + 3) as int],
                    ),
            r.is_None() ==> final(self).pos == old(self).pos,
    {
        let n = data.len();
        if n >= 4 && self.pos <= n - 4 {
            let v = be32_of_exec(
                data[self.pos],
                data[self.pos + 1],
                data[self.pos + 2],
                data[self.pos + 3],
            );
            self.pos += 4;
            Some(v)
        } else {
            None
        }
    }

    /// Origin Rust: /// Borrow the next `n` bytes. This is the only way to consume variable-length fields such as `TPM2B`
    /// and PCR selection bitmaps; the length comes from the packet itself, so boundary checks must happen
    /// here.
    /// pub fn read_bytes<'a>(&mut self, data: &'a [u8], n: usize) -> Option<&'a [u8]> (src/cursor.rs:79-93)
    /// Peer-controlled n: the returned slice is provably inside data
    /// (start/end discipline face).
    pub exec fn read_bytes<'a>(&mut self, data: &'a [u8], n: usize) -> (r: Option<&'a [u8]>)
        ensures
            r.is_Some() == (n <= data.len() && old(self).pos + n <= data.len()),
            r.is_Some() ==> final(self).pos == old(self).pos + n
                && r.unwrap()@ == data@.subrange((old(self).pos) as int, (old(self).pos + n) as int),
            r.is_None() ==> final(self).pos == old(self).pos,
    {
        let len = data.len();
        if n <= len && self.pos <= len - n {
            let start = self.pos;
            let end = self.pos + n;
            let s = &data[start..end];
            self.pos = end;
            Some(s)
        } else {
            None
        }
    }

    /// Origin Rust: /// Skip `n` bytes. This is used to ignore fields that are uninteresting in the current phase but whose
    /// layout is known.
    /// pub fn skip(&mut self, data: &[u8], n: usize) -> bool (src/cursor.rs:94-104)
    pub exec fn skip(&mut self, data: &[u8], n: usize) -> (r: bool)
        ensures
            r == (n <= data.len() && old(self).pos + n <= data.len()),
            r ==> final(self).pos == old(self).pos + n,
            !r ==> final(self).pos == old(self).pos,
    {
        let len = data.len();
        if n <= len && self.pos <= len - n {
            self.pos += n;
            true
        } else {
            false
        }
    }
}

// ------------------------------------------------------------------
// any_nonzero (cursor.rs:106-112)
// ------------------------------------------------------------------

/// Non-zero predicate at one index.
pub(crate) open spec fn nonzero_at(s: Seq<u8>, i: int) -> bool {
    0 <= i < s.len() && s[i] != 0
}

/// Truth of "some byte among the first k is non-zero", by prefix
/// recursion (the spec twin of the iter().any loop).
pub(crate) open spec fn any_nonzero_upto(s: Seq<u8>, k: int) -> bool
    decreases
        k,
{
    if k <= 0 {
        false
    } else {
        any_nonzero_upto(s, k - 1) || nonzero_at(s, k - 1)
    }
}

/// Whole-sequence face: a sequence contains a non-zero byte iff some
/// prefix position is non-zero (upto over the full length).
pub(crate) open spec fn any_nonzero_spec(s: Seq<u8>) -> bool {
    any_nonzero_upto(s, s.len() as int)
}

/// Origin Rust: /// Whether a slice contains any non-zero bytes.
/// ///
/// /// PCR allocation parsing uses this to determine whether a bank is actually allocated; a zero selection
/// /// bitmap means the algorithm is supported but not active.
/// pub(crate) fn any_nonzero(s: &[u8]) -> bool {
///     s.iter().any(|&b| b != 0)
/// } (src/cursor.rs:106-112)
pub(crate) exec fn any_nonzero(s: &[u8]) -> (r: bool)
    ensures
        r == any_nonzero_spec(s@),
{
    let mut i: usize = 0;
    let mut found = false;
    let n = s.len();
    while i < n
        invariant
            i <= n,
            s@.len() == n,
            found == any_nonzero_upto(s@, i as int),
        decreases
            n - i,
    {
        if s[i] != 0 {
            found = true;
        }
        i += 1;
    }
    found
}

} // verus!
