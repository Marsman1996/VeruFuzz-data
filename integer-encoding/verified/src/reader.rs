//! verified/src/reader.rs -- the per-function mirror of the upstream
//! code/src/reader.rs (a KVerus migrate artifact)
//!
//! Mirror and relaxation ledger:
//! 1. `impl<R: Read> VarIntReader for R` (reader.rs:93-115) and the async variant
//!    (cfg off) rely on external reads through the std::io::Read trait. Verus
//!    cannot directly verify a std trait generic extension, so the mirror models
//!    "read from the slice one byte at a time" as `read_varint_bytes_level_<T>`:
//!    an upstream-equivalent byte-scanning semantics (upstream semantics =
//!    successive reads handed to the VarIntProcessor; on IO error / early EOF
//!    termination, modeled as partial input). The IO boundary itself (the
//!    self.read() calls) is recorded as blocked / out of scope (not a
//!    behavioral-difference face of the verified sites).
//! 2. `VarIntProcessor` (reader.rs:34-65) private struct -> mirrored pub,
//!    keeping the push/finished/decode state-machine semantics verbatim; the
//!    `buf` 10-byte array semantics unchanged.
//! 3. IO Error is modeled as the enum `IoErrKind { UnexpectedEof, InvalidData }`
//!    (corresponding to the two upstream io::ErrorKind cases:
//!    UnexpectedEof("Reached EOF") / InvalidData("Unterminated varint")).
//!
//! The upstream tree is untouched; this file is the verified/ side copy.

use super::fixed::*;
use super::varint::*;
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

/// IO error model (corresponding to the upstream io::Error::kind())
#[derive(PartialEq, Eq)]
pub enum IoErrKind {
    UnexpectedEof,
    InvalidData,
}

pub struct ReadOutcome<T> {
    pub value: T,          // the decoded value (on success)
    pub used: usize,       // number of bytes consumed
}

// ============================================================
// VarIntProcessor (Origin: reader.rs:34-65)
// ============================================================

/// Origin: reader.rs:34-47 VarIntProcessor { buf: [u8; 10], maxsize, i }
#[derive(Default)]
pub struct VarIntProcessor {
    pub buf: [u8; 10],
    pub maxsize: usize,
    pub i: usize,
}

impl VarIntProcessor {
    /// Origin: reader.rs:42-47 new<VI>()
    pub exec fn new(maxsize_arg: usize) -> (r: Self)
        ensures
            r.i == 0,
            r.maxsize == maxsize_arg,
    {
        Self {
            buf: [0; 10],
            maxsize: maxsize_arg,
            i: 0,
        }
    }

/// Origin: reader.rs:48-58 push: on i >= maxsize -> InvalidData("Unterminated varint")
    pub exec fn push(&mut self, b: u8) -> (r: Result<(), IoErrKind>)
        requires self.i < self.maxsize,
        ensures
            r.is_Ok() ==> final(self).i == old(self).i + 1,
    {
        // Origin: if self.i >= self.maxsize { return Err(InvalidData("Unterminated varint")) }
        if self.i >= self.maxsize {
            return Err(IoErrKind::InvalidData);
        }
        self.buf[self.i] = b;
        self.i += 1;
        Ok(())
    }

/// Origin: reader.rs:59-61 finished: the last byte has the MSB clear
    pub exec fn finished(&self) -> (r: bool)
        ensures r == (self.i > 0 && (self.buf[self.i - 1] & MSB) == 0)
    {
        self.i > 0 && (self.buf[self.i - 1] & MSB) == 0
    }

/// Origin: reader.rs:62-64 decode: VI::decode_var(&self.buf[0..self.i])?
/// (the u64 family -- the byte-level layer of the upstream read_varint::<u64>)
    pub exec fn decode_u64(&self) -> (r: Option<(u64, usize)>)
    {
        let slice: &[u8] = &self.buf[0..self.i];
        decode_var_u64(slice)
    }
}

// ============================================================
// read_varint byte-level model (Origin: reader.rs:93-115)
// ============================================================

/// Byte-stream semantics mirror of the upstream read_varint::<u64>: bytes are
/// pushed one at a time into the VarIntProcessor (maxsize=10), until finished
/// or the input is exhausted.
/// - exhausted (p.i==0) -> UnexpectedEof("Reached EOF") (Origin :102-104)
/// - exhausted (p.i>0) -> decode continues on the buffered bytes; failure ->
///   UnexpectedEof (Origin :89)
/// - maxsize exceeded -> InvalidData("Unterminated varint") (Origin :48-58)
/// Upstream doc (reader.rs:17-22):
///   Returns either the decoded integer, or an error.
///
///   In general, this always reads a whole varint. If the encoded varint's value is bigger
///   than the valid value range of `VI`, then the value is truncated.
///
///   On EOF, an [`io::Error`] with [`io::ErrorKind::UnexpectedEof`] is returned.
pub exec fn read_varint_bytes_u64(src: &[u8]) -> (r: Result<u64, IoErrKind>)
{
    // Origin: let mut p = VarIntProcessor::new::<VI>();
    let mut p = VarIntProcessor::new(10);
    let mut idx: usize = 0;
    let mut err: Option<IoErrKind> = None;
    while !p.finished() && idx < src.len() && err.is_none()
        invariant
            idx <= src.len(),
            p.i <= p.maxsize,
            p.maxsize == 10,
            p.i == idx,
        decreases src.len() - idx
    {
        let b = src[idx];
        // Origin: p.push(buf[0])? -- upstream reads one byte at a time
        if p.i >= p.maxsize {
            err = Some(IoErrKind::InvalidData);
            break;
        }
        p.buf[p.i] = b;
        p.i = p.i + 1;
        idx += 1;
    }
    if err.is_some() {
        return Err(IoErrKind::InvalidData);
    }
    match p.decode_u64() {
        Some((v, _s)) => Ok(v),
        None => Err(IoErrKind::UnexpectedEof),
    }
}

// SPEC-DOC MISMATCH (dermesser/integer-encoding-rs#47): the read_varint doc
// promises "If the encoded varint's value is bigger than the valid value range
// of VI, then the value is truncated", but on the over-range input nothing is
// truncated -- this witness returns Err(UnexpectedEof) (same shape as upstream),
// so the doc-promised truncation clause is unprovable; the implementation-
// faithful error form is carried here.
/// Value-domain witness (finding-related):
/// When the encoded value exceeds the target type's width, the upstream doc claims
/// "the value is truncated", but the behavior visible in this mirror: it returns
/// Err(UnexpectedEof) (same shape as upstream), not a truncation. (Compare the
/// UT reality of varint.rs V17 test_decode_var_too_big.)
pub exec fn read_varint_bytes_overflows_u64(src: &[u8]) -> (r: Option<IoErrKind>)
{
    let out = read_varint_bytes_u64(src);
    match out {
        Ok(_) => None,
        Err(e) => Some(e),
    }
}

// ============================================================
// read_fixedint byte-level model (Origin: reader.rs:143-149)
// ============================================================

/// Byte-stream semantics mirror of the upstream read_fixedint::<u64>: read_exact
/// of 8 bytes, then LE decode.
/// Fewer than 8 bytes -> UnexpectedEof; exactly 8 -> the LE value of those 8 bytes.
/// Upstream doc (reader.rs:119-121):
///   Read a fixed integer from a reader. How many bytes are read depends on `FI`.
///
///   On EOF, an [`io::Error`] with [`io::ErrorKind::UnexpectedEof`] is returned.
pub exec fn read_fixedint_bytes_u64(src: &[u8]) -> (r: Result<u64, IoErrKind>)
{
    if src.len() < 8 {
        return Err(IoErrKind::UnexpectedEof);
    }
    let slice: &[u8] = &src[0..8];
    match decode_fixed_u64(slice) {
        Some(v) => Ok(v),
        None => Err(IoErrKind::UnexpectedEof),
    }
}

} // verus!
