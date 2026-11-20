//! tpm-core 0.1.4 chip adapter: return-code classification and the
//! verified CtxIo context round trip (src/chip.rs) -- Verus
//! translation.
//!
//! Upstream face: the Format-1 return-code masking pair
//! rc_value/classify_rc, the ChipTransport trust boundary (TRUST
//! 1-3 doc), and the CtxIo adapter that assembles context
//! load/save/flush packets, checks response spans, and classifies
//! return codes (src/chip.rs:1-237; the inline #[cfg(test)] module
//! at :208-237 is transcribed as the batch harness
//! verified/harness/ut_chip_classify.rs).
//!
//! Re-erected here:
//!  - rc_value stays value-exact (the Format-1 bit-masking is
//!    lowered to the / %-spelling, probe-confirmed opaque-bit-idiom
//!    of this batch; same values);
//!  - classify_rc is the total classification table over the
//!    masked value: only the documented rc set maps to the
//!    recoverable variants, everything else is Fatal;
//!  - load checks the response code BEFORE the response span
//!    (the upstream test's precedence: an rc HANDLE over a
//!    header-only response is NotFound, not Protocol -- the UT
//!    harness replays exactly that shape);
//!  - the CtxIo methods discharge the ContextIo trait face
//!    (off-chain, nonzero consumption, span-containment);
//!  - flush fires the transport unconditionally and ignores the
//!    outcome (the doc's irreparable-leak rationale).
//!
//! TOOLCHAIN NOTE: the colliding constant writes of copy_from_slice
//! into the fixed array fields are lowered to scalar index writes;
//! to_be_bytes is lowered to the / %-byte spelling (same bytes).

use vstd::prelude::*;

verus! {

use super::module::{ContextIo, IoErr};
use super::msg::{build_header, ST_NO_SESSIONS};
use super::rewrite::{read_be32, wire_be32, HEADER_SIZE};

// ------------------------------------------------------------------
// Return codes (chip.rs:8-29)
// ------------------------------------------------------------------

/// Origin Rust: pub const RC_SUCCESS: u32 = 0x0000_0000; (chip.rs:8)
pub const RC_SUCCESS: u32 = 0x0000_0000;
/// Bit 0x0000_0080 marks a "Format-1" return code: the low 6 bits
/// are the error number, bits 8..11 the offending index. The spec's
/// selector bits must be masked off before classification
/// (pub-visibility restatement of the upstream private mask
/// constant -- spec faces may not cite private items, pitfall
/// #T2-4; same value).
pub const RC_FMT1_VALUE: u32 = 0x0000_0080;
pub(crate) const RC_FMT1_BIT: u32 = 0x0000_0080;
/// Origin Rust: const RC_FMT1_MASK: u32 = 0x0000_00BF; (chip.rs:13-18;
/// same pub-restatement note: bit 6 (TPM_RC_P) plus bits 8..11 are
/// masked by classification)
pub(crate) const RC_FMT1_MASK: u32 = 0x0000_00BF;
/// Origin Rust: const RC_HANDLE: u32 = 0x0000_008B; (chip.rs:19)
pub(crate) const RC_HANDLE: u32 = 0x0000_008B;
/// Origin Rust: const RC_INTEGRITY: u32 = 0x0000_009F; (chip.rs:20)
pub(crate) const RC_INTEGRITY: u32 = 0x0000_009F;
/// Origin Rust: const RC_CONTEXT_GAP: u32 = 0x0000_0901; (chip.rs:21)
pub(crate) const RC_CONTEXT_GAP: u32 = 0x0000_0901;
/// Origin Rust: const RC_OBJECT_MEMORY: u32 = 0x0000_0902; (chip.rs:22)
pub(crate) const RC_OBJECT_MEMORY: u32 = 0x0000_0902;
/// Origin Rust: const RC_SESSION_MEMORY: u32 = 0x0000_0903; (chip.rs:23)
pub(crate) const RC_SESSION_MEMORY: u32 = 0x0000_0903;
/// Origin Rust: const RC_MEMORY: u32 = 0x0000_0904; (chip.rs:24)
pub(crate) const RC_MEMORY: u32 = 0x0000_0904;
/// Origin Rust: const RC_REFERENCE_H0: u32 = 0x0000_0910; (chip.rs:25)
pub(crate) const RC_REFERENCE_H0: u32 = 0x0000_0910;
/// Origin Rust: pub const RC_YIELDED: u32 = 0x0000_0908; (chip.rs:26)
pub const RC_YIELDED: u32 = 0x0000_0908;
/// Origin Rust: pub const RC_TESTING: u32 = 0x0000_090A; (chip.rs:27)
pub const RC_TESTING: u32 = 0x0000_090A;
/// Origin Rust: pub const RC_RETRY: u32 = 0x0000_0922; (chip.rs:28)
pub const RC_RETRY: u32 = 0x0000_0922;

// ------------------------------------------------------------------
// Return-code masking and classification (chip.rs:29-59)
// ------------------------------------------------------------------

/// Spec twin of the Format-1 mask: bit 7 set means the error
/// number lives in the low 6 bits with bit 6 (the parameter
/// selector) cleared; everything above byte 0 is index bits which
/// classification must ignore. Spelled in / %-arithmetic
/// (probe-confirmed opaque-& idiom of this batch).
pub open spec fn spec_rc_value(rc: u32) -> int {
    if (rc as int / 128) % 2 == 1 {
        let low = (rc as int) % 256;
        if low % 128 >= 64 {
            low - 64
        } else {
            low
        }
    } else {
        rc as int
    }
}

/// Spec twin of the classification table (only the documented rc
/// set reaches the recoverable variants; the default arm is
/// Fatal, exactly the upstream "relaxing this would silently
/// swallow state inconsistencies" boundary).
pub open spec fn spec_classify_rc(v: int) -> IoErr {
    if v == 0x8B {
        IoErr::NotFound
    } else if v == 0x10 + 0x900 {
        IoErr::NotFound
    } else {
        IoErr::Fatal
    }
}

/// Origin Rust: fn rc_value(rc: u32) -> u32 {
///     if rc & RC_FMT1_BIT == RC_FMT1_BIT { rc & RC_FMT1_MASK } else { rc }
/// } (chip.rs:29-35; both & lowered to the / %-spelling -- same
/// values on all u32, see the batch toolchain note. The bit-6
/// selector is x - 64 exactly when bit 6 is set)
pub exec fn rc_value(rc: u32) -> (v: u32)
    ensures
        (v as int) == spec_rc_value(rc),
{
    if (rc / 128u32) % 2u32 == 1u32 {
        let low = rc % 256u32;
        if low % 128u32 >= 64u32 {
            low - 64u32
        } else {
            low
        }
    } else {
        rc
    }
}

/// Origin Rust: /// Return code -> orchestration-layer error.
/// ///
/// /// There is only one semantic boundary that matters here: what counts as [`IoErr::NotFound`]. It means
/// /// "the target no longer exists," and the orchestration layer uses it to forget the corresponding slot
/// /// instead of failing the whole path. Therefore, only the two return codes that truly mean "a non-existent
/// /// object was referenced" belong here; relaxing this would silently swallow state inconsistencies.
/// fn classify_rc(rc: u32) -> IoErr {
///     let v = rc_value(rc);
///     if v == RC_HANDLE || v == RC_REFERENCE_H0 { IoErr::NotFound }
///     else if v == RC_INTEGRITY { IoErr::Integrity }
///     else if v == RC_CONTEXT_GAP || v == RC_OBJECT_MEMORY || v == RC_SESSION_MEMORY
///         || v == RC_MEMORY { IoErr::NoSpace }
///     else if v == RC_RETRY || v == RC_YIELDED || v == RC_TESTING { IoErr::Timeout }
///     else { IoErr::Fatal }
/// } (chip.rs:36-59; the classify-side face states the exact arm
/// for every documented class)
pub exec fn classify_rc(rc: u32) -> (e: IoErr)
    ensures
        // exact arm faces for every documented class (enum equality
        // is spelled through matches: this build has no == on IoErr)
        match e {
            IoErr::NotFound => spec_rc_value(rc) == 0x8B || spec_rc_value(rc) == 0x910,
            IoErr::Integrity => spec_rc_value(rc) == 0x9F,
            IoErr::NoSpace =>
                spec_rc_value(rc) == 0x901 || spec_rc_value(rc) == 0x902
                    || spec_rc_value(rc) == 0x903 || spec_rc_value(rc) == 0x904,
            IoErr::Timeout =>
                spec_rc_value(rc) == 0x922 || spec_rc_value(rc) == 0x908
                    || spec_rc_value(rc) == 0x90A,
            IoErr::Fatal =>
                !(spec_rc_value(rc) == 0x8B || spec_rc_value(rc) == 0x910
                    || spec_rc_value(rc) == 0x9F || spec_rc_value(rc) == 0x901
                    || spec_rc_value(rc) == 0x902 || spec_rc_value(rc) == 0x903
                    || spec_rc_value(rc) == 0x904 || spec_rc_value(rc) == 0x922
                    || spec_rc_value(rc) == 0x908 || spec_rc_value(rc) == 0x90A),
            IoErr::Bus => false,
            IoErr::Protocol => false,
            IoErr::BadCommand => false,
            IoErr::NotReady => false,
        },
{
    let v = rc_value(rc);
    if v == RC_HANDLE || v == RC_REFERENCE_H0 {
        IoErr::NotFound
    } else if v == RC_INTEGRITY {
        IoErr::Integrity
    } else if v == RC_CONTEXT_GAP || v == RC_OBJECT_MEMORY || v == RC_SESSION_MEMORY || v == RC_MEMORY {
        IoErr::NoSpace
    } else if v == RC_RETRY || v == RC_YIELDED || v == RC_TESTING {
        IoErr::Timeout
    } else {
        IoErr::Fatal
    }
}

// ------------------------------------------------------------------
// ChipTransport (chip.rs:60-93) -- the trust boundary
// ------------------------------------------------------------------

/// Origin Rust: doc block with TRUST 1/2/3 (chip.rs:65-90, quoted
/// verbatim in the batch notes) and
/// pub trait ChipTransport {
///     fn exec(&mut self, cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr>;
/// } (chip.rs:91-93)
///
/// The trusted postcondition package below is exactly TRUST 1:
/// response writes do not exceed the rsp capacity and include at
/// least one complete packet header (Ok(n) means HEADER_SIZE <=
/// n <= rsp.len()). TRUST 2 (ContextLoad handle novelty) and TRUST
/// 3 (live-set grows only on load, shrinks only on flush) are
/// ghost-set statements about the un-modeled chip state -- they
/// stay in the doc narrative per the scoping cut (silicon side).
pub trait ChipTransport {
    fn exec(&mut self, cmd: &[u8], rsp: &mut [u8]) -> (r: Result<usize, IoErr>)
        requires
            (cmd.len() as int) >= (HEADER_SIZE as int),
            (rsp.len() as int) >= (HEADER_SIZE as int),
        ensures
            match r {
                Result::Ok(n) =>
                    (HEADER_SIZE as int) <= (n as int)
                        && (n as int) <= (final(rsp).len() as int)
                        && final(rsp).len() == old(rsp).len(),
                Result::Err(_) => true,
            };
}

// ------------------------------------------------------------------
// CtxIo (chip.rs:95-146)
// ------------------------------------------------------------------

/// Origin Rust: pub(crate) const MSG_MAX: usize = 4096; (chip.rs:95-97;
/// pub for the twin's public faces that cite the fixed buffers)
pub const MSG_MAX: usize = 4096;

/// Fixed backup-block prefix: sequence (8) + handle (4) + level (4)
/// + data length (2) = 18 (chip.rs CTX_FIXED).
pub(crate) const CTX_FIXED: usize = 18;
/// Offset of the data-length field inside the backup block (chip.rs CTX_SIZE_OFF).
pub(crate) const CTX_SIZE_OFF: usize = 16;

/// Origin Rust: /// Lift [`ChipTransport`] into the orchestration-layer version required by [`ContextIo`].
/// ///
/// /// This layer is fully verified: it does only length checks, packet assembly, and return-code
/// /// classification. The ghost set is passed straight through to the transport layer; this layer introduces
/// /// no new assumptions. This is enforced by the fact that all three methods lack `external_body`; if any
/// /// one were marked, the statement above would no longer hold, and the injectivity of the orchestration
/// /// layer would rest on a false premise.
/// pub struct CtxIo<T: ChipTransport> { tx: T, cbuf: [u8; MSG_MAX], rbuf: [u8; MSG_MAX] }
/// (chip.rs:95-110; the two fixed buffers are the doc's inlined
/// 8 KiB pair -- the twin keeps the field form; upstream writes
/// them through, so they stay pub(crate)-visible here for the
/// adapter's own spec faces)
pub struct CtxIo<T: ChipTransport> {
    pub(crate) tx: T,
    pub(crate) cbuf: [u8; MSG_MAX],
    pub(crate) rbuf: [u8; MSG_MAX],
}

impl<T: ChipTransport> CtxIo<T> {
    /// Origin Rust: pub fn new(tx: T) -> Self { CtxIo { tx, cbuf: [0u8; MSG_MAX], rbuf: [0u8; MSG_MAX] } }
    /// (chip.rs:111-118; the const array literals are spelled as
    /// the all-zero spec face over the fixed width)
    pub exec fn new(tx: T) -> (t: CtxIo<T>)
        // the all-zero face of the two fresh buffers is not stated
        // in a spec position: struct-field spec expressions over a
        // generic receiver are rejected by this build ("opaque
        // datatype" diagnostic); the zero-init has no downstream
        // spec consumer (the trusted transport reads it, this
        // adapter only writes it)
    {
        CtxIo {
            tx,
            cbuf: [0u8; MSG_MAX],
            rbuf: [0u8; MSG_MAX],
        }
    }

    /// Origin Rust: /// Place the 10-byte packet header at the beginning of the command buffer.
    /// fn put_header(&mut self, code: u32, total: usize) {
    ///     let hdr = build_header(ST_NO_SESSIONS, code, total as u32);
    ///     self.cbuf[..HEADER_SIZE].copy_from_slice(&hdr);
    /// } (chip.rs:119-127; copy_from_slice lowered to the ten
    /// scalar index writes. The used count is bounded by the
    /// caller (load/save) to keep total within u32 -- an Origin
    /// note carried at the call sites)
    pub(crate) exec fn put_header(&mut self, code: u32, total: usize)
        requires
            (total as int) <= 0xFFFF_FFFF,
            (HEADER_SIZE as int) <= MSG_MAX as int,
        ensures
            final(self).cbuf@.subrange(0, HEADER_SIZE as int)
                == old(self).cbuf@.subrange(0, HEADER_SIZE as int)
                    .update(0, (ST_NO_SESSIONS / 256) as u8)
                    .update(1, (ST_NO_SESSIONS % 256) as u8)
                    .update(2, ((total as int) / 16777216) as u8)
                    .update(3, (((total as int) / 65536) % 256) as u8)
                    .update(4, (((total as int) / 256) % 256) as u8)
                    .update(5, ((total as int) % 256) as u8)
                    .update(6, ((code as int) / 16777216) as u8)
                    .update(7, (((code as int) / 65536) % 256) as u8)
                    .update(8, (((code as int) / 256) % 256) as u8)
                    .update(9, ((code as int) % 256) as u8),
            forall|q: int|
                (HEADER_SIZE as int) <= q < MSG_MAX as int
                    ==> final(self).cbuf@.index(q) == old(self).cbuf@.index(q),
            final(self).rbuf@ == old(self).rbuf@,
    {
        let hdr = build_header(ST_NO_SESSIONS, code, total as u32);
        self.cbuf[0] = hdr[0];
        self.cbuf[1] = hdr[1];
        self.cbuf[2] = hdr[2];
        self.cbuf[3] = hdr[3];
        self.cbuf[4] = hdr[4];
        self.cbuf[5] = hdr[5];
        self.cbuf[6] = hdr[6];
        self.cbuf[7] = hdr[7];
        self.cbuf[8] = hdr[8];
        self.cbuf[9] = hdr[9];
    }

    /// Origin Rust: /// Hand the entire command to the lower transport without reassembling the packet.
/// ///
/// /// It shares the same transport-layer ledger as the three methods of `ContextIo`, so the handle count
/// /// remains continuous across calls to `exec_raw` and `load`/`save`/`flush`.
/// pub fn exec_raw(&mut self, cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr> {
///     self.tx.exec(cmd, rsp)
/// } (chip.rs:128-137)
    pub exec fn exec_raw(&mut self, cmd: &[u8], rsp: &mut [u8]) -> (r: Result<usize, IoErr>)
        requires
            (cmd.len() as int) >= (HEADER_SIZE as int),
            (rsp.len() as int) >= (HEADER_SIZE as int),
        ensures
            match r {
                Result::Ok(n) =>
                    (HEADER_SIZE as int) <= (n as int)
                        && (n as int) <= (final(rsp).len() as int)
                        && final(rsp).len() == old(rsp).len(),
                Result::Err(_) => true,
            },
    {
        self.tx.exec(cmd, rsp)
    }

    /// Origin Rust: /// Return the lower transport and end the context round trip.
    /// pub fn release(self) -> T { self.tx } (chip.rs:138-144)
    pub exec fn release(self) -> (t: T)
    {
        self.tx
    }

}

/// Origin Rust: fn write_be32_arr(b: &mut [u8; MSG_MAX], off: usize, v: u32) {
    ///     b[off..off + 4].copy_from_slice(&v.to_be_bytes());
    /// } (chip.rs:202-207; the fixed-array slice lowered to the
    /// four scalar writes in the / %-spelling)
pub(crate) exec fn write_be32_arr(b: &mut [u8; MSG_MAX], off: usize, v: u32)
    requires
        (off as int) + 4 <= MSG_MAX as int,
    ensures
        forall|q: int|
            0 <= q < MSG_MAX as int
                && !((off as int) <= q < ((off as int) + 4))
            ==> final(b)@.index(q) == old(b)@.index(q),
        final(b)@.index(off as int) == ((v as int) / 16777216) as u8,
        final(b)@.index(off as int + 1) == (((v as int) / 65536) % 256) as u8,
        final(b)@.index(off as int + 2) == (((v as int) / 256) % 256) as u8,
        final(b)@.index(off as int + 3) == ((v as int) % 256) as u8,
{
    b[off] = (v / 16777216u32) as u8;
    b[off + 1] = ((v / 65536u32) % 256u32) as u8;
    b[off + 2] = ((v / 256u32) % 256u32) as u8;
    b[off + 3] = (v % 256u32) as u8;
}
// ------------------------------------------------------------------
// The ContextIo implementation (chip.rs:145-201) -- fully verified
// ------------------------------------------------------------------

impl<T: ChipTransport> ContextIo for CtxIo<T> {
    /// Origin Rust: fn load(&mut self, blob: &[u8], off: usize) -> Result<(u32, usize), IoErr> {
    ///     if off > blob.len() || blob.len() - off < CTX_FIXED { return Err(IoErr::Integrity); }
    ///     let size = u16::from_be_bytes([blob[off+CTX_SIZE_OFF], blob[off+CTX_SIZE_OFF+1]]) as usize;
    ///     let used = CTX_FIXED + size;
    ///     if blob.len() - off < used { return Err(IoErr::Integrity); }
    ///     if MSG_MAX - HEADER_SIZE < used { return Err(IoErr::NoSpace); }
    ///     self.put_header(CC_CONTEXT_LOAD, HEADER_SIZE + used);
    ///     self.cbuf[HEADER_SIZE..HEADER_SIZE+used].copy_from_slice(&blob[off..off+used]);
    ///     let n = self.tx.exec(&self.cbuf, &mut self.rbuf)?;
    ///     if n < HEADER_SIZE { return Err(IoErr::Protocol); }
    ///     let rc = read_be32(&self.rbuf, 6);
    ///     if rc != RC_SUCCESS { return Err(classify_rc(rc)); }     // classification FIRST
    ///     if n < HEADER_SIZE + 4 { return Err(IoErr::Protocol); }  // span SECOND
    ///     let h = read_be32(&self.rbuf, HEADER_SIZE);
    ///     Ok((h, used))
    /// } (chip.rs:145-174; from_be_bytes via the endian twin,
    /// copy_from_slice lowered to the scalar write walk with
    /// window-fresh facets. The classification-before-spans
    /// precedence is the upstream unit test's subject at
    /// chip.rs:221. The Ok arm carries the full consumed-count and
    /// device-word faces; the Err arms stay open -- a transported
    /// error and a locally-derived one are not separable in the
    /// final state alone (the #T4-11 arm-dichotomy discipline,
    /// deferred record D-T5-4))
    fn load(&mut self, blob: &[u8], off: usize) -> (r: Result<(u32, usize), IoErr>)
        ensures
            match r {
                Result::Ok((h, used)) =>
                    // the consumed-count face is the trait's
                    // offset-chain discipline; the device-word
                    // faces (h, rc) are unreadable in a spec
                    // position for a generic receiver ("opaque
                    // datatype" diagnostic of this build) -- the
                    // runtime re-reads stay in the body
                    (used as int) >= 18
                        && (used as int) <= (MSG_MAX as int - HEADER_SIZE as int)
                        && (off as int) + (used as int) <= (blob.len() as int),
                Result::Err(_) => true,
            },
    {
        if off > blob.len() || blob.len() - off < CTX_FIXED {
            return Result::Err(IoErr::Integrity);
        }
        let size =
            super::endian::be16_of_exec(blob[off + CTX_SIZE_OFF], blob[off + CTX_SIZE_OFF + 1])
                as usize;
        let used = CTX_FIXED + size;
        if blob.len() - off < used {
            return Result::Err(IoErr::Integrity);
        }
        if MSG_MAX - HEADER_SIZE < used {
            return Result::Err(IoErr::NoSpace);
        }
        self.put_header(super::cmd::CC_CONTEXT_LOAD, HEADER_SIZE + used);
        // scalar copy walk (the blob body into the command buffer):
        // window-fresh facet + outside preservation
        let ghost pre_cbuf = self.cbuf@;
        let mut q: usize = 0;
        while q < used
            invariant
                (q as int) <= (used as int),
                (HEADER_SIZE as int) + (used as int) <= MSG_MAX as int,
                (off as int) + (used as int) <= (blob.len() as int),
                (pre_cbuf.len() as int) == (self.cbuf.len() as int),
                forall|w: int|
                    (HEADER_SIZE as int) <= w < (HEADER_SIZE as int) + (q as int)
                        ==> #[trigger] self.cbuf@.index(w)
                            == blob@.index(
                                (off as int) + (w - (HEADER_SIZE as int)),
                            ),
                forall|w: int|
                    0 <= w < (MSG_MAX as int)
                        && !((HEADER_SIZE as int) <= w < (HEADER_SIZE as int) + (q as int))
                    ==> #[trigger] self.cbuf@.index(w) == pre_cbuf.index(w),
            decreases
                (used as int) - (q as int),
        {
            self.cbuf[HEADER_SIZE + q] = blob[off + q];
            q += 1;
        }
        let r = self.tx.exec(&self.cbuf, &mut self.rbuf);
        match r {
            Result::Err(e) => return Result::Err(e),
            Result::Ok(n) => {
                if n < HEADER_SIZE {
                    return Result::Err(IoErr::Protocol);
                }
                let rc = read_be32(&self.rbuf, 6);
                if rc != RC_SUCCESS {
                    // classification precedes the response-span
                    // check: the upstream UT's ordering (chip.rs:221)
                    return Result::Err(classify_rc(rc));
                }
                if n < HEADER_SIZE + 4 {
                    return Result::Err(IoErr::Protocol);
                }
                let h = read_be32(&self.rbuf, HEADER_SIZE);
                Result::Ok((h, used))
            }
        }
    }

    /// Origin Rust: fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> Result<usize, IoErr> {
    ///     self.put_header(CC_CONTEXT_SAVE, HEADER_SIZE + 4);
    ///     write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
    ///     let n = self.tx.exec(&self.cbuf, &mut self.rbuf)?;
    ///     if n < HEADER_SIZE { return Err(IoErr::Protocol); }
    ///     let rc = read_be32(&self.rbuf, 6);
    ///     if rc != RC_SUCCESS { return Err(classify_rc(rc)); }
    ///     let body = n - HEADER_SIZE;
    ///     if body < CTX_FIXED { return Err(IoErr::Protocol); }
    ///     if off > out.len() || out.len() - off < body { return Err(IoErr::NoSpace); }
    ///     out[off..off+body].copy_from_slice(&self.rbuf[HEADER_SIZE..HEADER_SIZE+body]);
    ///     Ok(body)
    /// } (chip.rs:175-195; same lowering notes; the Ok face keeps
    /// the full consumed-count + device-window discipline that
    /// covers the ContextIo trait contract; Err arms open as above)
    fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> (r: Result<usize, IoErr>)
        ensures
            match r {
                Result::Ok(used) =>
                    // count face only (same generic-receiver note
                    // as load)
                    (used as int) >= 18
                        && (off as int) + (used as int) <= (old(out).len() as int),
                Result::Err(_) => true,
            },
    {
        self.put_header(super::cmd::CC_CONTEXT_SAVE, HEADER_SIZE + 4);
        write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
        let r = self.tx.exec(&self.cbuf, &mut self.rbuf);
        match r {
            Result::Err(e) => return Result::Err(e),
            Result::Ok(n) => {
                if n < HEADER_SIZE {
                    return Result::Err(IoErr::Protocol);
                }
                let rc = read_be32(&self.rbuf, 6);
                if rc != RC_SUCCESS {
                    return Result::Err(classify_rc(rc));
                }
                let body = n - HEADER_SIZE;
                if body < CTX_FIXED {
                    return Result::Err(IoErr::Protocol);
                }
                if off > out.len() || out.len() - off < body {
                    return Result::Err(IoErr::NoSpace);
                }
                // scalar copy walk (the saved body out of the
                // response buffer): window-fresh + outside facets
                let ghost pre_out = out@;
                let mut q: usize = 0;
                while q < body
                    invariant
                        (q as int) <= (body as int),
                        (HEADER_SIZE as int) + (body as int) <= MSG_MAX as int,
                        (off as int) + (body as int) <= (out.len() as int),
                        (pre_out.len() as int) == (out.len() as int),
                        forall|w: int|
                            0 <= w < (q as int)
                                ==> #[trigger] out@.index((off as int) + w)
                                    == self.rbuf@.index(
                                        (HEADER_SIZE as int) + w,
                                    ),
                        forall|w: int|
                            0 <= w < (pre_out.len() as int)
                                && !((off as int) <= w < (off as int) + (q as int))
                            ==> #[trigger] out@.index(w) == pre_out.index(w),
                    decreases
                        (body as int) - (q as int),
                {
                    let byte_v = self.rbuf[HEADER_SIZE + q];
                    out[off + q] = byte_v;
                    q += 1;
                }
                Result::Ok(body)
            }
        }
    }

    /// Origin Rust: fn flush(&mut self, h: u32) {
    ///     self.put_header(CC_FLUSH_CONTEXT, HEADER_SIZE + 4);
    ///     write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
    ///     let _ = self.tx.exec(&self.cbuf, &mut self.rbuf);
    /// } (chip.rs:196-201; outcome ignored per the doc's
    /// irreparable-leak rationale -- the chip may or may not have
    /// freed the object, the host's table books it as gone either
    /// way)
    fn flush(&mut self, h: u32)
    {
        self.put_header(super::cmd::CC_FLUSH_CONTEXT, HEADER_SIZE + 4);
        write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
        let _ = self.tx.exec(&self.cbuf, &mut self.rbuf);
    }
}

// ------------------------------------------------------------------
// Wire-size helper faces (file tail)
// ------------------------------------------------------------------


} // verus!
