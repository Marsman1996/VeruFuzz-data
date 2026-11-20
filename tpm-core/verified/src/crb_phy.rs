//! tpm-core 0.1.4 CRB physical layer (src/crb_phy.rs) -- Verus
//! translation.
//!
//! Bank T3. This is the only contact surface between CRB and the
//! hardware; the runtime semantics are guaranteed by the concrete
//! backend implementation (upstream header comment, src/crb_phy.rs:3-8).
//! The trait below re-erects exactly that trust statement as spec
//! faces: the register reads/writes and the buffer moves are declared
//! with the pre/postconditions the driver side consumes, and the
//! concrete backends inherit the proof obligations. The register
//! value faces are left fully opaque (device-controlled); the one
//! load-bearing postcondition is the response-buffer window face of
//! read_rsp -- bytes outside the requested span are untouched and the
//! slice length is preserved -- which the recv framing weld needs.
//! Per the batch scoping cut the IO bodies themselves are not
//! formalized (trusted stub surface; never an obligation site).

use vstd::prelude::*;

verus! {

use crate::crb::{CrbErr, CMD_BUF_CAP, RSP_BUF_CAP};

// ===================================================================
// Physical layer: trust boundary (src/crb_phy.rs:10-41)
// ===================================================================

/// Origin Rust: pub trait CrbPhy { ... } (src/crb_phy.rs:10-41; the
/// method set is verbatim, with the doc lines moved into the spec
/// faces as noted per method).
pub trait CrbPhy {
    // ------------------------------------------------------------------
    // Control registers (src/crb_phy.rs:15-17)
    // ------------------------------------------------------------------

    /// Origin Rust: fn read32(&mut self, reg: u32) -> Result<u32, CrbErr>;
    /// (src/crb_phy.rs:15) Hard-register read; the value face is
    /// device-controlled and stays opaque (Phy/Timeout/... error
    /// variants propagate as-is).
    fn read32(&mut self, reg: u32) -> (r: Result<u32, CrbErr>);

    /// Origin Rust: fn write32(&mut self, reg: u32, value: u32) -> Result<(), CrbErr>;
    /// (src/crb_phy.rs:16) Hard-register write; outcome error variants
    /// propagate as-is.
    fn write32(&mut self, reg: u32, value: u32) -> (r: Result<(), CrbErr>);

    // ------------------------------------------------------------------
    // Command buffer (src/crb_phy.rs:23-27)
    // ------------------------------------------------------------------

    /// Origin Rust: /// Write the entire `data[0..n]` block into the command buffer header area.
    /// fn write_cmd(&mut self, data: &[u8], n: usize) -> Result<(), CrbErr>;
    /// (src/crb_phy.rs:24) The doc's span wording is the precondition:
    /// the caller hands over the block [0, n) of data, so n is at
    /// most the slice length (README Kernel/Platform Contract item 4,
    /// the write-side bound).
    fn write_cmd(&mut self, data: &[u8], n: usize) -> (r: Result<(), CrbErr>)
        requires
            (n as int) <= (data.len() as int);

    /// Origin Rust: /// Barrier: ensure the command-buffer write is visible to the device before START.
    /// fn fence(&mut self); (src/crb_phy.rs:27) Barrier semantics --
    /// ordering only, no observable state face.
    fn fence(&mut self);

    // ------------------------------------------------------------------
    // Response buffer (src/crb_phy.rs:33-34)
    // ------------------------------------------------------------------

    /// Origin Rust: /// Read `n` bytes from the response buffer at offset `off` into `out[off..off + n]`.
    /// fn read_rsp(&mut self, off: usize, out: &mut [u8], n: usize) -> Result<(), CrbErr>;
    /// (src/crb_phy.rs:34) The doc's wording is re-erected as the
    /// window face: exactly the span [off, off + n) receives response
    /// bytes, the rest of the buffer is left byte-identical, the
    /// slice length is preserved (README contract item 4, the
    /// read-side bound `off + n <= out.len()`).
    fn read_rsp(
        &mut self,
        off: usize,
        out: &mut [u8],
        n: usize,
    ) -> (r: Result<(), CrbErr>)
        requires
            (off as int) + (n as int) <= (out.len() as int),
        ensures
            (final(out)@.len() as int) == (old(out)@.len() as int),
            r.is_Ok() ==> forall|i: int|
                0 <= i < (old(out)@.len() as int)
                    && ((i < (off as int)) || (i >= (off as int) + (n as int)))
                ==> (final(out)@.index(i) as int) == (old(out)@.index(i) as int);

    // ------------------------------------------------------------------
    // Throttling (src/crb_phy.rs:40)
    // ------------------------------------------------------------------

    /// Origin Rust: fn delay(&mut self); (src/crb_phy.rs:40) README
    /// contract item 5: delay must eventually return; wall-clock time
    /// is outside the model, the polling budget is the only measure.
    fn delay(&mut self);
}

// ===================================================================
// Pure span checks (src/crb_phy.rs:43-60)
// ===================================================================

/// Origin Rust: #[inline]
/// pub(crate) fn check_cmd_bounds(data: &[u8], n: usize) -> Result<(), CrbErr> {
///     if n > data.len() || n > CMD_BUF_CAP { Err(CrbErr::BadLength) } else { Ok(()) }
/// } (src/crb_phy.rs:43-50) Exact span face: acceptance holds iff the
/// requested block fits both the caller slice and the static command
/// buffer cap.
pub(crate) exec fn check_cmd_bounds(data: &[u8], n: usize) -> (r: Result<(), CrbErr>)
    ensures
        r.is_Ok()
            == ((n as int) <= (data.len() as int) && (n as int) <= (CMD_BUF_CAP as int)),
        r.is_Err() ==> r == Result::Err(CrbErr::BadLength),
{
    if n > data.len() || n > CMD_BUF_CAP {
        Result::Err(CrbErr::BadLength)
    } else {
        Result::Ok(())
    }
}

/// Origin Rust: #[inline]
/// pub(crate) fn check_rsp_bounds(off: usize, out_len: usize, n: usize) -> Result<(), CrbErr> {
///     let end = off.checked_add(n).ok_or(CrbErr::BadLength)?;
///     if end > out_len || end > RSP_BUF_CAP { Err(CrbErr::BadLength) } else { Ok(()) }
/// } (src/crb_phy.rs:52-60; the ok_or + ? chain is lowered to a match
/// arm of the same Option semantics; the checked_add overflow case is
/// spelled as the explicit usize bound test, same reject class).
/// Exact span face: acceptance holds iff the response block end
/// (offset + count, in the unbounded view, so the overflowing sum is
/// rejected automatically) fits both the caller buffer and the static
/// response cap.
pub(crate) exec fn check_rsp_bounds(
    off: usize,
    out_len: usize,
    n: usize,
) -> (r: Result<(), CrbErr>)
    ensures
        r.is_Ok()
            == (((off as int) + (n as int)) <= (out_len as int)
                && ((off as int) + (n as int)) <= (RSP_BUF_CAP as int)),
        r.is_Err() ==> r == Result::Err(CrbErr::BadLength),
{
    if off > usize::MAX - n {
        return Result::Err(CrbErr::BadLength);
    }
    let end = off + n;
    if end > out_len || end > RSP_BUF_CAP {
        Result::Err(CrbErr::BadLength)
    } else {
        Result::Ok(())
    }
}

} // verus!
