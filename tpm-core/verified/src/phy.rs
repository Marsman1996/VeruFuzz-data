//! tpm-core 0.1.4 TIS physical-layer trait (src/phy.rs) -- Verus
//! translation.
//!
//! This trait is the trust boundary of the TIS stack (the scoping
//! cut): implementations live in platform glue outside the crate, so
//! the twin carries the CONTRACT only -- each FIFO method moves bytes
//! strictly inside the [off, off+n) window and leaves everything
//! outside untouched, exactly what the upstream doc lines promise.
//! Register, FIFO, and timing bodies are not transcribed; the
//! driver-side arithmetic that calls them is (src/tis_core.rs).

use vstd::prelude::*;

verus!{

use super::tis::TisErr;

/// Origin Rust: pub trait TisPhy {
///     fn read8(&mut self, addr: u32) -> Result<u8, TisErr>;
///     fn read32(&mut self, addr: u32) -> Result<u32, TisErr>;
///     fn write8(&mut self, addr: u32, value: u8) -> Result<(), TisErr>;
///     fn write32(&mut self, addr: u32, value: u32) -> Result<(), TisErr>; (phy.rs:3-8)
pub trait TisPhy {
    fn read8(&mut self, addr: u32) -> (r: Result<u8, TisErr>);

    fn read32(&mut self, addr: u32) -> (r: Result<u32, TisErr>);

    fn write8(&mut self, addr: u32, value: u8) -> (r: Result<(), TisErr>);

    fn write32(&mut self, addr: u32, value: u32) -> (r: Result<(), TisErr>);

    /// Origin Rust: /// Read `n` bytes from the data FIFO into `out[off..off + n]`.
    /// ///
    /// /// The bytes come from the device, and the specification does not say what they are; it only
    /// /// guarantees that the destination is correct: bytes outside the range remain untouched and the buffer
    /// /// length is unchanged. Therefore the caller bears the responsibility to ensure `off + n <= out.len()`,
    /// /// and that is enforced by type checking.
    /// ///
    /// /// # Panics
    /// ///
    /// /// Implementations may panic if `off + n > out.len()`.
    /// fn read_fifo(&mut self, addr: u32, out: &mut [u8], off: usize, n: usize) -> Result<(), TisErr>;
    ///     (phy.rs:10-18; the doc's "enforced by type checking" phrase
    ///     here reads as the caller-side proof obligation below -- the
    ///     pointer types alone do not enforce it, the twin makes it a
    ///     hard requires)
    fn read_fifo(&mut self, addr: u32, out: &mut [u8], off: usize, n: usize)
        -> (r: Result<(), TisErr>)
        requires
            (off as int) + (n as int) <= out.len() as int,
        ensures
            r == Result::Ok(())
                ==> final(out).len() == old(out).len()
                    && forall|i: int|
                        0 <= i < old(out)@.len()
                            && !((off as int) <= i < ((off + n) as int))
                        ==> final(out)@.index(i) == old(out)@.index(i),
    ;

    /// Origin Rust: /// Write `data[off..off + n]` into the data FIFO.
    /// ///
    /// /// On failure, the device may already have consumed a prefix -- bus transmission is not atomic. The
    /// /// specification writes this as "the accumulated count only increases" rather than "the data remains
    /// /// unchanged": the latter is false, and pretending otherwise invalidates all reasoning built on it.
    /// /// The caller must reset the FIFO on any failure path; after reset, the inexactness of this point is
    /// /// irrelevant.
    /// ///
    /// /// # Panics
    /// ///
    /// /// Implementations may panic if `off + n > data.len()`.
    /// fn write_fifo(&mut self, addr: u32, data: &[u8], off: usize, n: usize) -> Result<(), TisErr>;
    ///     (phy.rs:20-30; `data` is immutable, so the byte source face
    ///     is total; the "accumulated count only increases" sentence
    ///     is device-side state, not modeled here -- the driver-side
    ///     discipline (reset on failure) is carried in the callers)
    fn write_fifo(&mut self, addr: u32, data: &[u8], off: usize, n: usize)
        -> (r: Result<(), TisErr>)
        requires
            (off as int) + (n as int) <= data.len() as int,
    ;

    /// Origin Rust: /// Abort the current command and clear the data FIFO.
    /// ///
    /// /// This corresponds to writing the "command ready" bit. It is both the preparation action before
    /// /// sending and the cleanup action for every error path -- leaving half a command in the device is more
    /// /// dangerous than writing nothing at all.
    /// ///
    /// /// There is no return value: reset failure is unrecoverable, and all call sites are already on error
    /// /// handling paths; adding one more error to handle only makes those paths easier to miss.
    /// fn reset_fifo(&mut self, addr: u32); (phy.rs:31-39)
    fn reset_fifo(&mut self, addr: u32);

    /// Origin Rust: /// Wait between two polling iterations.
    /// ///
    /// /// The duration is implementation-defined and not present in the specification -- this layer models
    /// /// timeouts in terms of polling counts, and the actual waiting time only affects wall-clock latency, not
    /// /// any proven property.
    /// fn delay(&mut self); (phy.rs:40-45)
    fn delay(&mut self);
}

} // verus!
