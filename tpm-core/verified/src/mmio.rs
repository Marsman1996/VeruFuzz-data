//! tpm-core 0.1.4 memory-mapped TIS backend (src/mmio.rs) -- Verus
//! translation.
//!
//! Upstream face: the register read/write loop drivers over a
//! byte-granular bus trait (src/mmio.rs:1-61). The panic faces
//! documented on read_fifo/write_fifo ("Panics if off + n > len",
//! the raw panic claim of the README platform contract) are the
//! verified targets here: under the trait's off + n <= len
//! precondition both FIFO loops run slice accesses that stay inside
//! the slice, and they maintain the destination-correctness face of
//! the TisPhy contract on every path, including early bus errors.

use vstd::prelude::*;

verus!{

use super::phy::TisPhy;
use super::tis::TisErr;

/// Origin Rust: pub trait TisMmioBackend {
///     fn read8(&mut self, addr: u32) -> Result<u8, TisErr>;
///     fn read32(&mut self, addr: u32) -> Result<u32, TisErr>;
///     fn write8(&mut self, addr: u32, value: u8) -> Result<(), TisErr>;
///     fn write32(&mut self, addr: u32, value: u32) -> Result<(), TisErr>;
/// } (mmio.rs:3-8; the trusted platform bus: register semantics live
/// in silicon and platform glue, so this trait declares them without
/// contract bodies -- the verification boundary of the scoping cut)
pub trait TisMmioBackend {
    fn read8(&mut self, addr: u32) -> (r: Result<u8, TisErr>);

    fn read32(&mut self, addr: u32) -> (r: Result<u32, TisErr>);

    fn write8(&mut self, addr: u32, value: u8) -> (r: Result<(), TisErr>);

    fn write32(&mut self, addr: u32, value: u32) -> (r: Result<(), TisErr>);
}

/// Origin Rust: pub struct TisMmio<B: TisMmioBackend> {
///     backend: B,
///     /// Number of idle spin-loop iterations per [`TisPhy::delay`] call. This is not a duration; the
///     /// actual interval depends on the host CPU frequency.
///     spin: u32,
/// } (mmio.rs:10-14)
pub struct TisMmio<B: TisMmioBackend> {
    pub backend: B,
    /// Number of idle spin-loop iterations per [`TisPhy::delay`] call. This is not a duration; the
    /// actual interval depends on the host CPU frequency.
    pub spin: u32,
}

impl<B: TisMmioBackend> TisMmio<B> {
    /// Origin Rust: pub fn new(backend: B, spin: u32) -> Self {
    ///     TisMmio { backend, spin }
    /// } (mmio.rs:16-19)
    /// (Fields upstream-private `backend`/`spin`: the public `new`
    /// contract talks about the spin count, so the twin opens the
    /// field visibility -- runtime face unchanged.)
    pub exec fn new(backend: B, spin: u32) -> (m: TisMmio<B>)
        ensures
            m.spin == spin,
    {
        TisMmio { backend, spin }
    }
}

/// Origin Rust: impl<B: TisMmioBackend> TisPhy for TisMmio<B> { ... }
/// (mmio.rs:20-61; the whole impl is the verified target -- the FIFO
/// loops prove the TisPhy destination-correctness contract, and the
/// register methods pass through. `u32::from_le` / `value.to_le` are
/// identity on little-endian targets, which is the MMIO endianness
/// the README platform contract documents ("MMIO little-endian
/// behavior"), so they are lowered to plain moves.)
impl<B: TisMmioBackend> TisPhy for TisMmio<B> {
    /// Origin Rust: fn read8(&mut self, addr: u32) -> Result<u8, TisErr> {
    ///     self.backend.read8(addr)
    /// } (mmio.rs:21-23)
    fn read8(&mut self, addr: u32) -> (r: Result<u8, TisErr>) {
        self.backend.read8(addr)
    }

    /// Origin Rust: fn read32(&mut self, addr: u32) -> Result<u32, TisErr> {
    ///     let v = self.backend.read32(addr)?;
    ///     Ok(u32::from_le(v))
    /// } (mmio.rs:24-27; ? lowered to a match of the same semantics,
    /// from_le lowered to identity on this little-endian target)
    fn read32(&mut self, addr: u32) -> (r: Result<u32, TisErr>) {
        match self.backend.read32(addr) {
            Result::Ok(v) => Result::Ok(v),
            Result::Err(e) => Result::Err(e),
        }
    }

    /// Origin Rust: fn write8(&mut self, addr: u32, value: u8) -> Result<(), TisErr> {
    ///     self.backend.write8(addr, value)
    /// } (mmio.rs:28-30)
    fn write8(&mut self, addr: u32, value: u8) -> (r: Result<(), TisErr>) {
        self.backend.write8(addr, value)
    }

    /// Origin Rust: fn write32(&mut self, addr: u32, value: u32) -> Result<(), TisErr> {
    ///     self.backend.write32(addr, value.to_le())
    /// } (mmio.rs:31-33; to_le lowered to identity on this
    /// little-endian target)
    fn write32(&mut self, addr: u32, value: u32) -> (r: Result<(), TisErr>) {
        self.backend.write32(addr, value)
    }

    /// Origin Rust: /// # Panics
    /// ///
    /// /// Panics if `off + n > out.len()`.
    /// fn read_fifo(&mut self, addr: u32, out: &mut [u8], off: usize, n: usize) -> Result<(), TisErr> {
    ///     for slot in &mut out[off..off + n] {
    ///         *slot = self.backend.read8(addr)?;
    ///     }
    ///     Ok(())
    /// } (mmio.rs:34-42; the iterator loop is lowered to the explicit
    /// index walk, and the early ? return stays an explicit error
    /// return -- the panic face holds under the trait precondition,
    /// so the twin discharges it as index bounds)
    fn read_fifo(&mut self, addr: u32, out: &mut [u8], off: usize, n: usize)
        -> (r: Result<(), TisErr>)
    {
        let ghost pre = out@;
        assert(pre.len() == out.len() as int);
        let mut i: usize = off;
        let end: usize = off + n;
        while i < end
            invariant
                (off as int) <= (i as int),
                (i as int) <= (end as int),
                end == off + n,
                (off as int) + (n as int) <= out.len() as int,
                out.len() == pre.len(),
                forall|j: int|
                    0 <= j < pre.len() && !((off as int) <= j < (i as int))
                    ==> out@.index(j) == pre.index(j),
            decreases
                (end as int) - (i as int),
        {
            match self.backend.read8(addr) {
                Result::Ok(v) => {
                    out[i] = v;
                    assert forall|j: int|
                        0 <= j < pre.len() && !((off as int) <= j < (i as int + 1))
                        implies out@.index(j) == pre.index(j)
                    by {
                        // byte j == i is the fresh read; every other
                        // surviving index keeps the loop-invariant face
                    }
                    i = i + 1;
                }
                Result::Err(e) => return Result::Err(e),
            }
        }
        Result::Ok(())
    }

    /// Origin Rust: /// # Panics
    /// ///
    /// /// Panics if `off + n > data.len()`.
    /// fn write_fifo(&mut self, addr: u32, data: &[u8], off: usize, n: usize) -> Result<(), TisErr> {
    ///     for &byte in &data[off..off + n] {
    ///         self.backend.write8(addr, byte)?;
    ///     }
    ///     Ok(())
    /// } (mmio.rs:43-51; lowered to the explicit index walk)
    fn write_fifo(&mut self, addr: u32, data: &[u8], off: usize, n: usize)
        -> (r: Result<(), TisErr>)
    {
        let mut i: usize = off;
        let end: usize = off + n;
        while i < end
            invariant
                (off as int) <= (i as int),
                (i as int) <= (end as int),
                end == off + n,
                (off as int) + (n as int) <= data.len() as int,
            decreases
                (end as int) - (i as int),
        {
            match self.backend.write8(addr, data[i]) {
                Result::Ok(()) => i = i + 1,
                Result::Err(e) => return Result::Err(e),
            }
        }
        Result::Ok(())
    }

    /// Origin Rust: /// Write `TPM_STS_COMMAND_READY` (0x40).
    /// fn reset_fifo(&mut self, addr: u32) {
    ///     let _ = self.backend.write8(addr, 0x40u8);
    /// } (mmio.rs:52-55)
    fn reset_fifo(&mut self, addr: u32) {
        let _ = self.backend.write8(addr, 0x40u8);
    }

    /// Origin Rust: fn delay(&mut self) {
    ///     for _ in 0..self.spin {
    ///         core::hint::spin_loop();
    ///     }
    /// } (mmio.rs:56-60; the spin_loop intrinsic is a CPU hint with no
    /// observable semantics, so the twin keeps the count loop and
    /// elides the single hint instruction)
    fn delay(&mut self) {
        let mut i: u32 = 0;
        while i < self.spin
            invariant
                (i as int) <= (self.spin as int),
            decreases
                (self.spin as int) - (i as int),
        {
            i = i + 1;
        }
    }
}

} // verus!
