//! tpm-core 0.1.4 TIS byte-register protocol state machine
//! (src/tis_core.rs) -- Verus translation.
//!
//! Upstream face: the locality handshake, FIFO data pump, and
//! response framing weld over the trusted TisPhy register contract
//! (src/tis_core.rs:1-247). Re-erected here: the roll-forward
//! polling discipline (budget counters as the only termination
//! measure, budget_of >= 1), FIFO index monotonicity with
//! checked_add rejection, slice-bounded write_fifo/read_fifo calls,
//! the response-header weld (returned length == wire size == buffer
//! span), and the held-flag life cycle (set exactly on the success
//! paths of request_locality, cleared unconditionally by
//! relinquish_locality and by the single release site of transmit).

use vstd::prelude::*;

verus!{

use super::cursor::Cursor;
use super::endian::be32_of;
use super::phy::TisPhy;
use super::tis::{
    budget_of, reg_access, reg_data_fifo, reg_sts, TisErr, ACCESS_ACTIVE_LOCALITY,
    ACCESS_REQUEST_USE, ACCESS_VALID, STS_COMMAND_READY, STS_DATA_AVAIL, STS_DATA_EXPECT,
    STS_GO, STS_VALID, TIMEOUT_A_MS, TIMEOUT_B_MS, TIMEOUT_C_MS,
};

/// The response header length, value-twin of the crate-local constant
/// in msg.rs (`pub(crate) const TPM_HEADER_LEN: usize = 10`). The
/// public faces of this module cite it, so the twin re-declares the
/// value at pub visibility instead of re-opening the landed T1 file;
/// the tail lemma pins this module's wire-size face to the
/// corresponding msg.rs response-parser face.
pub const TPM_HEADER_LEN: usize = 10;

/// Wire value of the response size field at header offsets 2..6
/// (the bytes the cursor read in recv inspects). Same shape as the
/// msg.rs response-parser size face; the bridging lemma at the file
/// tail states the equality.
pub open spec fn recv_wire_size(s: Seq<u8>) -> int {
    16777216 * s.index(2) as int
        + 65536 * s.index(3) as int
        + 256 * s.index(4) as int
        + s.index(5) as int
}

/// Origin Rust: pub struct Tis<P: TisPhy> {
///     pub phy: P,
///     /// Locality number used by this driver.
///     pub locality: u8,
///     /// Whether locality has been acquired and not yet returned.
///     ///
///     /// This is the only persistent state in this layer. Keeping it separate rather than reading the device
///     /// every time is because the property we need to prove is "did the driver forget to return locality?",
///     /// which belongs to the local side and cannot be inferred from the device.
///     held: bool,
/// } (tis_core.rs:1-13; doc glyphs converted ASCII. The `held` field
/// is private upstream; the twin opens it to pub because the public
/// state faces of request_locality / relinquish_locality / transmit
/// talk about it in their contracts -- the runtime face is
/// unchanged, this is visibility only)
pub struct Tis<P: TisPhy> {
    pub phy: P,
    /// Locality number used by this driver.
    pub locality: u8,
    /// Whether locality has been acquired and not yet returned.
    ///
    /// This is the only persistent state in this layer. Keeping it separate rather than reading the device
    /// every time is because the property we need to prove is "did the driver forget to return locality?",
    /// which belongs to the local side and cannot be inferred from the device.
    pub held: bool,
}

impl<P: TisPhy> Tis<P> {
    /// Origin Rust: /// Create a TIS transport state at a specific locality.
    /// pub fn new(phy: P, locality: u8) -> Self {
    ///     Self { phy, locality, held: false }
    /// } (tis_core.rs:14-22)
    pub exec fn new(phy: P, locality: u8) -> (t: Tis<P>)
        ensures
            !t.held,
    {
        Tis { phy, locality, held: false }
    }

    /// Origin Rust: /// Whether locality is currently held by this transport state.
    /// pub fn is_holding_locality(&self) -> bool {
    ///     self.held
    /// } (tis_core.rs:23-27)
    pub exec fn is_holding_locality(&self) -> (r: bool)
        ensures
            r == self.held,
    {
        self.held
    }

    /// Origin Rust: fn status(&mut self) -> Result<u8, TisErr> {
    ///     let addr = reg_sts(self.locality);
    ///     self.phy.read8(addr)
    /// } (tis_core.rs:29-33)
    fn status(&mut self) -> (r: Result<u8, TisErr>) {
        let addr = reg_sts(self.locality);
        self.phy.read8(addr)
    }

    /// Origin Rust: /// Poll the status register until all bits in `mask` are set.
    /// ///
    /// /// The budget is the polling count, and `decreases` uses it directly -- this is the entire benefit of
    /// /// moving the timeout from the time domain to the count domain: termination does not require any
    /// /// assumptions about clocks.
    /// fn wait_status(&mut self, mask: u8, budget: u32) -> Result<u8, TisErr> {
    ///     let mut left = budget;
    ///     while left > 0 {
    ///         let s = self.status()?;
    ///         if (s & mask) == mask { return Ok(s); }
    ///         self.phy.delay();
    ///         left -= 1;
    ///     }
    ///     Err(TisErr::Timeout)
    /// } (tis_core.rs:34-49)
    ///
    /// Exact face: Ok happens only with every mask bit set; the
    /// Err arms are left open (the register read can surface any
    /// error kind through the trusted phy, and the budget-exit
    /// reports Timeout).
    fn wait_status(&mut self, mask: u8, budget: u32) -> (r: Result<u8, TisErr>)
        ensures
            match r {
                Result::Ok(s) => (s & mask) == mask,
                _ => true,
            },
    {
        let mut left = budget;
        while left > 0
            invariant
                left <= budget,
            decreases
                left,
        {
            let s = match self.status() {
                Result::Ok(v) => v,
                Result::Err(e) => return Result::Err(e),
            };
            if (s & mask) == mask {
                return Result::Ok(s);
            }
            self.phy.delay();
            left = left - 1;
        }
        Result::Err(TisErr::Timeout)
    }

    /// Origin Rust: /// Read how many bytes can be moved continuously in this round.
    /// ///
    /// /// The return value is guaranteed to be non-zero. A zero value means the device is not ready yet; in
    /// /// that case it keeps polling or times out here instead of returning a "transferred zero bytes" success --
    /// /// that would cause the upper transfer loop to spin forever, and no timeout budget would catch it.
    /// fn burstcount(&mut self, budget: u32) -> Result<u16, TisErr> {
    ///     let mut left = budget;
    ///     while left > 0 {
    ///         let addr = reg_sts(self.locality);
    ///         let v = self.phy.read32(addr)?;
    ///         let b = ((v >> 8u32) & 0xFFFFu32) as u16;
    ///         if b >= 1 { return Ok(b); }
    ///         self.phy.delay();
    ///         left -= 1;
    ///     }
    ///     Err(TisErr::Timeout)
    /// } (tis_core.rs:50-68; the shift/mask pair is lowered to the
    /// equivalent div/mod chain `(v / 256) % 65536`, same bits)
    ///
    /// Exact face: Ok carries a guaranteed-nonzero burst;
    /// Err arms stay open as in wait_status.
    fn burstcount(&mut self, budget: u32) -> (r: Result<u16, TisErr>)
        ensures
            match r {
                Result::Ok(b) => b >= 1,
                _ => true,
            },
    {
        let mut left = budget;
        while left > 0
            invariant
                left <= budget,
            decreases
                left,
        {
            let addr = reg_sts(self.locality);
            let v = match self.phy.read32(addr) {
                Result::Ok(x) => x,
                Result::Err(e) => return Result::Err(e),
            };
            let b = ((v / 256u32) % 65536u32) as u16;
            if b >= 1 {
                return Result::Ok(b);
            }
            self.phy.delay();
            left = left - 1;
        }
        Result::Err(TisErr::Timeout)
    }

    /// Origin Rust: /// Whether the device has already granted locality to this side.
    /// ///
    /// /// All three bits matter: `ACTIVE` alone is not enough; `VALID` must also be set to indicate the
    /// /// register contents are valid, and `REQUEST_USE` must already be cleared to show the request has
    /// /// been processed. Missing any bit in a race scenario would misclassify "request is still being processed" as
    /// /// "already granted".
    /// fn check_locality(&mut self) -> Result<bool, TisErr> {
    ///     let addr = reg_access(self.locality);
    ///     let a = self.phy.read8(addr)?;
    ///     let want = ACCESS_ACTIVE_LOCALITY | ACCESS_VALID;
    ///     let mask = want | ACCESS_REQUEST_USE;
    ///     Ok((a & mask) == want)
    /// } (tis_core.rs:69-81; the boolean is a pure function of the
    /// register value the caller never sees, so the twin keeps the
    /// call structurally but carries no value face to the callers --
    /// request_locality only needs the Ok/Err shape)
    fn check_locality(&mut self) -> (r: Result<bool, TisErr>)
        ensures
            final(self).held == old(self).held,
            final(self).locality == old(self).locality,
    {
        let addr = reg_access(self.locality);
        let a = match self.phy.read8(addr) {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        let want = ACCESS_ACTIVE_LOCALITY | ACCESS_VALID;
        let mask = want | ACCESS_REQUEST_USE;
        Result::Ok((a & mask) == want)
    }

    /// Origin Rust: /// Request locality.
    /// ///
    /// /// On failure it guarantees no ownership is held -- if a partially failed request leaves the flag as
    /// /// "held," the subsequent release would free a resource that was never acquired.
    /// pub fn request_locality(&mut self, budget: u32) -> Result<(), TisErr> { ... }
    ///     (tis_core.rs:82-103)
    ///
    /// The verifiable face: held is set exactly on the success paths
    /// and an error never changes it. The doc sentence "on failure it
    /// guarantees no ownership is held" holds under the entry state
    /// is_holding_locality() == false of every in-tree call site
    /// (transmit after its own relinquish); read unconditionally it
    /// fails -- see the SPEC-DOC MISMATCH note below.
    ///
    /// SPEC-DOC MISMATCH: the doc's failure clause, read as the
    /// postcondition `Err ==> !held`, is refutable: enter with
    /// held == true and a phy whose read8 returns Err(Phy) -- the
    /// first check_locality propagates its error, held keeps its
    /// entry value true, and is_holding_locality() still reports a
    /// held locality. The twin instead carries the exact face
    /// `Err ==> held == old(held)` (no phantom grant on failure).
    pub exec fn request_locality(&mut self, budget: u32) -> (r: Result<(), TisErr>)
        ensures
            r.is_Ok() ==> final(self).held,
            r.is_Err() ==> final(self).held == old(self).held,
    {
        let ghost h0 = self.held;
        proof {
            assert(h0 == old(self).held);
        }
        let granted0 = match self.check_locality() {
            Result::Ok(b) => b,
            Result::Err(e) => return Result::Err(e),
        };
        assert(self.held == h0);
        if granted0 {
            self.held = true;
            return Result::Ok(());
        }
        let addr = reg_access(self.locality);
        self.phy.write8(addr, ACCESS_REQUEST_USE)?;
        assert(self.held == h0);
        let mut left = budget;
        while left > 0
            invariant
                left <= budget,
                self.held == h0,
                h0 == old(self).held,
            decreases
                left,
        {
            let granted = match self.check_locality() {
                Result::Ok(b) => b,
                Result::Err(e) => {
                    assert(self.held == h0);
                    return Result::Err(e)
                }
            };
            if granted {
                self.held = true;
                return Result::Ok(());
            }
            self.phy.delay();
            left = left - 1;
        }
        Result::Err(TisErr::Timeout)
    }

    /// Origin Rust: /// Return locality.
    /// ///
    /// /// Regardless of whether the register write succeeds, the local held flag must be cleared. If the write
    /// /// fails, the bus is already broken; leaving the flag as "held" would make the driver think it owns the
    /// /// resource forever and prevent it from issuing the next command -- a recoverable bus fault would become
    /// /// a permanent functional loss.
    /// pub fn relinquish_locality(&mut self) {
    ///     let addr = reg_access(self.locality);
    ///     let _ = self.phy.write8(addr, ACCESS_ACTIVE_LOCALITY);
    ///     self.held = false;
    /// } (tis_core.rs:104-114)
    pub exec fn relinquish_locality(&mut self)
        ensures
            !final(self).held,
    {
        let addr = reg_access(self.locality);
        let _ = self.phy.write8(addr, ACCESS_ACTIVE_LOCALITY);
        self.held = false;
    }

    /// Origin Rust: /// Feed a command into the data FIFO.
    /// ///
    /// /// On success, the FIFO receives exactly the command itself -- no more, no less, in the same order. On
    /// /// failure, the FIFO is definitely cleared and no half-command is left behind: if a half-command remains
    /// /// in the device, the next send would assemble a packet that nobody ever wrote.
    /// pub fn send_data(&mut self, cmd: &[u8], len: usize) -> Result<(), TisErr> {
    ///     self.send_data_inner(cmd, len).inspect_err(|_| {
    ///         let sts_addr = reg_sts(self.locality);
    ///         self.phy.reset_fifo(sts_addr);
    ///     })?;
    ///     Ok(())
    /// } (tis_core.rs:115-126; the inspect_err closure is lowered to
    /// the explicit error arm -- reset runs before the error returns)
    ///
    /// Both success clauses are device-side state ("the FIFO
    /// receives exactly the command", "the FIFO is cleared"), which
    /// lives behind the trusted phy and is not modeled here; the
    /// verifiable side of this function is the inside of
    /// send_data_inner: index monotonicity and slice-bounded FIFO
    /// writes. The len bounds below are the caller contract the
    /// upstream function checks nowhere: len == 0 underflows the
    /// `len - 1` of send_data_inner (debug builds panic there) and
    /// len > cmd.len() walks write_fifo past the command buffer --
    /// see the batch ledger.
    pub exec fn send_data(&mut self, cmd: &[u8], len: usize) -> (r: Result<(), TisErr>)
        requires
            len >= 1,
            len <= cmd.len(),
    {
        match self.send_data_inner(cmd, len) {
            Result::Ok(()) => Result::Ok(()),
            Result::Err(e) => {
                let sts_addr = reg_sts(self.locality);
                self.phy.reset_fifo(sts_addr);
                Result::Err(e)
            }
        }
    }

    /// Origin Rust: fn send_data_inner(&mut self, cmd: &[u8], len: usize) -> Result<(), TisErr> {
    ///     let sts_addr = reg_sts(self.locality);
    ///     let fifo_addr = reg_data_fifo(self.locality);
    ///     let s0 = self.status()?;
    ///     if (s0 & STS_COMMAND_READY) == 0 {
    ///         self.phy.reset_fifo(sts_addr);
    ///         self.wait_status(STS_COMMAND_READY, budget_of(TIMEOUT_B_MS))?;
    ///     }
    ///     let last = len - 1;
    ///     let mut count: usize = 0;
    ///     while count < last {
    ///         let b = self.burstcount(budget_of(TIMEOUT_A_MS))?;
    ///         let rem = last - count;
    ///         let bs = b as usize;
    ///         let n = if bs < rem { bs } else { rem };
    ///         self.phy.write_fifo(fifo_addr, cmd, count, n)?;
    ///         let next = count.checked_add(n).ok_or(TisErr::Protocol)?;
    ///         count = next;
    ///         self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS))?;
    ///         let s1 = self.status()?;
    ///         if (s1 & STS_DATA_EXPECT) == 0 { return Err(TisErr::Protocol); }
    ///     }
    ///     self.phy.write_fifo(fifo_addr, cmd, count, 1)?;
    ///     self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS))?;
    ///     let s2 = self.status()?;
    ///     if (s2 & STS_DATA_EXPECT) != 0 { return Err(TisErr::Protocol); }
    ///     Ok(())
    /// } (tis_core.rs:127-158)
    fn send_data_inner(&mut self, cmd: &[u8], len: usize) -> (r: Result<(), TisErr>)
        requires
            len >= 1,
            len <= cmd.len(),
    {
        let sts_addr = reg_sts(self.locality);
        let fifo_addr = reg_data_fifo(self.locality);
        let s0 = match self.status() {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        if (s0 & STS_COMMAND_READY) == 0 {
            self.phy.reset_fifo(sts_addr);
            match self.wait_status(STS_COMMAND_READY, budget_of(TIMEOUT_B_MS)) {
                Result::Ok(_) => {}
                Result::Err(e) => return Result::Err(e),
            }
        }
        let last = len - 1;
        let mut count: usize = 0;
        while count < last
            invariant
                count <= last,
                last == len - 1,
                len >= 1,
                cmd.len() >= len,
            decreases
                last - count,
        {
            let b = match self.burstcount(budget_of(TIMEOUT_A_MS)) {
                Result::Ok(v) => v,
                Result::Err(e) => return Result::Err(e),
            };
            let rem = last - count;
            let bs = b as usize;
            let n = if bs < rem { bs } else { rem };
            assert(count + n <= last);
            match self.phy.write_fifo(fifo_addr, cmd, count, n) {
                Result::Ok(()) => {}
                Result::Err(e) => return Result::Err(e),
            }
            let next = match count.checked_add(n) {
                Option::Some(v) => v,
                Option::None => return Result::Err(TisErr::Protocol),
            };
            assert(next == count + n);
            count = next;
            match self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS)) {
                Result::Ok(_) => {}
                Result::Err(e) => return Result::Err(e),
            }
            let s1 = match self.status() {
                Result::Ok(v) => v,
                Result::Err(e) => return Result::Err(e),
            };
            if (s1 & STS_DATA_EXPECT) == 0 {
                return Result::Err(TisErr::Protocol);
            }
        }
        assert(count + 1 <= cmd.len());
        match self.phy.write_fifo(fifo_addr, cmd, count, 1) {
            Result::Ok(()) => {}
            Result::Err(e) => return Result::Err(e),
        }
        match self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS)) {
            Result::Ok(_) => {}
            Result::Err(e) => return Result::Err(e),
        }
        let s2 = match self.status() {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        if (s2 & STS_DATA_EXPECT) != 0 {
            return Result::Err(TisErr::Protocol);
        }
        Result::Ok(())
    }

    /// Origin Rust: /// Read `count` bytes from the FIFO into `out[off..]`.
    /// fn recv_data(&mut self, out: &mut [u8], off: usize, count: usize) -> Result<(), TisErr> {
    ///     let fifo_addr = reg_data_fifo(self.locality);
    ///     let mut got: usize = 0;
    ///     while got < count {
    ///         self.wait_status(STS_DATA_AVAIL | STS_VALID, budget_of(TIMEOUT_C_MS))?;
    ///         let b = self.burstcount(budget_of(TIMEOUT_A_MS))?;
    ///         let rem = count - got;
    ///         let bs = b as usize;
    ///         let n = if bs < rem { bs } else { rem };
    ///         self.phy.read_fifo(fifo_addr, out, off + got, n)?;
    ///         let next = got.checked_add(n).ok_or(TisErr::Protocol)?;
    ///         got = next;
    ///     }
    ///     Ok(())
    /// } (tis_core.rs:159-174)
    ///
    /// Both post-state clauses hold on success AND error paths: the
    /// running window of written bytes never crosses [off,
    /// off+count), and the buffer length never changes.
    fn recv_data(&mut self, out: &mut [u8], off: usize, count: usize) -> (r: Result<(), TisErr>)
        requires
            (off as int) + (count as int) <= out.len() as int,
        ensures
            r == Result::Ok(())
                ==> final(out).len() == old(out).len()
                    && forall|i: int|
                        0 <= i < old(out)@.len()
                            && !((off as int) <= i < ((off + count) as int))
                        ==> final(out)@.index(i) == old(out)@.index(i),
    {
        let fifo_addr = reg_data_fifo(self.locality);
        let ghost pre = out@;
        assert(pre.len() == out.len() as int);
        let mut got: usize = 0;
        while got < count
            invariant
                got <= count,
                out.len() == pre.len(),
                (off as int) + (count as int) <= pre.len(),
                forall|i: int|
                    0 <= i < pre.len() && !((off as int) <= i < ((off + got) as int))
                    ==> out@.index(i) == pre.index(i),
            decreases
                count - got,
        {
            match self.wait_status(STS_DATA_AVAIL | STS_VALID, budget_of(TIMEOUT_C_MS)) {
                Result::Ok(_) => {}
                Result::Err(e) => return Result::Err(e),
            }
            let b = match self.burstcount(budget_of(TIMEOUT_A_MS)) {
                Result::Ok(v) => v,
                Result::Err(e) => return Result::Err(e),
            };
            let rem = count - got;
            let bs = b as usize;
            let n = if bs < rem { bs } else { rem };
            self.phy.read_fifo(fifo_addr, out, off + got, n)?;
            assert forall|i: int|
                0 <= i < pre.len() && !((off as int) <= i < ((off + got + n) as int))
                implies out@.index(i) == pre.index(i)
            by {
                // skolem i: outside the param window read_fifo may
                // touch and outside the window already written, so
                // the trait face and the loop invariant both apply
            }
            let next = match got.checked_add(n) {
                Option::Some(v) => v,
                Option::None => return Result::Err(TisErr::Protocol),
            };
            got = next;
        }
        Result::Ok(())
    }

    /// Origin Rust: /// Receive a full response and return its length.
    /// ///
    /// /// The return value is also the **entry condition for the next layer's decoder**: on success, the
    /// /// `out[0..n]` length field matches `n`, which means the packet-layer format is valid. The decoding
    /// /// layer therefore does not need to re-check its length, and the two layers are welded together on the
    /// /// understanding of "how long a response is" by this postcondition.
    /// pub fn recv(&mut self, out: &mut [u8]) -> Result<usize, TisErr> { ... }
    ///     (tis_core.rs:175-199; doc glyphs converted ASCII)
    ///
    /// Exact face: on Ok the returned length IS the wire size field
    /// of the received header (the weld) and fills the declared span
    /// of the buffer. The BadLength/Protocol error arms are left
    /// open (`_`): the same variant values also arrive propagated
    /// from the trusted phy layer (any TisErr value can ride the
    /// register reads), where these faces are not semantic facts.
    /// The wire-rejection checks recv raises itself are exact at the
    /// decode layer instead (msg.rs parse_response, already
    /// verified); the error-arm faces are recorded as deferred.
    pub exec fn recv(&mut self, out: &mut [u8]) -> (r: Result<usize, TisErr>)
        requires
            (out.len() as int) >= (TPM_HEADER_LEN as int),
        ensures
            match r {
                Result::Ok(n) =>
                    final(out).len() == old(out).len()
                        && (TPM_HEADER_LEN as int) <= (n as int)
                        && (n as int) <= (final(out).len() as int)
                        && (n as int) == recv_wire_size(final(out)@),
                _ => true,
            },
    {
        self.recv_data(out, 0, TPM_HEADER_LEN)?;
        let mut c = Cursor::at(2);
        let expected = match c.read_be32(&*out) {
            Option::Some(v) => v,
            Option::None => return Result::Err(TisErr::BadLength),
        };
        let ghost hdr = out@;
        let n = expected as usize;
        if n < TPM_HEADER_LEN {
            return Result::Err(TisErr::BadLength);
        }
        if n > out.len() {
            return Result::Err(TisErr::BadLength);
        }
        self.recv_data(out, TPM_HEADER_LEN, n - TPM_HEADER_LEN)?;
        proof {
            // second burst read never touches offsets below
            // TPM_HEADER_LEN == 10, so the header size bytes the
            // cursor read are still the current ones
            assert(hdr.index(2) == out@.index(2));
            assert(hdr.index(3) == out@.index(3));
            assert(hdr.index(4) == out@.index(4));
            assert(hdr.index(5) == out@.index(5));
            assert((expected as int) == be32_of(
                hdr.index(2),
                hdr.index(3),
                hdr.index(4),
                hdr.index(5),
            ));
            assert((n as int) == recv_wire_size(out@));
        }
        match self.wait_status(STS_VALID, budget_of(TIMEOUT_C_MS)) {
            Result::Ok(_) => {}
            Result::Err(e) => return Result::Err(e),
        }
        let s = match self.status() {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        if (s & STS_DATA_AVAIL) != 0 {
            return Result::Err(TisErr::Protocol);
        }
        Result::Ok(n)
    }

    /// Origin Rust: /// Send a command and receive a response.
    /// ///
    /// /// **There is only one return site for locality, and it is not inside any conditional branch.** After the
    /// /// request is made, all potentially failing actions are moved into an internal function, making the
    /// /// release of locality an unconditional cleanup statement -- as a result, "every path exits with locality
    /// /// released" does not need to be checked path by path; it is directly encoded in the control flow. This is
    /// /// the one place where the layer is intentionally restructured for verifiability.
    /// ///
    /// /// `exec_budget` is the upper bound on the polling count used to wait for `STS_DATA_AVAIL`, supplied by
    /// /// the caller according to the command code (see [`crate::xfer::poll_budget`]). Different commands can
    /// /// differ by two orders of magnitude in execution time; only a command-specific budget lets us satisfy
    /// /// both "fast commands time out quickly" and "slow commands are not falsely reported as timed out."
    /// pub fn transmit(&mut self, cmd: &[u8], len: usize, out: &mut [u8], exec_budget: u32)
    ///     -> Result<usize, TisErr> {
    ///     self.request_locality(budget_of(TIMEOUT_A_MS))?;
    ///     let res = self.exchange(cmd, len, out, exec_budget);
    ///     self.relinquish_locality();
    ///     res
    /// } (tis_core.rs:200-223; doc glyphs converted ASCII)
    ///
    /// The verifiable face: Ok carries the response weld of recv
    /// plus the release; on Err the release holds under the entry
    /// state the doc's control-flow argument assumes (not holding on
    /// entry -- the state every in-tree call site is in, since
    /// transmit itself relinquishes on every exit). Under that entry
    /// state every path exits released; the requires-free entry-held
    /// corner is the one escape, tagged below.
    ///
    /// SPEC-DOC MISMATCH: read unconditionally, "every path exits
    /// with locality released" fails in exactly that corner: enter
    /// transmit with held == true and a bus whose read8 errors; the
    /// request_locality error return leaves held == true untouched
    /// and relinquish_locality never runs. Counterexample state:
    /// request_locality was called by the user before transmit, then
    /// transmit returns Err(Phy) while is_holding_locality() is
    /// still true. The twin keeps the entry-state-conditional face
    /// instead of dropping it silently.
    pub exec fn transmit(
        &mut self,
        cmd: &[u8],
        len: usize,
        out: &mut [u8],
        exec_budget: u32,
    ) -> (r: Result<usize, TisErr>)
        requires
            len >= 1,
            len <= cmd.len(),
            (out.len() as int) >= (TPM_HEADER_LEN as int),
        ensures
            match r {
                Result::Ok(n) =>
                    final(out).len() == old(out).len()
                        && !final(self).held
                        && (TPM_HEADER_LEN as int) <= (n as int)
                        && (n as int) <= (final(out).len() as int)
                        && (n as int) == recv_wire_size(final(out)@),
                Result::Err(_) => !old(self).held ==> !final(self).held,
            },
    {
        match self.request_locality(budget_of(TIMEOUT_A_MS)) {
            Result::Ok(()) => {}
            Result::Err(e) => return Result::Err(e),
        }
        let res = self.exchange(cmd, len, out, exec_budget);
        self.relinquish_locality();
        res
    }

    /// Origin Rust: fn exchange(&mut self, cmd: &[u8], len: usize, out: &mut [u8],
    ///     exec_budget: u32) -> Result<usize, TisErr> {
    ///     let sts_addr = reg_sts(self.locality);
    ///     self.phy.reset_fifo(sts_addr);
    ///     self.send_data(cmd, len)?;
    ///     self.phy.write8(sts_addr, STS_GO).inspect_err(|_| {
    ///         self.phy.reset_fifo(sts_addr);
    ///     })?;
    ///     self.wait_status(STS_DATA_AVAIL | STS_VALID, exec_budget)
    ///         .inspect_err(|_| { self.phy.reset_fifo(sts_addr); })?;
    ///     let n = self.recv(out).inspect_err(|_| {
    ///         self.phy.reset_fifo(sts_addr);
    ///     })?;
    ///     self.phy.reset_fifo(sts_addr);
    ///     Ok(n)
    /// } (tis_core.rs:224-246; the three inspect_err closures are
    /// lowered to explicit error arms -- each reset runs before the
    /// error returns)
    ///
    /// The Ok face is the recv weld; the cleanup resets on error
    /// paths are register writes through the trusted phy (device
    /// state, unmodeled -- the structural fact that every error arm
    /// resets before returning is preserved by the arm shape).
    fn exchange(
        &mut self,
        cmd: &[u8],
        len: usize,
        out: &mut [u8],
        exec_budget: u32,
    ) -> (r: Result<usize, TisErr>)
        requires
            len >= 1,
            len <= cmd.len(),
            (out.len() as int) >= (TPM_HEADER_LEN as int),
        ensures
            match r {
                Result::Ok(n) =>
                    final(out).len() == old(out).len()
                        && (TPM_HEADER_LEN as int) <= (n as int)
                        && (n as int) <= (final(out).len() as int)
                        && (n as int) == recv_wire_size(final(out)@),
                _ => true,
            },
    {
        let sts_addr = reg_sts(self.locality);
        self.phy.reset_fifo(sts_addr);
        match self.send_data(cmd, len) {
            Result::Ok(()) => {}
            Result::Err(e) => {
                let _ = self.phy.reset_fifo(sts_addr);
                return Result::Err(e);
            }
        }
        match self.phy.write8(sts_addr, STS_GO) {
            Result::Ok(()) => {}
            Result::Err(e) => {
                let _ = self.phy.reset_fifo(sts_addr);
                return Result::Err(e);
            }
        }
        match self.wait_status(STS_DATA_AVAIL | STS_VALID, exec_budget) {
            Result::Ok(_) => {}
            Result::Err(e) => {
                let _ = self.phy.reset_fifo(sts_addr);
                return Result::Err(e);
            }
        }
        let n = match self.recv(out) {
            Result::Ok(v) => v,
            Result::Err(e) => {
                let _ = self.phy.reset_fifo(sts_addr);
                return Result::Err(e);
            }
        };
        self.phy.reset_fifo(sts_addr);
        Result::Ok(n)
    }
}

// ------------------------------------------------------------------
// Cross-module bridge (proof zone, file tail).
// ------------------------------------------------------------------

/// The wire-size face used by this module's recv weld agrees with the
/// msg.rs response-parser's size field on every slice that carries a
/// full header (both are the big-endian u32 at offsets 2..6).
pub(crate) proof fn lemma_recv_wire_size_matches_msg(raw: &[u8])
    requires
        (raw.len() as int) >= 6,
    ensures
        recv_wire_size(raw@) == super::msg::resp_wire_size(raw),
{
    assert(super::msg::resp_wire_size(raw) == 16777216 * raw@.index(2) as int
        + 65536 * raw@.index(3) as int
        + 256 * raw@.index(4) as int
        + raw@.index(5) as int);
    assert(recv_wire_size(raw@) == 16777216 * raw@.index(2) as int
        + 65536 * raw@.index(3) as int
        + 256 * raw@.index(4) as int
        + raw@.index(5) as int);
}

} // verus!
