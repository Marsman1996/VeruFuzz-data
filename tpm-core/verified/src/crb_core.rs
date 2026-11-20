//! tpm-core 0.1.4 CRB driver core (src/crb_core.rs) -- Verus
//! translation.
//!
//! Bank T3 (family C, the CRB register flow). The driver state machine
//! is transcribed with its doc-paraphrased specs re-erected as faces:
//! the send/recv framing welds, the wf/quiescent entry guard of
//! transmit with locality release on every exit, and the exchange
//! guarantee that a cleanup failure cannot overwrite an already
//! received response. The trust boundary is the sibling crb_phy twin;
//! the poll loop terminates on the counting measure alone (timeout
//! domain is the poll budget, no wall-clock modeling, matching the
//! upstream design).

use vstd::prelude::*;

verus! {

use crate::crb::{
    budget_of, CMD_BUF_CAP, CrbErr, CTRL_CANCEL_CLEAR, CTRL_REQ_CMD_READY, CTRL_REQ_GO_IDLE,
    CTRL_START_INVOKE, CTRL_STS_ERROR, LOC_CTRL_RELINQUISH, LOC_CTRL_REQUEST,
    LOC_STATE_ASSIGNED, LOC_STATE_VALID, MAX_LOCALITY, REG_CTRL_CANCEL, REG_CTRL_CMD_SIZE,
    REG_CTRL_REQ, REG_CTRL_START, REG_CTRL_STS, REG_LOC_CTRL, REG_LOC_STATE, RSP_BUF_CAP,
    TIMEOUT_C_MS, TIMEOUT_LONG_MS,
};
use crate::crb_phy::{check_cmd_bounds, check_rsp_bounds, CrbPhy};
use crate::cursor::Cursor;
use crate::endian::{be32_of, be32_of_exec};
use crate::msg::TPM_HEADER_LEN;

// ===================================================================
// Spec faces shared by the recv/postconditions (this file only)
// ===================================================================

/// Header width of a TPM response, mirroring msg's TPM_HEADER_LEN.
/// A const-eval alias (`= crate::msg::TPM_HEADER_LEN`) is rejected
/// by the visibility leak rule (pub const may not name the pub(crate)
/// original), so the pub face spells the literal; exec bodies keep
/// using msg::TPM_HEADER_LEN, and every spec face below uses this
/// twin (one value, one repository source, two names until msg
/// opens the constant).
pub const CRB_HEADER_LEN: usize = 10;

/// Response size field at wire offset 2 (big-endian u32 across
/// out[2..6]); 0 below a 6-byte buffer. The pub twin of msg's
/// crate-internal resp_wire_size face, same offsets and weights, so
/// the public recv ensured face can name it.
pub open spec fn crb_rsp_len_field(post: Seq<u8>) -> int {
    if 6 <= post.len() {
        16777216 * post.index(2) as int
            + 65536 * post.index(3) as int
            + 256 * post.index(4) as int
            + post.index(5) as int
    } else {
        0
    }
}

/// Ok-arm framing weld of recv: on a successful response fetch the
/// device-written size field equals the returned byte count, the
/// response spans at least the header and fits both the caller buffer
/// and the static response cap, and no byte outside the returned span
/// [0, n) was touched (both phy response reads write inside that
/// span). This is the frame the next decode layer leans on.
pub open spec fn recv_ok_frame(pre: Seq<u8>, post: Seq<u8>, n: int) -> bool {
    post.len() == pre.len()
        && (CRB_HEADER_LEN as int) <= n
        && n <= (post.len() as int)
        && n <= (RSP_BUF_CAP as int)
        && crb_rsp_len_field(post) == n
        && forall|i: int| 0 <= i < pre.len() && i >= n ==> post.index(i) == pre.index(i)
}

// ===================================================================
// Driver state (src/crb_core.rs:10-18)
// ===================================================================

/// Origin Rust: pub struct Crb<P: CrbPhy> {
///     pub phy: P,
///     /// Locality number used by this driver.
///     pub locality: u8,
///     /// Whether locality has been requested and not yet released.
///     held: bool,
/// } (src/crb_core.rs:12-18; held was upstream-private, opened pub
/// here -- the transmit/postcondition faces name it, the T1-4 pub-face
/// precedent; runtime faces unchanged).
pub struct Crb<P: CrbPhy> {
    pub phy: P,
    /// Locality number used by this driver.
    pub locality: u8,
    /// Whether locality has been requested and not yet released.
    pub held: bool,
}

impl<P: CrbPhy> Crb<P> {
    /// Origin Rust: pub fn new(phy: P, locality: u8) -> Self {
    ///     Self { phy, locality, held: false }
    /// } (src/crb_core.rs:21-27)
    pub exec fn new(phy: P, locality: u8) -> (c: Crb<P>)
        ensures
            c.locality == locality,
            !c.held,
    {
        Crb {
            phy,
            locality,
            held: false,
        }
    }

    /// Origin Rust: pub fn is_holding_locality(&self) -> bool {
    ///     self.held
    /// } (src/crb_core.rs:29-31)
    pub exec fn is_holding_locality(&self) -> (r: bool)
        ensures
            r == self.held,
    {
        self.held
    }

    /// Origin Rust: #[inline]
    /// pub fn wf(&self) -> bool {
    ///     self.locality < MAX_LOCALITY
    /// } (src/crb_core.rs:33-37)
    pub exec fn wf(&self) -> (r: bool)
        ensures
            r == ((self.locality as int) < (MAX_LOCALITY as int)),
    {
        self.locality < MAX_LOCALITY
    }

    /// Origin Rust: #[inline]
    /// pub fn quiescent(&self) -> bool {
    ///     !self.held
    /// } (src/crb_core.rs:39-41)
    pub exec fn quiescent(&self) -> (r: bool)
        ensures
            r == !self.held,
    {
        !self.held
    }

    // ===================================================================
    // General polling (src/crb_core.rs:47-59)
    // ===================================================================

    /// Origin Rust: /// Poll a control register until `(value & mask) == want`.
    /// fn wait_reg32(&mut self, reg: u32, mask: u32, want: u32, budget: u32) -> Result<u32, CrbErr> {
    ///     let mut left = budget;
    ///     while left > 0 {
    ///         let v = self.phy.read32(reg)?;
    ///         if (v & mask) == want { return Ok(v); }
    ///         self.phy.delay();
    ///         left -= 1;
    ///     }
    ///     Err(CrbErr::Timeout)
    /// } (src/crb_core.rs:47-59; the read32 ? lowered to a match arm).
    /// Loop discipline: termination is by the counting measure alone
    /// (budget-decrement, no clock modeling). Ok face: the returned
    /// register value satisfied the mask condition. Err variants
    /// carry the phy error straight through; the Timeout arm is the
    /// budget-exhausted class.
    fn wait_reg32(&mut self, reg: u32, mask: u32, want: u32, budget: u32) -> (r: Result<u32, CrbErr>)
        ensures
            r.is_Ok() ==> (r.get_Ok_0() & mask) == want,
            final(self).held == old(self).held,
            final(self).locality == old(self).locality,
    {
        let mut left = budget;
        while left > 0
            invariant
                left <= budget,
            decreases
                left,
        {
            let v = match self.phy.read32(reg) {
                Result::Ok(v) => v,
                Result::Err(e) => return Result::Err(e),
            };
            if (v & mask) == want {
                return Result::Ok(v);
            }
            self.phy.delay();
            left -= 1;
        }
        Result::Err(CrbErr::Timeout)
    }

    // ===================================================================
    // locality (src/crb_core.rs:63-77)
    // ===================================================================

    /// Origin Rust: pub fn request_locality(&mut self, budget: u32) -> Result<(), CrbErr> {
    ///     self.phy.write32(REG_LOC_CTRL, LOC_CTRL_REQUEST)?;
    ///     let want = LOC_STATE_ASSIGNED | LOC_STATE_VALID;
    ///     self.wait_reg32(REG_LOC_STATE, want, want, budget)?;
    ///     self.held = true;
    ///     Ok(())
    /// } (src/crb_core.rs:65-72; write32 ? and wait ? lowered to match
    /// arms). State-guard face: held is set exactly on the success
    /// path, and no failure path disturbs it.
    pub exec fn request_locality(&mut self, budget: u32) -> (r: Result<(), CrbErr>)
        ensures
            r.is_Ok() ==> final(self).held,
            r.is_Err() ==> final(self).held == old(self).held,
    {
        match self.phy.write32(REG_LOC_CTRL, LOC_CTRL_REQUEST) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }

        let want = LOC_STATE_ASSIGNED | LOC_STATE_VALID;
        match self.wait_reg32(REG_LOC_STATE, want, want, budget) {
            Result::Ok(_) => {
                self.held = true;
                Result::Ok(())
            }
            Result::Err(e) => Result::Err(e),
        }
    }

    /// Origin Rust: pub fn relinquish_locality(&mut self) {
    ///     let _ = self.phy.write32(REG_LOC_CTRL, LOC_CTRL_RELINQUISH);
    ///     self.held = false;
    /// } (src/crb_core.rs:74-77) Release is unconditional: every exit
    /// of this function leaves the locality unheld.
    pub exec fn relinquish_locality(&mut self)
        ensures
            !final(self).held,
    {
        let _ = self.phy.write32(REG_LOC_CTRL, LOC_CTRL_RELINQUISH);
        self.held = false;
    }

    // ===================================================================
    // Ready / idle (src/crb_core.rs:81-93)
    // ===================================================================

    /// Origin Rust: fn cmd_ready(&mut self, budget: u32) -> Result<(), CrbErr> {
    ///     self.phy.write32(REG_CTRL_REQ, CTRL_REQ_CMD_READY)?;
    ///     self.wait_reg32(REG_CTRL_REQ, CTRL_REQ_CMD_READY, 0, budget)?;
    ///     Ok(())
    /// } (src/crb_core.rs:83-87; ? lowered to match arms)
    fn cmd_ready(&mut self, budget: u32) -> (r: Result<(), CrbErr>) {
        match self.phy.write32(REG_CTRL_REQ, CTRL_REQ_CMD_READY) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }
        match self.wait_reg32(REG_CTRL_REQ, CTRL_REQ_CMD_READY, 0, budget) {
            Result::Ok(_) => Result::Ok(()),
            Result::Err(e) => Result::Err(e),
        }
    }

    /// Origin Rust: fn go_idle(&mut self, budget: u32) -> Result<(), CrbErr> {
    ///     self.phy.write32(REG_CTRL_REQ, CTRL_REQ_GO_IDLE)?;
    ///     self.wait_reg32(REG_CTRL_REQ, CTRL_REQ_GO_IDLE, 0, budget)?;
    ///     Ok(())
    /// } (src/crb_core.rs:89-93; ? lowered to match arms)
    fn go_idle(&mut self, budget: u32) -> (r: Result<(), CrbErr>) {
        match self.phy.write32(REG_CTRL_REQ, CTRL_REQ_GO_IDLE) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }
        match self.wait_reg32(REG_CTRL_REQ, CTRL_REQ_GO_IDLE, 0, budget) {
            Result::Ok(_) => Result::Ok(()),
            Result::Err(e) => Result::Err(e),
        }
    }

    // ===================================================================
    // Send (src/crb_core.rs:97-121)
    // ===================================================================

    /// Origin Rust: pub fn send(&mut self, cmd: &[u8], len: usize) -> Result<(), CrbErr> {
    ///     if len == 0 { return Err(CrbErr::BadLength); }
    ///     check_cmd_bounds(cmd, len)?;
    ///     // Clear the cancel bit to avoid this command being affected by a stale cancel request from the
    ///     // previous one.
    ///     self.phy.write32(REG_CTRL_CANCEL, CTRL_CANCEL_CLEAR)?;
    ///     // Validate the device-reported available command size.
    ///     let adv = self.phy.read32(REG_CTRL_CMD_SIZE)?;
    ///     if (len as u32) > adv { return Err(CrbErr::BadLength); }
    ///     self.phy.write_cmd(cmd, len)?;
    ///     // Ensure the buffer write becomes visible to the device before START.
    ///     self.phy.fence();
    ///     self.phy.write32(REG_CTRL_START, CTRL_START_INVOKE)
    /// } (src/crb_core.rs:99-121; ? lowered to match arms).
    /// Length-rejection face: an empty or span-invalid request is
    /// rejected before any byte copy -- len == 0 outright, len beyond
    /// the caller slice or the static command cap by the span check
    /// (both before the first phy call).
    pub exec fn send(&mut self, cmd: &[u8], len: usize) -> (r: Result<(), CrbErr>)
        ensures
            (len as int) == 0 ==> r == Result::Err(CrbErr::BadLength),
            (len as int) > (cmd.len() as int) ==> r == Result::Err(CrbErr::BadLength),
            (len as int) > (CMD_BUF_CAP as int) ==> r == Result::Err(CrbErr::BadLength),
    {
        if len == 0 {
            return Result::Err(CrbErr::BadLength);
        }

        match check_cmd_bounds(cmd, len) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }

        // Clear the cancel bit to avoid this command being affected by a stale cancel request from the
        // previous one.
        match self.phy.write32(REG_CTRL_CANCEL, CTRL_CANCEL_CLEAR) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }

        // Validate the device-reported available command size.
        let adv = match self.phy.read32(REG_CTRL_CMD_SIZE) {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        if (len as u32) > adv {
            return Result::Err(CrbErr::BadLength);
        }

        match self.phy.write_cmd(cmd, len) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }

        // Ensure the buffer write becomes visible to the device before START.
        self.phy.fence();

        self.phy.write32(REG_CTRL_START, CTRL_START_INVOKE)
    }

    // ===================================================================
    // Completion / receive (src/crb_core.rs:125-165)
    // ===================================================================

    /// Origin Rust: fn wait_complete(&mut self, budget: u32) -> Result<(), CrbErr> {
    ///     self.wait_reg32(REG_CTRL_START, CTRL_START_INVOKE, 0, budget)?;
    ///     Ok(())
    /// } (src/crb_core.rs:127-130; ? lowered to a match arm). The INVOKE
    /// bit is set by send and cleared by the device itself on
    /// completion (the module-scope startup-mode modeling).
    fn wait_complete(&mut self, budget: u32) -> (r: Result<(), CrbErr>) {
        match self.wait_reg32(REG_CTRL_START, CTRL_START_INVOKE, 0, budget) {
            Result::Ok(_) => Result::Ok(()),
            Result::Err(e) => Result::Err(e),
        }
    }

    /// Origin Rust: pub fn recv(&mut self, out: &mut [u8]) -> Result<usize, CrbErr> {
    ///     if out.len() < TPM_HEADER_LEN { return Err(CrbErr::BadLength); }
    ///     let sts = self.phy.read32(REG_CTRL_STS)?;
    ///     if (sts & CTRL_STS_ERROR) != 0 { return Err(CrbErr::Protocol); }
    ///     check_rsp_bounds(0, out.len(), TPM_HEADER_LEN)?;
    ///     self.phy.read_rsp(0, out, TPM_HEADER_LEN)?;
    ///     let mut c = Cursor::at(2);
    ///     let expected = c.read_be32(out).ok_or(CrbErr::BadLength)?;
    ///     let n = expected as usize;
    ///     if n < TPM_HEADER_LEN { return Err(CrbErr::BadLength); }
    ///     check_rsp_bounds(0, out.len(), n)?;
    ///     self.phy.read_rsp(TPM_HEADER_LEN, out, n - TPM_HEADER_LEN)?;
    ///     // Runtime protection equivalent to the original spec: the response length field must match the
    ///     // returned length.
    ///     let hdr_len = u32::from_be_bytes([out[2], out[3], out[4], out[5]]) as usize;
    ///     if hdr_len != n { return Err(CrbErr::BadLength); }
    ///     Ok(n)
    /// } (src/crb_core.rs:132-165; ok_or + ? and ? lowered to match
    /// arms; u32::from_be_bytes lowered through the endian helper of
    /// the same weighted-sum value face).
    ///
    /// Ok-arm face: the response framing weld (recv_ok_frame) -- a
    /// full header is present, the size field equals the returned
    /// count, the count fits the caller buffer and the static
    /// response cap, and no byte outside [0, n) moved. The
    /// header-recheck runtime line that follows the second fetch is
    /// the faithful upstream double check: under the read_rsp window
    /// face it is provably redundant (bytes 2..6 sit below the header
    /// end, outside the second call's write span), so the runtime
    /// guard can never fire -- recorded here as the defense-in-depth
    /// the upstream comment claims, not as a behavioral fork.
    /// Protocol-class rejections depend on the device-reported status
    /// value and so are part of the trusted phy face (not
    /// characterized from this side of the boundary).
    pub exec fn recv(&mut self, out: &mut [u8]) -> (r: Result<usize, CrbErr>)
        ensures
            (old(out)@.len() as int) < (CRB_HEADER_LEN as int) ==> r
                == Result::Err(CrbErr::BadLength),
            r.is_Ok() ==> recv_ok_frame(old(out)@, final(out)@, r.get_Ok_0() as int),
    {
        let ghost pre = out@;
        if out.len() < TPM_HEADER_LEN {
            return Result::Err(CrbErr::BadLength);
        }

        let sts = match self.phy.read32(REG_CTRL_STS) {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        if (sts & CTRL_STS_ERROR) != 0 {
            return Result::Err(CrbErr::Protocol);
        }

        match check_rsp_bounds(0, out.len(), TPM_HEADER_LEN) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }

        match self.phy.read_rsp(0, out, TPM_HEADER_LEN) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }
        let ghost post1 = out@;

        let mut c = Cursor::at(2);
        let expected = match c.read_be32(out) {
            Option::Some(v) => v,
            Option::None => return Result::Err(CrbErr::BadLength),
        };
        proof {
            assert(out@ == post1);
        }
        let n = expected as usize;

        if n < TPM_HEADER_LEN {
            return Result::Err(CrbErr::BadLength);
        }
        match check_rsp_bounds(0, out.len(), n) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }

        match self.phy.read_rsp(TPM_HEADER_LEN, out, n - TPM_HEADER_LEN) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }
        proof {
            // bytes 2..6 live below the header end, so the second
            // window fetch cannot have disturbed them (window face of
            // read_rsp); the size field still carries `expected`.
            assert(out@.len() == post1.len());
            assert(out@.index(2) == post1.index(2));
            assert(out@.index(3) == post1.index(3));
            assert(out@.index(4) == post1.index(4));
            assert(out@.index(5) == post1.index(5));
        }

        // Runtime protection equivalent to the original spec: the response length field must match the
        // returned length.
        let hdr32 = be32_of_exec(out[2], out[3], out[4], out[5]);
        let hdr_len = hdr32 as usize;
        proof {
            assert(hdr32 as int == be32_of(post1.index(2), post1.index(3), post1.index(4), post1.index(5)));
            assert(crb_rsp_len_field(out@) == (expected as int));
            assert(hdr_len == n);
        }
        if hdr_len != n {
            return Result::Err(CrbErr::BadLength);
        }
        proof {
            assert(out@.len() == pre.len());
            assert(crb_rsp_len_field(out@) == (n as int));
            assert forall|i: int|
                0 <= i < pre.len() && i >= (n as int) implies out@.index(i) == pre.index(i) by {
                assert(0 <= i < pre.len());
                assert(i >= (n as int));
            }
        }

        Result::Ok(n)
    }

    // ===================================================================
    // One complete round trip (src/crb_core.rs:171-198)
    // ===================================================================

    /// Origin Rust: pub fn transmit(&mut self, cmd: &[u8], len: usize, out: &mut [u8]) -> Result<usize, CrbErr> {
    ///     if !self.wf() || !self.quiescent() || len < TPM_HEADER_LEN
    ///         || len > cmd.len() || out.len() < TPM_HEADER_LEN
    ///     {
    ///         return Err(CrbErr::BadLength);
    ///     }
    ///     self.request_locality(budget_of(TIMEOUT_C_MS))?;
    ///     let res = self.exchange(cmd, len, out);
    ///     self.relinquish_locality();
    ///     res
    /// } (src/crb_core.rs:171-185).
    /// Entry-guard face: an out-of-range locality number, an already
    /// held locality, or any span violation is rejected as BadLength
    /// before any bus activity. Held-flag face: entering unheld means
    /// leaving unheld -- the guard's quiescent leg plus
    /// relinquish_locality's unconditional clear pin the flag on every
    /// exit path (entry-held inputs fictitiously satisfy the guard;
    /// there the flag simply survives unchanged, which the face
    /// carries as old = final).
    pub exec fn transmit(
        &mut self,
        cmd: &[u8],
        len: usize,
        out: &mut [u8],
    ) -> (r: Result<usize, CrbErr>)
        ensures
            (old(self).locality as int) >= (MAX_LOCALITY as int) || old(self).held || (len as int)
                < (CRB_HEADER_LEN as int) || (len as int) > (cmd.len() as int) || (old(
                out,
            )@.len() as int)
                < (CRB_HEADER_LEN as int) ==> r == Result::Err(CrbErr::BadLength),
            final(self).held == old(self).held,
    {
        if !self.wf()
            || !self.quiescent()
            || len < TPM_HEADER_LEN
            || len > cmd.len()
            || out.len() < TPM_HEADER_LEN
        {
            return Result::Err(CrbErr::BadLength);
        }

        match self.request_locality(budget_of(TIMEOUT_C_MS)) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }
        let res = self.exchange(cmd, len, out);
        self.relinquish_locality();
        res
    }

    /// Origin Rust: fn exchange(&mut self, cmd: &[u8], len: usize, out: &mut [u8]) -> Result<usize, CrbErr> {
    ///     self.cmd_ready(budget_of(TIMEOUT_C_MS))?;
    ///     self.send(cmd, len)?;
    ///     self.wait_complete(budget_of(TIMEOUT_LONG_MS))?;
    ///     let n = self.recv(out)?;
    ///     // A cleanup failure must not overwrite an already received response.
    ///     let _ = self.go_idle(budget_of(TIMEOUT_C_MS));
    ///     Ok(n)
    /// } (src/crb_core.rs:187-197; ? lowered to match arms).
    /// The upstream comment is the spec: once recv returns Ok, the
    /// go_idle cleanup result is discarded by the `let _` binding, so
    /// the received response survives structurally (no branch can
    /// substitute a cleanup error for it).
    fn exchange(&mut self, cmd: &[u8], len: usize, out: &mut [u8]) -> (r: Result<usize, CrbErr>) {
        match self.cmd_ready(budget_of(TIMEOUT_C_MS)) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }
        match self.send(cmd, len) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }
        match self.wait_complete(budget_of(TIMEOUT_LONG_MS)) {
            Result::Ok(()) => (),
            Result::Err(e) => return Result::Err(e),
        }

        let n = match self.recv(out) {
            Result::Ok(n) => n,
            Result::Err(e) => return Result::Err(e),
        };

        // A cleanup failure must not overwrite an already received response.
        let _ = self.go_idle(budget_of(TIMEOUT_C_MS));
        Result::Ok(n)
    }
}

} // verus!
