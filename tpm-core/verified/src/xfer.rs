//! tpm-core 0.1.4 transport retry layer over TIS (src/xfer.rs) --
//! Verus translation.
//!
//! Upstream face: the command-code timing table, the retry policy
//! constants, the well-formedness gate cmd_wf, the backoff-saturation
//! retry loop `run`, and the `Xfer` struct pairing a TIS transport
//! with a caller-set retry budget (src/xfer.rs:1-219).
//!
//! Re-erected here:
//!  - cmd_wf is total and is the ONLY gate: no byte is sent unless
//!    it holds (the doc's "the device never sees them");
//!  - the retry loop threads the release discipline of T2's
//!    transmit entry-conditionally (each attempt is entered unheld
//!    whenever run itself was entered unheld; backoff preserves the
//!    held flag; every exit releases or preserves entry-held --
//!    the upstream "retries simply chain the guarantee" sentence);
//!  - the Ok weld: the returned length equals the response size
//!    field at 2..6, headers fit, and the returned rc is exactly
//!    the response header word at offset 6 (the "not rewritten or
//!    swallowed" sentence -- no translation of retryable codes);
//!  - the backoff tick count doubles with saturation at the cap
//!    (bounded by budget_of(RETRY_CAP_MS) throughout).
//!
//! Lowered spellings, each with an Origin note: peek_be32 stays a
//! trampoline over rewrite::read_be32; checked_sub/is_some_and in
//! body_at_least lowered to the explicit range test; the for-free
//! backoff loop lowered to the while walk.

use vstd::prelude::*;

verus! {

use super::cmd::{
    CC_CONTEXT_LOAD, CC_CONTEXT_SAVE, CC_FLUSH_CONTEXT, CC_GET_CAPABILITY, CC_GET_RANDOM,
    CC_PCR_EXTEND, CC_PCR_READ, CC_SELF_TEST, CC_SHUTDOWN, CC_STARTUP,
};
use super::phy::TisPhy;
use super::rewrite::{read_be32, wire_be32};
use super::tis::{budget_of, TisErr, MAX_LOCALITY};
use super::tis_core::{Tis, TPM_HEADER_LEN};

// ------------------------------------------------------------------
// Return codes and retry constants (xfer.rs:13-24)
// ------------------------------------------------------------------

/// Origin Rust: pub const RC_SUCCESS: u32 = 0x0000_0000; (xfer.rs:13)
pub const RC_SUCCESS: u32 = 0x0000_0000;
/// Origin Rust: pub const RC_WARN_BASE: u32 = 0x0000_0900; (xfer.rs:14-15)
pub const RC_WARN_BASE: u32 = 0x0000_0900;
/// Origin Rust: pub const RC_TESTING: u32 = 0x0000_090A; (xfer.rs:16-18)
pub const RC_TESTING: u32 = 0x0000_090A;
/// Origin Rust: pub const RC_RETRY: u32 = 0x0000_0922; (xfer.rs:19-20)
pub const RC_RETRY: u32 = 0x0000_0922;
/// Origin Rust: pub const RC_YIELDED: u32 = 0x0000_0908; (xfer.rs:21-24)
pub const RC_YIELDED: u32 = 0x0000_0908;
/// Origin Rust: const RETRY_FIRST_MS: u32 = 20; (xfer.rs:25-26)
pub(crate) const RETRY_FIRST_MS: u32 = 20;
/// Origin Rust: const RETRY_CAP_MS: u32 = 2000; (xfer.rs:27-28)
pub(crate) const RETRY_CAP_MS: u32 = 2000;
/// Origin Rust: const RETRY_MAX: u32 = 8; (xfer.rs:29-32; private
/// upstream -- the twin opens it to pub because the public contract
/// of Xfer::new cites it, visibility only. The retries field is
/// caller-mutable, so the constant is only the constructor default)
pub const RETRY_MAX: u32 = 8;
/// Origin Rust: const DURATION_SHORT_MS: u32 = 750; (xfer.rs:33)
pub(crate) const DURATION_SHORT_MS: u32 = 750;
/// Origin Rust: const DURATION_MEDIUM_MS: u32 = 2000; (xfer.rs:34)
pub(crate) const DURATION_MEDIUM_MS: u32 = 2000;
/// Origin Rust: const DURATION_LONG_MS: u32 = 30000; (xfer.rs:35)
pub(crate) const DURATION_LONG_MS: u32 = 30000;
/// Origin Rust: const DURATION_DEFAULT_MS: u32 = 120000; (xfer.rs:36-38)
pub(crate) const DURATION_DEFAULT_MS: u32 = 120000;

// ------------------------------------------------------------------
// Command timing table (xfer.rs:39-60)
// ------------------------------------------------------------------

/// Spec twin of the command-code timing table: the four tier values
/// by command membership. The command codes are pub(crate) constants
/// upstream (cmd.rs), so the spec twin spells the same wire values
/// literally (STARTUP 0x144, SHUTDOWN 0x145, PCR_READ 0x17E,
/// PCR_EXTEND 0x182, GET_CAPABILITY 0x17A, CONTEXT_LOAD 0x161,
/// CONTEXT_SAVE 0x162, FLUSH_CONTEXT 0x165, GET_RANDOM 0x17B,
/// SELF_TEST 0x143) -- value-equal to the exec table below.
pub open spec fn spec_duration_ms(cc: u32) -> int {
    if cc == 0x0000_0144u32
        || cc == 0x0000_0145u32
        || cc == 0x0000_017Eu32
        || cc == 0x0000_0182u32
        || cc == 0x0000_017Au32
        || cc == 0x0000_0161u32
        || cc == 0x0000_0162u32
        || cc == 0x0000_0165u32
    {
        750
    } else if cc == 0x0000_017Bu32 {
        2000
    } else if cc == 0x0000_0143u32 {
        30000
    } else {
        120000
    }
}

/// Origin Rust: fn duration_ms(cc: u32) -> u32 { ... } (xfer.rs:39-60;
/// the if-chain is kept, the constant spellings resolved to the
/// tier values used in the spec twin above)
pub(crate) exec fn duration_ms(cc: u32) -> (r: u32)
    ensures
        (r as int) == spec_duration_ms(cc),
{
    if cc == CC_STARTUP
        || cc == CC_SHUTDOWN
        || cc == CC_PCR_READ
        || cc == CC_PCR_EXTEND
        || cc == CC_GET_CAPABILITY
        || cc == CC_CONTEXT_LOAD
        || cc == CC_CONTEXT_SAVE
        || cc == CC_FLUSH_CONTEXT
    {
        DURATION_SHORT_MS
    } else if cc == CC_GET_RANDOM {
        DURATION_MEDIUM_MS
    } else if cc == CC_SELF_TEST {
        DURATION_LONG_MS
    } else {
        DURATION_DEFAULT_MS
    }
}

/// Origin Rust: /// Command code -> polling budget for waiting for a response.
/// pub fn poll_budget(cc: u32) -> u32 {
///     budget_of(duration_ms(cc))
/// } (xfer.rs:61-64; the face carries the "always positive" claim
/// of the doc line above it)
pub exec fn poll_budget(cc: u32) -> (r: u32)
    ensures
        r >= 1,
        spec_duration_ms(cc) == 0 ==> r == 1,
        spec_duration_ms(cc) >= 1 ==> (r as int) == spec_duration_ms(cc),
{
    let d = duration_ms(cc);
    assert((d as int) == spec_duration_ms(cc));
    budget_of(d)
}

// ------------------------------------------------------------------
// Error type (xfer.rs:65-72)
// ------------------------------------------------------------------

/// Origin Rust: #[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// pub enum XferErr {
///     /// Transport-layer error. The bytes did not complete a full round trip.
///     Bus(TisErr),
///     /// The command is invalid as a command: the length field does not match the buffer. No bytes of the
///     /// command are sent.
///     BadCommand,
/// } (xfer.rs:65-72; the derives carry no Verus twin)
pub enum XferErr {
    /// Transport-layer error. The bytes did not complete a full round trip.
    Bus(TisErr),
    /// The command is invalid as a command: the length field does not match the buffer. No bytes of the
    /// command are sent.
    BadCommand,
}

// ------------------------------------------------------------------
// Word access over the wire (xfer.rs:73-90)
// ------------------------------------------------------------------

/// Origin Rust: pub(crate) fn peek_be32(b: &[u8], off: usize) -> u32 {
///     read_be32(b, off)
/// } (xfer.rs:73-79; the doc's one-look-two-forms rationale is
/// representation only -- the body is the trampoline)
pub(crate) exec fn peek_be32(b: &[u8], off: usize) -> (r: u32)
    requires
        (off as int) + 4 <= (b.len() as int),
    ensures
        (r as int) == wire_be32(b@, off as int),
{
    read_be32(b, off)
}

/// Origin Rust: fn cmd_wf(cmd: &[u8], len: usize) -> bool {
///     if len < TPM_HEADER_LEN { return false; }
///     if len > cmd.len() { return false; }
///     let d = peek_be32(cmd, 2);
///     d as usize == len
/// } (xfer.rs:81-90; total: the early length tests keep the read
/// in bounds on every path that reaches it)
pub(crate) exec fn cmd_wf(cmd: &[u8], len: usize) -> (r: bool)
    ensures
        r == cmd_wf_spec(cmd@, len as int),
{
    if len < TPM_HEADER_LEN {
        return false;
    }
    if len > cmd.len() {
        return false;
    }
    peek_be32(cmd, 2) as usize == len
}

/// Spec twin of the well-formedness gate: header-sized, within the
/// buffer, and the wire size word agrees with the length.
pub open spec fn cmd_wf_spec(cmd: Seq<u8>, len: int) -> bool {
    (TPM_HEADER_LEN as int) <= len
        && len <= cmd.len()
        && wire_be32(cmd, 2) == len
}

/// Origin Rust: /// Returns whether the response body (everything after the header) has at least `min_body` bytes.
/// ///
/// /// This is the last gate before parsing. Parser entry points assume this condition holds.
/// pub fn body_at_least(n: usize, min_body: usize) -> bool {
///     n.checked_sub(TPM_HEADER_LEN).is_some_and(|body| body >= min_body)
/// } (xfer.rs:94-97; checked_sub + is_some_and lowered to the
/// explicit range test)
pub exec fn body_at_least(n: usize, min_body: usize) -> (r: bool)
    ensures
        r == ((n as int) >= (TPM_HEADER_LEN as int)
            && (n as int) - (TPM_HEADER_LEN as int) >= (min_body as int)),
{
    n >= TPM_HEADER_LEN && n - TPM_HEADER_LEN >= min_body
}

// ------------------------------------------------------------------
// Xfer (xfer.rs:98-110)
// ------------------------------------------------------------------

/// Origin Rust: pub struct Xfer<P: TisPhy> {
///     pub tis: Tis<P>,
///     /// Remaining retry budget. It is stored as a field rather than a constant because the boot phase (device
///     /// just powered on, self-test not complete) and the steady state use the same code but require different
///     /// patience.
///     pub retries: u32,
/// } (xfer.rs:98-104)
pub struct Xfer<P: TisPhy> {
    pub tis: Tis<P>,
    /// Remaining retry budget. It is stored as a field rather than a constant because the boot phase (device
    /// just powered on, self-test not complete) and the steady state use the same code but require different
    /// patience.
    pub retries: u32,
}

impl<P: TisPhy> Xfer<P> {
    /// Origin Rust: pub fn new(tis: Tis<P>) -> Self {
    ///     Xfer { tis, retries: RETRY_MAX }
    /// } (xfer.rs:105-111)
    pub exec fn new(tis: Tis<P>) -> (t: Xfer<P>)
        ensures
            t.tis == tis,
            t.retries == RETRY_MAX,
    {
        Xfer {
            tis,
            retries: RETRY_MAX,
        }
    }

    /// Origin Rust: /// Runtime self-check: whether the state satisfies the prerequisite for sending a command.
    /// ///
    /// /// This exists because of the interface boundary -- this layer is called by an interface without
    /// /// preconditions (the signature is chosen by the higher-level verification requirements and cannot be
    /// /// changed), while its own methods have preconditions. The gap must be closed at runtime: check once,
    /// /// and if the preconditions are not met, return immediately rather than continuing with invalid state.
    /// pub fn ready(&self) -> bool {
    ///     self.tis.locality < crate::tis::MAX_LOCALITY && !self.tis.is_holding_locality()
    /// } (xfer.rs:112-119; doc glyphs converted ASCII)
    pub exec fn ready(&self) -> (r: bool)
        ensures
            r == ((self.tis.locality as int) < (MAX_LOCALITY as int)
                && !self.tis.held),
    {
        self.tis.locality < MAX_LOCALITY && !self.tis.is_holding_locality()
    }

    // --------------------------------------------------------------
    // Backoff (xfer.rs:120-133)
    // --------------------------------------------------------------

    /// Origin Rust: /// Wait `ticks` polling intervals.
    /// ///
    /// /// This uses integer multiples of the polling interval as the wait length rather than accepting a sleep
    /// /// interface: this layer does not introduce a time concept, and the actual waiting duration is determined
    /// /// by the physical layer's throttling. The termination of this loop therefore comes directly from the
    /// /// counter.
    /// fn backoff(&mut self, ticks: u32) {
    ///     let mut left = ticks;
    ///     while left > 0 { self.tis.phy.delay(); left -= 1; }
    /// } (xfer.rs:120-133; the counter is the only termination
    /// measure, exactly as the doc states. The frame discipline of
    /// #T2-2 applies: the &mut knowledge is re-anchored in the loop
    /// invariants, and the fn-level face re-exports it)
    pub(crate) exec fn backoff(&mut self, ticks: u32)
        ensures
            final(self).tis.held == old(self).tis.held,
            final(self).tis.locality == old(self).tis.locality,
            final(self).retries == old(self).retries,
    {
        let ghost h0 = self.tis.held;
        let ghost l0 = self.tis.locality;
        let mut left = ticks;
        while left > 0
            invariant
                (left as int) <= (ticks as int),
                self.tis.held == h0,
                self.tis.locality == l0,
                self.retries == old(self).retries,
            decreases
                (left as int),
        {
            self.tis.phy.delay();
            left -= 1;
        }
    }

    // --------------------------------------------------------------
    // Single attempt (xfer.rs:134-155)
    // --------------------------------------------------------------

    /// Origin Rust: /// Send a command, receive a response, and extract the return code.
    /// ///
    /// /// The return code is read from a fixed offset in the response header, and its value does not depend on
    /// /// parsing the packet body -- the transport layer guarantees the response length is at least one header,
    /// /// so this read is unconditional.
    /// ///
    /// /// `exec_budget` is forwarded directly to [`Tis::transmit`] to bound the number of polling iterations
    /// /// spent waiting for `STS_DATA_AVAIL`.
    /// fn attempt(
    ///     &mut self, cmd: &[u8], len: usize, rsp: &mut [u8], exec_budget: u32,
    /// ) -> Result<(usize, u32), XferErr> {
    ///     let n = self.tis.transmit(cmd, len, rsp, exec_budget).map_err(XferErr::Bus)?;
    ///     let rc = peek_be32(&*rsp, 6);
    ///     Ok((n, rc))
    /// } (xfer.rs:134-155; map_err + ? lowered to the explicit match.
    /// The requires set is exactly T2's transmit entry contract -- len
    /// within [1, cmd.len()], response buffer header-sized -- which
    /// run's cmd_wf gate discharges for every in-tree caller)
    pub(crate) exec fn attempt(
        &mut self,
        cmd: &[u8],
        len: usize,
        rsp: &mut [u8],
        exec_budget: u32,
    ) -> (r: Result<(usize, u32), XferErr>)
        requires
            len >= 1,
            len <= cmd.len(),
            (rsp.len() as int) >= (TPM_HEADER_LEN as int),
        ensures
            final(self).retries == old(self).retries,
            match r {
                Result::Ok((n, rc)) =>
                    !final(self).tis.held
                        && final(rsp).len() == old(rsp).len()
                        && (TPM_HEADER_LEN as int) <= (n as int)
                        && (n as int) <= (final(rsp).len() as int)
                        && (n as int) == wire_be32(final(rsp)@, 2)
                        && wire_be32(final(rsp)@, 6) == (rc as int),
                Result::Err(XferErr::BadCommand) => false,
                Result::Err(_) =>
                    !old(self).tis.held ==> !final(self).tis.held,
            },
    {
        let r = self.tis.transmit(cmd, len, rsp, exec_budget);
        match r {
            Result::Ok(n) => {
                let rc = peek_be32(rsp, 6);
                Result::Ok((n, rc))
            }
            Result::Err(e) => Result::Err(XferErr::Bus(e)),
        }
    }

    /// Origin Rust: /// Retryable return codes.
    /// ///
    /// /// A self-test command encountering "still self-testing" is an exception: that command asks for exactly
    /// /// the self-test state, and "still testing" is a valid answer rather than a response to avoid. Treating it
    /// /// as retryable turns a simple status query into a blocking wait, which is especially wrong during the
    /// /// boot phase.
    /// pub fn retryable(rc: u32, cc: u32) -> bool { ... } (xfer.rs:156-170)
    pub exec fn retryable(rc: u32, cc: u32) -> (r: bool)
        ensures
            r == (rc == RC_RETRY
                || rc == RC_YIELDED
                || (rc == RC_TESTING && cc != 0x0000_0143u32)),
    {
        if rc == RC_RETRY || rc == RC_YIELDED {
            true
        } else if rc == RC_TESTING {
            cc != CC_SELF_TEST
        } else {
            false
        }
    }

    // --------------------------------------------------------------
    // The retry loop (xfer.rs:171-219)
    // --------------------------------------------------------------

    /// Origin Rust: pub fn run(&mut self, cmd: &[u8], len: usize, rsp: &mut [u8])
    ///     -> Result<(usize, u32), XferErr> { ... } (xfer.rs:171-219;
    /// see the full doc-quote below)
    ///
    /// Upstream doc, verbatim (the three fixed properties are the
    /// twin's three postcondition groups):
    ///
    /// /// Send a command, retry it if necessary, and return the response length and return code.
    /// ///
    /// /// Three properties are fixed in the signature:
    /// ///
    /// /// - **No byte is sent if the command has not passed self-test**. Malformed commands are rejected here,
    /// ///   and the device never sees them.
    /// /// - **Locality is never held across any exit path**. The transport layer guarantees this iteratively, and
    /// ///   retries simply chain the guarantee -- each attempt is a complete acquire/release cycle rather than
    /// ///   holding locality in a loop.
    /// /// - **The return code is exactly the value in the response header**. This layer does not rewrite,
    /// ///   swallow, or translate it; if the retry count is exhausted but the return code is still retryable, it
    /// ///   is passed through unchanged.
    ///
    /// The response buffer must fit at least one header (the README
    /// platform contract item; the twin carries it as the only
    /// requires -- the panic face of the undersized case is the
    /// T2 Batch S3 disposition, not reopened here).
    ///
    /// The tried loop shape: entry-held is ghost-captured; the loop
    /// invariant re-anchors it (pitfall #T2-2: old(self) disappears
    /// inside loops unless tied by an invariant) and chains the
    /// release discipline entry-conditionally, exactly as in the
    /// idiom probe of this batch.
    pub exec fn run(
        &mut self,
        cmd: &[u8],
        len: usize,
        rsp: &mut [u8],
    ) -> (r: Result<(usize, u32), XferErr>)
        requires
            (rsp.len() as int) >= (TPM_HEADER_LEN as int),
        ensures
            final(self).retries == old(self).retries,
            match r {
                Result::Ok((n, rc)) =>
                    !final(self).tis.held
                        && final(rsp).len() == old(rsp).len()
                        && (TPM_HEADER_LEN as int) <= (n as int)
                        && (n as int) <= (final(rsp).len() as int)
                        && (n as int) == wire_be32(final(rsp)@, 2)
                        && wire_be32(final(rsp)@, 6) == (rc as int),
                Result::Err(XferErr::BadCommand) =>
                    !cmd_wf_spec(cmd@, len as int)
                        && final(self).tis.held == old(self).tis.held
                        && final(rsp).len() == old(rsp).len(),
                Result::Err(_) =>
                    !old(self).tis.held ==> !final(self).tis.held,
            },
    {
        if !cmd_wf(cmd, len) {
            return Result::Err(XferErr::BadCommand);
        }
        let ghost cmd0 = cmd@;
        let cc = peek_be32(cmd, 6);
        let exec_budget = poll_budget(cc);
        let cap = budget_of(RETRY_CAP_MS);
        let mut ticks = budget_of(RETRY_FIRST_MS);
        let ghost h0 = self.tis.held;
        let ghost rsp0len = (rsp.len() as int);
        let mut left = self.retries;
        while left > 0
            invariant
                (left as int) <= (self.retries as int),
                self.retries == old(self).retries,
                old(self).tis.held == h0,
                h0 == false ==> !self.tis.held,
                self.tis.held == false || self.tis.held == h0,
                (cmd0.len() as int) == (cmd.len() as int),
                cmd@ == cmd0,
                cmd_wf_spec(cmd@, len as int),
                (rsp.len() as int) == (old(rsp).len() as int),
                (rsp.len() as int) >= (TPM_HEADER_LEN as int),
                exec_budget >= 1,
                (ticks as int) <= (cap as int),
                (ticks as int) >= 1,
            decreases
                (left as int),
        {
            match self.attempt(cmd, len, rsp, exec_budget) {
                Result::Ok((n, rc)) => {
                    if !Self::retryable(rc, cc) {
                        // face relay into the function exit
                        assert(!self.tis.held);
                        assert(rsp.len() as int == old(rsp).len() as int);
                        assert((TPM_HEADER_LEN as int) <= (n as int));
                        assert((n as int) <= rsp.len() as int);
                        assert((n as int) == wire_be32(rsp@, 2));
                        assert(wire_be32(rsp@, 6) == rc as int);
                        return Result::Ok((n, rc));
                    }
                }
                Result::Err(e) => return Result::Err(e),
            }
            // saturating doubling: never past the cap
            self.backoff(ticks);
            if ticks < cap {
                if ticks <= cap - ticks {
                    ticks += ticks;
                } else {
                    ticks = cap;
                }
            }
            left -= 1;
        }
        match self.attempt(cmd, len, rsp, exec_budget) {
            Result::Ok((n, rc)) => {
                assert(!self.tis.held);
                assert(rsp.len() as int == old(rsp).len() as int);
                assert((TPM_HEADER_LEN as int) <= (n as int));
                assert((n as int) <= rsp.len() as int);
                assert((n as int) == wire_be32(rsp@, 2));
                assert(wire_be32(rsp@, 6) == rc as int);
                Result::Ok((n, rc))
            }
            Result::Err(e) => Result::Err(e),
        }
    }
}

} // verus!
