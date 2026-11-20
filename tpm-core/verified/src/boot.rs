//! tpm-core 0.1.4 boot phase: startup, self-test and capacity
//! reconciliation (src/boot.rs) -- Verus translation.
//!
//! Upstream face: the boot-time return codes (RC_INITIALIZE treated
//! as success for startup, RC_TESTING treated as success for
//! self-test), the fixed boot packet images (every boot command has
//! a compile-time constant payload, so the length word is written
//! once in put_header and never rewritten -- the anti-drift
//! sentence of the put_header doc), the four-dimension capacity
//! probe against the static MSG_MAX reservations, and bring_up's
//! dependency-ordered four-step sequence (src/boot.rs:1-289).
//!
//! Re-erected here:
//!  - every put_* method's window face states the exact wire bytes
//!    and leaves everything outside the window untouched;
//!  - each command method fixes its ENTIRE assembled image in its
//!    contract (header + payload); since every image's size word
//!    equals the transmit length it is sent with, no boot command
//!    can ever trip the link gate: the four methods' Err(Bus(
//!    BadCommand)) arms carry the constant false face -- this is
//!    the put_header doc's discipline ("ensured by the
//!    postcondition of the assembler, rather than trusting each
//!    call site to remember it") closed as a theorem;
//!  - startup / self_test accept exactly their documented rc sets
//!    ({"RC_SUCCESS","RC_INITIALIZE"} resp. {"RC_SUCCESS",
//!    "RC_TESTING"}) and shutdown accepts nothing but RC_SUCCESS
//!    (the "no secondary interpretation" sentences);
//!  - property's ok face fixes the returned value to the wire
//!    property word of THIS response (a 27-byte minimum, a nonzero
//!    count, an accepted response tag), with both parsers' exact
//!    rejection shapes phrased over the response-buffer view (the
//!    slice-typed rsp.rs spec faces restated over Seq<u8>, same
//!    formulas, an Origin-noted lowering);
//!  - probe_limits's ok arm carries the MSG_MAX reconciliation
//!    triple exactly as upstream checks it (max_response /
//!    max_object_context / max_session_context; max_command is
//!    returned but NOT reconciled -- the notes carry the
//!    asymmetry), and its Capacity arm certifies the final round
//!    had parsed cleanly (capacity checks run only after all four
//!    property reads return);
//!  - bring_up: Err(Abi) is exactly the abi_ok guard; the ok arm
//!    returns the link unheld with the retry budget untouched.
//!    The doc's step ORDER lives in the body (startup, then
//!    self-test, then the capacity reads); which step produced an
//!    Err is not stateable on the public face (the #T4-11
//!    dichotomy precedent -- the arms keep what stays observable).
//!
//! NOTE (deferred face): locality is NOT claimed preserved through
//! run: T2's transmit contract fixes only the held flag and the
//! response facts, and Xfer::run relays nothing stronger, so no
//! boot face cites locality.

use vstd::prelude::*;

verus! {

use super::chip::MSG_MAX;
use super::cmd::CC_GET_CAPABILITY;
use super::cursor::{be16_bytes, be16_bytes_spec, be32_bytes, be32_bytes_spec};
use super::endian::be16_of;
use super::msg::{build_header, parse_response, ParseError, RC_SUCCESS};
use super::phy::TisPhy;
use super::rewrite::wire_be32;
use super::tis_core::TPM_HEADER_LEN;
use super::xfer::{cmd_wf_spec, Xfer, XferErr};

// ------------------------------------------------------------------
// Constants (boot.rs:11-33)
// ------------------------------------------------------------------

// Public spec faces of this module cite the command codes and the
// no-sessions tag, which cmd.rs / msg.rs keep pub(crate); they are
// restated pub HERE with their upstream names and values (the
// chip.rs Format-1 restatement and the xfer.rs spec_duration_ms
// literal precedent for spec-citation visibility; cmd.rs values
// 0x144 / 0x145 / 0x143 / cap 0x6, msg.rs tag 0x8001).

/// The TPM2_CC_Startup command code (cmd.rs pub(crate), restated
/// pub for the image contracts of this module).
pub const CC_STARTUP: u32 = 0x0000_0144;
/// The TPM2_CC_Shutdown command code (same restatement).
pub const CC_SHUTDOWN: u32 = 0x0000_0145;
/// The TPM2_CC_SelfTest command code (same restatement).
pub const CC_SELF_TEST: u32 = 0x0000_0143;
/// The TPM_CAP_TPM_PROPERTIES capability value (cmd.rs pub(crate),
/// same restatement).
pub const CAP_TPM_PROPERTIES: u32 = 0x0000_0006;
/// The request/response tag of no-sessions packets (msg.rs
/// pub(crate) 0x8001, same restatement).
pub const ST_NO_SESSIONS: u16 = 0x8001;

/// Origin Rust: /// The device has not been initialized, or conversely--has already been initialized.
/// ///
/// /// When it appears in the response to a startup command, it means "this command arrived too late; the
/// device was already started." The boot layer treats it as success; see the notes for [`Boot::startup`].
/// const RC_INITIALIZE: u32 = 0x0000_0100; (boot.rs:11-15; the
/// "treated as success" face is startup's rc set below)
/// Visibility opened pub (Origin note): the twin's public startup
/// contract cites this constant in its Rc arm; upstream keeps it
/// file-private. Runtime value unchanged.
pub const RC_INITIALIZE: u32 = 0x0000_0100;
/// Origin Rust: /// Self-test is already running in the background.
/// pub const RC_TESTING: u32 = 0x0000_090A; (boot.rs:16-17)
pub const RC_TESTING: u32 = 0x0000_090A;
/// Origin Rust: /// Longest command the device can receive.
/// const PT_MAX_COMMAND_SIZE: u32 = 0x0000_011E; (boot.rs:18-19)
pub const PT_MAX_COMMAND_SIZE: u32 = 0x0000_011E;
/// Origin Rust: /// Longest response the device can produce.
/// const PT_MAX_RESPONSE_SIZE: u32 = 0x0000_011F; (boot.rs:20-21)
pub const PT_MAX_RESPONSE_SIZE: u32 = 0x0000_011F;
/// Origin Rust: /// Maximum length of a single object backup block.
/// const PT_MAX_OBJECT_CONTEXT: u32 = 0x0000_0121; (boot.rs:22-23)
pub const PT_MAX_OBJECT_CONTEXT: u32 = 0x0000_0121;
/// Origin Rust: /// Maximum length of a single session backup block.
/// const PT_MAX_SESSION_CONTEXT: u32 = 0x0000_0122; (boot.rs:24-25)
pub const PT_MAX_SESSION_CONTEXT: u32 = 0x0000_0122;
/// Origin Rust: const SELF_TEST_FULL: u8 = 1; (boot.rs:26)
pub const SELF_TEST_FULL: u8 = 1;
/// Origin Rust: const SELF_TEST_INCREMENTAL: u8 = 0; (boot.rs:27)
pub const SELF_TEST_INCREMENTAL: u8 = 0;
/// Origin Rust: /// Longest boot command: packet header (10 bytes) + capability query with three u32 values.
/// const BOOT_CMD_MAX: usize = 22; (boot.rs:28-29)
pub const BOOT_CMD_MAX: usize = 22;
/// Origin Rust: /// Capacity of the boot response. A single property response is header 10 + fixed prefix 9 + key/value
/// pair 8 = 27 bytes; using 128 leaves room, while keeping this temporary buffer small enough to sit on
/// the stack.
/// const BOOT_RSP_MAX: usize = 128; (boot.rs:30-33)
pub const BOOT_RSP_MAX: usize = 128;

// ------------------------------------------------------------------
// BootErr / Limits (boot.rs:34-61)
// ------------------------------------------------------------------

/// Origin Rust: #[derive(PartialEq, Eq)]
/// pub enum BootErr { Abi, NotReady, Bus(XferErr), Rc(u32), Parse(ParseError), Capacity } (boot.rs:34-48;
/// the derives carry no Verus twin; variant docs: Abi "The
/// host-provided cryptographic interface does not match the
/// assumptions of this driver.", NotReady "The link is not in a
/// state that can issue a command.", Bus "Bytes did not complete
/// a full round trip.", Rc "The device returned a non-zero return
/// code.", Parse "The response arrived but parsing failed.",
/// Capacity "The device reported a capacity larger than the static
/// space reserved by this driver.")
pub enum BootErr {
    /// The host-provided cryptographic interface does not match the assumptions of this driver.
    Abi,
    /// The link is not in a state that can issue a command.
    NotReady,
    /// Bytes did not complete a full round trip.
    Bus(XferErr),
    /// The device returned a non-zero return code.
    Rc(u32),
    /// The response arrived but parsing failed.
    Parse(ParseError),
    /// The device reported a capacity larger than the static space reserved by this driver.
    Capacity,
}

/// Origin Rust: /// The four dimensions queried during boot.
/// ///
/// /// They are queried not for logging, but for **reconciliation**: this driver uses fixed-size buffers,
/// and their sizes are fixed at compile time. If the device requires larger packets or produces backup
/// blocks longer than the reserved space, that is a mismatch that must be exposed during boot. Delaying
/// it until runtime produces symptoms like sporadic truncation of a particular command, with no obvious
/// connection to the capacity value.
/// pub struct Limits { pub max_command: u32, ... } (boot.rs:49-61)
pub struct Limits {
    pub max_command: u32,
    pub max_response: u32,
    pub max_object_context: u32,
    pub max_session_context: u32,
}

// ------------------------------------------------------------------
// Image spec faces of this layer
// ------------------------------------------------------------------

/// The full request image of a no-sessions boot command: the
/// ST_NO_SESSIONS tag, the total size word, the command code, then
/// the payload (the one-shot fill the put_* chain mounts; every
/// command arm's contract below cites it).
pub open spec fn spec_boot_image(code: u32, total: u32, payload: Seq<u8>) -> Seq<u8> {
    be16_bytes_spec(ST_NO_SESSIONS)
        .add(be32_bytes_spec(total))
        .add(be32_bytes_spec(code))
        .add(payload)
}

/// The full 22-byte capability-query packet image property() builds.
pub open spec fn spec_boot_cap_image(pt: u32) -> Seq<u8> {
    spec_boot_image(
        CC_GET_CAPABILITY,
        (BOOT_CMD_MAX as u32),
        be32_bytes_spec(CAP_TPM_PROPERTIES)
            .add(be32_bytes_spec(pt))
            .add(be32_bytes_spec(1u32)),
    )
}

/// The count word of a GetCapability property response, restated
/// over the response-buffer view (the payload's count field sits at
/// payload bytes 5..9, i.e. response-buffer bytes 15..19; the
/// slice-typed rsp.rs getcap_wire_count's formula, an
/// Origin-noted lowering -- identical formula over the buffer the
/// arms must name).
pub open spec fn spec_rsp_prop_count(rbuf: Seq<u8>) -> int {
    if (19 as int) <= (rbuf.len() as int) {
        16777216 * (rbuf.index(15) as int)
            + 65536 * (rbuf.index(16) as int)
            + 256 * (rbuf.index(17) as int)
            + (rbuf.index(18) as int)
    } else {
        0
    }
}

/// The first property value word of a GetCapability property
/// response, restated over the response-buffer view (payload value
/// bytes 13..17 == response-buffer bytes 23..27; rsp.rs
/// prop_wire_value's formula, same lowering note).
pub open spec fn spec_rsp_prop_value(rbuf: Seq<u8>) -> int {
    if (27 as int) <= (rbuf.len() as int) {
        16777216 * (rbuf.index(23) as int)
            + 65536 * (rbuf.index(24) as int)
            + 256 * (rbuf.index(25) as int)
            + (rbuf.index(26) as int)
    } else {
        0
    }
}

// ------------------------------------------------------------------
// Boot (boot.rs:62-68)
// ------------------------------------------------------------------

/// Origin Rust: pub struct Boot<P: TisPhy> {
///     x: Xfer<P>,
///     /// Command temporary buffer. Private: all guarantees about packet length fields in this layer rely on
///     /// the fact that external code cannot modify it.
///     cbuf: [u8; BOOT_CMD_MAX],
///     rbuf: [u8; BOOT_RSP_MAX],
/// } (boot.rs:62-68)
/// Field visibility opened pub (Origin note, the session.rs /
/// cursor.rs precedent): the twin's public postconditions speak
/// about the assembled packet image and the response-buffer words;
/// upstream keeps all three fields private, runtime layout and
/// values unchanged.
pub struct Boot<P: TisPhy> {
    pub x: Xfer<P>,
    /// Command temporary buffer. Private: all guarantees about packet length fields in this layer rely on
    /// the fact that external code cannot modify it.
    pub cbuf: [u8; BOOT_CMD_MAX],
    pub rbuf: [u8; BOOT_RSP_MAX],
}

impl<P: TisPhy> Boot<P> {
    /// Origin Rust: pub fn new(x: Xfer<P>) -> Self {
    ///     Boot { x, cbuf: [0u8; BOOT_CMD_MAX], rbuf: [0u8; BOOT_RSP_MAX] }
    /// } (boot.rs:70-76; the fresh-buffer all-zero face is not
    /// stated in a spec position on a generic-receiver struct --
    /// the chip.rs CtxIo::new precedent of #T5-5; the zero-init has
    /// no downstream spec consumer in this tree)
    pub exec fn new(x: Xfer<P>) -> (b: Boot<P>)
        ensures
            b.x == x,
    {
        Boot {
            x,
            cbuf: [0u8; BOOT_CMD_MAX],
            rbuf: [0u8; BOOT_RSP_MAX],
        }
    }

    /// Origin Rust: /// Return the link and end the boot phase.
    /// pub fn finish(self) -> Xfer<P> { self.x } (boot.rs:77-80)
    /// By-value receiver: the param name in the spec IS the entry
    /// value (the #T4-9 discipline), so the identity is stateable
    /// without old().
    pub exec fn finish(self) -> (x: Xfer<P>)
        ensures
            x.tis == self.x.tis,
            x.retries == self.x.retries,
    {
        self.x
    }

    /// Origin Rust: /// Write the packet header.
    /// ///
    /// /// The length field is fixed here in one shot and is not rewritten later. The boot commands all have
    /// compile-time constant payload lengths, so there is no need for a "write the payload first, then see
    /// how long it was." That write-back is precisely the one entry point through which the length field can
    /// drift away from the actual byte count.
    /// fn put_header(&mut self, cc: u32, total: usize) {
    ///     let hdr = build_header(ST_NO_SESSIONS, cc, total as u32);
    ///     self.cbuf[..TPM_HEADER_LEN].copy_from_slice(&hdr);
    /// } (boot.rs:81-90; copy_from_slice lowered to the ten scalar
    /// index writes, the chip.rs put_header precedent)
    pub(crate) exec fn put_header(&mut self, code: u32, total: usize)
        requires
            (total as int) <= 0xFFFF_FFFF,
        ensures
            final(self).rbuf@ == old(self).rbuf@,
            final(self).x == old(self).x,
            final(self).cbuf@.subrange(0, (TPM_HEADER_LEN as int))
                == be16_bytes_spec(ST_NO_SESSIONS)
                    .add(be32_bytes_spec((total as u32)))
                    .add(be32_bytes_spec(code)),
            forall|k: int|
                0 <= k < (TPM_HEADER_LEN as int)
                    ==> final(self).cbuf@.index(k)
                        == be16_bytes_spec(ST_NO_SESSIONS)
                            .add(be32_bytes_spec((total as u32)))
                            .add(be32_bytes_spec(code))
                            .index(k),
            forall|k: int|
                (TPM_HEADER_LEN as int) <= k < (BOOT_CMD_MAX as int)
                    ==> final(self).cbuf@.index(k) == old(self).cbuf@.index(k),
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

    /// Origin Rust: /// Write a single byte payload.
    /// fn put_u8(&mut self, off: usize, v: u8) { self.cbuf[off] = v; } (boot.rs:91-94)
    pub(crate) exec fn put_u8(&mut self, off: usize, v: u8)
        requires
            (off as int) + 1 <= (BOOT_CMD_MAX as int),
        ensures
            final(self).rbuf@ == old(self).rbuf@,
            final(self).x == old(self).x,
            final(self).cbuf@.subrange(0, (off as int))
                == old(self).cbuf@.subrange(0, (off as int)),
            forall|k: int|
                0 <= k < (off as int)
                    ==> final(self).cbuf@.index(k) == old(self).cbuf@.index(k),
            final(self).cbuf@.index((off as int)) == v,
            forall|k: int|
                0 <= k < (BOOT_CMD_MAX as int)
                    && k != (off as int)
                    ==> final(self).cbuf@.index(k) == old(self).cbuf@.index(k),
    {
        self.cbuf[off] = v;
    }

    /// Origin Rust: /// Write a big-endian u16 payload.
    /// fn put_be16(&mut self, off: usize, v: u16) {
    ///     let b = be16_bytes(v);
    ///     self.cbuf[off] = b[0]; self.cbuf[off + 1] = b[1];
    /// } (boot.rs:95-100)
    pub(crate) exec fn put_be16(&mut self, off: usize, v: u16)
        requires
            (off as int) + 2 <= (BOOT_CMD_MAX as int),
        ensures
            final(self).rbuf@ == old(self).rbuf@,
            final(self).x == old(self).x,
            final(self).cbuf@.subrange(0, (off as int))
                == old(self).cbuf@.subrange(0, (off as int)),
            forall|k: int|
                0 <= k < (off as int)
                    ==> final(self).cbuf@.index(k) == old(self).cbuf@.index(k),
            final(self).cbuf@.subrange((off as int), (off as int) + 2)
                == be16_bytes_spec(v),
            forall|k: int|
                (off as int) <= k < ((off as int) + 2)
                    ==> final(self).cbuf@.index(k) == be16_bytes_spec(v).index(k - (off as int)),
            forall|k: int|
                0 <= k < (BOOT_CMD_MAX as int)
                    && !((off as int) <= k < ((off as int) + 2))
                    ==> final(self).cbuf@.index(k) == old(self).cbuf@.index(k),
    {
        let b = be16_bytes(v);
        self.cbuf[off] = b[0];
        self.cbuf[off + 1] = b[1];
    }

    /// Origin Rust: /// Write a big-endian u32 payload.
    /// fn put_be32(&mut self, off: usize, v: u32) {
    ///     let b = be32_bytes(v);
    ///     self.cbuf[off] = b[0]; self.cbuf[off + 1] = b[1]; self.cbuf[off + 2] = b[2]; self.cbuf[off + 3] = b[3];
    /// } (boot.rs:101-108)
    pub(crate) exec fn put_be32(&mut self, off: usize, v: u32)
        requires
            (off as int) + 4 <= (BOOT_CMD_MAX as int),
        ensures
            final(self).rbuf@ == old(self).rbuf@,
            final(self).x == old(self).x,
            final(self).cbuf@.subrange(0, (off as int))
                == old(self).cbuf@.subrange(0, (off as int)),
            forall|k: int|
                0 <= k < (off as int)
                    ==> final(self).cbuf@.index(k) == old(self).cbuf@.index(k),
            final(self).cbuf@.subrange((off as int), (off as int) + 4)
                == be32_bytes_spec(v),
            forall|k: int|
                (off as int) <= k < ((off as int) + 4)
                    ==> final(self).cbuf@.index(k) == be32_bytes_spec(v).index(k - (off as int)),
            forall|k: int|
                0 <= k < (BOOT_CMD_MAX as int)
                    && !((off as int) <= k < ((off as int) + 4))
                    ==> final(self).cbuf@.index(k) == old(self).cbuf@.index(k),
    {
        let b = be32_bytes(v);
        self.cbuf[off] = b[0];
        self.cbuf[off + 1] = b[1];
        self.cbuf[off + 2] = b[2];
        self.cbuf[off + 3] = b[3];
    }

    /// Origin Rust: /// Send the assembled command and retrieve the response length and return code.
    /// ///
    /// /// The precondition "the length field equals `len`" is not mere ceremony: the link layer uses this
    /// field to decide how many bytes to push onto the bus. If the field does not match the actual value,
    /// the device and the host will both wait for each other and time out. Writing it as a precondition
    /// here means that this fact is ensured by the postcondition of the assembler, rather than trusting
    /// each call site to remember it.
    /// fn exec(&mut self, len: usize) -> Result<(usize, u32), BootErr> {
    ///     if !self.x.ready() { return Err(BootErr::NotReady); }
    ///     match self.x.run(&self.cbuf, len, &mut self.rbuf) {
    ///         Ok((n, rc)) => Ok((n, rc)),
    ///         Err(e) => Err(BootErr::Bus(e)),
    ///     }
    /// } (boot.rs:109-124)
    /// The BadCommand face below closes the doc's discipline from
    /// the other side: a BadCommand exit means the PASSED image was
    /// not well-formed at the gate, which each image contract below
    /// refutes (the "never trips the link gate" theorem of this
    /// layer's four commands).
    pub(crate) exec fn exec(&mut self, len: usize) -> (r: Result<(usize, u32), BootErr>)
        requires
            (len as int) <= (BOOT_CMD_MAX as int),
        ensures
            final(self).x.retries == old(self).x.retries,
            final(self).cbuf@ == old(self).cbuf@,
            match r {
                Result::Ok((n, rc)) =>
                    !final(self).x.tis.held
                        && (TPM_HEADER_LEN as int) <= (n as int)
                        && (n as int) <= (BOOT_RSP_MAX as int)
                        && (final(self).rbuf@).len() == (BOOT_RSP_MAX as int)
                        && (n as int) == wire_be32(final(self).rbuf@, 2)
                        && wire_be32(final(self).rbuf@, 6) == (rc as int),
                Result::Err(BootErr::NotReady) =>
                    final(self).x.tis.held == old(self).x.tis.held,
                Result::Err(BootErr::Bus(e)) =>
                    match e {
                        XferErr::BadCommand => !cmd_wf_spec(final(self).cbuf@, len as int),
                        _ => !old(self).x.tis.held ==> !final(self).x.tis.held,
                    },
                Result::Err(_) => false,
            },
    {
        if !self.x.ready() {
            return Result::Err(BootErr::NotReady);
        }
        match self.x.run(&self.cbuf, len, &mut self.rbuf) {
            Result::Ok((n, rc)) => {
                proof {
                    assert((self.rbuf@).len() == (BOOT_RSP_MAX as int));
                    assert(wire_be32(self.rbuf@, 2) == (n as int));
                    assert(wire_be32(self.rbuf@, 6) == (rc as int));
                }
                Result::Ok((n, rc))
            }
            Result::Err(e) => Result::Err(BootErr::Bus(e)),
        }
    }

    /// Origin Rust: /// Declare the sender's startup mode.
    /// ///
    /// /// "Already started" is treated as success. The device startup state is defined by the power cycle, but
    /// /// this side may take over after an earlier firmware has already initialized the device. In that case,
    /// /// re-sending a startup command receives a rejection telling us "the required state already holds."
    /// /// Treating that as a failure would cause the driver to reject loading on a perfectly normal platform.
    /// ///
    /// /// Conversely, any other non-zero return code is reported as-is, without secondary interpretation.
    /// pub fn startup(&mut self, su: u16) -> Result<(), BootErr> (boot.rs:125-147)
    pub exec fn startup(&mut self, su: u16) -> (r: Result<(), BootErr>)
        ensures
            final(self).x.retries == old(self).x.retries,
            final(self).cbuf@.subrange(0, ((TPM_HEADER_LEN as int) + 2))
                == spec_boot_image(
                    CC_STARTUP,
                    ((TPM_HEADER_LEN + 2) as u32),
                    be16_bytes_spec(su),
                ),
            match r {
                Result::Ok(()) => !final(self).x.tis.held,
                Result::Err(BootErr::NotReady) => true,
                Result::Err(BootErr::Rc(rc)) =>
                    rc != RC_SUCCESS
                        && rc != RC_INITIALIZE
                        && wire_be32(final(self).rbuf@, 6) == (rc as int)
                        && (TPM_HEADER_LEN as int) <= wire_be32(final(self).rbuf@, 2)
                        && wire_be32(final(self).rbuf@, 2) <= (BOOT_RSP_MAX as int),
                Result::Err(BootErr::Bus(XferErr::BadCommand)) => false,
                Result::Err(BootErr::Bus(_)) =>
                    !old(self).x.tis.held ==> !final(self).x.tis.held,
                Result::Err(_) => false,
            },
    {
        let total = TPM_HEADER_LEN + 2;
        self.put_header(CC_STARTUP, total);
        self.put_be16(TPM_HEADER_LEN, su);
        proof {
            header_face_axioms();
            let hdr = be16_bytes_spec(ST_NO_SESSIONS)
                .add(be32_bytes_spec((total as u32)))
                .add(be32_bytes_spec(CC_STARTUP));
            let pay = be16_bytes_spec(su);
            assert forall|k: int| 0 <= k < 10 implies self.cbuf@.index(k) == hdr.index(k) by {}
            assert forall|k: int| 0 <= k < 2 implies self.cbuf@.index(10 + k) == pay.index(k) by {}
            boot_img_top(
                self.cbuf@,
                hdr,
                pay,
                spec_boot_image(CC_STARTUP, (total as u32), pay),
            );
        }
        match self.exec(total) {
            Result::Ok((_n, rc)) => {
                if rc == RC_SUCCESS || rc == RC_INITIALIZE {
                    Result::Ok(())
                } else {
                    Result::Err(BootErr::Rc(rc))
                }
            }
            Result::Err(e) => Result::Err(e),
        }
    }

    /// Origin Rust: /// Shut down.
    /// ///
    /// /// Unlike startup, this path does not ignore any non-zero return code: if shutdown does not succeed,
    /// the device will assume the previous power cycle ended abnormally and will reset part of its state
    /// the next time it powers up. The caller must know this.
    /// pub fn shutdown(&mut self, su: u16) -> Result<(), BootErr> (boot.rs:148-167)
    pub exec fn shutdown(&mut self, su: u16) -> (r: Result<(), BootErr>)
        ensures
            final(self).x.retries == old(self).x.retries,
            final(self).cbuf@.subrange(0, ((TPM_HEADER_LEN as int) + 2))
                == spec_boot_image(
                    CC_SHUTDOWN,
                    ((TPM_HEADER_LEN + 2) as u32),
                    be16_bytes_spec(su),
                ),
            match r {
                Result::Ok(()) => !final(self).x.tis.held,
                Result::Err(BootErr::NotReady) => true,
                Result::Err(BootErr::Rc(rc)) =>
                    rc != RC_SUCCESS
                        && wire_be32(final(self).rbuf@, 6) == (rc as int)
                        && (TPM_HEADER_LEN as int) <= wire_be32(final(self).rbuf@, 2)
                        && wire_be32(final(self).rbuf@, 2) <= (BOOT_RSP_MAX as int),
                Result::Err(BootErr::Bus(XferErr::BadCommand)) => false,
                Result::Err(BootErr::Bus(_)) =>
                    !old(self).x.tis.held ==> !final(self).x.tis.held,
                Result::Err(_) => false,
            },
    {
        let total = TPM_HEADER_LEN + 2;
        self.put_header(CC_SHUTDOWN, total);
        self.put_be16(TPM_HEADER_LEN, su);
        proof {
            header_face_axioms();
            let hdr = be16_bytes_spec(ST_NO_SESSIONS)
                .add(be32_bytes_spec((total as u32)))
                .add(be32_bytes_spec(CC_SHUTDOWN));
            let pay = be16_bytes_spec(su);
            assert forall|k: int| 0 <= k < 10 implies self.cbuf@.index(k) == hdr.index(k) by {}
            assert forall|k: int| 0 <= k < 2 implies self.cbuf@.index(10 + k) == pay.index(k) by {}
            boot_img_top(
                self.cbuf@,
                hdr,
                pay,
                spec_boot_image(CC_SHUTDOWN, (total as u32), pay),
            );
        }
        match self.exec(total) {
            Result::Ok((_n, rc)) => {
                if rc == RC_SUCCESS {
                    Result::Ok(())
                } else {
                    Result::Err(BootErr::Rc(rc))
                }
            }
            Result::Err(e) => Result::Err(e),
        }
    }

    /// Origin Rust: /// Trigger self-test. When `full` is true, all algorithms are re-tested; otherwise only the ones not
    /// yet tested are checked.
    /// ///
    /// /// "Still testing" is treated as success, for a different reason than the startup case: the semantics
    /// of this command are "start testing," not "testing is complete." If the device replies that it is
    /// still testing, that is actually proof that the command took effect. The final self-test result must
    /// be queried separately; this layer does not assume that responsibility. Treating "started" and
    /// "passed" as the same return value would make the caller believe it received the latter.
    /// pub fn self_test(&mut self, full: bool) -> Result<(), BootErr> (boot.rs:168-195)
    pub exec fn self_test(&mut self, full: bool) -> (r: Result<(), BootErr>)
        ensures
            final(self).x.retries == old(self).x.retries,
            final(self).cbuf@.subrange(0, ((TPM_HEADER_LEN as int) + 1))
                == spec_boot_image(
                    CC_SELF_TEST,
                    ((TPM_HEADER_LEN + 1) as u32),
                    Seq::<u8>::new(1, |_: int| if full { SELF_TEST_FULL } else { SELF_TEST_INCREMENTAL }),
                ),
            match r {
                Result::Ok(()) => !final(self).x.tis.held,
                Result::Err(BootErr::NotReady) => true,
                Result::Err(BootErr::Rc(rc)) =>
                    rc != RC_SUCCESS
                        && rc != RC_TESTING
                        && wire_be32(final(self).rbuf@, 6) == (rc as int)
                        && (TPM_HEADER_LEN as int) <= wire_be32(final(self).rbuf@, 2)
                        && wire_be32(final(self).rbuf@, 2) <= (BOOT_RSP_MAX as int),
                Result::Err(BootErr::Bus(XferErr::BadCommand)) => false,
                Result::Err(BootErr::Bus(_)) =>
                    !old(self).x.tis.held ==> !final(self).x.tis.held,
                Result::Err(_) => false,
            },
    {
        let total = TPM_HEADER_LEN + 1;
        self.put_header(CC_SELF_TEST, total);
        let arg = if full {
            SELF_TEST_FULL
        } else {
            SELF_TEST_INCREMENTAL
        };
        self.put_u8(TPM_HEADER_LEN, arg);
        proof {
            header_face_axioms();
            let pay = Seq::<u8>::new(1, |_: int| if full { SELF_TEST_FULL } else { SELF_TEST_INCREMENTAL });
            let hdr = be16_bytes_spec(ST_NO_SESSIONS)
                .add(be32_bytes_spec((total as u32)))
                .add(be32_bytes_spec(CC_SELF_TEST));
            assert(pay.len() == 1);
            assert(pay.index(0) == if full { SELF_TEST_FULL } else { SELF_TEST_INCREMENTAL });
            assert(arg == if full { SELF_TEST_FULL } else { SELF_TEST_INCREMENTAL });
            assert forall|k: int| 0 <= k < 10 implies self.cbuf@.index(k) == hdr.index(k) by {}
            assert forall|k: int| 0 <= k < 1 implies self.cbuf@.index(10 + k) == pay.index(k) by {}
            boot_img_top(
                self.cbuf@,
                hdr,
                pay,
                spec_boot_image(CC_SELF_TEST, (total as u32), pay),
            );
        }
        match self.exec(total) {
            Result::Ok((_n, rc)) => {
                if rc == RC_SUCCESS || rc == RC_TESTING {
                    Result::Ok(())
                } else {
                    Result::Err(BootErr::Rc(rc))
                }
            }
            Result::Err(e) => Result::Err(e),
        }
    }

    /// Origin Rust: /// Query one fixed property value.
    /// ///
    /// /// Only one property is queried at a time. A batched query could save a few round trips, but the key
    /// value pairs in the response are ordered by the device, and code that expects them to line up one by
    /// one must handle missing entries, reordering, and duplicates. The boot phase only asks for four
    /// properties in total; the round trips saved are not worth the extra branches.
    /// pub fn property(&mut self, pt: u32) -> Result<u32, BootErr> (boot.rs:196-220)
    /// The ok face: a 27-byte minimum response, an accepted
    /// response tag, a nonzero property count, and the returned
    /// value word of the FIRST pair of whatever the device shipped
    /// -- the queried property's identity is NOT re-validated (the
    /// "ordered by the device" sentence above; recorded as a
    /// design caveat in the batch notes, not a suspect: no upstream
    /// doc claims identity checking here).
    pub exec fn property(&mut self, pt: u32) -> (r: Result<u32, BootErr>)
        ensures
            final(self).x.retries == old(self).x.retries,
            final(self).cbuf@ == spec_boot_cap_image(pt),
            match r {
                Result::Ok(v) =>
                    !final(self).x.tis.held
                        && wire_be32(final(self).rbuf@, 6) == (RC_SUCCESS as int)
                        && (27 as int) <= wire_be32(final(self).rbuf@, 2)
                        && wire_be32(final(self).rbuf@, 2) <= (BOOT_RSP_MAX as int)
                        && (be16_of(final(self).rbuf@.index(0), final(self).rbuf@.index(1)) == (ST_NO_SESSIONS as int)
                            || be16_of(final(self).rbuf@.index(0), final(self).rbuf@.index(1)) == (super::msg::ST_SESSIONS as int))
                        && spec_rsp_prop_count(final(self).rbuf@) != 0
                        && (v as int) == spec_rsp_prop_value(final(self).rbuf@),
                Result::Err(BootErr::Rc(rc)) =>
                    rc != RC_SUCCESS
                        && wire_be32(final(self).rbuf@, 6) == (rc as int)
                        && (TPM_HEADER_LEN as int) <= wire_be32(final(self).rbuf@, 2)
                        && wire_be32(final(self).rbuf@, 2) <= (BOOT_RSP_MAX as int),
                Result::Err(BootErr::NotReady) => true,
                Result::Err(BootErr::Bus(XferErr::BadCommand)) => false,
                Result::Err(BootErr::Bus(_)) =>
                    !old(self).x.tis.held ==> !final(self).x.tis.held,
                Result::Err(BootErr::Parse(pe)) =>
                    match pe {
                        ParseError::Truncated =>
                            wire_be32(final(self).rbuf@, 2) < 19
                                || (((19 as int) <= wire_be32(final(self).rbuf@, 2)
                                    && wire_be32(final(self).rbuf@, 2) < 27)
                                    && spec_rsp_prop_count(final(self).rbuf@) != 0),
                        ParseError::Malformed =>
                            (TPM_HEADER_LEN as int) <= wire_be32(final(self).rbuf@, 2)
                                && !(be16_of(final(self).rbuf@.index(0), final(self).rbuf@.index(1)) == (ST_NO_SESSIONS as int)
                                    || be16_of(final(self).rbuf@.index(0), final(self).rbuf@.index(1)) == (super::msg::ST_SESSIONS as int)),
                        ParseError::Unsupported =>
                            (19 as int) <= wire_be32(final(self).rbuf@, 2)
                                && spec_rsp_prop_count(final(self).rbuf@) == 0,
                        _ => false,
                    },
                Result::Err(_) => false,
            },
    {
        let total = TPM_HEADER_LEN + 12;
        self.put_header(CC_GET_CAPABILITY, total);
        self.put_be32(TPM_HEADER_LEN, CAP_TPM_PROPERTIES);
        self.put_be32(TPM_HEADER_LEN + 4, pt);
        self.put_be32(TPM_HEADER_LEN + 8, 1);
        proof {
            header_face_axioms();
            let hdr = be16_bytes_spec(ST_NO_SESSIONS)
                .add(be32_bytes_spec((total as u32)))
                .add(be32_bytes_spec(CC_GET_CAPABILITY));
            let tail = be32_bytes_spec(CAP_TPM_PROPERTIES)
                .add(be32_bytes_spec(pt))
                .add(be32_bytes_spec(1u32));
            assert forall|k: int| 0 <= k < 10 implies self.cbuf@.index(k) == hdr.index(k) by {}
            assert forall|k: int| 0 <= k < 12 implies self.cbuf@.index(10 + k) == tail.index(k) by {}
            boot_cap_tail_window(self.cbuf@, pt);
            boot_img_top(self.cbuf@, hdr, tail, spec_boot_cap_image(pt));
        }
        let n = match self.exec(total) {
            Result::Ok((n, rc)) => {
                if rc != RC_SUCCESS {
                    return Result::Err(BootErr::Rc(rc));
                }
                n
            }
            Result::Err(e) => return Result::Err(e),
        };
        let raw = &self.rbuf[0..n];
        proof {
            assert((self.rbuf@).len() == (BOOT_RSP_MAX as int));
            assert(raw@ == self.rbuf@.subrange(0, (n as int)));
            assert(raw@.len() == (n as int));
            assert forall|j: int|
                0 <= j < (n as int)
                    implies raw@.index(j) == self.rbuf@.index(j)
            by {
                assert(raw@.index(j) == self.rbuf@.subrange(0, (n as int)).index(j));
            }
        }
        let rsp = match parse_response(raw) {
            Result::Ok(resp) => resp,
            Result::Err(pe) => return Result::Err(BootErr::Parse(pe)),
        };
        proof {
            // body view: the parse's ok arm split, mapped onto the
            // response-buffer tail; the count/value/tag index chains
            // ride on it so BOTH the ok and the error arms of the
            // property parser inherit the twin equalities
            let n2 = (raw@.len() as int);
            vstd::seq::lemma_seq_subrange_composition::<u8>(
                self.rbuf@, 0, (n as int), (TPM_HEADER_LEN as int), (n as int));
            assert(rsp.body@ == raw@.subrange((TPM_HEADER_LEN as int), n2));
            assert(rsp.body@ == self.rbuf@.subrange((TPM_HEADER_LEN as int), (n as int)));
            vstd::seq::lemma_seq_ext_equal::<u8>(
                rsp.body@, self.rbuf@.subrange((TPM_HEADER_LEN as int), (n as int)));
            assert(rsp.body@.len() == (n as int) - (TPM_HEADER_LEN as int));
            assert forall|j: int|
                0 <= j < (rsp.body@.len() as int)
                    implies rsp.body@.index(j) == self.rbuf@.index((TPM_HEADER_LEN as int) + j)
            by {
                assert(rsp.body@.index(j) == raw@.subrange((TPM_HEADER_LEN as int), n2).index(j));
                assert(raw@.subrange((TPM_HEADER_LEN as int), n2).index(j)
                    == raw@.index((TPM_HEADER_LEN as int) + j));
                assert(raw@.index((TPM_HEADER_LEN as int) + j) == self.rbuf@.index((TPM_HEADER_LEN as int) + j));
            }
        }
        match super::rsp::parse_tpm_property(rsp.body) {
            Result::Ok(v) => {
                proof {
                    // count/value words: the parser's ok face gives
                    // the 17-byte body floor, so both arithmetical
                    // twins are live; the chains are spelled so the
                    // sums instantiate without trigger hunting
                    assert(super::rsp::getcap_wire_count(rsp.body) != 0);
                    assert(super::rsp::prop_wire_value(rsp.body) == (v as int));
                    assert(17 <= (rsp.body@.len() as int));
                    assert(27 <= (n as int));
                    assert(rsp.body@.index(5) == self.rbuf@.index(15));
                    assert(rsp.body@.index(6) == self.rbuf@.index(16));
                    assert(rsp.body@.index(7) == self.rbuf@.index(17));
                    assert(rsp.body@.index(8) == self.rbuf@.index(18));
                    assert(rsp.body@.index(13) == self.rbuf@.index(23));
                    assert(rsp.body@.index(14) == self.rbuf@.index(24));
                    assert(rsp.body@.index(15) == self.rbuf@.index(25));
                    assert(rsp.body@.index(16) == self.rbuf@.index(26));
                    assert(super::rsp::getcap_wire_count(rsp.body)
                        == spec_rsp_prop_count(self.rbuf@));
                    assert(super::rsp::prop_wire_value(rsp.body)
                        == spec_rsp_prop_value(self.rbuf@));
                }
                Result::Ok(v)
            }
            Result::Err(pe) => {
                proof {
                    // the property parser's reachable error shapes
                    // (Truncated, Unsupported) both carry the 9-byte
                    // body floor on their live-count faces, but the
                    // Truncated face ALSO admits the short-body side
                    // (body < 9, where the slice-typed count guard
                    // inactivates and no count claim survives); the
                    // case split keeps both honest
                    let blen = (rsp.body@.len() as int);
                    if blen < 9 {
                        // short-body side: n < 19, and the ensure's
                        // first disjunct rides on the size word
                    } else {
                        assert(rsp.body@.index(5) == self.rbuf@.index(15));
                        assert(rsp.body@.index(6) == self.rbuf@.index(16));
                        assert(rsp.body@.index(7) == self.rbuf@.index(17));
                        assert(rsp.body@.index(8) == self.rbuf@.index(18));
                        assert(super::rsp::getcap_wire_count(rsp.body)
                            == spec_rsp_prop_count(self.rbuf@));
                    }
                }
                Result::Err(BootErr::Parse(pe))
            }
        }
    }

    /// Origin Rust: /// Query all four dimensions and reconcile them against the static reservations of this driver.
    /// ///
    /// /// If reconciliation fails, report an error and do not degrade. Degradation would mean there is a
    /// runtime path of "buffer too small, so split / truncate / skip," and that path will never be
    /// exercised on a machine with sufficient capacity, so it will never be tested. It is better to fail
    /// to load here.
    /// pub fn probe_limits(&mut self) -> Result<Limits, BootErr> (boot.rs:221-247)
    /// The capacity checks run only after all four property reads
    /// return Ok, so the Capacity arm still certifies a cleanly
    /// parsed FINAL round. max_command is returned unreconciled --
    /// upstream checks exactly the three dimensions below.
    pub exec fn probe_limits(&mut self) -> (r: Result<Limits, BootErr>)
        ensures
            final(self).x.retries == old(self).x.retries,
            match r {
                Result::Ok(l) =>
                    !final(self).x.tis.held
                        && (l.max_response as int) <= (MSG_MAX as int)
                        && (l.max_object_context as int) <= (MSG_MAX as int)
                        && (l.max_session_context as int) <= (MSG_MAX as int)
                        && wire_be32(final(self).rbuf@, 6) == (RC_SUCCESS as int)
                        && (l.max_session_context as int) == spec_rsp_prop_value(final(self).rbuf@)
                        && final(self).cbuf@ == spec_boot_cap_image(PT_MAX_SESSION_CONTEXT),
                Result::Err(BootErr::Capacity) =>
                    wire_be32(final(self).rbuf@, 6) == (RC_SUCCESS as int)
                        && final(self).cbuf@ == spec_boot_cap_image(PT_MAX_SESSION_CONTEXT),
                Result::Err(BootErr::Bus(XferErr::BadCommand)) => false,
                Result::Err(BootErr::Abi) => false,
                Result::Err(_) => true,
            },
    {
        let max_command = match self.property(PT_MAX_COMMAND_SIZE) {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        let max_response = match self.property(PT_MAX_RESPONSE_SIZE) {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        let max_object_context = match self.property(PT_MAX_OBJECT_CONTEXT) {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        let max_session_context = match self.property(PT_MAX_SESSION_CONTEXT) {
            Result::Ok(v) => v,
            Result::Err(e) => return Result::Err(e),
        };
        if max_response as usize > MSG_MAX {
            return Result::Err(BootErr::Capacity);
        }
        if max_object_context as usize > MSG_MAX {
            return Result::Err(BootErr::Capacity);
        }
        if max_session_context as usize > MSG_MAX {
            return Result::Err(BootErr::Capacity);
        }
        Result::Ok(Limits {
            max_command,
            max_response,
            max_object_context,
            max_session_context,
        })
    }
}

// ------------------------------------------------------------------
// Word-join helpers (the fill-in ladders of this layer; separate
// proof fns so each command method's own query stays cheap -- the
// T5-2 split discipline)
// ------------------------------------------------------------------

/// The two header pieces' length facts (every image's first ten
/// bytes are tag 2 + size 4 + code 4).
proof fn header_face_axioms()
{
    assert(be16_bytes_spec(ST_NO_SESSIONS).len() == 2);
    vstd::seq::lemma_seq_add_len::<u8>(be16_bytes_spec(ST_NO_SESSIONS), be32_bytes_spec(0u32));
    assert((be16_bytes_spec(ST_NO_SESSIONS).add(be32_bytes_spec(0u32))).len() == 6);
}

/// Two-window join: with the 10-byte header window and the payload
/// window in place, the whole prefix [0, 10 + payload.len()) of the
/// command buffer equals the full image.
proof fn boot_img_top(
    cbuf: Seq<u8>,
    hdr: Seq<u8>,
    payload: Seq<u8>,
    image: Seq<u8>,
)
    requires
        image == hdr.add(payload),
        (hdr.len() as int) == 10,
        (10 + (payload.len() as int)) <= (cbuf.len() as int),
        forall|k: int| 0 <= k < 10 ==> cbuf.index(k) == hdr.index(k),
        forall|k: int|
            0 <= k < (payload.len() as int)
                ==> cbuf.index(10 + k) == payload.index(k),
    ensures
        cbuf.subrange(0, 10 + (payload.len() as int)) == image,
{
    let total: int = 10 + (payload.len() as int);
    vstd::seq::lemma_seq_add_len::<u8>(hdr, payload);
    assert((image.len() as int) == total);
    assert((cbuf.subrange(0, total).len() as int) == total);
    assert((cbuf.subrange(0, total).len() as int) == (image.len() as int));
    assert forall|k: int|
        0 <= k < total
            implies cbuf.subrange(0, total).index(k) == image.index(k)
    by {
        vstd::seq::lemma_seq_subrange_index::<u8>(cbuf, 0, total, k);
        if k < 10 {
            vstd::seq::lemma_seq_add_index1::<u8>(hdr, payload, k);
            assert(image.index(k) == hdr.index(k));
        } else {
            vstd::seq::lemma_seq_add_index2::<u8>(hdr, payload, k);
            assert(image.index(k) == payload.index(k - (hdr.len() as int)));
        }
    }
    vstd::seq::lemma_seq_ext_equal::<u8>(cbuf.subrange(0, total), image);
}

/// The capability payload window: the three be32 payload writes of
/// property() join into the 12-byte query tail window [10, 22).
proof fn boot_cap_tail_window(cbuf: Seq<u8>, pt: u32)
    requires
        (22 as int) <= cbuf.len(),
        forall|k: int|
            0 <= k < 12
                ==> cbuf.index(10 + k)
                    == be32_bytes_spec(CAP_TPM_PROPERTIES)
                        .add(be32_bytes_spec(pt))
                        .add(be32_bytes_spec(1u32))
                        .index(k),
    ensures
        cbuf.subrange(10, 22)
            == be32_bytes_spec(CAP_TPM_PROPERTIES)
                .add(be32_bytes_spec(pt))
                .add(be32_bytes_spec(1u32)),
{
    let tail = be32_bytes_spec(CAP_TPM_PROPERTIES)
        .add(be32_bytes_spec(pt))
        .add(be32_bytes_spec(1u32));
    assert(be32_bytes_spec(CAP_TPM_PROPERTIES).len() == 4);
    assert(be32_bytes_spec(pt).len() == 4);
    vstd::seq::lemma_seq_add_len::<u8>(be32_bytes_spec(CAP_TPM_PROPERTIES), be32_bytes_spec(pt));
    vstd::seq::lemma_seq_add_len::<u8>(be32_bytes_spec(CAP_TPM_PROPERTIES).add(be32_bytes_spec(pt)), be32_bytes_spec(1u32));
    assert(tail.len() == 12);
    assert(cbuf.subrange(10, 22).len() == 12);
    assert forall|k: int|
        0 <= k < 12 implies cbuf.subrange(10, 22).index(k) == tail.index(k)
    by {
        vstd::seq::lemma_seq_subrange_index::<u8>(cbuf, 10, 22, k);
    }
    vstd::seq::lemma_seq_ext_equal::<u8>(cbuf.subrange(10, 22), tail);
}

/// Origin Rust: /// Move from a freshly established link to "can carry traffic," while also returning the device
/// capacity.
/// ///
/// /// The order is fixed by dependency, not habit:
/// ///
/// /// 1. **Host ABI self-check result** is supplied by the caller via `abi_ok` and decided first here. ...
/// /// 2. **Startup**. Before the device receives the startup command, it rejects most commands.
/// /// 3. **Self-test**. This must be triggered before any business commands arrive, allowing it to run in
/// /// parallel with subsequent operations.
/// /// 4. **Capacity reconciliation**. ...
/// ///
/// /// Any failure in the middle immediately returns and the link is discarded. This layer has no "partial
/// /// success" state -- if the boot process is not complete, the local side cannot say where the device is
/// currently at.
/// pub fn bring_up<P: TisPhy>(
///     x: Xfer<P>, su: u16, abi_ok: bool,
/// ) -> Result<(Xfer<P>, Limits), BootErr> (boot.rs:249-289)
pub exec fn bring_up<P: TisPhy>(
    x: Xfer<P>,
    su: u16,
    abi_ok: bool,
) -> (r: Result<(Xfer<P>, Limits), BootErr>)
    ensures
        match r {
            Result::Ok((migrated, lim)) =>
                !migrated.tis.held
                    && migrated.retries == x.retries
                    && (lim.max_response as int) <= (MSG_MAX as int)
                    && (lim.max_object_context as int) <= (MSG_MAX as int)
                    && (lim.max_session_context as int) <= (MSG_MAX as int),
            Result::Err(BootErr::Abi) => !abi_ok,
            Result::Err(_) => abi_ok,
        },
{
    if !abi_ok {
        return Result::Err(BootErr::Abi);
    }
    let mut b = Boot::new(x);
    match b.startup(su) {
        Result::Ok(()) => {}
        Result::Err(e) => return Result::Err(e),
    }
    match b.self_test(false) {
        Result::Ok(()) => {}
        Result::Err(e) => return Result::Err(e),
    }
    match b.probe_limits() {
        Result::Ok(lim) => {
            proof {
                assert(b.x.retries == x.retries);
                assert(!b.x.tis.held);
            }
            let migrated = b.finish();
            Result::Ok((migrated, lim))
        }
        Result::Err(e) => return Result::Err(e),
    }
}

} // verus!
