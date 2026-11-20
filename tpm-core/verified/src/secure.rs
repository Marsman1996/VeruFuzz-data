//! tpm-core 0.1.4 the authorized command wrapper (src/secure.rs)
//! -- Verus translation.
//!
//! The security narrative of this module is command construction on
//! the way in and credential-gated extraction on the way out:
//!  - CmdLayout is honestly caller-supplied data (upstream doc:
//!    knowledge of the command layer; this layer "is responsible
//!    only for checking that these partitions do not overlap and
//!    then filling them in"). The T4 audit (out/kverus-run/T4/
//!    notes.md, S-T4-1, CONFIRMED live) showed NO such check
//!    exists anywhere in the runtime twin: write_cmd_session and
//!    finalize receive every offset unchecked and Guarded::invoke
//!    forwards them unchecked. The twin therefore re-erects the
//!    boundaries on the public face of invoke as requires rows
//!    (the two-state answer the T4 dependency-closure section
//!    asked for: pin the bounds in the contract, or self-certify
//!    from a layout checker -- upstream has no checker, so the
//!    twin pins the contract and records the repair path).
//!  - invoke's ok arm is the composed byte-for-byte face: the
//!    command view after the round is the entry view with the
//!    73-byte authorization area filled in (session record from
//!    write_cmd_session's exact layout, MAC window from
//!    finalize's oracle face over the post-fill parameter bytes),
//!    and an Ok credential certifies that the response MAC
//!    recomputes exactly (check_response's gold face relayed
//!    over the response buffer).
//!  - params is the ONLY exit for response bytes: the upstream
//!    doc says its "precondition requires a credential matching
//!    the current temporary buffer contents" and release's doc
//!    says "their preconditions require the packet to match
//!    byte-for-byte the contents at creation time" -- like
//!    begin's phantom rng.draws() (S-T4-4), those verified-
//!    sibling preconditions did not survive into the runtime
//!    twin (nothing enforces buffer identity: a stale credential
//!    or a credential from another Guarded still reads bytes).
//!    The twin re-erects the promised precondition for real:
//!    params carries the byte-for-byte-matching requires, and
//!    invoke's Ok arm discharges it.

use vstd::prelude::*;

verus! {

use super::auth::{
    spec_auth_hmac, spec_cp_hash, spec_rp_hash, write_cmd_session, AuthErr,
    CMD_SESSION_LEN, SA_CONTINUE_SESSION, SESS_HMAC_OFF, ST_SESSIONS,
};
use super::chip::MSG_MAX;
use super::crypto::{
    HmacSha256Ctx, NonceSource, PASSPHRASE_MAX, NONCE_LEN, SHA256_LEN, Sha256Ctx,
};
use super::cursor::{be16_bytes_spec, be32_bytes_spec};
use super::endian::{be16_of, be32_of};
use super::phy::TisPhy;
use super::rewrite::wire_be32;
use super::session::{spec_key_material, AuthSession, SessionState};
use super::xfer::{cmd_wf_spec, Xfer, XferErr, RC_SUCCESS};

// ------------------------------------------------------------------
// CmdLayout (secure.rs:10-31)
// ------------------------------------------------------------------

/// Origin Rust: /// Partition of an authorized command within the buffer.
/// ///
/// /// This is provided by the caller rather than inferred by this layer: the partition depends on how
/// /// many handles the command has and how its parameters are arranged, which is command-layer
/// /// knowledge. This layer is responsible only for checking that these partitions do not overlap and
/// /// then filling them in.
/// pub struct CmdLayout {
///     /// Total command length. It must match the length field in the packet header; this is checked by
///     /// the link layer.
///     pub len: usize,
///     /// Start of the authorization area.
///     pub sess_off: usize,
///     /// This session's index within the authorization area.
///     pub index: usize,
///     /// Start of the parameter area.
///     pub param_off: usize,
///     /// Length of the parameter area.
///     pub param_len: usize,
///     /// Number of handles in the response. The digest covers the portion after the handles, and if this
///     /// count is wrong, the entire offset layout becomes wrong.
///     pub rhandles: usize,
/// } (src/secure.rs:10-31)
/// Audit verdict carried forward (T4, S-T4-1, confirmed live): the
/// doc sentence "This layer is responsible only for checking that
/// these partitions do not overlap and then filling them in" is
/// NOT implemented anywhere in the crate -- invoke forwards
/// sess_off / param_off / param_len / rhandles unchecked into
/// write_cmd_session, finalize and check_response, which is the
/// exact panic row of S-T4-1. The twin therefore does NOT erect
/// this sentence as a spec; the required bounds are pinned as
/// requires on invoke, and the doc's other sentence ("It must
/// match the length field in the packet header; this is checked by
/// the link layer") is verified as the cmd_wf rejection face of
/// invoke's Bus(BadCommand) arm. The spec predicate below is the
/// repair path: this IS the check the doc claims, offered so the
/// upstream fix (a runtime layout checker or an enforced type
/// state) has a ready-made contract; with it adopted, every
/// requires row of invoke follows mechanically (the batch harness
/// ut_invoke_layout_discharge proves the discharge).
pub struct CmdLayout {
    /// Total command length. It must match the length field in the packet header; this is checked by
    /// the link layer.
    pub len: usize,
    /// Start of the authorization area.
    pub sess_off: usize,
    /// This session's index within the authorization area.
    pub index: usize,
    /// Start of the parameter area.
    pub param_off: usize,
    /// Length of the parameter area.
    pub param_len: usize,
    /// Number of handles in the response. The digest covers the portion after the handles, and if this
    /// count is wrong, the entire offset layout becomes wrong.
    pub rhandles: usize,
}

/// The partition discipline the upstream CmdLayout doc claims to
/// check: the fixed header (10 bytes plus the handle area prefix),
/// the parameter area and the 73-byte authorization area are
/// pairwise disjoint and all inside the declared command. The
/// twin's invoke carries only the panic-bounds; if upstream
/// adopts this checker, the disjointness facts (auth window
/// within the packet, the digest area outside both) become
/// caller-provable.
pub open spec fn spec_layout_disjoint(lay: CmdLayout) -> bool {
    ((super::auth::HEADER_LEN as int) + 4) <= (lay.sess_off as int)
        && (lay.param_off as int) + (lay.param_len as int) <= (lay.sess_off as int)
        && (lay.sess_off as int) + (CMD_SESSION_LEN as int) <= (lay.len as int)
        && (lay.len as int) <= 0xFFFF_FFFF
}

// ------------------------------------------------------------------
// Wire-image spec helpers of this layer
// ------------------------------------------------------------------

/// The exact 73-byte authorization-area record that
/// write_cmd_session writes: handle (4), nonce size be16(32) (2),
/// the fresh session nonce (32), session attrs (1), hmac size
/// be16(32) (2), the all-zero placeholder the doc calls the
/// "obvious all-zero pattern" (32) -- CMD_SESSION_LEN total.
pub open spec fn spec_session_area(handle: u32, nonce: Seq<u8>, attrs: u8) -> Seq<u8> {
    be32_bytes_spec(handle)
        .add(be16_bytes_spec((NONCE_LEN as u16)))
        .add(nonce)
        .add(Seq::<u8>::new(1, |_: int| attrs))
        .add(be16_bytes_spec((NONCE_LEN as u16)))
        .add(super::auth::zero_seq32())
}

/// The command view after write_cmd_session ran: the entry view
/// with the authorization-area window [lay.sess_off, ..+73) filled
/// by the session record; total (gateway guard falls back to the
/// entry view when the window would not fit).
pub open spec fn spec_cmd_with_session_area(
    entry: Seq<u8>,
    lay: CmdLayout,
    handle: u32,
    nonce: Seq<u8>,
    attrs: u8,
) -> Seq<u8> {
    if (lay.sess_off as int) + (CMD_SESSION_LEN as int) <= entry.len() {
        entry
            .subrange(0, lay.sess_off as int)
            .add(spec_session_area(handle, nonce, attrs))
            .add(entry.subrange(
                (lay.sess_off as int) + (CMD_SESSION_LEN as int),
                entry.len() as int,
            ))
    } else {
        entry
    }
}

/// The credential-validity face: the response-buffer view carries
/// a parseable authorized response whose trailing 32 bytes are
/// exactly the MAC oracle recomputed over this session's key
/// material, the rp digest of the parameter bytes (with the
/// locally remembered ordinal), the two nonces and the session
/// attrs (the byte-for-byte content of check_response's Ok arm,
/// stated over the full fixed buffer -- the exit slice is
/// [0 .. a.hmac_off + SHA256_LEN), recoverable from the credential
/// alone; the rsp.rs slice-typed spec faces are restated over
/// Seq<u8> here because invoke's postcondition must name the
/// struct field view, an Origin-noted lowering with identical
/// formulas).
pub open spec fn spec_resp_auth_ok(
    a: super::auth::RspAuth,
    buf: Seq<u8>,
    keymat: Seq<u8>,
    ordinal: u32,
    our_nonce: Seq<u8>,
    attrs: u8,
) -> bool {
    ((a.hmac_off as int) + (SHA256_LEN as int)) <= buf.len()
        && ((super::auth::HEADER_LEN as int)
            <= ((a.hmac_off as int) + (SHA256_LEN as int)))
        && be16_of(buf.index(0), buf.index(1)) == (ST_SESSIONS as int)
        && be32_of(
            buf.index(2),
            buf.index(3),
            buf.index(4),
            buf.index(5),
        ) == ((a.hmac_off as int) + (SHA256_LEN as int))
        && ((super::auth::HEADER_LEN as int) <= (a.param_off as int))
        && ((a.param_off as int) + (a.param_len as int) <= (a.nonce_off as int))
        && ((a.nonce_off as int) + (NONCE_LEN as int) <= (a.hmac_off as int))
        && a.tpm_nonce@ == buf.subrange(
            (a.nonce_off as int),
            (a.nonce_off as int) + (NONCE_LEN as int),
        )
        && a.attrs == buf.index((a.nonce_off as int) + (NONCE_LEN as int))
        && buf.subrange(
            (a.hmac_off as int),
            (a.hmac_off as int) + (SHA256_LEN as int),
        ) == spec_auth_hmac(
            keymat,
            spec_rp_hash(
                0u32,
                ordinal,
                buf.subrange(
                    (a.param_off as int),
                    (a.param_off as int) + (a.param_len as int),
                ),
            ),
            (a.tpm_nonce)@,
            our_nonce,
            attrs,
        )
}

/// The byte-for-byte "credential matches the current temporary
/// buffer contents" precondition of the params accessor (re-erects
/// the upstream doc's promised precondition as an actual requires;
/// the runtime twin carries none).
pub open spec fn spec_credential_matches(
    t: &Authenticated,
    rbuf: Seq<u8>,
    sess: &AuthSession,
) -> bool {
    spec_resp_auth_ok(
        t.a,
        rbuf,
        spec_key_material(*sess),
        sess.ordinal,
        sess.our_nonce@,
        sess.attrs,
    )
}

// ------------------------------------------------------------------
// Authenticated / SecErr (secure.rs:32-51)
// ------------------------------------------------------------------

/// Origin Rust: /// A credential certifying that "this response
/// MAC matches". ... The location result `a` can be made public:
/// reading a few offsets does not create any capability; the
/// /// capability lies in the credential itself. The credential is created only after [`Guarded::invoke`]
/// validates successfully, and `#[non_exhaustive]` prevents external code from constructing one out of
/// /// thin air.
/// #[non_exhaustive]
/// pub struct Authenticated { pub a: RspAuth } (src/secure.rs:32-41)
/// The twin drops the #[non_exhaustive] attribute itself (a
/// downstream-crate constructor-blocking property; this tree
/// verifies as a single crate with #[path] mounts, where the
/// attribute's protection does not participate). The credential's
/// role is carried by invoke's Ok arm: the location record binds
/// to exactly the response bytes that check_response validated,
/// and no other constructor of it exists in this tree.
pub struct Authenticated {
    pub a: super::auth::RspAuth,
}

/// Origin Rust: #[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// pub enum SecErr {
///     /// Bytes did not complete a full round trip.
///     Bus(XferErr),
///     /// The device returned a non-zero return code. This type of response has no authorization area and
///     /// cannot be validated.
///     Rc(u32),
///     /// The response arrived, but authorization validation failed.
///     Auth(AuthErr),
/// } (src/secure.rs:42-51; the derives carry no Verus twin -- no
/// exec copy or ==-comparison of a SecErr happens in this tree)
pub enum SecErr {
    /// Bytes did not complete a full round trip.
    Bus(XferErr),
    /// The device returned a non-zero return code. This type of response has no authorization area and
    /// cannot be validated.
    Rc(u32),
    /// The response arrived, but authorization validation failed.
    Auth(AuthErr),
}

// ------------------------------------------------------------------
// Guarded (secure.rs:52-66)
// ------------------------------------------------------------------

/// Origin Rust: pub struct Guarded<P: TisPhy> {
///     x: Xfer<P>,
///     sess: AuthSession,
///     /// Response buffer. All guarantees of this layer rely on the fact that the caller outside the module
///     /// cannot access it.
///     rbuf: [u8; MSG_MAX],
/// } (src/secure.rs:52-58)
/// Field visibility opened pub (Origin note, the session.rs / cursor.rs
/// precedent): the twin's public postconditions speak about the
/// individual fields (the pass-through transport, the session
/// record faces and, above all, the response-buffer bytes the
/// credential-gated accessors read); upstream keeps all three
/// private, runtime layout and values unchanged.
pub struct Guarded<P: TisPhy> {
    pub x: Xfer<P>,
    /// Response buffer. All guarantees of this layer rely on the fact that the caller outside the module
    /// cannot access it.
    pub rbuf: [u8; MSG_MAX],
    pub sess: AuthSession,
}

impl<P: TisPhy> Guarded<P> {
    /// Origin Rust: pub fn new(x: Xfer<P>, sess: AuthSession) -> Self {
    ///     Guarded { x, sess, rbuf: [0u8; MSG_MAX] }
    /// } (src/secure.rs:59-66)
    pub exec fn new(x: Xfer<P>, sess: AuthSession) -> (g: Guarded<P>)
        ensures
            g.x == x,
            g.sess == sess,
    {
        Guarded {
            x,
            sess,
            rbuf: [0u8; MSG_MAX],
        }
    }

    /// Origin Rust: /// Send an authorized command; it returns only if the MAC matches.
    /// ///
    /// /// The caller must have already prepared the packet header, handle area, and parameter area and must
    /// /// leave space for the authorization area according to `lay`. The authorization area is filled by
    /// /// this function; it contains the current nonce, which is generated only when the round is finalized,
    /// /// so the caller cannot fill it in advance.
    /// ///
    /// /// All failure paths invalidate the session. Retrying with the same key after the session has failed
    /// /// gives the peer one more guessing opportunity; invalidating it forces a fresh handshake, which costs
    /// /// one round trip but prevents guessing opportunities from accumulating. (secure.rs:67-118)
    ///
    /// The requires set below is the two-state answer the T4
    /// batch's dependency-closure section asked for: upstream
    /// forwards every layout offset into the panicking callees
    /// unchecked (S-T4-1, confirmed live: invoke with a 16-byte
    /// cmd dies inside write_cmd_session before a single bus byte
    /// moves); the honest twin contract pins the callee bounds on
    /// the public face instead of re-erecting the false
    /// "this layer checks the partitions" claim. The bounds are
    /// exactly: the authorization window fits the command
    /// (write_cmd_session + finalize's sess_off bound), the
    /// parameter window fits the command (finalize's param bound),
    /// the response-handle skip arithmetic does not overflow
    /// (check_response's rhandles bound), and the session's
    /// passphrase is within its field capacity (the stored bound
    /// of every callee).
    pub exec fn invoke<S: Sha256Ctx, H: HmacSha256Ctx, R: NonceSource>(
        &mut self,
        rng: &mut R,
        cmd: &mut [u8],
        lay: CmdLayout,
        names: &[u8],
        ordinal: u32,
        attrs: u8,
    ) -> (r: Result<Authenticated, SecErr>)
        requires
            (lay.sess_off as int) + (CMD_SESSION_LEN as int) <= (cmd.len() as int),
            (lay.param_off as int) + (lay.param_len as int) <= (cmd.len() as int),
            ((lay.rhandles as int) * 4) <= (usize::MAX as int),
            (self.sess.passphrase_len as int) <= (PASSPHRASE_MAX as int),
        ensures
            final(self).x.retries == old(self).x.retries,
            final(cmd)@.len() == old(cmd)@.len(),
            // the session bookkeeping is process-wide state:
            // begin fixes attrs and ordinal, everything else of
            // the session survives every arm
            final(self).sess.attrs == (attrs | SA_CONTINUE_SESSION),
            final(self).sess.ordinal == ordinal,
            final(self).sess.handle == old(self).sess.handle,
            final(self).sess.session_key == old(self).sess.session_key,
            final(self).sess.passphrase == old(self).sess.passphrase,
            final(self).sess.passphrase_len == old(self).sess.passphrase_len,
            // the fill-in face: everything outside the
            // authorization window is the caller's own bytes
            forall|j: int|
                0 <= j < (final(cmd)@.len() as int)
                    && !((lay.sess_off as int) <= j
                        < ((lay.sess_off as int) + (CMD_SESSION_LEN as int)))
                ==> final(cmd)@.index(j) == old(cmd)@.index(j),
            // the authorization-area record the layer fills in:
            // handle, nonce size, the fresh nonce, attrs, hmac size
            final(cmd)@.subrange(
                (lay.sess_off as int),
                (lay.sess_off as int) + (SESS_HMAC_OFF as int),
            ) == spec_session_area(
                old(self).sess.handle,
                (final(self).sess.our_nonce)@,
                attrs | SA_CONTINUE_SESSION,
            ).subrange(0, (SESS_HMAC_OFF as int)),
            // the MAC window: the oracle face over the POST-fill
            // parameter bytes (finalize's exact contract; when
            // the partitions are disjoint this is the entry
            // parameter area -- see spec_layout_disjoint)
            final(cmd)@.subrange(
                (lay.sess_off as int) + (SESS_HMAC_OFF as int),
                (lay.sess_off as int) + (CMD_SESSION_LEN as int),
            ) == spec_auth_hmac(
                spec_key_material(old(self).sess),
                spec_cp_hash(
                    ordinal,
                    names@,
                    spec_cmd_with_session_area(
                        old(cmd)@,
                        lay,
                        old(self).sess.handle,
                        (final(self).sess.our_nonce)@,
                        attrs | SA_CONTINUE_SESSION,
                    ).subrange(
                        (lay.param_off as int),
                        (lay.param_off as int) + (lay.param_len as int),
                    ),
                ),
                (final(self).sess.our_nonce)@,
                (old(self).sess.tpm_nonce)@,
                attrs | SA_CONTINUE_SESSION,
            ),
            match r {
                Result::Ok(t) =>
                    // the credential face: response validated
                    // byte-for-byte against the CURRENT session
                    // state, and it matches the live buffer now
                    // (the MAC inputs are the entry key
                    // material, the begin-fixed ordinal/attrs and
                    // the begin-drawn nonce, each of which equals
                    // the final session's own record on this arm)
                    !final(self).x.tis.held
                        && final(self).sess.state == SessionState::Idle
                        && final(self).sess.tpm_nonce == t.a.tpm_nonce
                        && spec_credential_matches(
                            &t,
                            final(self).rbuf@,
                            &final(self).sess,
                        ),
                Result::Err(SecErr::Rc(rc)) =>
                    rc != RC_SUCCESS
                        && rc as int == wire_be32(final(self).rbuf@, 6)
                        && final(self).sess.state == SessionState::Closed
                        && final(self).sess.tpm_nonce == old(self).sess.tpm_nonce,
                Result::Err(SecErr::Bus(e)) =>
                    final(self).sess.state == SessionState::Closed
                        && final(self).sess.tpm_nonce == old(self).sess.tpm_nonce
                        && match e {
                            // the CmdLayout doc's "checked by the
                            // link layer" sentence, verified: the
                            // assembled command is rejected
                            // unseen by the device
                            XferErr::BadCommand =>
                                !cmd_wf_spec(final(cmd)@, lay.len as int),
                            _ => !old(self).x.tis.held ==> !final(self).x.tis.held,
                        },
                Result::Err(SecErr::Auth(e)) =>
                    final(self).sess.state == SessionState::Closed
                        && final(self).sess.tpm_nonce == old(self).sess.tpm_nonce
                        && wire_be32(final(self).rbuf@, 6) == (RC_SUCCESS as int),
            },
    {
        self.sess.begin(rng, ordinal, attrs);
        let handle = self.sess.handle();
        let nonce = self.sess.our_nonce();
        let sattrs = self.sess.attrs();
        write_cmd_session(cmd, lay.sess_off, handle, &nonce, sattrs);
        proof {
            // compose the Mounted view: from write_cmd_session's
            // piecewise broadcast (per-window subsequences, the
            // attrs point, the pointwise zero window and the
            // outside-window agreement) to the single equality
            // cmd@ == the entry view with the 73-byte record
            // mounted (the AM area face; the "fill them in" doc
            // claim as one fact). Word-level joins are spelled
            // here in the two halves then closed with the
            // ext-equality bridge, the T4 ct_eq32 pattern.
            let s = (lay.sess_off as int);
            let g = (SESS_HMAC_OFF as int);
            let w = (CMD_SESSION_LEN as int);
            let area = spec_session_area(handle, nonce@, sattrs);
            // half one: the 41-byte record prefix, joint from the
            // per-window broadcasts
            assert forall|k: int|
                0 <= k < g implies cmd@.index(s + k) == area.index(k)
            by {
                if k < 4 {
                    assert(cmd@.index(s + k) == cmd@.subrange(s, s + 4).index(k));
                    assert(area.index(k) == area.subrange(0, 4).index(k));
                } else if k < 6 {
                    assert(cmd@.index(s + k) == cmd@.subrange(s + 4, s + 6).index(k - 4));
                    assert(area.index(k) == area.subrange(4, 6).index(k - 4));
                } else if k < 38 {
                    assert(cmd@.index(s + k) == cmd@.subrange(s + 6, s + 38).index(k - 6));
                    assert(area.index(k) == area.subrange(6, 38).index(k - 6));
                } else if k == 38 {
                } else {
                    assert(cmd@.index(s + k) == cmd@.subrange(s + 39, s + 41).index(k - 39));
                    assert(area.index(k) == area.subrange(39, 41).index(k - 39));
                }
            }
            // half two: the 41..73 zero placeholder, pointwise
            assert forall|k: int|
                g <= k < w implies cmd@.index(s + k) == area.index(k)
            by {
                assert(area.index(k) == super::auth::zero_seq32().index(k - g));
            }
            // close the full window equality and lift it to the
            // whole-command equality against the mounted view
            assert(cmd@.subrange(s, s + w).len() == area.len());
            assert(area.len() == w);
            vstd::seq::lemma_seq_ext_equal::<u8>(cmd@.subrange(s, s + w), area);
            let mnt = spec_cmd_with_session_area(
                old(cmd)@,
                lay,
                handle,
                nonce@,
                sattrs,
            );
            assert(mnt.len() == (old(cmd)@).len());
            assert(mnt == (old(cmd)@).subrange(0, s)
                .add(area)
                .add((old(cmd)@).subrange(s + w, (old(cmd)@).len() as int)));
            assert forall|k: int|
                0 <= k < mnt.len() implies cmd@.index(k) == mnt.index(k)
            by {
                if k < s {
                    assert(mnt.index(k) == (old(cmd)@).index(k));
                } else if k < s + w {
                    assert(mnt.index(k) == area.index(k - s));
                    assert(cmd@.index(k) == cmd@.subrange(s, s + w).index(k - s));
                } else {
                    assert(mnt.index(k) == (old(cmd)@).index(k));
                }
            }
            vstd::seq::lemma_seq_ext_equal::<u8>(cmd@, mnt);
        }
        self.sess.finalize::<S, H>(
            cmd,
            lay.sess_off,
            lay.index,
            names,
            lay.param_off,
            lay.param_len,
        );
        match self.x.run(cmd, lay.len, &mut self.rbuf) {
            Result::Ok((n, rc)) => {
                if rc != RC_SUCCESS {
                    self.sess.close();
                    return Result::Err(SecErr::Rc(rc));
                }
                proof {
                    // response-side relay: the run broadcast's final
                    // response view is the response-buffer field's
                    // current view (rc == its header word at 6)
                    assert((self.rbuf@).len() == (MSG_MAX as int));
                    assert((n as int) <= (MSG_MAX as int));
                    assert(wire_be32(self.rbuf@, 6) == (rc as int));
                    assert(wire_be32(self.rbuf@, 6) == (RC_SUCCESS as int));
                }
                let raw = &self.rbuf[0..n];
                proof {
                    // the exit slice is the [0, n) head of the
                    // response buffer
                    assert(raw@ == self.rbuf@.subrange(0, (n as int)));
                    assert(raw@.len() == (n as int));
                }
                match self.sess.check_response::<S, H>(raw, lay.rhandles) {
                    Result::Ok(a) => {
                        proof {
                            // map check_response's slice-typed gold
                            // face onto the field-view seq twin:
                            // the credential's exit IS n, indices
                            // coincide, and the session MAC inputs
                            // are the current record (check preserves
                            // every input; begin fixed them)
                            assert((a.hmac_off as int) + (SHA256_LEN as int)
                                == (raw@.len() as int));
                            assert((a.hmac_off as int) + (SHA256_LEN as int)
                                == (n as int));
                            assert forall|j: int|
                                0 <= j < (n as int)
                                    implies raw@.index(j) == self.rbuf@.index(j)
                            by {
                                assert(raw@.index(j)
                                    == self.rbuf@.subrange(0, (n as int)).index(j));
                            }
                            let kn = (a.nonce_off as int) + (NONCE_LEN as int);
                            let kp = (a.param_off as int) + (a.param_len as int);
                            let kh = (a.hmac_off as int) + (SHA256_LEN as int);
                            // the three window compositions that live
                            // inside the mapping (nonce, parameter
                            // area, MAC window), spelled explicitly
                            // so the broadcast composition lemma's
                            // trigger matches (T5-4 trigger discipline)
                            vstd::seq::lemma_seq_subrange_composition::<u8>(
                                self.rbuf@,
                                0,
                                (n as int),
                                (a.nonce_off as int),
                                kn,
                            );
                            vstd::seq::lemma_seq_subrange_composition::<u8>(
                                self.rbuf@,
                                0,
                                (n as int),
                                (a.param_off as int),
                                kp,
                            );
                            vstd::seq::lemma_seq_subrange_composition::<u8>(
                                self.rbuf@,
                                0,
                                (n as int),
                                (a.hmac_off as int),
                                kh,
                            );
                            assert(spec_resp_auth_ok(
                                a,
                                self.rbuf@,
                                spec_key_material(self.sess),
                                self.sess.ordinal,
                                self.sess.our_nonce@,
                                self.sess.attrs,
                            ));
                        }
                        Result::Ok(Authenticated { a })
                    }
                    Result::Err(e) => Result::Err(SecErr::Auth(e)),
                }
            }
            Result::Err(e) => {
                self.sess.close();
                return Result::Err(SecErr::Bus(e));
            }
        }
    }

    /// Origin Rust: /// Extract the parameter area from the response.
    /// ///
    /// /// This is the **only exit** for response bytes from this structure. The precondition requires a
    /// /// credential matching the current temporary buffer contents; without a credential, the bytes cannot
    /// /// be obtained, and an expired credential also prevents access. (secure.rs:119-128)
    /// The doc's promised precondition does not survive in the
    /// runtime twin (nothing tracks buffer identity: a stale
    /// credential, or one minted by another Guarded, still reads
    /// bytes; suspects row S-T6-1). The twin re-erects the
    /// promised precondition as a real requires; invoke's Ok arm
    /// discharges it with a fresh credential.
    pub exec fn params<'a>(&'a self, t: &Authenticated) -> (r: &'a [u8])
        requires
            spec_credential_matches(t, self.rbuf@, &self.sess),
        ensures
            r@.len() == (t.a.param_len as int),
            r@ == self.rbuf@.subrange(
                (t.a.param_off as int),
                (t.a.param_off as int) + (t.a.param_len as int),
            ),
    {
        let off = t.a.param_off;
        let len = t.a.param_len;
        &self.rbuf[off..off + len]
    }

    /// Origin Rust: /// Length of the response parameter area. The credential has already fixed this value, so
    /// /// there is no need to parse the packet again before reading it.
    /// pub fn param_len(&self, t: &Authenticated) -> usize { t.a.param_len } (secure.rs:129-133)
    pub exec fn param_len(&self, t: &Authenticated) -> (r: usize)
        ensures
            r == t.a.param_len,
    {
        t.a.param_len
    }

    /// Origin Rust: /// Return the link and end the authorized phase. (secure.rs:134-145;
    /// the response buffer dies with `self` and the credentials
    /// lose their matching packet -- an ownership-typed property,
    /// carried by the by-value take; no ensures is stateable over
    /// a consumed receiver in this build, the chip.rs release
    /// precedent)
    pub exec fn release(self) -> (x: Xfer<P>)
    {
        self.x
    }
}

} // verus!
