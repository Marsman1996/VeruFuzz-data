//! tpm-core 0.1.4 authorization-area layout and response parsing
//! (src/auth.rs) -- Verus translation.
//!
//! Obligation sites of this batch live here: the exact
//! write_cmd_session byte layout (handle 4, nonce size 2, nonce 32,
//! attrs 1, hmac size 2, zero placeholder 32 = CMD_SESSION_LEN), the
//! patch_hmac overlay, and the full-supervision parser parse_rsp_auth
//! (every peer-controlled length checked before any slice is taken).
//! The HMAC digest value itself is a trusted oracle (see crypto.rs);
//! what this module proves is the update ordering and the offset
//! discipline around it.

use vstd::prelude::*;
use vstd::slice::SliceAdditionalExecFns;

verus! {

use super::buf::same_outside_range;
use super::crypto::{
    hmac_sha256_digest, kdfa32, sha256_digest, spec_kdfa32, HmacSha256Ctx, LABEL_ATH, LABEL_CFB,
    NONCE_LEN, SHA256_LEN,
};
use super::cursor::{be16_bytes_spec, be32_bytes_spec, Cursor};
use super::endian::{be16_of, be32_of};

// ------------------------------------------------------------------
// Constants (auth.rs:3-25)
// ------------------------------------------------------------------

/// Origin Rust: /// Tag: 2 bytes + length: 4 bytes + command code or return code: 4 bytes.
/// pub const HEADER_LEN: usize = 10; (src/auth.rs:3-4)
pub const HEADER_LEN: usize = 10;
/// Origin Rust: /// Tag for a packet with an authorization area. The authorization area exists only under this tag.
/// pub const ST_SESSIONS: u16 = 0x8002; (src/auth.rs:5-6)
pub const ST_SESSIONS: u16 = 0x8002;
/// Origin Rust: /// Session attribute bits.
/// pub const SA_CONTINUE_SESSION: u8 = 0x01; (src/auth.rs:7-8)
pub const SA_CONTINUE_SESSION: u8 = 0x01;
/// Origin Rust: pub const SA_DECRYPT: u8 = 0x20; (src/auth.rs:9)
pub const SA_DECRYPT: u8 = 0x20;
/// Origin Rust: pub const SA_ENCRYPT: u8 = 0x40; (src/auth.rs:10)
pub const SA_ENCRYPT: u8 = 0x40;
/// Origin Rust: /// Maximum number of sessions allowed in the authorization area.
/// ///
/// /// The spec limit is 3. This implementation appends only its own session, but the response may
/// /// contain additional sessions appended by the caller; the parsing side must still skip them. The
/// /// number of skipped sessions must be bounded, otherwise a carefully crafted response could stall
/// /// the parsing loop indefinitely.
/// pub const MAX_SESSIONS: usize = 3; (src/auth.rs:11-17)
/// Faithful twin of a constant that is never referenced by any code
/// path in the upstream crate (no parse-time check consults it, and
/// the skip loop below bounds itself by packet exhaustion instead);
/// the doc paragraph above states the bounded-skip discipline as
/// prose only. Suspects row in the out/ ledger carries the concrete
/// >MAX_SESSIONS acceptance values.
/// SPEC-DOC MISMATCH candidate (not filed): the doc claims the
/// parsing side must keep the skipped-session count bounded (spec
/// limit 3), but no code path enforces MAX_SESSIONS anywhere; the
/// parse loop below accepts an authorization area with any session
/// count a crafted packet cares to carry.
pub const MAX_SESSIONS: usize = 3;

/// Origin Rust: const SESS_HANDLE_OFF: usize = 0; (src/auth.rs:18)
/// The SESS_* offset constants are private upstream; visibility
/// opened pub here (Origin note) because the twin's public session
/// layer pins its postconditions through them (ghost consumers only;
/// runtime values unchanged).
pub const SESS_HANDLE_OFF: usize = 0;
/// Origin Rust: const SESS_NONCE_SIZE_OFF: usize = 4; (src/auth.rs:19)
pub const SESS_NONCE_SIZE_OFF: usize = 4;
/// Origin Rust: const SESS_NONCE_OFF: usize = 6; (src/auth.rs:20)
pub const SESS_NONCE_OFF: usize = 6;
/// Origin Rust: const SESS_ATTRS_OFF: usize = SESS_NONCE_OFF + NONCE_LEN; (src/auth.rs:21)
pub const SESS_ATTRS_OFF: usize = SESS_NONCE_OFF + NONCE_LEN;
/// Origin Rust: const SESS_HMAC_SIZE_OFF: usize = SESS_ATTRS_OFF + 1; (src/auth.rs:22)
pub const SESS_HMAC_SIZE_OFF: usize = SESS_ATTRS_OFF + 1;
/// Origin Rust: const SESS_HMAC_OFF: usize = SESS_HMAC_SIZE_OFF + 2; (src/auth.rs:23)
pub const SESS_HMAC_OFF: usize = SESS_HMAC_SIZE_OFF + 2;
/// Origin Rust: /// Number of bytes consumed by a single command-side session.
/// pub const CMD_SESSION_LEN: usize = SESS_HMAC_OFF + NONCE_LEN; (src/auth.rs:24-25)
pub const CMD_SESSION_LEN: usize = SESS_HMAC_OFF + NONCE_LEN;

/// Zero placeholder of exactly one digest length (the write_cmd_session
/// hmac padding face).
pub open spec fn zero_seq32() -> Seq<u8> {
    seq![
        0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    ]
}

// ------------------------------------------------------------------
// Error face (auth.rs:26-38)
// ------------------------------------------------------------------

/// Origin Rust: #[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// pub enum AuthErr { Malformed, NoSession, BadField, HmacMismatch } (src/auth.rs:26-38)
/// The Clone/Copy/PartialEq/Eq/Debug derives have no Verus twin: no
/// exec code in this tree compares AuthErr values by == (variant
/// tests go through match), per-variant doc lines carried on the
/// arms: Malformed "The packet structure does not match the length it
/// declares.", NoSession "The current session cannot be located in the
/// authorization area.", BadField "The nonce or HMAC field length is
/// not the expected digest length. These lengths are under the peer's
/// control; accepting arbitrary values would effectively let the peer
/// decide all later offset computations.", HmacMismatch "The
/// recomputed HMAC does not match the received one."
pub enum AuthErr {
    Malformed,
    NoSession,
    BadField,
    HmacMismatch,
}

// ------------------------------------------------------------------
// MAC / digest oracle faces (auth.rs:39-71)
// ------------------------------------------------------------------

/// Oracle face of auth_hmac: HMAC over the key of the stream
/// digest ++ newer nonce || older nonce || attrs byte.
pub open spec fn spec_auth_hmac(
    key: Seq<u8>,
    digest: Seq<u8>,
    newer: Seq<u8>,
    older: Seq<u8>,
    attrs: u8,
) -> Seq<u8> {
    hmac_sha256_digest(key, digest.add(newer).add(older).add(seq![attrs]))
}

/// Oracle face of rp_hash: SHA-256 over rc || ordinal || params.
pub open spec fn spec_rp_hash(rc: u32, ordinal: u32, params: Seq<u8>) -> Seq<u8> {
    sha256_digest(be32_bytes_spec(rc).add(be32_bytes_spec(ordinal)).add(params))
}

/// Oracle face of cp_hash: SHA-256 over ordinal || names || params.
pub open spec fn spec_cp_hash(ordinal: u32, names: Seq<u8>, params: Seq<u8>) -> Seq<u8> {
    sha256_digest(be32_bytes_spec(ordinal).add(names).add(params))
}

/// Origin Rust: pub(crate) fn auth_hmac<H: HmacSha256Ctx>(
///     key: &[u8], digest: &[u8; SHA256_LEN], newer: &[u8; NONCE_LEN],
///     older: &[u8; NONCE_LEN], attrs: u8,
/// ) -> [u8; SHA256_LEN] {
///     let mut h = H::with_key(key);
///     let tail: [u8; 1] = [attrs];
///     h.update(&digest[..]);
///     h.update(&newer[..]);
///     h.update(&older[..]);
///     h.update(&tail[..]);
///     h.finish()
/// } (src/auth.rs:39-53; update ordering is the obligation here)
pub(crate) exec fn auth_hmac<H: HmacSha256Ctx>(
    key: &[u8],
    digest: &[u8; SHA256_LEN],
    newer: &[u8; NONCE_LEN],
    older: &[u8; NONCE_LEN],
    attrs: u8,
) -> (r: [u8; SHA256_LEN])
    ensures
        r@ == spec_auth_hmac(key@, digest@, newer@, older@, attrs),
{
    let mut h = H::with_key(key);
    let tail: [u8; 1] = [attrs];
    let digest_sl: &[u8] = &digest[..];
    let newer_sl: &[u8] = &newer[..];
    let older_sl: &[u8] = &older[..];
    let tail_sl: &[u8] = &tail[..];
    proof {
        assert(digest_sl@ == digest@);
        assert(newer_sl@ == newer@);
        assert(older_sl@ == older@);
        assert(tail_sl@ == tail@);
    }
    h.update(digest_sl);
    proof {
        assert(h.key_view() == key@);
        assert(h.stream() == Seq::<u8>::empty().add(digest_sl@));
        assert(h.stream() == digest@);
    }
    h.update(newer_sl);
    proof {
        assert(h.stream() == digest@.add(newer@));
    }
    h.update(older_sl);
    proof {
        assert(h.stream() == digest@.add(newer@).add(older@));
    }
    h.update(tail_sl);
    proof {
        assert(h.stream() == digest@.add(newer@).add(older@).add(seq![attrs]));
    }
    h.finish()
}

/// Origin Rust: pub(crate) fn rp_hash<S: Sha256Ctx>(
///     rc: u32, ordinal: u32, params: &[u8]) -> [u8; SHA256_LEN] {
///     let mut s = S::new();
///     let rc_b = be32_arr(rc); let ord_b = be32_arr(ordinal);
///     s.update(&rc_b[..]); s.update(&ord_b[..]); s.update(params);
///     s.finish()
/// } (src/auth.rs:54-62)
pub(crate) exec fn rp_hash<S: super::crypto::Sha256Ctx>(
    rc: u32,
    ordinal: u32,
    params: &[u8],
) -> (r: [u8; SHA256_LEN])
    ensures
        r@ == spec_rp_hash(rc, ordinal, params@),
{
    let mut s = S::new();
    let rc_b = super::crypto::be32_arr(rc);
    let ord_b = super::crypto::be32_arr(ordinal);
    let rc_sl: &[u8] = &rc_b[..];
    let ord_sl: &[u8] = &ord_b[..];
    proof {
        assert(rc_sl@ == rc_b@);
        assert(ord_sl@ == ord_b@);
    }
    s.update(rc_sl);
    proof {
        assert(s.stream() == Seq::<u8>::empty().add(rc_sl@));
        assert(s.stream() == be32_bytes_spec(rc));
    }
    s.update(ord_sl);
    proof {
        assert(s.stream() == be32_bytes_spec(rc).add(be32_bytes_spec(ordinal)));
    }
    s.update(params);
    proof {
        assert(s.stream() == be32_bytes_spec(rc).add(be32_bytes_spec(ordinal)).add(params@));
    }
    s.finish()
}

/// Origin Rust: /// `names` is the concatenation of the names of all authorized handles, prepared by the session layer.
/// pub(crate) fn cp_hash<S: Sha256Ctx>(
///     ordinal: u32, names: &[u8], params: &[u8]) -> [u8; SHA256_LEN] {
///     let mut s = S::new();
///     let ord_b = be32_arr(ordinal);
///     s.update(&ord_b[..]); s.update(names); s.update(params);
///     s.finish()
/// } (src/auth.rs:63-71)
pub(crate) exec fn cp_hash<S: super::crypto::Sha256Ctx>(
    ordinal: u32,
    names: &[u8],
    params: &[u8],
) -> (r: [u8; SHA256_LEN])
    ensures
        r@ == spec_cp_hash(ordinal, names@, params@),
{
    let mut s = S::new();
    let ord_b = super::crypto::be32_arr(ordinal);
    let ord_sl: &[u8] = &ord_b[..];
    proof {
        assert(ord_sl@ == ord_b@);
    }
    s.update(ord_sl);
    proof {
        assert(s.stream() == Seq::<u8>::empty().add(ord_sl@));
        assert(s.stream() == be32_bytes_spec(ordinal));
    }
    s.update(names);
    proof {
        assert(s.stream() == be32_bytes_spec(ordinal).add(names@));
    }
    s.update(params);
    proof {
        assert(s.stream() == be32_bytes_spec(ordinal).add(names@).add(params@));
    }
    s.finish()
}

// ------------------------------------------------------------------
// Command-side session layout (auth.rs:72-105)
// ------------------------------------------------------------------

/// Origin Rust: /// Lay out a session at `out[off..]`, leaving the HMAC field blank.
/// ///
/// /// We leave it blank instead of filling it with random bytes: the placeholder is not part of any
/// /// checksum, but it will still be written into the final packet. If a later patch_hmac call is
/// /// skipped because of an error path, the leftover should be an obvious all-zero pattern rather than
/// /// something that looks like a real MAC.
/// pub(crate) fn write_cmd_session(
///     out: &mut [u8], off: usize, handle: u32,
///     nonce: &[u8; NONCE_LEN], attrs: u8) (src/auth.rs:72-100)
/// Upstream indexes out[off + SESS_*] with no bound on off; the
/// requires below carries the missing layout bound (suspects row in
/// the out/ ledger; upstream doc states no # Panics entry).
pub(crate) exec fn write_cmd_session(
    out: &mut [u8],
    off: usize,
    handle: u32,
    nonce: &[u8; NONCE_LEN],
    attrs: u8,
)
    requires
        (off as int) + (CMD_SESSION_LEN as int) <= (out.len() as int),
    ensures
        final(out)@.len() == old(out)@.len(),
        same_outside_range(
            old(out)@,
            final(out)@,
            (off as int),
            (off as int) + (CMD_SESSION_LEN as int),
        ),
        final(out)@.subrange((off as int) + (SESS_HANDLE_OFF as int), (off as int) + 4)
            == be32_bytes_spec(handle),
        final(out)@.subrange((off as int) + (SESS_NONCE_SIZE_OFF as int), (off as int) + 6)
            == be16_bytes_spec((NONCE_LEN as u16)),
        final(out)@.subrange((off as int) + (SESS_NONCE_OFF as int), (off as int) + (SESS_ATTRS_OFF as int))
            == nonce@,
        final(out)@.index((off as int) + (SESS_ATTRS_OFF as int)) == attrs,
        final(out)@.subrange(
            (off as int) + (SESS_HMAC_SIZE_OFF as int),
            (off as int) + (SESS_HMAC_OFF as int),
        ) == be16_bytes_spec((NONCE_LEN as u16)),
        forall|j: int|
            ((off as int) + (SESS_HMAC_OFF as int)) <= j
                < ((off as int) + (CMD_SESSION_LEN as int))
            ==> #[trigger] final(out)@.index(j) == 0u8,
{
    let ln = out.len();
    let ghost entry = out@;
    let h = super::crypto::be32_arr(handle);
    let n = super::crypto::be16_arr((NONCE_LEN as u16));
    let nc = *nonce;
    proof {
        assert(nc@ == nonce@);
        assert(h@ == be32_bytes_spec(handle));
        assert(n@ == be16_bytes_spec((NONCE_LEN as u16)));
        assert(ln == out@.len());
    }
    out.set(off + SESS_HANDLE_OFF, h[0]);
    out.set(off + SESS_HANDLE_OFF + 1, h[1]);
    out.set(off + SESS_HANDLE_OFF + 2, h[2]);
    out.set(off + SESS_HANDLE_OFF + 3, h[3]);
    out.set(off + SESS_NONCE_SIZE_OFF, n[0]);
    out.set(off + SESS_NONCE_SIZE_OFF + 1, n[1]);
    // nonce copy (copy_from_slice lowered to the element copy loop)
    let nonce_start = off + SESS_NONCE_OFF;
    let ghost pre_copy = out@;
    let mut i: usize = 0;
    while i < NONCE_LEN
        invariant
            i <= NONCE_LEN,
            ln == out@.len(),
            ((nonce_start as int) + (NONCE_LEN as int)) <= (ln as int),
            forall|j: int|
                0 <= j < out@.len()
                    && !((nonce_start as int) <= j < (nonce_start as int) + (i as int))
                    ==> #[trigger] out@.index(j) == pre_copy.index(j),
            forall|j: int| 0 <= j < (i as int)
                ==> #[trigger] out@.index((nonce_start as int) + j) == nc@.index(j),
        decreases
            NONCE_LEN - i,
    {
        out.set(nonce_start + i, nc[i]);
        i += 1;
    }
    proof {
        assert(i == NONCE_LEN);
        assert forall|j: int|
            0 <= j < (NONCE_LEN as int)
            implies out@.index((nonce_start as int) + j) == nc@.index(j)
        by {
            // loop exit face with i pinned to NONCE_LEN
        }
        assert forall|j: int|
            0 <= j < out@.len()
                && !((nonce_start as int) <= j < ((nonce_start + NONCE_LEN) as int))
            implies out@.index(j) == pre_copy.index(j)
        by {
            // skolem j: outside the nonce window, the copy loop
            // preserved it
        }
        assert(out@.subrange((nonce_start as int), ((nonce_start + NONCE_LEN) as int)).len()
            == NONCE_LEN);
        assert(out@.index((nonce_start as int)) == nc@.index(0));
        assert(out@.subrange((nonce_start as int), ((nonce_start + NONCE_LEN) as int)).index(0)
            == out@.index((nonce_start as int)));
        assert(out@.subrange((nonce_start as int), ((nonce_start + NONCE_LEN) as int))
            == nc@);
    }
    out.set(off + SESS_ATTRS_OFF, attrs);
    out.set(off + SESS_HMAC_SIZE_OFF, n[0]);
    out.set(off + SESS_HMAC_SIZE_OFF + 1, n[1]);
    // zero fill (fill(0) lowered to the element write loop)
    let hmac_start = off + SESS_HMAC_OFF;
    let ghost pre_fill = out@;
    let mut k: usize = 0;
    while k < NONCE_LEN
        invariant
            k <= NONCE_LEN,
            ln == out@.len(),
            ((hmac_start as int) + (NONCE_LEN as int)) <= (ln as int),
            forall|j: int|
                0 <= j < out@.len()
                    && !((hmac_start as int) <= j < (hmac_start as int) + (k as int))
                    ==> #[trigger] out@.index(j) == pre_fill.index(j),
            forall|j: int|
                (hmac_start as int) <= j < (hmac_start as int) + (k as int)
                    ==> out@.index(j) == 0u8,
        decreases
            NONCE_LEN - k,
    {
        out.set(hmac_start + k, 0u8);
        k += 1;
    }
    proof {
        assert(k == NONCE_LEN);
        assert forall|j: int|
            (hmac_start as int) <= j < ((hmac_start + NONCE_LEN) as int)
            implies out@.index(j) == 0u8
        by {
            // loop exit face with k pinned to NONCE_LEN (absolute-index
            // form so the pointwise zero-window ensures instantiates
            // directly)
        }
        // compose the three write regions into the outside-window face:
        // the scalar writes and both loop windows all sit inside
        // [off, off + CMD_SESSION_LEN)
        assert forall|j: int|
            0 <= j < out@.len()
                && !((off as int) <= j < ((off + CMD_SESSION_LEN) as int))
            implies out@.index(j) == entry.index(j)
        by {
            // step 1: fill-loop preservation (j outside the zero
            // window)
            assert(out@.index(j) == pre_fill.index(j));
            // step 2: the attrs/hmac-size scalar writes only touched
            // [off + 38, off + 41), inside the excluded window
            assert(pre_fill.index(j) == pre_copy.index(j));
            // step 3: copy-loop preservation (j outside the nonce
            // window)
            assert(pre_copy.index(j) == entry.index(j));
        }
    }
}

/// Origin Rust: /// Fill the reserved MAC field with the computed value.
/// pub(crate) fn patch_hmac(out: &mut [u8], off: usize, mac: &[u8; SHA256_LEN]) (src/auth.rs:101-105)
/// Upstream indexes out[off + SESS_HMAC_OFF .. + SHA256_LEN] with no
/// bound on off; the requires below carries the missing bound
/// (suspects row in the out/ ledger).
pub(crate) exec fn patch_hmac(out: &mut [u8], off: usize, mac: &[u8; SHA256_LEN])
    requires
        (off as int) + (SESS_HMAC_OFF as int) + (SHA256_LEN as int) <= (out.len() as int),
    ensures
        final(out)@.len() == old(out)@.len(),
        same_outside_range(
            old(out)@,
            final(out)@,
            (off as int) + (SESS_HMAC_OFF as int),
            (off as int) + (SESS_HMAC_OFF as int) + (SHA256_LEN as int),
        ),
        final(out)@.subrange(
            (off as int) + (SESS_HMAC_OFF as int),
            (off as int) + (SESS_HMAC_OFF as int) + (SHA256_LEN as int),
        ) == mac@,
{
    let start = off + SESS_HMAC_OFF;
    let ln = out.len();
    let ghost pre = out@;
    let mc = *mac;
    proof {
        assert(mc@ == mac@);
        assert(ln == out@.len());
    }
    let mut i: usize = 0;
    while i < SHA256_LEN
        invariant
            i <= SHA256_LEN,
            ln == out@.len(),
            ((start as int) + (SHA256_LEN as int)) <= (ln as int),
            forall|j: int|
                0 <= j < out@.len()
                    && !((start as int) <= j < (start as int) + (i as int))
                    ==> #[trigger] out@.index(j) == pre.index(j),
            forall|j: int| 0 <= j < (i as int)
                ==> #[trigger] out@.index((start as int) + j) == mc@.index(j),
        decreases
            SHA256_LEN - i,
    {
        out.set(start + i, mc[i]);
        i += 1;
    }
    proof {
        assert(i == SHA256_LEN);
        assert forall|j: int|
            0 <= j < (SHA256_LEN as int)
            implies out@.index((start as int) + j) == mc@.index(j)
        by {
            // loop exit face with i pinned to SHA256_LEN
        }
        assert(out@.subrange((start as int), ((start + SHA256_LEN) as int)).len()
            == SHA256_LEN);
        assert(out@.index((start as int)) == mc@.index(0));
        assert(out@.subrange((start as int), ((start + SHA256_LEN) as int)).index(0)
            == out@.index((start as int)));
        assert(out@.subrange((start as int), ((start + SHA256_LEN) as int)) == mac@);
    }
}

// ------------------------------------------------------------------
// Response-side location record (auth.rs:106-131)
// ------------------------------------------------------------------

/// Origin Rust: /// Session-related position information for a single response.
/// ///
/// /// We record only the offsets and not the content: the parameter area may be thousands of bytes long,
/// /// and the checksum only needs a way to point to it. The nonce is the exception—it must survive across
/// /// rounds and therefore must be copied out.
/// #[derive(Clone, Copy)]
/// pub struct RspAuth {
///     /// Start of the parameter area.
///     pub param_off: usize,
///     /// Length of the parameter area.
///     pub param_len: usize,
///     /// Start of this session's nonce field.
///     pub nonce_off: usize,
///     /// Start of this session's HMAC field.
///     pub hmac_off: usize,
///     /// Session attributes reported by the peer.
///     pub attrs: u8,
///     /// The peer's nonce for this round.
///     pub tpm_nonce: [u8; NONCE_LEN],
/// } (src/auth.rs:106-125; doc glyphs converted ASCII)
/// The Clone/Copy derives have no Verus twin (no copy of a RspAuth
/// happens inside this crate's verified code).
pub struct RspAuth {
    /// Start of the parameter area.
    pub param_off: usize,
    /// Length of the parameter area.
    pub param_len: usize,
    /// Start of this session's nonce field.
    pub nonce_off: usize,
    /// Start of this session's HMAC field.
    pub hmac_off: usize,
    /// Session attributes reported by the peer.
    pub attrs: u8,
    /// The peer's nonce for this round.
    pub tpm_nonce: [u8; NONCE_LEN],
}

/// The success face of parse_rsp_auth, gathered from the doc's three
/// called-out checks plus the param-overlap side condition:
/// the sessions tag, the declared size matching the byte count, all
/// offsets inside raw, the parameter area not reaching into this
/// session's nonce, our session being last
/// (hmac_off + SHA256_LEN == raw.len()), the peer nonce copied from
/// the wire, and attrs read from the wire at nonce_off + NONCE_LEN.
pub open spec fn rsp_auth_valid(a: RspAuth, raw: &[u8]) -> bool {
    (raw.len() as int) >= (HEADER_LEN as int)
        && be16_of(raw@[0], raw@[1]) == (ST_SESSIONS as int)
        && be32_of(raw@[2], raw@[3], raw@[4], raw@[5]) == (raw.len() as int)
        && (HEADER_LEN as int) <= (a.param_off as int)
        && (a.param_off as int) + (a.param_len as int) <= (a.nonce_off as int)
        && (a.nonce_off as int) + (NONCE_LEN as int) <= (a.hmac_off as int)
        && (a.hmac_off as int) + (SHA256_LEN as int) == (raw.len() as int)
        && a.tpm_nonce@ == raw@.subrange((a.nonce_off as int), (a.nonce_off as int) + (NONCE_LEN as int))
        && a.attrs == raw@.index((a.nonce_off as int) + (NONCE_LEN as int))
}

/// Origin Rust: fn read_nonce(raw: &[u8], off: usize) -> [u8; NONCE_LEN] {
///     let mut out = [0u8; NONCE_LEN];
///     out.copy_from_slice(&raw[off..off + NONCE_LEN]);
///     out
/// } (src/auth.rs:126-131; copy_from_slice lowered to the element
/// copy loop, same bytes)
fn read_nonce(raw: &[u8], off: usize) -> (out: [u8; NONCE_LEN])
    requires
        (off as int) + (NONCE_LEN as int) <= (raw.len() as int),
    ensures
        out@ == raw@.subrange((off as int), (off as int) + (NONCE_LEN as int)),
{
    let mut acc = [0u8; NONCE_LEN];
    let ln = raw.len();
    proof {
        assert(ln == raw@.len());
    }
    let mut i: usize = 0;
    while i < NONCE_LEN
        invariant
            i <= NONCE_LEN,
            ln == raw@.len(),
            ((off as int) + (NONCE_LEN as int)) <= (ln as int),
            forall|j: int| 0 <= j < (i as int)
                ==> #[trigger] acc@.index(j) == raw@.index((off as int) + j),
        decreases
            NONCE_LEN - i,
    {
        acc[i] = raw[off + i];
        i += 1;
    }
    proof {
        assert(i == NONCE_LEN);
        assert forall|j: int|
            0 <= j < (NONCE_LEN as int)
            implies acc@.index(j) == raw@.index((off as int) + j)
        by {
            // loop exit face with i pinned to NONCE_LEN
        }
        assert(acc@ == raw@.subrange((off as int), ((off + NONCE_LEN) as int)));
    }
    acc
}

// ------------------------------------------------------------------
// parse_rsp_auth (auth.rs:132-224)
// ------------------------------------------------------------------

/// Origin Rust (doc, abridged; the three called-out checks): "This session must be the last one. ... "
/// "The nonce and HMAC lengths must exactly match the digest length. These lengths are chosen by the peer;
/// allowing arbitrary values would hand all later offset reasoning to the peer." ... "The length field must
/// match the number of bytes actually present."
/// pub(crate) fn parse_rsp_auth(raw: &[u8], rhandles: usize, index: usize) -> Result<RspAuth, AuthErr>
/// (src/auth.rs:132-224)
/// Upstream computes `rhandles * 4` unchecked (debug panic on
/// overflow); the requires below carries the multiplication bound
/// (suspects row in the out/ ledger). The ok_or chains are lowered to
/// match arms of the same None/Some semantics.
/// Error arms are one-sided (the ok face is exact; error-kind
/// iff-faces are deferred to a consuming batch, T1 S5 precedent).
pub(crate) exec fn parse_rsp_auth(
    raw: &[u8],
    rhandles: usize,
    index: usize,
) -> (r: Result<RspAuth, AuthErr>)
    requires
        ((rhandles as int) * 4) <= (usize::MAX as int),
    ensures
        match r {
            Result::Ok(a) => rsp_auth_valid(a, raw),
            Result::Err(_) => true,
        },
{
    if raw.len() < HEADER_LEN {
        return Err(AuthErr::Malformed);
    }
    let mut c = Cursor::new();
    let tag = match c.read_be16(raw) {
        Option::Some(v) => v,
        Option::None => return Err(AuthErr::Malformed),
    };
    let size = match c.read_be32(raw) {
        Option::Some(v) => v,
        Option::None => return Err(AuthErr::Malformed),
    };
    if !c.skip(raw, 4) {
        return Err(AuthErr::Malformed);
    }
    if tag != ST_SESSIONS {
        return Err(AuthErr::Malformed);
    }
    if size as usize != raw.len() {
        return Err(AuthErr::Malformed);
    }
    if !c.skip(raw, rhandles * 4) {
        return Err(AuthErr::Malformed);
    }
    let param_len_u32 = match c.read_be32(raw) {
        Option::Some(v) => v,
        Option::None => return Err(AuthErr::Malformed),
    };
    if param_len_u32 as usize > raw.len() {
        return Err(AuthErr::Malformed);
    }
    let param_len = param_len_u32 as usize;
    let param_off = c.pos();
    if !c.skip(raw, param_len) {
        return Err(AuthErr::Malformed);
    }
    proof {
        assert((param_off as int) + (param_len as int) <= (raw.len() as int));
    }
    // skip chain over the index sessions before ours (each iteration
    // either consumes bytes or fails the whole parse)
    let mut i: usize = 0;
    while i < index
        invariant
            i <= index,
            c.pos <= raw.len(),
            (param_off as int) + (param_len as int) <= (c.pos as int),
        decreases
            index - i,
    {
        let nl = match c.read_be16(raw) {
            Option::Some(v) => v,
            Option::None => return Err(AuthErr::Malformed),
        };
        if !c.skip(raw, nl as usize) {
            return Err(AuthErr::Malformed);
        }
        if !c.skip(raw, 1) {
            return Err(AuthErr::Malformed);
        }
        let hl = match c.read_be16(raw) {
            Option::Some(v) => v,
            Option::None => return Err(AuthErr::Malformed),
        };
        if !c.skip(raw, hl as usize) {
            return Err(AuthErr::Malformed);
        }
        i += 1;
    }
    let nonce_len = match c.read_be16(raw) {
        Option::Some(v) => v,
        Option::None => return Err(AuthErr::NoSession),
    };
    if nonce_len as usize != NONCE_LEN {
        return Err(AuthErr::BadField);
    }
    let nonce_off = c.pos();
    if !c.skip(raw, NONCE_LEN) {
        return Err(AuthErr::Malformed);
    }
    proof {
        assert((nonce_off as int) + (NONCE_LEN as int) <= (raw.len() as int));
    }
    let tpm_nonce = read_nonce(raw, nonce_off);
    let attrs = match c.read_u8(raw) {
        Option::Some(v) => v,
        Option::None => return Err(AuthErr::Malformed),
    };
    let hmac_len = match c.read_be16(raw) {
        Option::Some(v) => v,
        Option::None => return Err(AuthErr::Malformed),
    };
    if hmac_len as usize != SHA256_LEN {
        return Err(AuthErr::BadField);
    }
    let hmac_off = c.pos();
    // upstream spells the two adds as checked_add().ok_or(Malformed)
    // with the same Malformed return on overflow; here the overflow
    // branch is spelled as an int-side guard (the cursor faces make it
    // unreachable, but the branch keeps the faithful checked shape)
    if hmac_off > usize::MAX - SHA256_LEN {
        return Err(AuthErr::Malformed);
    }
    let hmac_end = hmac_off + SHA256_LEN;
    if hmac_end != raw.len() {
        return Err(AuthErr::Malformed);
    }
    if param_off > usize::MAX - param_len {
        return Err(AuthErr::Malformed);
    }
    // param_off.checked_add(param_len) with the same checked shape
    let param_end = param_off + param_len;
    if param_end > nonce_off {
        return Err(AuthErr::Malformed);
    }
    proof {
        assert((hmac_off as int) + (SHA256_LEN as int) == (raw.len() as int));
        assert(be16_of(raw@[0], raw@[1]) == (ST_SESSIONS as int));
        assert(be32_of(raw@[2], raw@[3], raw@[4], raw@[5]) == (raw.len() as int));
        assert(tpm_nonce@ == raw@.subrange((nonce_off as int), (nonce_off as int) + (NONCE_LEN as int)));
        assert(attrs == raw@.index((nonce_off as int) + (NONCE_LEN as int)));
        assert((nonce_off as int) + (NONCE_LEN as int) <= (hmac_off as int));
    }
    Ok(RspAuth {
        param_off,
        param_len,
        nonce_off,
        hmac_off,
        attrs,
        tpm_nonce,
    })
}

// ------------------------------------------------------------------
// ct_eq32 (auth.rs:225-236)
// ------------------------------------------------------------------

/// Prefix byte-pair agreement up to k (the spec twin of the
/// constant-trip loop's accumulated decision).
pub(crate) open spec fn bytes_equal_upto(a: Seq<u8>, b: Seq<u8>, k: int) -> bool {
    forall|j: int| 0 <= j < k ==> a.index(j) == b.index(j)
}

/// Origin Rust: /// Compare byte by byte without early return.
/// ///
/// /// Early return makes the comparison time depend on the position of the first differing byte, which is
/// /// equivalent to telling the timing side how many bytes were guessed correctly. MAC comparison must be
/// /// constant-time.
/// pub(crate) fn ct_eq32(a: &[u8; SHA256_LEN], b: &[u8]) -> bool {
///     let mut acc: u8 = 0;
///     for i in 0..SHA256_LEN { acc |= a[i] ^ b[i]; }
///     acc == 0
/// } (src/auth.rs:225-236)
/// The functional face is plain byte equality; the loop shape below
/// is the audit artifact the doc claims it is: a fixed 32-trip while
/// loop with no data-dependent exit (the no-early-return intent is
/// structural, not just prose). Upstream indexes b[i] for i < 32 with
/// no length check on b; the requires carries the missing bound
/// (the face records that any out-of-range b would panic upstream;
/// the only in-crate call site binds a 32-byte slice).
pub(crate) exec fn ct_eq32(a: &[u8; SHA256_LEN], b: &[u8]) -> (r: bool)
    requires
        (b.len() as int) == (SHA256_LEN as int),
    ensures
        r == (a@ == b@),
{
    let aa = *a;
    let ghost b_entry = b@;
    proof {
        assert(aa@ == a@);
        assert(b_entry.len() == SHA256_LEN);
    }
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < SHA256_LEN
        invariant
            i <= SHA256_LEN,
            b@ == b_entry,
            (acc == 0) == bytes_equal_upto(aa@, b@, i as int),
            (acc as int) <= (i as int),
            aa@.len() == SHA256_LEN,
            b@.len() == SHA256_LEN,
        decreases
            SHA256_LEN - i,
    {
        // upstream: acc |= aa[i] ^ b[i]; XOR/OR accumulation is not
        // derivable in this verus build's default encoding (u8 bit
        // ops carry no axioms -- probe-confirmed at rlimit 600), so
        // the accumulator is lowered to the 0/1 difference flag sum:
        // same 32 fixed trips, same no-early-exit loop shape, same
        // decision value (acc == 0 <==> all bytes equal)
        let d = if aa[i] == b[i] { 0u8 } else { 1u8 };
        acc = acc + d;
        i += 1;
    }
    proof {
        // no direction is assumed: the exit state of the iff-invariant
        // is linked to the byte-for-byte seq equality through the
        // bytes_equal_upto definition (pointwise forall), the matching
        // lens, and the explicit ext-equality bridge
        assert(bytes_equal_upto(aa@, b@, SHA256_LEN as int)
            <==> forall|j: int|
                0 <= j < (SHA256_LEN as int) ==> aa@.index(j) == b@.index(j));
        assert(aa@.len() == b@.len());
        vstd::seq::lemma_seq_ext_equal::<u8>(aa@, b@);
        assert((acc == 0) == (aa@ == b@));
        assert((acc == 0) == (a@ == b@));
    }
    acc == 0
}

} // verus!
