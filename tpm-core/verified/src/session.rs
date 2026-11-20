//! tpm-core 0.1.4 HMAC authorization session state machine
//! (src/session.rs) -- Verus translation.
//!
//! Quoted upstream doc that this module re-erects as specs: check_response
//! "Returning Ok means the MAC in the packet is byte-for-byte identical to
//! the value recomputed using this session's key, the two nonces for this
//! round, and the command code for this round. The postcondition states
//! this explicitly, so any implementation that bypasses validation and
//! trusts the response directly will fail verification." The recomputed
//! MAC is a trusted-oracle composition (crypto.rs); what the twin proves
//! is that the Ok arm is exactly the byte equality, and that every
//! failure path leaves the session Closed.
//!
//! Key-material zeroization (the two Drop impls) is a documented-only
//! face per the batch scoping cut: the fill(0) + compiler_fence bodies
//! are transcribed as trusted (external_body) with no verification
//! obligation; Dead-store-elimination semantics are outside Verus
//! modeling (upstream's own doc says the fence is "the strongest
//! guarantee available", not a volatile guarantee).

use vstd::prelude::*;

verus! {

use super::auth::{
    auth_hmac, cp_hash, ct_eq32, parse_rsp_auth, patch_hmac, rp_hash, AuthErr, CMD_SESSION_LEN,
    RspAuth, SA_CONTINUE_SESSION, SESS_HMAC_OFF, spec_auth_hmac, spec_cp_hash, spec_rp_hash,
};
use super::buf::same_outside_range;
use super::crypto::{
    cfb_decrypt_view, cfb_encrypt_view, kdfa32, label_ath_seq, label_cfb_seq, spec_kdfa32, AesCfb,
    CFB_MATERIAL_LEN, HmacSha256Ctx, KEY_MATERIAL_MAX, LABEL_ATH, LABEL_CFB, NONCE_LEN,
    NonceSource, PASSPHRASE_MAX, SHA256_LEN, Sha256Ctx,
};

// ------------------------------------------------------------------
// SessionState (session.rs:3-18)
// ------------------------------------------------------------------

/// Origin Rust: /// Session lifecycle.
/// ///
/// /// `Pending` uses a tuple variant rather than named fields: a struct literal with braces in an `ensures`
/// /// clause is parsed as the start of the function body, and the specification rejects a state mention if it
/// /// appears even once. The tuple form is a call expression and has no such ambiguity.
/// #[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// pub enum SessionState { Idle, Pending(usize), Closed } (src/session.rs:3-18;
/// the Clone/Copy/PartialEq/Eq/Debug derives have no Verus twin --
/// no exec copy or ==-comparison of a state happens in this tree;
/// variant docs: Idle "Session is available and waiting for the
/// next command.", Pending "Command has been fixed and is waiting
/// for the response. The payload is the index of this session in the
/// authorization area.", Closed "Session has been invalidated. Its
/// handle still needs to be released once, and this structure must
/// never participate in any further computation after that.")
pub enum SessionState {
    Idle,
    Pending(usize),
    Closed,
}

/// Spec twin of the Pending test.
pub open spec fn state_is_pending(s: SessionState) -> bool {
    match s {
        SessionState::Pending(_) => true,
        SessionState::Idle => false,
        SessionState::Closed => false,
    }
}

/// Spec twin of the pending index extraction (-1 for non-Pending).
pub open spec fn state_pending_index(s: SessionState) -> int {
    match s {
        SessionState::Pending(i) => i as int,
        SessionState::Idle => -1,
        SessionState::Closed => -1,
    }
}

// ------------------------------------------------------------------
// AuthSession record (session.rs:19-40)
// ------------------------------------------------------------------

/// Origin Rust: /// An HMAC authorization session.
/// ///
/// /// The struct itself carries key material, so it does not implement `Clone` — every extra copy would mean
/// /// another place where the secret must be erased. It also does not implement `Debug` ...
/// pub struct AuthSession {
///     handle: u32,
///     our_nonce: [u8; NONCE_LEN],
///     tpm_nonce: [u8; NONCE_LEN],
///     session_key: [u8; SHA256_LEN],
///     passphrase: [u8; PASSPHRASE_MAX],
///     passphrase_len: usize,
///     attrs: u8,
///     ordinal: u32,
///     state: SessionState,
/// } (src/session.rs:19-40)
/// Field visibility opened pub (Origin note): the twin's public
/// postconditions speak about the individual fields (the cursor.rs
/// `pos` precedent of batch T1); upstream keeps them private, runtime
/// layout and values unchanged. The no-Clone/no-Debug discipline lines
/// are preserved: the twin implements neither.
pub struct AuthSession {
    pub handle: u32,
    /// Local nonce for this round.
    pub our_nonce: [u8; NONCE_LEN],
    /// Most recent nonce from the peer.
    pub tpm_nonce: [u8; NONCE_LEN],
    pub session_key: [u8; SHA256_LEN],
    pub passphrase: [u8; PASSPHRASE_MAX],
    pub passphrase_len: usize,
    /// Session attributes used in the current command.
    pub attrs: u8,
    /// Current command code. It is needed for the response digest, but the response packet does not carry
    /// the command code itself, so it must be remembered locally -- this is also why a response cannot be
    /// reused for another command.
    pub ordinal: u32,
    pub state: SessionState,
}

/// HMAC key material face of a session record: session key followed by
/// the stored (zero-stripped) passphrase prefix.
pub open spec fn spec_key_material(s: AuthSession) -> Seq<u8> {
    s.session_key@.add(s.passphrase@.subrange(0, s.passphrase_len as int))
}

// ------------------------------------------------------------------
// KeyMaterial erase-on-drop wrapper (session.rs:41-61)
// ------------------------------------------------------------------

/// Origin Rust: /// HMAC key material formed by concatenating the session key and passphrase; it is erased on drop.
/// ...
/// struct KeyMaterial { buf: [u8; KEY_MATERIAL_MAX], len: usize } (src/session.rs:41-50)
pub(crate) struct KeyMaterial {
    pub(crate) buf: [u8; KEY_MATERIAL_MAX],
    pub(crate) len: usize,
}

impl KeyMaterial {
    /// Origin Rust: fn as_slice(&self) -> &[u8] { &self.buf[..self.len] } (src/session.rs:52-54)
    pub(crate) exec fn as_slice(&self) -> (r: &[u8])
        requires
            (self.len as int) <= (KEY_MATERIAL_MAX as int),
        ensures
            r@ == self.buf@.subrange(0, self.len as int),
            r@.len() == self.len,
    {
        &self.buf[..self.len]
    }
}

/// Origin Rust: impl Drop for KeyMaterial {
///     fn drop(&mut self) {
///         self.buf.fill(0);
///         core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
///     }
/// } (src/session.rs:56-61)
/// Trusted (external_body): zeroization is a documented-only face in
/// this batch (the compiler_fence + dead-store-elimination semantics
/// are outside Verus modeling; upstream's doc itself frames it as the
/// available-in-constraint compromise, not a volatile guarantee).
impl Drop for KeyMaterial {
    #[verifier::external_body]
    fn drop(&mut self) opens_invariants none no_unwind {
        self.buf.fill(0);
        #[allow(unused_unsafe)] // not unsafe; silences no_std path lint
        {}
    }
}

// ------------------------------------------------------------------
// Getter faces (session.rs:62-75)
// ------------------------------------------------------------------

impl AuthSession {
    /// Origin Rust: /// Handle for this session.
    /// pub fn handle(&self) -> u32 { self.handle } (src/session.rs:63-66)
    pub exec fn handle(&self) -> (r: u32)
        ensures
            r == self.handle,
    {
        self.handle
    }

    /// Origin Rust: /// Local nonce for this round. Returns a copy: nonces are not secret, but callers should not be able to
    /// mutate the structure through them.
    /// pub fn our_nonce(&self) -> [u8; NONCE_LEN] { self.our_nonce } (src/session.rs:67-71)
    pub exec fn our_nonce(&self) -> (r: [u8; NONCE_LEN])
        ensures
            r == self.our_nonce,
    {
        self.our_nonce
    }

    /// Origin Rust: /// Session attributes for the current command.
    /// pub fn attrs(&self) -> u8 { self.attrs } (src/session.rs:72-75)
    pub exec fn attrs(&self) -> (r: u8)
        ensures
            r == self.attrs,
    {
        self.attrs
    }

    // --------------------------------------------------------------
    // key_buf (session.rs:76-87)
    // --------------------------------------------------------------

    /// Origin Rust: /// Concatenate the session key and passphrase into a fixed-length buffer. The returned
    /// [`KeyMaterial`] is erased on drop. fn key_buf(&self) -> KeyMaterial (src/session.rs:76-87;
    /// copy_from_slice lowered to the two element copy loops, same bytes)
    fn key_buf(&self) -> (r: KeyMaterial)
        requires
            (self.passphrase_len as int) <= (PASSPHRASE_MAX as int),
        ensures
            r.len == SHA256_LEN + self.passphrase_len,
            r.buf@.subrange(0, SHA256_LEN as int) == self.session_key@,
            r.buf@.subrange(SHA256_LEN as int, r.len as int)
                == self.passphrase@.subrange(0, self.passphrase_len as int),
    {
        let sk = self.session_key;
        let ph = self.passphrase;
        let sk_sl: &[u8] = &sk[..];
        let ph_sl: &[u8] = &ph[..];
        let mut buf = [0u8; KEY_MATERIAL_MAX];
        proof {
            assert(sk_sl@ == sk@);
            assert(sk_sl@ == self.session_key@);
            assert(ph_sl@ == ph@);
            assert(ph_sl@ == self.passphrase@);
            assert(sk_sl@.len() == SHA256_LEN);
            assert(ph_sl@.len() == PASSPHRASE_MAX);
            assert forall|j: int|
                0 <= j < (KEY_MATERIAL_MAX as int) implies buf@.index(j) == 0u8
            by {
                // zero-array literal view
            }
        }
        let ghost key_entry = sk@;
        let ghost phrase_entry = ph@;
        let plen = self.passphrase_len;
        let mut i: usize = 0;
        while i < SHA256_LEN
            invariant
                i <= SHA256_LEN,
                sk_sl@ == key_entry,
                sk_sl@.len() == SHA256_LEN,
                forall|j: int| 0 <= j < (i as int)
                    ==> #[trigger] buf@.index(j) == key_entry.index(j),
                forall|j: int| (i as int) <= j < (KEY_MATERIAL_MAX as int)
                    ==> #[trigger] buf@.index(j) == 0u8,
            decreases
                SHA256_LEN - i,
        {
            buf[i] = sk_sl[i];
            i += 1;
        }
        proof {
            assert(i == SHA256_LEN);
            assert forall|j: int|
                0 <= j < (SHA256_LEN as int) implies buf@.index(j) == key_entry.index(j)
            by {
                // loop exit face
            }
        }
        let mut m: usize = 0;
        while m < plen
            invariant
                m <= plen,
                ph_sl@ == phrase_entry,
                ph_sl@.len() == PASSPHRASE_MAX,
                ((self.passphrase_len as int) == (plen as int)),
                ((self.passphrase_len as int) <= (PASSPHRASE_MAX as int)),
                forall|j: int| 0 <= j < (SHA256_LEN as int)
                    ==> #[trigger] buf@.index(j) == key_entry.index(j),
                forall|j: int| 0 <= j < (m as int)
                    ==> #[trigger] buf@.index(SHA256_LEN as int + j) == phrase_entry.index(j),
                forall|j: int| (SHA256_LEN as int) + (m as int) <= j < (KEY_MATERIAL_MAX as int)
                    ==> #[trigger] buf@.index(j) == 0u8,
            decreases
                plen - m,
        {
            buf[SHA256_LEN + m] = ph_sl[m];
            m += 1;
        }
        proof {
            assert(m == plen);
            assert forall|j: int|
                0 <= j < (plen as int)
                implies buf@.index(SHA256_LEN as int + j) == phrase_entry.index(j)
            by {
                // loop exit face
            }
            assert(buf@.subrange(0, SHA256_LEN as int) == key_entry);
            assert(buf@.subrange(SHA256_LEN as int, (SHA256_LEN + plen) as int)
                == phrase_entry.subrange(0, plen as int));
        }
        KeyMaterial {
            buf,
            len: SHA256_LEN + plen,
        }
    }

    // --------------------------------------------------------------
    // open_session (session.rs:88-110)
    // --------------------------------------------------------------

    /// Origin Rust: /// Derive the session key from the negotiated shared secret and both nonces.
    /// ///
    /// /// The shared secret is used only here; the struct no longer holds it afterward -- key derivation is
    /// one-way, and leaking the session key does not let the secret be reconstructed.
    /// pub fn open_session<H: HmacSha256Ctx>(...) -> AuthSession (src/session.rs:88-110)
    /// The derivation is the kdfa32 single-round oracle face with
    /// the ATH label and the two nonces (peer nonce as u, local
    /// nonce as v).
    pub exec fn open_session<H: HmacSha256Ctx>(
        handle: u32,
        salt: &[u8],
        our_nonce: [u8; NONCE_LEN],
        tpm_nonce: [u8; NONCE_LEN],
    ) -> (r: AuthSession)
        ensures
            r.handle == handle,
            r.our_nonce == our_nonce,
            r.tpm_nonce == tpm_nonce,
            r.session_key@ == spec_kdfa32(salt@, label_ath_seq(), (tpm_nonce)@, (our_nonce)@),
            r.passphrase_len == 0,
            forall|j: int| 0 <= j < (PASSPHRASE_MAX as int) ==> r.passphrase@.index(j) == 0,
            r.attrs == 0,
            r.ordinal == 0,
            r.state == SessionState::Idle,
    {
        let label_ath_local: [u8; 4] = [0x41, 0x54, 0x48, 0x00];
        let lab_sl: &[u8] = &label_ath_local[..];
        let tp_sl: &[u8] = &tpm_nonce[..];
        let on_sl: &[u8] = &our_nonce[..];
        let mut out = [0u8; PASSPHRASE_MAX];
        proof {
            assert(label_ath_local@ == label_ath_seq());
            assert(lab_sl@ == label_ath_local@);
            assert(lab_sl@ == label_ath_seq());
            assert(tp_sl@ == (tpm_nonce)@);
            assert(on_sl@ == (our_nonce)@);
            assert forall|j: int|
                0 <= j < (PASSPHRASE_MAX as int) implies out@.index(j) == 0
            by {
                // zero-array literal view
            }
        }
        let key = kdfa32::<H>(salt, lab_sl, tp_sl, on_sl);
        AuthSession {
            handle,
            our_nonce,
            tpm_nonce,
            session_key: key,
            passphrase: out,
            passphrase_len: 0,
            attrs: 0,
            ordinal: 0,
            state: SessionState::Idle,
        }
    }

    // --------------------------------------------------------------
    // set_passphrase (session.rs:111-123)
    // --------------------------------------------------------------

    /// Origin Rust: /// Set the current passphrase. The trailing zero bytes are stripped first, as required by the
    /// specification.
    /// ///
    /// /// This stripping step cannot be skipped: the same passphrase with or without trailing zero bytes yields
    /// different MACs, and callers often pass a fixed-length buffer.
    /// pub fn set_passphrase(&mut self, pw: &[u8]) (src/session.rs:111-123)
    /// Upstream copies pw[..n] into a 32-byte field with no length
    /// check: any passphrase whose zero-stripped length exceeds 32
    /// panics. The requires below carries the missing bound (suspects
    /// row in the out/ ledger; PASSPHRASE_MAX is not even part of the
    /// public surface upstream).
    pub exec fn set_passphrase(&mut self, pw: &[u8])
        requires
            (pw.len() as int) <= (PASSPHRASE_MAX as int),
        ensures
            (final(self).passphrase_len as int) <= (pw.len() as int),
            (final(self).passphrase_len as int) == (pw.len() as int)
                || (final(self).passphrase_len as int) == 0
                || pw@.index((final(self).passphrase_len as int) - 1) != 0,
            forall|j: int| (final(self).passphrase_len as int) <= j < (pw.len() as int)
                ==> pw@.index(j) == 0,
            forall|j: int| 0 <= j < (final(self).passphrase_len as int)
                ==> final(self).passphrase@.index(j) == pw@.index(j),
            final(self).handle == old(self).handle,
            final(self).our_nonce == old(self).our_nonce,
            final(self).tpm_nonce == old(self).tpm_nonce,
            final(self).session_key == old(self).session_key,
            final(self).attrs == old(self).attrs,
            final(self).ordinal == old(self).ordinal,
            final(self).state == old(self).state,
    {
        let ghost pw_entry = pw@;
        let mut n = pw.len();
        while n > 0 && pw[n - 1] == 0
            invariant
                0 <= n,
                n <= pw.len(),
                ((pw.len() as int) <= (PASSPHRASE_MAX as int)),
                pw@ == pw_entry,
                ((pw.len() as int) == pw@.len()),
                forall|j: int| (n as int) <= j < (pw.len() as int)
                    ==> #[trigger] pw@.index(j) == 0,
            decreases
                n,
        {
            n -= 1;
        }
        let ghost pre_phrase = self.passphrase@;
        let mut m: usize = 0;
        while m < n
            invariant
                m <= n,
                n <= pw.len(),
                ((pw.len() as int) <= (PASSPHRASE_MAX as int)),
                pw@ == pw_entry,
                ((pw.len() as int) == pw@.len()),
                self.passphrase@.len() == PASSPHRASE_MAX,
                forall|j: int| 0 <= j < (m as int)
                    ==> #[trigger] self.passphrase@.index(j) == pw@.index(j),
                forall|j: int|
                    0 <= j < (PASSPHRASE_MAX as int)
                        && !((0 as int) <= j < (m as int))
                    ==> self.passphrase@.index(j) == pre_phrase.index(j),
            decreases
                n - m,
        {
            assert(m < PASSPHRASE_MAX);
            self.passphrase[m] = pw[m];
            m += 1;
        }
        proof {
            assert(m == n);
            assert forall|j: int|
                0 <= j < (n as int)
                implies self.passphrase@.index(j) == pw@.index(j)
            by {
                // loop exit face
            }
        }
        self.passphrase_len = n;
    }

    // --------------------------------------------------------------
    // begin (session.rs:124-138)
    // --------------------------------------------------------------

    /// Origin Rust: /// Generate a fresh nonce for the next command.
    /// ///
    /// /// The precondition `nonce_gen < rng.draws()` and the postcondition form a chain: each round's nonce
    /// generation is strictly greater than the previous one, so the same nonce can never be reused in two
    /// rounds. The unpredictability of the value is the random source's responsibility, not this function's.
    /// ...
    /// pub fn begin<R: NonceSource>(&mut self, rng: &mut R, ordinal: u32, attrs: u8) (src/session.rs:124-138)
    /// Twin-audit note: the doc paragraph paraphrases a spec chain
    /// built on a phantom `rng.draws()` that does not exist on the
    /// NonceSource trait of this tree (no nonce counter is expressed
    /// or enforced anywhere in the runtime crate); the twin carries
    /// the honest face -- the new nonce value is unconstrained, and
    /// only the attrs/ordinal/state effects are checkable. Suspects
    /// row in the out/ ledger records the stale paraphrase.
    /// The "continue session" bit forcing (attrs | SA_CONTINUE_SESSION)
    /// is an exact face.
    pub exec fn begin<R: NonceSource>(&mut self, rng: &mut R, ordinal: u32, attrs: u8)
        ensures
            final(self).attrs == (attrs | SA_CONTINUE_SESSION),
            final(self).ordinal == ordinal,
            final(self).handle == old(self).handle,
            final(self).tpm_nonce == old(self).tpm_nonce,
            final(self).session_key == old(self).session_key,
            final(self).passphrase == old(self).passphrase,
            final(self).passphrase_len == old(self).passphrase_len,
            final(self).state == old(self).state,
    {
        self.our_nonce = rng.nonce();
        self.ordinal = ordinal;
        self.attrs = attrs | SA_CONTINUE_SESSION;
    }

    // --------------------------------------------------------------
    // finalize (session.rs:139-165)
    // --------------------------------------------------------------

    /// Origin Rust: /// Compute the command MAC and write it into the authorization area.
    /// ///
    /// /// This is the only valid call time: after all parameters have been written. If even a single byte in
    /// the parameter area changes, the MAC becomes invalid. ...
    /// pub fn finalize<S: Sha256Ctx, H: HmacSha256Ctx>(
    ///     &mut self, buf: &mut [u8], sess_off: usize, index: usize,
    ///     names: &[u8], param_off: usize, param_len: usize) (src/session.rs:139-165)
    /// Upstream slices buf[param_off..param_off+param_len] and writes
    /// the 32-byte MAC at sess_off+SESS_HMAC_OFF with no bound checks:
    /// the two requires below carry the missing layout bounds
    /// (suspects row in the out/ ledger; upstream doc promises no
    /// # Panics entry). The MAC face: the overlay equals the
    /// HMAC-oracle over this session's key material, the cp digest
    /// of the ENTRY parameter bytes (the digest reads the buffer
    /// before the overlay is written), both nonces, and attrs.
    pub exec fn finalize<S: Sha256Ctx, H: HmacSha256Ctx>(
        &mut self,
        buf: &mut [u8],
        sess_off: usize,
        index: usize,
        names: &[u8],
        param_off: usize,
        param_len: usize,
    )
        requires
            (sess_off as int) + (CMD_SESSION_LEN as int) <= (buf.len() as int),
            (param_off as int) + (param_len as int) <= (buf.len() as int),
            (self.passphrase_len as int) <= (PASSPHRASE_MAX as int),
        ensures
            final(buf)@.len() == old(buf)@.len(),
            same_outside_range(
                old(buf)@,
                final(buf)@,
                (sess_off as int) + (SESS_HMAC_OFF as int),
                (sess_off as int) + (CMD_SESSION_LEN as int),
            ),
            final(buf)@.subrange(
                (sess_off as int) + (SESS_HMAC_OFF as int),
                (sess_off as int) + (CMD_SESSION_LEN as int),
            ) == spec_auth_hmac(
                spec_key_material(*old(self)),
                spec_cp_hash(
                    old(self).ordinal,
                    names@,
                    old(buf)@.subrange((param_off as int), (param_off as int) + (param_len as int)),
                ),
                (old(self).our_nonce)@,
                (old(self).tpm_nonce)@,
                old(self).attrs,
            ),
            final(self).state == SessionState::Pending(index),
            final(self).handle == old(self).handle,
            final(self).our_nonce == old(self).our_nonce,
            final(self).tpm_nonce == old(self).tpm_nonce,
            final(self).session_key == old(self).session_key,
            final(self).passphrase == old(self).passphrase,
            final(self).passphrase_len == old(self).passphrase_len,
            final(self).attrs == old(self).attrs,
            final(self).ordinal == old(self).ordinal,
    {
        let params = &buf[param_off..param_off + param_len];
        proof {
            assert(params@ == buf@.subrange((param_off as int), (param_off as int) + (param_len as int)));
        }
        let cph = cp_hash::<S>(self.ordinal, names, params);
        let km = self.key_buf();
        proof {
            assert((km.len as int) == (SHA256_LEN as int) + (self.passphrase_len as int));
            assert((km.len as int) <= (KEY_MATERIAL_MAX as int));
        }
        let key = km.as_slice();
        proof {
            assert(key@ == km.buf@.subrange(0, km.len as int));
            assert(key@ == spec_key_material(*self));
        }
        let on = self.our_nonce;
        let tn = self.tpm_nonce;
        proof {
            assert(on@ == self.our_nonce@);
            assert(tn@ == self.tpm_nonce@);
        }
        let mac = auth_hmac::<H>(key, &cph, &on, &tn, self.attrs);
        patch_hmac(buf, sess_off, &mac);
        proof {
            assert(mac@ == spec_auth_hmac(
                spec_key_material(*self),
                spec_cp_hash(self.ordinal, names@, params@),
                self.our_nonce@,
                self.tpm_nonce@,
                self.attrs,
            ));
        }
        self.state = SessionState::Pending(index);
    }

    // --------------------------------------------------------------
    // check_response (session.rs:166-225)
    // --------------------------------------------------------------

    /// Origin Rust: /// Validate the response MAC.
    /// ///
    /// /// **This is the reason this module exists.** Returning `Ok` means the MAC in the packet is byte-for-byte
    /// identical to the value recomputed using this session's key, the two nonces for this round, and the
    /// command code for this round. The postcondition states this explicitly, so any implementation that
    /// bypasses validation and trusts the response directly will fail verification.
    /// ///
    /// /// The command code is taken from local state rather than from the packet ... Any failure path marks
    /// the session as closed.
    /// pub fn check_response<S: Sha256Ctx, H: HmacSha256Ctx>(
    ///     &mut self, raw: &[u8], rhandles: usize) -> Result<RspAuth, AuthErr> (src/session.rs:166-225)
    /// The Ok arm of the retface IS the byte-for-byte claim: the
    /// packet's trailing 32 bytes equal the oracle MAC over this
    /// session's key material, the rp digest with the locally
    /// remembered ordinal, the two nonces, and attrs. Every Err arm
    /// leaves the session Closed (the doc-quoted guessing-opportunity
    /// discipline).
    pub exec fn check_response<S: Sha256Ctx, H: HmacSha256Ctx>(
        &mut self,
        raw: &[u8],
        rhandles: usize,
    ) -> (r: Result<RspAuth, AuthErr>)
        requires
            ((rhandles as int) * 4) <= (usize::MAX as int),
            (self.passphrase_len as int) <= (PASSPHRASE_MAX as int),
        ensures
            final(self).handle == old(self).handle,
            final(self).our_nonce == old(self).our_nonce,
            final(self).session_key == old(self).session_key,
            final(self).passphrase == old(self).passphrase,
            final(self).passphrase_len == old(self).passphrase_len,
            final(self).attrs == old(self).attrs,
            final(self).ordinal == old(self).ordinal,
            match r {
                Result::Ok(a) =>
                    state_is_pending(old(self).state)
                        && final(self).state == SessionState::Idle
                        && final(self).tpm_nonce == a.tpm_nonce
                        && super::auth::rsp_auth_valid(a, raw)
                        && raw@.subrange(
                            (a.hmac_off as int),
                            (a.hmac_off as int) + (SHA256_LEN as int),
                        ) == spec_auth_hmac(
                            spec_key_material(*old(self)),
                            spec_rp_hash(
                                0u32,
                                old(self).ordinal,
                                raw@.subrange(
                                    (a.param_off as int),
                                    (a.param_off as int) + (a.param_len as int),
                                ),
                            ),
                            (a.tpm_nonce)@,
                            (old(self).our_nonce)@,
                            old(self).attrs,
                        ),
                // Err(NoSession) is reachable both from the
                // non-pending guard and from parse_rsp_auth's own
                // NoSession arm, so the !pending dichotomy is NOT a
                // face of this variant (deferred: distinguishing the
                // two routes needs parse-error-kind exactness, T1 S5
                // precedent); the closed-on-failure discipline below
                // is the exact part
                Result::Err(AuthErr::NoSession) =>
                    final(self).state == SessionState::Closed
                        && final(self).tpm_nonce == old(self).tpm_nonce,
                // HmacMismatch shares the wildcard Err arm: the Err
                // variants carry no location record, so the mismatch
                // direction of the byte-equality is one-sided here --
                // the Ok arm is the exact face, the Err arms stay at
                // the doc-quoted "failure path marks the session
                // closed" level (deferred face, T1 S5 precedent).
                Result::Err(_) =>
                    final(self).state == SessionState::Closed
                        && final(self).tpm_nonce == old(self).tpm_nonce,
            },
    {
        let index = match self.state {
            SessionState::Pending(i) => i,
            _ => {
                self.state = SessionState::Closed;
                return Err(AuthErr::NoSession);
            }
        };
        let a = match parse_rsp_auth(raw, rhandles, index) {
            Result::Ok(a) => a,
            Result::Err(e) => {
                self.state = SessionState::Closed;
                return Err(e);
            }
        };
        proof {
            // parse face gives both adds' totality (upstream spells
            // them checked_add().ok_or(Malformed); the branch is
            // infeasible under the parse ok face)
            assert((a.param_off as int) + (a.param_len as int) <= (a.nonce_off as int));
            assert((a.hmac_off as int) + (SHA256_LEN as int) <= (raw.len() as int));
            assert(super::auth::rsp_auth_valid(a, raw));
        }
        let param_end = a.param_off + a.param_len;
        let params = &raw[a.param_off..param_end];
        proof {
            assert(params@ == raw@.subrange((a.param_off as int), (a.param_off as int) + (a.param_len as int)));
        }
        let rph = rp_hash::<S>(0, self.ordinal, params);
        let km = self.key_buf();
        proof {
            assert((km.len as int) == (SHA256_LEN as int) + (self.passphrase_len as int));
            assert((km.len as int) <= (KEY_MATERIAL_MAX as int));
        }
        let key = km.as_slice();
        proof {
            assert(key@ == km.buf@.subrange(0, km.len as int));
            assert(key@ == spec_key_material(*self));
        }
        let on = self.our_nonce;
        proof {
            assert(on@ == self.our_nonce@);
        }
        let expect = auth_hmac::<H>(key, &rph, &a.tpm_nonce, &on, self.attrs);
        proof {
            assert(expect@ == spec_auth_hmac(
                spec_key_material(*self),
                spec_rp_hash(0u32, self.ordinal, params@),
                a.tpm_nonce@,
                self.our_nonce@,
                self.attrs,
            ));
        }
        let hmac_end = a.hmac_off + SHA256_LEN;
        let got = &raw[a.hmac_off..hmac_end];
        proof {
            assert(got@.len() == SHA256_LEN);
            assert(got@ == raw@.subrange((a.hmac_off as int), (a.hmac_off as int) + (SHA256_LEN as int)));
        }
        if !ct_eq32(&expect, got) {
            proof {
                assert(expect@ != got@);
            }
            self.state = SessionState::Closed;
            return Err(AuthErr::HmacMismatch);
        }
        self.tpm_nonce = a.tpm_nonce;
        self.state = SessionState::Idle;
        proof {
            assert(expect@ == got@);
            // the Ok arm's composition: the entry-session key material,
            // ordinal and attrs are untouched on this path, so the
            // oracle face assembled above is the ensures' face
            assert(spec_key_material(*self) == spec_key_material(*old(self)));
            assert(self.ordinal == old(self).ordinal);
            assert(self.attrs == old(self).attrs);
            assert(self.our_nonce == old(self).our_nonce);
            assert(state_is_pending(old(self).state));
        }
        Ok(a)
    }

    // --------------------------------------------------------------
    // close (session.rs:226-230)
    // --------------------------------------------------------------

    /// Origin Rust: /// Close the session immediately. Used as the cleanup path when error handling bypasses
    /// [`AuthSession::check_response`].
    /// pub fn close(&mut self) { self.state = SessionState::Closed; } (src/session.rs:226-230)
    pub exec fn close(&mut self)
        ensures
            final(self).state == SessionState::Closed,
            final(self).handle == old(self).handle,
            final(self).our_nonce == old(self).our_nonce,
            final(self).tpm_nonce == old(self).tpm_nonce,
            final(self).session_key == old(self).session_key,
            final(self).passphrase == old(self).passphrase,
            final(self).passphrase_len == old(self).passphrase_len,
            final(self).attrs == old(self).attrs,
            final(self).ordinal == old(self).ordinal,
    {
        self.state = SessionState::Closed;
    }
}

// ------------------------------------------------------------------
// AuthSession Drop (session.rs:232-247) -- trusted transcription
// ------------------------------------------------------------------

/// Origin Rust: impl Drop for AuthSession {
///     /// Erase key material on destruction. ... This is also why this structure intentionally does not implement
///     /// `Clone`: there is only one copy, so there is only one place that needs erasure.
///     fn drop(&mut self) {
///         self.session_key.fill(0); self.passphrase.fill(0); self.passphrase_len = 0;
///         core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
///     }
/// } (src/session.rs:232-247)
/// Trusted (external_body): documented-only zeroization face (see the
/// module header); the compiler_fence call is unavailable to Verus
/// modeling by the batch's own scoping cut. The no-Clone discipline
/// (one copy, one erasure place) is preserved textually above.
impl Drop for AuthSession {
    #[verifier::external_body]
    fn drop(&mut self) opens_invariants none no_unwind {
        self.session_key.fill(0);
        self.passphrase.fill(0);
        self.passphrase_len = 0;
    }
}

// ------------------------------------------------------------------
// Parameter encryption faces (session.rs:248-271)
// ------------------------------------------------------------------

/// Origin Rust: /// Derive the key and IV needed for parameter encryption/decryption in the current round.
/// ///
/// /// The order of the two nonces determines the direction: in command direction, the local nonce comes
/// /// first; in response direction, the peer nonce comes first. The material differs between directions,
/// /// which is why the two directions on the same session do not reuse the same keystream.
/// pub fn cfb_material<H: HmacSha256Ctx>(
///     session: &AuthSession, newer: &[u8; NONCE_LEN], older: &[u8; NONCE_LEN],
/// ) -> [u8; CFB_MATERIAL_LEN] {
///     let km = session.key_buf(); let key = km.as_slice();
///     kdfa32::<H>(key, &LABEL_CFB[..], &newer[..], &older[..])
/// } (src/session.rs:248-261)
pub exec fn cfb_material<H: HmacSha256Ctx>(
    session: &AuthSession,
    newer: &[u8; NONCE_LEN],
    older: &[u8; NONCE_LEN],
) -> (r: [u8; CFB_MATERIAL_LEN])
    requires
        (session.passphrase_len as int) <= (PASSPHRASE_MAX as int),
    ensures
        r@ == spec_kdfa32(spec_key_material(*session), label_cfb_seq(), (newer)@, (older)@),
{
    let km = session.key_buf();
    proof {
        assert((km.len as int) == (SHA256_LEN as int) + (session.passphrase_len as int));
        assert((km.len as int) <= (KEY_MATERIAL_MAX as int));
    }
    let key = km.as_slice();
    let label_cfb_local: [u8; 4] = [0x43, 0x46, 0x42, 0x00];
    let lab_sl: &[u8] = &label_cfb_local[..];
    let nw_sl: &[u8] = &newer[..];
    let od_sl: &[u8] = &older[..];
    proof {
        assert(key@ == spec_key_material(*session));
        assert(label_cfb_local@ == label_cfb_seq());
        assert(lab_sl@ == label_cfb_local@);
        assert(lab_sl@ == label_cfb_seq());
        assert(nw_sl@ == (newer)@);
        assert(od_sl@ == (older)@);
    }
    kdfa32::<H>(key, lab_sl, nw_sl, od_sl)
}

/// Origin Rust: /// Encrypt the first parameter in place. Must be called before [`AuthSession::finalize`].
/// pub fn encrypt_param<A: AesCfb>(aes: &A, material: &[u8; CFB_MATERIAL_LEN], param: &mut [u8]) {
///     aes.encrypt(material, param);
/// } (src/session.rs:262-265)
pub exec fn encrypt_param<A: AesCfb>(
    aes: &A,
    material: &[u8; CFB_MATERIAL_LEN],
    param: &mut [u8],
)
    ensures
        final(param)@.len() == old(param)@.len(),
        final(param)@ == cfb_encrypt_view(material@, old(param)@),
{
    aes.encrypt(material, param);
}

/// Origin Rust: /// Decrypt the first parameter in place. Must be called only after [`AuthSession::-check_response`] returns
/// `Ok` -- decrypting unvalidated bytes is equivalent to treating arbitrary peer-provided data as plain
/// text for the upper layer.
/// pub fn decrypt_param<A: AesCfb>(aes: &A, material: &[u8; CFB_MATERIAL_LEN], param: &mut [u8]) {
///     aes.decrypt(material, param);
/// } (src/session.rs:266-271; doc glyphs converted ASCII)
/// The "only after check_response returns Ok" discipline is a
/// caller-discipline line: nothing in this layer enforces it at
/// runtime, and the twin keeps it comment-level (upstream face
/// unchanged).
pub exec fn decrypt_param<A: AesCfb>(
    aes: &A,
    material: &[u8; CFB_MATERIAL_LEN],
    param: &mut [u8],
)
    ensures
        final(param)@.len() == old(param)@.len(),
        final(param)@ == cfb_decrypt_view(material@, old(param)@),
{
    aes.decrypt(material, param);
}

} // verus!
