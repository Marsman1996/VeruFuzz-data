//! tpm-core 0.1.4 crypto trust-boundary traits and single-round KDF
//! (src/crypto.rs) -- Verus translation.
//!
//! This batch's scoping cut (harness inventory section 7): SHA-256,
//! HMAC and AES-CFB bodies live outside this crate; what this layer
//! owes is the byte layout and ordering of the update calls into those
//! traits (the serialization facts). The traits below are therefore
//! trusted spec faces ONLY: each trait carries ghost views (the bound
//! key and the concatenated update stream) whose sole purpose is to
//! make "which bytes were fed, in which order" a checkable fact at
//! every call site; the digest bodies stay uninterpreted oracles.
//!
//! The kdfa32 doc pins the derivation to ONE counter round (the
//! counter advances only once); with the multi-round loop gone the
//! spec indeed reduces to a single equality -- here the equality
//! between the concatenated update stream and
//! kdfa32_stream(label, u, v).

use vstd::prelude::*;

verus! {

use super::cursor::{be16_bytes, be16_bytes_spec, be32_bytes, be32_bytes_spec};

// ------------------------------------------------------------------
// Constants (crypto.rs:1-18)
// ------------------------------------------------------------------

/// Origin Rust: /// SHA-256 digest length. The nonce, session key, and HMAC fields in this layer all use this length.
/// pub const SHA256_LEN: usize = 32; (src/crypto.rs:1-2)
pub const SHA256_LEN: usize = 32;
/// Origin Rust: /// Session nonce length. ...
/// pub const NONCE_LEN: usize = SHA256_LEN; (src/crypto.rs:3-6)
pub const NONCE_LEN: usize = SHA256_LEN;
/// Origin Rust: pub const AES_KEY_LEN: usize = 16; (src/crypto.rs:7)
pub const AES_KEY_LEN: usize = 16;
/// Origin Rust: pub const AES_BLOCK_LEN: usize = 16; (src/crypto.rs:8)
pub const AES_BLOCK_LEN: usize = 16;
/// Origin Rust: /// Key material needed for parameter encryption/decryption ... exactly one digest-block length ...
/// pub const CFB_MATERIAL_LEN: usize = AES_KEY_LEN + AES_BLOCK_LEN; (src/crypto.rs:9-14)
pub const CFB_MATERIAL_LEN: usize = AES_KEY_LEN + AES_BLOCK_LEN;
/// Origin Rust: /// Maximum space for a password in the session structure.
/// pub(crate) const PASSPHRASE_MAX: usize = SHA256_LEN; (src/crypto.rs:15-16)
/// Visibility opened pub (Origin note): the twin's public session
/// layer carries this bound in a pub requires (upstream panics
/// instead); runtime value unchanged.
pub const PASSPHRASE_MAX: usize = SHA256_LEN;
/// Origin Rust: /// Maximum HMAC key material: session key followed by passphrase.
/// pub(crate) const KEY_MATERIAL_MAX: usize = SHA256_LEN + PASSPHRASE_MAX; (src/crypto.rs:17-18)
/// Visibility pub (Origin note): same treatment as PASSPHRASE_MAX;
/// ghost/spec consumers only, runtime value unchanged.
pub const KEY_MATERIAL_MAX: usize = SHA256_LEN + PASSPHRASE_MAX;

/// Origin Rust: pub(crate) fn be16_arr(v: u16) -> [u8; 2] {
///     super::cursor::be16_bytes(v)
/// } (src/crypto.rs:19-21; the cross-module path is spelled by the
/// sibling mount).
pub(crate) exec fn be16_arr(v: u16) -> (r: [u8; 2])
    ensures
        r@ == be16_bytes_spec(v),
{
    be16_bytes(v)
}

/// Origin Rust: pub(crate) fn be32_arr(v: u32) -> [u8; 4] {
///     super::cursor::be32_bytes(v)
/// } (src/crypto.rs:22-24)
pub(crate) exec fn be32_arr(v: u32) -> (r: [u8; 4])
    ensures
        r@ == be32_bytes_spec(v),
{
    be32_bytes(v)
}

// ------------------------------------------------------------------
// Trusted crypto oracles (digest bodies stay outside verification)
// ------------------------------------------------------------------

/// Trusted oracle for the SHA-256 digest over a complete update
/// stream. Bodyless by design: the digest internals live in the
/// trait implementations outside this crate; the verifiable fact of
/// this layer is which bytes enter the stream, in which order, not
/// the digest arithmetic.
pub uninterp spec fn sha256_digest(stream: Seq<u8>) -> Seq<u8>;

/// Trusted oracle for HMAC-SHA-256 (key, complete update stream).
pub uninterp spec fn hmac_sha256_digest(key: Seq<u8>, stream: Seq<u8>) -> Seq<u8>;

/// Trusted oracle face of an in-place AES-CFB encryption pass over
/// `data` with `material` (key ++ iv); the transform preserves
/// length, and the output depends only on the material and the input
/// bytes (the determinism face this layer can honestly state; the
/// cipher body is not verifiable here).
pub uninterp spec fn cfb_encrypt_view(material: Seq<u8>, data: Seq<u8>) -> Seq<u8>;

/// Trusted oracle face of an in-place AES-CFB decryption pass
/// (same treatment as cfb_encrypt_view).
pub uninterp spec fn cfb_decrypt_view(material: Seq<u8>, data: Seq<u8>) -> Seq<u8>;

// ------------------------------------------------------------------
// Trust-boundary traits (crypto.rs:25-42) -- spec faces only
// ------------------------------------------------------------------

/// Origin Rust: pub trait Sha256Ctx: Sized {
///     fn new() -> Self;
///     fn update(&mut self, data: &[u8]);
///     fn finish(self) -> [u8; SHA256_LEN];
/// } (src/crypto.rs:25-29)
/// Trusted spec face: the ghost `stream` view concatenates every
/// update argument in call order; `finish` is pinned to the digest
/// oracle over that stream. This is the SPIRIT-style update log that
/// makes the serialization ordering of every layer above checkable.
pub trait Sha256Ctx: Sized {
    /// Ghost view: concatenated update arguments so far.
    spec fn stream(&self) -> Seq<u8>;

    fn new() -> (r: Self)
        ensures
            r.stream() == Seq::<u8>::empty(),
    ;

    fn update(&mut self, data: &[u8])
        ensures
            final(self).stream() == old(self).stream().add(data@),
    ;

    fn finish(self) -> (r: [u8; SHA256_LEN])
        ensures
            r@ == sha256_digest(self.stream()),
    ;
}

/// Origin Rust: pub trait HmacSha256Ctx: Sized {
///     fn with_key(key: &[u8]) -> Self;
///     fn update(&mut self, data: &[u8]);
///     fn finish(self) -> [u8; SHA256_LEN];
/// } (src/crypto.rs:30-34)
/// Trusted spec face: `key_view` remembers the bound key, `stream`
/// concatenates the update arguments in call order, and `finish` is
/// pinned to the HMAC oracle over both.
pub trait HmacSha256Ctx: Sized {
    /// Ghost view: the key bound at construction.
    spec fn key_view(&self) -> Seq<u8>;

    /// Ghost view: concatenated update arguments so far.
    spec fn stream(&self) -> Seq<u8>;

    fn with_key(key: &[u8]) -> (r: Self)
        ensures
            r.key_view() == key@,
            r.stream() == Seq::<u8>::empty(),
    ;

    fn update(&mut self, data: &[u8])
        ensures
            final(self).stream() == old(self).stream().add(data@),
            final(self).key_view() == old(self).key_view(),
    ;

    fn finish(self) -> (r: [u8; SHA256_LEN])
        ensures
            r@ == hmac_sha256_digest(self.key_view(), self.stream()),
    ;
}

/// Origin Rust: pub trait NonceSource {
///     fn nonce(&mut self) -> [u8; NONCE_LEN];
/// } (src/crypto.rs:35-37)
/// No spec face: the entropy of the drawn value is the random
/// source's responsibility, not this layer's (the same honest
/// treatment the upstream begin() doc concedes when it hands the
/// "unpredictability" claim to the source). The draws() precondition
/// that the upstream begin() doc names does not exist on this trait
/// surface; see the session.rs begin() Origin note.
pub trait NonceSource {
    fn nonce(&mut self) -> [u8; NONCE_LEN];
}

/// Origin Rust: pub trait AesCfb {
///     /// In-place encryption. The first half of `material` is the key and the second half is the IV.
///     fn encrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8]);
///     fn decrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8]);
/// } (src/crypto.rs:39-42)
/// Trusted spec face: the in-place pass preserves length (automatic
/// for the slice type) and the output is the oracle image of the
/// material and the old bytes -- the determinism fact, nothing more.
pub trait AesCfb {
    fn encrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8])
        ensures
            final(data)@.len() == old(data)@.len(),
            final(data)@ == cfb_encrypt_view(material@, old(data)@),
    ;

    fn decrypt(&self, material: &[u8; CFB_MATERIAL_LEN], data: &mut [u8])
        ensures
            final(data)@.len() == old(data)@.len(),
            final(data)@ == cfb_decrypt_view(material@, old(data)@),
    ;
}

// ------------------------------------------------------------------
// Key derivation labels (crypto.rs:43-46)
// ------------------------------------------------------------------

/// Origin Rust: /// Session key derivation label (including trailing NUL).
/// pub(crate) const LABEL_ATH: [u8; 4] = [0x41, 0x54, 0x48, 0x00]; (src/crypto.rs:43-44)
pub(crate) const LABEL_ATH: [u8; 4] = [0x41, 0x54, 0x48, 0x00];
/// Origin Rust: /// Parameter encryption/decryption key derivation label (including trailing NUL).
/// pub(crate) const LABEL_CFB: [u8; 4] = [0x43, 0x46, 0x42, 0x00]; (src/crypto.rs:45-46)
pub(crate) const LABEL_CFB: [u8; 4] = [0x43, 0x46, 0x42, 0x00];

/// Sequence twin of LABEL_ATH (the wire bytes the KDF feeds).
pub open spec fn label_ath_seq() -> Seq<u8> {
    seq![0x41u8, 0x54u8, 0x48u8, 0x00u8]
}

/// Sequence twin of LABEL_CFB.
pub open spec fn label_cfb_seq() -> Seq<u8> {
    seq![0x43u8, 0x46u8, 0x42u8, 0x00u8]
}

// ------------------------------------------------------------------
// kdfa32 (crypto.rs:47-70)
// ------------------------------------------------------------------

/// The single-round update stream of kdfa32: the counter (be32 of 1)
/// first, then label, u, v, then the requested bit count (be32 of
/// 256). This is the exact byte sequence the upstream doc fixes by
/// "the counter advances only once".
pub open spec fn kdfa32_stream(label: Seq<u8>, u: Seq<u8>, v: Seq<u8>) -> Seq<u8> {
    be32_bytes_spec(1u32)
        .add(label)
        .add(u)
        .add(v)
        .add(be32_bytes_spec(256u32))
}

/// Full oracle face of kdfa32: the derived material is the HMAC of
/// the key over the single-round stream above.
pub open spec fn spec_kdfa32(key: Seq<u8>, label: Seq<u8>, u: Seq<u8>, v: Seq<u8>) -> Seq<u8> {
    hmac_sha256_digest(key, kdfa32_stream(label, u, v))
}

/// Origin Rust: /// Derive 32 bytes of key material.
/// ///
/// /// The counter advances only once. ... Once it is fixed to a single round, the loop invariant and termination proof no
/// /// longer matter, and the specification reduces to a single equality. ...
/// pub(crate) fn kdfa32<H: HmacSha256Ctx>(
///     key: &[u8], label: &[u8], u: &[u8], v: &[u8],
/// ) -> [u8; SHA256_LEN] {
///     let mut h = H::with_key(key);
///     let counter = be32_arr(1);
///     let bits = be32_arr(256);
///     h.update(&counter[..]);
///     h.update(label);
///     h.update(u);
///     h.update(v);
///     h.update(&bits[..]);
///     h.finish()
/// } (src/crypto.rs:47-70)
/// The ordering of update calls against the ghost stream is the
/// obligation this twin verifies; the digest value itself is the
/// trusted oracle face.
pub(crate) exec fn kdfa32<H: HmacSha256Ctx>(
    key: &[u8],
    label: &[u8],
    u: &[u8],
    v: &[u8],
) -> (r: [u8; SHA256_LEN])
    ensures
        r@ == spec_kdfa32(key@, label@, u@, v@),
{
    let mut h = H::with_key(key);
    let counter = be32_arr(1u32);
    let bits = be32_arr(256u32);
    let counter_sl: &[u8] = &counter[..];
    let bits_sl: &[u8] = &bits[..];
    proof {
        // array full-slice views are the array views themselves
        assert(counter_sl@ == counter@);
        assert(bits_sl@ == bits@);
    }
    h.update(counter_sl);
    proof {
        assert(h.key_view() == key@);
        assert(h.stream() == Seq::<u8>::empty().add(counter_sl@));
        assert(h.stream() == counter_sl@);
    }
    h.update(label);
    proof {
        assert(h.stream() == counter_sl@.add(label@));
    }
    h.update(u);
    proof {
        assert(h.stream() == counter_sl@.add(label@).add(u@));
    }
    h.update(v);
    proof {
        assert(h.stream() == counter_sl@.add(label@).add(u@).add(v@));
    }
    h.update(bits_sl);
    proof {
        assert(h.stream()
            == counter_sl@.add(label@).add(u@).add(v@).add(bits_sl@));
        assert(h.stream()
            == be32_bytes_spec(1u32)
                .add(label@)
                .add(u@)
                .add(v@)
                .add(be32_bytes_spec(256u32)));
        assert(h.stream() == kdfa32_stream(label@, u@, v@));
    }
    h.finish()
}

} // verus!
