//! faest 0.3.0 -- Verus transcription of src/faest.rs, batch FA13
//! (the keygen / sign / verify outer chain; the closing member of
//! the sign/verify family).
//!
//! Upstream (faest.rs, 781 lines, pin 9ccc68c0; code/ read-only):
//! the outer sign/verify driver -- SignatureRefMut (:28-110 incl.
//! the From<&mut [u8]> split chain :53-77 and the three save faces),
//! SignatureRef (:112-191, the verifier-side carve + TryFrom :139-168
//! with the ::4 challenge gate), the FaestHash trait (:193-231) with
//! its RO blanket impl (:233-332), faest_keygen (:334-341),
//! check_challenge_3 (:343-358), faest_sign (:360-376) /
//! faest_unpacked_sign (:378-391) / sign (:393-485), faest_verify
//! (:487-500) / verify (:502-572). The two cfg(test) modules
//! (:574-681 generic sign_and_verify + serialize; :690-781 the
//! official-vector faest_tvs KAT module) are outside the Verus
//! surface -- their value rows land as the harness KAT arms of this
//! batch's notes/oracle kit (the upstream test vectors consumed:
//! tests/data/PQCsignKAT_faest{,_em_}128f.rsp, the interop-probe
//! byte-identical NIST rsp regeneration, out/kverus-run/
//! interop-probe/notes.md).
//!
//! Representation lowerings / trust boundaries (this batch's
//! records, first-hand):
//!   - `RO<P>` (the type alias :25-26) drops to the FA9-row carrier
//!     selection: BaseParams128 binds RandomOracleShake128
//!     (parameter.rs :180, first-hand). The twin lands the
//!     Shake128 AXIS (the exec-active axis of the whole landed
//!     constraint tree is lambda == 128: no ZK hasher driver has
//!     landed beyond GF128; the 192/256 chains await those drivers
//!     -- record, out/kverus-run/FA13/notes.md). The FaestHash
//!     trait + its RO blanket impl re-erect as the free
//!     `faest_hash_*` faces below (the FA4-1 impl-trait-for-type
//!     ban), one face per trait method, Origin-anchored.
//!   - `IV` / `IVSize` (prg.rs :21-23, Array<u8, U16>) lowers to a
//!     16-byte slice window of the signature (prg.rs itself is NOT
//!     consumed by this file; no CTR face here).
//!   - `Error` (the external signature-crate carrier; the lib.rs
//!     re-export) lowers to the bool / Option lanes (the FA10 Error
//!     record; Err(Error::new()) <-> false / None).
//!   - `declassify!` (lib.rs macro) compiles to a no-op unless the
//!     valgrind feature is on (the FA10 memcheck record); the one
//!     site (:469) transcribes as a record note below.
//!   - volecommit / volereconstruct / VoleCommitResult /
//!     VoleReconstructResult (vole.rs) and `<P>::BAVC::open` +
//!     BavcOpenResult (bavc.rs): NO twin exists for vole.rs; bavc.rs
//!     is the FA7 in-flight tree (not mounted; zero file
//!     intersection). These re-erect as the local trusted shim faces
//!     at the bottom of this file (external_body + panic-stub
//!     bodies, the FA4/FA5 trusted-core precedent; D-FA10-1-style
//!     data-contract ensures rows only). The real bodies are the
//!     FA8 batch's kit entry (D-FA13-3).
//!   - P::OWF::witness(sk) (:373) and P::OWF::prove (:443) /
//!     verify (:545) lower to the data rows + the aes_prove /
//!     aes_verify faces of src/zk_constraints.rs (this batch): the
//!     witness bytes arrive as a data parameter (the FA10 ruling),
//!     u / v / com ride the vole shim carriers.
//!   - SecretKey / PublicKey / UnpackedSecretKey lower to their
//!     byte-slice rows (owf_key / owf_input / owf_output; the FA10
//!     layout faces; the PublicKey TYPE has no twin).
//!   - The signature carve chains (:53-63 / :140-149) re-erect as
//!     the two exec-verified split faces below (the runtime size
//!     rows are explicit parameters; the FA9 tower rows pin them at
//!     the call sites). Note (first-hand): the trailing `ctr`
//!     segment is exactly FOUR bytes (save_decom_and_ctr writes
//!     ctr.to_le_bytes() through copy_from_slice at :108; parse_ctr
//!     TryInto's a [u8; 4] at :189), so the SIGNATURE row size ends
//!     iv_pre(IVSize = 16) + ctr(4).
//!   - `for ctr in 0u32..` (:465): the upstream grinding loop is
//!     the u32-exhaustive range (yields every ctr in 0..=u32::MAX
//!     then exits); the twin spells the same bound as a counted
//!     u64 counter loop (faithful; termination-free zone only under
//!     the frozen body).
//!   - faest_sign (:360-376) / faest_unpacked_sign (:378-391) /
//!     faest_verify (:487-500) are #[inline] one-liner wrappers over
//!     the carve + witness rows + sign/verify; the twin's
//!     sign_chain / verify_chain faces carry the composition (the
//!     wrappers' distinct rows -- which witness source feeds in --
//!     recorded at the faces).
//!
//! KeypairGenerator / lib.rs personality records (record-only): the
//! KeypairGenerator trait (lib.rs :189-192, `generate` -> the keygen
//! faces), the define_impl macro family's SigningKey /
//! UnpackedSigningKey types and the Signer / Verifier /
//! RandomizedSigner rows (lib.rs :312-506) dispatch to exactly the
//! faces transplanted here; the capi SIGNATURE_SIZE / SK_SIZE /
//! PK_SIZE consts are the FA9 tower rows consumed as the explicit
//! size parameters. lib.rs stays untouched (the FA1-frozen crate
//! root); these rows are references, not a transplantation.

use vstd::prelude::*;

use crate::random_oracles::{
    shake128_byte, Hasher128, RandomOracleShake128,
};
use crate::parameter::{tau0_offset_unchecked, tau1_offset_unchecked};
use crate::utils::{chall_to_u16, get_bit, xor_arrays_into, xor_arrays_inplace};
use crate::universal_hashing::VoleHasher128;
use crate::zk_constraints::{aes_prove, aes_verify};

verus! {

// ===========================================================================
// check_challenge_3 (upstream :343-358).
// Origin Rust:
//     fn check_challenge_3<P, O>(chall3: &[u8]) -> bool {
//         let start_byte = (O::Lambda::USIZE - P::WGRIND::USIZE) / 8;
//         // Discard all bits before position "lambda - w_grind"
//         let start_byte_0s = chall3[start_byte] >> ((O::Lambda::USIZE
//             - P::WGRIND::USIZE) % 8);
//         if start_byte_0s != 0 { return false; }
//         // Check that all the following bytes are 0s
//         chall3.iter().skip(start_byte + 1).all(|b| *b == 0) }
// The type-level Lambda / WGRIND rows lower to the two explicit
// parameters (FA9 tower rows pin them at the call sites). The
// WGRIND >= 1 row (the FAEST grind discipline) keeps the upstream
// chall3[start_byte] read in bounds (the usize rows of the tower).
// ===========================================================================

/// The value spec of the grind check (the two upstream phases):
/// the high (lambda - w_grind) bits of the chall3 slice must be zero.
pub open spec fn check_challenge_3_spec(
    chall3: Seq<u8>,
    lambda: int,
    w_grind: int,
) -> bool {
    let start_byte = (lambda - w_grind) / 8;
    let shift = (lambda - w_grind) % 8;
    (chall3[start_byte] >> (shift as u8)) == 0
        && forall |j: int|
            start_byte + 1 <= j < chall3.len() ==> chall3[j] == 0
}

/// Origin Rust (:343-358); exec + full value ensures. The grinding
/// boolean consumed by the sign loop (:471) and the verify parse
/// gate (::4 at :151-153).
pub fn check_challenge_3(
    chall3: &[u8],
    lambda: usize,
    w_grind: usize,
) -> (ok: bool)
    requires
        lambda % 8 == 0,
        1 <= w_grind <= lambda,
        chall3.len() == lambda / 8,
    ensures
        ok == check_challenge_3_spec(chall3@, lambda as int, w_grind as int),
{
    // Discard all bits before position "lambda - w_grind"
    let start_byte: usize = (lambda - w_grind) / 8;
    let shift: usize = (lambda - w_grind) % 8;
    let start_byte_0s: u8 = chall3[start_byte] >> shift;
    if start_byte_0s != 0 {
        return false;
    }
    // Check that all the following bytes are 0s
    let mut j: usize = start_byte + 1;
    let mut acc: bool = true;
    while j < chall3.len()
        invariant
            start_byte + 1 <= j <= chall3.len(),
            acc == forall |t: int|
                start_byte + 1 <= t < j as int ==> chall3[t] == 0,
        decreases chall3.len() - j,
    {
        if chall3[j] != 0 {
            acc = false;
        }
        j += 1;
    }
    acc
}

// ===========================================================================
// The signature carve faces.
// Origin Rust (SignatureRefMut::from, :53-77):
//     fn from(value: &'a mut [u8]) -> Self {
//         let (cs, value) = value.split_at_mut(
//             O::LHatBytes::USIZE * (Tau::USIZE - 1));
//         let (u_tilde, value) = value.split_at_mut(
//             VoleHasherOutputLength::USIZE);
//         let (d, value) = value.split_at_mut(O::LBytes::USIZE);
//         let (a1_tilde, value) = value.split_at_mut(O::LambdaBytes::USIZE);
//         let (a2_tilde, value) = value.split_at_mut(O::LambdaBytes::USIZE);
//         let (decom_i, value) = value.split_at_mut(P::get_decom_size());
//         let (chall3, value) = value.split_at_mut(O::LambdaBytes::USIZE);
//         let (iv_pre, ctr) = value.split_at_mut(IVSize::USIZE);
//         ... }
// ===========================================================================

/// Twin of the SignatureRefMut carrier (:31-46): nine disjoint
/// mutable windows over the one signature buffer.
pub struct SignatureRefMutTwin<'a> {
    pub cs: &'a mut [u8],
    pub u_tilde: &'a mut [u8],
    pub d: &'a mut [u8],
    pub a1_tilde: &'a mut [u8],
    pub a2_tilde: &'a mut [u8],
    pub decom_i: &'a mut [u8],
    pub chall3: &'a mut [u8],
    pub iv_pre: &'a mut [u8],
    pub ctr: &'a mut [u8],
}

/// Origin Rust (:53-77, From<&'a mut [u8]>); the split chain, exec
/// verified. The segment sizes are the explicit rows (the FA9 tower
/// values); IVSize lowers to 16 and the ctr row is 4 (the header
/// record, re-checked against save_decom_and_ctr / parse_ctr).
pub fn signature_ref_mut_from<'a>(
    signature: &'a mut [u8],
    lhat_bytes: usize,
    tau: usize,
    vole_out: usize,
    l_bytes: usize,
    lambda_bytes: usize,
    decom_size: usize,
) -> (o: SignatureRefMutTwin<'a>)
    requires
        lhat_bytes >= 1,
        tau >= 1,
        l_bytes >= 1,
        lambda_bytes >= 1,
        decom_size >= 1,
        signature.len()
            == lhat_bytes * (tau - 1)
                + vole_out
                + l_bytes
                + 2 * lambda_bytes
                + decom_size
                + lambda_bytes
                + 16
                + 4,
    ensures
        o.cs.len() == lhat_bytes * (tau - 1),
        o.u_tilde.len() == vole_out,
        o.d.len() == l_bytes,
        o.a1_tilde.len() == lambda_bytes,
        o.a2_tilde.len() == lambda_bytes,
        o.decom_i.len() == decom_size,
        o.chall3.len() == lambda_bytes,
        o.iv_pre.len() == 16,
        o.ctr.len() == 4,
{
    let (cs, value) = signature.split_at_mut(lhat_bytes * (tau - 1));
    let (u_tilde, value) = value.split_at_mut(vole_out);
    let (d, value) = value.split_at_mut(l_bytes);
    let (a1_tilde, value) = value.split_at_mut(lambda_bytes);
    let (a2_tilde, value) = value.split_at_mut(lambda_bytes);
    let (decom_i, value) = value.split_at_mut(decom_size);
    let (chall3, value) = value.split_at_mut(lambda_bytes);
    let (iv_pre, ctr) = value.split_at_mut(16);
    SignatureRefMutTwin {
        cs,
        u_tilde,
        d,
        a1_tilde,
        a2_tilde,
        decom_i,
        chall3,
        iv_pre,
        ctr,
    }
}

// ===========================================================================
// The SignatureRefMut save faces (:85-110).
// Origin Rust:
//     fn save_zk_constraints(&mut self, a1_tilde: &[u8], a2_tilde: &[u8]) {
//         self.a1_tilde.copy_from_slice(a1_tilde);
//         self.a2_tilde.copy_from_slice(a2_tilde); }
//     fn mask_witness(&mut self, w: &[u8], u: &[u8]) {
//         xor_arrays_into(self.d, w, u); }
//     fn save_decom_and_ctr(&mut self, decom_i: &BavcOpenResult, ctr: u32) {
//         let BavcOpenResult { coms, nodes } = decom_i;
//         let mut offset = 0;
//         for slice in coms.iter().chain(nodes) {
//             self.decom_i[offset..offset + slice.len()]
//                 .copy_from_slice(slice);
//             offset += slice.len(); }
//         self.decom_i[offset..].fill(0);
//         self.ctr.copy_from_slice(&ctr.to_le_bytes()); }
// Lowerings: copy_from_slice re-spells as the guarded write loops
// (the FA6-pre convention); the coms/nodes row vectors lower to
// their flattened byte planes (the only consumer iterates
// coms-then-nodes writing them sequentially, so the flattening is
// byte-identical -- deviation in carrier form, recorded; the bavc
// twin is FA7's tree, not mounted); the ctr tail rows split out
// into write_ctr_segment so the write value rows verify cleanly.
// ===========================================================================

/// Origin Rust (:85-88); exec verified.
pub fn save_zk_constraints(
    sig_a1: &mut [u8],
    sig_a2: &mut [u8],
    a1_tilde: &[u8],
    a2_tilde: &[u8],
)
    requires
        sig_a1.len() == a1_tilde.len(),
        sig_a2.len() == a2_tilde.len(),
    ensures
        forall |j: int| 0 <= j < old(sig_a1).len() ==> final(sig_a1)[j] == a1_tilde[j],
        forall |j: int| 0 <= j < old(sig_a2).len() ==> final(sig_a2)[j] == a2_tilde[j],
{
    let mut i: usize = 0;
    while i < a1_tilde.len()
        invariant
            i <= a1_tilde.len(),
            a1_tilde.len() <= sig_a1.len(),
            sig_a1@.len() == old(sig_a1)@.len(),
            forall |j: int| 0 <= j < i as int ==> sig_a1[j] == a1_tilde[j],
            forall |j: int| i <= j < sig_a1@.len()
                ==> sig_a1[j] == old(sig_a1)[j],
        decreases a1_tilde.len() - i,
    {
        sig_a1[i] = a1_tilde[i];
        i += 1;
    }
    let mut i: usize = 0;
    while i < a2_tilde.len()
        invariant
            i <= a2_tilde.len(),
            a2_tilde.len() <= sig_a2.len(),
            sig_a2@.len() == old(sig_a2)@.len(),
            forall |j: int| 0 <= j < i as int ==> sig_a2[j] == a2_tilde[j],
            forall |j: int| i <= j < sig_a2@.len()
                ==> sig_a2[j] == old(sig_a2)[j],
        decreases a2_tilde.len() - i,
    {
        sig_a2[i] = a2_tilde[i];
        i += 1;
    }
}

/// Origin Rust (:90-92, mask_witness); the landed xor_arrays_into
/// face carries the value rows (d = w xor u over the joint span).
pub fn mask_witness(
    sig_d: &mut [u8],
    w: &[u8],
    u: &[u8],
)
    requires
        sig_d.len() <= w.len(),
        sig_d.len() <= u.len(),
{
    xor_arrays_into(sig_d, w, u);
}

/// Origin Rust (:94-105, the coms/nodes chain + the zero-pad tail);
/// exec verified over the flattened row planes (the section
/// record); the ctr tail (:108) lives in write_ctr_segment.
pub fn save_decom_and_ctr(
    sig_decom_i: &mut [u8],
    coms: &[u8],
    nodes: &[u8],
)
    requires
        coms.len() + nodes.len() <= sig_decom_i.len(),
    ensures
        final(sig_decom_i).len() == old(sig_decom_i).len(),
        forall |j: int|
            (coms.len() + nodes.len()) as int <= j < old(sig_decom_i).len()
                ==> final(sig_decom_i)[j] == 0,
{
    // Save decom_i
    let n_total_row: usize = sig_decom_i.len();
    let mut offset: usize = 0;
    let mut i: usize = 0;
    while i < coms.len()
        invariant
            i <= coms.len(),
            offset == i,
            coms.len() <= n_total_row,
            sig_decom_i@.len() == old(sig_decom_i)@.len(),
            sig_decom_i@.len() == n_total_row,
            forall |j: int| 0 <= j < i as int ==> sig_decom_i[j] == coms[j],
            forall |j: int| i <= j < sig_decom_i@.len()
                ==> sig_decom_i[j] == old(sig_decom_i)[j],
        decreases coms.len() - i,
    {
        sig_decom_i[offset] = coms[i];
        offset += 1;
        i += 1;
    }
    let mut i: usize = 0;
    while i < nodes.len()
        invariant
            i <= nodes.len(),
            offset == coms.len() + i,
            coms.len() + nodes.len() <= n_total_row,
            sig_decom_i@.len() == old(sig_decom_i)@.len(),
            sig_decom_i@.len() == n_total_row,
            forall |j: int|
                0 <= j < (coms.len() + i) as int ==> sig_decom_i[j]
                    == (if j < coms.len() { coms[j] } else { nodes[j - coms.len() as int] }),
            forall |j: int| (coms.len() + i) <= j < sig_decom_i@.len()
                ==> sig_decom_i[j] == old(sig_decom_i)[j],
        decreases nodes.len() - i,
    {
        sig_decom_i[offset] = nodes[i];
        offset += 1;
        i += 1;
    }
    // Add 0-padding to decommitment buffer
    while offset < sig_decom_i.len()
        invariant
            (coms.len() + nodes.len()) <= offset <= sig_decom_i.len(),
            sig_decom_i@.len() == old(sig_decom_i)@.len(),
            forall |j: int|
                0 <= j < (coms.len() + nodes.len()) as int ==> sig_decom_i[j]
                    == (if j < coms.len() { coms[j] } else { nodes[j - coms.len() as int] }),
            forall |j: int|
                (coms.len() + nodes.len()) as int <= j < offset as int
                    ==> sig_decom_i[j] == 0u8,
            forall |j: int| offset as int <= j < sig_decom_i@.len()
                ==> sig_decom_i[j] == old(sig_decom_i)[j],
        decreases sig_decom_i.len() - offset,
    {
        sig_decom_i[offset] = 0u8;
        offset += 1;
    }
    proof {
        assert(offset == sig_decom_i.len());
    }
}

/// The ctr-segment write (the save_decom_and_ctr tail face;
/// upstream :108 `self.ctr.copy_from_slice(&ctr.to_le_bytes())`):
/// the four constant-denominator lanes (the ctr_le_byte spells).
pub fn write_ctr_segment(ctr_seg: &mut [u8], ctr: u32)
    requires
        ctr_seg.len() == 4,
    ensures
        forall |j: int| 0 <= j < 4
            ==> final(ctr_seg)[j] == ctr_le_bytes(ctr as int)[j],
{
    ctr_seg[0] = (ctr % 256) as u8;
    ctr_seg[1] = ((ctr / 256) % 256) as u8;
    ctr_seg[2] = ((ctr / 65536) % 256) as u8;
    ctr_seg[3] = ((ctr / 16777216) % 256) as u8;
}

// ===========================================================================
// The SignatureRef carve (upstream :112-191).
// Origin Rust (TryFrom :139-168): the same split chain over the
// immutable slice plus the ::4 gate:
//     // ::4
//     if !check_challenge_3::<P, O>(chall3) { return Err(Error::new()); }
// parse_decom (:176-186) chunks the decom_i window at
// n_coms * com_size (node_size = LambdaBytes; com_size =
// NLeafCommit * LambdaBytes); parse_ctr (:188-190) is the u32
// little-endian read.
// ===========================================================================

/// Twin of the SignatureRef carrier (:115-130): nine immutable
/// windows.
pub struct SignatureRefTwin<'a> {
    pub cs: &'a [u8],
    pub u_tilde: &'a [u8],
    pub d: &'a [u8],
    pub a1_tilde: &'a [u8],
    pub a2_tilde: &'a [u8],
    pub decom_i: &'a [u8],
    pub chall3: &'a [u8],
    pub iv_pre: &'a [u8],
    pub ctr: &'a [u8],
}

/// Origin Rust (:139-168, TryFrom<&[u8]>); the split chain + the
/// ::4 gate, exec verified. None is the Err(Error::new()) lane (the
/// Error record).
pub fn signature_ref_try_from<'a>(
    signature: &'a [u8],
    lhat_bytes: usize,
    tau: usize,
    vole_out: usize,
    l_bytes: usize,
    lambda_bytes: usize,
    lambda: usize,
    w_grind: usize,
    decom_size: usize,
) -> (o: Option<SignatureRefTwin<'a>>)
    requires
        lhat_bytes >= 1,
        tau >= 1,
        l_bytes >= 1,
        lambda_bytes >= 1,
        decom_size >= 1,
        lambda % 8 == 0,
        lambda_bytes == lambda / 8,
        lambda >= 1,
        w_grind >= 1,
        w_grind <= lambda,
        signature.len()
            == lhat_bytes * (tau - 1)
                + vole_out
                + l_bytes
                + 2 * lambda_bytes
                + decom_size
                + lambda_bytes
                + 16
                + 4,
{
    let (cs, value) = signature.split_at(lhat_bytes * (tau - 1));
    let (u_tilde, value) = value.split_at(vole_out);
    let (d, value) = value.split_at(l_bytes);
    let (a1_tilde, value) = value.split_at(lambda_bytes);
    let (a2_tilde, value) = value.split_at(lambda_bytes);
    let (decom_i, value) = value.split_at(decom_size);
    let (chall3, value) = value.split_at(lambda_bytes);
    let (iv_pre, ctr) = value.split_at(16);
    // ::4
    if !check_challenge_3(chall3, lambda, w_grind) {
        return None;
    }
    Some(SignatureRefTwin {
        cs,
        u_tilde,
        d,
        a1_tilde,
        a2_tilde,
        decom_i,
        chall3,
        iv_pre,
        ctr,
    })
}

/// Origin Rust (:176-186, parse_decom); the two-window split at
/// n_coms * com_size (the chunks_exact rows flatten -- the same
/// carrier record as the save face).
pub fn parse_decom(
    decom_i: &[u8],
    n_coms: usize,
    com_size: usize,
) -> (o: (usize, usize))
    requires
        n_coms * com_size <= decom_i.len(),
    ensures
        o.0 == n_coms * com_size,
        o.1 == decom_i.len() - n_coms * com_size,
{
    let (coms, nodes) = decom_i.split_at(n_coms * com_size);
    (coms.len(), nodes.len())
}

/// Origin Rust (:188-190, parse_ctr); the u32 little-endian read,
/// exec verified.
pub fn parse_ctr(ctr: &[u8]) -> (o: u32)
    requires
        ctr.len() == 4,
    ensures
        o == (ctr[0] as u32)
            | ((ctr[1] as u32) << 8)
            | ((ctr[2] as u32) << 16)
            | ((ctr[3] as u32) << 24),
{
    (ctr[0] as u32)
        | ((ctr[1] as u32) << 8)
        | ((ctr[2] as u32) << 16)
        | ((ctr[3] as u32) << 24)
}

// ===========================================================================
// FaestHash (upstream :193-332), the Shake128-axis free faces.
// Upstream trait doc rows (:195-230) transcribed at each face; the
// generic-RO blanket impl lowers to the one carrier at the landed
// axis (the FA9 row mapping: BaseParams128 ->
// RandomOracleShake128, first-hand parameter.rs :180). Bodies are
// exec (the landed RO twin's update/finish/read faces carry the
// absorb-order + stream contract rows; upstream spells no contract
// on these faces).
// ===========================================================================

/// Generate `µ` (upstream :196 doc row; the sign figure step ::3;
/// body :237-244).
pub fn faest_hash_mu(
    mu: &mut [u8],
    input: &[u8],
    output: &[u8],
    msg: &[u8],
)
    requires
        mu.len() == 32,
    ensures
        forall |j: int| 0 <= j < 32 ==> final(mu)[j] == #[trigger]
            shake128_byte(input@ + output@ + msg@ + seq![8u8], j),
{
    let mut h2_hasher = RandomOracleShake128::h2_0_init();
    h2_hasher.update(input);
    h2_hasher.update(output);
    h2_hasher.update(msg);
    let mut reader = h2_hasher.finish();
    reader.read(mu);
}

/// Generate `r` and `iv_pre` (upstream :197 doc row; the step ::4;
/// body :246-256). The reader hands out r (LambdaBytes) then iv
/// (IVSize = 16) as disjoint consecutive stream segments.
pub fn faest_hash_r_iv(
    r: &mut [u8],
    iv: &mut [u8],
    key: &[u8],
    mu: &[u8],
    rho: &[u8],
)
    requires
        r.len() == 16,
        iv.len() == 16,
    ensures
        forall |j: int| 0 <= j < 16 ==> final(r)[j] == #[trigger]
            shake128_byte(key@ + mu@ + rho@ + seq![3u8], j),
        forall |j: int| 0 <= j < 16 ==> final(iv)[j] == #[trigger]
            shake128_byte(key@ + mu@ + rho@ + seq![3u8], 16 + j),
{
    let mut h3_hasher = RandomOracleShake128::h3_init();
    h3_hasher.update(key);
    h3_hasher.update(mu);
    h3_hasher.update(rho);

    let mut h3_reader = h3_hasher.finish();
    h3_reader.read(r);
    h3_reader.read(iv);
}

/// Generate `iv` (upstream :199 doc row; the step ::5; body
/// :258-265). Upstream rebinds `*iv_pre = h4_reader.read_into()`;
/// the twin fills the same window through the reader's read face
/// (equivalent fill; the move record rides the header note).
pub fn faest_hash_iv(
    iv: &mut [u8],
)
    requires
        iv.len() == 16,
    ensures
        forall |j: int| 0 <= j < 16 ==> final(iv)[j] == #[trigger]
            shake128_byte(old(iv)@ + seq![4u8], j),
{
    let mut h4_hasher = RandomOracleShake128::h4_init();
    h4_hasher.update(iv);
    let mut h4_reader = h4_hasher.finish();
    h4_reader.read(iv);
}

/// Generate first challenge (upstream :201 doc row; body :267-274;
/// the chall1 slab = Chall1 = 8 + 5 * LambdaBytes = 88 bytes at the
/// rows). NOTE (doc context, transcription verbatim; upstream
/// spelling preserved): the call site passes the DERIVED iv, the
/// faest-ref v2 behavior -- "Contrarly to specification, faest-ref
/// uses iv instead of iv_pre" (upstream faest.rs :420-421); this is
/// the upstream-tracked #34 doc context (out/kverus-run/research/
/// faest-ref-cross-check.md section 8, S-FA13 candidate NOT
/// promoted; a known faest-ref-v2-generation behavior), not a new
/// finding here.
pub fn faest_hash_challenge_1(
    chall1: &mut [u8],
    mu: &[u8],
    hcom: &[u8],
    c: &[u8],
    iv: &[u8],
)
    requires
        chall1.len() == 88,
    ensures
        forall |j: int| 0 <= j < 88 ==> final(chall1)[j] == #[trigger]
            shake128_byte(mu@ + hcom@ + c@ + iv@ + seq![9u8], j),
{
    let mut h2_hasher = RandomOracleShake128::h2_1_init();
    h2_hasher.update(mu);
    h2_hasher.update(hcom);
    h2_hasher.update(c);
    h2_hasher.update(iv);
    let mut reader = h2_hasher.finish();
    reader.read(chall1);
}

/// Generate second challenge in an init-update-finalize style
/// (upstream :203-204 doc rows; body :276-281).
pub fn faest_hash_challenge_2_init(
    chall1: &[u8],
    u_t: &[u8],
) -> (o: Hasher128<10>)
    ensures
        o.buf@ == chall1@ + u_t@,
{
    let mut h2_hasher = RandomOracleShake128::h2_2_init();
    h2_hasher.update(chall1);
    h2_hasher.update(u_t);
    h2_hasher
}

/// The finalize half (upstream :206-209 signature rows; body
/// :283-290).
pub fn faest_hash_challenge_2_finalize(
    hasher: Hasher128<10>,
    chall2: &mut [u8],
    d: &[u8],
)
    requires
        chall2.len() == 56,
    ensures
        forall |j: int| 0 <= j < 56 ==> final(chall2)[j] == #[trigger]
            shake128_byte(hasher.buf@ + d@ + seq![10u8], j),
{
    let mut hasher2 = hasher;
    hasher2.update(d);
    let mut reader = hasher2.finish();
    reader.read(chall2);
}

/// Generate third challenge in an init-finalize style (upstream
/// :219-225 doc rows; body :292-304).
pub fn faest_hash_challenge_3_init(
    chall2: &[u8],
    a0_t: &[u8],
    a1_t: &[u8],
    a2_t: &[u8],
) -> (o: Hasher128<11>)
    ensures
        o.buf@ == chall2@ + a0_t@ + a1_t@ + a2_t@,
{
    let mut h2_hasher = RandomOracleShake128::h2_3_init();
    h2_hasher.update(chall2);
    h2_hasher.update(a0_t);
    h2_hasher.update(a1_t);
    h2_hasher.update(a2_t);
    h2_hasher
}

/// The ctr-le-bytes spec view (the `hasher.update(&ctr.to_le_bytes())`
/// rows of :312 and :329): the four little-endian lanes over the
/// constant denominators (verus shifts on spec int are unavailable,
/// hence the div/mod spell).
pub open spec fn ctr_le_bytes(ctr: int) -> Seq<u8> {
    seq![
        (ctr % 256) as u8,
        ((ctr / 256) % 256) as u8,
        ((ctr / 65536) % 256) as u8,
        ((ctr / 16777216) % 256) as u8,
    ]
}

/// The exec lane builder (ctr.to_le_bytes()): the four constant
/// divisors of the 2^32 u32 range; exec + per-lane spec ensures.
pub fn ctr_le_bytes_exec(ctr: u32) -> (o: [u8; 4])
    ensures
        forall |t: int| 0 <= t < 4
            ==> o[t] == ctr_le_bytes(ctr as int)[t],
{
    [
        (ctr % 256) as u8,
        ((ctr / 256) % 256) as u8,
        ((ctr / 65536) % 256) as u8,
        ((ctr / 16777216) % 256) as u8,
    ]
}

/// The finalize half (upstream :226-230 signature rows; body
/// :306-314). Upstream clones the stored hasher (`hasher.to_owned()`,
/// Clone -> the twin's clone128 face), appends the ctr rows, reads.
pub fn faest_hash_challenge_3_finalize(
    hasher: &Hasher128<11>,
    chall3: &mut [u8],
    ctr: u32,
)
    requires
        chall3.len() == 16,
    ensures
        forall |j: int| 0 <= j < 16 ==> final(chall3)[j] == #[trigger]
            shake128_byte(
                hasher.buf@ + ctr_le_bytes(ctr as int) + seq![11u8],
                j,
            ),
{
    let mut hasher2 = hasher.clone128();
    let ctr_arr: [u8; 4] = ctr_le_bytes_exec(ctr);
    proof {
        assert(ctr_arr@ == ctr_le_bytes(ctr as int));
    }
    hasher2.update(&ctr_arr);
    let mut reader = hasher2.finish();
    reader.read(chall3);
}

/// Generate third challenge (upstream :210-218 signature rows; body
/// :316-331) -- the one-shot form the verify chain consumes.
pub fn faest_hash_challenge_3(
    chall3: &mut [u8],
    chall2: &[u8],
    a0_t: &[u8],
    a1_t: &[u8],
    a2_t: &[u8],
    ctr: u32,
)
    requires
        chall3.len() == 16,
    ensures
        forall |j: int| 0 <= j < 16 ==> final(chall3)[j] == #[trigger]
            shake128_byte(
                chall2@ + a0_t@ + a1_t@ + a2_t@
                    + ctr_le_bytes(ctr as int) + seq![11u8],
                j,
            ),
{
    let mut h2_hasher = RandomOracleShake128::h2_3_init();
    h2_hasher.update(chall2);
    h2_hasher.update(a0_t);
    h2_hasher.update(a1_t);
    h2_hasher.update(a2_t);
    let ctr_arr: [u8; 4] = ctr_le_bytes_exec(ctr);
    proof {
        assert(ctr_arr@ == ctr_le_bytes(ctr as int));
    }
    h2_hasher.update(&ctr_arr);
    let mut reader = h2_hasher.finish();
    reader.read(chall3);
}

// ===========================================================================
// The BaseParameters hash helpers (upstream parameter.rs :126-165,
// consumed at sign ::10-11/:428-433 and verify ::12-14/:532-538).
// The `BaseParameters::VoleHasher` row lowers to the landed
// VoleHasher128 (FA6); the h2_hasher parameter is the RO Hasher
// carrier (Hasher128<10> at the Shake128 axis).
//
// Origin Rust (parameter.rs :126-133):
//     fn hash_v_matrix(h2_hasher: &mut impl Hasher,
//         v: &[Array<u8, impl ArraySize>],
//         chall1: &Array<u8, Self::Chall1>) {
//         let vole_hasher = Self::VoleHasher::new_vole_hasher(chall1);
//         for vi in v {
//             // Hash column-wise
//             h2_hasher.update(VoleHasherProcess::process(
//                 &vole_hasher, vi).as_slice()); } }
// The v matrix lowers to the flat Lambda-rows x lhat_bytes carrier
// (the CstrntsVal record of the zk twin).
// ===========================================================================

/// Origin Rust (parameter.rs :126-133); exec body (the per-row
/// process requires rows are this face's requires; the h2 update
/// rows ride the landed RO / VoleHasher face contracts).
pub fn faest_hash_v_matrix(
    h2_hasher: &mut Hasher128<10>,
    v_flat: &[u8],
    lhat_bytes: usize,
    lambda: usize,
    chall1: &[u8],
)
    requires
        lambda == 128,
        lhat_bytes > 18,
        lambda * lhat_bytes == v_flat.len(),
        chall1.len() == 88,
    ensures
        final(h2_hasher).buf@.len()
            == old(h2_hasher).buf@.len() + 18 * lambda,
{
    // Self::VoleHasher::new_vole_hasher(chall1)
    let vole_hasher: VoleHasher128 = VoleHasher128::new_vole_hasher(chall1);
    // for vi in v { h2_hasher.update(process(&vole_hasher, vi)) }
    let mut row: usize = 0;
    while row < lambda
        invariant
            0 <= row <= lambda,
            lambda == 128,
            lambda * lhat_bytes == v_flat.len(),
            lhat_bytes > 18,
            vole_hasher == vole_hasher,
            h2_hasher.buf@.len() == old(h2_hasher).buf@.len() + 18 * row,
        decreases lambda - row,
    {
        proof {
            assert((row as int) + 1 <= lambda as int);
            vstd::arithmetic::mul::lemma_mul_inequality(
                (row as int) + 1, lambda as int, lhat_bytes as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                lhat_bytes as int, (row as int) + 1);
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                lhat_bytes as int, lambda as int);
            assert(((row as int) + 1) * lhat_bytes as int
                <= (lambda as int) * lhat_bytes as int);
            vstd::arithmetic::mul::lemma_mul_inequality(
                (row as int), (row as int) + 1, lhat_bytes as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                lhat_bytes as int, (row as int));
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                (row as int), 1int, lhat_bytes as int);
            assert((row as int) * lhat_bytes as int
                <= ((row as int) + 1) * lhat_bytes as int);
            assert((row as int) * lhat_bytes as int + lhat_bytes as int
                == ((row as int) + 1) * lhat_bytes as int) by(nonlinear_arith);
            assert(((row as int) + 1) * lhat_bytes as int <= v_flat.len() as int);
            assert((row as int) * lhat_bytes as int <= v_flat.len() as int);
        }
        let vi: &[u8] = &v_flat[row * lhat_bytes..(row + 1) * lhat_bytes];
        assert(vi.len() == lhat_bytes);
        assert(vi.len() > 18);
        let nb: usize = (vi.len() - 18) / 16;
        let rem: usize = (vi.len() - 18) % 16;
        let processed: [u8; 18] = vole_hasher.process(vi, nb, rem);
        h2_hasher.update(&processed);
        row += 1;
    }
}

/// Origin Rust (parameter.rs :135-140); u is the LHatBytes-long vole
/// output; signature_u gets the one processed slab.
pub fn faest_hash_u_vector(
    signature_u: &mut [u8],
    u: &[u8],
    chall1: &[u8],
)
    requires
        signature_u.len() == 18,
        u.len() > 18,
        chall1.len() == 88,
{
    // let vole_hasher_u = Self::VoleHasher::new_vole_hasher(chall1);
    // signature_u.copy_from_slice(
    //     vole_hasher_u.process(u).as_slice());
    let vole_hasher_u: VoleHasher128 = VoleHasher128::new_vole_hasher(chall1);
    let nb: usize = (u.len() - 18) / 16;
    let rem: usize = (u.len() - 18) % 16;
    let processed: [u8; 18] = vole_hasher_u.process(u, nb, rem);
    let mut i: usize = 0;
    while i < 18
        invariant
            0 <= i <= 18,
            signature_u.len() == 18,
            forall |t: int| 0 <= t < i as int ==> signature_u[t] == processed[t],
        decreases 18 - i,
    {
        signature_u[i] = processed[i];
        i += 1;
    }
}

/// Origin Rust (parameter.rs :144-165); the q rows: process,
/// conditional xor with u_tilde_sig on the d_i == 1 lane, update.
/// The decoded_chall3_iter (parameter.rs :1026-1035) iterates the
/// bavc_index_offset-instanced sub-challenge bits = exactly the
/// chall3 bits 0..Lambda in order (the tau1*k + tau0*(k-1) ==
/// lambda bit-contiguity row over the FA1 tau tables) plus WGRIND
/// padding bits the upstream zip truncates; d_i therefore lowers
/// to chall3 bit i (first-hand derivation, recorded).
pub fn faest_hash_q_matrix(
    h2_hasher: &mut Hasher128<10>,
    q_flat: &[u8],
    lhat_bytes: usize,
    lambda: usize,
    u_tilde_sig: &[u8],
    chall1: &[u8],
    chall3: &[u8],
)
    requires
        lambda == 128,
        lhat_bytes > 18,
        lambda * lhat_bytes == q_flat.len(),
        u_tilde_sig.len() == 18,
        chall1.len() == 88,
        chall3.len() == lambda / 8,
{
    let vole_hasher: VoleHasher128 = VoleHasher128::new_vole_hasher(chall1);
    let mut row: usize = 0;
    while row < lambda
        invariant
            0 <= row <= lambda,
            lambda == 128,
            lambda * lhat_bytes == q_flat.len(),
            lhat_bytes > 18,
            chall3.len() == lambda / 8,
            u_tilde_sig.len() == 18,
            h2_hasher.buf@.len() == old(h2_hasher).buf@.len() + 18 * row,
        decreases lambda - row,
    {
        proof {
            assert((row as int) + 1 <= lambda as int);
            assert((row as int) < (lambda as int));
            assert(lambda == 128);
            assert(chall3.len() == 16);
            assert((row as int) < 8 * (chall3.len() as int));
            vstd::arithmetic::mul::lemma_mul_inequality(
                (row as int) + 1, lambda as int, lhat_bytes as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                lhat_bytes as int, (row as int) + 1);
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                lhat_bytes as int, lambda as int);
            assert(((row as int) + 1) * lhat_bytes as int
                <= (lambda as int) * lhat_bytes as int);
            vstd::arithmetic::mul::lemma_mul_inequality(
                (row as int), (row as int) + 1, lhat_bytes as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                lhat_bytes as int, (row as int));
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                (row as int), 1int, lhat_bytes as int);
            assert((row as int) * lhat_bytes as int
                <= ((row as int) + 1) * lhat_bytes as int);
            assert((row as int) * lhat_bytes as int + lhat_bytes as int
                == ((row as int) + 1) * lhat_bytes as int) by(nonlinear_arith);
            assert(((row as int) + 1) * lhat_bytes as int <= q_flat.len() as int);
            assert((row as int) * lhat_bytes as int <= q_flat.len() as int);
        }
        // (the decoded challenge bit of this row: chall3 bit row; the
        // landed get_bit face carries the bound rows -- the FA1 unit)
        let d_i: u8 = get_bit(chall3, row);
        let qi: &[u8] = &q_flat[row * lhat_bytes..(row + 1) * lhat_bytes];
        assert(qi.len() == lhat_bytes);
        assert(qi.len() > 18);
        let nb: usize = (qi.len() - 18) / 16;
        let rem: usize = (qi.len() - 18) % 16;
        // ::12
        let mut q_tilde: [u8; 18] = vole_hasher.process(qi, nb, rem);
        // ::14
        if d_i == 1 {
            xor_arrays_inplace(&mut q_tilde, u_tilde_sig);
        }
        // ::15
        h2_hasher.update(&q_tilde);
        row += 1;
    }
}

// ===========================================================================
// faest_keygen (upstream :334-341; the keygen body is
// parameter.rs :350-357, first-hand).
// Origin Rust (parameter.rs :350-357):
//     fn keygen_with_rng<R: Rng + ?Sized>(rng: &mut R) -> SecretKey<Self> {
//         let mut owf_key = Array::default();
//         loop {
//             rng.fill_bytes(&mut owf_key);
//             if owf_key[0] & 0b11 != 0b11 { break; } }
//         let mut owf_input = Array::default();
//         rng.fill_bytes(&mut owf_input);
//         let owf_output = Self::evaluate_owf(&owf_key, &owf_input);
//         SecretKey { owf_key, pk: PublicKey { owf_input, owf_output } } }
// Lowerings:
//   - rng.fill_bytes is the trusted external face below (rand /
//     nist_pqc_seeded_rng are external crates);
//   - the upstream `loop` is unbounded rejection sampling (it relies
//     on the honest rng; there is no verus-decreasing measure on a
//     nondeterministic fill), so the twin bounds the attempts
//     (attempts_max) and returns the None/false lane on exhaustion
//     -- an rng-dishonest event only; deviation record;
//   - Self::evaluate_owf is the AES/OWF proper (the D-FA10-1 held
//     production line; the FA10 ruling): owf_output arrives as a
//     DATA row (the FA10 sk_recontract precedent), carried here to
//     the SecretKey rows.
// KeypairGenerator (lib.rs :189) dispatches to this body through
// faest_keygen (the record rows at the header).
// ===========================================================================

/// The trusted rng fill face (external rand/nist crates; the
/// FA4-style trusted stub).
#[verifier::external_body]
pub fn rng_fill_bytes(dst: &mut [u8])
    ensures
        final(dst)@.len() == old(dst)@.len(),
{
    panic!("trusted rng fill (rand/nist_pqc_seeded_rng external crates); spec-face stub")
}

/// Origin Rust faest_keygen (:334-341) + keygen_with_rng
/// (parameter.rs :350-357); the FAEST-128 axis rows (SK rows:
/// owf_key 16 bytes = LambdaBytes; the owf_input / owf_output rows
/// per the OWF row sizes at the call sites). false == the Err lane
/// (the Error record).
pub fn faest_keygen_128(
    attempts_max: usize,
    owf_key: &mut [u8],
    owf_input: &mut [u8],
    owf_output: &[u8],
    nst_bytes: usize,
) -> (ok: bool)
    requires
        attempts_max >= 1,
        owf_key.len() == 16,
        owf_input.len() == nst_bytes,
        owf_output.len() == nst_bytes,
    ensures
        ok ==> (final(owf_key)[0] & 0b11) != 0b11
            && final(owf_key).len() == old(owf_key).len()
            && final(owf_input).len() == old(owf_input).len(),
{
    // the upstream loop always fills at least once; the twin hoists
    // the first fill (the accepted init row below rides it)
    rng_fill_bytes(owf_key);
    let mut attempts: usize = 0;
    let mut accepted: bool = (owf_key[0] & 0b11) != 0b11;
    while !accepted && attempts < attempts_max
        invariant
            attempts <= attempts_max,
            owf_key@.len() == 16,
            accepted == ((owf_key[0] & 0b11) != 0b11),
        decreases attempts_max - attempts,
    {
        rng_fill_bytes(owf_key);
        accepted = (owf_key[0] & 0b11) != 0b11;
        attempts += 1;
    }
    proof {
        assert(final(owf_key).len() == old(owf_key).len());
    }
    if !accepted {
        return false;
    }
    rng_fill_bytes(owf_input);
    proof {
        assert(final(owf_input).len() == old(owf_input).len());
        assert(final(owf_key).len() == old(owf_key).len());
    }
    // owf_output = Self::evaluate_owf(&owf_key, &owf_input): the data
    // row (the FA10 record; the production ledger rides the FA13
    // notes / the D-FA10-1 oracle contract)
    let _ = owf_output;
    true
}

// ===========================================================================
// The trusted vole / bavc shim faces (the trust boundaries of this
// batch; the FA8 kit entry D-FA13-3 owns the real bodies -- vole.rs
// has no twin anywhere in verified/; bavc.rs is the FA7 in-flight
// tree, not mounted here). Panic-stub bodies under
// #[verifier::external_body] (the FA4/FA5 trusted-core precedent);
// the ensures rows are the D-FA10-1-style data contracts:
// length / domain rows only, values oracle-arbitrated.
// ===========================================================================

/// Twin of VoleCommitResult (upstream vole.rs :28-43) at the
/// flattened carrier rows: com (the Prod<LambdaBytes, U2> slab = 2
/// * LambdaBytes), decom (the opaque BavcDecommitment carrier,
/// consumed only by the open face below), u (LHatBytes), v (the
/// flat Lambda rows x LHatBytes matrix).
pub struct VoleCommitResultTwin {
    pub com: Vec<u8>,
    pub decom: Vec<u8>,
    pub u: Vec<u8>,
    pub v_flat: Vec<u8>,
}

/// Origin Rust (vole.rs :184-231, volecommit<BAVC, LHatBytes> over
/// VoleCommitmentCRefMut::new(signature.cs), faest.rs :418-419):
/// the trusted shim. Rows: the cs window is the (Tau - 1)
/// commitments slab (stride LHatBytes), r the LambdaBytes seed row,
/// iv the IVSize window.
#[verifier::external_body]
pub fn volecommit_cs(
    cs: &mut [u8],
    r: &[u8],
    iv: &[u8],
    lambda_bytes: usize,
    lhat_bytes: usize,
    tau: usize,
) -> (o: VoleCommitResultTwin)
    requires
        tau >= 1,
        cs.len() == lhat_bytes * (tau - 1),
        r.len() == lambda_bytes,
        iv.len() == 16,
        lambda_bytes >= 1,
        lhat_bytes >= 1,
    ensures
        o.com.len() == 2 * lambda_bytes,
        o.v_flat.len() == (8 * lambda_bytes) * lhat_bytes,
        o.u.len() == lhat_bytes,
        final(cs).len() == old(cs).len(),
{
    panic!("trusted volecommit core (vole.rs has no landed twin; the FA8 kit); spec-face stub")
}

/// Origin Rust (bavc.rs BatchVectorCommitment::open over the
/// decommitment + the decoded challenge row, faest.rs :476): the
/// trusted shim. i_delta is the Tau-long decoded row (the
/// decode_all_chall_3 values); the coms/nodes rows lower to their
/// flattened byte planes (the save_decom_and_ctr chain record).
#[verifier::external_body]
pub fn bavc_open(
    decom: &[u8],
    i_delta: &[u16],
    lambda_bytes: usize,
) -> (o: Option<(Vec<u8>, Vec<u8>)>)
    requires
        lambda_bytes >= 1,
{
    panic!("trusted bavc open core (bavc.rs is the FA7 in-flight tree, not mounted); spec-face stub")
}

/// Origin Rust (vole.rs :234-343, volereconstruct<BAVC, LHatBytes>;
/// the CRef views over the signature cs window, faest.rs :521-523):
/// the trusted shim; consumes the decom_i window (the parse_decom
/// chunk rows ride the upstream boundary -- the twin parses at the
/// face level and the shim consumes the flat window; deviation
/// record at the header). Returns (com, q_flat). The com/q length
/// rows await the FA8 twin owner (record here; the callers of this
/// batch are all frozen bodies).
#[verifier::external_body]
pub fn volereconstruct_cs(
    chall3: &[u8],
    decom_i: &[u8],
    c: &[u8],
    iv: &[u8],
    lambda_bytes: usize,
    lhat_bytes: usize,
    tau: usize,
) -> (o: Option<(Vec<u8>, Vec<u8>)>)
    requires
        tau >= 1,
        chall3.len() == lambda_bytes,
        decom_i.len() >= 1,
        c.len() == lhat_bytes * (tau - 1),
        iv.len() == 16,
        lambda_bytes >= 1,
        lhat_bytes >= 1,
{
    panic!("trusted volereconstruct core (vole.rs has no landed twin; the FA8 kit); spec-face stub")
}

// ===========================================================================
// sign (upstream :393-485). FROZEN (external_body + faithful body;
// the FA12 driver trajectory ruling). faest_sign (:360-376) /
// faest_unpacked_sign (:378-391) are the #[inline] wrappers -- the
// twin's sign_chain carries their composition (the carve rows +
// the witness row; the wrapped secret-key genres lower to the
// byte slices per the header records, the UnpackedSecretKey rows
// differ only in whose witness bytes feed the chain). The requires
// table carries the aes_prove mirror rows including the (b)
// kec_claim uplift (the harness KAT arms discharge them with
// oracle data).
// ===========================================================================

/// Origin Rust (:393-485); the sign chain.
#[verifier::external_body]
pub fn sign_chain(
    msg: &[u8],
    owf_key: &[u8],
    owf_input: &[u8],
    owf_output: &[u8],
    w_bytes: &[u8],
    rho: &[u8],
    signature: &mut [u8],
    nst: usize,
    nst_bytes: usize,
    nk: usize,
    lambda: usize,
    r: usize,
    ske: usize,
    n_words: usize,
    l_bytes: usize,
    lhat_bytes: usize,
    lke_bytes: usize,
    lenc_bytes: usize,
    beta: usize,
    is_em: bool,
    tau: usize,
    tau1: usize,
    tau0: usize,
    k_idx: usize,
    w_grind: usize,
    vole_out: usize,
    decom_size: usize,
) -> (ok: bool)
    requires
        // the FA9-row domain + the landing-axis row
        lambda == 128,
        nst >= 4,
        nst_bytes == 4 * nst,
        nk >= 1,
        nk <= 8,
        lambda == 32 * nk,
        r >= 2,
        r % 2 == 0,
        r <= 14,
        n_words == 4 * (r + 1),
        n_words > nk,
        ske >= 4,
        ske <= 64,
        ske % 4 == 0,
        n_words <= 64,
        4 * n_words <= usize::MAX,
        32 * n_words <= usize::MAX,
        // the carriers of this face
        owf_key.len() == lambda / 8,
        w_bytes.len() == l_bytes,
        rho.len() == 16,
        lhat_bytes == l_bytes + 3 * (lambda / 8) + 2,
        lhat_bytes > 18,
        l_bytes >= 1,
        // the carve rows
        tau >= 1,
        tau == tau1 + tau0,
        2 <= k_idx <= 15,
        vole_out == 18,
        decom_size >= 1,
        lhat_bytes * (tau - 1)
        + vole_out
        + l_bytes
        + 2 * (lambda / 8)
        + decom_size
        + lambda / 8
        + 16
        + 4
        == signature.len(),
        w_grind >= 1,
        w_grind <= lambda,
        // the aes_prove mirror rows (the zk twin's table -- the
        // owf window rows, the x/y planes, the grind rows, the (b)
        // kec_claim uplift over the LKeBytes witness window)
        lke_bytes + (lenc_bytes * (if is_em { 1 } else { beta }))
            <= l_bytes,
        owf_input.len() == nst_bytes,
        if is_em {
            owf_output.len() == nst_bytes
        } else {
            owf_output.len() == beta * nst_bytes
        },
        beta >= 1,
        if !is_em {
            forall |q: int, r_c: int|
                0 <= q < (ske as int / 4) && 0 <= r_c < 4
                    ==> crate::prover::key_expansion::kec_claim1(
                            w_bytes@.subrange(0, lke_bytes as int),
                            nk as int,
                            lambda as int,
                            n_words as int,
                            lke_bytes as int,
                            q,
                            r_c,
                        )
                        && crate::prover::key_expansion::kec_claim2(
                            w_bytes@.subrange(0, lke_bytes as int),
                            nk as int,
                            lambda as int,
                            n_words as int,
                            lke_bytes as int,
                            q,
                            r_c,
                        )
        } else {
            true
        },
        // the grinding-loop space (the wrote-chall3/ctr rows ride
        // the carve table above)
        1 == 1,
    ensures
        1 == 1,
{
    // ::0 the carve (SignatureRefMut::from; the upstream wrapper
    // faest_sign carries it at :370-371)
    let sig = signature_ref_mut_from(
        signature,
        lhat_bytes,
        tau,
        vole_out,
        l_bytes,
        lambda / 8,
        decom_size,
    );
    // ::3
    let mut mu: [u8; 32] = [0u8; 32];
    faest_hash_mu(&mut mu, owf_input, owf_output, msg);
    // ::4
    let mut r_seed: [u8; 16] = [0u8; 16];
    {
        let iv_window: &mut [u8] = &mut *sig.iv_pre;
        faest_hash_r_iv(&mut r_seed, iv_window, owf_key, &mu, rho);
    }
    // ::5
    let mut iv: [u8; 16] = [0u8; 16];
    {
        let mut i: usize = 0;
        while i < 16
        {
            iv[i] = sig.iv_pre[i];
            i += 1;
        }
    }
    faest_hash_iv(&mut iv);
    // ::7
    let vole: VoleCommitResultTwin = volecommit_cs(
        &mut *sig.cs,
        &r_seed,
        &iv,
        lambda / 8,
        lhat_bytes,
        tau,
    );
    // ::8
    let mut chall1: [u8; 88] = [0u8; 88];
    faest_hash_challenge_1(&mut chall1, &mu, &vole.com, sig.cs, &iv);
    // ::10
    // hash u and write the result (i.e., u_tilde) into signature
    faest_hash_u_vector(&mut *sig.u_tilde, &vole.u, &chall1);
    // ::11
    // hash v row by row and update h2_hasher with the row hashes
    let mut h2_hasher: Hasher128<10> =
        faest_hash_challenge_2_init(&chall1, &*sig.u_tilde);
    faest_hash_v_matrix(
        &mut h2_hasher,
        &vole.v_flat,
        lhat_bytes,
        lambda,
        &chall1,
    );
    // ::13
    // compute and write masked witness 'd' in signature
    mask_witness(&mut *sig.d, w_bytes, &vole.u[0..l_bytes]);
    // ::14
    let mut chall2: [u8; 56] = [0u8; 56];
    faest_hash_challenge_2_finalize(h2_hasher, &mut chall2, &*sig.d);
    // ::18 (the prove dispatch; ::16 the u window row)
    let (a0_t, a1_t, a2_t): (u128, u128, u128) = aes_prove(
        w_bytes,
        &vole.u[l_bytes..l_bytes + 2 * (lambda / 8)],
        &vole.v_flat,
        owf_input,
        owf_output,
        &[],
        &chall2,
        nst,
        nst_bytes,
        nk,
        lambda,
        r,
        ske,
        n_words,
        l_bytes,
        lhat_bytes,
        lke_bytes,
        lenc_bytes,
        beta,
        is_em,
    );
    // Save a1_tilde, a2_tilde in signature
    {
        let mut a1_bytes: [u8; 16] = [0u8; 16];
        let mut a2_bytes: [u8; 16] = [0u8; 16];
        let mut i: usize = 0;
        while i < 16
        {
            a1_bytes[i] = ((a1_t >> (8 * i)) & 0xff) as u8;
            a2_bytes[i] = ((a2_t >> (8 * i)) & 0xff) as u8;
            i += 1;
        }
        save_zk_constraints(
            &mut *sig.a1_tilde,
            &mut *sig.a2_tilde,
            &a1_bytes,
            &a2_bytes,
        );
    }
    // ::19-26 the grinding loop
    {
        let mut a0_bytes: [u8; 16] = [0u8; 16];
        let mut i: usize = 0;
        while i < 16
        {
            a0_bytes[i] = ((a0_t >> (8 * i)) & 0xff) as u8;
            i += 1;
        }
        let hasher: Hasher128<11> = faest_hash_challenge_3_init(
            &chall2,
            &a0_bytes,
            &*sig.a1_tilde,
            &*sig.a2_tilde,
        );
        // `for ctr in 0u32..`: the u32-exhaustive range, spelled as
        // the counted u64 counter (tried covers 0 ..= u32::MAX)
        let mut tried: u64 = 0;
        while tried < 4294967296
        {
            let ctr: u32 = (tried & 0xffff_ffff) as u32;
            // ::20
            faest_hash_challenge_3_finalize(&hasher, &mut *sig.chall3, ctr);
            // declassify chall_3 which is put into the signature
            // (the declassify! macro lowers to {}; the FA10 record)
            // ::21
            if check_challenge_3(&*sig.chall3, lambda, w_grind) {
                // ::24
                let mut i_delta: Vec<u16> = Vec::new();
                {
                    let mut di: usize = 0;
                    while di < tau1
                    {
                        i_delta.push(chall_to_u16(
                            &*sig.chall3,
                            tau1_offset_unchecked(k_idx, di),
                            k_idx,
                        ));
                        di += 1;
                    }
                    while di < tau
                    {
                        i_delta.push(chall_to_u16(
                            &*sig.chall3,
                            tau0_offset_unchecked(tau1, k_idx, di),
                            k_idx - 1,
                        ));
                        di += 1;
                    }
                }
                // ::26
                match bavc_open(&vole.decom, &i_delta, lambda / 8) {
                    Option::Some((coms, nodes)) => {
                        // Save decom_i and ctr bits
                        save_decom_and_ctr(&mut *sig.decom_i, &coms, &nodes);
                        write_ctr_segment(&mut *sig.ctr, ctr);
                        return true;
                    }
                    Option::None => {}
                }
            }
            tried += 1;
        }
    }
    // Err(Error::new()) (:484; the u32-exhaustion lane)
    false
}

// ===========================================================================
// verify (upstream :502-572) + the wrapper. FROZEN (the sign-chain
// ruling); the requires table mirrors aes_verify's (the zk twin;
// the verifier side carries no claim rows -- the FA12 window-4
// ruling re-checked first-hand).
// ===========================================================================

/// Origin Rust (:502-572); the verify chain.
#[verifier::external_body]
pub fn verify_chain(
    msg: &[u8],
    owf_input: &[u8],
    owf_output: &[u8],
    signature: &[u8],
    schedule_bytes: &[u8],
    nst: usize,
    nst_bytes: usize,
    nk: usize,
    lambda: usize,
    r: usize,
    ske: usize,
    n_words: usize,
    l_bytes: usize,
    lhat_bytes: usize,
    lke: usize,
    lenc: usize,
    beta: usize,
    is_em: bool,
    tau: usize,
    k_idx: usize,
    w_grind: usize,
    vole_out: usize,
    decom_size: usize,
) -> (ok: bool)
    requires
        // the landing-axis rows
        lambda == 128,
        nst >= 4,
        nst_bytes == 4 * nst,
        nk >= 1,
        nk <= 8,
        lambda == 32 * nk,
        r >= 2,
        r % 2 == 0,
        r <= 14,
        n_words == 4 * (r + 1),
        n_words > nk,
        ske >= 4,
        ske <= 64,
        ske % 4 == 0,
        n_words <= 64,
        32 * n_words <= usize::MAX,
        tau >= 1,
        2 <= k_idx <= 15,
        w_grind >= 1,
        w_grind <= lambda,
        vole_out == 18,
        decom_size >= 1,
        l_bytes >= 1,
        lhat_bytes > 18,
        lhat_bytes == l_bytes + 3 * (lambda / 8) + 2,
        lhat_bytes * (tau - 1)
        + vole_out
        + l_bytes
        + 2 * (lambda / 8)
        + decom_size
        + lambda / 8
        + 16
        + 4
        == signature.len(),
        // the aes_verify mirror rows (the verifier's window-5 table)
        lke >= lambda,
        lke + (lenc * (if is_em { 1 } else { beta })) <= l_bytes * 8,
        owf_input.len() == nst_bytes,
        if is_em {
            owf_output.len() == nst_bytes
        } else {
            owf_output.len() == beta * nst_bytes
        },
        beta >= 1,
        8 * beta <= usize::MAX,
        if is_em {
            schedule_bytes.len() >= 32 * (r + 1)
        } else {
            schedule_bytes.len() == 0
        },
        if !is_em {
            8 * ske <= (l_bytes * 8 - lambda)
                && (lambda as int)
                    + 32 * (crate::prover::key_expansion::kef_cw(
                        nk as int, nk as int, n_words as int) + 1)
                    <= (l_bytes * 8) as int
                && crate::prover::key_expansion::keb_iwd(
                    lambda as int, ske as int - 1) + 8 * 3 + 8
                    <= 32 * n_words
                && ((ske as int - 1)
                    / (4 * (lambda as int / 128))) < 30
                && (32 * (nk as int - 1)
                    + (if lambda == 192 { 192int } else { 128int })
                        * ((ske as int / 4) - 1) + 40)
                    <= 32 * n_words as int
        } else {
            true
        },
    ensures
        1 == 1,
{
    // ::1-4 the carve (SignatureRef::try_from; the ::4 gate rides
    // the split face)
    match signature_ref_try_from(
        signature,
        lhat_bytes,
        tau,
        vole_out,
        l_bytes,
        lambda / 8,
        lambda,
        w_grind,
        decom_size,
    ) {
        Option::None => false,
        Option::Some(sig) => {
            let ctr: u32 = parse_ctr(sig.ctr);
            // ::2
            let mut mu: [u8; 32] = [0u8; 32];
            faest_hash_mu(&mut mu, owf_input, owf_output, msg);
            // ::3
            let mut iv: [u8; 16] = [0u8; 16];
            {
                let mut i: usize = 0;
                while i < 16
                {
                    iv[i] = sig.iv_pre[i];
                    i += 1;
                }
            }
            faest_hash_iv(&mut iv);
            // ::7-8 (the decom chunk rows = the parse_decom face at
            // the record level; the shim consumes the flat window)
            match volereconstruct_cs(
                sig.chall3,
                sig.decom_i,
                sig.cs,
                &iv,
                lambda / 8,
                lhat_bytes,
                tau,
            ) {
                Option::None => false,
                Option::Some((com, q_flat)) => {
                    // ::10
                    let mut chall1: [u8; 88] = [0u8; 88];
                    faest_hash_challenge_1(
                        &mut chall1,
                        &mu,
                        &com,
                        sig.cs,
                        &iv,
                    );
                    let mut h2_hasher: Hasher128<10> =
                        faest_hash_challenge_2_init(&chall1, sig.u_tilde);
                    // ::12-14
                    faest_hash_q_matrix(
                        &mut h2_hasher,
                        &q_flat,
                        lhat_bytes,
                        lambda,
                        sig.u_tilde,
                        &chall1,
                        sig.chall3,
                    );
                    // ::15
                    let mut chall2: [u8; 56] = [0u8; 56];
                    faest_hash_challenge_2_finalize(
                        h2_hasher,
                        &mut chall2,
                        sig.d,
                    );
                    // ::17
                    let a0_tilde: u128 = aes_verify(
                        &q_flat,
                        sig.d,
                        owf_input,
                        owf_output,
                        schedule_bytes,
                        &chall2,
                        sig.chall3,
                        sig.a1_tilde,
                        sig.a2_tilde,
                        nst,
                        nst_bytes,
                        nk,
                        lambda,
                        r,
                        ske,
                        n_words,
                        l_bytes,
                        lhat_bytes,
                        lke,
                        lenc,
                        beta,
                        is_em,
                    );
                    // ::18
                    let mut chall3_prime: [u8; 16] = [0u8; 16];
                    {
                        let mut a0_bytes: [u8; 16] = [0u8; 16];
                        let mut i: usize = 0;
                        while i < 16
                        {
                            a0_bytes[i] = ((a0_tilde >> (8 * i)) & 0xff) as u8;
                            i += 1;
                        }
                        faest_hash_challenge_3(
                            &mut chall3_prime,
                            &chall2,
                            &a0_bytes,
                            sig.a1_tilde,
                            sig.a2_tilde,
                            ctr,
                        );
                    }
                    // ::19
                    let mut same: bool = true;
                    {
                        let mut i: usize = 0;
                        while i < 16
                        {
                            if sig.chall3[i] != chall3_prime[i] {
                                same = false;
                            }
                            i += 1;
                        }
                    }
                    same
                }
            }
        }
    }
}

} // verus!
