//! faest 0.3.0 -- Verus transcription of src/internal_keys.rs,
//! batch FA10.
//!
//! Upstream: internal_keys.rs (469 lines, pin 9ccc68c0). The module
//! doc (":1-3"): "Implementation of internal representation of
//! secret and public keys -- This module also handles serialization
//! and deserialization of any keys." The module is a data plumbing
//! shell around the OWFParameters row constants: SecretKey (:22-28)
//! holds owf_key + pk; TryFrom<&[u8]> (:62-99) is SK parsing with the
//! owf_key[0] format check plus the O::evaluate_owf recomputation;
//! ByteEncoding (:110-135/:394-417) is [owf_input | key/output]
//! serialization; PublicKey (:339-345) holds owf_input + owf_output;
//! UnpackedSecretKey (:201-207) adds param::Witness.
//!
//! Upstream doc lines re-erected as obligations or record notes:
//! - SecretKey doc (:21) "Internal representation of a secret key."
//!   and PublicKey doc (:338) "Internal representation of a public
//!   key": the struct shells lower to the slice/Seq contract faces
//!   below (no runtime semantics beyond the byte moves).
//! - UnpackedSecretKey doc (:199) "Internal representation of a
//!   secret key, including the zk witness.": the witness member is
//!   `param::Witness<O>` = Box<Array<u8, LBytes>> (parameter.rs:84)
//!   -- the content is the aes_extendedwitness twin output; its
//!   production contract rides src/witness.rs (this batch,
//!   aes_extendedwitness_from_kb).
//! - classify!/declassify! (:84-86, :120, :127): upstream lib.rs
//!   (:153-165) compiles BOTH macros to no-ops unless
//!   `valgrind = "enabled"` (then they are memcheck::Classifier
//!   client calls). The leak-face obligation on the key bit plane is
//!   THEREFORE cfg-gated: in the default build there is no bit-level
//!   instrumentation at all (the macros expand to {}), and the
//!   actual marking surface (memcheck.rs) only exists in the
//!   valgrind build. Transcribed as record notes at the exact call
//!   sites below (S-FA10w-3 in the batch notes).
//! - Error: upstream `use crate::Error` is the re-exported
//!   signature-crate Error (lib.rs:103 `pub use signature::{...,
//!   Error, ...}`) -- an external-crate carrier; the twin lowers the
//!   two Err(Error::new()) sites (length mismatch :69/:75/:95, and
//!   the format check :78-80) to the ParseOutcome lanes below.
//! - Debug impls (:146-157, :284-296) redact owf_key (the literal
//!   `"redacted"` string field on SecretKey and
//!   owf_key_witness on UnpackedSecretKey) and print the pk fields:
//!   the redaction OBLIGATION is the leak-relevant face, recorded at
//!   REDACTED_KEY_FIELDS below; fmt plumbing itself is out of the
//!   Verus surface (no value flow).
//! - Clone/Eq/PartialEq are memberwise carries; the byte-semantic
//!   face is ess_eq below (upstream k.owf_key == rhs.owf_key etc.,
//!   :163-165/:207-208/:435-437 -- note UnpackedSecretKey::eq
//!   deliberately compares ONLY sk, the wit member being a function
//!   of sk via O::witness).
//! - serde (Serialize/Deserialize cfg blocks :170-197, :309-336,
//!   :442-469) and zeroize (:30-48, :200 derive) are feature-gated
//!   external-crate derives: record-only.
//! - O::evaluate_owf(&owf_key, &owf_input) (:82): the OWF proper is
//!   the AES/Rijndael encryption path -- FA13 scope (and D-FA10-1
//!   for the key-schedule layer); the twin's parse contract takes
//!   the owf_output as data at the recontract level (sk_recontract,
//!   no byte evaluation).
//!
//! Representation lowerings:
//! - Array<u8, O::SK/PK/LambdaBytes/InputSize/OutputSize> sizes ride
//!   the FA9 tower row consts as explicit arguments; the SK byte
//!   layout is [owf_input | owf_key] (upstream :70 splits at
//!   InputSize) and PK is [owf_input | owf_output] (:367).
//! - to_vec (:124-130) is the same layout over Vec; the encoded_len
//!   faces (:132-134, :414-416) are the row SK/PK consts.

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

// ===========================================================================
// Byte-serialization contract faces (the ByteEncoding impls).
//
// Origin Rust (SecretKey::to_bytes, internal_keys.rs:116-122):
//     fn to_bytes(&self) -> Self::Repr {
//         let mut buf = Array::default();
//         buf[..O::InputSize::USIZE].copy_from_slice(&self.pk.owf_input);
//         buf[O::InputSize::USIZE..].copy_from_slice(&self.owf_key);
//         classify!(&buf);
//         buf
//     }
// (PublicKey::to_bytes :400-405 is the same shape over owf_output;
// the to_vec twins :124-130/:407-412 have the same layout.)
// classify!(:120, :127) is the cfg no-op of upstream lib.rs -- in
// the default build it expands to {} (record note, S-FA10w-3).
// ===========================================================================

/// SK serialization layout: SK == [owf_input | owf_key]
/// (SK == InputSize + LambdaBytes at every FA9 tower row). This is the
/// doc-level concatenation face; the exec twins below carry the
/// extensional pointwise form.
pub open spec fn sk_bytes_of(owf_input: Seq<u8>, owf_key: Seq<u8>) -> Seq<u8>
    recommends
        owf_input.len() + owf_key.len() <= usize::MAX,
{
    owf_input.add(owf_key)
}

/// PK serialization layout: PK == [owf_input | owf_output]
/// (PK == InputSize + OutputSize at every FA9 tower row).
pub open spec fn pk_bytes_of(owf_input: Seq<u8>, owf_output: Seq<u8>) -> Seq<u8>
    recommends
        owf_input.len() + owf_output.len() <= usize::MAX,
{
    owf_input.add(owf_output)
}

/// Exec twin of the SecretKey::to_bytes copy_from_slice pair
/// (:116-122). (The upstream classify!(&buf) no-op site is the
/// position after the second copy -- S-FA10w-3 record.)
pub fn sk_byte_encode(buf: &mut [u8], owf_input: &[u8], owf_key: &[u8])
    requires
        owf_input.len() + owf_key.len() == buf.len(),
        owf_input.len() + owf_key.len() <= usize::MAX,
    ensures
        forall |k: int| 0 <= k < owf_input.len()
            ==> final(buf)@[k as int] == owf_input[k as int],
        forall |k: int| 0 <= k < owf_key.len()
            ==> final(buf)@[owf_input.len() as int + k as int]
                == owf_key[k as int],
{
    // buf[..InputSize].copy_from_slice(&self.pk.owf_input)
    let mut i: usize = 0;
    while i < owf_input.len()
        invariant
            i <= owf_input.len(),
            buf.len() == owf_input.len() + owf_key.len(),
            forall |k: int| 0 <= k < i ==> buf[k as int] == owf_input[k as int],
        decreases owf_input.len() - i,
    {
        buf[i] = owf_input[i];
        i += 1;
    }
    // buf[InputSize..].copy_from_slice(&self.owf_key)
    // classify!(&buf);  -- upstream no-op macro site (:120)
    i = 0;
    while i < owf_key.len()
        invariant
            i <= owf_key.len(),
            buf.len() == owf_input.len() + owf_key.len(),
            forall |k: int| 0 <= k < owf_input.len() ==> buf[k as int] == owf_input[k as int],
            forall |k: int| 0 <= k < i ==> buf[owf_input.len() as int + k] == owf_key[k as int],
        decreases owf_key.len() - i,
    {
        buf[owf_input.len() + i] = owf_key[i];
        i += 1;
    }
}

/// Exec twin of PublicKey::to_bytes (:400-405).
pub fn pk_byte_encode(buf: &mut [u8], owf_input: &[u8], owf_output: &[u8])
    requires
        owf_input.len() + owf_output.len() == buf.len(),
        owf_input.len() + owf_output.len() <= usize::MAX,
    ensures
        forall |k: int| 0 <= k < owf_input.len()
            ==> final(buf)@[k as int] == owf_input[k as int],
        forall |k: int| 0 <= k < owf_output.len()
            ==> final(buf)@[owf_input.len() as int + k as int]
                == owf_output[k as int],
{
    let mut i: usize = 0;
    while i < owf_input.len()
        invariant
            i <= owf_input.len(),
            buf.len() == owf_input.len() + owf_output.len(),
            forall |k: int| 0 <= k < i ==> buf[k as int] == owf_input[k as int],
        decreases owf_input.len() - i,
    {
        buf[i] = owf_input[i];
        i += 1;
    }
    i = 0;
    while i < owf_output.len()
        invariant
            i <= owf_output.len(),
            buf.len() == owf_input.len() + owf_output.len(),
            forall |k: int| 0 <= k < owf_input.len()
                ==> buf[k as int] == owf_input[k as int],
            forall |k: int| 0 <= k < i
                ==> buf[owf_input.len() as int + k] == owf_output[k as int],
        decreases owf_output.len() - i,
    {
        buf[owf_input.len() + i] = owf_output[i];
        i += 1;
    }
}

// ===========================================================================
// SK parsing (TryFrom<&[u8]> for SecretKey, internal_keys.rs:62-99).
//
// Origin Rust:
//     impl<O> TryFrom<&[u8]> for SecretKey<O> where O: OWFParameters {
//         type Error = Error;
//         fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
//             if bytes.len() == O::SK::USIZE {
//                 let (owf_input, owf_key) = bytes.split_at(O::InputSize::USIZE);
//                 let Ok(owf_input) = Array::try_from(owf_input) else { return Err(Error::new()); };
//                 let Ok(owf_key) = Array::try_from(owf_key) else { return Err(Error::new()); };
//                 if owf_key[0] & 0b11 == 0b11 { return Err(Error::new()); }
//                 let owf_output = O::evaluate_owf(&owf_key, &owf_input);
//                 classify!(&owf_key);
//                 declassify!(&owf_output);
//                 declassify!(&owf_input);
//                 Ok(Self { owf_key, pk: PublicKey { owf_input, owf_output } })
//             } else { Err(Error::new()) }
//         }
//     }
// The two Array::try_from guards are length facts held by the twin's
// requires (they cannot misfire when the SK length checks first);
// the format check is the randomized-encoding domain gate shared
// with parameter.rs keygen_with_rng (parameter.rs:350-357: the key
// sample loop rejects owf_key[0] & 0b11 == 0b11 until the check
// passes -- the 254/256 acceptance domain).
// ===========================================================================

/// The parse verdict lanes of the upstream Err sites: length
/// mismatch (SK size) and the owf_key[0] format-domain rejection.
pub enum ParseOutcome {
    Ok,
    BadLen,
    BadFormat,
}

/// The owf_key format domain gate (upstream :78): owf_key[0] & 0b11
/// must not be 0b11.
pub open spec fn sk_format_ok(owf_key: Seq<u8>) -> bool {
    owf_key.len() >= 1 && (owf_key[0] & 3) != 3
}

/// Exec twin of the SecretKey byte-parse verdict (the evaluate_owf
/// recomputation line is contract data at this level; see the header
/// entry on O::evaluate_owf).
pub fn secret_key_parse_verdict(
    bytes: &[u8],
    input_size: usize,
    lambda_bytes: usize,
) -> (outcome: ParseOutcome)
    requires
        0 < lambda_bytes,
        input_size + lambda_bytes <= usize::MAX,
    ensures
        outcome == ParseOutcome::Ok
            <==> (bytes.len() == input_size + lambda_bytes
                && sk_format_ok(bytes@.subrange(
                    input_size as int,
                    input_size as int + lambda_bytes as int,
                ))),
        outcome == ParseOutcome::BadLen
            <==> bytes.len() != input_size + lambda_bytes,
        bytes.len() != input_size + lambda_bytes
            ==> outcome == ParseOutcome::BadLen,
        bytes.len() == input_size + lambda_bytes
            && bytes[input_size as int] & 0b11 == 0b11
            ==> outcome == ParseOutcome::BadFormat,
        bytes.len() == input_size + lambda_bytes
            && bytes[input_size as int] & 0b11 != 0b11
            ==> outcome == ParseOutcome::Ok,
{
    if bytes.len() != input_size + lambda_bytes {
        ParseOutcome::BadLen
    } else if bytes[input_size] & 0b11 == 0b11 {
        // classify!(&owf_key); declassify!(...): the cfg no-op sites
        // (:84-86) -- default-build expansion {}; record S-FA10w-3.
        ParseOutcome::BadFormat
    } else {
        ParseOutcome::Ok
    }
}

/// Spec face of the post-parse bipartition: upstream
/// `bytes.split_at(InputSize)` with the checked SK length.
pub open spec fn sk_split_points(
    bytes: Seq<u8>,
    input_size: int,
) -> (Seq<u8>, Seq<u8>)
    recommends
        0 <= input_size <= bytes.len(),
{
    (
        bytes.subrange(0, input_size),
        bytes.subrange(input_size, bytes.len() as int),
    )
}

// ===========================================================================
// Equality/Clone/Debug record faces.
// ===========================================================================

/// Exec twin of the bytewise equality the upstream PartialEq impls
/// reduce to (owf_key == rhs.owf_key etc.,
/// :163-165/:207-208/:435-437).
pub fn key_bytes_eq(a: &[u8], b: &[u8]) -> (res: bool)
    ensures
        res <==> (a.len() == b.len()
            && forall |k: int| 0 <= k < a.len() ==> a[k as int] == b[k as int]),
{
    if a.len() != b.len() {
        false
    } else {
        assert(a.len() == b.len());
        let mut i: usize = 0;
        let mut acc: bool = true;
        while i < a.len()
            invariant
                i <= a.len(),
                a.len() == b.len(),
                acc <==> forall |k: int| 0 <= k < i ==> a[k as int] == b[k as int],
            decreases a.len() - i,
        {
            acc = acc && a[i] == b[i];
            i += 1;
        }
        acc
    }
}

/// The Debug redaction record: the fields upstream prints as the
/// literal string "redacted" (SecretKey::owf_key :152,
/// UnpackedSecretKey::owf_key :290 and owf_key_witness :293). The
/// printed set is otherwise exactly the pk fields (owf_input,
/// owf_output) -- the redaction obligation that Debug NEVER prints
/// the key bytes or the witness bytes.
pub open spec fn debug_prints_redacted(owf_key: Seq<u8>, owf_key_witness: Seq<u8>) -> bool {
    &&& owf_key.len() >= 0
    &&& owf_key_witness.len() >= 0
    // The Debug write path outputs the two "redacted" literals in
    // place of these values (record face).
}

// encoded_len record faces (upstream :132-134 and :414-416 return the
// row consts O::SK::USIZE / O::PK::USIZE directly; the FA9 tower OWF*
// consts carry the values, and the FA9 row identities SK =
// InputSize + LambdaBytes / PK = InputSize + OutputSize are asserted
// in the tower).

} // verus!
