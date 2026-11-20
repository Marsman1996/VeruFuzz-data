//! faest 0.3.0 -- Verus transcription of src/witness.rs, batch FA10.
//!
//! Upstream: witness.rs (266 lines, pin 9ccc68c0) is the GF-circuit
//! side of the AES witness extension: aes_extendedwitness (:20-57)
//! builds the extended witness by running the bitsliced Rijndael
//! round function with the delta invnorm'd state captures; the
//! helpers are save_key_bits (:59-65), save_non_lin_bits (:67-92),
//! gf8_exp_238 (:94-108), invnorm (:110-113), store_invnorm_state
//! (:115-118), round_with_save (:120-171); the #[cfg(test)] module
//! (:173-266) runs the six tests/data/AesExtendedWitness.json vectors
//! through O::extendwitness (its KAT content is re-erected in
//! out/kverus-run/FA10 harness rows from the ORACLE crate's realtime
//! upstream run; see batch notes).
//!
//! Upstream doc lines re-erected as obligations or record notes:
//!   - witness.rs:33-35 (the Step 6 note, transcribed verbatim in the
//!     aes_extendedwitness body below): "Note: for FAEST-LAMBDA-EM,
//!     SKE is set to the actual number of S-Boxes in
//!     Rijndael-LAMBDA.KeyExpansion. This slightly differs from FAEST
//!     Spec v2, where SKE is always set to 0 in EM mode." -- the EM
//!     rows' SKe const (40/52/60) claims this deviation from the FAEST
//!     Spec v2 value 0; the deviation's value surface is measured and
//!     oracle-arbitrated in the batch notes (S-FA10w-1; the row consts
//!     ride the FA9 tower pins).
//!   - witness.rs:46 "In EM mode, AES key is part of public input
//!     while pt is secret" -- the EM rows of upstream parameter.rs
//!     call aes_extendedwitness::<O>(owf_input, owf_key) (the swapped
//!     argument order, parameter.rs:638/:706/:776), so the save_key_bits
//!     branch stores the secret pt while the key schedule runs over
//!     the public AES key; kept as the contract order in the twin.
//!   - witness.rs:130 "Input1 is always empty except for FAEST-EM-192
//!     and FAEST-EM-256" -- upstream splits input1 at 16 and relies on
//!     the bitslice debug-assert domain (len 0/8/16, FA10-pre S-FA10-4);
//!     the twin re-erects the trichotomy as the input-size requires.
//!
//! Representation lowerings (trust boundary):
//!   - the O: OWFParameters generic dispatch lowers to the RowCfg
//!     struct of witness-relevant row constants (the six FA9 tower
//!     row sets); each upstream O::XXX::USIZE site spells row.xxx at
//!     the same code position.
//!   - upstream `Box<Array<u8, O::LBytes>>` lowers to the caller-
//!     provided witness slice plus the returned final index (alloc
//!     shells carry no semantics); upstream's type-length guarantee
//!     `written == LBytes` becomes the top ensures.
//!   - upstream's `owf_input.to_owned()` + `input[0] ^= 1` lowers to a
//!     fixed 32-byte workspace copy (InputSize <= 32 at all six rows).
//!   - hybrid_array copy_from_slice has no vstd spec: every byte copy
//!     is an explicit while loop with pointwise ensures (FA1
//!     xor_arrays precedent).
//!   - `Array::<_, U3>::from_iter(convert_from_batchblocks(..).take(
//!     3))` lowers to three convert_from_batchblocks_word reads
//!     (indices 0,1,2 -- the FA10-pre word accessor twin).
//!   - rijndael_key_schedule (the D-FA10-1 deferred serialization
//!     layer) is NOT transcribed here: the twin takes kb as an input
//!     parameter under the structural contract below (kb length ==
//!     the OWF*_KB_WORDS const of the row; consumption windows
//!     verified to fit); the kb production line is carried by the
//!     ORACLE crate (upstream actual-run, 6/6 AesExtendedWitness
//!     vectors pass there) -- the FA10-pre delivery-note discrepancy
//!     (its notes list OWF*_KB_WORDS consts that never landed) is
//!     recorded in the batch notes; the pins are built HERE.
//!   - the three deep-loop exec twins (save_non_lin_bits,
//!     round_with_save, aes_extendedwitness_from_kb) and their
//!     spec-budget families are transcribed with upstream bodies in
//!     sibling file src/witness_loops.rs -- D-FA10w-1 (their verus
//!     loop-contract chains have not converged this batch; the
//!     probe-filed invariant rules live in that file's header). The
//!     value surface of the round loop's per-byte write helpers
//!     (invnorm/store_invnorm_state), the save_key_bits/copy4 byte
//!     movers, the row dispatch consts, the kb pins + window
//!     identities, and the internal_keys contract faces are all
//!     verified here and in the fa10w driver panel.

use vstd::prelude::*;
use vstd::seq::Seq;

use crate::parameter_tower::{
    OWF128EM_BETA, OWF128EM_IS_EM, OWF128EM_L_BYTES, OWF128EM_NK, OWF128EM_NST, OWF128EM_R,
    OWF128EM_SKE, OWF128_BETA, OWF128_IS_EM, OWF128_L_BYTES, OWF128_NK, OWF128_NST, OWF128_R,
    OWF128_SKE, OWF192EM_BETA, OWF192EM_IS_EM, OWF192EM_L_BYTES, OWF192EM_NK, OWF192EM_NST,
    OWF192EM_R, OWF192EM_SKE, OWF192_BETA, OWF192_IS_EM, OWF192_L_BYTES, OWF192_NK, OWF192_NST,
    OWF192_R, OWF192_SKE, OWF256EM_BETA, OWF256EM_IS_EM, OWF256EM_L_BYTES, OWF256EM_NK,
    OWF256EM_NST, OWF256EM_R, OWF256EM_SKE, OWF256_BETA, OWF256_IS_EM, OWF256_L_BYTES, OWF256_NK,
    OWF256_NST, OWF256_R, OWF256_SKE, OWF128_INPUT_SIZE, OWF128EM_INPUT_SIZE, OWF192_INPUT_SIZE,
    OWF192EM_INPUT_SIZE, OWF256_INPUT_SIZE, OWF256EM_INPUT_SIZE, BASE128_LAMBDA_BYTES,
    BASE192_LAMBDA_BYTES, BASE256_LAMBDA_BYTES,
};
use crate::rijndael_32::{
    bitslice, inv_bitslice, mix_columns_0, convert_from_batchblocks_word,
    rijndael_add_round_key, rijndael_shift_rows_1, rijndael_sub_bytes, State,
};
use crate::small_fields::{gf8_mul, gf8_mul_spec, gf8_square};

verus! {

// ===========================================================================
// gf8_exp_238 (upstream witness.rs:94-108).
// Origin Rust:
//     fn gf8_exp_238(x: GF8) -> GF8 {
//         // 238 == 0b11101110
//         let y = x.square(); // x^2
//         let x = y.square(); // x^4
//         let y = x * y;
//         let x = x.square(); // x^8
//         let y = x * y;
//         let x = x.square(); // x^16
//         let x = x.square(); // x^32
//         let y = x * y;
//         let x = x.square(); // x^64
//         let y = x * y;
//         let x = x.square(); // x^128
//         x * y
//     }
// GF8 and Square lower to the FA2 faces (gf8_square / gf8_mul over the
// u8 representation; the Square trait face is fields/mod.rs squared8,
// whose body IS gf8_mul_spec(x, x)).
// ===========================================================================

/// Spec face of the upstream square/mul chain: the exponent ladder
/// 2,4,6,8,14,16,32,46,64,110,128,238 (238 == 0b11101110) in GF(2^8).
pub open spec fn gf8_exp_238_spec(x0: u8) -> u8 {
    let y2 = gf8_mul_spec(x0, x0);        // x^2
    let x4 = gf8_mul_spec(y2, y2);        // x^4
    let y6 = gf8_mul_spec(x4, y2);        // x^6
    let x8 = gf8_mul_spec(x4, x4);        // x^8
    let y14 = gf8_mul_spec(x8, y6);       // x^14
    let x16 = gf8_mul_spec(x8, x8);       // x^16
    let x32 = gf8_mul_spec(x16, x16);     // x^32
    let y46 = gf8_mul_spec(x32, y14);     // x^46
    let x64 = gf8_mul_spec(x32, x32);     // x^64
    let y110 = gf8_mul_spec(x64, y46);    // x^110
    let x128 = gf8_mul_spec(x64, x64);    // x^128
    gf8_mul_spec(x128, y110)             // x^238
}

/// Exec twin (body verbatim; the shadowing `let y = ...` ladder is
/// re-spelled with named lanes because Verus rejects shadowing in
/// lets; every lane keeps its upstream exponent comment).
pub fn gf8_exp_238(x: u8) -> (res: u8)
    ensures
        res == gf8_exp_238_spec(x),
{
    let y2 = gf8_square(x); // x^2
    let x4 = gf8_square(y2); // x^4
    let y6 = gf8_mul(x4, y2);
    let x8 = gf8_square(x4); // x^8
    let y14 = gf8_mul(x8, y6);
    let x16 = gf8_square(x8); // x^16
    let x32 = gf8_square(x16); // x^32
    let y46 = gf8_mul(x32, y14);
    let x64 = gf8_square(x32); // x^64
    let y110 = gf8_mul(x64, y46);
    let x128 = gf8_square(x64); // x^128
    gf8_mul(x128, y110)
}

// ===========================================================================
// invnorm (upstream witness.rs:110-113) and store_invnorm_state
// (:115-118).
// Origin Rust:
//     fn invnorm(x: u8) -> u8 {
//         let x = u8::from(gf8_exp_238(x.into()));
//         (x & 1) ^ ((x >> 5) & 6) ^ ((x << 1) & 8)
//     }
//     #[inline]
//     fn store_invnorm_state(lo_idx: u8, hi_idx: u8) -> u8 {
//         invnorm(lo_idx) | (invnorm(hi_idx) << 4)
//     }
// ===========================================================================

/// Spec face of invnorm over the exp-238 image: the (norm of the)
/// nonlinear-part encoding for the delta-to-be-checked byte.
pub open spec fn invnorm_spec(x: u8) -> u8 {
    let g = gf8_exp_238_spec(x);
    (g & 1) ^ ((g >> 5) & 6) ^ ((g << 1) & 8)
}

/// Exec twin of invnorm (body verbatim modulo the ror/shift vstd
/// semantics -- plain u8 machine ops, mirrors in the spec face).
pub fn invnorm(x: u8) -> (res: u8)
    ensures
        res == invnorm_spec(x),
{
    let g = gf8_exp_238(x);
    (g & 1) ^ ((g >> 5) & 6) ^ ((g << 1) & 8)
}

/// Exec twin of store_invnorm_state (verbatim; the two invnorm lanes
/// and the << 4 paste of the nibbles).
#[inline]
pub fn store_invnorm_state(lo_idx: u8, hi_idx: u8) -> (res: u8)
    ensures
        res == (invnorm_spec(lo_idx) | (invnorm_spec(hi_idx) << 4)),
{
    invnorm(lo_idx) | (invnorm(hi_idx) << 4)
}

} // verus!

verus! {

// ===========================================================================
// The row dispatch (upstream O: OWFParameters generic bound).
//
// Origin Rust (witness.rs:20-26):
//     pub(crate) fn aes_extendedwitness<O>(
//         owf_secret: &Array<u8, O::LambdaBytes>,
//         owf_input: &Array<u8, O::InputSize>,
//     ) -> Box<Array<u8, O::LBytes>>
//     where O: OWFParameters,
// The typenum size types lower to the RowCfg constant set (the same
// FA9 tower values); every O::XXX::USIZE site below spells row.xxx
// at the same code position as upstream.
// ===========================================================================

/// The six upstream rows' witness-relevant members. Field values at
/// the six const instances below are the FA9 tower row pins (see the
/// per-field Origin comments for upstream anchors). Copy derive rides
/// the all-scalar field set (upstream O is a zero-sized marker).
#[derive(Copy, Clone)]
pub struct RowCfg {
    /// O::LambdaBytes::USIZE (parameter.rs:184/:206/:228 rows --
    /// LambdaBytesTimes2/2).
    pub lambda_bytes: usize,
    /// O::NSt::USIZE ("Block size (in 32-bit words)").
    pub bc: usize,
    /// O::NK::USIZE ("Number of 32-bit words in key").
    pub kc: usize,
    /// O::R::USIZE ("Number of encryption rounds").
    pub rounds: usize,
    /// O::SKe::USIZE ("Number of S-boxes in key schedule").
    pub ske: usize,
    /// O::Beta::USIZE ("Number of message blocks").
    pub beta: usize,
    /// O::IS_EM ("Returns whether the OWF is used in EM mode").
    pub is_em: bool,
    /// O::LBytes::USIZE ("Witness length for the zk proof (in
    /// bytes)").
    pub l_bytes: usize,
    /// O::InputSize::USIZE ("The input size of the OWF (in bytes)").
    pub input_size: usize,
    /// The fixsliced key-schedule word count of this row (the D-FA10-1
    /// structural contract face of rijndael_key_schedule's output;
    /// the FA10-pre oracle measured these lengths on the upstream
    /// module, see the OWF*_KB_WORDS consts below).
    pub kb_words: usize,
}

/// Row OWF128 (upstream parameter.rs:378-436).
pub const ROW_OW128: RowCfg = RowCfg {
    lambda_bytes: BASE128_LAMBDA_BYTES,
    bc: OWF128_NST,
    kc: OWF128_NK,
    rounds: OWF128_R,
    ske: OWF128_SKE,
    beta: OWF128_BETA,
    is_em: OWF128_IS_EM,
    l_bytes: OWF128_L_BYTES,
    input_size: OWF128_INPUT_SIZE,
    kb_words: 96,
};
/// Row OWF192 (upstream parameter.rs:441-505).
pub const ROW_OW192: RowCfg = RowCfg {
    lambda_bytes: BASE192_LAMBDA_BYTES,
    bc: OWF192_NST,
    kc: OWF192_NK,
    rounds: OWF192_R,
    ske: OWF192_SKE,
    beta: OWF192_BETA,
    is_em: OWF192_IS_EM,
    l_bytes: OWF192_L_BYTES,
    input_size: OWF192_INPUT_SIZE,
    kb_words: 168,
};
/// Row OWF256 (upstream parameter.rs:510-574).
pub const ROW_OW256: RowCfg = RowCfg {
    lambda_bytes: BASE256_LAMBDA_BYTES,
    bc: OWF256_NST,
    kc: OWF256_NK,
    rounds: OWF256_R,
    ske: OWF256_SKE,
    beta: OWF256_BETA,
    is_em: OWF256_IS_EM,
    l_bytes: OWF256_L_BYTES,
    input_size: OWF256_INPUT_SIZE,
    kb_words: 256,
};
/// Row OWF128EM (upstream parameter.rs:579-640).
pub const ROW_OW128EM: RowCfg = RowCfg {
    lambda_bytes: BASE128_LAMBDA_BYTES,
    bc: OWF128EM_NST,
    kc: OWF128EM_NK,
    rounds: OWF128EM_R,
    ske: OWF128EM_SKE,
    beta: OWF128EM_BETA,
    is_em: OWF128EM_IS_EM,
    l_bytes: OWF128EM_L_BYTES,
    input_size: OWF128EM_INPUT_SIZE,
    kb_words: 96,
};
/// Row OWF192EM (upstream parameter.rs:649-710).
pub const ROW_OW192EM: RowCfg = RowCfg {
    lambda_bytes: BASE192_LAMBDA_BYTES,
    bc: OWF192EM_NST,
    kc: OWF192EM_NK,
    rounds: OWF192EM_R,
    ske: OWF192EM_SKE,
    beta: OWF192EM_BETA,
    is_em: OWF192EM_IS_EM,
    l_bytes: OWF192EM_L_BYTES,
    input_size: OWF192EM_INPUT_SIZE,
    kb_words: 112,
};
/// Row OWF256EM (upstream parameter.rs:717-778).
pub const ROW_OW256EM: RowCfg = RowCfg {
    lambda_bytes: BASE256_LAMBDA_BYTES,
    bc: OWF256EM_NST,
    kc: OWF256EM_NK,
    rounds: OWF256EM_R,
    ske: OWF256EM_SKE,
    beta: OWF256EM_BETA,
    is_em: OWF256EM_IS_EM,
    l_bytes: OWF256EM_L_BYTES,
    input_size: OWF256EM_INPUT_SIZE,
    kb_words: 128,
};

// ===========================================================================
// The kb length pins and their consumption-window identities.
//
// kb = rijndael_key_schedule::<NSt, NK, R>(owf_secret, SKe) (the
// D-FA10-1 serialization layer, not transcribed). The structural
// contract every witness consumer needs:
//   (a) the round windows: add_round_key touches kb[0..8] and
//       kb[8*(j+1)..8*(j+2)] for j in 0..R-1, so 8*R <= kb_words;
//   (b) the non-lin window (non-EM rows only): save_non_lin_bits
//       reads kb[8*j..8*(j+1)] for j in 1+NK/8 .. 1+NK/8+nlb, so
//       8*(start_off+nlb) <= kb_words.
// The FA10-pre oracle measured these lengths on the upstream module
// (kb 96/168/256/96/112/128 words per row).
// NOTE (batch bookkeeping): the FA10-pre batch notes list these same
// OWF*_KB_WORDS consts as delivered, but they never landed in the
// verified tree (its rijndael_32.rs carries only ske_noreq); they are
// built here, in the consuming twin.
// ===========================================================================

/// KB word count of the OWF128/OWF128EM rows.
pub const OW128_KB_WORDS: usize = 96;
/// KB word count of the OWF192 row.
pub const OW192_KB_WORDS: usize = 168;
/// KB word count of the OWF256 row.
pub const OW256_KB_WORDS: usize = 256;
/// KB word count of the OWF192EM row.
pub const OW192EM_KB_WORDS: usize = 112;
/// KB word count of the OWF256EM row.
pub const OW256EM_KB_WORDS: usize = 128;

/// start_off of save_non_lin_bits (upstream witness.rs:71 `let
/// start_off = 1 + (O::NK::USIZE / 8)`), spec face.
pub open spec fn nl_start_off(kc: int) -> int {
    1 + kc / 8
}

/// non_lin_blocks of save_non_lin_bits (upstream witness.rs:73-77),
/// spec face (NK divisible by 4 -> SKe/4, else 3*SKe/8).
pub open spec fn nl_blocks(kc: int, ske: int) -> int {
    if kc % 4 == 0 { ske / 4 } else { ske * 3 / 8 }
}

/// (a): the round windows fit every row's kb.
pub proof fn kb_covers_rounds_identity() {
    assert(8 * ROW_OW128.rounds <= OW128_KB_WORDS);
    assert(8 * ROW_OW192.rounds <= OW192_KB_WORDS);
    assert(8 * ROW_OW256.rounds <= OW256_KB_WORDS);
    assert(8 * ROW_OW128EM.rounds <= OW128_KB_WORDS);
    assert(8 * ROW_OW192EM.rounds <= OW192EM_KB_WORDS);
    assert(8 * ROW_OW256EM.rounds <= OW256EM_KB_WORDS);
}

/// (b): the non-lin windows fit the three non-EM rows.
/// OWF128: nlb = 40/4 = 10 blocks after start 1 -> 88 <= 96.
/// OWF192: nlb = 32*3/8 = 12 blocks after start 1 -> 104 <= 168.
/// OWF256: nlb = 52/4 = 13 blocks after start 2 -> 15 blocks -> 120
/// <= 256 (upstream interleaves 16-byte round rows into a 4*NK-word
/// alloc; the serialized tail has large slack here, S-FA10-2).
pub proof fn kb_covers_nonlin_identity() {
    assert(nl_start_off(4) == 1);
    assert(nl_blocks(4, 40) == 10);
    assert(8 * (nl_start_off(4) + nl_blocks(4, 40)) <= OW128_KB_WORDS);
    assert(nl_blocks(6, 32) == 12);
    assert(8 * (nl_start_off(6) + nl_blocks(6, 32)) <= OW192_KB_WORDS);
    assert(nl_blocks(8, 52) == 13);
    assert(8 * (nl_start_off(8) + nl_blocks(8, 52)) <= OW256_KB_WORDS);
}


} // verus!

verus! {

// ===========================================================================
// save_key_bits (upstream witness.rs:59-65).
// Origin Rust:
//     fn save_key_bits<O>(witness: &mut [u8], key: &[u8], index: &mut usize)
//     where O: OWFParameters,
//     {
//         witness[..O::LambdaBytes::USIZE].copy_from_slice(key);
//         *index += O::LambdaBytes::USIZE;
//     }
// copy_from_slice lowers to the pointwise loop (FA1 precedent); the
// O::LambdaBytes::USIZE bound is row.lambda_bytes at the caller.
// ===========================================================================

/// Exec twin: writes key.len() bytes of key at witness[index..] and
/// returns the advanced index. (Upstream's copy_from_slice length
/// equality key.len()==LambdaBytes is guaranteed by the requires.)
pub fn save_key_bits(
    witness: &mut [u8],
    key: &[u8],
    index: usize,
    lambda_bytes: usize,
) -> (new_index: usize)
    requires
        key.len() == lambda_bytes,
        index + lambda_bytes <= witness.len(),
    ensures
        new_index == index + lambda_bytes,
        forall |k: int| 0 <= k < key.len() ==> final(witness)[index + k] == key[k],
        forall |k: int| k < index || index + key.len() <= k < final(witness).len()
            ==> final(witness)[k] == old(witness)[k],
{
    let mut i: usize = 0;
    while i < key.len()
        invariant
            i <= key.len(),
            witness@.len() == old(witness)@.len(),
            index + key.len() <= witness@.len(),
            index + i <= witness.len(),
            forall |k: int| 0 <= k < i ==> witness[index + k] == key[k],
            forall |k: int| k < index || index + key.len() <= k < witness.len()
                ==> witness[k] == old(witness)[k],
        decreases key.len() - i,
    {
        witness[index + i] = key[i];
        i += 1;
    }
    index + lambda_bytes
}

// ===========================================================================
// save_non_lin_bits (upstream witness.rs:67-92).
// Origin Rust:
//     fn save_non_lin_bits<O>(witness: &mut [u8], kb: &[u32], index: &mut usize)
//     where O: OWFParameters,
//     {
//         let start_off = 1 + (O::NK::USIZE / 8);
//
//         let non_lin_blocks = if O::NK::USIZE % 4 == 0 {
//             O::SKe::USIZE / 4
//         } else {
//             O::SKe::USIZE * 3 / 8
//         };
//
//         for j in start_off..start_off + non_lin_blocks {
//             let inside = Array::<_, U3>::from_iter(
//                 convert_from_batchblocks(inv_bitslice(&kb[8 * j..8 * (j + 1)])).take(3),
//             );
//
//             if O::NK::USIZE != 6 || j % 3 == 0 {
//                 witness[*index..*index + size_of::<u32>()].copy_from_slice(&inside[0]);
//                 *index += size_of::<u32>();
//             } else if j % 3 == 1 {
//                 witness[*index..*index + size_of::<u32>()].copy_from_slice(&inside[2]);
//                 *index += size_of::<u32>();
//             }
//         }
//     }
// The `Array::<_, U3>::from_iter(..take(3))` lowers to the three
// word reads i0/i1/i2 (only i0 and i2 are consumed by the branches);
// copy_from_slice(4 bytes) lowers to the unrolled 4-byte writes;
// size_of::<u32>() == 4 is const-folded.
// ===========================================================================

/// The 4-byte window copy (upstream's
/// `witness[*index..*index+4].copy_from_slice(&inside[k])`).
pub fn copy4(witness: &mut [u8], at: usize, w: &[u8; 4])
    requires
        at + 4 <= witness.len(),
    ensures
        forall |k: int| 0 <= k < 4 ==> final(witness)[at + k] == w[k],
        forall |k: int| k < at || at + 4 <= k < final(witness).len()
            ==> final(witness)[k] == old(witness)[k],
        final(witness).len() == old(witness).len(),
{
    let entry_len_c4: usize = witness.len();
    let mut t: usize = 0;
    while t < 4
        invariant
            t <= 4,
            witness@.len() == old(witness)@.len(),
            witness.len() == entry_len_c4,
            at + 4 <= witness@.len(),
            at + t <= witness.len(),
            forall |k: int| 0 <= k < t ==> witness[at + k] == w[k],
            forall |k: int| k < at || at + 4 <= k < witness.len()
                ==> witness[k] == old(witness)[k],
        decreases 4 - t,
    {
        witness[at + t] = w[t];
        t += 1;
    }
}


} // verus!

verus! {

// ===========================================================================
// round_with_save (upstream witness.rs:120-171).
// Origin Rust:
//     fn round_with_save<O>(
//         input1: &[u8], // in
//         kb: &[u32],    // k_bar
//         witness: &mut [u8],
//         index: &mut usize,
//     ) where O: OWFParameters,
//     {
//         let mut state = State::default();
//
//         // Input1 is always empty except for FAEST-EM-192 and FAEST-EM-256
//         let (input0, input1) = input1.split_at(16);
//         bitslice(&mut state, input0, input1);
//
//         rijndael_add_round_key(&mut state, &kb[..8]);
//
//         for j in 0..O::R::USIZE - 1 {
//             let even_round = (j % 2) == 0;
//
//             // Step 19
//             if even_round {
//                 let to_take = if !O::IS_EM { 4 } else { O::NK::USIZE };
//                 for i in convert_from_batchblocks(inv_bitslice(&state)).take(to_take) {
//                     witness[*index] = store_invnorm_state(i[0], i[1]);
//                     *index += 1;
//                     witness[*index] = store_invnorm_state(i[2], i[3]);
//                     *index += 1;
//                 }
//             }
//
//             // Step 23
//             rijndael_sub_bytes(&mut state);
//
//             // Step 24
//             rijndael_shift_rows_1::<O::NSt>(&mut state);
//
//             // Step 25
//             if !even_round {
//                 // Step 26
//                 for i in convert_from_batchblocks(inv_bitslice(&state)).take(O::NSt::USIZE) {
//                     witness[*index..*index + size_of::<u32>()].copy_from_slice(&i);
//                     *index += size_of::<u32>();
//                 }
//             }
//
//             // Step 27
//             mix_columns_0(&mut state);
//
//             // Step 28
//             rijndael_add_round_key(&mut state, &kb[8 * (j + 1)..8 * (j + 2)]);
//         }
//     }
// Lowering notes: State::default() = the zero [u32; 8]; split_at(16)
// lowers to the two workspace copies i0/i1t (pvstd has no split_at
// spec) with i1t's live length n1t = input1.len() - 16 in {0, 8, 16}
// (the bitslice domain, FA10-pre S-FA10-4); the two `for i in
// convert_from_batchblocks(..take(n))` iterator loops lower to the
// indexed word reads; copy_from_slice(4) is the copy4 helper above.
// ===========================================================================


} // verus!

verus! {

// ===========================================================================
// aes_extendedwitness (upstream witness.rs:20-57).
// Origin Rust:
//     pub(crate) fn aes_extendedwitness<O>(
//         owf_secret: &Array<u8, O::LambdaBytes>,
//         owf_input: &Array<u8, O::InputSize>,
//     ) -> Box<Array<u8, O::LBytes>>
//     where O: OWFParameters,
//     {
//         // Step 0
//         let mut input: Array<u8, O::InputSize> = owf_input.to_owned();
//
//         // Step 3
//         let mut witness = Box::<Array<u8, O::LBytes>>::default();
//
//         // Step 6
//         // Note: for FAEST-LAMBDA-EM, SKE is set to the actual number of S-Boxes in Rijndael-LAMBDA.KeyExpansion.
//         // This slightly differs from FAEST Spec v2, where SKE is always set to 0 in EM mode.
//         let kb = rijndael_key_schedule::<O::NSt, O::NK, O::R>(owf_secret, O::SKe::USIZE);
//
//         let mut index = 0;
//
//         // Step 7
//         if !O::IS_EM {
//             save_key_bits::<O>(&mut witness, owf_secret, &mut index);
//             // Step 8
//             save_non_lin_bits::<O>(&mut witness, &kb, &mut index);
//         } else {
//             // In EM mode, AES key is part of public input while pt is secret
//             save_key_bits::<O>(&mut witness, owf_input, &mut index);
//         }
//
//         // Step 14
//         for _ in 0..O::Beta::USIZE {
//             round_with_save::<O>(&input, &kb, &mut witness, &mut index);
//             input[0] ^= 1;
//         }
//
//         witness
//     }
// The Step 6 kb production line (rijndael_key_schedule) is the D-FA10-1
// deferred layer: the twin takes kb as the input parameter under the
// structural contract; the two verbatim EM note lines above stay as
// the batch's S-FA10w-1 anchors (SKe=40/52/60 at the EM rows).
// The Step-numbered comments of upstream are kept at each site.
// ===========================================================================


} // verus!
