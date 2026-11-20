//! faest 0.3.0 -- Verus transcription of the remaining parameter.rs
//! constant tower (batch FA9, the constant-identity batch: one spec
//! mirror per upstream typenum arithmetic chain, plus the cross-group
//! identity theorem set).
//!
//! Origin Rust: upstream src/parameter.rs pins the tower as trait
//! associated types over typenum array sizes:
//!   - BaseParameters rows (BaseParams128 :173-190, BaseParams192
//!     :195-212, BaseParams256 :217-234) over the SecurityParameter
//!     bound (:85-98);
//!   - OWFParameters rows (OWF128 :378-436, OWF192 :441-505, OWF256
//!     :510-574, OWF128EM :579-640, OWF192EM :649-710, OWF256EM
//!     :717-778);
//!   - FAESTParameters rows (:1037-1203; the WGRIND half of each row
//!     was pinned by FA1, SIGNATURE_SIZE rides here);
//!   - get_decom_size (:1014-1023);
//!   plus the upstream const-identity test templates that give this
//!     batch its theorem shapes: lambda (:1233-1237), pk_sk_size
//!     (:1239-1243), owf_parameters (:1245-1252), tau_config
//!     (:1277-1286).
//!
//! Verus has no typenum; per the batch plan (harness-inventory FA9)
//! every Sum/Prod/Quot/Diff type-level chain becomes a flat pinned
//! usize const plus an open spec-fn mirror of the chain arithmetic,
//! and one identity theorem per group checks const == mirror at
//! every row. Sizes are in bytes unless the name says bits. The tau
//! table, the OWF Lambda pins and the WGRIND bindings are NOT
//! re-declared here: they live in the sibling FA1 module
//! `parameter` (verified/src/parameter.rs) and are imported.
//!
//! Out of this batch's scope (recorded in the FA9 notes): the
//! bavc_index_offset / bavc_max_node_depth / bavc_max_node_index /
//! pos_in_tree / vole_array_length default methods (:806-847, booked
//! FA7), decode_challenge_as_iter (:1026, needs the bavc offsets),
//! the OWF method bodies evaluate_owf / extendwitness /
//! keygen_with_rng (trusted-aes and rng stub faces, FA10 profile)
//! and the BAVC*/BavcEm type aliases (:1205-1223, pure type-level
//! bindings with no arithmetic content).
//!
//! Not mounted by src/lib.rs yet (FA2 holds lib.rs this window); this
//! file is verified through verified/fa9-driver.rs, which mounts the
//! FA1 parameter/utils panels alongside it.

use vstd::prelude::*;

use super::parameter::{
    FAEST128F_WGRIND, FAEST128S_WGRIND, FAEST192F_WGRIND, FAEST192S_WGRIND, FAEST256F_WGRIND,
    FAEST256S_WGRIND, FAESTEM128F_WGRIND, FAESTEM128S_WGRIND, FAESTEM192F_WGRIND,
    FAESTEM192S_WGRIND, FAESTEM256F_WGRIND, FAESTEM256S_WGRIND, OWF128_LAMBDA, OWF192_LAMBDA,
    OWF256_LAMBDA, TAU128F_EM_K, TAU128F_EM_TAU, TAU128F_EM_TAU0, TAU128F_EM_TAU1,
    TAU128F_EM_TOPEN, TAU128F_K, TAU128F_TAU, TAU128F_TAU0, TAU128F_TAU1, TAU128F_TOPEN,
    TAU128S_EM_K, TAU128S_EM_TAU, TAU128S_EM_TAU0, TAU128S_EM_TAU1, TAU128S_EM_TOPEN, TAU128S_K,
    TAU128S_TAU, TAU128S_TAU0, TAU128S_TAU1, TAU128S_TOPEN, TAU192F_EM_K, TAU192F_EM_TAU,
    TAU192F_EM_TAU0, TAU192F_EM_TAU1, TAU192F_EM_TOPEN, TAU192F_K, TAU192F_TAU, TAU192F_TAU0,
    TAU192F_TAU1, TAU192F_TOPEN, TAU192S_EM_K, TAU192S_EM_TAU, TAU192S_EM_TAU0,
    TAU192S_EM_TAU1, TAU192S_EM_TOPEN, TAU192S_K, TAU192S_TAU, TAU192S_TAU0, TAU192S_TAU1,
    TAU192S_TOPEN, TAU256F_EM_K, TAU256F_EM_TAU, TAU256F_EM_TAU0, TAU256F_EM_TAU1,
    TAU256F_EM_TOPEN, TAU256F_K, TAU256F_TAU, TAU256F_TAU0, TAU256F_TAU1, TAU256F_TOPEN,
    TAU256S_EM_K, TAU256S_EM_TAU, TAU256S_EM_TAU0, TAU256S_EM_TAU1, TAU256S_EM_TOPEN, TAU256S_K,
    TAU256S_TAU, TAU256S_TAU0, TAU256S_TAU1, TAU256S_TOPEN,
};

verus! {

// ===========================================================================
// Part 1: spec mirrors of the upstream typenum chains.
//
// Each mirror reproduces exactly one `type X = <chain>` binding from
// parameter.rs as arithmetic over int; the identity theorems at the
// bottom of this file pin the flat consts to these formulas row by
// row. Generic over the chain inputs so the same mirror serves all
// FAEST security levels and variation rows.
// ===========================================================================

/// Spec mirror of the SecurityParameter 2*LambdaBytes bindings
/// (`type LambdaBytesTimes2: ArraySize`, parameter.rs:121, bound as
/// `Prod<Self::LambdaBytes, U2>` at :389/:452/:521/:590/:660/:728).
pub open spec fn lambda_bytes_times2(lambda_bytes: int) -> int {
    2 * lambda_bytes
}

/// Spec mirror of the BaseParameters Chall binding
/// `type Chall = Sum<U8, Prod<U3, Self::LambdaBytes>>`
/// (parameter.rs:187/:209/:231).
pub open spec fn chall_bytes(lambda_bytes: int) -> int {
    8 + 3 * lambda_bytes
}

/// Spec mirror of the BaseParameters Chall1 binding
/// `type Chall1 = Sum<U8, Prod<U5, Self::LambdaBytes>>`
/// (parameter.rs:188/:210/:232).
pub open spec fn chall1_bytes(lambda_bytes: int) -> int {
    8 + 5 * lambda_bytes
}

/// Spec mirror of the BaseParameters VoleHasherOutputLength binding
/// `type VoleHasherOutputLength = Sum<Self::LambdaBytes, B>`
/// (parameter.rs:189/:211/:233), where B is the universal-hashing
/// padding B in BYTES (universal_hashing.rs:21-23,
/// `type BBits = U16; type B = Quot<BBits, U8>;`).
pub open spec fn vole_hasher_output_length(lambda_bytes: int, b_padding_bytes: int) -> int {
    lambda_bytes + b_padding_bytes
}

/// Spec mirror of the LHatBytes type family
/// `type LHatBytes<LBytes, LambdaBytes, B>
///     = Sum<LBytes, Sum<Prod<U3, LambdaBytes>, Quot<B, U8>>>`
/// with the upstream header comment `// l_hat = l + 3*lambda + B`
/// (parameter.rs:74-75); the OWF-side B is in bits, hence the / 8.
pub open spec fn lhat_bytes(l_bytes: int, lambda_bytes: int, b_bits: int) -> int {
    l_bytes + 3 * lambda_bytes + b_bits / 8
}

/// Spec mirror of the `type L = Prod<Self::LBytes, U8>` bindings
/// (parameter.rs:391/:454/:523/:592/:662/:730), the trait doc line
/// "Witness length for the zk proof (in bytes)" for LBytes and
/// "... (in bits)" for L (:258-261).
pub open spec fn bits_of_bytes(byte_len: int) -> int {
    8 * byte_len
}

/// Spec mirror of the Quot<Bits, U8> half of the LKe/LEnc chains
/// (`type LKeBytes = Quot<Self::LKe, U8>` at :399/:463/:532/:604/:674
/// /:742, same shape for LEncBytes; Euclidean division of a
/// multiple of 8 at every pinned row).
pub open spec fn bytes_of_bits(bit_len: int) -> int {
    bit_len / 8
}

/// Spec mirror of `type LProdLambdaBytes = Sum<Self::LambdaBytesTimes2,
/// Self::LBytes>` (parameter.rs:406/:456/:525/:594/:664/:732), the
/// trait doc line "Result of [`Self::L`] * [`Self::Lambda`] (in
/// bytes)" (:292; the row bodies sum LambdaBytesTimes2 + LBytes).
pub open spec fn lprod_lambda_bytes(lambda_bytes_times2: int, l_bytes: int) -> int {
    lambda_bytes_times2 + l_bytes
}

/// Spec mirror of `type NStBytes = Prod<Self::NSt, U4>`
/// (parameter.rs:403/:466/:536/:598/:668/:736), "Block size (in
/// 32-bit words)" -> bytes.
pub open spec fn nst_bytes(nst_words: int) -> int {
    4 * nst_words
}

/// Spec mirror of `type NStBits = Prod<Self::NStBytes, U8>`
/// (parameter.rs:404/:467/:537/:598/:669/:737), "Block size (in
/// bits)" (:286).
pub open spec fn nst_bits(nst_bytes: int) -> int {
    8 * nst_bytes
}

/// Spec mirror of the R1Times128 chains
/// `type R1Times128 = Prod<Sum<Self::R, U1>, U128>`
/// (non-EM rows :408/:471/:540/:609) and
/// `Prod<Sum<Self::R, U1>, Self::Lambda>` (EM rows :679/:747), the
/// trait doc line "Result of ([`Self::R`] + 1) * 128 (in bits)"
/// (:298). The EM rows pass Lambda as the factor, so the doc's "*128"
/// only names the non-EM product (see batch notes S-FA9-2).
pub open spec fn r1_times128_bits(rounds: int, factor: int) -> int {
    (rounds + 1) * factor
}

/// Spec mirror of `type R1Times128Bytes = Quot<Self::R1Times128, U8>`
/// (parameter.rs:409/:472/:541/:610/:680/:748), doc line "Result of
/// ([`Self::R`] + 1) * 128 (in bytes)" (:294).
pub open spec fn r1_times128_bytes(rounds: int, factor: int) -> int {
    r1_times128_bits(rounds, factor) / 8
}

/// Spec mirror of `type LKeMinusLambda = Diff<Self::LKe, Self::Lambda>`
/// (parameter.rs:411/:474/:543/:612/:682/:750), doc line "Result of
/// [`Self::LKe`] - [`Self::Lambda`] (in bits)" (:300).
pub open spec fn lke_minus_lambda_bits(lke: int, lambda: int) -> int {
    lke - lambda
}

/// Spec mirror of `type LKeMinusLambdaBytes =
/// Quot<Self::LKeMinusLambda, U8>`
/// (parameter.rs:412/:475/:544/:613/:683/:751), doc line "Result of
/// [`Self::LKe`] - [`Self::Lambda`] (in bytes)" (:301).
pub open spec fn lke_minus_lambda_bytes(lke: int, lambda: int) -> int {
    lke_minus_lambda_bits(lke, lambda) / 8
}

/// Spec mirror of the SecretKey size relation the upstream test
/// asserts (`O::SK::USIZE == O::InputSize::USIZE +
/// O::LambdaBytes::USIZE`, parameter.rs:1241).
pub open spec fn sk_size(input_size: int, lambda_bytes: int) -> int {
    input_size + lambda_bytes
}

/// Spec mirror of the PublicKey size relation the upstream test
/// asserts (`O::PK::USIZE == O::InputSize::USIZE +
/// O::OutputSize::USIZE`, parameter.rs:1242).
pub open spec fn pk_size(input_size: int, output_size: int) -> int {
    input_size + output_size
}

/// Spec mirror of the tau_config identity the upstream test asserts
/// over every FAESTParameters row
/// (`Lambda == Tau1*K + Tau0*(K-1) + WGRIND`,
/// parameter.rs:1277-1286).
pub open spec fn tau_config_lambda(tau1: int, k: int, tau0: int, wgrind: int) -> int {
    tau1 * k + tau0 * (k - 1) + wgrind
}

/// Spec mirror of get_decom_size
/// (parameter.rs:1014-1023: NLeafCommit * LambdaBytes * Tau, the
/// `// coms` term, plus Topen * LambdaBytes, the `// nodes` term).
pub open spec fn decom_size(
    n_leaf_commit: int,
    lambda_bytes: int,
    tau: int,
    topen: int,
) -> int {
    n_leaf_commit * lambda_bytes * tau + topen * lambda_bytes
}

// ===========================================================================
// Part 2: the universal padding B.
//
// Origin Rust (universal_hashing.rs:21-23):
//   type BBits = U16;
//   pub(crate) type B = Quot<BBits, U8>;
// The BaseParameters VoleHasherOutputLength consumes this byte-typed
// B, while each OWFParameters row binds its own `type B = U16` IN
// BITS and LHatBytes divides by 8; the two names coincide at one
// padding of 2 bytes (see batch notes S-FA9-1).
// ===========================================================================

/// universal_hashing.rs:21 `type BBits = U16` -- the VOLE/ZK check
/// padding in bits.
pub const UNIVERSAL_B_BITS: usize = 16;

/// universal_hashing.rs:23 `type B = Quot<BBits, U8>` -- the same
/// padding in bytes, consumed by VoleHasherOutputLength.
pub const UNIVERSAL_B_BYTES: usize = 2;

// ===========================================================================
// Part 3: BaseParameters rows (one per security level).
//
// Upstream doc lines (trait BaseParameters, parameter.rs:101-124,
// quoted verbatim per member):
//   Field    -- "The field that is of size `2^λ` which is defined as
//                [`Self::Lambda`]"
//   ZKHasher -- "Hasher implementation of `ZKHash`"
//   VoleHasher -- "Hasher implementation of `VOLEHash`"
//   RandomOracle -- "Associated random oracle"
//   PRG      -- "Associated PRG"
//   Lambda   -- "Security parameter (in bits)"
//   LambdaBytes -- "Security parameter (in bytes)"
//   LambdaBytesTimes2 -- "Two times the security parameter (in bytes)"
// The Field/ZKHasher/VoleHasher/RandomOracle/PRG bindings carry no
// arithmetic (marker types; e.g. `type PRG = PRG128`, :181, binds the
/// FA4 PRG wrapper whose KeySize is this row's LambdaBytes); only
/// the numeric members are pinned here as consts. Lambda itself is
/// the FA1 pin (OWF128_LAMBDA/OWF192_LAMBDA/OWF256_LAMBDA in the
/// sibling parameter module).
// ===========================================================================

/// `impl BaseParameters for BaseParams128<F>` (parameter.rs:173-190):
/// LambdaBytes = U16 (:184), LambdaBytesTimes2 = U32 (:185),
/// Chall = Sum<U8, Prod<U3, U16>> (:187), Chall1 = Sum<U8,
/// Prod<U5, U16>> (:188), VoleHasherOutputLength = Sum<U16, B>
/// (:189). Serves OWF128 and OWF128EM.
pub const BASE128_LAMBDA_BYTES: usize = 16;
pub const BASE128_LAMBDA_BYTES_TIMES2: usize = 32;
pub const BASE128_CHALL: usize = 56;
pub const BASE128_CHALL1: usize = 88;
pub const BASE128_VOLE_HASHER_OUTPUT_LENGTH: usize = 18;

/// `impl BaseParameters for BaseParams192<F>` (parameter.rs:195-212):
/// LambdaBytes = U24 (:206), LambdaBytesTimes2 = U48 (:207),
/// Chall (:209), Chall1 (:210), VoleHasherOutputLength (:211).
/// Serves OWF192 and OWF192EM.
pub const BASE192_LAMBDA_BYTES: usize = 24;
pub const BASE192_LAMBDA_BYTES_TIMES2: usize = 48;
pub const BASE192_CHALL: usize = 80;
pub const BASE192_CHALL1: usize = 128;
pub const BASE192_VOLE_HASHER_OUTPUT_LENGTH: usize = 26;

/// `impl BaseParameters for BaseParams256<F>` (parameter.rs:217-234):
/// LambdaBytes = U32 (:228), LambdaBytesTimes2 = U64 (:229),
/// Chall (:231), Chall1 (:232), VoleHasherOutputLength (:233).
/// Serves OWF256 and OWF256EM.
pub const BASE256_LAMBDA_BYTES: usize = 32;
pub const BASE256_LAMBDA_BYTES_TIMES2: usize = 64;
pub const BASE256_CHALL: usize = 104;
pub const BASE256_CHALL1: usize = 168;
pub const BASE256_VOLE_HASHER_OUTPUT_LENGTH: usize = 34;

// ===========================================================================
// Part 4: OWFParameters rows.
//
// Upstream doc lines (trait OWFParameters, parameter.rs:236-303,
// quoted verbatim per member):
//   SK  -- "Length of secret key (in bytes)"
//   PK  -- "Length of public key (in bytes)"
//   InputSize  -- "The input size of the OWF (in bytes)"
//   OutputSize -- "The output size of the OWF (in bytes)"
//   Lambda / LambdaBytes / LambdaBytesTimes2 -- "Security parameter
//     (in bits)" / "(in bytes)" / "Two times the security parameter
//     (in bytes)" (Lambda/LambdaBytes pinned by FA1; Times2 pinned in
//     Part 3 above)
//   B   -- "Extra length padding for the VOLE check" (bound U16, in
//          bits; LHatBytes divides by 8)
//   LBytes -- "Witness length for the zk proof (in bytes)"
//   L      -- "Witness length for the zk proof (in bits)"
//   LHatBytes -- "Witness length plus extra randomness for VOLE + ZK
//                 checks"
//   Beta -- "Number of message blocks"
//   NK   -- "Number of 32-bit words in key"
//   R    -- "Number of encryption rounds"
//   SKe  -- "Number of S-boxes in key schedule" (upstream spells the
//           member SKe; the const below keeps that spelling)
//   LKe / LKeBytes -- "Number of witness bits for key schedule (in
//                      bits)" / "(in bytes)"
//   LEnc / LEncBytes -- "Number of witness bits for encryption (in
//                        bits)" / "(in bytes)"
//   NSt / NStBytes / NStBits -- "Block size (in 32-bit words)" /
//     "Block size (in bytes)" / "Block size (in bits)"
//   NLeafCommit -- "Number of Lambda-bit blocks in each leaf
//                   commitment"
//   LProdLambdaBytes / R1Times128Bytes / R1Times128 /
//     LKeMinusLambdaBytes / LKeMinusLambda -- per Part 1 mirrors
//   IS_EM -- "Returns whether the OWF is used in EM mode"
// ===========================================================================

/// `impl OWFParameters for OWF128<F>` (parameter.rs:378-436):
/// InputSize=U16 (:383), OutputSize=U16 (:384), B=U16 (:386),
/// LBytes=U160 (:390), L (:391), LHatBytes (:392), NK=U4 (:394),
/// R=U10 (:395), SKe=U40 (:396), Beta=U1 (:397), LKe=U448 (:398),
/// LEnc=U832 (:400), NSt=U4 (:402), NLeafCommit=U3 (:405),
/// LProdLambdaBytes (:406), R1Times128 (:408), LKeMinusLambda (:411),
/// SK=U32 (:414), PK=U32 (:415), IS_EM=false (:417). AES-128 mode.
pub const OWF128_INPUT_SIZE: usize = 16;
pub const OWF128_OUTPUT_SIZE: usize = 16;
pub const OWF128_B: usize = 16;
pub const OWF128_L_BYTES: usize = 160;
pub const OWF128_L: usize = 1280;
pub const OWF128_L_HAT_BYTES: usize = 210;
pub const OWF128_BETA: usize = 1;
pub const OWF128_NK: usize = 4;
pub const OWF128_R: usize = 10;
pub const OWF128_SKE: usize = 40;
pub const OWF128_LKE: usize = 448;
pub const OWF128_LKE_BYTES: usize = 56;
pub const OWF128_LENC: usize = 832;
pub const OWF128_LENC_BYTES: usize = 104;
pub const OWF128_NST: usize = 4;
pub const OWF128_NST_BYTES: usize = 16;
pub const OWF128_NST_BITS: usize = 128;
pub const OWF128_NLEAF_COMMIT: usize = 3;
pub const OWF128_LPROD_LAMBDA_BYTES: usize = 192;
pub const OWF128_R1_TIMES128: usize = 1408;
pub const OWF128_R1_TIMES128_BYTES: usize = 176;
pub const OWF128_LKE_MINUS_LAMBDA: usize = 320;
pub const OWF128_LKE_MINUS_LAMBDA_BYTES: usize = 40;
pub const OWF128_SK: usize = 32;
pub const OWF128_PK: usize = 32;
pub const OWF128_IS_EM: bool = false;

/// `impl OWFParameters for OWF192<F>` (parameter.rs:441-505):
/// InputSize=U16 (:446), OutputSize=U32 (:447), B=U16 (:449),
/// LBytes=U312 (:453), L (:454), LHatBytes (:455), NK=U6 (:458),
/// R=U12 (:459), SKe=U32 (:460), Beta=U2 (:461), LKe=U448 (:462),
/// LEnc=U1024 (:464), NSt=U4 (:466), NLeafCommit=U3 (:469),
/// LProdLambdaBytes (:456), R1Times128 (:471), LKeMinusLambda (:474),
/// SK=U40 (:477), PK=U48 (:478), IS_EM=false (:480). Two-block
/// AES-192 mode (Beta=2).
pub const OWF192_INPUT_SIZE: usize = 16;
pub const OWF192_OUTPUT_SIZE: usize = 32;
pub const OWF192_B: usize = 16;
pub const OWF192_L_BYTES: usize = 312;
pub const OWF192_L: usize = 2496;
pub const OWF192_L_HAT_BYTES: usize = 386;
pub const OWF192_BETA: usize = 2;
pub const OWF192_NK: usize = 6;
pub const OWF192_R: usize = 12;
pub const OWF192_SKE: usize = 32;
pub const OWF192_LKE: usize = 448;
pub const OWF192_LKE_BYTES: usize = 56;
pub const OWF192_LENC: usize = 1024;
pub const OWF192_LENC_BYTES: usize = 128;
pub const OWF192_NST: usize = 4;
pub const OWF192_NST_BYTES: usize = 16;
pub const OWF192_NST_BITS: usize = 128;
pub const OWF192_NLEAF_COMMIT: usize = 3;
pub const OWF192_LPROD_LAMBDA_BYTES: usize = 360;
pub const OWF192_R1_TIMES128: usize = 1664;
pub const OWF192_R1_TIMES128_BYTES: usize = 208;
pub const OWF192_LKE_MINUS_LAMBDA: usize = 256;
pub const OWF192_LKE_MINUS_LAMBDA_BYTES: usize = 32;
pub const OWF192_SK: usize = 40;
pub const OWF192_PK: usize = 48;
pub const OWF192_IS_EM: bool = false;

/// `impl OWFParameters for OWF256<F>` (parameter.rs:510-574):
/// InputSize=U16 (:515), OutputSize=U32 (:516), B=U16 (:518),
/// LBytes=U388 (:522), L (:523), LHatBytes (:524), NK=U8 (:527),
/// R=U14 (:528), SKe=U52 (:529), Beta=U2 (:530), LKe=U672 (:531),
/// LEnc=U1216 (:533, U1216 = Sum<U1024, U192> per :70-72), NSt=U4
/// (:535), NLeafCommit=U3 (:538), LProdLambdaBytes (:525),
/// R1Times128 (:540), LKeMinusLambda (:543), SK=U48 (:546),
/// PK=U48 (:547), IS_EM=false (:549). Two-block AES-256 mode.
pub const OWF256_INPUT_SIZE: usize = 16;
pub const OWF256_OUTPUT_SIZE: usize = 32;
pub const OWF256_B: usize = 16;
pub const OWF256_L_BYTES: usize = 388;
pub const OWF256_L: usize = 3104;
pub const OWF256_L_HAT_BYTES: usize = 486;
pub const OWF256_BETA: usize = 2;
pub const OWF256_NK: usize = 8;
pub const OWF256_R: usize = 14;
pub const OWF256_SKE: usize = 52;
pub const OWF256_LKE: usize = 672;
pub const OWF256_LKE_BYTES: usize = 84;
pub const OWF256_LENC: usize = 1216;
pub const OWF256_LENC_BYTES: usize = 152;
pub const OWF256_NST: usize = 4;
pub const OWF256_NST_BYTES: usize = 16;
pub const OWF256_NST_BITS: usize = 128;
pub const OWF256_NLEAF_COMMIT: usize = 3;
pub const OWF256_LPROD_LAMBDA_BYTES: usize = 452;
pub const OWF256_R1_TIMES128: usize = 1920;
pub const OWF256_R1_TIMES128_BYTES: usize = 240;
pub const OWF256_LKE_MINUS_LAMBDA: usize = 416;
pub const OWF256_LKE_MINUS_LAMBDA_BYTES: usize = 52;
pub const OWF256_SK: usize = 48;
pub const OWF256_PK: usize = 48;
pub const OWF256_IS_EM: bool = false;

/// `impl OWFParameters for OWF128EM<F>` (parameter.rs:579-640):
/// InputSize=U16 (:584), OutputSize=U16 (:585), B=U16 (:587),
/// LBytes=U120 (:591), L (:592), LHatBytes (:593), NK=U4 (:596),
/// NSt=U4 (:597), R=U10 (:600), SKe=U40 (:601), Beta=U1 (:602),
/// LKe=U128 (:603), LEnc=U832 (:605), NLeafCommit=U2 (:607),
/// LProdLambdaBytes (:594), R1Times128 (:609), LKeMinusLambda (:612),
/// SK=U32 (:615), PK=U32 (:616), IS_EM=true (:618). Even-Mansour
/// AES-128.
pub const OWF128EM_INPUT_SIZE: usize = 16;
pub const OWF128EM_OUTPUT_SIZE: usize = 16;
pub const OWF128EM_B: usize = 16;
pub const OWF128EM_L_BYTES: usize = 120;
pub const OWF128EM_L: usize = 960;
pub const OWF128EM_L_HAT_BYTES: usize = 170;
pub const OWF128EM_BETA: usize = 1;
pub const OWF128EM_NK: usize = 4;
pub const OWF128EM_R: usize = 10;
pub const OWF128EM_SKE: usize = 40;
pub const OWF128EM_LKE: usize = 128;
pub const OWF128EM_LKE_BYTES: usize = 16;
pub const OWF128EM_LENC: usize = 832;
pub const OWF128EM_LENC_BYTES: usize = 104;
pub const OWF128EM_NST: usize = 4;
pub const OWF128EM_NST_BYTES: usize = 16;
pub const OWF128EM_NST_BITS: usize = 128;
pub const OWF128EM_NLEAF_COMMIT: usize = 2;
pub const OWF128EM_LPROD_LAMBDA_BYTES: usize = 152;
pub const OWF128EM_R1_TIMES128: usize = 1408;
pub const OWF128EM_R1_TIMES128_BYTES: usize = 176;
pub const OWF128EM_LKE_MINUS_LAMBDA: usize = 0;
pub const OWF128EM_LKE_MINUS_LAMBDA_BYTES: usize = 0;
pub const OWF128EM_SK: usize = 32;
pub const OWF128EM_PK: usize = 32;
pub const OWF128EM_IS_EM: bool = true;

/// `impl OWFParameters for OWF192EM<F>` (parameter.rs:649-710):
/// InputSize=U24 (:654), OutputSize=U24 (:655), B=U16 (:657),
/// LBytes=U216 (:661), L (:662), LHatBytes (:663), NK=U6 (:666),
/// NSt=U6 (:667), R=U12 (:671), SKe=U52 (:672), Beta=U1 (:670),
/// LKe=U192 (:673), LEnc=U1536 (:675, U1536 = Sum<U1024, U512>
/// per :647), NLeafCommit=U2 (:677), LProdLambdaBytes (:664),
/// R1Times128 (:679, factor Self::Lambda), LKeMinusLambda (:682),
/// SK=U48 (:685), PK=U48 (:686), IS_EM=true (:688). Even-Mansour
/// Rijndael-192 (block = key = 24 bytes).
pub const OWF192EM_INPUT_SIZE: usize = 24;
pub const OWF192EM_OUTPUT_SIZE: usize = 24;
pub const OWF192EM_B: usize = 16;
pub const OWF192EM_L_BYTES: usize = 216;
pub const OWF192EM_L: usize = 1728;
pub const OWF192EM_L_HAT_BYTES: usize = 290;
pub const OWF192EM_BETA: usize = 1;
pub const OWF192EM_NK: usize = 6;
pub const OWF192EM_R: usize = 12;
pub const OWF192EM_SKE: usize = 52;
pub const OWF192EM_LKE: usize = 192;
pub const OWF192EM_LKE_BYTES: usize = 24;
pub const OWF192EM_LENC: usize = 1536;
pub const OWF192EM_LENC_BYTES: usize = 192;
pub const OWF192EM_NST: usize = 6;
pub const OWF192EM_NST_BYTES: usize = 24;
pub const OWF192EM_NST_BITS: usize = 192;
pub const OWF192EM_NLEAF_COMMIT: usize = 2;
pub const OWF192EM_LPROD_LAMBDA_BYTES: usize = 264;
pub const OWF192EM_R1_TIMES128: usize = 2496;
pub const OWF192EM_R1_TIMES128_BYTES: usize = 312;
pub const OWF192EM_LKE_MINUS_LAMBDA: usize = 0;
pub const OWF192EM_LKE_MINUS_LAMBDA_BYTES: usize = 0;
pub const OWF192EM_SK: usize = 48;
pub const OWF192EM_PK: usize = 48;
pub const OWF192EM_IS_EM: bool = true;

/// `impl OWFParameters for OWF256EM<F>` (parameter.rs:717-778):
/// InputSize=U32 (:722), OutputSize=U32 (:723), B=U16 (:725),
/// LBytes=U336 (:729), L (:730), LHatBytes (:731), NK=U8 (:734),
/// NSt=U8 (:735), R=U14 (:739), SKe=U60 (:740), Beta=U1 (:738),
/// LKe=U256 (:741), LEnc=U2432 (:743, U2432 = Sum<U2048, U384>
/// per :72), NLeafCommit=U2 (:745), LProdLambdaBytes (:732),
/// R1Times128 (:747, factor Self::Lambda), LKeMinusLambda (:750),
/// SK=U64 (:753), PK=U64 (:754), IS_EM=true (:756). Even-Mansour
/// Rijndael-256 (block = key = 32 bytes).
pub const OWF256EM_INPUT_SIZE: usize = 32;
pub const OWF256EM_OUTPUT_SIZE: usize = 32;
pub const OWF256EM_B: usize = 16;
pub const OWF256EM_L_BYTES: usize = 336;
pub const OWF256EM_L: usize = 2688;
pub const OWF256EM_L_HAT_BYTES: usize = 434;
pub const OWF256EM_BETA: usize = 1;
pub const OWF256EM_NK: usize = 8;
pub const OWF256EM_R: usize = 14;
pub const OWF256EM_SKE: usize = 60;
pub const OWF256EM_LKE: usize = 256;
pub const OWF256EM_LKE_BYTES: usize = 32;
pub const OWF256EM_LENC: usize = 2432;
pub const OWF256EM_LENC_BYTES: usize = 304;
pub const OWF256EM_NST: usize = 8;
pub const OWF256EM_NST_BYTES: usize = 32;
pub const OWF256EM_NST_BITS: usize = 256;
pub const OWF256EM_NLEAF_COMMIT: usize = 2;
pub const OWF256EM_LPROD_LAMBDA_BYTES: usize = 400;
pub const OWF256EM_R1_TIMES128: usize = 3840;
pub const OWF256EM_R1_TIMES128_BYTES: usize = 480;
pub const OWF256EM_LKE_MINUS_LAMBDA: usize = 0;
pub const OWF256EM_LKE_MINUS_LAMBDA_BYTES: usize = 0;
pub const OWF256EM_SK: usize = 64;
pub const OWF256EM_PK: usize = 64;
pub const OWF256EM_IS_EM: bool = true;

// ===========================================================================
// Part 5: FAESTParameters rows.
//
// Upstream doc lines (trait FAESTParameters, parameter.rs:995-1011,
// quoted verbatim):
//   OWF  -- "Associated [`OWFParameters`] type"
//   Tau  -- "Associated [`TauParameters`] type"
//   BAVC -- "Associated [`BatchVectorCommitment`] type"
//   WGRIND -- "Grinding parameter specifying how many upperbits of
//             the Fiat-Shamir challenge must be set to 0"
//   SIGNATURE_SIZE -- "Size of the signature (in bytes)"
// The WGRIND half of each row is the FA1 pin; the OWF/Tau/BAVC
// bindings are record-only (marker types; BAVC aliases at
// parameter.rs:1205-1223). SIGNATURE_SIZE has no in-file formula --
// it totals the wire layout batch FA13 owns -- so these consts are
// pinned data for that batch. The decom-size half of each row is
// computed by get_decom_size below and pinned as a const.
// Row anchors: FAEST128s :1040-1049, FAEST128f :1052-1063,
// FAEST192s :1066-1077, FAEST192f :1079-1091, FAEST256s :1093-1105,
// FAEST256f :1107-1119, FAESTEM128s :1121-1133, FAESTEM128f
// :1135-1147, FAESTEM192s :1149-1161, FAESTEM192f :1163-1175,
// FAESTEM256s :1177-1189, FAESTEM256f :1191-1203.
// ===========================================================================

pub const FAEST128S_SIGNATURE_SIZE: usize = 4506;
pub const FAEST128F_SIGNATURE_SIZE: usize = 5924;
pub const FAEST192S_SIGNATURE_SIZE: usize = 11260;
pub const FAEST192F_SIGNATURE_SIZE: usize = 14948;
pub const FAEST256S_SIGNATURE_SIZE: usize = 20696;
pub const FAEST256F_SIGNATURE_SIZE: usize = 26548;
pub const FAESTEM128S_SIGNATURE_SIZE: usize = 3906;
pub const FAESTEM128F_SIGNATURE_SIZE: usize = 5060;
pub const FAESTEM192S_SIGNATURE_SIZE: usize = 9340;
pub const FAESTEM192F_SIGNATURE_SIZE: usize = 12380;
pub const FAESTEM256S_SIGNATURE_SIZE: usize = 17984;
pub const FAESTEM256F_SIGNATURE_SIZE: usize = 23476;

// get_decom_size() at each row (decom == NLeafCommit * LambdaBytes *
// Tau + Topen * LambdaBytes; see the identity theorem
// decom_size_identity for the checked versions of every value).
pub const FAEST128S_DECOM_SIZE: usize = 2160;
pub const FAEST128F_DECOM_SIZE: usize = 2528;
pub const FAEST192S_DECOM_SIZE: usize = 5040;
pub const FAEST192F_DECOM_SIZE: usize = 5640;
pub const FAEST256S_DECOM_SIZE: usize = 9952;
pub const FAEST256F_DECOM_SIZE: usize = 10944;
pub const FAESTEM128S_DECOM_SIZE: usize = 2000;
pub const FAESTEM128F_DECOM_SIZE: usize = 2304;
pub const FAESTEM192S_DECOM_SIZE: usize = 4656;
pub const FAESTEM192F_DECOM_SIZE: usize = 5376;
pub const FAESTEM256S_DECOM_SIZE: usize = 8384;
pub const FAESTEM256F_DECOM_SIZE: usize = 9536;

// ===========================================================================
// Part 6: the get_decom_size exec twin.
// ===========================================================================

/// Origin Rust: fn get_decom_size() -> usize
///   (parameter.rs:1014-1023; FAESTParameters default method):
///     <<Self as FAESTParameters>::OWF as OWFParameters>::
///       NLeafCommit::USIZE * ...LambdaBytes::USIZE * ...Tau::USIZE
///     + ...Topen::USIZE * ...LambdaBytes::USIZE
/// (`// coms` then `// nodes` terms).
/// Twin lowers the row types to arguments; the overflow-free product
/// bounds ride requires (the upstream body relies on typenum-size
/// arguments, all far below usize::MAX at every pinned row).
pub exec fn get_decom_size(
    n_leaf_commit: usize,
    lambda_bytes: usize,
    tau: usize,
    topen: usize,
) -> (o: usize)
    requires
        n_leaf_commit * lambda_bytes <= usize::MAX,
        (n_leaf_commit * lambda_bytes) * tau <= usize::MAX,
        topen * lambda_bytes
            <= usize::MAX - (n_leaf_commit * lambda_bytes) * tau,
    ensures
        o == decom_size(
            n_leaf_commit as int,
            lambda_bytes as int,
            tau as int,
            topen as int,
        ),
{
    n_leaf_commit * lambda_bytes * tau + topen * lambda_bytes
}

// ===========================================================================
// Part 7: the constant-identity theorem set.
//
// One proof fn per upstream identity clan; each row assert pins a
// flat const to its Part-1 mirror formula (typenum chain) and, where
// the upstream test suite spells a formula directly, to that test's
// shape. Concrete constant folding only -- no recursion, no bit
// ops, no loop faces in this batch.
// ===========================================================================

/// BaseParameters rows (upstream test `lambda`, parameter.rs:1233-1237
/// shape, plus the remaining chain bindings :185/:187/:188/:189):
/// Lambda is a security level, LambdaBytes * 8 == Lambda,
/// LambdaBytesTimes2 == 2 * LambdaBytes, Chall/Chall1 per the
/// Sum/Prod chains, VoleHasherOutputLength == LambdaBytes + B.
proof fn base_level_identity() {
    // Lambda level face (upstream :1235) over the three levels.
    assert(OWF128_LAMBDA == 128 || OWF128_LAMBDA == 192 || OWF128_LAMBDA == 256);
    assert(OWF192_LAMBDA == 128 || OWF192_LAMBDA == 192 || OWF192_LAMBDA == 256);
    assert(OWF256_LAMBDA == 128 || OWF256_LAMBDA == 192 || OWF256_LAMBDA == 256);
    // LambdaBits == 8 * LambdaBytes (upstream :1236).
    assert(OWF128_LAMBDA == bits_of_bytes(BASE128_LAMBDA_BYTES as int));
    assert(OWF192_LAMBDA == bits_of_bytes(BASE192_LAMBDA_BYTES as int));
    assert(OWF256_LAMBDA == bits_of_bytes(BASE256_LAMBDA_BYTES as int));
    // LambdaBytesTimes2 == 2 * LambdaBytes.
    assert((BASE128_LAMBDA_BYTES_TIMES2 as int)
        == lambda_bytes_times2(BASE128_LAMBDA_BYTES as int));
    assert((BASE192_LAMBDA_BYTES_TIMES2 as int)
        == lambda_bytes_times2(BASE192_LAMBDA_BYTES as int));
    assert((BASE256_LAMBDA_BYTES_TIMES2 as int)
        == lambda_bytes_times2(BASE256_LAMBDA_BYTES as int));
    // Chall == 8 + 3 * LambdaBytes; Chall1 == 8 + 5 * LambdaBytes.
    assert((BASE128_CHALL as int) == chall_bytes(BASE128_LAMBDA_BYTES as int));
    assert((BASE192_CHALL as int) == chall_bytes(BASE192_LAMBDA_BYTES as int));
    assert((BASE256_CHALL as int) == chall_bytes(BASE256_LAMBDA_BYTES as int));
    assert((BASE128_CHALL1 as int) == chall1_bytes(BASE128_LAMBDA_BYTES as int));
    assert((BASE192_CHALL1 as int) == chall1_bytes(BASE192_LAMBDA_BYTES as int));
    assert((BASE256_CHALL1 as int) == chall1_bytes(BASE256_LAMBDA_BYTES as int));
    // LambdaBytesTimes2 == 2 * LambdaBytes (usize faces, straight
    // arithmetic for any consumer that stays in exec context).
    assert(BASE128_LAMBDA_BYTES_TIMES2 == 2 * BASE128_LAMBDA_BYTES);
    assert(BASE192_LAMBDA_BYTES_TIMES2 == 2 * BASE192_LAMBDA_BYTES);
    assert(BASE256_LAMBDA_BYTES_TIMES2 == 2 * BASE256_LAMBDA_BYTES);
    // VoleHasherOutputLength == LambdaBytes + B (B in bytes).
    assert((BASE128_VOLE_HASHER_OUTPUT_LENGTH as int)
        == vole_hasher_output_length(
            (BASE128_LAMBDA_BYTES as int),
            (UNIVERSAL_B_BYTES as int),
        ));
    assert((BASE192_VOLE_HASHER_OUTPUT_LENGTH as int)
        == vole_hasher_output_length(
            (BASE192_LAMBDA_BYTES as int),
            (UNIVERSAL_B_BYTES as int),
        ));
    assert((BASE256_VOLE_HASHER_OUTPUT_LENGTH as int)
        == vole_hasher_output_length(
            (BASE256_LAMBDA_BYTES as int),
            (UNIVERSAL_B_BYTES as int),
        ));
    // The OWF-side B is in bits and equals 8 * the universal B.
    assert(OWF128_B == 8 * UNIVERSAL_B_BYTES);
    assert(OWF192_B == 8 * UNIVERSAL_B_BYTES);
    assert(OWF256_B == 8 * UNIVERSAL_B_BYTES);
    assert(OWF128EM_B == 8 * UNIVERSAL_B_BYTES);
    assert(OWF192EM_B == 8 * UNIVERSAL_B_BYTES);
    assert(OWF256EM_B == 8 * UNIVERSAL_B_BYTES);
}

/// OWFParameters size relations (upstream test `pk_sk_size`,
/// parameter.rs:1239-1243): SK == InputSize + LambdaBytes and
/// PK == InputSize + OutputSize at all six rows.
proof fn pk_sk_size_identity() {
    assert((OWF128_SK as int)
        == sk_size((OWF128_INPUT_SIZE as int), (BASE128_LAMBDA_BYTES as int)));
    assert((OWF128_PK as int)
        == pk_size((OWF128_INPUT_SIZE as int), (OWF128_OUTPUT_SIZE as int)));
    assert((OWF192_SK as int)
        == sk_size((OWF192_INPUT_SIZE as int), (BASE192_LAMBDA_BYTES as int)));
    assert((OWF192_PK as int)
        == pk_size((OWF192_INPUT_SIZE as int), (OWF192_OUTPUT_SIZE as int)));
    assert((OWF256_SK as int)
        == sk_size((OWF256_INPUT_SIZE as int), (BASE256_LAMBDA_BYTES as int)));
    assert((OWF256_PK as int)
        == pk_size((OWF256_INPUT_SIZE as int), (OWF256_OUTPUT_SIZE as int)));
    assert((OWF128EM_SK as int)
        == sk_size((OWF128EM_INPUT_SIZE as int), (BASE128_LAMBDA_BYTES as int)));
    assert((OWF128EM_PK as int)
        == pk_size((OWF128EM_INPUT_SIZE as int), (OWF128EM_OUTPUT_SIZE as int)));
    assert((OWF192EM_SK as int)
        == sk_size((OWF192EM_INPUT_SIZE as int), (BASE192_LAMBDA_BYTES as int)));
    assert((OWF192EM_PK as int)
        == pk_size((OWF192EM_INPUT_SIZE as int), (OWF192EM_OUTPUT_SIZE as int)));
    assert((OWF256EM_SK as int)
        == sk_size((OWF256EM_INPUT_SIZE as int), (BASE256_LAMBDA_BYTES as int)));
    assert((OWF256EM_PK as int)
        == pk_size((OWF256EM_INPUT_SIZE as int), (OWF256EM_OUTPUT_SIZE as int)));
}

/// Witness-length relations (upstream test `owf_parameters`,
/// parameter.rs:1245-1252): LKe and LEnc are whole bytes, L is whole
/// bits, LBytes * 8 == L, and the Quot mirrors check LKeBytes/LEncBytes.
proof fn owf_parameters_identity() {
    assert(OWF128_LKE % 8 == 0);
    assert(OWF128_LENC % 8 == 0);
    assert(OWF128_L % 8 == 0);
    assert((OWF128_L as int) == bits_of_bytes(OWF128_L_BYTES as int));
    assert((OWF128_LKE_BYTES as int) == bytes_of_bits(OWF128_LKE as int));
    assert((OWF128_LENC_BYTES as int) == bytes_of_bits(OWF128_LENC as int));

    assert(OWF192_LKE % 8 == 0);
    assert(OWF192_LENC % 8 == 0);
    assert(OWF192_L % 8 == 0);
    assert((OWF192_L as int) == bits_of_bytes(OWF192_L_BYTES as int));
    assert((OWF192_LKE_BYTES as int) == bytes_of_bits(OWF192_LKE as int));
    assert((OWF192_LENC_BYTES as int) == bytes_of_bits(OWF192_LENC as int));

    assert(OWF256_LKE % 8 == 0);
    assert(OWF256_LENC % 8 == 0);
    assert(OWF256_L % 8 == 0);
    assert((OWF256_L as int) == bits_of_bytes(OWF256_L_BYTES as int));
    assert((OWF256_LKE_BYTES as int) == bytes_of_bits(OWF256_LKE as int));
    assert((OWF256_LENC_BYTES as int) == bytes_of_bits(OWF256_LENC as int));

    assert(OWF128EM_LKE % 8 == 0);
    assert(OWF128EM_LENC % 8 == 0);
    assert(OWF128EM_L % 8 == 0);
    assert((OWF128EM_L as int) == bits_of_bytes(OWF128EM_L_BYTES as int));
    assert((OWF128EM_LKE_BYTES as int) == bytes_of_bits(OWF128EM_LKE as int));
    assert((OWF128EM_LENC_BYTES as int) == bytes_of_bits(OWF128EM_LENC as int));

    assert(OWF192EM_LKE % 8 == 0);
    assert(OWF192EM_LENC % 8 == 0);
    assert(OWF192EM_L % 8 == 0);
    assert((OWF192EM_L as int) == bits_of_bytes(OWF192EM_L_BYTES as int));
    assert((OWF192EM_LKE_BYTES as int) == bytes_of_bits(OWF192EM_LKE as int));
    assert((OWF192EM_LENC_BYTES as int) == bytes_of_bits(OWF192EM_LENC as int));

    assert(OWF256EM_LKE % 8 == 0);
    assert(OWF256EM_LENC % 8 == 0);
    assert(OWF256EM_L % 8 == 0);
    assert((OWF256EM_L as int) == bits_of_bytes(OWF256EM_L_BYTES as int));
    assert((OWF256EM_LKE_BYTES as int) == bytes_of_bits(OWF256EM_LKE as int));
    assert((OWF256EM_LENC_BYTES as int) == bytes_of_bits(OWF256EM_LENC as int));
}

/// LHatBytes rows (parameter.rs:74-75 family, `l_hat = l + 3*lambda
/// + B`): LHatBytes == LBytes + 3 * LambdaBytes + B/8.
proof fn lhat_identity() {
    assert((OWF128_L_HAT_BYTES as int)
        == lhat_bytes(
            (OWF128_L_BYTES as int),
            (BASE128_LAMBDA_BYTES as int),
            (OWF128_B as int),
        ));
    assert((OWF192_L_HAT_BYTES as int)
        == lhat_bytes(
            (OWF192_L_BYTES as int),
            (BASE192_LAMBDA_BYTES as int),
            (OWF192_B as int),
        ));
    assert((OWF256_L_HAT_BYTES as int)
        == lhat_bytes(
            (OWF256_L_BYTES as int),
            (BASE256_LAMBDA_BYTES as int),
            (OWF256_B as int),
        ));
    assert((OWF128EM_L_HAT_BYTES as int)
        == lhat_bytes(
            (OWF128EM_L_BYTES as int),
            (BASE128_LAMBDA_BYTES as int),
            (OWF128EM_B as int),
        ));
    assert((OWF192EM_L_HAT_BYTES as int)
        == lhat_bytes(
            (OWF192EM_L_BYTES as int),
            (BASE192_LAMBDA_BYTES as int),
            (OWF192EM_B as int),
        ));
    assert((OWF256EM_L_HAT_BYTES as int)
        == lhat_bytes(
            (OWF256EM_L_BYTES as int),
            (BASE256_LAMBDA_BYTES as int),
            (OWF256EM_B as int),
        ));
}

/// LProdLambdaBytes rows (`Sum<Self::LambdaBytesTimes2, Self::LBytes>`
/// :406/:456/:525/:594/:664/:732).
proof fn lprod_lambda_identity() {
    assert((OWF128_LPROD_LAMBDA_BYTES as int)
        == lprod_lambda_bytes(
            (BASE128_LAMBDA_BYTES_TIMES2 as int),
            (OWF128_L_BYTES as int),
        ));
    assert((OWF192_LPROD_LAMBDA_BYTES as int)
        == lprod_lambda_bytes(
            (BASE192_LAMBDA_BYTES_TIMES2 as int),
            (OWF192_L_BYTES as int),
        ));
    assert((OWF256_LPROD_LAMBDA_BYTES as int)
        == lprod_lambda_bytes(
            (BASE256_LAMBDA_BYTES_TIMES2 as int),
            (OWF256_L_BYTES as int),
        ));
    assert((OWF128EM_LPROD_LAMBDA_BYTES as int)
        == lprod_lambda_bytes(
            (BASE128_LAMBDA_BYTES_TIMES2 as int),
            (OWF128EM_L_BYTES as int),
        ));
    assert((OWF192EM_LPROD_LAMBDA_BYTES as int)
        == lprod_lambda_bytes(
            (BASE192_LAMBDA_BYTES_TIMES2 as int),
            (OWF192EM_L_BYTES as int),
        ));
    assert((OWF256EM_LPROD_LAMBDA_BYTES as int)
        == lprod_lambda_bytes(
            (BASE256_LAMBDA_BYTES_TIMES2 as int),
            (OWF256EM_L_BYTES as int),
        ));
}

/// Block-size rows and the EM input-block observation:
/// NStBytes == 4 * NSt, NStBits == 8 * NStBytes, and at every row
/// (EM and non-EM alike) InputSize == NStBytes -- the AO input is
/// exactly one block per row.
proof fn block_size_identity() {
    assert((OWF128_INPUT_SIZE as int) == nst_bytes(OWF128_NST as int));
    assert((OWF128_NST_BYTES as int) == nst_bytes(OWF128_NST as int));
    assert((OWF128_NST_BITS as int) == nst_bits(OWF128_NST_BYTES as int));

    assert((OWF192_INPUT_SIZE as int) == nst_bytes(OWF192_NST as int));
    assert((OWF192_NST_BYTES as int) == nst_bytes(OWF192_NST as int));
    assert((OWF192_NST_BITS as int) == nst_bits(OWF192_NST_BYTES as int));

    assert((OWF256_INPUT_SIZE as int) == nst_bytes(OWF256_NST as int));
    assert((OWF256_NST_BYTES as int) == nst_bytes(OWF256_NST as int));
    assert((OWF256_NST_BITS as int) == nst_bits(OWF256_NST_BYTES as int));

    assert((OWF128EM_INPUT_SIZE as int) == nst_bytes(OWF128EM_NST as int));
    assert((OWF128EM_NST_BYTES as int) == nst_bytes(OWF128EM_NST as int));
    assert((OWF128EM_NST_BITS as int) == nst_bits(OWF128EM_NST_BYTES as int));

    assert((OWF192EM_INPUT_SIZE as int) == nst_bytes(OWF192EM_NST as int));
    assert((OWF192EM_NST_BYTES as int) == nst_bytes(OWF192EM_NST as int));
    assert((OWF192EM_NST_BITS as int) == nst_bits(OWF192EM_NST_BYTES as int));

    assert((OWF256EM_INPUT_SIZE as int) == nst_bytes(OWF256EM_NST as int));
    assert((OWF256EM_NST_BYTES as int) == nst_bytes(OWF256EM_NST as int));
    assert((OWF256EM_NST_BITS as int) == nst_bits(OWF256EM_NST_BYTES as int));
}

/// R1Times128 rows: non-EM rows use factor 128 (the doc formula
/// "Result of ([Self::R] + 1) * 128", :294-299), the EM rows use
/// Self::Lambda as the factor (:679/:747 -- see notes S-FA9-2), and
/// every row's R1Times128Bytes * 8 == R1Times128.
proof fn r1_times128_identity() {
    assert((OWF128_R1_TIMES128 as int)
        == r1_times128_bits((OWF128_R as int), 128));
    assert((OWF128_R1_TIMES128_BYTES as int)
        == r1_times128_bytes((OWF128_R as int), 128));

    assert((OWF192_R1_TIMES128 as int)
        == r1_times128_bits((OWF192_R as int), 128));
    assert((OWF192_R1_TIMES128_BYTES as int)
        == r1_times128_bytes((OWF192_R as int), 128));

    assert((OWF256_R1_TIMES128 as int)
        == r1_times128_bits((OWF256_R as int), 128));
    assert((OWF256_R1_TIMES128_BYTES as int)
        == r1_times128_bytes((OWF256_R as int), 128));

    assert((OWF128EM_R1_TIMES128 as int)
        == r1_times128_bits((OWF128EM_R as int), (OWF128_LAMBDA as int)));
    assert((OWF128EM_R1_TIMES128_BYTES as int)
        == r1_times128_bytes((OWF128EM_R as int), (OWF128_LAMBDA as int)));

    assert((OWF192EM_R1_TIMES128 as int)
        == r1_times128_bits((OWF192EM_R as int), (OWF192_LAMBDA as int)));
    assert((OWF192EM_R1_TIMES128_BYTES as int)
        == r1_times128_bytes((OWF192EM_R as int), (OWF192_LAMBDA as int)));

    assert((OWF256EM_R1_TIMES128 as int)
        == r1_times128_bits((OWF256EM_R as int), (OWF256_LAMBDA as int)));
    assert((OWF256EM_R1_TIMES128_BYTES as int)
        == r1_times128_bytes((OWF256EM_R as int), (OWF256_LAMBDA as int)));
}

/// LKeMinusLambda rows plus the non-EM S-box cross-group relation:
/// every row has
/// LKeMinusLambda == LKe - Lambda and
/// LKeMinusLambdaBytes * 8 == LKeMinusLambda; the three non-EM rows
/// additionally satisfy SKe == LKeMinusLambdaBytes (the key-schedule
/// S-box count is the key-schedule witness bits beyond Lambda,
/// eight-fold), while the EM rows carry LKe == Lambda (SKe stays
/// nonzero there -- the witness.rs:30 EM-SKE deviation surface, FA13
/// scope).
proof fn lke_minus_lambda_identity() {
    assert((OWF128_LKE_MINUS_LAMBDA as int)
        == lke_minus_lambda_bits((OWF128_LKE as int), (OWF128_LAMBDA as int)));
    assert((OWF128_LKE_MINUS_LAMBDA_BYTES as int)
        == lke_minus_lambda_bytes((OWF128_LKE as int), (OWF128_LAMBDA as int)));
    assert(OWF128_LKE_MINUS_LAMBDA_BYTES == OWF128_SKE);

    assert((OWF192_LKE_MINUS_LAMBDA as int)
        == lke_minus_lambda_bits((OWF192_LKE as int), (OWF192_LAMBDA as int)));
    assert((OWF192_LKE_MINUS_LAMBDA_BYTES as int)
        == lke_minus_lambda_bytes((OWF192_LKE as int), (OWF192_LAMBDA as int)));
    assert(OWF192_LKE_MINUS_LAMBDA_BYTES == OWF192_SKE);

    assert((OWF256_LKE_MINUS_LAMBDA as int)
        == lke_minus_lambda_bits((OWF256_LKE as int), (OWF256_LAMBDA as int)));
    assert((OWF256_LKE_MINUS_LAMBDA_BYTES as int)
        == lke_minus_lambda_bytes((OWF256_LKE as int), (OWF256_LAMBDA as int)));
    assert(OWF256_LKE_MINUS_LAMBDA_BYTES == OWF256_SKE);

    assert((OWF128EM_LKE_MINUS_LAMBDA as int)
        == lke_minus_lambda_bits((OWF128EM_LKE as int), (OWF128_LAMBDA as int)));
    assert((OWF128EM_LKE_MINUS_LAMBDA_BYTES as int)
        == lke_minus_lambda_bytes((OWF128EM_LKE as int), (OWF128_LAMBDA as int)));
    assert(OWF128EM_LKE == OWF128_LAMBDA);

    assert((OWF192EM_LKE_MINUS_LAMBDA as int)
        == lke_minus_lambda_bits((OWF192EM_LKE as int), (OWF192_LAMBDA as int)));
    assert((OWF192EM_LKE_MINUS_LAMBDA_BYTES as int)
        == lke_minus_lambda_bytes((OWF192EM_LKE as int), (OWF192_LAMBDA as int)));
    assert(OWF192EM_LKE == OWF192_LAMBDA);

    assert((OWF256EM_LKE_MINUS_LAMBDA as int)
        == lke_minus_lambda_bits((OWF256EM_LKE as int), (OWF256_LAMBDA as int)));
    assert((OWF256EM_LKE_MINUS_LAMBDA_BYTES as int)
        == lke_minus_lambda_bytes((OWF256EM_LKE as int), (OWF256_LAMBDA as int)));
    assert(OWF256EM_LKE == OWF256_LAMBDA);
}

/// The tau_config trunk identity over all twelve FAEST rows
/// (upstream test parameter.rs:1277-1286, re-erected over the FA1
/// pins): Lambda == Tau1 * K + Tau0 * (K - 1) + WGRIND.
proof fn tau_config_identity() {
    // FAEST rows (non-EM).
    assert((OWF128_LAMBDA as int)
        == tau_config_lambda(
            (TAU128S_TAU1 as int),
            (TAU128S_K as int),
            (TAU128S_TAU0 as int),
            (FAEST128S_WGRIND as int),
        ));
    assert((OWF128_LAMBDA as int)
        == tau_config_lambda(
            (TAU128F_TAU1 as int),
            (TAU128F_K as int),
            (TAU128F_TAU0 as int),
            (FAEST128F_WGRIND as int),
        ));
    assert((OWF192_LAMBDA as int)
        == tau_config_lambda(
            (TAU192S_TAU1 as int),
            (TAU192S_K as int),
            (TAU192S_TAU0 as int),
            (FAEST192S_WGRIND as int),
        ));
    assert((OWF192_LAMBDA as int)
        == tau_config_lambda(
            (TAU192F_TAU1 as int),
            (TAU192F_K as int),
            (TAU192F_TAU0 as int),
            (FAEST192F_WGRIND as int),
        ));
    assert((OWF256_LAMBDA as int)
        == tau_config_lambda(
            (TAU256S_TAU1 as int),
            (TAU256S_K as int),
            (TAU256S_TAU0 as int),
            (FAEST256S_WGRIND as int),
        ));
    assert((OWF256_LAMBDA as int)
        == tau_config_lambda(
            (TAU256F_TAU1 as int),
            (TAU256F_K as int),
            (TAU256F_TAU0 as int),
            (FAEST256F_WGRIND as int),
        ));
    // FAEST-EM rows.
    assert((OWF128_LAMBDA as int)
        == tau_config_lambda(
            (TAU128S_EM_TAU1 as int),
            (TAU128S_EM_K as int),
            (TAU128S_EM_TAU0 as int),
            (FAESTEM128S_WGRIND as int),
        ));
    assert((OWF128_LAMBDA as int)
        == tau_config_lambda(
            (TAU128F_EM_TAU1 as int),
            (TAU128F_EM_K as int),
            (TAU128F_EM_TAU0 as int),
            (FAESTEM128F_WGRIND as int),
        ));
    assert((OWF192_LAMBDA as int)
        == tau_config_lambda(
            (TAU192S_EM_TAU1 as int),
            (TAU192S_EM_K as int),
            (TAU192S_EM_TAU0 as int),
            (FAESTEM192S_WGRIND as int),
        ));
    assert((OWF192_LAMBDA as int)
        == tau_config_lambda(
            (TAU192F_EM_TAU1 as int),
            (TAU192F_EM_K as int),
            (TAU192F_EM_TAU0 as int),
            (FAESTEM192F_WGRIND as int),
        ));
    assert((OWF256_LAMBDA as int)
        == tau_config_lambda(
            (TAU256S_EM_TAU1 as int),
            (TAU256S_EM_K as int),
            (TAU256S_EM_TAU0 as int),
            (FAESTEM256S_WGRIND as int),
        ));
    assert((OWF256_LAMBDA as int)
        == tau_config_lambda(
            (TAU256F_EM_TAU1 as int),
            (TAU256F_EM_K as int),
            (TAU256F_EM_TAU0 as int),
            (FAESTEM256F_WGRIND as int),
        ));
}

/// Decom sizes over all twelve FAEST rows (get_decom_size,
/// parameter.rs:1014-1023): decom == NLeafCommit * LambdaBytes * Tau
/// + Topen * LambdaBytes, pinned const == formula per row.
proof fn decom_size_identity() {
    // FAEST rows (non-EM; NLeafCommit = 3).
    assert((FAEST128S_DECOM_SIZE as int)
        == decom_size(
            (OWF128_NLEAF_COMMIT as int),
            (BASE128_LAMBDA_BYTES as int),
            (TAU128S_TAU as int),
            (TAU128S_TOPEN as int),
        ));
    assert((FAEST128F_DECOM_SIZE as int)
        == decom_size(
            (OWF128_NLEAF_COMMIT as int),
            (BASE128_LAMBDA_BYTES as int),
            (TAU128F_TAU as int),
            (TAU128F_TOPEN as int),
        ));
    assert((FAEST192S_DECOM_SIZE as int)
        == decom_size(
            (OWF192_NLEAF_COMMIT as int),
            (BASE192_LAMBDA_BYTES as int),
            (TAU192S_TAU as int),
            (TAU192S_TOPEN as int),
        ));
    assert((FAEST192F_DECOM_SIZE as int)
        == decom_size(
            (OWF192_NLEAF_COMMIT as int),
            (BASE192_LAMBDA_BYTES as int),
            (TAU192F_TAU as int),
            (TAU192F_TOPEN as int),
        ));
    assert((FAEST256S_DECOM_SIZE as int)
        == decom_size(
            (OWF256_NLEAF_COMMIT as int),
            (BASE256_LAMBDA_BYTES as int),
            (TAU256S_TAU as int),
            (TAU256S_TOPEN as int),
        ));
    assert((FAEST256F_DECOM_SIZE as int)
        == decom_size(
            (OWF256_NLEAF_COMMIT as int),
            (BASE256_LAMBDA_BYTES as int),
            (TAU256F_TAU as int),
            (TAU256F_TOPEN as int),
        ));
    // FAEST-EM rows (NLeafCommit = 2).
    assert((FAESTEM128S_DECOM_SIZE as int)
        == decom_size(
            (OWF128EM_NLEAF_COMMIT as int),
            (BASE128_LAMBDA_BYTES as int),
            (TAU128S_EM_TAU as int),
            (TAU128S_EM_TOPEN as int),
        ));
    assert((FAESTEM128F_DECOM_SIZE as int)
        == decom_size(
            (OWF128EM_NLEAF_COMMIT as int),
            (BASE128_LAMBDA_BYTES as int),
            (TAU128F_EM_TAU as int),
            (TAU128F_EM_TOPEN as int),
        ));
    assert((FAESTEM192S_DECOM_SIZE as int)
        == decom_size(
            (OWF192EM_NLEAF_COMMIT as int),
            (BASE192_LAMBDA_BYTES as int),
            (TAU192S_EM_TAU as int),
            (TAU192S_EM_TOPEN as int),
        ));
    assert((FAESTEM192F_DECOM_SIZE as int)
        == decom_size(
            (OWF192EM_NLEAF_COMMIT as int),
            (BASE192_LAMBDA_BYTES as int),
            (TAU192F_EM_TAU as int),
            (TAU192F_EM_TOPEN as int),
        ));
    assert((FAESTEM256S_DECOM_SIZE as int)
        == decom_size(
            (OWF256EM_NLEAF_COMMIT as int),
            (BASE256_LAMBDA_BYTES as int),
            (TAU256S_EM_TAU as int),
            (TAU256S_EM_TOPEN as int),
        ));
    assert((FAESTEM256F_DECOM_SIZE as int)
        == decom_size(
            (OWF256EM_NLEAF_COMMIT as int),
            (BASE256_LAMBDA_BYTES as int),
            (TAU256F_EM_TAU as int),
            (TAU256F_EM_TOPEN as int),
        ));
}

/// EM-mode flag face: the three non-EM rows are plain AES-key modes
/// and the three EM rows are Even-Mansour (upstream `const IS_EM`,
/// :417/:480/:549/:618/:688/:756).
proof fn is_em_face() {
    assert(OWF128_IS_EM == false);
    assert(OWF192_IS_EM == false);
    assert(OWF256_IS_EM == false);
    assert(OWF128EM_IS_EM == true);
    assert(OWF192EM_IS_EM == true);
    assert(OWF256EM_IS_EM == true);
}

} // verus!
