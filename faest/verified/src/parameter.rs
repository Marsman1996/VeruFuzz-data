//! faest 0.3.0 -- Verus transcription of the consumed slice of
//! src/parameter.rs (the Tau configuration face), batch FA1.
//!
//! Origin Rust: upstream parameter.rs pins the tau traits as associated
//! types of `TauParameters` (parameter.rs:780-850) with twelve concrete
//! configurations (Tau128Small/Fast .. Tau256Small/Fast, lines 852-1000,
//! plus the six EM twins), each bound to a FAESTParameters row by
//! `type WGRIND` (lines 1041-1205). The upstream generic face
//! (`type Tau/K/Tau0/Tau1: ArraySize` + `const L` + `type Topen`) is
//! transcribed here as flat usize constants per configuration: Verus has
//! no typenum, and the batch plan (harness-inventory section 8, FA1)
//! directs concrete constants over carried trait generics. Names encode
//! the upstream marker-struct rows.
//!
//! Transcribed members (with upstream fixed offsets, parameter.rs):
//!   - tau1_offset_unchecked (parameter.rs:795): K * i
//!   - tau0_offset_unchecked (parameter.rs:800):
//!         Tau1 * K + (K - 1) * (i - Tau1)
//! plus the constant tables the challenge-decode closure consumes.
//!
//! Out of FA1 scope (later batches, per the plan): bavc_index_offset
//! (:803), bavc_max_node_depth (:813), bavc_max_node_index (:819),
//! pos_in_tree (:828, rides with FA7), vole_array_length (:830),
//! get_decom_size (:1007), decode_challenge_as_iter (:1026, FA9).

use vstd::prelude::*;

verus! {

// ===========================================================================
// TauParameters constant slice (upstream parameter.rs:780-850).
// Upstream doc lines (quoted verbatim from the trait declaration):
//   "Number of small-VOLE instances"           -> Tau
//   "Bit-length of the larger small-VOLE
//    instances (the smaller small-VOLE instances have length K-1)" -> K
//   "Number of smaller small-VOLE instances"   -> Tau0
//   "Number of larger small-VOLE instances"     -> Tau1
//   "Number of leaves of the GGM tree"          -> L
//   "Threshold for the maximum opening size of the GGM tree" -> Topen
// ===========================================================================

// --- FAEST tau configurations (non-EM, parameter.rs:852-924) --------------

/// `impl TauParameters for Tau128Small` (parameter.rs:854-861),
/// the FAEST128s row: Tau=U11, K=U12, L=22528, Tau0=U11, Tau1=U0,
/// Topen=U102.
pub const TAU128S_TAU: usize = 11;
pub const TAU128S_K: usize = 12;
pub const TAU128S_L: usize = 22528;
pub const TAU128S_TAU0: usize = 11;
pub const TAU128S_TAU1: usize = 0;
pub const TAU128S_TOPEN: usize = 102;

/// `impl TauParameters for Tau128Fast` (parameter.rs:866-873),
/// the FAEST128f row: Tau=U16, K=U8, L=3072, Tau0=U8, Tau1=U8,
/// Topen=U110. This is the concrete TAU this batch wires into the
/// challenge-decode twin (upstream type alias BAVC128Fast).
pub const TAU128F_TAU: usize = 16;
pub const TAU128F_K: usize = 8;
pub const TAU128F_L: usize = 3072;
pub const TAU128F_TAU0: usize = 8;
pub const TAU128F_TAU1: usize = 8;
pub const TAU128F_TOPEN: usize = 110;

/// `impl TauParameters for Tau192Small` (parameter.rs:878-885),
/// the FAEST192s row: Tau=U16, K=U12, L=40960, Tau0=U12, Tau1=U4,
/// Topen=U162.
pub const TAU192S_TAU: usize = 16;
pub const TAU192S_K: usize = 12;
pub const TAU192S_L: usize = 40960;
pub const TAU192S_TAU0: usize = 12;
pub const TAU192S_TAU1: usize = 4;
pub const TAU192S_TOPEN: usize = 162;

/// `impl TauParameters for Tau192Fast` (parameter.rs:890-897),
/// the FAEST192f row: Tau=U24, K=U8, L=5120, Tau0=U8, Tau1=U16,
/// Topen=U163.
pub const TAU192F_TAU: usize = 24;
pub const TAU192F_K: usize = 8;
pub const TAU192F_L: usize = 5120;
pub const TAU192F_TAU0: usize = 8;
pub const TAU192F_TAU1: usize = 16;
pub const TAU192F_TOPEN: usize = 163;

/// `impl TauParameters for Tau256Small` (parameter.rs:902-909),
/// the FAEST256s row: Tau=U22, K=U12, L=61440, Tau0=U14, Tau1=U8,
/// Topen=U245.
pub const TAU256S_TAU: usize = 22;
pub const TAU256S_K: usize = 12;
pub const TAU256S_L: usize = 61440;
pub const TAU256S_TAU0: usize = 14;
pub const TAU256S_TAU1: usize = 8;
pub const TAU256S_TOPEN: usize = 245;

/// `impl TauParameters for Tau256Fast` (parameter.rs:914-921),
/// the FAEST256f row: Tau=U32, K=U8, L=7168, Tau0=U8, Tau1=U24,
/// Topen=U246.
pub const TAU256F_TAU: usize = 32;
pub const TAU256F_K: usize = 8;
pub const TAU256F_L: usize = 7168;
pub const TAU256F_TAU0: usize = 8;
pub const TAU256F_TAU1: usize = 24;
pub const TAU256F_TOPEN: usize = 246;

// --- FAEST-EM tau configurations (parameter.rs:925-999) -------------------

/// `impl TauParameters for Tau128SmallEM` (parameter.rs:927-934):
/// Tau=U11, K=U12, L=22528, Tau0=U11, Tau1=U0, Topen=U103
/// (FAESTEM128s row).
pub const TAU128S_EM_TAU: usize = 11;
pub const TAU128S_EM_K: usize = 12;
pub const TAU128S_EM_L: usize = 22528;
pub const TAU128S_EM_TAU0: usize = 11;
pub const TAU128S_EM_TAU1: usize = 0;
pub const TAU128S_EM_TOPEN: usize = 103;

/// `impl TauParameters for Tau128FastEM` (parameter.rs:938-945):
/// Tau=U16, K=U8, L=3072, Tau0=U8, Tau1=U8, Topen=U112
/// (FAESTEM128f row).
pub const TAU128F_EM_TAU: usize = 16;
pub const TAU128F_EM_K: usize = 8;
pub const TAU128F_EM_L: usize = 3072;
pub const TAU128F_EM_TAU0: usize = 8;
pub const TAU128F_EM_TAU1: usize = 8;
pub const TAU128F_EM_TOPEN: usize = 112;

/// `impl TauParameters for Tau192SmallEM` (parameter.rs:948-955):
/// Tau=U16, K=U12, L=49152, Tau0=U8, Tau1=U8, Topen=U162
/// (FAESTEM192s row).
pub const TAU192S_EM_TAU: usize = 16;
pub const TAU192S_EM_K: usize = 12;
pub const TAU192S_EM_L: usize = 49152;
pub const TAU192S_EM_TAU0: usize = 8;
pub const TAU192S_EM_TAU1: usize = 8;
pub const TAU192S_EM_TOPEN: usize = 162;

/// `impl TauParameters for Tau192FastEM` (parameter.rs:958-965):
/// Tau=U24, K=U8, L=5120, Tau0=U8, Tau1=U16, Topen=U176
/// (FAESTEM192f row).
pub const TAU192F_EM_TAU: usize = 24;
pub const TAU192F_EM_K: usize = 8;
pub const TAU192F_EM_L: usize = 5120;
pub const TAU192F_EM_TAU0: usize = 8;
pub const TAU192F_EM_TAU1: usize = 16;
pub const TAU192F_EM_TOPEN: usize = 176;

/// `impl TauParameters for Tau256SmallEM` (parameter.rs:968-975):
/// Tau=U22, K=U12, L=61440, Tau0=U14, Tau1=U8, Topen=U218
/// (FAESTEM256s row).
pub const TAU256S_EM_TAU: usize = 22;
pub const TAU256S_EM_K: usize = 12;
pub const TAU256S_EM_L: usize = 61440;
pub const TAU256S_EM_TAU0: usize = 14;
pub const TAU256S_EM_TAU1: usize = 8;
pub const TAU256S_EM_TOPEN: usize = 218;

/// `impl TauParameters for Tau256FastEM` (parameter.rs:978-985):
/// Tau=U32, K=U8, L=7168, Tau0=U8, Tau1=U24, Topen=U234
/// (FAESTEM256f row).
pub const TAU256F_EM_TAU: usize = 32;
pub const TAU256F_EM_K: usize = 8;
pub const TAU256F_EM_L: usize = 7168;
pub const TAU256F_EM_TAU0: usize = 8;
pub const TAU256F_EM_TAU1: usize = 24;
pub const TAU256F_EM_TOPEN: usize = 234;

// ===========================================================================
// OWFParameters / FAESTParameters constant slice (upstream 1041-1205).
// Upstream doc line (WGRIND): "Grinding parameter specifying how many
// upperbits of the Fiat-Shamir challenge must be set to 0".
// OWF Lambda is the security parameter of the row's OWF
// (`type Lambda = U128/U192/U256`, parameter.rs:387/450/519/588/658/726).
// The binding per FAESTParameters row is transcribed as flat consts;
// SIGNATURE_SIZE rides with FA9 (the wire-format batch).
// ===========================================================================

/// Lambda of the OWF128/OWF128EM rows (parameter.rs:387, :588).
pub const OWF128_LAMBDA: usize = 128;
/// Lambda of the OWF192/OWF192EM rows (parameter.rs:450, :658).
pub const OWF192_LAMBDA: usize = 192;
/// Lambda of the OWF256/OWF256EM rows (parameter.rs:519, :726).
pub const OWF256_LAMBDA: usize = 256;

/// FAEST128sParameters (parameter.rs:1043-1051):
/// OWF=OWF128, Tau=Tau128Small, WGRIND=U7.
pub const FAEST128S_WGRIND: usize = 7;
/// FAEST128fParameters (parameter.rs:1055-1063):
/// OWF=OWF128, Tau=Tau128Fast, WGRIND=U8.
pub const FAEST128F_WGRIND: usize = 8;
/// FAEST192sParameters: OWF=OWF192, Tau=Tau192Small, WGRIND=U12.
pub const FAEST192S_WGRIND: usize = 12;
/// FAEST192fParameters: OWF=OWF192, Tau=Tau192Fast, WGRIND=U8.
pub const FAEST192F_WGRIND: usize = 8;
/// FAEST256sParameters: OWF=OWF256, Tau=Tau256Small, WGRIND=U6.
pub const FAEST256S_WGRIND: usize = 6;
/// FAEST256fParameters: OWF=OWF256, Tau=Tau256Fast, WGRIND=U8.
pub const FAEST256F_WGRIND: usize = 8;
/// FAESTEM128sParameters: OWF=OWF128EM, Tau=Tau128SmallEM, WGRIND=U7.
pub const FAESTEM128S_WGRIND: usize = 7;
/// FAESTEM128fParameters: OWF=OWF128EM, Tau=Tau128FastEM, WGRIND=U8.
pub const FAESTEM128F_WGRIND: usize = 8;
/// FAESTEM192sParameters: OWF=OWF192EM, Tau=Tau192SmallEM, WGRIND=U8.
pub const FAESTEM192S_WGRIND: usize = 8;
/// FAESTEM192fParameters: OWF=OWF192EM, Tau=Tau192FastEM, WGRIND=U8.
pub const FAESTEM192F_WGRIND: usize = 8;
/// FAESTEM256sParameters: OWF=OWF256EM, Tau=Tau256SmallEM, WGRIND=U6.
pub const FAESTEM256S_WGRIND: usize = 6;
/// FAESTEM256fParameters: OWF=OWF256EM, Tau=Tau256FastEM, WGRIND=U8.
pub const FAESTEM256F_WGRIND: usize = 8;

// ===========================================================================
// tau-offset faces (upstream default trait methods, parameter.rs:795-802).
// Upstream: `fn tau1_offset_unchecked(i: usize) -> usize { Self::K::USIZE
// * i }` and `fn tau0_offset_unchecked(i: usize) -> usize { Self::Tau1::
// USIZE * (Self::K::USIZE) + (Self::K::USIZE - 1) * (i - Self::Tau1::
// USIZE) }`. The "_unchecked" names carry no caller guard upstream; this
// twin turns the (small) arithmetic bounds into explicit requires.
// The spec twins state the same bodies in Euclidean ints.
// ===========================================================================

/// Spec face of tau1_offset_unchecked (upstream parameter.rs:795-797):
/// the bit offset of the i-th larger small-VOLE instance inside the
/// challenge is K * i.
pub open spec fn tau1_offset_spec(k: int, i: int) -> int {
    k * i
}

/// Spec face of tau0_offset_unchecked (upstream parameter.rs:800-802):
/// the bit offset of the i-th smaller small-VOLE instance is
/// Tau1 * K + (K - 1) * (i - Tau1).
pub open spec fn tau0_offset_spec(tau1: int, k: int, i: int) -> int {
    tau1 * k + (k - 1) * (i - tau1)
}

/// Origin Rust: #[inline] fn tau1_offset_unchecked(i: usize) -> usize {
///     Self::K::USIZE * i }   (parameter.rs:795)
/// Bit offset of the i-th larger small-VOLE challenge slice. The
/// upstream name keeps "_unchecked" for the silent release un-checked
/// product; here the product bound is an explicit requires.
#[inline]
pub exec fn tau1_offset_unchecked(k: usize, i: usize) -> (o: usize)
    requires
        k * i <= usize::MAX,
    ensures
        o == tau1_offset_spec(k as int, i as int),
{
    k * i
}

/// Origin Rust: #[inline] fn tau0_offset_unchecked(i: usize) -> usize {
///     Self::Tau1::USIZE * (Self::K::USIZE)
///         + (Self::K::USIZE - 1) * (i - Self::Tau1::USIZE) }
///   (parameter.rs:800)
/// Bit offset of the (i-th) smaller small-VOLE challenge slice; the
/// upstream body subtracts Tau1 from i unchecked -- this twin carries
/// the ordering `tau1 <= i` as requires.
#[inline]
pub exec fn tau0_offset_unchecked(tau1: usize, k: usize, i: usize) -> (o: usize)
    requires
        1 <= k,
        tau1 <= i,
        tau1 * k <= usize::MAX,
        (k - 1) * (i - tau1) <= usize::MAX - tau1 * k,
    ensures
        o == tau0_offset_spec(tau1 as int, k as int, i as int),
{
    tau1 * k + (k - 1) * (i - tau1)
}

} // verus!
