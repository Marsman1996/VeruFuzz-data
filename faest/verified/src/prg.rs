//! faest 0.3.0 -- Verus transcription of src/prg.rs, batch FA4.
//!
//! Upstream: prg.rs (228 lines) of the pinned tree (fetch.conf 9ccc68c0;
//! code/ read-only).
//!
//! Batch trust split (per the FA4 plan): the AES-CTR bodies
//! (Aes128/192/256Ctr32LE, ctr::Ctr32LE::new and apply_keystream) live in
//! external crates (`aes`, `ctr`) and stay trusted; what this twin
//! verifies is
//!   (a) add_tweak -- the wrapping tweak arithmetic that feeds the cipher
//!       state -- in full (a pure u32 little-endian wrapping add over the
//!       last four IV bytes; the carry out of the 32-bit word is discarded
//!       and never reaches IV bytes 0..12), and
//!   (b) the PRG contract face over the trusted stream: the update order
//!       (a strictly advancing consumed counter; successive reads cover
//!       disjoint consecutive stream segments), the length face (the
//!       counter advances by dst.len()), the fill semantics (apply_
//!       keystream xor form in general, pure fill exactly on
//!       zero-initialized destinations -- which closes D-FA1-1),
//!       determinism (the stream is a function of the key and the
//!       tweaked IV), and the KeySize == LambdaBytes / 2*LambdaBytes
//!       seed/digest slab pins (FA9 tower consumption).
//!
//! read_from_stream note (upstream prg.rs:35-51, the audited inline
//! contract): the upstream comment block says the function is "the safe
//! variants of this function ... but since we are always reading into
//! destinatations that are all-0, we can just call apply_keystream"
//! (typos upstream). apply_keystream XORs the keystream into dst, so the
//! fast path equals a pure fill only under that all-0 assumption. The
//! twin keeps the general xor semantics as the read contract and derives
//! the zero-dst fill form as a checked face (read_zero_init +
//! prg_contract_faces); every current upstream PRG::read call site was
//! audited to pass a zero-initialized destination (vole.rs:139-140 via
//! vec![Box::default()]/Array::default, bavc.rs:143-145/193-195 over the
//! vec![Array::default(); 2L-1] key array, and the read_into sites
//! bavc.rs:107/125 through FA1's zero-initializing read_into default
//! method) -- the assumption holds at all call sites, so the conditional
//! is record-only (S-FA4-2 in the batch notes).
//!
//! Naming/shape adaptations (Origin-noted at each item):
//!   - hybrid_array::Array<u8, N> lowers to the fixed [u8; N] form (the
//!     FA1 trusted-representation decision; held for IV and key slabs).
//!   - upstream `type KeySize: ArraySize` (associated type) lowers to an
//!     associated `const KEYBYTES: usize` (probe1: this build rejects
//!     generic const operations on `Self`, so a typed
//!     `[u8; Self::KEYBYTES]` parameter is unavailable at the trait
//!     level; the trait method therefore pins the slice length by
//!     requires -- the array-typed face lives on the inherent new_prg).
//!   - upstream `struct PRG128(Aes128Ctr32LE)` etc. lower to one
//!     const-generic carrier PRG<KEYBYTES> holding the contract view
//!     (key, tweaked IV, consumed counter); the trusted cipher state
//!     stays inside the prg_byte oracle.
//!   - the upstream KATs (prg.rs test mod) are 232-byte AES-CTR outputs
//!     over the trusted core and are not reproducible in this profile;
//!     the add_tweak-reachable half of each vector (the (iv, tweak)
//!     pair -- all three upstream tests carry out of the 32-bit word)
//!     is asserted below in add_tweak_kat, together with synthetic
//!     full-carry-chain and wraparound cases.
//!   - read_into (the FA1 Reader default method) stays interface-only:
//!     the trait default body carries no contract at trait level, so
//!     the fill face is stated and checked on the concrete carrier
//!     (read / read_zero_init), where every current downstream consumer
//!     reaches it; nothing in this batch claims the generic path.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::seq::Seq;

use vstd::arithmetic::div_mod::lemma_div_denominator;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

use super::parameter_tower::{
    BASE128_LAMBDA_BYTES, BASE128_LAMBDA_BYTES_TIMES2, BASE192_LAMBDA_BYTES,
    BASE192_LAMBDA_BYTES_TIMES2, BASE256_LAMBDA_BYTES, BASE256_LAMBDA_BYTES_TIMES2,
};
use super::utils::Reader;

verus! {

// ==================================================================
// IV / tweak aliases (upstream prg.rs:20-25)
// ==================================================================

/// Origin Rust: /// Size of the IV
/// pub(crate) type IVSize = U16; (prg.rs:20-21; the hybrid_array
/// typenum U16 lowers to the literal 16 per the FA1
/// trusted-representation decision; exposed as a const so downstream
/// specs can avoid the literal).
pub const IV_SIZE: usize = 16;

/// Origin Rust: /// IV of the PRG
/// pub(crate) type IV = Array<u8, IVSize>; (prg.rs:22-23)
pub type IV = [u8; IV_SIZE];

/// Origin Rust: /// TWEAK of the PRG
/// pub(crate) type Twk = u32; (prg.rs:25)
pub type Twk = u32;

// ==================================================================
// Wrapping tweak arithmetic (upstream prg.rs:27-33)
// ==================================================================

/// Little-endian u32 view of the last four IV bytes (spec model); the
/// add_tweak arithmetic operates exactly on this word (upstream
/// u32::from_le_bytes over iv[12..16], prg.rs:30).
pub open spec fn le32_tail(iv: Seq<u8>) -> int
    recommends
        iv.len() == 16,
{
    (iv[12] as int) + 256 * (iv[13] as int) + 65536 * (iv[14] as int)
        + 16777216 * (iv[15] as int)
}

/// The tweaked 32-bit word: (last four IV bytes as LE u32) +~ tweak,
/// truncated modulo 2^32 (upstream wrapping_add, prg.rs:30; the wrap
/// discards the carry out of the word, so IV[0..12] is never touched).
pub open spec fn tweaked_word(iv: Seq<u8>, twk: int) -> int
    recommends
        iv.len() == 16,
{
    (le32_tail(iv) + twk) % 4294967296
}

/// Spec twin of add_tweak: bytes 0..12 unchanged, bytes 12..16 the base
/// 256 digits of the wrapped word (upstream to_le_bytes/
/// copy_from_slice, prg.rs:31).
pub open spec fn add_tweak_spec(iv: Seq<u8>, twk: int) -> Seq<u8>
    recommends
        iv.len() == 16,
{
    let t = tweaked_word(iv, twk);
    Seq::new(
        16,
        |j: int| if 0 <= j < 12 {
            iv[j]
        } else if j == 12 {
            (t % 256) as u8
        } else if j == 13 {
            ((t / 256) % 256) as u8
        } else if j == 14 {
            ((t / 65536) % 256) as u8
        } else {
            ((t / 16777216) % 256) as u8
        },
    )
}

/// Origin Rust:
///     /// Add tweak to the IV
///     fn add_tweak(iv: &IV, tweak: Twk) -> Array<u8, IVSize> {
///         let mut iv = *iv;
///         let tweaked_word =
///             u32::from_le_bytes([iv[12], iv[13], iv[14], iv[15]]).wrapping_add(tweak);
///         iv[12..].copy_from_slice(&tweaked_word.to_le_bytes());
///         iv
///     }
/// (prg.rs:27-33; the by-reference receiver lowers to the FA1 by-value
/// form; from_le_bytes/wrapping_add/to_le_bytes lower to base-256
/// arithmetic -- wrapping_add is exactly (a + b) % 2^32 on the u32
/// domain, and the exec body computes it as a u64 sum plus a constant
/// modulus, which keeps the machine body free of bit operations (the
/// #FA1 probe1 u8/u16 bit-op black hole) while staying value-identical.
/// The second ensures clause is the per-index form of the first (the
/// downstream-friendly spelling); the third is the word-level
/// reassembly face.)
pub fn add_tweak(iv: IV, tweak: Twk) -> (res: IV)
    ensures
        res@ == add_tweak_spec(iv@, tweak as int),
        forall |j: int| 0 <= j < 16 ==>
            #[trigger]
            res[j] == add_tweak_spec(iv@, tweak as int)[j],
        le32_tail(res@) == tweaked_word(iv@, tweak as int),
{
    let mut res = iv;
    let b12: u64 = iv[12] as u64;
    let b13: u64 = iv[13] as u64;
    let b14: u64 = iv[14] as u64;
    let b15: u64 = iv[15] as u64;
    let w: u64 = b12 + 256 * b13 + 65536 * b14 + 16777216 * b15;
    assert((w as int) == le32_tail(iv@));
    let t64: u64 = tweak as u64;
    let s: u64 = (w + t64) % 4294967296u64;
    assert((s as int) == tweaked_word(iv@, tweak as int));
    res[12] = (s % 256u64) as u8;
    res[13] = ((s / 256u64) % 256u64) as u8;
    res[14] = ((s / 65536u64) % 256u64) as u8;
    res[15] = ((s / 16777216u64) % 256u64) as u8;
    // wrapped-word reassembly: the four machine digits re-add to st.
    // Euclidean rungs (nested div by constants via lemma_div_denominator
    // -- the #FA1-3/T4 style bridge, on int domain).
    assert(
        (res[12] as int) + 256 * (res[13] as int) + 65536 * (res[14] as int)
            + 16777216 * (res[15] as int) == (s as int)
    ) by {
        let st: int = s as int;
        assert(st >= 0);
        assert(st < 4294967296);
        lemma_fundamental_div_mod(st, 256);
        lemma_fundamental_div_mod(st / 256, 256);
        lemma_fundamental_div_mod(st / 65536, 256);
        lemma_fundamental_div_mod(st / 16777216, 256);
        lemma_div_denominator(st, 256, 256);
        lemma_div_denominator(st, 65536, 256);
        assert((st / 256int) / 256 == st / 65536);
        assert((st / 65536int) / 256 == st / 16777216);
        assert(16777216int * (st / 16777216) <= st);
        assert(st / 16777216 < 256);
        assert(st / 16777216 <= 255);
        assert(
            st % 256 + 256 * ((st / 256) % 256) + 65536 * ((st / 65536) % 256)
                + 16777216 * ((st / 16777216) % 256) == st
        );
    }
    res
}

// ==================================================================
// Trusted AES-CTR stream face (the batch trust boundary)
// ==================================================================

/// Trusted AES-CTR byte oracle: the keystream byte at stream index
/// `idx` for the PRG instance keyed by `key` with initial counter
/// block `tweaked_iv` (the add_tweak output; upstream prg.rs:69/86/102:
/// Aes{N}Ctr32LE::new(k, &add_tweak(iv, tweak))). Bodyless by design:
/// the cipher internals live in the external `aes`/`ctr` crates; the
/// verifiable contract of this batch is the call structure (which key,
/// which tweaked IV, which stream offsets), not the cipher arithmetic
/// (the tpm-core crypto.rs trusted-oracle precedent).
pub uninterp spec fn prg_byte(key: Seq<u8>, tweaked_iv: Seq<u8>, idx: int) -> u8;

// ==================================================================
// PRG carrier (upstream prg.rs:62-111): the three AES-CTR newtype
// structs lower to one const-generic carrier holding the contract view
// (key, tweaked IV, consumed); the trusted cipher state stays inside
// prg_byte.
// ==================================================================

/// Origin Rust:
///     #[cfg_attr(feature = "zeroize", derive(ZeroizeOnDrop))]
///     pub(crate) struct PRG128(Aes128Ctr32LE);
/// (prg.rs:62-63; zeroize is a feature-gated external derive, outside
/// the no-external-crypto profile). PRG192 (prg.rs:79-80) and PRG256
/// (prg.rs:96-97) are the same shape; the three tuples lower to the
/// three-field contract view below (aliases at the end of the file).
pub struct PRG<const KEYBYTES: usize> {
    /// The PRG key slab (upstream `k`; LambdaBytes-sized per level).
    pub key: [u8; KEYBYTES],
    /// The tweaked IV actually fed to the cipher constructor.
    pub tweaked_iv: IV,
    /// Number of keystream bytes consumed so far (the update order).
    pub consumed: usize,
}

impl<const KEYBYTES: usize> PRG<KEYBYTES> {
    /// Spec view: the keystream byte at absolute stream index idx.
    pub open spec fn stream(self: &Self, idx: int) -> u8 {
        prg_byte(self.key@, self.tweaked_iv@, idx)
    }

    /// Origin Rust:
    ///     fn new_prg(k: &Array<u8, Self::KeySize>, iv: &IV, tweak: Twk) -> Self {
    ///         Self(Aes128Ctr32LE::new(k, &add_tweak(iv, tweak)))
    ///     }
    /// (prg.rs:68-70; the two PRG192/PRG256 impls prg.rs:85-87/102-104
    /// are the same shape). This twin is fully verified on the
    /// reachable half: add_tweak is the verifier's obligation; the
    /// Aes*Ctr32LE::new half is trusted and captured by prg_byte
    /// keying on (key, tweaked_iv).
    pub fn new_prg(k: [u8; KEYBYTES], iv: IV, tweak: Twk) -> (ret: PRG<KEYBYTES>)
        ensures
            ret.key@ == k@,
            ret.tweaked_iv@ == add_tweak_spec(iv@, tweak as int),
            ret.consumed == 0,
    {
        PRG {
            key: k,
            tweaked_iv: add_tweak(iv, tweak),
            consumed: 0,
        }
    }

    /// Origin Rust:
    ///     fn read_from_stream<S: StreamCipher>(stream: &mut S, dst: &mut [u8]) {
    ///         /* "This is acutally the safe variants of this function.
    ///          *  But since we are always reading into destinatations
    ///          *  that are all-0, we can just call apply_keystream" */
    ///         stream.apply_keystream(dst);
    ///     }
    /// (prg.rs:35-51, reached from the three Reader::read impls
    /// prg.rs:73-77/90-94/107-111). Trusted face: verus does not check
    /// this body (external cipher), but the contract stated IS the
    /// honest apply_keystream semantics -- dst is xor'ed with the
    /// consecutive keystream bytes starting at the consumed position,
    /// and the counter advances by exactly dst.len(). The upstream
    /// all-0-dst conditional then derives as the zero case (see
    /// read_zero_init and the call-site audit note in the module doc).
    #[verifier::external_body]
    pub fn read(&mut self, dst: &mut [u8])
        ensures
            final(self).consumed == old(self).consumed + final(dst).len(),
            final(dst)@.len() == old(dst)@.len(),
            final(self).key@ == old(self).key@,
            final(self).tweaked_iv@ == old(self).tweaked_iv@,
            forall |i: int| 0 <= i < final(dst)@.len() ==>
                #[trigger]
                final(dst)[i] == (old(dst)[i] ^ prg_byte(final(self).key@, final(self).tweaked_iv@, old(self).consumed + i)) as u8,
    {
        panic!("trusted AES-CTR core (external crates aes/ctr); spec-face stub")
    }

    /// Twin-side adapter (no upstream counterpart; derived from the
    /// read_from_stream conditional comment): the zero-initialized-dst
    /// special case, where the xor semantics collapse to a pure fill.
    /// This is the D-FA1-1 fill-semantics face that FA1 deferred to
    /// this batch.
    pub fn read_zero_init(&mut self, dst: &mut [u8])
        requires
            forall |i: int| 0 <= i < dst@.len() ==> dst[i] == 0u8,
        ensures
            final(self).consumed == old(self).consumed + final(dst).len(),
            final(dst)@.len() == old(dst)@.len(),
            forall |i: int| 0 <= i < final(dst)@.len() ==>
                #[trigger]
                final(dst)[i] == prg_byte(final(self).key@, final(self).tweaked_iv@, old(self).consumed + i),
    {
        self.read(dst);
        assert forall |i: int| 0 <= i < dst@.len() implies
            #[trigger]
            dst[i] == prg_byte(self.key@, self.tweaked_iv@, old(self).consumed + i)
            by {
                assert(old(dst)[i] == 0u8);
                lemma_xor_zero_term(old(dst)[i], prg_byte(self.key@, self.tweaked_iv@, old(self).consumed + i));
            }
    }
}

/// Origin Rust:
///     #[cfg_attr(feature = "zeroize", derive(ZeroizeOnDrop))]
///     pub(crate) struct PRG192(Aes192Ctr32LE); (prg.rs:79-80)
/// PRG192 lowers to PRG<24> (KeySize U24; the FA9 LambdaBytes pin at
/// security level 192).
pub type PRG192 = PRG<24>;

/// Origin Rust:
///     #[cfg_attr(feature = "zeroize", derive(ZeroizeOnDrop))]
///     pub(crate) struct PRG256(Aes256Ctr32LE); (prg.rs:96-97)
/// PRG256 lowers to PRG<32> (KeySize U32; the FA9 LambdaBytes pin at
/// security level 256).
pub type PRG256 = PRG<32>;

/// Origin Rust:
///     #[cfg_attr(feature = "zeroize", derive(ZeroizeOnDrop))]
///     pub(crate) struct PRG128(Aes128Ctr32LE); (prg.rs:62-63)
pub type PRG128 = PRG<16>;

/// u8 fact: a zero term absorbs into xor (the T4-6 u8 bit-op blackout
/// closes via bit_vector, the FA1 lemma_mask family precedent). The
/// two-argument form is the caller-side shape: read's ensure spells the
/// keystream term as `pre_dst[i] ^ ks`, so the rewrite needed at a
/// zero-initialized call site is x == 0 ==> x ^ y == y.
pub proof fn lemma_xor_zero_term(x: u8, y: u8)
    requires
        x == 0u8,
    ensures
        (x ^ y) == y,
{
    assert((x ^ y) == y) by (bit_vector)
        requires
            x == 0u8,
    ;
}

// ==================================================================
// Reader impls (upstream prg.rs:73-77 / 90-94 / 107-111)
// ==================================================================

/// Origin Rust:
///     impl Reader for PRG128 {
///         fn read(&mut self, dst: &mut [u8]) {
///             read_from_stream(&mut self.0, dst);
///         }
///     }
/// (prg.rs:73-77; PRG192 prg.rs:90-94 and PRG256 prg.rs:107-111 are the
/// same shape). The FA1 Reader trait is interface-only (fill semantics
/// deferred to this batch as D-FA1-1); the delegation reaches the
/// spec-carrying inherent read, so every read through either name
/// satisfies the xor contract above.
impl<const KEYBYTES: usize> Reader for PRG<KEYBYTES> {
    fn read(&mut self, dst: &mut [u8]) {
        PRG::read(self, dst);
    }
}

// ==================================================================
// The PRG interface trait (upstream prg.rs:53-60)
// ==================================================================

/// Origin Rust:
///     /// Interface for the PRG
///     pub(crate) trait PseudoRandomGenerator: Sized + Reader {
///         /// Size of the PRG key
///         type KeySize: ArraySize;
///         /// Instantiate new PRG instance
///         fn new_prg(k: &Array<u8, Self::KeySize>, iv: &IV, tweak: Twk) -> Self;
///     }
/// (prg.rs:53-60; consumed by bavc.rs:60/84-89/136 and parameter.rs:115
/// `type PRG: PseudoRandomGenerator<KeySize = Self::LambdaBytes>`).
/// Shape adaptations (probe1-settled; see batch notes): KeySize lowers
/// to `const KEYBYTES` (ArraySize is the hybrid-array trusted
/// representation, and a typed [u8; Self::KEYBYTES] parameter is not
/// available at the trait level in this build -- "generic parameters
/// may not be used in const operations" -- so new_prg pins the slice
/// length by requires). The three spec views carry the contract face
/// at trait level: the bound key, the tweaked IV actually fed to the
/// cipher, and the consumed counter.
/// NOTE (FA4-5 finding, batch notes): the upstream supertrait bound
/// `Sized + Reader` is lowered to `Sized` here. This build emits
/// Reader-supertrait well-formedness axioms that destabilize the FA1
/// closed panel (utils.rs lemma_chall_bits_split) inside any shared
/// compile unit (bisect: trait decl with the Reader bound alone --
/// even with no other item -- flips that lemma's z3 search; without
/// the bound the same declaration is green; the empty-trait control
/// is green). Every concrete carrier still implements Reader (the
/// impl below per upstream prg.rs:73-77), so the typing discipline
/// of the upstream bound is preserved at the concrete level.
pub trait PseudoRandomGenerator: Sized {
    /// Size of the PRG key (upstream `type KeySize: ArraySize`).
    const KEYBYTES: usize;

    /// Spec view: the bound key slab.
    spec fn key_view(&self) -> Seq<u8>;

    /// Spec view: the tweaked IV (the add_tweak output).
    spec fn tweaked_iv_view(&self) -> Seq<u8>;

    /// Spec view: keystream bytes consumed so far.
    spec fn consumed_view(&self) -> int;

    /// Instantiate new PRG instance (upstream prg.rs:58-59).
    fn new_prg(k: &[u8], iv: &IV, tweak: Twk) -> (p: Self)
        requires
            k.len() == Self::KEYBYTES,
        ensures
            p.key_view() == k@,
            p.tweaked_iv_view() == add_tweak_spec(iv@, tweak as int),
            p.consumed_view() == 0,
    ;
}

/// Twin-side adapter: slice-to-array copy used by the trait method
/// (not an upstream item; exists because the trait face is slice-typed
/// while the array-typed constructor is const-generic).
fn copy_key_bytes<const KEYBYTES: usize>(k: &[u8]) -> (a: [u8; KEYBYTES])
    requires
        k.len() == KEYBYTES,
    ensures
        a@ == k@,
{
    let mut a = [0u8; KEYBYTES];
    let mut i: usize = 0;
    while i < KEYBYTES
        invariant
            k.len() == KEYBYTES,
            a@.len() == KEYBYTES,
            i <= KEYBYTES,
            forall |q: int| 0 <= q < i ==> a[q] == k[q],
        decreases
            KEYBYTES - i,
    {
        a[i] = k[i];
        i += 1;
    }
    a
}

/// Origin Rust: the three `impl PseudoRandomGenerator for PRG{128,192,256}`
/// blocks (prg.rs:65-71 / 82-88 / 99-105, KeySize bindings U16/U24/U32);
/// the generic carrier shares one impl; the KEYBYTES bindings are
/// pinned to the FA9 tower LambdaBytes consts in prg_keysize_pins
/// below.
impl<const KEYBYTES: usize> PseudoRandomGenerator for PRG<KEYBYTES> {
    const KEYBYTES: usize = KEYBYTES;

    open spec fn key_view(&self) -> Seq<u8> {
        self.key@
    }

    open spec fn tweaked_iv_view(&self) -> Seq<u8> {
        self.tweaked_iv@
    }

    open spec fn consumed_view(&self) -> int {
        self.consumed as int
    }

    fn new_prg(k: &[u8], iv: &IV, tweak: Twk) -> (p: Self)
    {
        // KEYBYTES == Self::KEYBYTES by the associated const binding;
        // the slice face reaches the array-typed constructor.
        assert(k.len() == KEYBYTES);
        PRG::new_prg(copy_key_bytes(k), *iv, tweak)
    }
}

// ==================================================================
// KeySize / slab pins (FA9 tower consumption; upstream
// parameter.rs:115 `type PRG: PseudoRandomGenerator<KeySize =
// Self::LambdaBytes>` and the bavc.rs:355/435
// read_into::<Self::LambdaBytesTimes2> digest slabs).
// ==================================================================

/// Key sizes of the three PRG instantiations, pinned to the FA9
/// BaseParameters LambdaBytes consts (16/24/32): the PRG KeySize IS
/// the LambdaBytes seed slab (the FAEST-v2 "SeedBytes" vocabulary,
/// which this upstream carries only as LambdaBytes-shaped slabs, per
/// the FA9 spec-side group note), and the PRG-backed digest slabs are
/// exactly 2*LambdaBytes ("DigestBytes").
proof fn prg_keysize_pins()
{
    assert(PRG128::KEYBYTES == BASE128_LAMBDA_BYTES);
    assert(PRG192::KEYBYTES == BASE192_LAMBDA_BYTES);
    assert(PRG256::KEYBYTES == BASE256_LAMBDA_BYTES);
    assert(PRG128::KEYBYTES == IV_SIZE);
    assert(BASE128_LAMBDA_BYTES_TIMES2 == 2 * BASE128_LAMBDA_BYTES);
    assert(BASE192_LAMBDA_BYTES_TIMES2 == 2 * BASE192_LAMBDA_BYTES);
    assert(BASE256_LAMBDA_BYTES_TIMES2 == 2 * BASE256_LAMBDA_BYTES);
}

// ==================================================================
// Contract faces (update order, length, determinism, xor vs fill)
// ==================================================================

/// The trusted-stream contract, machine-checked end to end on the
/// concrete carrier. Covers, in order: the D-FA1-1 fill face on a
/// zero-initialized buffer; strict update order (the second read
/// continues the stream exactly where the first ended: no overlap, no
/// gap); the length face (consumed advances by dst.len()); composition
/// plus determinism (two consecutive zero-dst reads of lengths 6 and 4
/// equal the first ten bytes of one fresh-instance read, because the
/// stream is a function of (key, tweaked IV, index)); and the general
/// xor semantics on a NON-zero destination -- the upstream fast-path
/// precondition exercised in the violating direction, where the pure
/// fill claim would be false exactly as the read_from_stream comment
/// warns.
fn prg_contract_faces()
{
    let k: [u8; 16] = [
        0x14, 0x2b, 0x05, 0x66, 0x9e, 0x21, 0xcf, 0x0b, 0x19, 0xe7, 0x4f, 0x11,
        0x88, 0x32, 0x48, 0x51,
    ];
    let iv: IV = [
        0x52, 0x24, 0x27, 0x94, 0xa5, 0x95, 0xfc, 0x1e, 0x66, 0x65, 0x45, 0x2f,
        0x76, 0x2e, 0x23, 0xb0,
    ];
    let tweak: Twk = 0x2a71f3c1;
    let tiv = add_tweak(iv, tweak);

    let mut p = PRG128::new_prg(k, iv, tweak);
    assert(p.key@ == k@);
    assert(p.tweaked_iv@ == tiv@);
    assert(p.consumed == 0);

    // D-FA1-1 fill face: zero-initialized dst, pure stream bytes.
    // (a0 is the pre-call snapshot; the read instantiation ties it to
    // the borrowed pre-state.)
    let mut a = [0u8; 6];
    let a0 = a;
    p.read(&mut a);
    assert(p.consumed == 6);
    assert forall |i: int| 0 <= i < a@.len() implies
        #[trigger]
        a[i] == prg_byte(k@, tiv@, i)
        by {
            assert(a[i] == a0[i] ^ prg_byte(p.key@, p.tweaked_iv@, 0 + i) as u8);
            assert(a0[i] == 0u8);
            lemma_xor_zero_term(a0[i], prg_byte(p.key@, p.tweaked_iv@, 0 + i));
        }

    // update order: the next read continues the stream at index 6.
    let mut b = [0u8; 4];
    let b0 = b;
    assert(p.consumed == 6);
    p.read(&mut b);
    assert(p.consumed == 10);
    assert forall |i: int| 0 <= i < b@.len() implies
        #[trigger]
        b[i] == prg_byte(k@, tiv@, 6 + i)
        by {
            assert(b[i] == b0[i] ^ prg_byte(p.key@, p.tweaked_iv@, 6 + i) as u8);
            assert(b0[i] == 0u8);
            lemma_xor_zero_term(b0[i], prg_byte(p.key@, p.tweaked_iv@, 6 + i));
        }

    // composition + determinism: a fresh instance over the same
    // (key, iv, tweak), read in one 10-byte zero buffer, produces the
    // same bytes (a[i] == c[i], b[i] == c[6+i]).
    let mut q = PRG128::new_prg(k, iv, tweak);
    assert(q.key@ == k@);
    assert(q.tweaked_iv@ == tiv@);
    assert(q.consumed == 0);
    let mut c = [0u8; 10];
    let c0 = c;
    q.read(&mut c);
    assert(q.consumed == 10);
    assert forall |i: int| 0 <= i < c@.len() implies
        #[trigger]
        c[i] == prg_byte(k@, tiv@, i)
        by {
            assert(c[i] == c0[i] ^ prg_byte(q.key@, q.tweaked_iv@, 0 + i) as u8);
            assert(c0[i] == 0u8);
            lemma_xor_zero_term(c0[i], prg_byte(q.key@, q.tweaked_iv@, 0 + i));
        }
    assert forall |i: int| 0 <= i < a@.len() implies
        #[trigger]
        a[i] == c[i]
        by {
        }
    assert forall |i: int| 0 <= i < b@.len() implies
        #[trigger]
        b[i] == c[6 + i]
        by {
        }

    // xor semantics on a NON-zero destination: the same 0xAB-filled
    // buffer reads as 0xAB xor keystream. The pure-fill reading of
    // read would be FALSE here -- exactly why upstream restricts the
    // fast path to all-0 destinations.
    let mut d = [0xABu8; 4];
    let d0 = d;
    q.read(&mut d);
    assert(q.consumed == 14);
    assert forall |i: int| 0 <= i < d@.len() implies
        #[trigger]
        d[i] == (0xABu8 ^ prg_byte(k@, tiv@, 10 + i)) as u8
        by {
            assert(d[i] == d0[i] ^ prg_byte(q.key@, q.tweaked_iv@, 10 + i) as u8);
            assert(d0[i] == 0xABu8);
        }
}

// ==================================================================
// KATs (upstream prg.rs:113-228, the reachable half)
// ==================================================================

/// The three upstream test vectors, at the add_tweak level: for each
/// (iv, tweak) pair of test_prg128/192/256 (prg.rs:123-127/160-164/
/// 198-202) the tweaked IV bytes are asserted exactly (hand-computed
/// wrapping add; all three carry out of the 32-bit word, so the
/// modulo-2^32 discard is exercised on every upstream vector). The
/// AES-CTR output halves (232 bytes each) are trusted core and stay
/// out. Two synthetic vectors complete the coverage: a full four-byte
/// carry chain with wrap discard, and the all-0xff wrap.
fn add_tweak_kat()
{
    // test_prg128 (prg.rs:119-151): iv tail [47 2d 2d d3], tweak
    // 1180718807 (= 0x466056d7):
    // 0xd32d2d47 + 0x466056d7 = 0x1_198d841e -> bytes [1e 84 8d 19]
    let iv128: IV = [
        0xd2, 0x33, 0x1c, 0x8b, 0xd9, 0x1b, 0x1e, 0x01, 0x56, 0x59, 0x09,
        0x44, 0x47, 0x2d, 0x2d, 0xd3,
    ];
    let r128 = add_tweak(iv128, 1180718807);
    proof {
        assert(iv128@.len() == 16);
        assert(iv128@[0] == 0xd2);
        assert(iv128@[2] == 0x1c);
        assert(iv128@[11] == 0x44);
        assert(iv128@[12] == 0x47);
        assert(iv128@[13] == 0x2d);
        assert(iv128@[14] == 0x2d);
        assert(iv128@[15] == 0xd3);
        assert(
            le32_tail(iv128@) == (0x47 as int + 256 * (0x2d as int) + 65536 * (0x2d as int)
                + 16777216 * (0xd3 as int))
        );
        assert(0x47int as int + 256 * (0x2d as int) + 65536 * (0x2d as int) + 16777216 * (0xd3 as int) == 3542953287);
        assert(tweaked_word(iv128@, 1180718807) == (3542953287 + 1180718807) % 4294967296);
        assert((3542953287int + 1180718807) % 4294967296 == 428704798);
        assert(428704798int % 256 == 0x1e);
        assert((428704798int / 256) % 256 == 0x84);
        assert((428704798int / 65536) % 256 == 0x8d);
        assert((428704798int / 16777216) % 256 == 0x19);
        assert(r128@[12] == add_tweak_spec(iv128@, 1180718807)[12]);
    }
    assert(r128[12] == 0x1e && r128[13] == 0x84 && r128[14] == 0x8d && r128[15] == 0x19);
    assert(r128[0] == 0xd2 && r128[11] == 0x44 && r128[2] == 0x1c);

    // test_prg192 (prg.rs:154-189): iv tail [df 92 8c 81], tweak
    // 2615172839 (= 0x9be05ee7):
    // 0x818c92df + 0x9be05ee7 = 0x1_1d6cf1c6 -> bytes [c6 f1 6c 1d]
    let iv192: IV = [
        0x06, 0x08, 0xc1, 0x2f, 0x86, 0xe8, 0xeb, 0x59, 0x47, 0x75, 0xa7,
        0x31, 0xdf, 0x92, 0x8c, 0x81,
    ];
    let r192 = add_tweak(iv192, 2615172839);
    proof {
        assert(iv192@.len() == 16);
        assert(iv192@[0] == 0x06);
        assert(iv192@[11] == 0x31);
        assert(iv192@[12] == 0xdf);
        assert(iv192@[13] == 0x92);
        assert(iv192@[14] == 0x8c);
        assert(iv192@[15] == 0x81);
        assert(
            le32_tail(iv192@) == (0xdf as int + 256 * (0x92 as int) + 65536 * (0x8c as int)
                + 16777216 * (0x81 as int))
        );
        assert(0xdf as int + 256int * (0x92 as int) + 65536 * (0x8c as int) + 16777216 * (0x81 as int) == 2173473503);
        assert(tweaked_word(iv192@, 2615172839) == (2173473503 + 2615172839) % 4294967296);
        assert((2173473503int + 2615172839) % 4294967296 == 493679046);
        assert(493679046int % 256 == 0xc6);
        assert((493679046int / 256) % 256 == 0xf1);
        assert((493679046int / 65536) % 256 == 0x6c);
        assert((493679046int / 16777216) % 256 == 0x1d);
        assert(r192@[12] == add_tweak_spec(iv192@, 2615172839)[12]);
    }
    assert(r192[12] == 0xc6 && r192[13] == 0xf1 && r192[14] == 0x6c && r192[15] == 0x1d);
    assert(r192[0] == 0x06 && r192[11] == 0x31);

    // test_prg256 (prg.rs:191-227): iv tail [b4 39 53 43], tweak
    // 4046638322 (= 0xf132ccf2):
    // 0x435339b4 + 0xf132ccf2 = 0x1_348606a6 -> bytes [a6 06 86 34]
    let iv256: IV = [
        0x15, 0x79, 0x77, 0x10, 0x74, 0xf1, 0xab, 0x33, 0x81, 0x46, 0x57,
        0xc2, 0xb4, 0x39, 0x53, 0x43,
    ];
    let r256 = add_tweak(iv256, 4046638322);
    proof {
        assert(iv256@.len() == 16);
        assert(iv256@[0] == 0x15);
        assert(iv256@[11] == 0xc2);
        assert(iv256@[12] == 0xb4);
        assert(iv256@[13] == 0x39);
        assert(iv256@[14] == 0x53);
        assert(iv256@[15] == 0x43);
        assert(
            le32_tail(iv256@) == (0xb4 as int + 256 * (0x39 as int) + 65536 * (0x53 as int)
                + 16777216 * (0x43 as int))
        );
        assert(0xb4int as int + 256 * (0x39 as int) + 65536 * (0x53 as int) + 16777216 * (0x43 as int) == 1129527732);
        assert(tweaked_word(iv256@, 4046638322) == (1129527732 + 4046638322) % 4294967296);
        assert((1129527732int + 4046638322) % 4294967296 == 881198758);
        assert(881198758int % 256 == 0xa6);
        assert((881198758int / 256) % 256 == 0x06);
        assert((881198758int / 65536) % 256 == 0x86);
        assert((881198758int / 16777216) % 256 == 0x34);
        assert(r256@[12] == add_tweak_spec(iv256@, 4046638322)[12]);
    }
    assert(r256[12] == 0xa6 && r256[13] == 0x06 && r256[14] == 0x86 && r256[15] == 0x34);
    assert(r256[0] == 0x15 && r256[11] == 0xc2);

    // synthetic: full four-byte carry chain with wrap discard --
    // tail [00 10 00 00] (0x00001000) + 0xfffff100 = 0x1_00000100
    // -> bytes [00 01 00 00]; the prefix must stay untouched.
    let ivc: IV = [
        0x33, 0x33, 0x33, 0x33, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x10, 0x00, 0x00,
    ];
    let rc = add_tweak(ivc, 0xfffff100);
    proof {
        assert(ivc@.len() == 16);
        assert(ivc@[0] == 0x33);
        assert(ivc@[3] == 0x33);
        assert(ivc@[11] == 0x00);
        assert(ivc@[12] == 0x00);
        assert(ivc@[13] == 0x10);
        assert(ivc@[14] == 0x00);
        assert(ivc@[15] == 0x00);
        assert(tweaked_word(ivc@, 0xfffff100) == (4096 + 0xfffff100) % 4294967296);
        assert((4096int + 0xfffff100) % 4294967296 == 256);
        assert(256int % 256 == 0x00);
        assert((256int / 256) % 256 == 0x01);
        assert((256int / 65536) % 256 == 0x00);
        assert((256int / 16777216) % 256 == 0x00);
        assert(rc@[12] == add_tweak_spec(ivc@, 0xfffff100)[12]);
    }
    assert(rc[12] == 0x00 && rc[13] == 0x01 && rc[14] == 0x00 && rc[15] == 0x00);
    assert(rc[0] == 0x33 && rc[3] == 0x33 && rc[11] == 0x00);

    // synthetic: all-0xff tail + max tweak, pure modulo-2^32 wrap --
    // 0xffffffff + 0xffffffff = 0x1_fffffffe -> bytes [fe ff ff ff],
    // low 12 bytes untouched.
    let ivw: IV = [
        0x00, 0x01, 0x02, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0xff, 0xff, 0xff, 0xff,
    ];
    let rw = add_tweak(ivw, 0xffffffff);
    proof {
        assert(ivw@.len() == 16);
        assert(ivw@[0] == 0x00);
        assert(ivw@[3] == 0x03);
        assert(ivw@[12] == 0xff);
        assert(ivw@[13] == 0xff);
        assert(ivw@[14] == 0xff);
        assert(ivw@[15] == 0xff);
        assert(tweaked_word(ivw@, 0xffffffff) == (4294967295 + 4294967295) % 4294967296);
        assert((4294967295int + 4294967295) % 4294967296 == 4294967294);
        assert(4294967294int % 256 == 0xfe);
        assert((4294967294int / 256) % 256 == 0xff);
        assert((4294967294int / 65536) % 256 == 0xff);
        assert((4294967294int / 16777216) % 256 == 0xff);
        assert(rw@[12] == add_tweak_spec(ivw@, 0xffffffff)[12]);
    }
    assert(rw[12] == 0xfe && rw[13] == 0xff && rw[14] == 0xff && rw[15] == 0xff);
    assert(rw[0] == 0x00 && rw[3] == 0x03);
}

} // verus!
