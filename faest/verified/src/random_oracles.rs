//! faest 0.3.0 -- Verus transcription of src/random_oracles.rs, batch FA5.
//!
//! Upstream: random_oracles.rs (505 lines) of the pinned tree (fetch.conf
//! 9ccc68c0; code/ read-only): the RandomOracle and Hasher traits (the
//! FAEST H0..H4 hash family over SHAKE128/SHAKE256 with single-byte
//! domain separation), the const-generic Hasher128/Hasher256 carriers
//! and their Reader wrappers, plus the sixteen inline KAT tests (eight
//! Hx inits x two SHAKE variants, :131-504).
//!
//! Batch trust split (per the FA5 plan; the FA4 notes' dependency
//! closure): the `shake` crate core -- the Keccak sponge absorb behind
//! Shake128/256::update and the XofReader squeeze behind its read --
//! stays TRUSTED, captured by two uninterpreted byte oracles keyed on
//! the full post-finish absorbed string and the stream index. What
//! this twin verifies is the whole contract face around that core:
//!   (a) absorb order: update appends its bytes at the end of the
//!       absorbed string, in call order (the FAEST paper's concat
//!       input layout; the twin's update is a verified push loop over
//!       the carrier's own Vec view, so the append contract is
//!       machine-checked, not trusted);
//!   (b) finish: the one-byte domain-separation pad (the carriers'
//!       const SEP) is appended AFTER all input (upstream
//!       self.hasher.update(&[SEP]) :92/:105) and the digest stream
//!       starts at index 0 (consumed == 0);
//!   (c) read: the SHAKE XofReader FILLS dst with the consecutive
//!       oracle bytes (pure fill -- unconditional, unlike the PRG twin's
//!       apply_keystream xor form, prg.rs:299-310; the FA4 notes judged
//!       this SHAKE face "structurally cleaner"), the consumed counter
//!       advances by exactly the destination length (the length face;
//!       disjoint consecutive stream segments), the stream is
//!       extendable past any implied output length (XOF), and equal
//!       (upstream) instances derive equal segments (determinism);
//!   (d) the slot discipline downstream lives on: the bavc H0 stream is
//!       read in LambdaBytes chunks (bavc.rs:337-339/408-410 uhash_i)
//!       and the H1 com slab is exactly LambdaBytesTimes2 (the
//!       bavc.rs:355/:423 read_into::<Self::LambdaBytesTimes2> slot;
//!       the FA4 notes' 2xKeyBytes pin, re-checked against the FA9
//!       tower consts here).
//!
//! Shape adaptations (Origin-noted at each item; probe1 in
//! out/kverus-run/FA5 settled the build limits):
//!   - the upstream associated type `type Hasher<const SEP: u8>` (a
//!     const-generic GAT, random_oracles.rs:9) crashes this build's
//!     rustc outright ("expected const for SEP/#1 but found
//!     Lifetime(SEP/#1)", binder.rs:817), and an associated const
//!     cannot instantiate a const-generic carrier anyway ("generic
//!     parameters may not be used in const operations", the FA4-2
//!     class) -- so the RandomOracle trait lowers to a binding-level
//!     marker and the h0_init..h4_init family becomes inherent impls
//!     on the two marker oracle structs, one per SHAKE variant, with
//!     the upstream SEP bindings (H0=0, H1=1, H2^0..H2^3=8..11, H3=3,
//!     H4=4) pinned in the carrier types and checked in
//!     oracle_layout_faces below;
//!   - the upstream Hasher assoc-type bound `type Reader: Reader` drops
//!     to a bare `type Reader` (the FA4-1 well-formedness hazard class:
//!     trait bounds on associated types emit trait-WF axioms that
//!     destabilize the FA1 utils panel inside a shared unit; the
//!     concrete readers still impl the FA1 Reader trait, so the typing
//!     discipline is preserved at the concrete level, the S-FA4-3
//!     precedent);
//!   - by-value receivers carry no old() in this build (builtin old
//!     takes &mut), and bodyless trait slots reject `mut self`, so the
//!     Hasher trait's finish slot is &mut and composes the inherent
//!     by-value finish (which itself never mutates its parameter; the
//!     spec references the immutable owned binding -- no old() needed),
//!     and upstream `fn finish(mut self)` loses its cosmetic `mut`;
//!   - upstream test bodies assert concrete SHAKE outputs. The SHAKE
//!     half is trusted here (uninterpreted oracle), so the twin KAT
//!     groups check the INPUT layout (the absorbed string equals the
//!     KAT input bytes followed by the SEP pad) and the OUTPUT SLOT
//!     layout (the read fills a destination of exactly the upstream
//!     output length, at the right consecutive offsets), and quote the
//!     upstream output values in comments as trusted references only.
//!     Adding the KAT bytes as axioms over the uninterpreted oracle
//!     would fabricate trust; they are honestly NOT verified, and no
//!     obligation over output VALUES is claimed by this batch.
//!
//! Downstream note for FA7 (bavc) and FA13 (faest): the generic
//! `RO::Hasher<SEP>` route is unavailable at trait level in this build;
//! route the H-family through the concrete carriers and the inherent
//! spec-bearing methods (the D-FA4-1/D-FA4-2 pattern: the array-typed
//! face lives on the inherent fn).

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::seq::Seq;

use super::parameter_tower::{
    BASE128_LAMBDA_BYTES, BASE128_LAMBDA_BYTES_TIMES2, BASE192_LAMBDA_BYTES,
    BASE192_LAMBDA_BYTES_TIMES2, BASE256_LAMBDA_BYTES, BASE256_LAMBDA_BYTES_TIMES2,
};
use super::utils::Reader;

verus! {

// ==================================================================
// Trusted SHAKE oracles (the batch trust boundary)
// ==================================================================

/// Trusted SHAKE128 byte oracle: the Xof stream byte at index idx of the
/// sponge state reached by absorbing the byte string msg (the twin keys
/// the oracle on the FULL post-finish string -- all update'd bytes plus
/// the SEP pad). Bodyless by design: the Keccak core lives in the
/// external `shake` crate (upstream finalize_xof + Shake128Reader::read,
/// random_oracles.rs:93/:74-78); what this batch verifies is the call
/// structure (which bytes, which pad, which stream offsets), not the
/// sponge arithmetic (the FA4 prg_byte / tpm crypto.rs trusted-oracle
/// precedent).
pub uninterp spec fn shake128_byte(msg: Seq<u8>, idx: int) -> u8;

/// Trusted SHAKE256 byte oracle: the same face over Shake256 (upstream
/// random_oracles.rs:106/:120-124).
pub uninterp spec fn shake256_byte(msg: Seq<u8>, idx: int) -> u8;

// ==================================================================
// The Hasher128 carrier (upstream :64-95)
// ==================================================================

/// Origin Rust:
///     /// Hasher based on `SHAKE128`
///     #[derive(Debug, Default, Clone)]
///     pub(crate) struct Hasher128<const SEP: u8> {
///         hasher: Shake128,
///     }
/// (random_oracles.rs:66-70). Twin lowering: the trusted sponge state
/// (the Shake128 field) stays inside the shake128_byte oracle; the exec
/// carrier holds the observed absorbed byte string (every update'd byte,
/// in call order -- the twin's own verified buffer, not trusted state).
/// The derived Default lowers to a manual impl over fresh() and Clone to
/// a manual copy impl below (probe-settled); the cosmetic Debug derive
/// has no contract content and is not carried (record-only).
pub struct Hasher128<const SEP: u8> {
    /// Bytes absorbed since init, in update call order (the SHAKE
    /// sponge absorbs exactly these bytes, in this order -- trusted
    /// core; the ORDER is what this batch machine-checks).
    pub buf: Vec<u8>,
}

/// Origin Rust:
///     pub(crate) struct Hasher128Reader(Shake128Reader);
/// (random_oracles.rs:72). The upstream newtype wraps the trusted
/// XofReader; the twin carries the contract view instead: the finished
/// message (post-SEP-pad) and the number of stream bytes handed out.
pub struct Hasher128Reader {
    /// The full finished absorbed string (input bytes + the SEP pad).
    pub msg: Vec<u8>,
    /// Stream bytes consumed so far (the update-order counter).
    pub consumed: usize,
}

/// Helper: copy a Vec byte-for-byte (the Clone compose below; no
/// upstream counterpart -- this exists because the twin carrier is
/// self-owned where the upstream used the trusted crate's state).
fn clone_vec128(src: &Vec<u8>) -> (o: Vec<u8>)
    ensures
        o@ == src@,
{
    let mut o: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < src.len()
        invariant
            i <= src.len(),
            o.len() == i,
            forall |j: int| 0 <= j < i ==> o[j] == src[j],
        decreases
            src.len() - i,
    {
        o.push(src[i]);
        i += 1;
    }
    o
}

impl<const SEP: u8> Hasher128<SEP> {
    /// Twin-side constructor for the derived Default (upstream
    /// #[derive(Default)] on the Shake128 field: a fresh sponge has
    /// absorbed nothing). Vec::new carries the empty-seq contract in
    /// this build; the std Default::default() route does not, so the
    /// fresh face lives here and both the manual Default impl and the
    /// h*_init family route through it.
    pub fn fresh() -> (h: Self)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher128 { buf: Vec::new() }
    }

    /// Origin Rust:
    ///     /// Hash additional bytes
    ///     fn update(&mut self, data: &[u8]) {
    ///         self.hasher.update(data);
    ///     }
    /// (random_oracles.rs:57-59, the Hasher trait body; verbatim at
    /// :86-89 for Hasher128). The trusted sponge absorb is one call;
    /// the twin verifies the OBSERVABLE order face: data lands at the
    /// end of the absorbed string, so successive updates concatenate
    /// exactly in call order. The second ensures clause is the
    /// per-index form (downstream-friendly spelling, the FA4 idiom).
    pub fn update(&mut self, data: &[u8])
        ensures
            final(self).buf@ == old(self).buf@ + data@,
            forall |j: int| old(self).buf@.len() <= j < old(self).buf@.len() + data@.len() ==>
                #[trigger]
                final(self).buf[j] == data[j - old(self).buf@.len()],
    {
        let mut i: usize = 0;
        let pre_len: usize = self.buf.len();
        while i < data.len()
            invariant
                i <= data.len(),
                pre_len == old(self).buf@.len(),
                self.buf.len() == pre_len + i,
                forall |j: int| 0 <= j < pre_len ==> self.buf[j] == old(self).buf[j],
                forall |j: int| 0 <= j < i ==> self.buf[pre_len + j] == data[j],
            decreases
                data.len() - i,
        {
            self.buf.push(data[i]);
            i += 1;
        }
        assert(self.buf@ == old(self).buf@ + data@);
    }

    /// Origin Rust:
    ///     /// Finish hashing
    ///     fn finish(mut self) -> Self::Reader {
    ///         self.hasher.update(&[SEP]);
    ///         Hasher128Reader(self.hasher.finalize_xof())
    ///     }
    /// (random_oracles.rs:60-61 verbatim; :91-94 for Hasher128). Twin
    /// lowering: the by-value consume is KEPT (self moved at the call
    /// site, upstream ownership shape), but the pad is appended over a
    /// copy instead of mutating the receiver (by-value parameters carry
    /// no old() in this build; the spec references the immutable owned
    /// binding). The contract is the FAEST layout face: the SEP pad is
    /// the LAST absorbed byte -- after every input byte -- and the
    /// digest stream starts at index 0.
    pub fn finish(self) -> (r: Hasher128Reader)
        ensures
            r.msg@ == self.buf@ + seq![SEP],
            r.msg@.len() == self.buf@.len() + 1,
            r.msg@[r.msg@.len() - 1] == SEP,
            r.consumed == 0,
    {
        let mut m: Vec<u8> = clone_vec128(&self.buf);
        m.push(SEP);
        Hasher128Reader { msg: m, consumed: 0 }
    }
}

/// Origin Rust:
///     impl Reader for Hasher128Reader {
///         fn read(&mut self, dst: &mut [u8]) {
///             self.0.read(dst);
///         }
///     }
/// (random_oracles.rs:74-78). The delegation target is the shake
/// crate's XofReader::read -- TRUSTED (the batch trust boundary). The
/// honest contract, per the inventory cut: SHAKE's read FILLS dst with
/// the consecutive stream bytes (no xor, no zero-dst conditional -- the
/// caller-observable difference from the PRG twin's apply_keystream
/// face: identical pre-states produce identical fills on all input and
/// NON-zero destinations are valid). The consumed counter advances by
/// exactly the destination length (the length face), so successive
/// reads cover disjoint consecutive stream segments, and read imposes
/// no length bound (XOF extendability -- any output length is legal,
/// which is what lets bavc read arbitrary many LambdaBytes chunks out
/// of one H0 stream and read_into arbitrary slab sizes at bavc.rs:355).
impl Hasher128Reader {
    #[verifier::external_body]
    pub fn read(&mut self, dst: &mut [u8])
        ensures
            final(self).consumed == old(self).consumed + final(dst).len(),
            final(dst)@.len() == old(dst)@.len(),
            final(self).msg@ == old(self).msg@,
            forall |i: int| 0 <= i < final(dst)@.len() ==>
                #[trigger]
                final(dst)[i] == shake128_byte(final(self).msg@, old(self).consumed + i),
    {
        panic!("trusted SHAKE128 XofReader core (shake crate); spec-face stub")
    }
}

// FA1 Reader wiring (upstream :74-78's delegation lowers here): the
// trait method routes to the spec-bearing inherent face (the D-FA4
// pattern: the array-typed/slab consumers reach the contract through
// the concrete method; the trait default read_into body stays
// interface-only there).
impl Reader for Hasher128Reader {
    fn read(&mut self, dst: &mut [u8]) {
        Hasher128Reader::read(self, dst)
    }
}

// ==================================================================
// The Hasher256 carrier (upstream :96-128)
// ==================================================================

/// Origin Rust:
///     /// Hasher based on SHAKE256
///     #[derive(Debug, Default, Clone)]
///     pub(crate) struct Hasher256<const SEP: u8> {
///         hasher: Shake256,
///     }
/// (random_oracles.rs:112-116). Same twin lowering as Hasher128: the
/// trusted Shake256 state lives inside the shake256_byte oracle; the
/// exec carrier holds the verified absorbed-string view.
pub struct Hasher256<const SEP: u8> {
    /// Bytes absorbed since init, in update call order.
    pub buf: Vec<u8>,
}

/// Origin Rust:
///     pub(crate) struct Hasher256Reader(Shake256Reader);
/// (random_oracles.rs:118). Same contract view as Hasher128Reader.
pub struct Hasher256Reader {
    /// The full finished absorbed string (input bytes + the SEP pad).
    pub msg: Vec<u8>,
    /// Stream bytes consumed so far.
    pub consumed: usize,
}

fn clone_vec256(src: &Vec<u8>) -> (o: Vec<u8>)
    ensures
        o@ == src@,
{
    let mut o: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < src.len()
        invariant
            i <= src.len(),
            o.len() == i,
            forall |j: int| 0 <= j < i ==> o[j] == src[j],
        decreases
            src.len() - i,
    {
        o.push(src[i]);
        i += 1;
    }
    o
}

impl<const SEP: u8> Hasher256<SEP> {
    /// Fresh SHAKE256 carrier (the derived-Default lowering, Hasher256
    /// counterpart of Hasher128::fresh).
    pub fn fresh() -> (h: Self)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher256 { buf: Vec::new() }
    }

    /// Origin Rust: Hasher256::update (random_oracles.rs:99-101,
    /// verbatim of the trait body :57-59). Same append face.
    pub fn update(&mut self, data: &[u8])
        ensures
            final(self).buf@ == old(self).buf@ + data@,
            forall |j: int| old(self).buf@.len() <= j < old(self).buf@.len() + data@.len() ==>
                #[trigger]
                final(self).buf[j] == data[j - old(self).buf@.len()],
    {
        let mut i: usize = 0;
        let pre_len: usize = self.buf.len();
        while i < data.len()
            invariant
                i <= data.len(),
                pre_len == old(self).buf@.len(),
                self.buf.len() == pre_len + i,
                forall |j: int| 0 <= j < pre_len ==> self.buf[j] == old(self).buf[j],
                forall |j: int| 0 <= j < i ==> self.buf[pre_len + j] == data[j],
            decreases
                data.len() - i,
        {
            self.buf.push(data[i]);
            i += 1;
        }
        assert(self.buf@ == old(self).buf@ + data@);
    }

    /// Origin Rust: Hasher256::finish (random_oracles.rs:103-107,
    /// verbatim of :60-61 + :104-107). Same pad-and-stream contract,
    /// keyed on shake256_byte.
    pub fn finish(self) -> (r: Hasher256Reader)
        ensures
            r.msg@ == self.buf@ + seq![SEP],
            r.msg@.len() == self.buf@.len() + 1,
            r.msg@[r.msg@.len() - 1] == SEP,
            r.consumed == 0,
    {
        let mut m: Vec<u8> = clone_vec256(&self.buf);
        m.push(SEP);
        Hasher256Reader { msg: m, consumed: 0 }
    }
}

/// Origin Rust:
///     impl Reader for Hasher256Reader {
///         fn read(&mut self, dst: &mut [u8]) {
///             self.0.read(dst);
///         }
///     }
/// (random_oracles.rs:120-124). Trusted SHAKE256 XofReader face; same
/// pure-fill/length/extendability contract as the 128 side.
impl Hasher256Reader {
    #[verifier::external_body]
    pub fn read(&mut self, dst: &mut [u8])
        ensures
            final(self).consumed == old(self).consumed + final(dst).len(),
            final(dst)@.len() == old(dst)@.len(),
            final(self).msg@ == old(self).msg@,
            forall |i: int| 0 <= i < final(dst)@.len() ==>
                #[trigger]
                final(dst)[i] == shake256_byte(final(self).msg@, old(self).consumed + i),
    {
        panic!("trusted SHAKE256 XofReader core (shake crate); spec-face stub")
    }
}

impl Reader for Hasher256Reader {
    fn read(&mut self, dst: &mut [u8]) {
        Hasher256Reader::read(self, dst)
    }
}

// ==================================================================
// The Hasher trait (upstream :52-62)
// ==================================================================

/// Origin Rust:
///     /// Interface for hashers associated ot the random oracles
///     pub(crate) trait Hasher {
///         /// Digest reader
///         type Reader: Reader;
///         /// Hash additional bytes
///         fn update(&mut self, data: &[u8]);
///         /// Finish hashing
///         fn finish(self) -> Self::Reader;
///     }
/// (random_oracles.rs:52-62; doc typo "associated ot" upstream).
/// Twin lowering (probe1-settled; see the module doc):
///   - `type Reader: Reader` drops to a bare `type Reader` (the FA4-1
///     WF-axiom hazard class for trait bounds in the shared unit; the
///     concrete readers still impl the FA1 Reader, preserving the
///     upstream typing at the concrete level);
///   - update carries the trait-level slice-append contract through
///     the absorbed_view/sep_view spec views (the twin's real content);
///   - the by-value finish slot cannot exist on a bodyless trait decl
///     (no `mut self` in bodyless slots; no old() for by-value), so
///     the slot is &mut and the impls compose the inherent by-value
///     finish (which carries the pad contract); the associated Reader
///     type carries no trait-level spec -- downstream consumers route
///     through the inherent methods (D-FA4 pattern).
pub trait Hasher {
    /// Digest reader (upstream `type Reader: Reader`; bound lowered,
    /// see above).
    type Reader;

    /// Spec view: bytes absorbed so far, in update call order.
    spec fn absorbed_view(&self) -> Seq<u8>;

    /// Spec view: this hasher's domain-separation byte (the const
    /// generic -- the value upstream appends at finish, :92/:105).
    spec fn sep_view(&self) -> u8;

    /// Hash additional bytes (upstream :57-59). The endpoint face:
    /// absorbed after the call equals absorbed before the call
    /// followed by data, in order.
    fn update(&mut self, data: &[u8])
        ensures
            final(self).absorbed_view() == old(self).absorbed_view() + data@;

    /// Finish hashing (upstream :60-61; &mut compose form, see above).
    fn finish(&mut self) -> (r: Self::Reader);
}

impl<const SEP: u8> Hasher for Hasher128<SEP> {
    type Reader = Hasher128Reader;

    open spec fn absorbed_view(&self) -> Seq<u8> {
        self.buf@
    }

    open spec fn sep_view(&self) -> u8 {
        SEP
    }

    fn update(&mut self, data: &[u8]) {
        Hasher128::update(self, data);
    }

    fn finish(&mut self) -> (r: Hasher128Reader) {
        let r = Hasher128::finish(self.clone128());
        // upstream finish consumes the hasher; this build cannot carry a
        // by-value bound-self trait slot, so the compose runs the inherent
        // by-value finish over the spec-checked copy below and empties the
        // carrier (the &mut view sees an empty absorbed string after
        // finish -- the consume discipline rendered on the &mut face).
        *self = Hasher128::fresh();
        r
    }
}

impl<const SEP: u8> Hasher for Hasher256<SEP> {
    type Reader = Hasher256Reader;

    open spec fn absorbed_view(&self) -> Seq<u8> {
        self.buf@
    }

    open spec fn sep_view(&self) -> u8 {
        SEP
    }

    fn update(&mut self, data: &[u8]) {
        Hasher256::update(self, data);
    }

    fn finish(&mut self) -> (r: Hasher256Reader) {
        let r = Hasher256::finish(self.clone256());
        *self = Hasher256::fresh();
        r
    }
}

// ==================================================================
// Default / Clone derivations (upstream :67 / :113 derive lines)
// ==================================================================

/// Origin Rust: `#[derive(Default)]` (random_oracles.rs:67, on the
/// Shake128 field). Manual lowering: Default routes to fresh (the std
/// Default::default() route carries no spec in this build; every spec
/// consumer -- the h*_init family -- calls fresh directly).
impl<const SEP: u8> Default for Hasher128<SEP> {
    fn default() -> Self {
        Hasher128::fresh()
    }
}

/// Origin Rust: `#[derive(Clone)]` (random_oracles.rs:67). Manual copy
/// lowering with the exact-absorb contract (upstream Clone on the
/// sponge state is the faest.rs:309 `hasher.to_owned()` route -- the
/// challenge-3 finalize keeps a clone of the mid-state hasher; the
/// twin copy preserves the absorbed byte string, so the cloned hasher
/// finishes to the SAME stream).
impl<const SEP: u8> Clone for Hasher128<SEP> {
    fn clone(&self) -> (r: Self)
        ensures
            r.buf@ == self.buf@,
    {
        Hasher128 { buf: clone_vec128(&self.buf) }
    }
}

impl<const SEP: u8> Hasher128<SEP> {
    /// Spec-checked copy used by the Hasher trait compose (the Clone
    /// lowerings above share the clone_vec128 helper).
    pub fn clone128(&self) -> (r: Self)
        ensures
            r.buf@ == self.buf@,
    {
        Hasher128 { buf: clone_vec128(&self.buf) }
    }
}

impl<const SEP: u8> Default for Hasher256<SEP> {
    fn default() -> Self {
        Hasher256::fresh()
    }
}

impl<const SEP: u8> Clone for Hasher256<SEP> {
    fn clone(&self) -> (r: Self)
        ensures
            r.buf@ == self.buf@,
    {
        Hasher256 { buf: clone_vec256(&self.buf) }
    }
}

impl<const SEP: u8> Hasher256<SEP> {
    /// Spec-checked copy used by the Hasher trait compose.
    pub fn clone256(&self) -> (r: Self)
        ensures
            r.buf@ == self.buf@,
    {
        Hasher256 { buf: clone_vec256(&self.buf) }
    }
}

// ==================================================================
// The RandomOracle trait and the two oracle carriers (upstream :8-64,
// :110,:126-128)
// ==================================================================

/// Origin Rust:
///     pub(crate) trait RandomOracle {
///         type Hasher<const SEP: u8>: Hasher + Default + Clone;
///
///         /// Create hasher for `H0`
///         fn h0_init() -> Self::Hasher<0> { Self::Hasher::default() }
///         ... h1_init :17, h2_0_init :22, h2_1_init :27, h2_2_init :30,
///             h2_3_init :35, h3_init :41, h4_init :46 (same body shape)
///     }
/// (random_oracles.rs:8-50). Twin lowering (probe1: the
/// const-generic associated type `type Hasher<const SEP: u8>` crashes
/// this build's rustc -- "expected const for SEP/#1 but found
/// Lifetime(SEP/#1)" at binder.rs:817; even without the crash, an
/// associated const cannot instantiate a const-generic carrier in this
/// build, the FA4-2 class): the trait keeps only the binding-level
/// face (parameter.rs:113 `type RandomOracle: RandomOracle`; bavc
/// generics RO: RandomOracle), and the eight init functions become
/// inherent impls on the two carrier structs below -- RandomOracleShake128
/// binds the SHAKE128 hashers, RandomOracleShake256 the SHAKE256 hashers,
/// with the upstream SEP space H0=0, H1=1, H2^0..H2^3=8..11, H3=3, H4=4
/// pinned in the return types and machine-checked in oracle_layout_faces.
pub trait RandomOracle: Sized {}

/// Origin Rust: `pub(crate) struct RandomOracleShake128 {}`
/// (random_oracles.rs:64; the empty marker struct, verbatim).
pub struct RandomOracleShake128 {}

/// Origin Rust: `pub(crate) struct RandomOracleShake256 {}`
/// (random_oracles.rs:110; verbatim).
pub struct RandomOracleShake256 {}

/// Origin Rust: `impl RandomOracle for RandomOracleShake128 { type
/// Hasher<const SEP: u8> = Hasher128<SEP>; }`
/// (random_oracles.rs:80-82). The GAT half lowers to the marker impl;
/// the family lives in the inherent impl below.
impl RandomOracle for RandomOracleShake128 {}

/// Origin Rust: `impl RandomOracle for RandomOracleShake256 { type
/// Hasher<const SEP: u8> = Hasher256<SEP>; }`
/// (random_oracles.rs:126-128).
impl RandomOracle for RandomOracleShake256 {}

/// Origin Rust (the eight RandomOracle default methods,
/// random_oracles.rs:11-49, each body `Self::Hasher::default()`),
/// lowered onto the SHAKE128 carrier as inherent functions. Each doc
/// line below quotes the upstream doc of the corresponding method.
impl RandomOracleShake128 {
    /// Origin Rust: /// Create hasher for `H0`
    ///     fn h0_init() -> Self::Hasher<0> { Self::Hasher::default() }
    /// (random_oracles.rs:11-14). H0's domain separation byte is 0x00
    /// (bound in the Hasher128<0> return type; checked below). The
    /// bavc.rs:323/:400 H0 hasher absorbs only the IV (16 bytes) and is
    /// then finished and read in LambdaBytes chunks (bavc.rs:337-339/
    /// 408-410 -- the uhash_i slots).
    pub fn h0_init() -> (h: Hasher128<0>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher128::fresh()
    }

    /// Origin Rust: /// Create hasher for `H1`
    ///     fn h1_init() -> Self::Hasher<1> { Self::Hasher::default() }
    /// (random_oracles.rs:16-19). H1's SEP is 0x01. The bavc H1 com
    /// family (bavc.rs:331/:337/:405/:414/:487/:492/:560/:565) absorbs
    /// the per-leaf commitments and the whole tree finishes into the
    /// LambdaBytesTimes2 com slab (bavc.rs:355 read_into slot).
    pub fn h1_init() -> (h: Hasher128<1>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher128::fresh()
    }

    /// Origin Rust: /// Create hasher for `H2^0`
    ///     fn h2_0_init() -> Self::Hasher<8> { Self::Hasher::default() }
    /// (random_oracles.rs:21-24). H2^0's SEP is 0x08. The faest.rs
    /// hash_mu flow (:239-249) absorbs input||output||msg under H2^0.
    pub fn h2_0_init() -> (h: Hasher128<8>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher128::fresh()
    }

    /// Origin Rust: /// Create hasher for `H2^1`
    ///     fn h2_1_init() -> Self::Hasher<9> { Self::Hasher::default() }
    /// (random_oracles.rs:26-29). H2^1's SEP is 0x09. The faest.rs
    /// first-challenge flow (:258-265) absorbs mu||hcom||c||iv under
    /// H2^1.
    pub fn h2_1_init() -> (h: Hasher128<9>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher128::fresh()
    }

    /// Origin Rust: /// Create hasher for `H2^2`
    ///     fn h2_2_init() -> Self::Hasher<10> { Self::Hasher::default() }
    /// (random_oracles.rs:31-34). H2^2's SEP is 0x0a. The faest.rs
    /// second-challenge flow (:272-281) absorbs chall1||u_t under
    /// H2^2, holding the hasher across the finalize boundary.
    pub fn h2_2_init() -> (h: Hasher128<10>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher128::fresh()
    }

    /// Origin Rust: /// Create hasher for `H2^3`
    ///     fn h2_3_init() -> Self::Hasher<11> { Self::Hasher::default() }
    /// (random_oracles.rs:36-39). H2^3's SEP is 0x0b. The faest.rs
    /// third-challenge flow (:292-325) absorbs chall2||a0_t||a1_t||a2_t
    /// (and, in the closed form, the ctr LE bytes) under H2^3.
    pub fn h2_3_init() -> (h: Hasher128<11>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher128::fresh()
    }

    /// Origin Rust: /// Create hasher for `H3`
    ///     fn h3_init() -> Self::Hasher<3> { Self::Hasher::default() }
    /// (random_oracles.rs:41-44). H3's SEP is 0x03. The faest.rs
    /// hash_r_iv flow (:251-257) absorbs key||mu||rho under H3 and
    /// reads r then iv off ONE finished stream (two successive reads).
    pub fn h3_init() -> (h: Hasher128<3>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher128::fresh()
    }

    /// Origin Rust: /// Create hasher for `H4`
    ///     fn h4_init() -> Self::Hasher<4> { Self::Hasher::default() }
    /// (random_oracles.rs:46-49). H4's SEP is 0x04. The faest.rs
    /// hash_iv flow (:259-264) absorbs iv_pre under H4 and reads the
    /// full 16-byte IV slab.
    pub fn h4_init() -> (h: Hasher128<4>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher128::fresh()
    }
}

/// Origin Rust: the SHAKE256 half of the same eight default methods
/// (upstream random_oracles.rs:11-49 have generic bodies under
/// Self::Hasher = Hasher256<SEP> via the :126-128 impl). Same SEP
/// space, SHAKE256 carriers.
impl RandomOracleShake256 {
    /// Origin Rust: /// Create hasher for `H0`
    /// (random_oracles.rs:11-14, over Hasher256).
    pub fn h0_init() -> (h: Hasher256<0>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher256::fresh()
    }

    /// Origin Rust: /// Create hasher for `H1`
    /// (random_oracles.rs:16-19, over Hasher256).
    pub fn h1_init() -> (h: Hasher256<1>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher256::fresh()
    }

    /// Origin Rust: /// Create hasher for `H2^0`
    /// (random_oracles.rs:21-24, over Hasher256).
    pub fn h2_0_init() -> (h: Hasher256<8>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher256::fresh()
    }

    /// Origin Rust: /// Create hasher for `H2^1`
    /// (random_oracles.rs:26-29, over Hasher256).
    pub fn h2_1_init() -> (h: Hasher256<9>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher256::fresh()
    }

    /// Origin Rust: /// Create hasher for `H2^2`
    /// (random_oracles.rs:31-34, over Hasher256).
    pub fn h2_2_init() -> (h: Hasher256<10>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher256::fresh()
    }

    /// Origin Rust: /// Create hasher for `H2^3`
    /// (random_oracles.rs:36-39, over Hasher256).
    pub fn h2_3_init() -> (h: Hasher256<11>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher256::fresh()
    }

    /// Origin Rust: /// Create hasher for `H3`
    /// (random_oracles.rs:41-44, over Hasher256).
    pub fn h3_init() -> (h: Hasher256<3>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher256::fresh()
    }

    /// Origin Rust: /// Create hasher for `H4`
    /// (random_oracles.rs:46-49, over Hasher256).
    pub fn h4_init() -> (h: Hasher256<4>)
        ensures
            h.buf@ == Seq::empty(),
    {
        Hasher256::fresh()
    }
}

// ==================================================================
// Slot pins (the FA9 tower consumption; the FA4 notes' bavc.rs:355
// 2xKeyBytes pin, re-checked on the oracle side)
// ==================================================================

/// The H-family read slabs downstream, pinned against the FA9 tower
/// consts (this is the FA4 prg_keysize_pins counterpart on the oracle
/// side): the bavc H0 stream is read in LambdaBytes chunks
/// (uhash_i, bavc.rs:107 read_into -- LambdaBytes per chunk), the H1
/// com slab is exactly LambdaBytesTimes2 (bavc.rs:355/:423
/// read_into::<Self::LambdaBytesTimes2> -- the 2*LambdaBytes digest
/// slab whose PRG-side twin FA4 pinned as TIMES2 == 2*KEYBYTES), and
/// the parameter.rs:121 SecurityParameter LambdaBytesTimes2 binding
/// is Prod<LambdaBytes, U2> at every level (FA9's spec mirror).
proof fn oracle_slot_pins()
{
    assert(BASE128_LAMBDA_BYTES_TIMES2 == 2 * BASE128_LAMBDA_BYTES);
    assert(BASE192_LAMBDA_BYTES_TIMES2 == 2 * BASE192_LAMBDA_BYTES);
    assert(BASE256_LAMBDA_BYTES_TIMES2 == 2 * BASE256_LAMBDA_BYTES);
    // the bavc.rs:355 slot at level 128: the SHAKE128 H1 com slab.
    assert(BASE128_LAMBDA_BYTES == 16);
    assert(BASE128_LAMBDA_BYTES_TIMES2 == 32);
    // the SHAKE256 variant carries level 192/256 slabs (parameter.rs
    // :202/:224 RandomOracle bindings).
    assert(BASE192_LAMBDA_BYTES == 24);
    assert(BASE256_LAMBDA_BYTES == 32);
}

// ==================================================================
// Layout faces (absorb order + the SEP space, machine-checked)
// ==================================================================

/// The input-layout face of the H family, machine-checked end to end
/// on concrete carriers:
///   (a) fresh hashers absorb nothing (the Default face);
///   (b) absorb order is observable: update(a); update(b) yields
///       a||b at the end of the string -- the reversed order yields
///       b||a, which differs already at index 0 (0x01 vs 0x02 -- the
///       reversed-order counterexample value);
///   (c) the same bytes under different Hx inits finish to different
///       absorbed strings -- the pad is part of the oracle key (the
///       domain-separation layout): after the same two input bytes,
///       the finished messages of H0, H1, H2^0..H2^3, H3, H4 end in
///       0x00, 0x01, 0x08..0x0b, 0x03, 0x04 respectively (all eight
///       pinned on the SHAKE128 side, the two extreme family members
///       re-pinned on the SHAKE256 side).
fn oracle_layout_faces()
{
    // (a) fresh face.
    let h0 = RandomOracleShake128::h0_init();
    assert(h0.buf@ == Seq::empty());
    assert(h0.buf@.len() == 0);

    // (b) absorb order, concrete counterexample value: 0x01 then 0x02.
    let a1: [u8; 1] = [0x01];
    let b1: [u8; 1] = [0x02];
    let mut h_ab = RandomOracleShake128::h0_init();
    h_ab.update(&a1);
    h_ab.update(&b1);
    assert(h_ab.buf@.len() == 2);
    assert(h_ab.buf@[0] == 0x01);
    assert(h_ab.buf@[1] == 0x02);
    let mut h_ba = RandomOracleShake128::h0_init();
    h_ba.update(&b1);
    h_ba.update(&a1);
    assert(h_ba.buf@[0] == 0x02);
    assert(h_ba.buf@[1] == 0x01);
    // the order difference is visible in the finished key too.
    let r_ab = h_ab.finish();
    let r_ba = h_ba.finish();
    assert(r_ab.msg@[0] == 0x01 && r_ab.msg@[2] == 0x00);
    assert(r_ba.msg@[0] == 0x02 && r_ba.msg@[2] == 0x00);

    // (c) domain separation: same input bytes, eight Hx pads (all on
    // the SHAKE128 carrier; input one byte 0x7f so the pad is msg[1]).
    let inp1: [u8; 1] = [0x7f];
    let mut m0 = RandomOracleShake128::h0_init();
    m0.update(&inp1);
    let r0 = m0.finish();
    assert(r0.msg@.len() == 2);
    assert(r0.msg@[1] == 0x00);

    let mut m1 = RandomOracleShake128::h1_init();
    m1.update(&inp1);
    let r1 = m1.finish();
    assert(r1.msg@.len() == 2);
    assert(r1.msg@[1] == 0x01);
    assert(r1.msg@ != r0.msg@);

    let mut m2_0 = RandomOracleShake128::h2_0_init();
    m2_0.update(&inp1);
    let r2_0 = m2_0.finish();
    assert(r2_0.msg@[1] == 0x08);

    let mut m2_1 = RandomOracleShake128::h2_1_init();
    m2_1.update(&inp1);
    let r2_1 = m2_1.finish();
    assert(r2_1.msg@[1] == 0x09);

    let mut m2_2 = RandomOracleShake128::h2_2_init();
    m2_2.update(&inp1);
    let r2_2 = m2_2.finish();
    assert(r2_2.msg@[1] == 0x0a);

    let mut m2_3 = RandomOracleShake128::h2_3_init();
    m2_3.update(&inp1);
    let r2_3 = m2_3.finish();
    assert(r2_3.msg@[1] == 0x0b);

    let mut m3 = RandomOracleShake128::h3_init();
    m3.update(&inp1);
    let r3 = m3.finish();
    assert(r3.msg@[1] == 0x03);

    let mut m4 = RandomOracleShake128::h4_init();
    m4.update(&inp1);
    let r4 = m4.finish();
    assert(r4.msg@[1] == 0x04);

    // the SHAKE256 half pins the same SEP space at the two extremes;
    // the pad lands identically (the 256 carrier keys shake256_byte).
    let mut s0 = RandomOracleShake256::h0_init();
    s0.update(&inp1);
    let q0 = s0.finish();
    assert(q0.msg@[1] == 0x00);
    let mut s2_1 = RandomOracleShake256::h2_1_init();
    s2_1.update(&inp1);
    let q2_1 = s2_1.finish();
    assert(q2_1.msg@[1] == 0x09);

    // multi-segment absorb recap: two 1-byte updates equal one 2-byte
    // update of the concatenated prefix (bavc/faest absorb several
    // slices per hasher; e.g. faest.rs:241-243 inputs output msg).
    let inp2: [u8; 2] = [0x7f, 0x35];
    let mut whole = RandomOracleShake128::h1_init();
    whole.update(&inp2);
    let mut split = RandomOracleShake128::h1_init();
    split.update(&[inp2[0]]);
    split.update(&[inp2[1]]);
    assert(split.buf@ == whole.buf@);
    let rw = whole.finish();
    let rs = split.finish();
    assert(rs.msg@ == rw.msg@);
}

// ==================================================================
// Stream faces (fill, composition, determinism, extendability)
// ==================================================================

/// The read-side contract face of the SHAKE readers, machine-checked
/// end to end (the FA4 prg_contract_faces counterpart for the
/// SHAKE/oracle side):
///   (a) fill + composition: reads cover disjoint consecutive stream
///       segments (6+4 bytes; consumed 6 then 10; the second segment
///       keys the oracle at offsets 6..10);
///   (b) deterministic derivation: a freshly finished instance over
///       the same absorbed string yields the SAME bytes (equal keys
///       and equal indices give equal oracle bytes -- the batch's
///       determinism claim; a[i] == c[i] and b[i] == c[6+i]);
///   (c) pure fill on a NON-zero destination: the 0xAB-prefilled
///       buffer still reads the oracle bytes -- the exact spot where
///       the SHAKE face diverges from the PRG twin's xor contract
///       (prg.rs:299-310: old^ks; a fill reading THERE would be false,
///       record-only S-FA4-2 -- and an xor reading HERE would be
///       refuted by the trusted shake: the fill contract below is the
///       honest one, but no value inequality claim is made over the
///       uninterpreted oracle);
///   (d) extendability (the implied-output-length discipline): after
///       reading a whole presumed "output", further reads continue
///       the SAME stream seamlessly (offsets 10, 14 -- XOF has no
///       output end; that is what lets bavc keep chunk-reading the
///       H0 stream per tree row and faest read r then iv off one H3
///       stream, faest.rs:256-257);
///   (e) the bavc chunk discipline: three consecutive 16-byte chunks
///       (the level-128 LambdaBytes uhash_i slot; bavc.rs:337-341)
///       cover offsets 0..16, 16..32, 32..48 with consumed pinned.
fn oracle_stream_faces()
{
    let a2: [u8; 2] = [0x14, 0x2b];
    let b2: [u8; 4] = [0x05, 0x66, 0x9e, 0x21];
    let mut h = RandomOracleShake128::h1_init();
    h.update(&a2);
    h.update(&b2);
    let mut r = h.finish();
    assert(r.msg@ == a2@ + b2@ + seq![0x01]);

    // (a) fill + composition: read 6 then 4.
    let mut x = [0u8; 6];
    r.read(&mut x);
    assert(r.consumed == 6);
    assert forall |i: int| 0 <= i < x@.len() implies
        #[trigger]
        x[i] == shake128_byte(r.msg@, i)
        by {
    }
    let mut y = [0u8; 4];
    r.read(&mut y);
    assert(r.consumed == 10);
    assert forall |i: int| 0 <= i < y@.len() implies
        #[trigger]
        y[i] == shake128_byte(r.msg@, 6 + i)
        by {
    }

    // (b) determinism: a fresh identical instance gives one 10-byte
    // read whose bytes equal the two composed ones.
    let mut h2 = RandomOracleShake128::h1_init();
    h2.update(&a2);
    h2.update(&b2);
    let mut c = h2.finish();
    assert(c.msg@ == r.msg@);
    let mut z = [0u8; 10];
    c.read(&mut z);
    assert(c.consumed == 10);
    assert forall |i: int| 0 <= i < z@.len() implies
        #[trigger]
        z[i] == shake128_byte(c.msg@, i)
        by {
    }
    assert forall |i: int| 0 <= i < x@.len() implies
        #[trigger]
        x[i] == z[i]
        by {
    }
    assert forall |i: int| 0 <= i < y@.len() implies
        #[trigger]
        y[i] == z[6 + i]
        by {
    }

    // (c) pure fill on a NON-zero destination.
    let mut d = [0xABu8; 4];
    r.read(&mut d);
    assert(r.consumed == 14);
    assert forall |i: int| 0 <= i < d@.len() implies
        #[trigger]
        d[i] == shake128_byte(r.msg@, 10 + i)
        by {
    }

    // (d) extendability: past the 10-byte "output" the same stream
    // continues (XOF: no implied output length is a bound; upstream
    // read accepts any length -- random_oracles.rs:75 verbatim).
    let mut e = [0u8; 4];
    r.read(&mut e);
    assert(r.consumed == 18);
    assert forall |i: int| 0 <= i < e@.len() implies
        #[trigger]
        e[i] == shake128_byte(r.msg@, 14 + i)
        by {
    }

    // (e) the bavc H0 chunk discipline on the SHAKE256 side: three
    // 32-byte chunks (the level-256 LambdaBytes uhash_i slot) off one
    // finished stream, at the bavc.rs:408-410 offsets.
    let mut g = RandomOracleShake256::h0_init();
    let ivs: [u8; 16] = [
        0x52, 0x24, 0x27, 0x94, 0xa5, 0x95, 0xfc, 0x1e, 0x66, 0x65, 0x45, 0x2f,
        0x76, 0x2e, 0x23, 0xb0,
    ];
    g.update(&ivs);
    let mut gr = g.finish();
    assert(gr.msg@ == ivs@ + seq![0x00]);
    let mut u1 = [0u8; 32];
    gr.read(&mut u1);
    assert(gr.consumed == 32);
    let mut u2 = [0u8; 32];
    gr.read(&mut u2);
    assert(gr.consumed == 64);
    let mut u3 = [0u8; 32];
    gr.read(&mut u3);
    assert(gr.consumed == 96);
    assert forall |i: int| 0 <= i < u1@.len() implies
        #[trigger]
        u1[i] == shake256_byte(gr.msg@, i)
        by {
    }
    assert forall |i: int| 0 <= i < u2@.len() implies
        #[trigger]
        u2[i] == shake256_byte(gr.msg@, 32 + i)
        by {
    }
    assert forall |i: int| 0 <= i < u3@.len() implies
        #[trigger]
        u3[i] == shake256_byte(gr.msg@, 64 + i)
        by {
    }
}

// ==================================================================
// The slot faces (bavc.rs:355 Times2 slab + the H0 chunk slots)
// ==================================================================

/// The slot-length discipline the H family feeds downstream, this
/// time against the FA9 tower consts at the READ side: the level-128
/// H1 com slab is exactly 32 == BASE128_LAMBDA_BYTES_TIMES2 bytes
/// (the bavc.rs:355 read_into slot size; the FA4 notes' 2xKeyBytes
/// pin), and the level-128 H0 chunk is exactly 16 ==
/// BASE128_LAMBDA_BYTES (the uhash_i slot). The rungs read the
/// tower-const-sized destinations through the concrete carriers so
/// the consumed offsets stay pinned to the slot sizes.
fn oracle_slot_faces()
{
    // bavc.rs:355 (level 128): the H1 com slab.
    assert(BASE128_LAMBDA_BYTES_TIMES2 == 32);
    let mut h = RandomOracleShake128::h1_init();
    h.update(&[0x0au8]);
    let mut r = h.finish();
    let mut com32 = [0u8; 32];
    assert(com32@.len() == BASE128_LAMBDA_BYTES_TIMES2);
    r.read(&mut com32);
    assert(r.consumed == BASE128_LAMBDA_BYTES_TIMES2);
    assert forall |i: int| 0 <= i < com32@.len() implies
        #[trigger]
        com32[i] == shake128_byte(r.msg@, i)
        by {
    }

    // bavc.rs:337-341 (level 128): the H0 uhash chunk.
    assert(BASE128_LAMBDA_BYTES == 16);
    let mut h0 = RandomOracleShake128::h0_init();
    h0.update(&[0x0bu8]);
    let mut r0 = h0.finish();
    let mut u16 = [0u8; 16];
    assert(u16@.len() == BASE128_LAMBDA_BYTES);
    r0.read(&mut u16);
    assert(r0.consumed == BASE128_LAMBDA_BYTES);
    assert forall |i: int| 0 <= i < u16@.len() implies
        #[trigger]
        u16[i] == shake128_byte(r0.msg@, i)
        by {
    }
}

// ==================================================================
// KATs (upstream random_oracles.rs:131-504, three groups; the SHAKE
// output values stay TRUSTED -- see the module doc honesty note)
// ==================================================================

/// Origin Rust (test_h0_128, random_oracles.rs:145-160):
///     let input = [0xe1, 0x52, 0x3a, 0x89, ..., 0x04, 0xd1];
///     let output = [0xcb, 0xbf, 0x57, 0xa9, ..., 0x4b, 0x79, 0x43];
///     let hasher = RandomOracleShake128::h0_init();
///     verify(hasher, &input, &output);
/// The upstream verify helper (:137-143) updates the input, finishes,
/// and reads output.len() bytes. Twin obligations (VERIFIED): the
/// input layout -- the finished message is exactly input||[0x00] --
/// and the output slot layout -- a 48-byte read covers the stream
/// offsets 0..48 with consumed pinned. The output VALUES
/// (0xcb, 0xbf, ... -- 48 trusted bytes) are SHAKE-core facts and are
/// NOT asserted as obligations over the uninterpreted oracle; the
/// first/last bytes are quoted here as trusted references only.
fn oracle_kat_h0_128()
{
    let input: [u8; 16] = [
        0xe1, 0x52, 0x3a, 0x89, 0x80, 0xc1, 0x62, 0x83, 0xcb, 0xc8, 0x5e, 0x71,
        0x70, 0x3a, 0x04, 0xd1,
    ];
    let mut hasher = RandomOracleShake128::h0_init();
    hasher.update(&input);
    // input layout: input bytes in order, then the H0 pad.
    let mut reader = hasher.finish();
    assert(reader.msg@ == input@ + seq![0x00]);
    assert(reader.msg@.len() == 17);
    assert(reader.msg@[0] == 0xe1);
    assert(reader.msg@[15] == 0xd1);
    assert(reader.msg@[16] == 0x00);
    assert(reader.consumed == 0);
    // output slot layout: 48 bytes (the upstream output length).
    let mut out = [0u8; 48];
    reader.read(&mut out);
    assert(reader.consumed == 48);
    assert forall |i: int| 0 <= i < out@.len() implies
        #[trigger]
        out[i] == shake128_byte(reader.msg@, i)
        by {
    }
    // trusted reference (NOT an obligation): upstream's 48 output bytes
    // begin 0xcb, 0xbf, 0x57, 0xa9 and end 0x4b, 0x79, 0x43.
}

/// Origin Rust (test_h1_128, random_oracles.rs:182-197):
///     let input = [0xd2, 0x33, 0x1c, 0x8b, ..., 0x2d, 0x2d, 0xd3];
///     let output = [0x93, 0xe3, 0x5f, 0xee, ... 0x4f, 0xdd, 0xd9];
///     let hasher = RandomOracleShake128::h1_init();
///     verify(hasher, &input, &output);
/// Twin group picked for the bavc.rs:355 slot: the upstream output is
/// exactly 32 bytes == BASE128_LAMBDA_BYTES_TIMES2, the LambdaBytes
/// com-slab size -- so the KAT rung doubles as the slot-length pin
/// rung. Input layout (input||[0x01]) and slot layout verified; output
/// values (0x93, 0xe3, ... trusted) not obligated.
fn oracle_kat_h1_128()
{
    let input: [u8; 16] = [
        0xd2, 0x33, 0x1c, 0x8b, 0xd9, 0x1b, 0x1e, 0x01, 0x56, 0x59, 0x09, 0x44,
        0x47, 0x2d, 0x2d, 0xd3,
    ];
    let mut hasher = RandomOracleShake128::h1_init();
    hasher.update(&input);
    let mut reader = hasher.finish();
    assert(reader.msg@ == input@ + seq![0x01]);
    assert(reader.msg@.len() == 17);
    assert(reader.msg@[16] == 0x01);
    let mut out = [0u8; 32];
    // the 32-byte slot IS the level-128 LambdaBytesTimes2 slab
    // (bavc.rs:355).
    assert(out@.len() == 32);
    assert(out@.len() == BASE128_LAMBDA_BYTES_TIMES2);
    reader.read(&mut out);
    assert(reader.consumed == 32);
    assert forall |i: int| 0 <= i < out@.len() implies
        #[trigger]
        out[i] == shake128_byte(reader.msg@, i)
        by {
    }
    // trusted reference (NOT an obligation): upstream's output begins
    // 0x93, 0xe3, 0x5f, 0xee and ends 0x5c, 0x4f, 0xdd, 0xd9.
}

/// Origin Rust (test_h2_1_256, random_oracles.rs:282-316): the
/// SHAKE256 H2^1 KAT -- a 176-byte input, a 168-byte output, the
/// mid-family pad SEP 0x09. The 176-byte input is too large to feed
/// per index (FA1-4 per-rung cost); the rungs below pin the input
/// layout structurally (the finished message equals
/// input||[0x09] as ONE concat assert, then the first, middle and
/// last input bytes at their exact offsets), the split-absorb
/// equivalence (two updates covering 128+48 bytes finish to the SAME
/// message as the single update -- the concat order face at scale),
/// and the output slot layout (a 168-byte read covers offsets 0..168,
/// then extendability continues past the upstream "output end" --
/// which only a trusted value-map could refuse). Output values
/// (0x60, 0x7e, ... trusted) not obligated.
fn oracle_kat_h2_1_256()
{
    let input: [u8; 176] = [
        0xbf, 0xbb, 0x6c, 0x34, 0xe9, 0xc8, 0xd6, 0xa4, 0xa9, 0xc9, 0x06, 0x4e,
        0x9f, 0x17, 0xa0, 0x1a, 0xdb, 0xbc, 0x39, 0xc1, 0xa5, 0xee, 0xd8, 0x83,
        0xb1, 0x93, 0x2d, 0xe2, 0xa9, 0xfe, 0xec, 0x28, 0xf6, 0x73, 0x7b, 0x30,
        0x90, 0xce, 0x01, 0x20, 0x46, 0xb4, 0x8e, 0xe9, 0xe0, 0x77, 0xe8, 0xe7,
        0xa7, 0xf1, 0x94, 0x92, 0x81, 0x7a, 0xe7, 0x80, 0x3a, 0x40, 0x1e, 0x6d,
        0x0a, 0x20, 0xcd, 0xac, 0x44, 0x3f, 0xb1, 0xea, 0x2e, 0x3e, 0x6d, 0xce,
        0xd3, 0xf8, 0xbf, 0x28, 0x60, 0x25, 0xd7, 0xe5, 0xa5, 0xcb, 0x28, 0x5e,
        0x2f, 0x91, 0x32, 0xa8, 0x5e, 0x33, 0x07, 0x13, 0x0f, 0x26, 0x23, 0x63,
        0xdb, 0xd5, 0xfd, 0xc2, 0x58, 0xd8, 0x6d, 0x9a, 0x8e, 0x4f, 0xcc, 0x70,
        0x7c, 0x91, 0xc9, 0x49, 0xf7, 0xad, 0x9c, 0xd8, 0x52, 0xfe, 0x68, 0xc9,
        0xc0, 0xe7, 0xb4, 0x41, 0x80, 0x60, 0xe0, 0x54, 0x2d, 0x2e, 0xb2, 0x6b,
        0x72, 0x3d, 0x5a, 0x3d, 0x2a, 0xb6, 0xd2, 0xa1, 0xaf, 0xff, 0x06, 0xc6,
        0x09, 0x87, 0xe4, 0x3c, 0x43, 0x0c, 0x61, 0xf0, 0xbb, 0x24, 0x1e, 0x6f,
        0x22, 0x32, 0xed, 0x61, 0x1f, 0xee, 0x05, 0x1b, 0xad, 0xfc, 0x5e, 0xec,
        0x14, 0x26, 0xdd, 0x72, 0x99, 0x7a, 0x59, 0xeb,
    ];
    let mut hasher = RandomOracleShake256::h2_1_init();
    hasher.update(&input);
    let mut reader = hasher.finish();
    // input layout: the whole 176-byte KAT input, then the 0x09 pad.
    assert(reader.msg@ == input@ + seq![0x09]);
    assert(reader.msg@.len() == 177);
    assert(reader.msg@[0] == 0xbf);
    assert(reader.msg@[87] == 0xa8);
    assert(reader.msg@[175] == 0xeb);
    assert(reader.msg@[176] == 0x09);

    // split-absorb equivalence at scale: two updates of 128 + 48 bytes
    // finish to the identical message (the concatenation order face
    // the bavc/faest multi-slice absorbs rely on).
    let mut split = RandomOracleShake256::h2_1_init();
    let mut seg1 = [0u8; 128];
    let mut seg2 = [0u8; 48];
    let mut k: usize = 0;
    while k < 128
        invariant
            k <= 128,
            forall |q: int| 0 <= q < k ==> seg1[q] == input[q],
        decreases
            128 - k,
    {
        seg1[k] = input[k];
        k += 1;
    }
    let mut j: usize = 0;
    while j < 48
        invariant
            j <= 48,
            forall |q: int| 0 <= q < j ==> seg2[q] == input[128 + q],
        decreases
            48 - j,
    {
        seg2[j] = input[128 + j];
        j += 1;
    }
    split.update(&seg1);
    split.update(&seg2);
    let mut reader_split = split.finish();
    assert(reader_split.msg@ == reader.msg@);

    // output slot layout: the 168-byte upstream output length.
    let mut out = [0u8; 168];
    reader.read(&mut out);
    assert(reader.consumed == 168);
    assert forall |i: int| 0 <= i < out@.len() implies
        #[trigger]
        out[i] == shake256_byte(reader.msg@, i)
        by {
    }
    // extendability past the upstream output end (XOF).
    let mut tail = [0u8; 8];
    reader.read(&mut tail);
    assert(reader.consumed == 176);
    assert forall |i: int| 0 <= i < tail@.len() implies
        #[trigger]
        tail[i] == shake256_byte(reader.msg@, 168 + i)
        by {
    }

    // trusted reference (NOT an obligation): upstream's 168 output
    // bytes begin 0x60, 0x7e, 0x4e, 0x0e and end 0x06, 0x37, 0x70.
}

} // verus!
