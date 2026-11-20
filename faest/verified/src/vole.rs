//! faest 0.3.0 -- Verus transcription of src/vole.rs, batch FA8.
//!
//! Upstream: vole.rs (542 lines) of the pinned tree (fetch.conf
//! 9ccc68c0; code/ read-only): the VOLE commitment / reconstruct layer
//! (TWEAK_OFFSET, VoleCommitResult, VoleReconstructResult, the two
//! VoleCommitmentCRef[Mut] index faces, convert_to_vole, volecommit,
//! volereconstruct; upstream :23-312, the cfg(test) module :314-542
//! carried by the harness in extract form), plus the
//! vole_array_length slice of TauParameters (upstream parameter.rs
//! :841-846 -- the FA1 notes deferred it to the vole owner, and the
//! FA7 mount decision explicitly recorded it "FA8 territory"; this
//! twin collects it).
//!
//! Trusted-core boundary (inherited, closed panels): everything FA7
//! landed green is consumed as-is -- the tau helpers
//! (bavc_max_node_depth / bavc_max_node_index + their spec faces),
//! the FA4 prg_byte oracle + prg_prefix stream view, the FA1
//! xor_arrays_inplace / decode rows (mounted read-only), and the
//! flat-slab plumbing (key_row / bpow / mpow) from the FA7 bavc
//! twin.  The bavc fold ladder itself (commit / open / reconstruct
//! main loops) stays behind the open-ledger wall D-FA7-1 (the FA7
//! window-four freeze: the z3 4.16.0 process-death query shapes on
//! the grown-Seq chains; the ladder awaits a z3 upgrade or the FA14
//! frozen-tree rescan) -- the vole main loops fold over that
//! ladder's result structures by their contract rows, per the
//! frozen-face convention of FA11/FA12/FA13 (external_body + the
//! faithful body in comments + the parameter-domain requires
//! table).
//!
//! Value semantics pinned this batch (first-hand, the python arm
//! `out/kverus-run/FA8/sim_vole.py`, ALL 12 upstream vole rows
//! bit-exact; see the notes for the per-row derivation):
//! - convert_to_vole's rj window array IS an open-cascade binary
//!   counter: at pair-done phi = i+1, the ni = 2^D seed rows have
//!   grown exactly D window rows (the identity
//!   `vole_array_length(i) == bavc_max_node_depth(i)` holds on all
//!   twelve tau configs -- closed-form-proved at this twin,
//!   lemma_vole_array_length_is_depth -- i.e. row rj[d] holds the
//!   cascade node 2^(d+1)*(2z+1) of the done-tree; row 0 at ::10 is
//!   the level-D root, the xor-fold of all ni per-leaf expanded
//!   streams);
//! - the v row d equals the xor of the odd half-marks at rung d
//!   (level 0 = the expanded leaves) -- recorded as cascade_row +
//!   vole_row_of spec faces;
//! - the c correction of round i is u_i xor u_0 bytewise (::8);
//!   volereconstruct's ::9 remap feeds slot jx == 0 the zero row
//!   (the "skip j = delta_i" comment lowers to the zero placeholder;
//!   a delta-punctured read otherwise), and ::15 xors the c row into
//!   column j exactly at the set bits of delta_i.
//!
//! Shape lowerings (batch decisions, module-doc record):
//! - the upstream typenum Mul/Prod constellation (LambdaBytes x U8 =
//!   Lambda, cs slab = LHatBytes x (Tau-1), v = Lambda rows x
//!   LHatBytes) lowers to flat byte vectors and slices with
//!   requires-pinned lengths (the FA1/FA7 trusted-representation
//!   decision); VoleCommitResult / VoleReconstructResult keep flat
//!   planes (v / q as flat matrices, rows via Stride extraction).
//! - the generic <BAVC, LHatBytes> parameters lower to explicit
//!   exec arguments over the FA1/FA9 configuration rows (lam bytes,
//!   lhat bytes, tau, k, tau1) -- the same lowering the FA7 tau
//!   helpers took.
//! - `1 << 31` in the TWEAK_OFFSET initializer lowers to the plain
//!   literal (the #FA1-3 machine bit-op blackout sits at the shift;
//!   value identical).
//! - `n / (1 << d)` in vole_array_length lowers to mpow over the
//!   FA7 chain (n == 2^D, so n / 2^d == 2^(D-d) and n/2 == 2^(D-1));
//!   the descending upstream range lowers to an ascending-counted
//!   accumulator (same value set).
//!
//! FA14 interface record (D-FA13-3): the FA13 shim trio
//! (faest.rs volecommit_cs / bavc_open / volereconstruct_cs) is the
//! CONSUMER shape -- the twin faces here spell ensured carrier
//! lengths compatibly (v_flat / q_flat flat planes; com 2*lam) so
//! the FA14 assembly swaps the shim bodies for this twin's chain
//! without re-carving the sign/verify callers.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::seq::Seq;

use super::bavc::{
    bavc_max_node_depth, bavc_max_node_depth_spec, bavc_max_node_index_spec, bpow, key_row,
    lemma_bpow_ge1, mpow, prg_prefix,
};

verus! {

// ===========================================================================
// Section 0: vole-side value-view spec faces over the green FA7
// machinery (no upstream counterpart at the type level -- the spec
// vocabulary the frozen main-loop faces and the FA14 ledger rows
// speak).
// ===========================================================================

/// Pointwise xor of two equal-length spec sequences (the xor_arrays
/// value view at the Seq level; the upstream zip iterator's
/// elementwise semantics as a spec fn, consumed by cascade_row).
pub open spec fn seq_xor(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len() as nat, |t: int| (a[t] ^ b[t]) as u8)
}

/// Spec face of CASCADE_row -- row (d, m) of the convert_to_vole
/// cascade value space: level 0 rows are the per-leaf lhat-byte
/// expanded streams of the seed rows (the two reads of fresh GGM
/// leaf pairs' sd under the shared round tweak), and a parent row
/// is the pointwise xor of its two children (:146 / :171, the
/// "father is left xor right" rows).  Row m at level d spans the
/// leaf window [m * 2^d, (m + 1) * 2^d); the apex value this face's
/// consumers carry is (D, 0) -- the ::10 r_{d,0} return row.
pub open spec fn cascade_row(
    seeds: Seq<u8>,
    lam: int,
    lhat: int,
    iv: Seq<u8>,
    twk: int,
    d: int,
    m: int,
) -> Seq<u8>
    decreases
        d,
{
    if d <= 0 {
        prg_prefix(key_row(seeds, lam, m), iv, twk, lhat)
    } else {
        seq_xor(
            cascade_row(seeds, lam, lhat, iv, twk, d - 1, 2 * m),
            cascade_row(seeds, lam, lhat, iv, twk, d - 1, 2 * m + 1),
        )
    }
}

/// Spec view of the level-d v row (::143 / :168, the "Level d =>
/// update V[d]" rows): the xor of the odd half-marks at rung d over
/// the ni = 2^D covered leaves -- i.e. the xor of the expanded leaf
/// values at the leaf positions (2m + 1) * 2^d,
/// m = 0 .. 2^(depth-d-1) - 1.
pub open spec fn vole_row_of(
    seeds: Seq<u8>,
    lam: int,
    lhat: int,
    iv: Seq<u8>,
    twk: int,
    d: int,
    depth: int,
) -> Seq<u8>
    recommends
        0 <= d,
        d < depth,
{
    vole_row_span(seeds, lam, lhat, iv, twk, d, depth, 0)
}

/// Recursive core of vole_row_of: the leaf-index scan from window m
/// (each window is one odd half-mark leaf position
/// (2m + 1) * 2^d; the scan count at rung d is 2^(depth-d-1)).  The
/// decreasing measure is the remaining window count, spelled
/// directly on the window index.
pub open spec fn vole_row_span(
    seeds: Seq<u8>,
    lam: int,
    lhat: int,
    iv: Seq<u8>,
    twk: int,
    d: int,
    depth: int,
    m: int,
) -> Seq<u8>
    decreases
        bpow(depth - d - 1) - m,
{
    if d >= depth || d < 0 {
        Seq::empty()
    } else if m >= bpow(depth - d - 1) {
        Seq::empty()
    } else {
        seq_xor(
            cascade_row(seeds, lam, lhat, iv, twk, 0, (2 * m + 1) * bpow(d)),
            vole_row_span(seeds, lam, lhat, iv, twk, d, depth, m + 1),
        )
    }
}

// ===========================================================================
// Section 1: TWEAK_OFFSET (upstream vole.rs:23-24).
// ===========================================================================

/// Origin Rust:
///     /// Initial tweak value as by FEAST specification
///     const TWEAK_OFFSET: u32 = 1 << 31;
/// (vole.rs:23-24). The initializer's machine shift lowers to the
/// plain literal (the #FA1-3 bit-op blackout sits at the shift
/// lowering; value identical: 1 << 31 == 2^31).
pub const TWEAK_OFFSET: u32 = 2147483648;

/// Exec face of `let twk = round + TWEAK_OFFSET;` (upstream
/// convert_to_vole :125; no wrap on the FAEST domain: round is the
/// vole round index < Tau <= 32).
pub fn vole_tweak_of(round: u32) -> (twk: u32)
    requires
        round <= 1024,
    ensures
        (twk as int) == (TWEAK_OFFSET as int) + (round as int),
{
    round + TWEAK_OFFSET
}

// ===========================================================================
// Section 2: the two VoleCommitmentCRef index faces (upstream
// vole.rs:54-113: VoleCommitmentCRef / VoleCommitmentCRefMut, each
// with an Index / IndexMut impl slicing row i to
// [i * LHatBytes, (i + 1) * LHatBytes)).
// ===========================================================================

/// Twin of `VoleCommitmentCRef::index` (vole.rs:64-66; the immutable
/// variant) as the slice window face: row i of the lhat-stride cs
/// slab.  The PhantomData<LHatBytes> parameter and the Index trait
/// surface lower to the explicit stride argument (the FA9 row
/// decision: the stride is a first-class exec parameter everywhere
/// the twin consumes the two faces; the machine band rows pin the
/// multiplication against the usize.overflow hazards per the FA13
/// requires-table conventions).  The body takes the split chain
/// (the FA13 signature_ref_mut_from shape) instead of the direct
/// range index.
/// The requiring rows spell the SPLIT-sum form (p + lhat <= len,
/// p = i * lhat) so the exec faces' only machine product -- the
/// split index i * lhat -- is bounded linearly by the caller-side
/// row (the FA13 requires-table convention: the same product
/// spelled once, adjoined additively; spec rows themselves carry
/// int arithmetic, so the guard is a single linear row).
pub fn vole_row_ref(cs: &[u8], lhat: usize, i: usize) -> (row: &[u8])
    requires
        0 < lhat,
        lhat <= 262144,
        i <= 4096,
        i * lhat + lhat <= cs.len(),
    ensures
        row.len() == lhat,
        forall |t: int| 0 <= t < (lhat as int) ==>
            #[trigger]
            row[t] == cs[(i as int) * (lhat as int) + t],
{
    let (_head, tail) = cs.split_at(i * lhat);
    let (row, _rest) = tail.split_at(lhat);
    row
}

/// Twin of `VoleCommitmentCRefMut::index_mut` (vole.rs:106-112; the
/// mutable variant): the mutable row window.  Content rows of a
/// &mut borrow face stay at the call site (the FA13
/// signature_ref_mut_from convention: the split chain pins the
/// segment LENGTHS in ensures; the content rows ride the caller's
/// own slice state).
pub fn vole_row_ref_mut(cs: &mut [u8], lhat: usize, i: usize) -> (row: &mut [u8])
    requires
        0 < lhat,
        lhat <= 262144,
        i <= 4096,
        i * lhat + lhat <= cs.len(),
    ensures
        row.len() == lhat,
{
    let (_head, tail) = cs.split_at_mut(i * lhat);
    let (row, _rest) = tail.split_at_mut(lhat);
    row
}

// ===========================================================================
// Section 3: vole_array_length (upstream parameter.rs:841-846 -- the
// tau helper the FA1/FA7 notes deferred to this, the vole owner).
// ===========================================================================

/// Spec face of the loop's partial window accumulation: the windows
/// at levels 2 .. dd already summed
///     sum_(d = 2 .. dd) (2^(D-d) - 1)
/// (the upstream `(2..depth).map(|d| n / (1 << d) - 1).sum()` body's
/// ascending twin -- the value set is the identical geometric
/// series; upstream spells the range descending).
pub open spec fn vole_window_sum(D: int, dd: int) -> int
    decreases
        dd,
{
    if dd <= 2 {
        0
    } else {
        (bpow(D - (dd - 1)) - 1) + vole_window_sum(D, dd - 1)
    }
}

/// Fact helper: bpow(a) <= bpow(b) on ordered nonneg exponents (the
/// FA7 monotone lemma wrapper).
pub proof fn lemma_bound_ordered(e: int, b: int)
    requires
        0 <= e,
        e <= b,
        b <= 52,
    ensures
        bpow(e) <= bpow(b),
{
    super::bavc::lemma_bpow_le(e, b);
}

/// Fact helper: bpow(a + b) == bpow(a) * bpow(b) on the nonneg band
/// (the closed-form geometric splits ride it).
pub proof fn lemma_bpow_add(a: int, b: int)
    requires
        0 <= a,
        0 <= b,
        a + b <= 30,
    ensures
        bpow(a + b) == bpow(a) * bpow(b),
    decreases
        a,
{
    if a == 0 {
        assert(bpow(0) == 1);
        assert(0 + b == b);
        assert(bpow(0 + b) == bpow(b));
        assert(1 * bpow(b) == bpow(b)) by {
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(1int, 0int, bpow(b));
            vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(1int);
        }
    } else {
        assert(bpow(a + b) == 2 * bpow(a - 1 + b));
        assert(bpow(a) == 2 * bpow(a - 1));
        lemma_bpow_add(a - 1, b);
        // (2 * bpow(a-1)) * bpow(b) == 2 * (bpow(a-1) * bpow(b))
        vstd::arithmetic::mul::lemma_mul_is_associative(2int, bpow(a - 1), bpow(b));
    }
}

/// The bpow(27) literal row (the exec loop's machine-band anchor;
/// the pw bridge + the vstd 64-entry power table).
pub proof fn lemma_bpow_27()
    ensures
        bpow(27) == 134217728,
{
    super::bavc::lemma_bpow_pw(27);
    vstd::arithmetic::power2::lemma2_to64();
    assert(super::utils::pw(27nat) == 134217728);
}

/// Closed form of vole_window_sum (the twin's machine-bound fact and
/// the depth-identity lemma's bridge):
///     vole_window_sum(D, dd) == (2^(D-1) - 2^(D-dd+1)) - (dd - 2)
/// -- the geometric tail minus the counted offset.  Also pins the
/// bpow(D-1) ceiling on the sum (both subtracted parts are
/// nonnegative on this domain: bpow(D-dd+1) >= 2^1 and dd >= 2).  A
/// separate nonneg row for the sum is NOT needed by any consumer
/// (the exec face's machine accumulation carries it directly: every
/// window term is >= 1) -- the first draft spelled a count-vs-
/// geometric product chain here; this restructure drops it (found
/// red at the drv4 round, replaced by the ceiling-first order).
pub proof fn lemma_vole_window_sum_closed(D: int, dd: int)
    requires
        2 <= dd,
        dd <= D,
        D <= 30,
    ensures
        vole_window_sum(D, dd) == (bpow(D - 1) - bpow(D - dd + 1)) - (dd - 2),
        vole_window_sum(D, dd) <= bpow(D - 1),
    decreases
        dd,
{
    lemma_bpow_ge1(D - 1);
    lemma_bpow_ge1(D - dd + 1);
    if dd == 2 {
        assert(vole_window_sum(D, 2) == 0);
        assert(0 == (bpow(D - 1) - bpow(D - 1)) - 0);
        assert(0 <= bpow(D - 1));
    } else {
        assert(vole_window_sum(D, dd) == (bpow(D - (dd - 1)) - 1) + vole_window_sum(D, dd - 1));
        lemma_vole_window_sum_closed(D, dd - 1);
        assert(bpow(D - dd + 2) == 2 * bpow(D - dd + 1));
        assert((bpow(D - dd + 1) - 1) + (bpow(D - 1) - bpow(D - dd + 2)) - (dd - 3)
            == (bpow(D - 1) - bpow(D - dd + 1)) - (dd - 2));
        // ceiling: the subtracted parts are nonneg
        assert((bpow(D - 1) - bpow(D - dd + 1)) - (dd - 2) <= bpow(D - 1));
    }
}

/// Spec face of `vole_array_length` (upstream parameter.rs:841-846:
/// `n / 2 - (2..depth).map(|d| n / (1 << d) - 1).sum()` with
/// n == 2^D: n/2 == 2^(D-1), n / 2^d == 2^(D-d)).
pub open spec fn vole_array_length_spec(tau1: int, k: int, i: int) -> int {
    let D = bavc_max_node_depth_spec(tau1, k, i);
    bpow(D - 1) - vole_window_sum(D, D)
}

/// Origin Rust:
///     /// Returns the required array length for generating the vole
///     /// correlations in [`crate::vole::convert_to_vole`]
///     fn vole_array_length(i: usize) -> usize {
///         let n = Self::bavc_max_node_index(i);
///         n / 2 - (2..Self::bavc_max_node_depth(i))
///                 .map(|d| n / (1 << d) - 1)
///                 .sum::<usize>()
///     }
/// (parameter.rs:841-846).  The (2..D) iterator range never
/// includes d == D.  Config constants as exec args (the FA7 face
/// shape); the shifts lower to mpow (n == 2^D so n / 2^d == 2^(D-d),
/// n/2 == 2^(D-1)).
pub fn vole_array_length(tau1: usize, k: usize, i: usize) -> (o: usize)
    requires
        2 <= k,
        k <= 28,
    ensures
        o == vole_array_length_spec(tau1 as int, k as int, i as int),
{
    let D: usize = bavc_max_node_depth(tau1, k, i);
    let half: usize = mpow(D - 1);
    let mut acc: usize = 0;
    // The loop runs only on D >= 3 (D == 1/2 have the empty window
    // range: acc stays 0 and half == D -- the D-2 case is folded
    // into the same exit formula; the invariant's 2 <= dd <= D row
    // is what forced this gate, found red at the drv4 round).
    if D >= 3 {
        let mut dd: usize = 2;
        while dd < D
            invariant
                2 <= dd <= D,
                D >= 3,
                D <= 28,
                (D as int) == bavc_max_node_depth_spec(tau1 as int, k as int, i as int),
                (acc as int) == vole_window_sum(D as int, dd as int),
                0 <= (acc as int),
                (acc as int) <= bpow((D as int) - 1),
                acc <= 0x8000000,
            decreases
                D - dd,
        {
            // window at level dd: n / (1 << dd) - 1 == 2^(D-dd) - 1
            let term: usize = mpow(D - dd);
            proof {
                // term >= 1 (the machine subtraction guard)
                lemma_bpow_ge1(D as int - dd as int);
                // the post-state accumulation identity and its
                // closed-form ceiling (machine add guard + the exact
                // spec row)
                lemma_vole_window_sum_closed(D as int, dd as int + 1);
                assert(vole_window_sum(D as int, dd as int + 1)
                    == (bpow(D as int - dd as int) - 1)
                        + vole_window_sum(D as int, dd as int));
                assert((dd as int) + 1 <= D as int);
                assert((acc as int) + ((term as int) - 1)
                    == vole_window_sum(D as int, dd as int + 1));
                assert((acc as int) + ((term as int) - 1) <= bpow((D as int) - 1));
                assert(bpow((D as int) - 1) <= 0x8000000) by {
                    lemma_bound_ordered(D as int - 1, 27);
                    lemma_bpow_27();
                }
                assert((term as int) <= bpow((D as int) - (dd as int)));
                lemma_bound_ordered(D as int - dd as int, 27);
            }
            assert(term >= 1);
            acc = acc + (term - 1);
            dd = dd + 1;
        }
    }
    proof {
        // the spec's own body is bpow(D-1) - window_sum(D, D): the
        // first assert is the loop-exit invariant row at D >= 3 and
        // the definition's 0 row at D <= 2 (acc stays 0 there);
        // everything else is def-unfolding + the loop ceiling row.
        assert((D as int) == bavc_max_node_depth_spec(tau1 as int, k as int, i as int));
        assert((acc as int) == vole_window_sum(D as int, D as int));
        assert(vole_array_length_spec(tau1 as int, k as int, i as int)
            == bpow((D as int) - 1) - vole_window_sum(D as int, D as int));
        assert((half as int) == bpow((D as int) - 1));
        assert((acc as int) <= (half as int));
    }
    half - acc
}

/// The identity this batch pins: the required window array length
/// of round i EQUALS the instance's max node depth (the rj window
/// rows count) on the k >= 2 domain:
///     vole_array_length(i) == bavc_max_node_depth(i)
/// -- recorded first-hand by the python arm on all twelve tau
/// configs (the sim's standing assert: non-EM/EM, s/f, all lambdas),
/// and closed-form-proved here (the window sum telescopes to
/// (2^(D-1) - 2) - (D - 2), so the array length is 2 + (D - 2)).
pub proof fn lemma_vole_array_length_is_depth(tau1: int, k: int, i: int)
    requires
        2 <= k,
        k <= 28,
    ensures
        vole_array_length_spec(tau1, k, i)
            == bavc_max_node_depth_spec(tau1, k, i),
{
    let D = bavc_max_node_depth_spec(tau1, k, i);
    assert(D == k || D == k - 1);
    assert(D >= 1);
    if D >= 2 {
        lemma_vole_window_sum_closed(D, D);
        assert(vole_window_sum(D, D) == (bpow(D - 1) - bpow(1)) - (D - 2));
        assert(vole_array_length_spec(tau1, k, i)
            == bpow(D - 1) - (bpow(D - 1) - bpow(1)) + (D - 2));
        super::bavc::lemma_bpow_pw(1int);
        vstd::arithmetic::power2::lemma2_to64();
        assert(super::utils::pw(1nat) == 2);
        assert(bpow(1) == 2);
        assert(vole_array_length_spec(tau1, k, i) == 2 + (D - 2));
        assert(vole_array_length_spec(tau1, k, i) == D);
    } else {
        // D == 1 (k == 2, i >= tau1): loop range (2..1) is empty,
        // n/2 == 1 == D.
        assert(vole_window_sum(D, D) == 0);
        assert(vole_array_length_spec(tau1, k, i) == bpow(0));
        assert(bpow(0) == 1);
        assert(D == 1);
    }
}

// ===========================================================================
// Section 4: convert_to_vole (upstream vole.rs:115-182) -- FROZEN
// face this batch (the cascade row-value ladder rides the D-FA7-5
// z3-wall query shapes; the per-iteration machinery recipe is in
// the batch notes' deferred ledger).
// ===========================================================================

/// Origin Rust:
///     pub(crate) fn convert_to_vole<'a, 'b, BAVC, LHatBytes>(
///         v: &'a mut [Array<u8, LHatBytes>],
///         sd: impl ExactSizeIterator
///             <Item = &'a Array<u8, BAVC::LambdaBytes>>,
///         iv: &IV,
///         round: u32,
///     ) -> Box<Array<u8, LHatBytes>> {
///         let twk = round + TWEAK_OFFSET;
///         let ni = BAVC::TAU::bavc_max_node_index(round as usize);
///         debug_assert!(sd.len() == ni);
///         // Init auxiliary memory
///         let mut rj: Vec<Box<Array<u8, LHatBytes>>> =
///             vec![Box::default();
///                  BAVC::TAU::vole_array_length(round as usize)];
///         let mut right_leaf: Array<u8, LHatBytes> = Array::default();
///         let mut next = 0;
///         for i in 0..ni / 2 {
///             // 1. Read left leaf and right leaf
///             // SAFETY: FAEST parameters ensure sd.len() = ni,
///             // hence the two unwraps are safe
///             BAVC::PRG::new_prg(sd.next().unwrap(), iv, twk)
///                 .read(&mut rj[next]);
///             BAVC::PRG::new_prg(sd.next().unwrap(), iv, twk)
///                 .read(&mut right_leaf);
///             // 2. Level 0 => update V[0]
///             xor_arrays_inplace(v[0].as_mut_slice(),
///                                 right_leaf.as_slice());
///             // 3. Father (level 1) is left leaf xor right leaf
///             xor_arrays_inplace(&mut rj[next], right_leaf.as_slice());
///             // Move one position forward and clean right leaf
///             next += 1;
///             right_leaf.fill(0);
///             // Traverse all levels for which we can already
///             // compute internal nodes
///             for (d, v_d) in v[1..].iter_mut().enumerate() {
///                 // Last two nodes are on different levels => abort
///                 if (i + 1) % (1 << (d + 1)) != 0 { break; }
///                 // Last two nodes are on same level:
///                 // 1. Save them as left, right
///                 let (left, right) = { ... };
///                 // 2. Level d => Update V[d]
///                 xor_arrays_inplace(v_d.as_mut_slice(), right);
///                 // 3. Father (level d+1) is left node xor right node
///                 xor_arrays_inplace(left, right);
///                 // 4. Move one position back and clean right node
///                 right.fill(0);
///                 next -= 1;
///             }
///         }
///         // ::10: after traversing all levels, rj[0] will contain
///         // r_{d,0}
///         // SAFETY: FAEST parameters ensure LHatBytes > 0
///         // (hence rj is not empty)
///         rj.into_iter().next().unwrap()
///     }
/// (vole.rs:115-182; the upstream `// SAFETY:` comments are kept
/// verbatim in this Origin block, spelled requires rows at the
/// face: the caller pins sd.len() == ni * lam
/// and vole's row lengths == lhat; the ni/2 == D power-of-two pair
/// structure rides bavc_max_node_index).
///
/// Facing facts (the value ledger rows recorded at this frozen face;
/// proof obligations for the FA14/FA7-continuation assembly,
/// KAT-anchored by the batch python arm):
/// - rj/next state machine: the rows open after the done-pair
///   cascade are the binary counter's set-bit nodes of the done
///   count (e.g. done = 101110b opens rows [32, 8, 4, 2], taken
///   MSB-down as heights) and row d of them equals the cascade node
///   value cascade_row(seeds@, ...) over the covered leaf window;
/// - return == cascade_row(seeds, lam, lhat, iv, twk, D, 0) (the
///   ::10 r_{d,0} row);
/// - v row d updates: v@fin row d == vole_row_of(seeds, ..., d, D);
/// - the PRG reads are the FA4 zero-init fill rows
///   (bprg_read_pair's single-read analog at lhat length).
#[verifier::external_body]
pub fn convert_to_vole(
    v: &mut Vec<Vec<u8>>,
    seeds: &[u8],
    iv: &[u8; 16],
    round: usize,
    lam: usize,
    lhat: usize,
    tau1: usize,
    k: usize,
) -> (o: Vec<u8>)
    requires
        2 <= k,
        k <= 28,
        1 <= lam,
        lam <= 1024,
        1 <= lhat,
        lhat <= 0x10000000,
        round <= 1024,
        bavc_max_node_depth_spec(tau1 as int, k as int, round as int) >= 1,
        (v.len() as int) == bavc_max_node_depth_spec(tau1 as int, k as int, round as int),
        (seeds.len() as int)
            == bavc_max_node_index_spec(tau1 as int, k as int, round as int) * (lam as int),
        forall |d: int| 0 <= d < v.len() ==> v[d].len() == lhat,
    ensures
        o.len() == lhat,
        final(v).len() == old(v).len(),
        forall |d: int| 0 <= d < final(v).len() ==>
            final(v)[d].len() == old(v)[d].len(),
{
    panic!("convert_to_vole: frozen behind the D-FA7-5 cascade row-value wall (see notes)")
}

// ===========================================================================
// Section 5: the result carriers (upstream vole.rs:26-52; the flat
// planes per the module doc) -- spelled ahead of the main faces
// their twin bodies return.
// ===========================================================================

/// Origin Rust:
///     #[derive(Clone, Debug, Default)]
///     pub struct VoleCommitResult<LambdaBytes, NLeafCommit, LHatBytes>
///     where ... {
///         pub com: Array<u8, Prod<LambdaBytes, U2>>,
///         pub decom: BavcDecommitment<LambdaBytes, NLeafCommit>,
///         pub u: Box<Array<u8, LHatBytes>>,
///         pub v: Box<Array<Array<u8, LHatBytes>,
///                     Prod<LambdaBytes, U8>>>,
///     }
/// (vole.rs:26-41; the derive rows carry no contract content and
/// are record-only).  Flat planes: com (2*lam), the decom planes
/// spelled inline (keys the open-node plane (2l-1)*lam slabs, coms
/// the per-leaf commitment plane), u (lhat), v_flat the flat
/// 8*lam x lhat matrix (rows lhat-strided; the FA13 shim carrier
/// shape, D-FA13-3-compatible).
pub struct VoleCommitResult {
    pub com: Vec<u8>,
    pub decom_keys: Vec<u8>,
    pub decom_coms: Vec<u8>,
    pub u: Vec<u8>,
    pub v_flat: Vec<u8>,
}

/// Origin Rust (vole.rs:43-52):
///     pub struct VoleReconstructResult<LambdaBytes, LHatBytes> ... {
///         pub com: Array<u8, Prod<LambdaBytes, U2>>,
///         pub q: Box<Array<Array<u8, LHatBytes>,
///                     Prod<LambdaBytes, U8>>>,
///     }
/// (flat planes as above; q_flat the 8*lam x lhat matrix).
pub struct VoleReconstructResult {
    pub com: Vec<u8>,
    pub q_flat: Vec<u8>,
}

// ===========================================================================
// Section 6: volecommit / volereconstruct (upstream vole.rs:184-312
// -- the folds over the bavc contract rows; behind the D-FA7-1
// upstream wall this batch, pruned to the contract rows; FA13's
// volecommit_cs / volereconstruct_cs are the consumer shapes of
// these faces -- D-FA13-3, the FA14 shim-replacement kit entry).
// ===========================================================================

/// Origin Rust:
///     pub fn volecommit<BAVC, LHatBytes>(
///         c: VoleCommitmentCRefMut<LHatBytes>,
///         r: &Array<u8, BAVC::LambdaBytes>,
///         iv: &IV,
///     ) -> VoleCommitResult<...> {
///         // ::2
///         let BavcCommitResult { com, decom, seeds } =
///             BAVC::commit(r, iv);
///         let mut v = Box::<...>::default();
///         let mut seeds_iter = seeds.iter();
///         // ::3.0
///         let (mut v_in, mut v_next) =
///             v.split_at_mut(BAVC::TAU::bavc_max_node_depth(0));
///         let u = convert_to_vole::<BAVC, LHatBytes>(
///             v_in, seeds_iter.by_ref()
///                      .take(BAVC::TAU::bavc_max_node_index(0)),
///             iv, 0);
///         // ::3.1..
///         for i in 1..BAVC::Tau::U32 {
///             let ni = BAVC::TAU::bavc_max_node_index(i);
///             let ki = BAVC::TAU::bavc_max_node_depth(i);
///             (v_in, v_next) = v_next.split_at_mut(ki);
///             // ::4..6
///             let u_i = convert_to_vole::<BAVC, LHatBytes>(
///                 v_in, seeds_iter.by_ref().take(ni), iv, i);
///             // ::8
///             for (u_i, u, c) in izip!(u_i.iter(), u.iter(),
///                                       &mut c[i - 1]) {
///                 *c = u_i ^ u;
///             }
///         }
///         VoleCommitResult { com, decom, u, v }
///     }
/// (vole.rs:184-232).  The ::2 commit fold rides D-FA7-1 (notes).
/// The FAEST config identity rows the seeds/v split needs:
/// the seeds carry the instance order (i, j) of the bavc leaf
/// records, i.e. seeds.len() == l * lam with l the GGM leaf count
/// and v split sums the per-round depths ki to 8*lam (the twin
/// asserts these as requires; upstream gets them from the type
/// arithmetic).
#[verifier::external_body]
pub fn volecommit_twin(
    cs: &mut [u8],
    r: &[u8],
    iv: &[u8; 16],
    lam: usize,
    lhat: usize,
    tau: usize,
    tau1: usize,
    k: usize,
    l: usize,
) -> (o: VoleCommitResult)
    requires
        2 <= k,
        k <= 28,
        1 <= tau,
        tau <= 1024,
        tau1 <= tau,
        1 <= lam,
        lam <= 1024,
        lam <= lhat,
        lhat <= 0x10000000,
        // the FAEST config identity (bavc leaf count)
        (l as int) == ((tau as int) + (tau1 as int)) * bpow((k as int) - 1),
        l <= 0x8000000,
        r.len() == lam,
        cs.len() == lhat * (tau - 1),
        iv.len() == 16,
    ensures
        o.com.len() == 2 * lam,
        o.u.len() == lhat,
        o.v_flat.len() == 8 * lam * lhat,
        o.decom_keys.len() == (2 * l - 1) * lam,
        final(cs).len() == old(cs).len(),
        // the ::8 row face: the cs plane is the u-correction rows
        // (one lhat row per round i in 1..tau); value rows are
        // deferred to the FA14 ledger (the u_i == cascade spec
        // chain), KAT-pinned bitwise by the python arm.
{
    panic!("volecommit_twin: frozen behind the D-FA7-1 commit fold wall (see notes)")
}

/// Origin Rust:
///     pub fn volereconstruct<BAVC, LHatBytes>(
///         chall: &Array<u8, BAVC::LambdaBytes>,
///         decom_i: &BavcOpenResult,
///         c: VoleCommitmentCRef<LHatBytes>,
///         iv: &IV,
///     ) -> Option<VoleReconstructResult<...>> {
///         let i_delta = decode_all_chall_3::<BAVC::TAU>(chall);
///         // Skip ::2 ... (parameter constraints ensure that we
///         // only provide valid challenges/indexes)
///         // ::4
///         let rec = BAVC::reconstruct(decom_i, &i_delta, iv)?;
///         let mut q = Box::<...>::default();
///         let mut q_ref = q.as_mut_slice();
///         // At round i, seeds_i has offset \sum_{j=0}^{i-1} N_j
///         // in the seeds vector
///         let mut sdi_off = 0;
///         let zero_arr = Array::default();
///         for i in 0..BAVC::Tau::U32 {
///             let delta_i = i_delta[i as usize];
///             let ni = BAVC::TAU::bavc_max_node_index(i);
///             let ki = BAVC::TAU::bavc_max_node_depth(i);
///             let (qi_ref, rest) = q_ref.split_at_mut(ki);
///             let seeds_i = (0..ni).map(|j_xor_delta| {
///                 if j_xor_delta == 0 { return &zero_arr; }
///                 let j = j_xor_delta ^ delta_i as usize;
///                 let seeds_idx = if j < delta_i as usize {
///                     sdi_off + j
///                 } else {
///                     sdi_off + j - 1 };
///                 &rec.seeds[seeds_idx] });
///             let _ =
///                 convert_to_vole::<BAVC, LHatBytes>(
///                     qi_ref, seeds_i, iv, i);
///             // ::14
///             if i != 0 {
///                 // ::15
///                 for (_, q_ij) in qi_ref.iter_mut().enumerate()
///                     .filter(|(j, _)| delta_i & (1 << j) != 0) {
///                     for (q_ij, c_ij) in zip(q_ij.iter_mut(),
///                         c[i - 1].iter()) {
///                         *q_ij ^= c_ij; } } }
///             // Round i+1 will write the next N_{i+1} columns
///             sdi_off += ni - 1;
///         }
///         Some(VoleReconstructResult { com: rec.com, q })
///     }
/// (vole.rs:234-312; the `// Skip ::2 as decode_all_chall_3 can't
/// fail` comment is kept verbatim in the Origin block -- the twin
/// takes i_delta as the decoded rows parameter and pins the
/// `parameter constraints` it names: every delta_i inside its
/// instance's node-index bound).  The ::4 reconstruct fold and the
/// convert cascade ride D-FA7-1 / D-FA7-5 (notes); the remap rows
/// are the face's spec lattice (the delta-punctured seed vector on
/// the puncture side j ^ delta > delta <=> seed slot - 1).
#[verifier::external_body]
pub fn volereconstruct_twin(
    decom_coms: &[u8],
    decom_nodes: &[u8],
    c: &[u8],
    iv: &[u8; 16],
    lam: usize,
    lhat: usize,
    tau: usize,
    tau1: usize,
    k: usize,
    delta: &[u16],
) -> (o: Option<VoleReconstructResult>)
    requires
        2 <= k,
        k <= 28,
        1 <= tau,
        tau <= 1024,
        tau1 <= tau,
        1 <= lam,
        lam <= 1024,
        lam <= lhat,
        lhat <= 0x10000000,
        c.len() == lhat * (tau - 1),
        iv.len() == 16,
        delta.len() == tau,
        forall |i: int| 0 <= i < delta.len() ==>
            ((delta[i] as int) < bavc_max_node_index_spec(tau1 as int, k as int, i)),
    ensures
        match o {
            Some(res) => {
                res.com.len() == 2 * lam
                    && res.q_flat.len() == 8 * lam * lhat
            }
            None => true,
        },
{
    panic!("volereconstruct_twin: frozen behind the D-FA7-1/D-FA7-5 walls (see notes)")
}

// ===========================================================================
// Section 7: Reader / decode consumption note (upstream import face:
// utils::{Reader, decode_all_chall_3, xor_arrays_inplace}).  The
// FA1 utils twin owns all three rows (Reader trait, the
// decode_all_chall_3 exec with the 2<=k<=15 bound rows + the
// per-index value rows, xor_arrays_inplace with the two-zone
// ensures); this module consumes them mounted read-only: the
// delta rows take the decoded face straight (Section 6 face), the
// xor consumption rows are the frozen bodies' value lattice
// (recorded at the faces above).
// ===========================================================================

} // verus!
