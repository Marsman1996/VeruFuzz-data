//! faest 0.3.0 -- Verus transcription of src/verifier/vole_
//! commitments.rs, batch FA12 (the verifier-tree VOLE commitment
//! carriers; the lightest dependency closure -- fields + utils only).
//!
//! Upstream (verifier/vole_commitments.rs, 143 lines, pin 9ccc68c0):
//! VoleCommits (:13-17, the owned scalar-plane container), its impl
//! block (:19-63: from_constant :24-35, to_ref :37-42,
//! get_commits_ref :44-52, get_field_commit :54-58,
//! get_field_commit_sq :59-62), VoleCommitsRef (:65-69, the slice
//! view), its get_commits_ref (:71-85), and the Index<..> /
//! AsRef<Array<F, L>> impls (:87-143). The upstream file carries no
//! in-file test rows; its value surface rides the batch oracle arm.
//!
//! Representation lowering (trust boundary, this batch's records):
//!   - F: BigGaloisField instantiates at the closed GF128 axis (u128;
//!     the crate::fields re-spell of upstream :1-11 rides
//!     crate::large_fields, the FA6-pre/FA11 convention). The
//!     GF192/GF256 axes are out of this batch's scope (D-FA11b-2
//!     family deferral inherited).
//!   - `Box<Array<F, L>>` (scalars) lowers to Vec<u128>; `&Array<F,
//!     L>` lowers to &[u128] (the FA1 hybrid-array trust convention;
//!     the Box carrier lowers to the owned Vec); `&'a F` (delta)
//!     settles as &'a u128 -- the Delta storage face verbatim.
//!   - The typenum size algebra (`L: ArraySize + Mul<U8, Output =
//!     L2>` etc.) drops at the boundary (FA10-pre rijndael
//!     precedent); lengths ride as plain runtime requires.
//!   - The upstream `Mul<u8>` on F (`*delta * get_bit(input, i)` and
//!     the AddRoundKey byte planes) is the apply_mask(bit0) select:
//!     delta * bit == delta or 0 (fields/large_fields record); it is
//!     NOT a field multiply. First-hand derivation this batch.
//!   - The upstream doc line on from_constant (:24, "Turns the input
//!     array into vole commitments using the challenge delta.") rides
//!     as the doc line below (data transcription, not a claim).
//!   - The upstream debug_assert! rows (:55, :60 -- `idx * 8 + 8 <=
//!     L::USIZE`) re-erect as requires (the `# Panics`-to-requires
//!     convention).
//!   - The Index<usize> / Index<Range<usize>> / AsRef impls (:87-143)
//!     drop at the trait boundary (the FA4-1 impl-trait-for-type
//!     ban); the tree's consumption sites (`w[4 * i..4 * i + 4]`,
//!     `w.scalars[a..b]`) re-spell directly at the twin callsites --
//!     each re-spelling point records this here once.
//!   - The `get_bit(input, i)` utils face (upstream utils.rs :118-122:
//!     `(input[index / 8] >> index % 8) & 1`) re-spells inline at the
//!     twin body (the utils.rs twin's harness consumers own the utils
//!     module; this file's use is a two-lane select, first-hand
//!     transcribed).

use vstd::prelude::*;

use crate::large_fields::{
    gf128_byte_combine_slice, gf128_byte_combine_spec, gf128_byte_combine_sq_slice,
    sqb_slot8,
};

verus! {

// ===========================================================================
// VoleCommits (upstream :13-17):
//     #[derive(Debug, Clone)]
//     pub(crate) struct VoleCommits<'a, F: BigGaloisField, L: ArraySize> {
//         pub(crate) scalars: Box<Array<F, L>>,
//         pub(crate) delta: &'a F }
// The derives drop at the twin boundary (the FA6-pre clone-family
// record: clone re-erects as the explicit member loops at consumers);
// Box<Array<F, L>> -> Vec<u128>.
// ===========================================================================

pub struct VoleCommits<'a> {
    /// The scalar-plane VOLE commitments (one field element per bit
    /// slot of the committed state; upstream `scalars`).
    pub scalars: Vec<u128>,
    /// The challenge delta (upstream `delta`; the Delta storage face).
    pub delta: &'a u128,
}

// ===========================================================================
// VoleCommitsRef (upstream :65-69):
//     #[derive(Debug, Copy, Clone)]
//     pub(crate) struct VoleCommitsRef<'a, F: BigGaloisField, L: ArraySize> {
//         pub(crate) scalars: &'a Array<F, L>,
//         pub(crate) delta: &'a F }
// ===========================================================================

pub struct VoleCommitsRef<'a> {
    pub scalars: &'a [u128],
    pub delta: &'a u128,
}

impl<'a> VoleCommits<'a> {
    /// Origin Rust (:24-35, from_constant; upstream doc line verbatim:
    /// "Turns the input array into vole commitments using the
    /// challenge delta."):
    ///     pub(crate) fn from_constant<L2>(input: &Array<u8, L>,
    ///         delta: &'a F) -> VoleCommits<'a, F, L2>
    ///     where L: ArraySize + Mul<U8, Output = L2>, L2: ArraySize
    ///     {
    ///         let scalars = Box::new(<Array<F, L2>>::from_iter(
    ///             (0..L2::USIZE).map(|i| *delta * get_bit(input, i))));
    ///         VoleCommits { scalars, delta } }
    /// The typenum L->L2 product lowers to the runtime length
    /// (input.len() * 8); the map lowers to the index loop; the
    /// `*delta * get_bit(input, i)` Mul<u8> is the bit-0 select
    /// (header record).
    pub fn from_constant(input: &[u8], delta: &'a u128) -> (o: VoleCommits<'a>)
        requires
            input.len() * 8 <= usize::MAX,
        ensures
            o.scalars.len() == input.len() * 8,
            forall |i: int|
                0 <= i < o.scalars.len()
                    ==> o.scalars[i]
                        == (if (((input[i / 8] >> (i % 8)) & 1) == 1) {
                            *delta
                        } else {
                            0u128
                        }),
            o.delta == delta,
    {
        let mut scalars: Vec<u128> = Vec::new();
        let mut i: usize = 0;
        while i < input.len() * 8
            invariant
                input.len() * 8 <= usize::MAX,
                i <= input.len() * 8,
                scalars.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> scalars[j]
                            == (if (((input[j / 8] >> (j % 8)) & 1) == 1) {
                                *delta
                            } else {
                                0u128
                            }),
            decreases
                input.len() * 8 - i,
        {
            assert(i / 8 < input.len()) by (nonlinear_arith)
                requires
                    i < 8 * input.len(),
            {
            }
            let bit: u8 = (input[i / 8] >> (i % 8)) & 1;
            if bit == 1 {
                scalars.push(*delta);
            } else {
                scalars.push(0u128);
            }
            i += 1;
        }
        VoleCommits { scalars, delta }
    }

    /// Origin Rust (:37-42, to_ref): the full-window borrow view.
    pub fn to_ref(self: &Self) -> (o: VoleCommitsRef<'_>)
        ensures
            o.scalars.len() == self.scalars.len(),
            forall |j: int|
                0 <= j < o.scalars.len()
                    ==> o.scalars[j] == self.scalars[j as int],
            o.delta == self.delta,
    {
        VoleCommitsRef { scalars: &self.scalars, delta: self.delta }
    }

    /// Origin Rust (:44-52, get_commits_ref): the sub-window borrow
    /// view (typenum L2 lowers to the runtime l2 window length,
    /// FA10-pre precedent).
    pub fn get_commits_ref(self: &Self, start_idx: usize, l2: usize) -> (o: VoleCommitsRef)
        requires
            start_idx + l2 <= self.scalars.len(),
        ensures
            o.scalars.len() == l2,
            forall |j: int|
                0 <= j < l2
                    ==> o.scalars[j] == self.scalars[(start_idx + j) as int],
            o.delta == self.delta,
    {
        VoleCommitsRef {
            scalars: &self.scalars[start_idx..start_idx + l2],
            delta: self.delta,
        }
    }

    /// Origin Rust (:54-58, get_field_commit):
    ///     pub(crate) fn get_field_commit(&self, idx: usize) -> F {
    ///         debug_assert!(idx * 8 + 8 <= L::USIZE);
    ///         F::byte_combine_slice(&self.scalars[8 * idx..8 * idx + 8]) }
    /// The debug_assert re-erects as requires (the # Panics
    /// convention); the byte_combine_slice fold lowers to the
    /// large_fields face (ensures == gf128_byte_combine_spec).
    pub fn get_field_commit(self: &Self, idx: usize) -> (o: u128)
        requires
            idx * 8 + 8 <= self.scalars.len(),
        ensures
            o == gf128_byte_combine_spec(
                self.scalars[idx * 8],
                self.scalars[idx * 8 + 1],
                self.scalars[idx * 8 + 2],
                self.scalars[idx * 8 + 3],
                self.scalars[idx * 8 + 4],
                self.scalars[idx * 8 + 5],
                self.scalars[idx * 8 + 6],
                self.scalars[idx * 8 + 7],
            ),
    {
        gf128_byte_combine_slice(&self.scalars[8 * idx..8 * idx + 8])
    }

    /// Origin Rust (:59-62, get_field_commit_sq): the squared fold
    /// (square_byte then byte_combine, the FA11-beta fields face).
    pub fn get_field_commit_sq(self: &Self, idx: usize) -> (o: u128)
        requires
            idx * 8 + 8 <= self.scalars.len(),
        ensures
            o == gf128_byte_combine_spec(
                sqb_slot8(0, self.scalars[idx * 8], self.scalars[idx * 8 + 1], self.scalars[idx * 8 + 2], self.scalars[idx * 8 + 3], self.scalars[idx * 8 + 4], self.scalars[idx * 8 + 5], self.scalars[idx * 8 + 6], self.scalars[idx * 8 + 7]),
                sqb_slot8(1, self.scalars[idx * 8], self.scalars[idx * 8 + 1], self.scalars[idx * 8 + 2], self.scalars[idx * 8 + 3], self.scalars[idx * 8 + 4], self.scalars[idx * 8 + 5], self.scalars[idx * 8 + 6], self.scalars[idx * 8 + 7]),
                sqb_slot8(2, self.scalars[idx * 8], self.scalars[idx * 8 + 1], self.scalars[idx * 8 + 2], self.scalars[idx * 8 + 3], self.scalars[idx * 8 + 4], self.scalars[idx * 8 + 5], self.scalars[idx * 8 + 6], self.scalars[idx * 8 + 7]),
                sqb_slot8(3, self.scalars[idx * 8], self.scalars[idx * 8 + 1], self.scalars[idx * 8 + 2], self.scalars[idx * 8 + 3], self.scalars[idx * 8 + 4], self.scalars[idx * 8 + 5], self.scalars[idx * 8 + 6], self.scalars[idx * 8 + 7]),
                sqb_slot8(4, self.scalars[idx * 8], self.scalars[idx * 8 + 1], self.scalars[idx * 8 + 2], self.scalars[idx * 8 + 3], self.scalars[idx * 8 + 4], self.scalars[idx * 8 + 5], self.scalars[idx * 8 + 6], self.scalars[idx * 8 + 7]),
                sqb_slot8(5, self.scalars[idx * 8], self.scalars[idx * 8 + 1], self.scalars[idx * 8 + 2], self.scalars[idx * 8 + 3], self.scalars[idx * 8 + 4], self.scalars[idx * 8 + 5], self.scalars[idx * 8 + 6], self.scalars[idx * 8 + 7]),
                sqb_slot8(6, self.scalars[idx * 8], self.scalars[idx * 8 + 1], self.scalars[idx * 8 + 2], self.scalars[idx * 8 + 3], self.scalars[idx * 8 + 4], self.scalars[idx * 8 + 5], self.scalars[idx * 8 + 6], self.scalars[idx * 8 + 7]),
                sqb_slot8(7, self.scalars[idx * 8], self.scalars[idx * 8 + 1], self.scalars[idx * 8 + 2], self.scalars[idx * 8 + 3], self.scalars[idx * 8 + 4], self.scalars[idx * 8 + 5], self.scalars[idx * 8 + 6], self.scalars[idx * 8 + 7]),
            ),
    {
        gf128_byte_combine_sq_slice(&self.scalars[8 * idx..8 * idx + 8])
    }
}

impl<'a> VoleCommitsRef<'a> {
    /// Origin Rust (:76-85, VoleCommitsRef::get_commits_ref): the
    /// sub-window re-slice of the view (same typenum-L2 lowering as
    /// the owned face above).
    pub fn get_commits_ref(self: &Self, start_idx: usize, l2: usize) -> (o: VoleCommitsRef<'a>)
        requires
            start_idx + l2 <= self.scalars.len(),
        ensures
            o.scalars.len() == l2,
            forall |j: int|
                0 <= j < l2
                    ==> o.scalars[j] == self.scalars[(start_idx + j) as int],
            o.delta == self.delta,
    {
        VoleCommitsRef {
            scalars: &self.scalars[start_idx..start_idx + l2],
            delta: self.delta,
        }
    }
}

// Records (upstream surfaces outside this twin's lowered scope):
//   - The Index<usize> / Index<Range<usize>> impls for both structs
//     (:87-133) and AsRef<Array<F, L>> (:135-143) drop at the trait
//     boundary (FA4-1); consumption sites re-spell at the twin
//     callsites (verifier/aes.rs + encryption.rs + key_expansion.rs
//     twins read `.scalars[...]` and slice windows directly).
//   - The derives on both structs (Debug/Clone/Copy) drop at the
//     twin boundary; consumer copies re-erect explicitly.

} // verus!
