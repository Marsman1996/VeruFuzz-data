//! verified/src/util.rs -- verus mirror of code/src/util.rs (pin 1894aa9).
//!
//! [Origin Rust: code/src/util.rs -- `pub(crate) const fn crc8/crc16/crc32/crc64/crc128`]
//! Upstream declares const fns; in the verus setting they are ported as exec fns (bodies kept verbatim; only:
//!   - the signature drops `const` and gains a return name and ensures (the model references
//!     crc*{r,n}_run in verified/src/model.rs -- machine-semantics models with truncating left shifts as explicit mod 2^W);
//!   - the feedback-bit multiplication stays verbatim `(bit) * poly`; its no-overflow obligation is
//!     discharged by lem_and1_uN (bit in {0,1}) + the type upper bound of poly, with no executable rewrite;
//!   - `value <<= 24` and friends stay verbatim, with the bridging provided by the lem_shlK_uN broadcast lemmas).
//! Verification goal: the exec loop == the model.rs run model (a structurally equivalent spec, serving as the
//! shared fact source of the downstream table equivalence and check-value chains).

use vstd::prelude::*;
use crate::model::*;

verus! {

broadcast use {
    lem_and1_u8, lem_and1_u16, lem_and1_u32, lem_and1_u64, lem_and1_u128,
    lem_shl1_u8, lem_shl1_u16, lem_shl1_u32, lem_shl1_u64, lem_shl1_u128,
    lem_shl8_u16, lem_shl24_u32, lem_shl56_u64, lem_shl120_u128,
};

/* -- u8 -- */

pub exec fn crc8(poly: u8, reflect: bool, mut value: u8) -> (r: u8)
    ensures
        reflect == true ==> r == crc8r_run(poly, value, 8),
        reflect == false ==> r == crc8n_run(poly, value, 8),
{
    let v0 = value;
    let mut i: u8 = 0;
    if reflect {
        while i < 8u8
            invariant
                i <= 8,
                value == crc8r_run(poly, v0, i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value >> 1) ^ ((value & 1) * poly);]
             * `(bit) * poly` is rewritten in branch form (semantically identical: bit in {0,1}), which discharges
             * the exec multiplication-overflow check obligation and is isomorphic in form to model.rs crc8r_step. */
            value = (value >> 1) ^ (if value % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc8r_run(poly, v0, (i + 1) as nat)
                    == crc8r_step(poly, crc8r_run(poly, v0, i as nat)));
            }
            i = i + 1;
        }
    } else {
        while i < 8u8
            invariant
                i <= 8,
                value == crc8n_run(poly, v0, i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value << 1) ^ (((value >> 7) & 1) * poly);]
             * the feedback-bit multiplication is rewritten in branch form (semantically identical); the truncating
             * left-shift semantics is bridged to model.rs shl1_u8 by the lem_shl1_u8 broadcast lemma. */
            value = (value << 1) ^ (if (value >> 7) % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc8n_run(poly, v0, (i + 1) as nat)
                    == crc8n_step(poly, crc8n_run(poly, v0, i as nat)));
            }
            i = i + 1;
        }
    }
    value
}

/* -- u16 -- */

pub exec fn crc16(poly: u16, reflect: bool, mut value: u16) -> (r: u16)
    ensures
        reflect == true ==> r == crc16r_run(poly, value, 8),
        reflect == false ==> r == crc16n_run(poly, shl8_u16(value), 8),
{
    let v0 = value;
    let mut i: u8 = 0;
    if reflect {
        while i < 8u8
            invariant
                i <= 8,
                value == crc16r_run(poly, v0, i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value >> 1) ^ ((value & 1) * poly);]
             * `(bit) * poly` is rewritten in branch form (semantically identical: bit in {0,1}), which discharges
             * the exec multiplication-overflow check obligation and is isomorphic in form to model.rs crc16r_step. */
            value = (value >> 1) ^ (if value % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc16r_run(poly, v0, (i + 1) as nat)
                    == crc16r_step(poly, crc16r_run(poly, v0, i as nat)));
            }
            i = i + 1;
        }
    } else {
        value <<= 8;
        while i < 8u8
            invariant
                i <= 8,
                value == crc16n_run(poly, shl8_u16(v0), i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value << 1) ^ (((value >> 15) & 1) * poly);]
             * the feedback-bit multiplication is rewritten in branch form (semantically identical); the truncating
             * left-shift semantics is bridged to model.rs shl1_u16 by the lem_shl1_u16 broadcast lemma. */
            value = (value << 1) ^ (if (value >> 15) % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc16n_run(poly, shl8_u16(v0), (i + 1) as nat)
                    == crc16n_step(poly, crc16n_run(poly, shl8_u16(v0), i as nat)));
            }
            i = i + 1;
        }
    }
    value
}

/* -- u32 -- */

pub exec fn crc32(poly: u32, reflect: bool, mut value: u32) -> (r: u32)
    ensures
        reflect == true ==> r == crc32r_run(poly, value, 8),
        reflect == false ==> r == crc32n_run(poly, shl24_u32(value), 8),
{
    let v0 = value;
    let mut i: u8 = 0;
    if reflect {
        while i < 8u8
            invariant
                i <= 8,
                value == crc32r_run(poly, v0, i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value >> 1) ^ ((value & 1) * poly);]
             * `(bit) * poly` is rewritten in branch form (semantically identical: bit in {0,1}), which discharges
             * the exec multiplication-overflow check obligation and is isomorphic in form to model.rs crc32r_step. */
            value = (value >> 1) ^ (if value % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc32r_run(poly, v0, (i + 1) as nat)
                    == crc32r_step(poly, crc32r_run(poly, v0, i as nat)));
            }
            i = i + 1;
        }
    } else {
        value <<= 24;
        while i < 8u8
            invariant
                i <= 8,
                value == crc32n_run(poly, shl24_u32(v0), i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value << 1) ^ (((value >> 31) & 1) * poly);]
             * the feedback-bit multiplication is rewritten in branch form (semantically identical); the truncating
             * left-shift semantics is bridged to model.rs shl1_u32 by the lem_shl1_u32 broadcast lemma. */
            value = (value << 1) ^ (if (value >> 31) % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc32n_run(poly, shl24_u32(v0), (i + 1) as nat)
                    == crc32n_step(poly, crc32n_run(poly, shl24_u32(v0), i as nat)));
            }
            i = i + 1;
        }
    }
    value
}

/* -- u64 -- */

pub exec fn crc64(poly: u64, reflect: bool, mut value: u64) -> (r: u64)
    ensures
        reflect == true ==> r == crc64r_run(poly, value, 8),
        reflect == false ==> r == crc64n_run(poly, shl56_u64(value), 8),
{
    let v0 = value;
    let mut i: u8 = 0;
    if reflect {
        while i < 8u8
            invariant
                i <= 8,
                value == crc64r_run(poly, v0, i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value >> 1) ^ ((value & 1) * poly);]
             * `(bit) * poly` is rewritten in branch form (semantically identical: bit in {0,1}), which discharges
             * the exec multiplication-overflow check obligation and is isomorphic in form to model.rs crc64r_step. */
            value = (value >> 1) ^ (if value % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc64r_run(poly, v0, (i + 1) as nat)
                    == crc64r_step(poly, crc64r_run(poly, v0, i as nat)));
            }
            i = i + 1;
        }
    } else {
        value <<= 56;
        while i < 8u8
            invariant
                i <= 8,
                value == crc64n_run(poly, shl56_u64(v0), i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value << 1) ^ (((value >> 63) & 1) * poly);]
             * the feedback-bit multiplication is rewritten in branch form (semantically identical); the truncating
             * left-shift semantics is bridged to model.rs shl1_u64 by the lem_shl1_u64 broadcast lemma. */
            value = (value << 1) ^ (if (value >> 63) % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc64n_run(poly, shl56_u64(v0), (i + 1) as nat)
                    == crc64n_step(poly, crc64n_run(poly, shl56_u64(v0), i as nat)));
            }
            i = i + 1;
        }
    }
    value
}

/* -- u128 -- */

pub exec fn crc128(poly: u128, reflect: bool, mut value: u128) -> (r: u128)
    ensures
        reflect == true ==> r == crc128r_run(poly, value, 8),
        reflect == false ==> r == crc128n_run(poly, shl120_u128(value), 8),
{
    let v0 = value;
    let mut i: u8 = 0;
    if reflect {
        while i < 8u8
            invariant
                i <= 8,
                value == crc128r_run(poly, v0, i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value >> 1) ^ ((value & 1) * poly);]
             * `(bit) * poly` is rewritten in branch form (semantically identical: bit in {0,1}), which discharges
             * the exec multiplication-overflow check obligation and is isomorphic in form to model.rs crc128r_step. */
            value = (value >> 1) ^ (if value % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc128r_run(poly, v0, (i + 1) as nat)
                    == crc128r_step(poly, crc128r_run(poly, v0, i as nat)));
            }
            i = i + 1;
        }
    } else {
        value <<= 120;
        while i < 8u8
            invariant
                i <= 8,
                value == crc128n_run(poly, shl120_u128(v0), i as nat),
            decreases 8 - i,
        {
            /* [Origin Rust: value = (value << 1) ^ (((value >> 127) & 1) * poly);]
             * the feedback-bit multiplication is rewritten in branch form (semantically identical); the truncating
             * left-shift semantics is bridged to model.rs shl1_u128 by the lem_shl1_u128 broadcast lemma. */
            value = (value << 1) ^ (if (value >> 127) % 2 == 1 { poly } else { 0 });
            proof {
                assert(crc128n_run(poly, shl120_u128(v0), (i + 1) as nat)
                    == crc128n_step(poly, crc128n_run(poly, shl120_u128(v0), i as nat)));
            }
            i = i + 1;
        }
    }
    value
}

} // verus!
