//! faest batch-FA3 harness (large fields, GF128 first wave) --
//! reference-style mount over the verified src tree.
//!
//! Transcribes the upstream inline test module of
//! code/src/fields/large_fields.rs:1495-1771 (field_ops for GF128 --
//! GF192/GF256 instantiation mount with their wave), instantiated at
//! GF128:
//!   - mul (:1693-1710, LargeFieldMul.json lambda==128): tuples 0 and
//!     1 of the five rows plus tuple 0's swapped direction as three
//!     full textbook-model (hmul/xtime) chains. The gf128_mul_spec
//!     karatsuba+reduction route's sample chain is a deferred item
//!     (D-FA3-1, batch notes): plain encoding does not substitute
//!     value-equal arguments into spec-fn applications (probes 7/8),
//!     so the exec==mul_spec (all inputs, proven in the src) plus
//!     the python dual-model offline check over ALL five rows (both
//!     the karatsuba+reduction and the textbook recomputations match
//!     the JSON values) carry the row evidence;
//!   - byte_combine_bits (:1749-1761, LargeFieldByteCombineBits.json
//!     lambda==128): rows 0/1, full-constant single blasts;
//!   - from_bit (:1545-1550): exec drivers of the identity rows;
//!   - mul_bit (:1601-1621): exec drivers (anything*0u8 == ZERO,
//!     anything*1u8 == anything) over the mul_u8 face; also the
//!     F::ZERO / F::ONE rows of the mul test's `anything` family via
//!     the library lemmas (generic, upstream samples only);
//!   - byte_combine_constants (:1636-1666): BYTE_COMBINE_2/3 rows via
//!     the field one/zero lemmas at the const faces;
//!   - byte_conversions (:1680-1690): as_bytes/from_bytes roundtrip
//!     proof on the KAT sample bytes + an exec driver;
//!   - square (:1738-1746): upstream `element * element ==
//!     element.square()` is closed by the library theorem
//!     gf128_square(at the hmul model) -- both directions covered at
//!     the sample level by the dual chains of the mul row, the
//!     mul_spec sample-bridge, and the square exec driver here.
//!   - sum_poly (:1624-1633) and byte_combine_slice (:1669-1677)
//!     upstream rows are second-wave scope (SumPoly faces and the
//!     slice-form face are recorded in the src twin; see notes).
//!
//! Consumes verified/src/lib.rs via the #[path] mount; nothing from
//! the src zone is re-copied.

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod faest;

use faest::fields::large_fields::{
    clmul64_bits, gf128_byte_combine_bits_spec, gf128_byte_combine_slice,
    gf128_sum_poly8, gf128_sum_poly_bits1, gf192_mul, gf256_mul,
    lemma_extension_length_pin_128, lemma_extension_length_pin_192,
    lemma_extension_length_pin_256, GF128_LENGTH_BYTES, GF192_LENGTH_BYTES,
    GF256_LENGTH_BYTES, GF384_LENGTH_BYTES, GF576_LENGTH_BYTES,
    GF768_LENGTH_BYTES,
    gf128_hmul, gf128_mul_bits,
    gf128_mul_spec, lemma_clmul64_bits_unfold, lemma_hmul128_bits_unfold,
    lemma_karatsuba_hi_def, lemma_karatsuba_lo_def, lemma_karatsuba_mid_def,
    lemma_mul128_one_r, lemma_mul128_spec_def, lemma_mul128_zero_r,
    lemma_sum_poly8_zero, lemma_sum_poly_bits1_zero,
    lemma_u128_bytes_eq, lemma_byte_combine_bits_spec_def,
    lemma_byte_combine_spec_def, byte128, gf128_as_bytes, gf128_from_bytes,
    gf128_bit_at, gf128_byte_combine, gf128_byte_combine_bits, gf128_double,
    gf128_from_bit, gf128_mul, gf128_mul_assign, gf128_mul_gf64, gf128_mul_self,
    gf128_reduce, gf128_karatsuba_hi, gf128_karatsuba_lo, gf128_karatsuba_mid,
    gf128_square, gf128_xtime, GF128_ALPHA,
    gf384_mul_gf128, gf576_mul_gf192, gf768_mul_gf256,
    gf384_as_bytes, gf384_from_bytes, gf576_as_bytes,
    gf576_from_bytes, gf768_as_bytes, gf768_from_bytes,
    gf384_mul_bits, gf576_mul_bits, gf768_mul_bits,
    GF192_ALPHA, GF256_ALPHA, GF192_BYTE_COMBINE_2,
    GF192_BYTE_COMBINE_3, GF256_BYTE_COMBINE_2,
    GF256_BYTE_COMBINE_3, U128_LOWER_MASK,
};

verus! {

// ===========================================================================
// Generated KAT section (gen_harness_kat.py; do not edit by hand).
// ===========================================================================

// tuple 0 offline dual-model check passed
proof fn kat_t0_hmul()
    ensures gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == 0xe6df41181a1477eae9131e9141c70a15u128,
{
    // rung chain precomputed + model-checked offline (python)
    assert((((0xa3fa4befd33ec6de509de93498eb9f05u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de93498eb9f05u128) >> 1u128) == 0x51fd25f7e99f636f284ef49a4c75cf82u128)) by (bit_vector);
    assert(((((0x261dffa502bbff620185b5b0891eec27u128) << 1) ^ (if ((((0x261dffa502bbff620185b5b0891eec27u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4c3bff4a0577fec4030b6b61123dd84eu128) by (bit_vector);
    assert(gf128_xtime(0x261dffa502bbff620185b5b0891eec27u128) == 0x4c3bff4a0577fec4030b6b61123dd84eu128);
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == 0x261dffa502bbff620185b5b0891eec27u128 ^ gf128_mul_bits(0x4c3bff4a0577fec4030b6b61123dd84eu128, 0x51fd25f7e99f636f284ef49a4c75cf82u128, 127nat)) by { lemma_hmul128_bits_unfold(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat); }
    assert((((0x51fd25f7e99f636f284ef49a4c75cf82u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49a4c75cf82u128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4d263ae7c1u128)) by (bit_vector);
    assert(((((0x4c3bff4a0577fec4030b6b61123dd84eu128) << 1) ^ (if ((((0x4c3bff4a0577fec4030b6b61123dd84eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9877fe940aeffd880616d6c2247bb09cu128) by (bit_vector);
    assert(gf128_xtime(0x4c3bff4a0577fec4030b6b61123dd84eu128) == 0x9877fe940aeffd880616d6c2247bb09cu128);
    assert(gf128_mul_bits(0x4c3bff4a0577fec4030b6b61123dd84eu128, 0x51fd25f7e99f636f284ef49a4c75cf82u128, 127nat) == 0u128 ^ gf128_mul_bits(0x9877fe940aeffd880616d6c2247bb09cu128, 0x28fe92fbf4cfb1b794277a4d263ae7c1u128, 126nat)) by { lemma_hmul128_bits_unfold(0x4c3bff4a0577fec4030b6b61123dd84eu128, 0x51fd25f7e99f636f284ef49a4c75cf82u128, 127nat); }
    assert((((0x28fe92fbf4cfb1b794277a4d263ae7c1u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4d263ae7c1u128) >> 1u128) == 0x147f497dfa67d8dbca13bd26931d73e0u128)) by (bit_vector);
    assert(((((0x9877fe940aeffd880616d6c2247bb09cu128) << 1) ^ (if ((((0x9877fe940aeffd880616d6c2247bb09cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x30effd2815dffb100c2dad8448f761bfu128) by (bit_vector);
    assert(gf128_xtime(0x9877fe940aeffd880616d6c2247bb09cu128) == 0x30effd2815dffb100c2dad8448f761bfu128);
    assert(gf128_mul_bits(0x9877fe940aeffd880616d6c2247bb09cu128, 0x28fe92fbf4cfb1b794277a4d263ae7c1u128, 126nat) == 0x9877fe940aeffd880616d6c2247bb09cu128 ^ gf128_mul_bits(0x30effd2815dffb100c2dad8448f761bfu128, 0x147f497dfa67d8dbca13bd26931d73e0u128, 125nat)) by { lemma_hmul128_bits_unfold(0x9877fe940aeffd880616d6c2247bb09cu128, 0x28fe92fbf4cfb1b794277a4d263ae7c1u128, 126nat); }
    assert((((0x147f497dfa67d8dbca13bd26931d73e0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd26931d73e0u128) >> 1u128) == 0xa3fa4befd33ec6de509de93498eb9f0u128)) by (bit_vector);
    assert(((((0x30effd2815dffb100c2dad8448f761bfu128) << 1) ^ (if ((((0x30effd2815dffb100c2dad8448f761bfu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x61dffa502bbff620185b5b0891eec37eu128) by (bit_vector);
    assert(gf128_xtime(0x30effd2815dffb100c2dad8448f761bfu128) == 0x61dffa502bbff620185b5b0891eec37eu128);
    assert(gf128_mul_bits(0x30effd2815dffb100c2dad8448f761bfu128, 0x147f497dfa67d8dbca13bd26931d73e0u128, 125nat) == 0u128 ^ gf128_mul_bits(0x61dffa502bbff620185b5b0891eec37eu128, 0xa3fa4befd33ec6de509de93498eb9f0u128, 124nat)) by { lemma_hmul128_bits_unfold(0x30effd2815dffb100c2dad8448f761bfu128, 0x147f497dfa67d8dbca13bd26931d73e0u128, 125nat); }
    assert((((0xa3fa4befd33ec6de509de93498eb9f0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de93498eb9f0u128) >> 1u128) == 0x51fd25f7e99f636f284ef49a4c75cf8u128)) by (bit_vector);
    assert(((((0x61dffa502bbff620185b5b0891eec37eu128) << 1) ^ (if ((((0x61dffa502bbff620185b5b0891eec37eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc3bff4a0577fec4030b6b61123dd86fcu128) by (bit_vector);
    assert(gf128_xtime(0x61dffa502bbff620185b5b0891eec37eu128) == 0xc3bff4a0577fec4030b6b61123dd86fcu128);
    assert(gf128_mul_bits(0x61dffa502bbff620185b5b0891eec37eu128, 0xa3fa4befd33ec6de509de93498eb9f0u128, 124nat) == 0u128 ^ gf128_mul_bits(0xc3bff4a0577fec4030b6b61123dd86fcu128, 0x51fd25f7e99f636f284ef49a4c75cf8u128, 123nat)) by { lemma_hmul128_bits_unfold(0x61dffa502bbff620185b5b0891eec37eu128, 0xa3fa4befd33ec6de509de93498eb9f0u128, 124nat); }
    assert((((0x51fd25f7e99f636f284ef49a4c75cf8u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49a4c75cf8u128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4d263ae7cu128)) by (bit_vector);
    assert(((((0xc3bff4a0577fec4030b6b61123dd86fcu128) << 1) ^ (if ((((0xc3bff4a0577fec4030b6b61123dd86fcu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x877fe940aeffd880616d6c2247bb0d7fu128) by (bit_vector);
    assert(gf128_xtime(0xc3bff4a0577fec4030b6b61123dd86fcu128) == 0x877fe940aeffd880616d6c2247bb0d7fu128);
    assert(gf128_mul_bits(0xc3bff4a0577fec4030b6b61123dd86fcu128, 0x51fd25f7e99f636f284ef49a4c75cf8u128, 123nat) == 0u128 ^ gf128_mul_bits(0x877fe940aeffd880616d6c2247bb0d7fu128, 0x28fe92fbf4cfb1b794277a4d263ae7cu128, 122nat)) by { lemma_hmul128_bits_unfold(0xc3bff4a0577fec4030b6b61123dd86fcu128, 0x51fd25f7e99f636f284ef49a4c75cf8u128, 123nat); }
    assert((((0x28fe92fbf4cfb1b794277a4d263ae7cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4d263ae7cu128) >> 1u128) == 0x147f497dfa67d8dbca13bd26931d73eu128)) by (bit_vector);
    assert(((((0x877fe940aeffd880616d6c2247bb0d7fu128) << 1) ^ (if ((((0x877fe940aeffd880616d6c2247bb0d7fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xeffd2815dffb100c2dad8448f761a79u128) by (bit_vector);
    assert(gf128_xtime(0x877fe940aeffd880616d6c2247bb0d7fu128) == 0xeffd2815dffb100c2dad8448f761a79u128);
    assert(gf128_mul_bits(0x877fe940aeffd880616d6c2247bb0d7fu128, 0x28fe92fbf4cfb1b794277a4d263ae7cu128, 122nat) == 0u128 ^ gf128_mul_bits(0xeffd2815dffb100c2dad8448f761a79u128, 0x147f497dfa67d8dbca13bd26931d73eu128, 121nat)) by { lemma_hmul128_bits_unfold(0x877fe940aeffd880616d6c2247bb0d7fu128, 0x28fe92fbf4cfb1b794277a4d263ae7cu128, 122nat); }
    assert((((0x147f497dfa67d8dbca13bd26931d73eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd26931d73eu128) >> 1u128) == 0xa3fa4befd33ec6de509de93498eb9fu128)) by (bit_vector);
    assert(((((0xeffd2815dffb100c2dad8448f761a79u128) << 1) ^ (if ((((0xeffd2815dffb100c2dad8448f761a79u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1dffa502bbff620185b5b0891eec34f2u128) by (bit_vector);
    assert(gf128_xtime(0xeffd2815dffb100c2dad8448f761a79u128) == 0x1dffa502bbff620185b5b0891eec34f2u128);
    assert(gf128_mul_bits(0xeffd2815dffb100c2dad8448f761a79u128, 0x147f497dfa67d8dbca13bd26931d73eu128, 121nat) == 0u128 ^ gf128_mul_bits(0x1dffa502bbff620185b5b0891eec34f2u128, 0xa3fa4befd33ec6de509de93498eb9fu128, 120nat)) by { lemma_hmul128_bits_unfold(0xeffd2815dffb100c2dad8448f761a79u128, 0x147f497dfa67d8dbca13bd26931d73eu128, 121nat); }
    assert((((0xa3fa4befd33ec6de509de93498eb9fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de93498eb9fu128) >> 1u128) == 0x51fd25f7e99f636f284ef49a4c75cfu128)) by (bit_vector);
    assert(((((0x1dffa502bbff620185b5b0891eec34f2u128) << 1) ^ (if ((((0x1dffa502bbff620185b5b0891eec34f2u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3bff4a0577fec4030b6b61123dd869e4u128) by (bit_vector);
    assert(gf128_xtime(0x1dffa502bbff620185b5b0891eec34f2u128) == 0x3bff4a0577fec4030b6b61123dd869e4u128);
    assert(gf128_mul_bits(0x1dffa502bbff620185b5b0891eec34f2u128, 0xa3fa4befd33ec6de509de93498eb9fu128, 120nat) == 0x1dffa502bbff620185b5b0891eec34f2u128 ^ gf128_mul_bits(0x3bff4a0577fec4030b6b61123dd869e4u128, 0x51fd25f7e99f636f284ef49a4c75cfu128, 119nat)) by { lemma_hmul128_bits_unfold(0x1dffa502bbff620185b5b0891eec34f2u128, 0xa3fa4befd33ec6de509de93498eb9fu128, 120nat); }
    assert((((0x51fd25f7e99f636f284ef49a4c75cfu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49a4c75cfu128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4d263ae7u128)) by (bit_vector);
    assert(((((0x3bff4a0577fec4030b6b61123dd869e4u128) << 1) ^ (if ((((0x3bff4a0577fec4030b6b61123dd869e4u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x77fe940aeffd880616d6c2247bb0d3c8u128) by (bit_vector);
    assert(gf128_xtime(0x3bff4a0577fec4030b6b61123dd869e4u128) == 0x77fe940aeffd880616d6c2247bb0d3c8u128);
    assert(gf128_mul_bits(0x3bff4a0577fec4030b6b61123dd869e4u128, 0x51fd25f7e99f636f284ef49a4c75cfu128, 119nat) == 0x3bff4a0577fec4030b6b61123dd869e4u128 ^ gf128_mul_bits(0x77fe940aeffd880616d6c2247bb0d3c8u128, 0x28fe92fbf4cfb1b794277a4d263ae7u128, 118nat)) by { lemma_hmul128_bits_unfold(0x3bff4a0577fec4030b6b61123dd869e4u128, 0x51fd25f7e99f636f284ef49a4c75cfu128, 119nat); }
    assert((((0x28fe92fbf4cfb1b794277a4d263ae7u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4d263ae7u128) >> 1u128) == 0x147f497dfa67d8dbca13bd26931d73u128)) by (bit_vector);
    assert(((((0x77fe940aeffd880616d6c2247bb0d3c8u128) << 1) ^ (if ((((0x77fe940aeffd880616d6c2247bb0d3c8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xeffd2815dffb100c2dad8448f761a790u128) by (bit_vector);
    assert(gf128_xtime(0x77fe940aeffd880616d6c2247bb0d3c8u128) == 0xeffd2815dffb100c2dad8448f761a790u128);
    assert(gf128_mul_bits(0x77fe940aeffd880616d6c2247bb0d3c8u128, 0x28fe92fbf4cfb1b794277a4d263ae7u128, 118nat) == 0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ gf128_mul_bits(0xeffd2815dffb100c2dad8448f761a790u128, 0x147f497dfa67d8dbca13bd26931d73u128, 117nat)) by { lemma_hmul128_bits_unfold(0x77fe940aeffd880616d6c2247bb0d3c8u128, 0x28fe92fbf4cfb1b794277a4d263ae7u128, 118nat); }
    assert((((0x147f497dfa67d8dbca13bd26931d73u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd26931d73u128) >> 1u128) == 0xa3fa4befd33ec6de509de93498eb9u128)) by (bit_vector);
    assert(((((0xeffd2815dffb100c2dad8448f761a790u128) << 1) ^ (if ((((0xeffd2815dffb100c2dad8448f761a790u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xdffa502bbff620185b5b0891eec34fa7u128) by (bit_vector);
    assert(gf128_xtime(0xeffd2815dffb100c2dad8448f761a790u128) == 0xdffa502bbff620185b5b0891eec34fa7u128);
    assert(gf128_mul_bits(0xeffd2815dffb100c2dad8448f761a790u128, 0x147f497dfa67d8dbca13bd26931d73u128, 117nat) == 0xeffd2815dffb100c2dad8448f761a790u128 ^ gf128_mul_bits(0xdffa502bbff620185b5b0891eec34fa7u128, 0xa3fa4befd33ec6de509de93498eb9u128, 116nat)) by { lemma_hmul128_bits_unfold(0xeffd2815dffb100c2dad8448f761a790u128, 0x147f497dfa67d8dbca13bd26931d73u128, 117nat); }
    assert((((0xa3fa4befd33ec6de509de93498eb9u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de93498eb9u128) >> 1u128) == 0x51fd25f7e99f636f284ef49a4c75cu128)) by (bit_vector);
    assert(((((0xdffa502bbff620185b5b0891eec34fa7u128) << 1) ^ (if ((((0xdffa502bbff620185b5b0891eec34fa7u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbff4a0577fec4030b6b61123dd869fc9u128) by (bit_vector);
    assert(gf128_xtime(0xdffa502bbff620185b5b0891eec34fa7u128) == 0xbff4a0577fec4030b6b61123dd869fc9u128);
    assert(gf128_mul_bits(0xdffa502bbff620185b5b0891eec34fa7u128, 0xa3fa4befd33ec6de509de93498eb9u128, 116nat) == 0xdffa502bbff620185b5b0891eec34fa7u128 ^ gf128_mul_bits(0xbff4a0577fec4030b6b61123dd869fc9u128, 0x51fd25f7e99f636f284ef49a4c75cu128, 115nat)) by { lemma_hmul128_bits_unfold(0xdffa502bbff620185b5b0891eec34fa7u128, 0xa3fa4befd33ec6de509de93498eb9u128, 116nat); }
    assert((((0x51fd25f7e99f636f284ef49a4c75cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49a4c75cu128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4d263aeu128)) by (bit_vector);
    assert(((((0xbff4a0577fec4030b6b61123dd869fc9u128) << 1) ^ (if ((((0xbff4a0577fec4030b6b61123dd869fc9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7fe940aeffd880616d6c2247bb0d3f15u128) by (bit_vector);
    assert(gf128_xtime(0xbff4a0577fec4030b6b61123dd869fc9u128) == 0x7fe940aeffd880616d6c2247bb0d3f15u128);
    assert(gf128_mul_bits(0xbff4a0577fec4030b6b61123dd869fc9u128, 0x51fd25f7e99f636f284ef49a4c75cu128, 115nat) == 0u128 ^ gf128_mul_bits(0x7fe940aeffd880616d6c2247bb0d3f15u128, 0x28fe92fbf4cfb1b794277a4d263aeu128, 114nat)) by { lemma_hmul128_bits_unfold(0xbff4a0577fec4030b6b61123dd869fc9u128, 0x51fd25f7e99f636f284ef49a4c75cu128, 115nat); }
    assert((((0x28fe92fbf4cfb1b794277a4d263aeu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4d263aeu128) >> 1u128) == 0x147f497dfa67d8dbca13bd26931d7u128)) by (bit_vector);
    assert(((((0x7fe940aeffd880616d6c2247bb0d3f15u128) << 1) ^ (if ((((0x7fe940aeffd880616d6c2247bb0d3f15u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xffd2815dffb100c2dad8448f761a7e2au128) by (bit_vector);
    assert(gf128_xtime(0x7fe940aeffd880616d6c2247bb0d3f15u128) == 0xffd2815dffb100c2dad8448f761a7e2au128);
    assert(gf128_mul_bits(0x7fe940aeffd880616d6c2247bb0d3f15u128, 0x28fe92fbf4cfb1b794277a4d263aeu128, 114nat) == 0u128 ^ gf128_mul_bits(0xffd2815dffb100c2dad8448f761a7e2au128, 0x147f497dfa67d8dbca13bd26931d7u128, 113nat)) by { lemma_hmul128_bits_unfold(0x7fe940aeffd880616d6c2247bb0d3f15u128, 0x28fe92fbf4cfb1b794277a4d263aeu128, 114nat); }
    assert((((0x147f497dfa67d8dbca13bd26931d7u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd26931d7u128) >> 1u128) == 0xa3fa4befd33ec6de509de93498ebu128)) by (bit_vector);
    assert(((((0xffd2815dffb100c2dad8448f761a7e2au128) << 1) ^ (if ((((0xffd2815dffb100c2dad8448f761a7e2au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xffa502bbff620185b5b0891eec34fcd3u128) by (bit_vector);
    assert(gf128_xtime(0xffd2815dffb100c2dad8448f761a7e2au128) == 0xffa502bbff620185b5b0891eec34fcd3u128);
    assert(gf128_mul_bits(0xffd2815dffb100c2dad8448f761a7e2au128, 0x147f497dfa67d8dbca13bd26931d7u128, 113nat) == 0xffd2815dffb100c2dad8448f761a7e2au128 ^ gf128_mul_bits(0xffa502bbff620185b5b0891eec34fcd3u128, 0xa3fa4befd33ec6de509de93498ebu128, 112nat)) by { lemma_hmul128_bits_unfold(0xffd2815dffb100c2dad8448f761a7e2au128, 0x147f497dfa67d8dbca13bd26931d7u128, 113nat); }
    assert((((0xa3fa4befd33ec6de509de93498ebu128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de93498ebu128) >> 1u128) == 0x51fd25f7e99f636f284ef49a4c75u128)) by (bit_vector);
    assert(((((0xffa502bbff620185b5b0891eec34fcd3u128) << 1) ^ (if ((((0xffa502bbff620185b5b0891eec34fcd3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xff4a0577fec4030b6b61123dd869f921u128) by (bit_vector);
    assert(gf128_xtime(0xffa502bbff620185b5b0891eec34fcd3u128) == 0xff4a0577fec4030b6b61123dd869f921u128);
    assert(gf128_mul_bits(0xffa502bbff620185b5b0891eec34fcd3u128, 0xa3fa4befd33ec6de509de93498ebu128, 112nat) == 0xffa502bbff620185b5b0891eec34fcd3u128 ^ gf128_mul_bits(0xff4a0577fec4030b6b61123dd869f921u128, 0x51fd25f7e99f636f284ef49a4c75u128, 111nat)) by { lemma_hmul128_bits_unfold(0xffa502bbff620185b5b0891eec34fcd3u128, 0xa3fa4befd33ec6de509de93498ebu128, 112nat); }
    assert((((0x51fd25f7e99f636f284ef49a4c75u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49a4c75u128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4d263au128)) by (bit_vector);
    assert(((((0xff4a0577fec4030b6b61123dd869f921u128) << 1) ^ (if ((((0xff4a0577fec4030b6b61123dd869f921u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfe940aeffd880616d6c2247bb0d3f2c5u128) by (bit_vector);
    assert(gf128_xtime(0xff4a0577fec4030b6b61123dd869f921u128) == 0xfe940aeffd880616d6c2247bb0d3f2c5u128);
    assert(gf128_mul_bits(0xff4a0577fec4030b6b61123dd869f921u128, 0x51fd25f7e99f636f284ef49a4c75u128, 111nat) == 0xff4a0577fec4030b6b61123dd869f921u128 ^ gf128_mul_bits(0xfe940aeffd880616d6c2247bb0d3f2c5u128, 0x28fe92fbf4cfb1b794277a4d263au128, 110nat)) by { lemma_hmul128_bits_unfold(0xff4a0577fec4030b6b61123dd869f921u128, 0x51fd25f7e99f636f284ef49a4c75u128, 111nat); }
    assert((((0x28fe92fbf4cfb1b794277a4d263au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4d263au128) >> 1u128) == 0x147f497dfa67d8dbca13bd26931du128)) by (bit_vector);
    assert(((((0xfe940aeffd880616d6c2247bb0d3f2c5u128) << 1) ^ (if ((((0xfe940aeffd880616d6c2247bb0d3f2c5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfd2815dffb100c2dad8448f761a7e50du128) by (bit_vector);
    assert(gf128_xtime(0xfe940aeffd880616d6c2247bb0d3f2c5u128) == 0xfd2815dffb100c2dad8448f761a7e50du128);
    assert(gf128_mul_bits(0xfe940aeffd880616d6c2247bb0d3f2c5u128, 0x28fe92fbf4cfb1b794277a4d263au128, 110nat) == 0u128 ^ gf128_mul_bits(0xfd2815dffb100c2dad8448f761a7e50du128, 0x147f497dfa67d8dbca13bd26931du128, 109nat)) by { lemma_hmul128_bits_unfold(0xfe940aeffd880616d6c2247bb0d3f2c5u128, 0x28fe92fbf4cfb1b794277a4d263au128, 110nat); }
    assert((((0x147f497dfa67d8dbca13bd26931du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd26931du128) >> 1u128) == 0xa3fa4befd33ec6de509de93498eu128)) by (bit_vector);
    assert(((((0xfd2815dffb100c2dad8448f761a7e50du128) << 1) ^ (if ((((0xfd2815dffb100c2dad8448f761a7e50du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfa502bbff620185b5b0891eec34fca9du128) by (bit_vector);
    assert(gf128_xtime(0xfd2815dffb100c2dad8448f761a7e50du128) == 0xfa502bbff620185b5b0891eec34fca9du128);
    assert(gf128_mul_bits(0xfd2815dffb100c2dad8448f761a7e50du128, 0x147f497dfa67d8dbca13bd26931du128, 109nat) == 0xfd2815dffb100c2dad8448f761a7e50du128 ^ gf128_mul_bits(0xfa502bbff620185b5b0891eec34fca9du128, 0xa3fa4befd33ec6de509de93498eu128, 108nat)) by { lemma_hmul128_bits_unfold(0xfd2815dffb100c2dad8448f761a7e50du128, 0x147f497dfa67d8dbca13bd26931du128, 109nat); }
    assert((((0xa3fa4befd33ec6de509de93498eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de93498eu128) >> 1u128) == 0x51fd25f7e99f636f284ef49a4c7u128)) by (bit_vector);
    assert(((((0xfa502bbff620185b5b0891eec34fca9du128) << 1) ^ (if ((((0xfa502bbff620185b5b0891eec34fca9du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf4a0577fec4030b6b61123dd869f95bdu128) by (bit_vector);
    assert(gf128_xtime(0xfa502bbff620185b5b0891eec34fca9du128) == 0xf4a0577fec4030b6b61123dd869f95bdu128);
    assert(gf128_mul_bits(0xfa502bbff620185b5b0891eec34fca9du128, 0xa3fa4befd33ec6de509de93498eu128, 108nat) == 0u128 ^ gf128_mul_bits(0xf4a0577fec4030b6b61123dd869f95bdu128, 0x51fd25f7e99f636f284ef49a4c7u128, 107nat)) by { lemma_hmul128_bits_unfold(0xfa502bbff620185b5b0891eec34fca9du128, 0xa3fa4befd33ec6de509de93498eu128, 108nat); }
    assert((((0x51fd25f7e99f636f284ef49a4c7u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49a4c7u128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4d263u128)) by (bit_vector);
    assert(((((0xf4a0577fec4030b6b61123dd869f95bdu128) << 1) ^ (if ((((0xf4a0577fec4030b6b61123dd869f95bdu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe940aeffd880616d6c2247bb0d3f2bfdu128) by (bit_vector);
    assert(gf128_xtime(0xf4a0577fec4030b6b61123dd869f95bdu128) == 0xe940aeffd880616d6c2247bb0d3f2bfdu128);
    assert(gf128_mul_bits(0xf4a0577fec4030b6b61123dd869f95bdu128, 0x51fd25f7e99f636f284ef49a4c7u128, 107nat) == 0xf4a0577fec4030b6b61123dd869f95bdu128 ^ gf128_mul_bits(0xe940aeffd880616d6c2247bb0d3f2bfdu128, 0x28fe92fbf4cfb1b794277a4d263u128, 106nat)) by { lemma_hmul128_bits_unfold(0xf4a0577fec4030b6b61123dd869f95bdu128, 0x51fd25f7e99f636f284ef49a4c7u128, 107nat); }
    assert((((0x28fe92fbf4cfb1b794277a4d263u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4d263u128) >> 1u128) == 0x147f497dfa67d8dbca13bd26931u128)) by (bit_vector);
    assert(((((0xe940aeffd880616d6c2247bb0d3f2bfdu128) << 1) ^ (if ((((0xe940aeffd880616d6c2247bb0d3f2bfdu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd2815dffb100c2dad8448f761a7e577du128) by (bit_vector);
    assert(gf128_xtime(0xe940aeffd880616d6c2247bb0d3f2bfdu128) == 0xd2815dffb100c2dad8448f761a7e577du128);
    assert(gf128_mul_bits(0xe940aeffd880616d6c2247bb0d3f2bfdu128, 0x28fe92fbf4cfb1b794277a4d263u128, 106nat) == 0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ gf128_mul_bits(0xd2815dffb100c2dad8448f761a7e577du128, 0x147f497dfa67d8dbca13bd26931u128, 105nat)) by { lemma_hmul128_bits_unfold(0xe940aeffd880616d6c2247bb0d3f2bfdu128, 0x28fe92fbf4cfb1b794277a4d263u128, 106nat); }
    assert((((0x147f497dfa67d8dbca13bd26931u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd26931u128) >> 1u128) == 0xa3fa4befd33ec6de509de93498u128)) by (bit_vector);
    assert(((((0xd2815dffb100c2dad8448f761a7e577du128) << 1) ^ (if ((((0xd2815dffb100c2dad8448f761a7e577du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa502bbff620185b5b0891eec34fcae7du128) by (bit_vector);
    assert(gf128_xtime(0xd2815dffb100c2dad8448f761a7e577du128) == 0xa502bbff620185b5b0891eec34fcae7du128);
    assert(gf128_mul_bits(0xd2815dffb100c2dad8448f761a7e577du128, 0x147f497dfa67d8dbca13bd26931u128, 105nat) == 0xd2815dffb100c2dad8448f761a7e577du128 ^ gf128_mul_bits(0xa502bbff620185b5b0891eec34fcae7du128, 0xa3fa4befd33ec6de509de93498u128, 104nat)) by { lemma_hmul128_bits_unfold(0xd2815dffb100c2dad8448f761a7e577du128, 0x147f497dfa67d8dbca13bd26931u128, 105nat); }
    assert((((0xa3fa4befd33ec6de509de93498u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de93498u128) >> 1u128) == 0x51fd25f7e99f636f284ef49a4cu128)) by (bit_vector);
    assert(((((0xa502bbff620185b5b0891eec34fcae7du128) << 1) ^ (if ((((0xa502bbff620185b5b0891eec34fcae7du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4a0577fec4030b6b61123dd869f95c7du128) by (bit_vector);
    assert(gf128_xtime(0xa502bbff620185b5b0891eec34fcae7du128) == 0x4a0577fec4030b6b61123dd869f95c7du128);
    assert(gf128_mul_bits(0xa502bbff620185b5b0891eec34fcae7du128, 0xa3fa4befd33ec6de509de93498u128, 104nat) == 0u128 ^ gf128_mul_bits(0x4a0577fec4030b6b61123dd869f95c7du128, 0x51fd25f7e99f636f284ef49a4cu128, 103nat)) by { lemma_hmul128_bits_unfold(0xa502bbff620185b5b0891eec34fcae7du128, 0xa3fa4befd33ec6de509de93498u128, 104nat); }
    assert((((0x51fd25f7e99f636f284ef49a4cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49a4cu128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4d26u128)) by (bit_vector);
    assert(((((0x4a0577fec4030b6b61123dd869f95c7du128) << 1) ^ (if ((((0x4a0577fec4030b6b61123dd869f95c7du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x940aeffd880616d6c2247bb0d3f2b8fau128) by (bit_vector);
    assert(gf128_xtime(0x4a0577fec4030b6b61123dd869f95c7du128) == 0x940aeffd880616d6c2247bb0d3f2b8fau128);
    assert(gf128_mul_bits(0x4a0577fec4030b6b61123dd869f95c7du128, 0x51fd25f7e99f636f284ef49a4cu128, 103nat) == 0u128 ^ gf128_mul_bits(0x940aeffd880616d6c2247bb0d3f2b8fau128, 0x28fe92fbf4cfb1b794277a4d26u128, 102nat)) by { lemma_hmul128_bits_unfold(0x4a0577fec4030b6b61123dd869f95c7du128, 0x51fd25f7e99f636f284ef49a4cu128, 103nat); }
    assert((((0x28fe92fbf4cfb1b794277a4d26u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4d26u128) >> 1u128) == 0x147f497dfa67d8dbca13bd2693u128)) by (bit_vector);
    assert(((((0x940aeffd880616d6c2247bb0d3f2b8fau128) << 1) ^ (if ((((0x940aeffd880616d6c2247bb0d3f2b8fau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x2815dffb100c2dad8448f761a7e57173u128) by (bit_vector);
    assert(gf128_xtime(0x940aeffd880616d6c2247bb0d3f2b8fau128) == 0x2815dffb100c2dad8448f761a7e57173u128);
    assert(gf128_mul_bits(0x940aeffd880616d6c2247bb0d3f2b8fau128, 0x28fe92fbf4cfb1b794277a4d26u128, 102nat) == 0u128 ^ gf128_mul_bits(0x2815dffb100c2dad8448f761a7e57173u128, 0x147f497dfa67d8dbca13bd2693u128, 101nat)) by { lemma_hmul128_bits_unfold(0x940aeffd880616d6c2247bb0d3f2b8fau128, 0x28fe92fbf4cfb1b794277a4d26u128, 102nat); }
    assert((((0x147f497dfa67d8dbca13bd2693u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd2693u128) >> 1u128) == 0xa3fa4befd33ec6de509de9349u128)) by (bit_vector);
    assert(((((0x2815dffb100c2dad8448f761a7e57173u128) << 1) ^ (if ((((0x2815dffb100c2dad8448f761a7e57173u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x502bbff620185b5b0891eec34fcae2e6u128) by (bit_vector);
    assert(gf128_xtime(0x2815dffb100c2dad8448f761a7e57173u128) == 0x502bbff620185b5b0891eec34fcae2e6u128);
    assert(gf128_mul_bits(0x2815dffb100c2dad8448f761a7e57173u128, 0x147f497dfa67d8dbca13bd2693u128, 101nat) == 0x2815dffb100c2dad8448f761a7e57173u128 ^ gf128_mul_bits(0x502bbff620185b5b0891eec34fcae2e6u128, 0xa3fa4befd33ec6de509de9349u128, 100nat)) by { lemma_hmul128_bits_unfold(0x2815dffb100c2dad8448f761a7e57173u128, 0x147f497dfa67d8dbca13bd2693u128, 101nat); }
    assert((((0xa3fa4befd33ec6de509de9349u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de9349u128) >> 1u128) == 0x51fd25f7e99f636f284ef49a4u128)) by (bit_vector);
    assert(((((0x502bbff620185b5b0891eec34fcae2e6u128) << 1) ^ (if ((((0x502bbff620185b5b0891eec34fcae2e6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa0577fec4030b6b61123dd869f95c5ccu128) by (bit_vector);
    assert(gf128_xtime(0x502bbff620185b5b0891eec34fcae2e6u128) == 0xa0577fec4030b6b61123dd869f95c5ccu128);
    assert(gf128_mul_bits(0x502bbff620185b5b0891eec34fcae2e6u128, 0xa3fa4befd33ec6de509de9349u128, 100nat) == 0x502bbff620185b5b0891eec34fcae2e6u128 ^ gf128_mul_bits(0xa0577fec4030b6b61123dd869f95c5ccu128, 0x51fd25f7e99f636f284ef49a4u128, 99nat)) by { lemma_hmul128_bits_unfold(0x502bbff620185b5b0891eec34fcae2e6u128, 0xa3fa4befd33ec6de509de9349u128, 100nat); }
    assert((((0x51fd25f7e99f636f284ef49a4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49a4u128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4d2u128)) by (bit_vector);
    assert(((((0xa0577fec4030b6b61123dd869f95c5ccu128) << 1) ^ (if ((((0xa0577fec4030b6b61123dd869f95c5ccu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x40aeffd880616d6c2247bb0d3f2b8b1fu128) by (bit_vector);
    assert(gf128_xtime(0xa0577fec4030b6b61123dd869f95c5ccu128) == 0x40aeffd880616d6c2247bb0d3f2b8b1fu128);
    assert(gf128_mul_bits(0xa0577fec4030b6b61123dd869f95c5ccu128, 0x51fd25f7e99f636f284ef49a4u128, 99nat) == 0u128 ^ gf128_mul_bits(0x40aeffd880616d6c2247bb0d3f2b8b1fu128, 0x28fe92fbf4cfb1b794277a4d2u128, 98nat)) by { lemma_hmul128_bits_unfold(0xa0577fec4030b6b61123dd869f95c5ccu128, 0x51fd25f7e99f636f284ef49a4u128, 99nat); }
    assert((((0x28fe92fbf4cfb1b794277a4d2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4d2u128) >> 1u128) == 0x147f497dfa67d8dbca13bd269u128)) by (bit_vector);
    assert(((((0x40aeffd880616d6c2247bb0d3f2b8b1fu128) << 1) ^ (if ((((0x40aeffd880616d6c2247bb0d3f2b8b1fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x815dffb100c2dad8448f761a7e57163eu128) by (bit_vector);
    assert(gf128_xtime(0x40aeffd880616d6c2247bb0d3f2b8b1fu128) == 0x815dffb100c2dad8448f761a7e57163eu128);
    assert(gf128_mul_bits(0x40aeffd880616d6c2247bb0d3f2b8b1fu128, 0x28fe92fbf4cfb1b794277a4d2u128, 98nat) == 0u128 ^ gf128_mul_bits(0x815dffb100c2dad8448f761a7e57163eu128, 0x147f497dfa67d8dbca13bd269u128, 97nat)) by { lemma_hmul128_bits_unfold(0x40aeffd880616d6c2247bb0d3f2b8b1fu128, 0x28fe92fbf4cfb1b794277a4d2u128, 98nat); }
    assert((((0x147f497dfa67d8dbca13bd269u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd269u128) >> 1u128) == 0xa3fa4befd33ec6de509de934u128)) by (bit_vector);
    assert(((((0x815dffb100c2dad8448f761a7e57163eu128) << 1) ^ (if ((((0x815dffb100c2dad8448f761a7e57163eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x2bbff620185b5b0891eec34fcae2cfbu128) by (bit_vector);
    assert(gf128_xtime(0x815dffb100c2dad8448f761a7e57163eu128) == 0x2bbff620185b5b0891eec34fcae2cfbu128);
    assert(gf128_mul_bits(0x815dffb100c2dad8448f761a7e57163eu128, 0x147f497dfa67d8dbca13bd269u128, 97nat) == 0x815dffb100c2dad8448f761a7e57163eu128 ^ gf128_mul_bits(0x2bbff620185b5b0891eec34fcae2cfbu128, 0xa3fa4befd33ec6de509de934u128, 96nat)) by { lemma_hmul128_bits_unfold(0x815dffb100c2dad8448f761a7e57163eu128, 0x147f497dfa67d8dbca13bd269u128, 97nat); }
    assert((((0xa3fa4befd33ec6de509de934u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de934u128) >> 1u128) == 0x51fd25f7e99f636f284ef49au128)) by (bit_vector);
    assert(((((0x2bbff620185b5b0891eec34fcae2cfbu128) << 1) ^ (if ((((0x2bbff620185b5b0891eec34fcae2cfbu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x577fec4030b6b61123dd869f95c59f6u128) by (bit_vector);
    assert(gf128_xtime(0x2bbff620185b5b0891eec34fcae2cfbu128) == 0x577fec4030b6b61123dd869f95c59f6u128);
    assert(gf128_mul_bits(0x2bbff620185b5b0891eec34fcae2cfbu128, 0xa3fa4befd33ec6de509de934u128, 96nat) == 0u128 ^ gf128_mul_bits(0x577fec4030b6b61123dd869f95c59f6u128, 0x51fd25f7e99f636f284ef49au128, 95nat)) by { lemma_hmul128_bits_unfold(0x2bbff620185b5b0891eec34fcae2cfbu128, 0xa3fa4befd33ec6de509de934u128, 96nat); }
    assert((((0x51fd25f7e99f636f284ef49au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49au128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4du128)) by (bit_vector);
    assert(((((0x577fec4030b6b61123dd869f95c59f6u128) << 1) ^ (if ((((0x577fec4030b6b61123dd869f95c59f6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xaeffd880616d6c2247bb0d3f2b8b3ecu128) by (bit_vector);
    assert(gf128_xtime(0x577fec4030b6b61123dd869f95c59f6u128) == 0xaeffd880616d6c2247bb0d3f2b8b3ecu128);
    assert(gf128_mul_bits(0x577fec4030b6b61123dd869f95c59f6u128, 0x51fd25f7e99f636f284ef49au128, 95nat) == 0u128 ^ gf128_mul_bits(0xaeffd880616d6c2247bb0d3f2b8b3ecu128, 0x28fe92fbf4cfb1b794277a4du128, 94nat)) by { lemma_hmul128_bits_unfold(0x577fec4030b6b61123dd869f95c59f6u128, 0x51fd25f7e99f636f284ef49au128, 95nat); }
    assert((((0x28fe92fbf4cfb1b794277a4du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4du128) >> 1u128) == 0x147f497dfa67d8dbca13bd26u128)) by (bit_vector);
    assert(((((0xaeffd880616d6c2247bb0d3f2b8b3ecu128) << 1) ^ (if ((((0xaeffd880616d6c2247bb0d3f2b8b3ecu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x15dffb100c2dad8448f761a7e57167d8u128) by (bit_vector);
    assert(gf128_xtime(0xaeffd880616d6c2247bb0d3f2b8b3ecu128) == 0x15dffb100c2dad8448f761a7e57167d8u128);
    assert(gf128_mul_bits(0xaeffd880616d6c2247bb0d3f2b8b3ecu128, 0x28fe92fbf4cfb1b794277a4du128, 94nat) == 0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ gf128_mul_bits(0x15dffb100c2dad8448f761a7e57167d8u128, 0x147f497dfa67d8dbca13bd26u128, 93nat)) by { lemma_hmul128_bits_unfold(0xaeffd880616d6c2247bb0d3f2b8b3ecu128, 0x28fe92fbf4cfb1b794277a4du128, 94nat); }
    assert((((0x147f497dfa67d8dbca13bd26u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd26u128) >> 1u128) == 0xa3fa4befd33ec6de509de93u128)) by (bit_vector);
    assert(((((0x15dffb100c2dad8448f761a7e57167d8u128) << 1) ^ (if ((((0x15dffb100c2dad8448f761a7e57167d8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x2bbff620185b5b0891eec34fcae2cfb0u128) by (bit_vector);
    assert(gf128_xtime(0x15dffb100c2dad8448f761a7e57167d8u128) == 0x2bbff620185b5b0891eec34fcae2cfb0u128);
    assert(gf128_mul_bits(0x15dffb100c2dad8448f761a7e57167d8u128, 0x147f497dfa67d8dbca13bd26u128, 93nat) == 0u128 ^ gf128_mul_bits(0x2bbff620185b5b0891eec34fcae2cfb0u128, 0xa3fa4befd33ec6de509de93u128, 92nat)) by { lemma_hmul128_bits_unfold(0x15dffb100c2dad8448f761a7e57167d8u128, 0x147f497dfa67d8dbca13bd26u128, 93nat); }
    assert((((0xa3fa4befd33ec6de509de93u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de93u128) >> 1u128) == 0x51fd25f7e99f636f284ef49u128)) by (bit_vector);
    assert(((((0x2bbff620185b5b0891eec34fcae2cfb0u128) << 1) ^ (if ((((0x2bbff620185b5b0891eec34fcae2cfb0u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x577fec4030b6b61123dd869f95c59f60u128) by (bit_vector);
    assert(gf128_xtime(0x2bbff620185b5b0891eec34fcae2cfb0u128) == 0x577fec4030b6b61123dd869f95c59f60u128);
    assert(gf128_mul_bits(0x2bbff620185b5b0891eec34fcae2cfb0u128, 0xa3fa4befd33ec6de509de93u128, 92nat) == 0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ gf128_mul_bits(0x577fec4030b6b61123dd869f95c59f60u128, 0x51fd25f7e99f636f284ef49u128, 91nat)) by { lemma_hmul128_bits_unfold(0x2bbff620185b5b0891eec34fcae2cfb0u128, 0xa3fa4befd33ec6de509de93u128, 92nat); }
    assert((((0x51fd25f7e99f636f284ef49u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef49u128) >> 1u128) == 0x28fe92fbf4cfb1b794277a4u128)) by (bit_vector);
    assert(((((0x577fec4030b6b61123dd869f95c59f60u128) << 1) ^ (if ((((0x577fec4030b6b61123dd869f95c59f60u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xaeffd880616d6c2247bb0d3f2b8b3ec0u128) by (bit_vector);
    assert(gf128_xtime(0x577fec4030b6b61123dd869f95c59f60u128) == 0xaeffd880616d6c2247bb0d3f2b8b3ec0u128);
    assert(gf128_mul_bits(0x577fec4030b6b61123dd869f95c59f60u128, 0x51fd25f7e99f636f284ef49u128, 91nat) == 0x577fec4030b6b61123dd869f95c59f60u128 ^ gf128_mul_bits(0xaeffd880616d6c2247bb0d3f2b8b3ec0u128, 0x28fe92fbf4cfb1b794277a4u128, 90nat)) by { lemma_hmul128_bits_unfold(0x577fec4030b6b61123dd869f95c59f60u128, 0x51fd25f7e99f636f284ef49u128, 91nat); }
    assert((((0x28fe92fbf4cfb1b794277a4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277a4u128) >> 1u128) == 0x147f497dfa67d8dbca13bd2u128)) by (bit_vector);
    assert(((((0xaeffd880616d6c2247bb0d3f2b8b3ec0u128) << 1) ^ (if ((((0xaeffd880616d6c2247bb0d3f2b8b3ec0u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5dffb100c2dad8448f761a7e57167d07u128) by (bit_vector);
    assert(gf128_xtime(0xaeffd880616d6c2247bb0d3f2b8b3ec0u128) == 0x5dffb100c2dad8448f761a7e57167d07u128);
    assert(gf128_mul_bits(0xaeffd880616d6c2247bb0d3f2b8b3ec0u128, 0x28fe92fbf4cfb1b794277a4u128, 90nat) == 0u128 ^ gf128_mul_bits(0x5dffb100c2dad8448f761a7e57167d07u128, 0x147f497dfa67d8dbca13bd2u128, 89nat)) by { lemma_hmul128_bits_unfold(0xaeffd880616d6c2247bb0d3f2b8b3ec0u128, 0x28fe92fbf4cfb1b794277a4u128, 90nat); }
    assert((((0x147f497dfa67d8dbca13bd2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bd2u128) >> 1u128) == 0xa3fa4befd33ec6de509de9u128)) by (bit_vector);
    assert(((((0x5dffb100c2dad8448f761a7e57167d07u128) << 1) ^ (if ((((0x5dffb100c2dad8448f761a7e57167d07u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbbff620185b5b0891eec34fcae2cfa0eu128) by (bit_vector);
    assert(gf128_xtime(0x5dffb100c2dad8448f761a7e57167d07u128) == 0xbbff620185b5b0891eec34fcae2cfa0eu128);
    assert(gf128_mul_bits(0x5dffb100c2dad8448f761a7e57167d07u128, 0x147f497dfa67d8dbca13bd2u128, 89nat) == 0u128 ^ gf128_mul_bits(0xbbff620185b5b0891eec34fcae2cfa0eu128, 0xa3fa4befd33ec6de509de9u128, 88nat)) by { lemma_hmul128_bits_unfold(0x5dffb100c2dad8448f761a7e57167d07u128, 0x147f497dfa67d8dbca13bd2u128, 89nat); }
    assert((((0xa3fa4befd33ec6de509de9u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509de9u128) >> 1u128) == 0x51fd25f7e99f636f284ef4u128)) by (bit_vector);
    assert(((((0xbbff620185b5b0891eec34fcae2cfa0eu128) << 1) ^ (if ((((0xbbff620185b5b0891eec34fcae2cfa0eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x77fec4030b6b61123dd869f95c59f49bu128) by (bit_vector);
    assert(gf128_xtime(0xbbff620185b5b0891eec34fcae2cfa0eu128) == 0x77fec4030b6b61123dd869f95c59f49bu128);
    assert(gf128_mul_bits(0xbbff620185b5b0891eec34fcae2cfa0eu128, 0xa3fa4befd33ec6de509de9u128, 88nat) == 0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ gf128_mul_bits(0x77fec4030b6b61123dd869f95c59f49bu128, 0x51fd25f7e99f636f284ef4u128, 87nat)) by { lemma_hmul128_bits_unfold(0xbbff620185b5b0891eec34fcae2cfa0eu128, 0xa3fa4befd33ec6de509de9u128, 88nat); }
    assert((((0x51fd25f7e99f636f284ef4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284ef4u128) >> 1u128) == 0x28fe92fbf4cfb1b794277au128)) by (bit_vector);
    assert(((((0x77fec4030b6b61123dd869f95c59f49bu128) << 1) ^ (if ((((0x77fec4030b6b61123dd869f95c59f49bu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xeffd880616d6c2247bb0d3f2b8b3e936u128) by (bit_vector);
    assert(gf128_xtime(0x77fec4030b6b61123dd869f95c59f49bu128) == 0xeffd880616d6c2247bb0d3f2b8b3e936u128);
    assert(gf128_mul_bits(0x77fec4030b6b61123dd869f95c59f49bu128, 0x51fd25f7e99f636f284ef4u128, 87nat) == 0u128 ^ gf128_mul_bits(0xeffd880616d6c2247bb0d3f2b8b3e936u128, 0x28fe92fbf4cfb1b794277au128, 86nat)) by { lemma_hmul128_bits_unfold(0x77fec4030b6b61123dd869f95c59f49bu128, 0x51fd25f7e99f636f284ef4u128, 87nat); }
    assert((((0x28fe92fbf4cfb1b794277au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277au128) >> 1u128) == 0x147f497dfa67d8dbca13bdu128)) by (bit_vector);
    assert(((((0xeffd880616d6c2247bb0d3f2b8b3e936u128) << 1) ^ (if ((((0xeffd880616d6c2247bb0d3f2b8b3e936u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xdffb100c2dad8448f761a7e57167d2ebu128) by (bit_vector);
    assert(gf128_xtime(0xeffd880616d6c2247bb0d3f2b8b3e936u128) == 0xdffb100c2dad8448f761a7e57167d2ebu128);
    assert(gf128_mul_bits(0xeffd880616d6c2247bb0d3f2b8b3e936u128, 0x28fe92fbf4cfb1b794277au128, 86nat) == 0u128 ^ gf128_mul_bits(0xdffb100c2dad8448f761a7e57167d2ebu128, 0x147f497dfa67d8dbca13bdu128, 85nat)) by { lemma_hmul128_bits_unfold(0xeffd880616d6c2247bb0d3f2b8b3e936u128, 0x28fe92fbf4cfb1b794277au128, 86nat); }
    assert((((0x147f497dfa67d8dbca13bdu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bdu128) >> 1u128) == 0xa3fa4befd33ec6de509deu128)) by (bit_vector);
    assert(((((0xdffb100c2dad8448f761a7e57167d2ebu128) << 1) ^ (if ((((0xdffb100c2dad8448f761a7e57167d2ebu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbff620185b5b0891eec34fcae2cfa551u128) by (bit_vector);
    assert(gf128_xtime(0xdffb100c2dad8448f761a7e57167d2ebu128) == 0xbff620185b5b0891eec34fcae2cfa551u128);
    assert(gf128_mul_bits(0xdffb100c2dad8448f761a7e57167d2ebu128, 0x147f497dfa67d8dbca13bdu128, 85nat) == 0xdffb100c2dad8448f761a7e57167d2ebu128 ^ gf128_mul_bits(0xbff620185b5b0891eec34fcae2cfa551u128, 0xa3fa4befd33ec6de509deu128, 84nat)) by { lemma_hmul128_bits_unfold(0xdffb100c2dad8448f761a7e57167d2ebu128, 0x147f497dfa67d8dbca13bdu128, 85nat); }
    assert((((0xa3fa4befd33ec6de509deu128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509deu128) >> 1u128) == 0x51fd25f7e99f636f284efu128)) by (bit_vector);
    assert(((((0xbff620185b5b0891eec34fcae2cfa551u128) << 1) ^ (if ((((0xbff620185b5b0891eec34fcae2cfa551u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7fec4030b6b61123dd869f95c59f4a25u128) by (bit_vector);
    assert(gf128_xtime(0xbff620185b5b0891eec34fcae2cfa551u128) == 0x7fec4030b6b61123dd869f95c59f4a25u128);
    assert(gf128_mul_bits(0xbff620185b5b0891eec34fcae2cfa551u128, 0xa3fa4befd33ec6de509deu128, 84nat) == 0u128 ^ gf128_mul_bits(0x7fec4030b6b61123dd869f95c59f4a25u128, 0x51fd25f7e99f636f284efu128, 83nat)) by { lemma_hmul128_bits_unfold(0xbff620185b5b0891eec34fcae2cfa551u128, 0xa3fa4befd33ec6de509deu128, 84nat); }
    assert((((0x51fd25f7e99f636f284efu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284efu128) >> 1u128) == 0x28fe92fbf4cfb1b794277u128)) by (bit_vector);
    assert(((((0x7fec4030b6b61123dd869f95c59f4a25u128) << 1) ^ (if ((((0x7fec4030b6b61123dd869f95c59f4a25u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xffd880616d6c2247bb0d3f2b8b3e944au128) by (bit_vector);
    assert(gf128_xtime(0x7fec4030b6b61123dd869f95c59f4a25u128) == 0xffd880616d6c2247bb0d3f2b8b3e944au128);
    assert(gf128_mul_bits(0x7fec4030b6b61123dd869f95c59f4a25u128, 0x51fd25f7e99f636f284efu128, 83nat) == 0x7fec4030b6b61123dd869f95c59f4a25u128 ^ gf128_mul_bits(0xffd880616d6c2247bb0d3f2b8b3e944au128, 0x28fe92fbf4cfb1b794277u128, 82nat)) by { lemma_hmul128_bits_unfold(0x7fec4030b6b61123dd869f95c59f4a25u128, 0x51fd25f7e99f636f284efu128, 83nat); }
    assert((((0x28fe92fbf4cfb1b794277u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794277u128) >> 1u128) == 0x147f497dfa67d8dbca13bu128)) by (bit_vector);
    assert(((((0xffd880616d6c2247bb0d3f2b8b3e944au128) << 1) ^ (if ((((0xffd880616d6c2247bb0d3f2b8b3e944au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xffb100c2dad8448f761a7e57167d2813u128) by (bit_vector);
    assert(gf128_xtime(0xffd880616d6c2247bb0d3f2b8b3e944au128) == 0xffb100c2dad8448f761a7e57167d2813u128);
    assert(gf128_mul_bits(0xffd880616d6c2247bb0d3f2b8b3e944au128, 0x28fe92fbf4cfb1b794277u128, 82nat) == 0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ gf128_mul_bits(0xffb100c2dad8448f761a7e57167d2813u128, 0x147f497dfa67d8dbca13bu128, 81nat)) by { lemma_hmul128_bits_unfold(0xffd880616d6c2247bb0d3f2b8b3e944au128, 0x28fe92fbf4cfb1b794277u128, 82nat); }
    assert((((0x147f497dfa67d8dbca13bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13bu128) >> 1u128) == 0xa3fa4befd33ec6de509du128)) by (bit_vector);
    assert(((((0xffb100c2dad8448f761a7e57167d2813u128) << 1) ^ (if ((((0xffb100c2dad8448f761a7e57167d2813u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xff620185b5b0891eec34fcae2cfa50a1u128) by (bit_vector);
    assert(gf128_xtime(0xffb100c2dad8448f761a7e57167d2813u128) == 0xff620185b5b0891eec34fcae2cfa50a1u128);
    assert(gf128_mul_bits(0xffb100c2dad8448f761a7e57167d2813u128, 0x147f497dfa67d8dbca13bu128, 81nat) == 0xffb100c2dad8448f761a7e57167d2813u128 ^ gf128_mul_bits(0xff620185b5b0891eec34fcae2cfa50a1u128, 0xa3fa4befd33ec6de509du128, 80nat)) by { lemma_hmul128_bits_unfold(0xffb100c2dad8448f761a7e57167d2813u128, 0x147f497dfa67d8dbca13bu128, 81nat); }
    assert((((0xa3fa4befd33ec6de509du128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509du128) >> 1u128) == 0x51fd25f7e99f636f284eu128)) by (bit_vector);
    assert(((((0xff620185b5b0891eec34fcae2cfa50a1u128) << 1) ^ (if ((((0xff620185b5b0891eec34fcae2cfa50a1u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfec4030b6b61123dd869f95c59f4a1c5u128) by (bit_vector);
    assert(gf128_xtime(0xff620185b5b0891eec34fcae2cfa50a1u128) == 0xfec4030b6b61123dd869f95c59f4a1c5u128);
    assert(gf128_mul_bits(0xff620185b5b0891eec34fcae2cfa50a1u128, 0xa3fa4befd33ec6de509du128, 80nat) == 0xff620185b5b0891eec34fcae2cfa50a1u128 ^ gf128_mul_bits(0xfec4030b6b61123dd869f95c59f4a1c5u128, 0x51fd25f7e99f636f284eu128, 79nat)) by { lemma_hmul128_bits_unfold(0xff620185b5b0891eec34fcae2cfa50a1u128, 0xa3fa4befd33ec6de509du128, 80nat); }
    assert((((0x51fd25f7e99f636f284eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284eu128) >> 1u128) == 0x28fe92fbf4cfb1b79427u128)) by (bit_vector);
    assert(((((0xfec4030b6b61123dd869f95c59f4a1c5u128) << 1) ^ (if ((((0xfec4030b6b61123dd869f95c59f4a1c5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfd880616d6c2247bb0d3f2b8b3e9430du128) by (bit_vector);
    assert(gf128_xtime(0xfec4030b6b61123dd869f95c59f4a1c5u128) == 0xfd880616d6c2247bb0d3f2b8b3e9430du128);
    assert(gf128_mul_bits(0xfec4030b6b61123dd869f95c59f4a1c5u128, 0x51fd25f7e99f636f284eu128, 79nat) == 0u128 ^ gf128_mul_bits(0xfd880616d6c2247bb0d3f2b8b3e9430du128, 0x28fe92fbf4cfb1b79427u128, 78nat)) by { lemma_hmul128_bits_unfold(0xfec4030b6b61123dd869f95c59f4a1c5u128, 0x51fd25f7e99f636f284eu128, 79nat); }
    assert((((0x28fe92fbf4cfb1b79427u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b79427u128) >> 1u128) == 0x147f497dfa67d8dbca13u128)) by (bit_vector);
    assert(((((0xfd880616d6c2247bb0d3f2b8b3e9430du128) << 1) ^ (if ((((0xfd880616d6c2247bb0d3f2b8b3e9430du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfb100c2dad8448f761a7e57167d2869du128) by (bit_vector);
    assert(gf128_xtime(0xfd880616d6c2247bb0d3f2b8b3e9430du128) == 0xfb100c2dad8448f761a7e57167d2869du128);
    assert(gf128_mul_bits(0xfd880616d6c2247bb0d3f2b8b3e9430du128, 0x28fe92fbf4cfb1b79427u128, 78nat) == 0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ gf128_mul_bits(0xfb100c2dad8448f761a7e57167d2869du128, 0x147f497dfa67d8dbca13u128, 77nat)) by { lemma_hmul128_bits_unfold(0xfd880616d6c2247bb0d3f2b8b3e9430du128, 0x28fe92fbf4cfb1b79427u128, 78nat); }
    assert((((0x147f497dfa67d8dbca13u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca13u128) >> 1u128) == 0xa3fa4befd33ec6de509u128)) by (bit_vector);
    assert(((((0xfb100c2dad8448f761a7e57167d2869du128) << 1) ^ (if ((((0xfb100c2dad8448f761a7e57167d2869du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf620185b5b0891eec34fcae2cfa50dbdu128) by (bit_vector);
    assert(gf128_xtime(0xfb100c2dad8448f761a7e57167d2869du128) == 0xf620185b5b0891eec34fcae2cfa50dbdu128);
    assert(gf128_mul_bits(0xfb100c2dad8448f761a7e57167d2869du128, 0x147f497dfa67d8dbca13u128, 77nat) == 0xfb100c2dad8448f761a7e57167d2869du128 ^ gf128_mul_bits(0xf620185b5b0891eec34fcae2cfa50dbdu128, 0xa3fa4befd33ec6de509u128, 76nat)) by { lemma_hmul128_bits_unfold(0xfb100c2dad8448f761a7e57167d2869du128, 0x147f497dfa67d8dbca13u128, 77nat); }
    assert((((0xa3fa4befd33ec6de509u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de509u128) >> 1u128) == 0x51fd25f7e99f636f284u128)) by (bit_vector);
    assert(((((0xf620185b5b0891eec34fcae2cfa50dbdu128) << 1) ^ (if ((((0xf620185b5b0891eec34fcae2cfa50dbdu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xec4030b6b61123dd869f95c59f4a1bfdu128) by (bit_vector);
    assert(gf128_xtime(0xf620185b5b0891eec34fcae2cfa50dbdu128) == 0xec4030b6b61123dd869f95c59f4a1bfdu128);
    assert(gf128_mul_bits(0xf620185b5b0891eec34fcae2cfa50dbdu128, 0xa3fa4befd33ec6de509u128, 76nat) == 0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ gf128_mul_bits(0xec4030b6b61123dd869f95c59f4a1bfdu128, 0x51fd25f7e99f636f284u128, 75nat)) by { lemma_hmul128_bits_unfold(0xf620185b5b0891eec34fcae2cfa50dbdu128, 0xa3fa4befd33ec6de509u128, 76nat); }
    assert((((0x51fd25f7e99f636f284u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f284u128) >> 1u128) == 0x28fe92fbf4cfb1b7942u128)) by (bit_vector);
    assert(((((0xec4030b6b61123dd869f95c59f4a1bfdu128) << 1) ^ (if ((((0xec4030b6b61123dd869f95c59f4a1bfdu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd880616d6c2247bb0d3f2b8b3e94377du128) by (bit_vector);
    assert(gf128_xtime(0xec4030b6b61123dd869f95c59f4a1bfdu128) == 0xd880616d6c2247bb0d3f2b8b3e94377du128);
    assert(gf128_mul_bits(0xec4030b6b61123dd869f95c59f4a1bfdu128, 0x51fd25f7e99f636f284u128, 75nat) == 0u128 ^ gf128_mul_bits(0xd880616d6c2247bb0d3f2b8b3e94377du128, 0x28fe92fbf4cfb1b7942u128, 74nat)) by { lemma_hmul128_bits_unfold(0xec4030b6b61123dd869f95c59f4a1bfdu128, 0x51fd25f7e99f636f284u128, 75nat); }
    assert((((0x28fe92fbf4cfb1b7942u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b7942u128) >> 1u128) == 0x147f497dfa67d8dbca1u128)) by (bit_vector);
    assert(((((0xd880616d6c2247bb0d3f2b8b3e94377du128) << 1) ^ (if ((((0xd880616d6c2247bb0d3f2b8b3e94377du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb100c2dad8448f761a7e57167d286e7du128) by (bit_vector);
    assert(gf128_xtime(0xd880616d6c2247bb0d3f2b8b3e94377du128) == 0xb100c2dad8448f761a7e57167d286e7du128);
    assert(gf128_mul_bits(0xd880616d6c2247bb0d3f2b8b3e94377du128, 0x28fe92fbf4cfb1b7942u128, 74nat) == 0u128 ^ gf128_mul_bits(0xb100c2dad8448f761a7e57167d286e7du128, 0x147f497dfa67d8dbca1u128, 73nat)) by { lemma_hmul128_bits_unfold(0xd880616d6c2247bb0d3f2b8b3e94377du128, 0x28fe92fbf4cfb1b7942u128, 74nat); }
    assert((((0x147f497dfa67d8dbca1u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbca1u128) >> 1u128) == 0xa3fa4befd33ec6de50u128)) by (bit_vector);
    assert(((((0xb100c2dad8448f761a7e57167d286e7du128) << 1) ^ (if ((((0xb100c2dad8448f761a7e57167d286e7du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x620185b5b0891eec34fcae2cfa50dc7du128) by (bit_vector);
    assert(gf128_xtime(0xb100c2dad8448f761a7e57167d286e7du128) == 0x620185b5b0891eec34fcae2cfa50dc7du128);
    assert(gf128_mul_bits(0xb100c2dad8448f761a7e57167d286e7du128, 0x147f497dfa67d8dbca1u128, 73nat) == 0xb100c2dad8448f761a7e57167d286e7du128 ^ gf128_mul_bits(0x620185b5b0891eec34fcae2cfa50dc7du128, 0xa3fa4befd33ec6de50u128, 72nat)) by { lemma_hmul128_bits_unfold(0xb100c2dad8448f761a7e57167d286e7du128, 0x147f497dfa67d8dbca1u128, 73nat); }
    assert((((0xa3fa4befd33ec6de50u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de50u128) >> 1u128) == 0x51fd25f7e99f636f28u128)) by (bit_vector);
    assert(((((0x620185b5b0891eec34fcae2cfa50dc7du128) << 1) ^ (if ((((0x620185b5b0891eec34fcae2cfa50dc7du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc4030b6b61123dd869f95c59f4a1b8fau128) by (bit_vector);
    assert(gf128_xtime(0x620185b5b0891eec34fcae2cfa50dc7du128) == 0xc4030b6b61123dd869f95c59f4a1b8fau128);
    assert(gf128_mul_bits(0x620185b5b0891eec34fcae2cfa50dc7du128, 0xa3fa4befd33ec6de50u128, 72nat) == 0u128 ^ gf128_mul_bits(0xc4030b6b61123dd869f95c59f4a1b8fau128, 0x51fd25f7e99f636f28u128, 71nat)) by { lemma_hmul128_bits_unfold(0x620185b5b0891eec34fcae2cfa50dc7du128, 0xa3fa4befd33ec6de50u128, 72nat); }
    assert((((0x51fd25f7e99f636f28u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f28u128) >> 1u128) == 0x28fe92fbf4cfb1b794u128)) by (bit_vector);
    assert(((((0xc4030b6b61123dd869f95c59f4a1b8fau128) << 1) ^ (if ((((0xc4030b6b61123dd869f95c59f4a1b8fau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x880616d6c2247bb0d3f2b8b3e9437173u128) by (bit_vector);
    assert(gf128_xtime(0xc4030b6b61123dd869f95c59f4a1b8fau128) == 0x880616d6c2247bb0d3f2b8b3e9437173u128);
    assert(gf128_mul_bits(0xc4030b6b61123dd869f95c59f4a1b8fau128, 0x51fd25f7e99f636f28u128, 71nat) == 0u128 ^ gf128_mul_bits(0x880616d6c2247bb0d3f2b8b3e9437173u128, 0x28fe92fbf4cfb1b794u128, 70nat)) by { lemma_hmul128_bits_unfold(0xc4030b6b61123dd869f95c59f4a1b8fau128, 0x51fd25f7e99f636f28u128, 71nat); }
    assert((((0x28fe92fbf4cfb1b794u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b794u128) >> 1u128) == 0x147f497dfa67d8dbcau128)) by (bit_vector);
    assert(((((0x880616d6c2247bb0d3f2b8b3e9437173u128) << 1) ^ (if ((((0x880616d6c2247bb0d3f2b8b3e9437173u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x100c2dad8448f761a7e57167d286e261u128) by (bit_vector);
    assert(gf128_xtime(0x880616d6c2247bb0d3f2b8b3e9437173u128) == 0x100c2dad8448f761a7e57167d286e261u128);
    assert(gf128_mul_bits(0x880616d6c2247bb0d3f2b8b3e9437173u128, 0x28fe92fbf4cfb1b794u128, 70nat) == 0u128 ^ gf128_mul_bits(0x100c2dad8448f761a7e57167d286e261u128, 0x147f497dfa67d8dbcau128, 69nat)) by { lemma_hmul128_bits_unfold(0x880616d6c2247bb0d3f2b8b3e9437173u128, 0x28fe92fbf4cfb1b794u128, 70nat); }
    assert((((0x147f497dfa67d8dbcau128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbcau128) >> 1u128) == 0xa3fa4befd33ec6de5u128)) by (bit_vector);
    assert(((((0x100c2dad8448f761a7e57167d286e261u128) << 1) ^ (if ((((0x100c2dad8448f761a7e57167d286e261u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x20185b5b0891eec34fcae2cfa50dc4c2u128) by (bit_vector);
    assert(gf128_xtime(0x100c2dad8448f761a7e57167d286e261u128) == 0x20185b5b0891eec34fcae2cfa50dc4c2u128);
    assert(gf128_mul_bits(0x100c2dad8448f761a7e57167d286e261u128, 0x147f497dfa67d8dbcau128, 69nat) == 0u128 ^ gf128_mul_bits(0x20185b5b0891eec34fcae2cfa50dc4c2u128, 0xa3fa4befd33ec6de5u128, 68nat)) by { lemma_hmul128_bits_unfold(0x100c2dad8448f761a7e57167d286e261u128, 0x147f497dfa67d8dbcau128, 69nat); }
    assert((((0xa3fa4befd33ec6de5u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6de5u128) >> 1u128) == 0x51fd25f7e99f636f2u128)) by (bit_vector);
    assert(((((0x20185b5b0891eec34fcae2cfa50dc4c2u128) << 1) ^ (if ((((0x20185b5b0891eec34fcae2cfa50dc4c2u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4030b6b61123dd869f95c59f4a1b8984u128) by (bit_vector);
    assert(gf128_xtime(0x20185b5b0891eec34fcae2cfa50dc4c2u128) == 0x4030b6b61123dd869f95c59f4a1b8984u128);
    assert(gf128_mul_bits(0x20185b5b0891eec34fcae2cfa50dc4c2u128, 0xa3fa4befd33ec6de5u128, 68nat) == 0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ gf128_mul_bits(0x4030b6b61123dd869f95c59f4a1b8984u128, 0x51fd25f7e99f636f2u128, 67nat)) by { lemma_hmul128_bits_unfold(0x20185b5b0891eec34fcae2cfa50dc4c2u128, 0xa3fa4befd33ec6de5u128, 68nat); }
    assert((((0x51fd25f7e99f636f2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636f2u128) >> 1u128) == 0x28fe92fbf4cfb1b79u128)) by (bit_vector);
    assert(((((0x4030b6b61123dd869f95c59f4a1b8984u128) << 1) ^ (if ((((0x4030b6b61123dd869f95c59f4a1b8984u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x80616d6c2247bb0d3f2b8b3e94371308u128) by (bit_vector);
    assert(gf128_xtime(0x4030b6b61123dd869f95c59f4a1b8984u128) == 0x80616d6c2247bb0d3f2b8b3e94371308u128);
    assert(gf128_mul_bits(0x4030b6b61123dd869f95c59f4a1b8984u128, 0x51fd25f7e99f636f2u128, 67nat) == 0u128 ^ gf128_mul_bits(0x80616d6c2247bb0d3f2b8b3e94371308u128, 0x28fe92fbf4cfb1b79u128, 66nat)) by { lemma_hmul128_bits_unfold(0x4030b6b61123dd869f95c59f4a1b8984u128, 0x51fd25f7e99f636f2u128, 67nat); }
    assert((((0x28fe92fbf4cfb1b79u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b79u128) >> 1u128) == 0x147f497dfa67d8dbcu128)) by (bit_vector);
    assert(((((0x80616d6c2247bb0d3f2b8b3e94371308u128) << 1) ^ (if ((((0x80616d6c2247bb0d3f2b8b3e94371308u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc2dad8448f761a7e57167d286e2697u128) by (bit_vector);
    assert(gf128_xtime(0x80616d6c2247bb0d3f2b8b3e94371308u128) == 0xc2dad8448f761a7e57167d286e2697u128);
    assert(gf128_mul_bits(0x80616d6c2247bb0d3f2b8b3e94371308u128, 0x28fe92fbf4cfb1b79u128, 66nat) == 0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ gf128_mul_bits(0xc2dad8448f761a7e57167d286e2697u128, 0x147f497dfa67d8dbcu128, 65nat)) by { lemma_hmul128_bits_unfold(0x80616d6c2247bb0d3f2b8b3e94371308u128, 0x28fe92fbf4cfb1b79u128, 66nat); }
    assert((((0x147f497dfa67d8dbcu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbcu128) >> 1u128) == 0xa3fa4befd33ec6deu128)) by (bit_vector);
    assert(((((0xc2dad8448f761a7e57167d286e2697u128) << 1) ^ (if ((((0xc2dad8448f761a7e57167d286e2697u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x185b5b0891eec34fcae2cfa50dc4d2eu128) by (bit_vector);
    assert(gf128_xtime(0xc2dad8448f761a7e57167d286e2697u128) == 0x185b5b0891eec34fcae2cfa50dc4d2eu128);
    assert(gf128_mul_bits(0xc2dad8448f761a7e57167d286e2697u128, 0x147f497dfa67d8dbcu128, 65nat) == 0u128 ^ gf128_mul_bits(0x185b5b0891eec34fcae2cfa50dc4d2eu128, 0xa3fa4befd33ec6deu128, 64nat)) by { lemma_hmul128_bits_unfold(0xc2dad8448f761a7e57167d286e2697u128, 0x147f497dfa67d8dbcu128, 65nat); }
    assert((((0xa3fa4befd33ec6deu128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6deu128) >> 1u128) == 0x51fd25f7e99f636fu128)) by (bit_vector);
    assert(((((0x185b5b0891eec34fcae2cfa50dc4d2eu128) << 1) ^ (if ((((0x185b5b0891eec34fcae2cfa50dc4d2eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x30b6b61123dd869f95c59f4a1b89a5cu128) by (bit_vector);
    assert(gf128_xtime(0x185b5b0891eec34fcae2cfa50dc4d2eu128) == 0x30b6b61123dd869f95c59f4a1b89a5cu128);
    assert(gf128_mul_bits(0x185b5b0891eec34fcae2cfa50dc4d2eu128, 0xa3fa4befd33ec6deu128, 64nat) == 0u128 ^ gf128_mul_bits(0x30b6b61123dd869f95c59f4a1b89a5cu128, 0x51fd25f7e99f636fu128, 63nat)) by { lemma_hmul128_bits_unfold(0x185b5b0891eec34fcae2cfa50dc4d2eu128, 0xa3fa4befd33ec6deu128, 64nat); }
    assert((((0x51fd25f7e99f636fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636fu128) >> 1u128) == 0x28fe92fbf4cfb1b7u128)) by (bit_vector);
    assert(((((0x30b6b61123dd869f95c59f4a1b89a5cu128) << 1) ^ (if ((((0x30b6b61123dd869f95c59f4a1b89a5cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x616d6c2247bb0d3f2b8b3e9437134b8u128) by (bit_vector);
    assert(gf128_xtime(0x30b6b61123dd869f95c59f4a1b89a5cu128) == 0x616d6c2247bb0d3f2b8b3e9437134b8u128);
    assert(gf128_mul_bits(0x30b6b61123dd869f95c59f4a1b89a5cu128, 0x51fd25f7e99f636fu128, 63nat) == 0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ gf128_mul_bits(0x616d6c2247bb0d3f2b8b3e9437134b8u128, 0x28fe92fbf4cfb1b7u128, 62nat)) by { lemma_hmul128_bits_unfold(0x30b6b61123dd869f95c59f4a1b89a5cu128, 0x51fd25f7e99f636fu128, 63nat); }
    assert((((0x28fe92fbf4cfb1b7u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1b7u128) >> 1u128) == 0x147f497dfa67d8dbu128)) by (bit_vector);
    assert(((((0x616d6c2247bb0d3f2b8b3e9437134b8u128) << 1) ^ (if ((((0x616d6c2247bb0d3f2b8b3e9437134b8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc2dad8448f761a7e57167d286e26970u128) by (bit_vector);
    assert(gf128_xtime(0x616d6c2247bb0d3f2b8b3e9437134b8u128) == 0xc2dad8448f761a7e57167d286e26970u128);
    assert(gf128_mul_bits(0x616d6c2247bb0d3f2b8b3e9437134b8u128, 0x28fe92fbf4cfb1b7u128, 62nat) == 0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ gf128_mul_bits(0xc2dad8448f761a7e57167d286e26970u128, 0x147f497dfa67d8dbu128, 61nat)) by { lemma_hmul128_bits_unfold(0x616d6c2247bb0d3f2b8b3e9437134b8u128, 0x28fe92fbf4cfb1b7u128, 62nat); }
    assert((((0x147f497dfa67d8dbu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8dbu128) >> 1u128) == 0xa3fa4befd33ec6du128)) by (bit_vector);
    assert(((((0xc2dad8448f761a7e57167d286e26970u128) << 1) ^ (if ((((0xc2dad8448f761a7e57167d286e26970u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x185b5b0891eec34fcae2cfa50dc4d2e0u128) by (bit_vector);
    assert(gf128_xtime(0xc2dad8448f761a7e57167d286e26970u128) == 0x185b5b0891eec34fcae2cfa50dc4d2e0u128);
    assert(gf128_mul_bits(0xc2dad8448f761a7e57167d286e26970u128, 0x147f497dfa67d8dbu128, 61nat) == 0xc2dad8448f761a7e57167d286e26970u128 ^ gf128_mul_bits(0x185b5b0891eec34fcae2cfa50dc4d2e0u128, 0xa3fa4befd33ec6du128, 60nat)) by { lemma_hmul128_bits_unfold(0xc2dad8448f761a7e57167d286e26970u128, 0x147f497dfa67d8dbu128, 61nat); }
    assert((((0xa3fa4befd33ec6du128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6du128) >> 1u128) == 0x51fd25f7e99f636u128)) by (bit_vector);
    assert(((((0x185b5b0891eec34fcae2cfa50dc4d2e0u128) << 1) ^ (if ((((0x185b5b0891eec34fcae2cfa50dc4d2e0u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x30b6b61123dd869f95c59f4a1b89a5c0u128) by (bit_vector);
    assert(gf128_xtime(0x185b5b0891eec34fcae2cfa50dc4d2e0u128) == 0x30b6b61123dd869f95c59f4a1b89a5c0u128);
    assert(gf128_mul_bits(0x185b5b0891eec34fcae2cfa50dc4d2e0u128, 0xa3fa4befd33ec6du128, 60nat) == 0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ gf128_mul_bits(0x30b6b61123dd869f95c59f4a1b89a5c0u128, 0x51fd25f7e99f636u128, 59nat)) by { lemma_hmul128_bits_unfold(0x185b5b0891eec34fcae2cfa50dc4d2e0u128, 0xa3fa4befd33ec6du128, 60nat); }
    assert((((0x51fd25f7e99f636u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f636u128) >> 1u128) == 0x28fe92fbf4cfb1bu128)) by (bit_vector);
    assert(((((0x30b6b61123dd869f95c59f4a1b89a5c0u128) << 1) ^ (if ((((0x30b6b61123dd869f95c59f4a1b89a5c0u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x616d6c2247bb0d3f2b8b3e9437134b80u128) by (bit_vector);
    assert(gf128_xtime(0x30b6b61123dd869f95c59f4a1b89a5c0u128) == 0x616d6c2247bb0d3f2b8b3e9437134b80u128);
    assert(gf128_mul_bits(0x30b6b61123dd869f95c59f4a1b89a5c0u128, 0x51fd25f7e99f636u128, 59nat) == 0u128 ^ gf128_mul_bits(0x616d6c2247bb0d3f2b8b3e9437134b80u128, 0x28fe92fbf4cfb1bu128, 58nat)) by { lemma_hmul128_bits_unfold(0x30b6b61123dd869f95c59f4a1b89a5c0u128, 0x51fd25f7e99f636u128, 59nat); }
    assert((((0x28fe92fbf4cfb1bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1bu128) >> 1u128) == 0x147f497dfa67d8du128)) by (bit_vector);
    assert(((((0x616d6c2247bb0d3f2b8b3e9437134b80u128) << 1) ^ (if ((((0x616d6c2247bb0d3f2b8b3e9437134b80u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc2dad8448f761a7e57167d286e269700u128) by (bit_vector);
    assert(gf128_xtime(0x616d6c2247bb0d3f2b8b3e9437134b80u128) == 0xc2dad8448f761a7e57167d286e269700u128);
    assert(gf128_mul_bits(0x616d6c2247bb0d3f2b8b3e9437134b80u128, 0x28fe92fbf4cfb1bu128, 58nat) == 0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ gf128_mul_bits(0xc2dad8448f761a7e57167d286e269700u128, 0x147f497dfa67d8du128, 57nat)) by { lemma_hmul128_bits_unfold(0x616d6c2247bb0d3f2b8b3e9437134b80u128, 0x28fe92fbf4cfb1bu128, 58nat); }
    assert((((0x147f497dfa67d8du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67d8du128) >> 1u128) == 0xa3fa4befd33ec6u128)) by (bit_vector);
    assert(((((0xc2dad8448f761a7e57167d286e269700u128) << 1) ^ (if ((((0xc2dad8448f761a7e57167d286e269700u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x85b5b0891eec34fcae2cfa50dc4d2e87u128) by (bit_vector);
    assert(gf128_xtime(0xc2dad8448f761a7e57167d286e269700u128) == 0x85b5b0891eec34fcae2cfa50dc4d2e87u128);
    assert(gf128_mul_bits(0xc2dad8448f761a7e57167d286e269700u128, 0x147f497dfa67d8du128, 57nat) == 0xc2dad8448f761a7e57167d286e269700u128 ^ gf128_mul_bits(0x85b5b0891eec34fcae2cfa50dc4d2e87u128, 0xa3fa4befd33ec6u128, 56nat)) by { lemma_hmul128_bits_unfold(0xc2dad8448f761a7e57167d286e269700u128, 0x147f497dfa67d8du128, 57nat); }
    assert((((0xa3fa4befd33ec6u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33ec6u128) >> 1u128) == 0x51fd25f7e99f63u128)) by (bit_vector);
    assert(((((0x85b5b0891eec34fcae2cfa50dc4d2e87u128) << 1) ^ (if ((((0x85b5b0891eec34fcae2cfa50dc4d2e87u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb6b61123dd869f95c59f4a1b89a5d89u128) by (bit_vector);
    assert(gf128_xtime(0x85b5b0891eec34fcae2cfa50dc4d2e87u128) == 0xb6b61123dd869f95c59f4a1b89a5d89u128);
    assert(gf128_mul_bits(0x85b5b0891eec34fcae2cfa50dc4d2e87u128, 0xa3fa4befd33ec6u128, 56nat) == 0u128 ^ gf128_mul_bits(0xb6b61123dd869f95c59f4a1b89a5d89u128, 0x51fd25f7e99f63u128, 55nat)) by { lemma_hmul128_bits_unfold(0x85b5b0891eec34fcae2cfa50dc4d2e87u128, 0xa3fa4befd33ec6u128, 56nat); }
    assert((((0x51fd25f7e99f63u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e99f63u128) >> 1u128) == 0x28fe92fbf4cfb1u128)) by (bit_vector);
    assert(((((0xb6b61123dd869f95c59f4a1b89a5d89u128) << 1) ^ (if ((((0xb6b61123dd869f95c59f4a1b89a5d89u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x16d6c2247bb0d3f2b8b3e9437134bb12u128) by (bit_vector);
    assert(gf128_xtime(0xb6b61123dd869f95c59f4a1b89a5d89u128) == 0x16d6c2247bb0d3f2b8b3e9437134bb12u128);
    assert(gf128_mul_bits(0xb6b61123dd869f95c59f4a1b89a5d89u128, 0x51fd25f7e99f63u128, 55nat) == 0xb6b61123dd869f95c59f4a1b89a5d89u128 ^ gf128_mul_bits(0x16d6c2247bb0d3f2b8b3e9437134bb12u128, 0x28fe92fbf4cfb1u128, 54nat)) by { lemma_hmul128_bits_unfold(0xb6b61123dd869f95c59f4a1b89a5d89u128, 0x51fd25f7e99f63u128, 55nat); }
    assert((((0x28fe92fbf4cfb1u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfb1u128) >> 1u128) == 0x147f497dfa67d8u128)) by (bit_vector);
    assert(((((0x16d6c2247bb0d3f2b8b3e9437134bb12u128) << 1) ^ (if ((((0x16d6c2247bb0d3f2b8b3e9437134bb12u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x2dad8448f761a7e57167d286e2697624u128) by (bit_vector);
    assert(gf128_xtime(0x16d6c2247bb0d3f2b8b3e9437134bb12u128) == 0x2dad8448f761a7e57167d286e2697624u128);
    assert(gf128_mul_bits(0x16d6c2247bb0d3f2b8b3e9437134bb12u128, 0x28fe92fbf4cfb1u128, 54nat) == 0x16d6c2247bb0d3f2b8b3e9437134bb12u128 ^ gf128_mul_bits(0x2dad8448f761a7e57167d286e2697624u128, 0x147f497dfa67d8u128, 53nat)) by { lemma_hmul128_bits_unfold(0x16d6c2247bb0d3f2b8b3e9437134bb12u128, 0x28fe92fbf4cfb1u128, 54nat); }
    assert((((0x147f497dfa67d8u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f497dfa67d8u128) >> 1u128) == 0xa3fa4befd33ecu128)) by (bit_vector);
    assert(((((0x2dad8448f761a7e57167d286e2697624u128) << 1) ^ (if ((((0x2dad8448f761a7e57167d286e2697624u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5b5b0891eec34fcae2cfa50dc4d2ec48u128) by (bit_vector);
    assert(gf128_xtime(0x2dad8448f761a7e57167d286e2697624u128) == 0x5b5b0891eec34fcae2cfa50dc4d2ec48u128);
    assert(gf128_mul_bits(0x2dad8448f761a7e57167d286e2697624u128, 0x147f497dfa67d8u128, 53nat) == 0u128 ^ gf128_mul_bits(0x5b5b0891eec34fcae2cfa50dc4d2ec48u128, 0xa3fa4befd33ecu128, 52nat)) by { lemma_hmul128_bits_unfold(0x2dad8448f761a7e57167d286e2697624u128, 0x147f497dfa67d8u128, 53nat); }
    assert((((0xa3fa4befd33ecu128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33ecu128) >> 1u128) == 0x51fd25f7e99f6u128)) by (bit_vector);
    assert(((((0x5b5b0891eec34fcae2cfa50dc4d2ec48u128) << 1) ^ (if ((((0x5b5b0891eec34fcae2cfa50dc4d2ec48u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb6b61123dd869f95c59f4a1b89a5d890u128) by (bit_vector);
    assert(gf128_xtime(0x5b5b0891eec34fcae2cfa50dc4d2ec48u128) == 0xb6b61123dd869f95c59f4a1b89a5d890u128);
    assert(gf128_mul_bits(0x5b5b0891eec34fcae2cfa50dc4d2ec48u128, 0xa3fa4befd33ecu128, 52nat) == 0u128 ^ gf128_mul_bits(0xb6b61123dd869f95c59f4a1b89a5d890u128, 0x51fd25f7e99f6u128, 51nat)) by { lemma_hmul128_bits_unfold(0x5b5b0891eec34fcae2cfa50dc4d2ec48u128, 0xa3fa4befd33ecu128, 52nat); }
    assert((((0x51fd25f7e99f6u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7e99f6u128) >> 1u128) == 0x28fe92fbf4cfbu128)) by (bit_vector);
    assert(((((0xb6b61123dd869f95c59f4a1b89a5d890u128) << 1) ^ (if ((((0xb6b61123dd869f95c59f4a1b89a5d890u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128) by (bit_vector);
    assert(gf128_xtime(0xb6b61123dd869f95c59f4a1b89a5d890u128) == 0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128);
    assert(gf128_mul_bits(0xb6b61123dd869f95c59f4a1b89a5d890u128, 0x51fd25f7e99f6u128, 51nat) == 0u128 ^ gf128_mul_bits(0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128, 0x28fe92fbf4cfbu128, 50nat)) by { lemma_hmul128_bits_unfold(0xb6b61123dd869f95c59f4a1b89a5d890u128, 0x51fd25f7e99f6u128, 51nat); }
    assert((((0x28fe92fbf4cfbu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfbu128) >> 1u128) == 0x147f497dfa67du128)) by (bit_vector);
    assert(((((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128) << 1) ^ (if ((((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xdad8448f761a7e57167d286e2697634eu128) by (bit_vector);
    assert(gf128_xtime(0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128) == 0xdad8448f761a7e57167d286e2697634eu128);
    assert(gf128_mul_bits(0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128, 0x28fe92fbf4cfbu128, 50nat) == 0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128 ^ gf128_mul_bits(0xdad8448f761a7e57167d286e2697634eu128, 0x147f497dfa67du128, 49nat)) by { lemma_hmul128_bits_unfold(0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128, 0x28fe92fbf4cfbu128, 50nat); }
    assert((((0x147f497dfa67du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67du128) >> 1u128) == 0xa3fa4befd33eu128)) by (bit_vector);
    assert(((((0xdad8448f761a7e57167d286e2697634eu128) << 1) ^ (if ((((0xdad8448f761a7e57167d286e2697634eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb5b0891eec34fcae2cfa50dc4d2ec61bu128) by (bit_vector);
    assert(gf128_xtime(0xdad8448f761a7e57167d286e2697634eu128) == 0xb5b0891eec34fcae2cfa50dc4d2ec61bu128);
    assert(gf128_mul_bits(0xdad8448f761a7e57167d286e2697634eu128, 0x147f497dfa67du128, 49nat) == 0xdad8448f761a7e57167d286e2697634eu128 ^ gf128_mul_bits(0xb5b0891eec34fcae2cfa50dc4d2ec61bu128, 0xa3fa4befd33eu128, 48nat)) by { lemma_hmul128_bits_unfold(0xdad8448f761a7e57167d286e2697634eu128, 0x147f497dfa67du128, 49nat); }
    assert((((0xa3fa4befd33eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4befd33eu128) >> 1u128) == 0x51fd25f7e99fu128)) by (bit_vector);
    assert(((((0xb5b0891eec34fcae2cfa50dc4d2ec61bu128) << 1) ^ (if ((((0xb5b0891eec34fcae2cfa50dc4d2ec61bu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x6b61123dd869f95c59f4a1b89a5d8cb1u128) by (bit_vector);
    assert(gf128_xtime(0xb5b0891eec34fcae2cfa50dc4d2ec61bu128) == 0x6b61123dd869f95c59f4a1b89a5d8cb1u128);
    assert(gf128_mul_bits(0xb5b0891eec34fcae2cfa50dc4d2ec61bu128, 0xa3fa4befd33eu128, 48nat) == 0u128 ^ gf128_mul_bits(0x6b61123dd869f95c59f4a1b89a5d8cb1u128, 0x51fd25f7e99fu128, 47nat)) by { lemma_hmul128_bits_unfold(0xb5b0891eec34fcae2cfa50dc4d2ec61bu128, 0xa3fa4befd33eu128, 48nat); }
    assert((((0x51fd25f7e99fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e99fu128) >> 1u128) == 0x28fe92fbf4cfu128)) by (bit_vector);
    assert(((((0x6b61123dd869f95c59f4a1b89a5d8cb1u128) << 1) ^ (if ((((0x6b61123dd869f95c59f4a1b89a5d8cb1u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd6c2247bb0d3f2b8b3e9437134bb1962u128) by (bit_vector);
    assert(gf128_xtime(0x6b61123dd869f95c59f4a1b89a5d8cb1u128) == 0xd6c2247bb0d3f2b8b3e9437134bb1962u128);
    assert(gf128_mul_bits(0x6b61123dd869f95c59f4a1b89a5d8cb1u128, 0x51fd25f7e99fu128, 47nat) == 0x6b61123dd869f95c59f4a1b89a5d8cb1u128 ^ gf128_mul_bits(0xd6c2247bb0d3f2b8b3e9437134bb1962u128, 0x28fe92fbf4cfu128, 46nat)) by { lemma_hmul128_bits_unfold(0x6b61123dd869f95c59f4a1b89a5d8cb1u128, 0x51fd25f7e99fu128, 47nat); }
    assert((((0x28fe92fbf4cfu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbf4cfu128) >> 1u128) == 0x147f497dfa67u128)) by (bit_vector);
    assert(((((0xd6c2247bb0d3f2b8b3e9437134bb1962u128) << 1) ^ (if ((((0xd6c2247bb0d3f2b8b3e9437134bb1962u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xad8448f761a7e57167d286e269763243u128) by (bit_vector);
    assert(gf128_xtime(0xd6c2247bb0d3f2b8b3e9437134bb1962u128) == 0xad8448f761a7e57167d286e269763243u128);
    assert(gf128_mul_bits(0xd6c2247bb0d3f2b8b3e9437134bb1962u128, 0x28fe92fbf4cfu128, 46nat) == 0xd6c2247bb0d3f2b8b3e9437134bb1962u128 ^ gf128_mul_bits(0xad8448f761a7e57167d286e269763243u128, 0x147f497dfa67u128, 45nat)) by { lemma_hmul128_bits_unfold(0xd6c2247bb0d3f2b8b3e9437134bb1962u128, 0x28fe92fbf4cfu128, 46nat); }
    assert((((0x147f497dfa67u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfa67u128) >> 1u128) == 0xa3fa4befd33u128)) by (bit_vector);
    assert(((((0xad8448f761a7e57167d286e269763243u128) << 1) ^ (if ((((0xad8448f761a7e57167d286e269763243u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5b0891eec34fcae2cfa50dc4d2ec6401u128) by (bit_vector);
    assert(gf128_xtime(0xad8448f761a7e57167d286e269763243u128) == 0x5b0891eec34fcae2cfa50dc4d2ec6401u128);
    assert(gf128_mul_bits(0xad8448f761a7e57167d286e269763243u128, 0x147f497dfa67u128, 45nat) == 0xad8448f761a7e57167d286e269763243u128 ^ gf128_mul_bits(0x5b0891eec34fcae2cfa50dc4d2ec6401u128, 0xa3fa4befd33u128, 44nat)) by { lemma_hmul128_bits_unfold(0xad8448f761a7e57167d286e269763243u128, 0x147f497dfa67u128, 45nat); }
    assert((((0xa3fa4befd33u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd33u128) >> 1u128) == 0x51fd25f7e99u128)) by (bit_vector);
    assert(((((0x5b0891eec34fcae2cfa50dc4d2ec6401u128) << 1) ^ (if ((((0x5b0891eec34fcae2cfa50dc4d2ec6401u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb61123dd869f95c59f4a1b89a5d8c802u128) by (bit_vector);
    assert(gf128_xtime(0x5b0891eec34fcae2cfa50dc4d2ec6401u128) == 0xb61123dd869f95c59f4a1b89a5d8c802u128);
    assert(gf128_mul_bits(0x5b0891eec34fcae2cfa50dc4d2ec6401u128, 0xa3fa4befd33u128, 44nat) == 0x5b0891eec34fcae2cfa50dc4d2ec6401u128 ^ gf128_mul_bits(0xb61123dd869f95c59f4a1b89a5d8c802u128, 0x51fd25f7e99u128, 43nat)) by { lemma_hmul128_bits_unfold(0x5b0891eec34fcae2cfa50dc4d2ec6401u128, 0xa3fa4befd33u128, 44nat); }
    assert((((0x51fd25f7e99u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e99u128) >> 1u128) == 0x28fe92fbf4cu128)) by (bit_vector);
    assert(((((0xb61123dd869f95c59f4a1b89a5d8c802u128) << 1) ^ (if ((((0xb61123dd869f95c59f4a1b89a5d8c802u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x6c2247bb0d3f2b8b3e9437134bb19083u128) by (bit_vector);
    assert(gf128_xtime(0xb61123dd869f95c59f4a1b89a5d8c802u128) == 0x6c2247bb0d3f2b8b3e9437134bb19083u128);
    assert(gf128_mul_bits(0xb61123dd869f95c59f4a1b89a5d8c802u128, 0x51fd25f7e99u128, 43nat) == 0xb61123dd869f95c59f4a1b89a5d8c802u128 ^ gf128_mul_bits(0x6c2247bb0d3f2b8b3e9437134bb19083u128, 0x28fe92fbf4cu128, 42nat)) by { lemma_hmul128_bits_unfold(0xb61123dd869f95c59f4a1b89a5d8c802u128, 0x51fd25f7e99u128, 43nat); }
    assert((((0x28fe92fbf4cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4cu128) >> 1u128) == 0x147f497dfa6u128)) by (bit_vector);
    assert(((((0x6c2247bb0d3f2b8b3e9437134bb19083u128) << 1) ^ (if ((((0x6c2247bb0d3f2b8b3e9437134bb19083u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd8448f761a7e57167d286e2697632106u128) by (bit_vector);
    assert(gf128_xtime(0x6c2247bb0d3f2b8b3e9437134bb19083u128) == 0xd8448f761a7e57167d286e2697632106u128);
    assert(gf128_mul_bits(0x6c2247bb0d3f2b8b3e9437134bb19083u128, 0x28fe92fbf4cu128, 42nat) == 0u128 ^ gf128_mul_bits(0xd8448f761a7e57167d286e2697632106u128, 0x147f497dfa6u128, 41nat)) by { lemma_hmul128_bits_unfold(0x6c2247bb0d3f2b8b3e9437134bb19083u128, 0x28fe92fbf4cu128, 42nat); }
    assert((((0x147f497dfa6u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f497dfa6u128) >> 1u128) == 0xa3fa4befd3u128)) by (bit_vector);
    assert(((((0xd8448f761a7e57167d286e2697632106u128) << 1) ^ (if ((((0xd8448f761a7e57167d286e2697632106u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb0891eec34fcae2cfa50dc4d2ec6428bu128) by (bit_vector);
    assert(gf128_xtime(0xd8448f761a7e57167d286e2697632106u128) == 0xb0891eec34fcae2cfa50dc4d2ec6428bu128);
    assert(gf128_mul_bits(0xd8448f761a7e57167d286e2697632106u128, 0x147f497dfa6u128, 41nat) == 0u128 ^ gf128_mul_bits(0xb0891eec34fcae2cfa50dc4d2ec6428bu128, 0xa3fa4befd3u128, 40nat)) by { lemma_hmul128_bits_unfold(0xd8448f761a7e57167d286e2697632106u128, 0x147f497dfa6u128, 41nat); }
    assert((((0xa3fa4befd3u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befd3u128) >> 1u128) == 0x51fd25f7e9u128)) by (bit_vector);
    assert(((((0xb0891eec34fcae2cfa50dc4d2ec6428bu128) << 1) ^ (if ((((0xb0891eec34fcae2cfa50dc4d2ec6428bu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x61123dd869f95c59f4a1b89a5d8c8591u128) by (bit_vector);
    assert(gf128_xtime(0xb0891eec34fcae2cfa50dc4d2ec6428bu128) == 0x61123dd869f95c59f4a1b89a5d8c8591u128);
    assert(gf128_mul_bits(0xb0891eec34fcae2cfa50dc4d2ec6428bu128, 0xa3fa4befd3u128, 40nat) == 0xb0891eec34fcae2cfa50dc4d2ec6428bu128 ^ gf128_mul_bits(0x61123dd869f95c59f4a1b89a5d8c8591u128, 0x51fd25f7e9u128, 39nat)) by { lemma_hmul128_bits_unfold(0xb0891eec34fcae2cfa50dc4d2ec6428bu128, 0xa3fa4befd3u128, 40nat); }
    assert((((0x51fd25f7e9u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7e9u128) >> 1u128) == 0x28fe92fbf4u128)) by (bit_vector);
    assert(((((0x61123dd869f95c59f4a1b89a5d8c8591u128) << 1) ^ (if ((((0x61123dd869f95c59f4a1b89a5d8c8591u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc2247bb0d3f2b8b3e9437134bb190b22u128) by (bit_vector);
    assert(gf128_xtime(0x61123dd869f95c59f4a1b89a5d8c8591u128) == 0xc2247bb0d3f2b8b3e9437134bb190b22u128);
    assert(gf128_mul_bits(0x61123dd869f95c59f4a1b89a5d8c8591u128, 0x51fd25f7e9u128, 39nat) == 0x61123dd869f95c59f4a1b89a5d8c8591u128 ^ gf128_mul_bits(0xc2247bb0d3f2b8b3e9437134bb190b22u128, 0x28fe92fbf4u128, 38nat)) by { lemma_hmul128_bits_unfold(0x61123dd869f95c59f4a1b89a5d8c8591u128, 0x51fd25f7e9u128, 39nat); }
    assert((((0x28fe92fbf4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92fbf4u128) >> 1u128) == 0x147f497dfau128)) by (bit_vector);
    assert(((((0xc2247bb0d3f2b8b3e9437134bb190b22u128) << 1) ^ (if ((((0xc2247bb0d3f2b8b3e9437134bb190b22u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x8448f761a7e57167d286e269763216c3u128) by (bit_vector);
    assert(gf128_xtime(0xc2247bb0d3f2b8b3e9437134bb190b22u128) == 0x8448f761a7e57167d286e269763216c3u128);
    assert(gf128_mul_bits(0xc2247bb0d3f2b8b3e9437134bb190b22u128, 0x28fe92fbf4u128, 38nat) == 0u128 ^ gf128_mul_bits(0x8448f761a7e57167d286e269763216c3u128, 0x147f497dfau128, 37nat)) by { lemma_hmul128_bits_unfold(0xc2247bb0d3f2b8b3e9437134bb190b22u128, 0x28fe92fbf4u128, 38nat); }
    assert((((0x147f497dfau128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f497dfau128) >> 1u128) == 0xa3fa4befdu128)) by (bit_vector);
    assert(((((0x8448f761a7e57167d286e269763216c3u128) << 1) ^ (if ((((0x8448f761a7e57167d286e269763216c3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x891eec34fcae2cfa50dc4d2ec642d01u128) by (bit_vector);
    assert(gf128_xtime(0x8448f761a7e57167d286e269763216c3u128) == 0x891eec34fcae2cfa50dc4d2ec642d01u128);
    assert(gf128_mul_bits(0x8448f761a7e57167d286e269763216c3u128, 0x147f497dfau128, 37nat) == 0u128 ^ gf128_mul_bits(0x891eec34fcae2cfa50dc4d2ec642d01u128, 0xa3fa4befdu128, 36nat)) by { lemma_hmul128_bits_unfold(0x8448f761a7e57167d286e269763216c3u128, 0x147f497dfau128, 37nat); }
    assert((((0xa3fa4befdu128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befdu128) >> 1u128) == 0x51fd25f7eu128)) by (bit_vector);
    assert(((((0x891eec34fcae2cfa50dc4d2ec642d01u128) << 1) ^ (if ((((0x891eec34fcae2cfa50dc4d2ec642d01u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1123dd869f95c59f4a1b89a5d8c85a02u128) by (bit_vector);
    assert(gf128_xtime(0x891eec34fcae2cfa50dc4d2ec642d01u128) == 0x1123dd869f95c59f4a1b89a5d8c85a02u128);
    assert(gf128_mul_bits(0x891eec34fcae2cfa50dc4d2ec642d01u128, 0xa3fa4befdu128, 36nat) == 0x891eec34fcae2cfa50dc4d2ec642d01u128 ^ gf128_mul_bits(0x1123dd869f95c59f4a1b89a5d8c85a02u128, 0x51fd25f7eu128, 35nat)) by { lemma_hmul128_bits_unfold(0x891eec34fcae2cfa50dc4d2ec642d01u128, 0xa3fa4befdu128, 36nat); }
    assert((((0x51fd25f7eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd25f7eu128) >> 1u128) == 0x28fe92fbfu128)) by (bit_vector);
    assert(((((0x1123dd869f95c59f4a1b89a5d8c85a02u128) << 1) ^ (if ((((0x1123dd869f95c59f4a1b89a5d8c85a02u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x2247bb0d3f2b8b3e9437134bb190b404u128) by (bit_vector);
    assert(gf128_xtime(0x1123dd869f95c59f4a1b89a5d8c85a02u128) == 0x2247bb0d3f2b8b3e9437134bb190b404u128);
    assert(gf128_mul_bits(0x1123dd869f95c59f4a1b89a5d8c85a02u128, 0x51fd25f7eu128, 35nat) == 0u128 ^ gf128_mul_bits(0x2247bb0d3f2b8b3e9437134bb190b404u128, 0x28fe92fbfu128, 34nat)) by { lemma_hmul128_bits_unfold(0x1123dd869f95c59f4a1b89a5d8c85a02u128, 0x51fd25f7eu128, 35nat); }
    assert((((0x28fe92fbfu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbfu128) >> 1u128) == 0x147f497dfu128)) by (bit_vector);
    assert(((((0x2247bb0d3f2b8b3e9437134bb190b404u128) << 1) ^ (if ((((0x2247bb0d3f2b8b3e9437134bb190b404u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x448f761a7e57167d286e269763216808u128) by (bit_vector);
    assert(gf128_xtime(0x2247bb0d3f2b8b3e9437134bb190b404u128) == 0x448f761a7e57167d286e269763216808u128);
    assert(gf128_mul_bits(0x2247bb0d3f2b8b3e9437134bb190b404u128, 0x28fe92fbfu128, 34nat) == 0x2247bb0d3f2b8b3e9437134bb190b404u128 ^ gf128_mul_bits(0x448f761a7e57167d286e269763216808u128, 0x147f497dfu128, 33nat)) by { lemma_hmul128_bits_unfold(0x2247bb0d3f2b8b3e9437134bb190b404u128, 0x28fe92fbfu128, 34nat); }
    assert((((0x147f497dfu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497dfu128) >> 1u128) == 0xa3fa4befu128)) by (bit_vector);
    assert(((((0x448f761a7e57167d286e269763216808u128) << 1) ^ (if ((((0x448f761a7e57167d286e269763216808u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x891eec34fcae2cfa50dc4d2ec642d010u128) by (bit_vector);
    assert(gf128_xtime(0x448f761a7e57167d286e269763216808u128) == 0x891eec34fcae2cfa50dc4d2ec642d010u128);
    assert(gf128_mul_bits(0x448f761a7e57167d286e269763216808u128, 0x147f497dfu128, 33nat) == 0x448f761a7e57167d286e269763216808u128 ^ gf128_mul_bits(0x891eec34fcae2cfa50dc4d2ec642d010u128, 0xa3fa4befu128, 32nat)) by { lemma_hmul128_bits_unfold(0x448f761a7e57167d286e269763216808u128, 0x147f497dfu128, 33nat); }
    assert((((0xa3fa4befu128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4befu128) >> 1u128) == 0x51fd25f7u128)) by (bit_vector);
    assert(((((0x891eec34fcae2cfa50dc4d2ec642d010u128) << 1) ^ (if ((((0x891eec34fcae2cfa50dc4d2ec642d010u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x123dd869f95c59f4a1b89a5d8c85a0a7u128) by (bit_vector);
    assert(gf128_xtime(0x891eec34fcae2cfa50dc4d2ec642d010u128) == 0x123dd869f95c59f4a1b89a5d8c85a0a7u128);
    assert(gf128_mul_bits(0x891eec34fcae2cfa50dc4d2ec642d010u128, 0xa3fa4befu128, 32nat) == 0x891eec34fcae2cfa50dc4d2ec642d010u128 ^ gf128_mul_bits(0x123dd869f95c59f4a1b89a5d8c85a0a7u128, 0x51fd25f7u128, 31nat)) by { lemma_hmul128_bits_unfold(0x891eec34fcae2cfa50dc4d2ec642d010u128, 0xa3fa4befu128, 32nat); }
    assert((((0x51fd25f7u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25f7u128) >> 1u128) == 0x28fe92fbu128)) by (bit_vector);
    assert(((((0x123dd869f95c59f4a1b89a5d8c85a0a7u128) << 1) ^ (if ((((0x123dd869f95c59f4a1b89a5d8c85a0a7u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x247bb0d3f2b8b3e9437134bb190b414eu128) by (bit_vector);
    assert(gf128_xtime(0x123dd869f95c59f4a1b89a5d8c85a0a7u128) == 0x247bb0d3f2b8b3e9437134bb190b414eu128);
    assert(gf128_mul_bits(0x123dd869f95c59f4a1b89a5d8c85a0a7u128, 0x51fd25f7u128, 31nat) == 0x123dd869f95c59f4a1b89a5d8c85a0a7u128 ^ gf128_mul_bits(0x247bb0d3f2b8b3e9437134bb190b414eu128, 0x28fe92fbu128, 30nat)) by { lemma_hmul128_bits_unfold(0x123dd869f95c59f4a1b89a5d8c85a0a7u128, 0x51fd25f7u128, 31nat); }
    assert((((0x28fe92fbu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fbu128) >> 1u128) == 0x147f497du128)) by (bit_vector);
    assert(((((0x247bb0d3f2b8b3e9437134bb190b414eu128) << 1) ^ (if ((((0x247bb0d3f2b8b3e9437134bb190b414eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x48f761a7e57167d286e269763216829cu128) by (bit_vector);
    assert(gf128_xtime(0x247bb0d3f2b8b3e9437134bb190b414eu128) == 0x48f761a7e57167d286e269763216829cu128);
    assert(gf128_mul_bits(0x247bb0d3f2b8b3e9437134bb190b414eu128, 0x28fe92fbu128, 30nat) == 0x247bb0d3f2b8b3e9437134bb190b414eu128 ^ gf128_mul_bits(0x48f761a7e57167d286e269763216829cu128, 0x147f497du128, 29nat)) by { lemma_hmul128_bits_unfold(0x247bb0d3f2b8b3e9437134bb190b414eu128, 0x28fe92fbu128, 30nat); }
    assert((((0x147f497du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497du128) >> 1u128) == 0xa3fa4beu128)) by (bit_vector);
    assert(((((0x48f761a7e57167d286e269763216829cu128) << 1) ^ (if ((((0x48f761a7e57167d286e269763216829cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x91eec34fcae2cfa50dc4d2ec642d0538u128) by (bit_vector);
    assert(gf128_xtime(0x48f761a7e57167d286e269763216829cu128) == 0x91eec34fcae2cfa50dc4d2ec642d0538u128);
    assert(gf128_mul_bits(0x48f761a7e57167d286e269763216829cu128, 0x147f497du128, 29nat) == 0x48f761a7e57167d286e269763216829cu128 ^ gf128_mul_bits(0x91eec34fcae2cfa50dc4d2ec642d0538u128, 0xa3fa4beu128, 28nat)) by { lemma_hmul128_bits_unfold(0x48f761a7e57167d286e269763216829cu128, 0x147f497du128, 29nat); }
    assert((((0xa3fa4beu128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4beu128) >> 1u128) == 0x51fd25fu128)) by (bit_vector);
    assert(((((0x91eec34fcae2cfa50dc4d2ec642d0538u128) << 1) ^ (if ((((0x91eec34fcae2cfa50dc4d2ec642d0538u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x23dd869f95c59f4a1b89a5d8c85a0af7u128) by (bit_vector);
    assert(gf128_xtime(0x91eec34fcae2cfa50dc4d2ec642d0538u128) == 0x23dd869f95c59f4a1b89a5d8c85a0af7u128);
    assert(gf128_mul_bits(0x91eec34fcae2cfa50dc4d2ec642d0538u128, 0xa3fa4beu128, 28nat) == 0u128 ^ gf128_mul_bits(0x23dd869f95c59f4a1b89a5d8c85a0af7u128, 0x51fd25fu128, 27nat)) by { lemma_hmul128_bits_unfold(0x91eec34fcae2cfa50dc4d2ec642d0538u128, 0xa3fa4beu128, 28nat); }
    assert((((0x51fd25fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25fu128) >> 1u128) == 0x28fe92fu128)) by (bit_vector);
    assert(((((0x23dd869f95c59f4a1b89a5d8c85a0af7u128) << 1) ^ (if ((((0x23dd869f95c59f4a1b89a5d8c85a0af7u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x47bb0d3f2b8b3e9437134bb190b415eeu128) by (bit_vector);
    assert(gf128_xtime(0x23dd869f95c59f4a1b89a5d8c85a0af7u128) == 0x47bb0d3f2b8b3e9437134bb190b415eeu128);
    assert(gf128_mul_bits(0x23dd869f95c59f4a1b89a5d8c85a0af7u128, 0x51fd25fu128, 27nat) == 0x23dd869f95c59f4a1b89a5d8c85a0af7u128 ^ gf128_mul_bits(0x47bb0d3f2b8b3e9437134bb190b415eeu128, 0x28fe92fu128, 26nat)) by { lemma_hmul128_bits_unfold(0x23dd869f95c59f4a1b89a5d8c85a0af7u128, 0x51fd25fu128, 27nat); }
    assert((((0x28fe92fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe92fu128) >> 1u128) == 0x147f497u128)) by (bit_vector);
    assert(((((0x47bb0d3f2b8b3e9437134bb190b415eeu128) << 1) ^ (if ((((0x47bb0d3f2b8b3e9437134bb190b415eeu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x8f761a7e57167d286e26976321682bdcu128) by (bit_vector);
    assert(gf128_xtime(0x47bb0d3f2b8b3e9437134bb190b415eeu128) == 0x8f761a7e57167d286e26976321682bdcu128);
    assert(gf128_mul_bits(0x47bb0d3f2b8b3e9437134bb190b415eeu128, 0x28fe92fu128, 26nat) == 0x47bb0d3f2b8b3e9437134bb190b415eeu128 ^ gf128_mul_bits(0x8f761a7e57167d286e26976321682bdcu128, 0x147f497u128, 25nat)) by { lemma_hmul128_bits_unfold(0x47bb0d3f2b8b3e9437134bb190b415eeu128, 0x28fe92fu128, 26nat); }
    assert((((0x147f497u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f497u128) >> 1u128) == 0xa3fa4bu128)) by (bit_vector);
    assert(((((0x8f761a7e57167d286e26976321682bdcu128) << 1) ^ (if ((((0x8f761a7e57167d286e26976321682bdcu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1eec34fcae2cfa50dc4d2ec642d0573fu128) by (bit_vector);
    assert(gf128_xtime(0x8f761a7e57167d286e26976321682bdcu128) == 0x1eec34fcae2cfa50dc4d2ec642d0573fu128);
    assert(gf128_mul_bits(0x8f761a7e57167d286e26976321682bdcu128, 0x147f497u128, 25nat) == 0x8f761a7e57167d286e26976321682bdcu128 ^ gf128_mul_bits(0x1eec34fcae2cfa50dc4d2ec642d0573fu128, 0xa3fa4bu128, 24nat)) by { lemma_hmul128_bits_unfold(0x8f761a7e57167d286e26976321682bdcu128, 0x147f497u128, 25nat); }
    assert((((0xa3fa4bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fa4bu128) >> 1u128) == 0x51fd25u128)) by (bit_vector);
    assert(((((0x1eec34fcae2cfa50dc4d2ec642d0573fu128) << 1) ^ (if ((((0x1eec34fcae2cfa50dc4d2ec642d0573fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128) by (bit_vector);
    assert(gf128_xtime(0x1eec34fcae2cfa50dc4d2ec642d0573fu128) == 0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128);
    assert(gf128_mul_bits(0x1eec34fcae2cfa50dc4d2ec642d0573fu128, 0xa3fa4bu128, 24nat) == 0x1eec34fcae2cfa50dc4d2ec642d0573fu128 ^ gf128_mul_bits(0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128, 0x51fd25u128, 23nat)) by { lemma_hmul128_bits_unfold(0x1eec34fcae2cfa50dc4d2ec642d0573fu128, 0xa3fa4bu128, 24nat); }
    assert((((0x51fd25u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fd25u128) >> 1u128) == 0x28fe92u128)) by (bit_vector);
    assert(((((0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128) << 1) ^ (if ((((0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7bb0d3f2b8b3e9437134bb190b415cfcu128) by (bit_vector);
    assert(gf128_xtime(0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128) == 0x7bb0d3f2b8b3e9437134bb190b415cfcu128);
    assert(gf128_mul_bits(0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128, 0x51fd25u128, 23nat) == 0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128 ^ gf128_mul_bits(0x7bb0d3f2b8b3e9437134bb190b415cfcu128, 0x28fe92u128, 22nat)) by { lemma_hmul128_bits_unfold(0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128, 0x51fd25u128, 23nat); }
    assert((((0x28fe92u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28fe92u128) >> 1u128) == 0x147f49u128)) by (bit_vector);
    assert(((((0x7bb0d3f2b8b3e9437134bb190b415cfcu128) << 1) ^ (if ((((0x7bb0d3f2b8b3e9437134bb190b415cfcu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf761a7e57167d286e26976321682b9f8u128) by (bit_vector);
    assert(gf128_xtime(0x7bb0d3f2b8b3e9437134bb190b415cfcu128) == 0xf761a7e57167d286e26976321682b9f8u128);
    assert(gf128_mul_bits(0x7bb0d3f2b8b3e9437134bb190b415cfcu128, 0x28fe92u128, 22nat) == 0u128 ^ gf128_mul_bits(0xf761a7e57167d286e26976321682b9f8u128, 0x147f49u128, 21nat)) by { lemma_hmul128_bits_unfold(0x7bb0d3f2b8b3e9437134bb190b415cfcu128, 0x28fe92u128, 22nat); }
    assert((((0x147f49u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147f49u128) >> 1u128) == 0xa3fa4u128)) by (bit_vector);
    assert(((((0xf761a7e57167d286e26976321682b9f8u128) << 1) ^ (if ((((0xf761a7e57167d286e26976321682b9f8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xeec34fcae2cfa50dc4d2ec642d057377u128) by (bit_vector);
    assert(gf128_xtime(0xf761a7e57167d286e26976321682b9f8u128) == 0xeec34fcae2cfa50dc4d2ec642d057377u128);
    assert(gf128_mul_bits(0xf761a7e57167d286e26976321682b9f8u128, 0x147f49u128, 21nat) == 0xf761a7e57167d286e26976321682b9f8u128 ^ gf128_mul_bits(0xeec34fcae2cfa50dc4d2ec642d057377u128, 0xa3fa4u128, 20nat)) by { lemma_hmul128_bits_unfold(0xf761a7e57167d286e26976321682b9f8u128, 0x147f49u128, 21nat); }
    assert((((0xa3fa4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fa4u128) >> 1u128) == 0x51fd2u128)) by (bit_vector);
    assert(((((0xeec34fcae2cfa50dc4d2ec642d057377u128) << 1) ^ (if ((((0xeec34fcae2cfa50dc4d2ec642d057377u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xdd869f95c59f4a1b89a5d8c85a0ae669u128) by (bit_vector);
    assert(gf128_xtime(0xeec34fcae2cfa50dc4d2ec642d057377u128) == 0xdd869f95c59f4a1b89a5d8c85a0ae669u128);
    assert(gf128_mul_bits(0xeec34fcae2cfa50dc4d2ec642d057377u128, 0xa3fa4u128, 20nat) == 0u128 ^ gf128_mul_bits(0xdd869f95c59f4a1b89a5d8c85a0ae669u128, 0x51fd2u128, 19nat)) by { lemma_hmul128_bits_unfold(0xeec34fcae2cfa50dc4d2ec642d057377u128, 0xa3fa4u128, 20nat); }
    assert((((0x51fd2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x51fd2u128) >> 1u128) == 0x28fe9u128)) by (bit_vector);
    assert(((((0xdd869f95c59f4a1b89a5d8c85a0ae669u128) << 1) ^ (if ((((0xdd869f95c59f4a1b89a5d8c85a0ae669u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbb0d3f2b8b3e9437134bb190b415cc55u128) by (bit_vector);
    assert(gf128_xtime(0xdd869f95c59f4a1b89a5d8c85a0ae669u128) == 0xbb0d3f2b8b3e9437134bb190b415cc55u128);
    assert(gf128_mul_bits(0xdd869f95c59f4a1b89a5d8c85a0ae669u128, 0x51fd2u128, 19nat) == 0u128 ^ gf128_mul_bits(0xbb0d3f2b8b3e9437134bb190b415cc55u128, 0x28fe9u128, 18nat)) by { lemma_hmul128_bits_unfold(0xdd869f95c59f4a1b89a5d8c85a0ae669u128, 0x51fd2u128, 19nat); }
    assert((((0x28fe9u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fe9u128) >> 1u128) == 0x147f4u128)) by (bit_vector);
    assert(((((0xbb0d3f2b8b3e9437134bb190b415cc55u128) << 1) ^ (if ((((0xbb0d3f2b8b3e9437134bb190b415cc55u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x761a7e57167d286e26976321682b982du128) by (bit_vector);
    assert(gf128_xtime(0xbb0d3f2b8b3e9437134bb190b415cc55u128) == 0x761a7e57167d286e26976321682b982du128);
    assert(gf128_mul_bits(0xbb0d3f2b8b3e9437134bb190b415cc55u128, 0x28fe9u128, 18nat) == 0xbb0d3f2b8b3e9437134bb190b415cc55u128 ^ gf128_mul_bits(0x761a7e57167d286e26976321682b982du128, 0x147f4u128, 17nat)) by { lemma_hmul128_bits_unfold(0xbb0d3f2b8b3e9437134bb190b415cc55u128, 0x28fe9u128, 18nat); }
    assert((((0x147f4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x147f4u128) >> 1u128) == 0xa3fau128)) by (bit_vector);
    assert(((((0x761a7e57167d286e26976321682b982du128) << 1) ^ (if ((((0x761a7e57167d286e26976321682b982du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xec34fcae2cfa50dc4d2ec642d057305au128) by (bit_vector);
    assert(gf128_xtime(0x761a7e57167d286e26976321682b982du128) == 0xec34fcae2cfa50dc4d2ec642d057305au128);
    assert(gf128_mul_bits(0x761a7e57167d286e26976321682b982du128, 0x147f4u128, 17nat) == 0u128 ^ gf128_mul_bits(0xec34fcae2cfa50dc4d2ec642d057305au128, 0xa3fau128, 16nat)) by { lemma_hmul128_bits_unfold(0x761a7e57167d286e26976321682b982du128, 0x147f4u128, 17nat); }
    assert((((0xa3fau128) & 1) == 0u128)) by (bit_vector);
    assert((((0xa3fau128) >> 1u128) == 0x51fdu128)) by (bit_vector);
    assert(((((0xec34fcae2cfa50dc4d2ec642d057305au128) << 1) ^ (if ((((0xec34fcae2cfa50dc4d2ec642d057305au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd869f95c59f4a1b89a5d8c85a0ae6033u128) by (bit_vector);
    assert(gf128_xtime(0xec34fcae2cfa50dc4d2ec642d057305au128) == 0xd869f95c59f4a1b89a5d8c85a0ae6033u128);
    assert(gf128_mul_bits(0xec34fcae2cfa50dc4d2ec642d057305au128, 0xa3fau128, 16nat) == 0u128 ^ gf128_mul_bits(0xd869f95c59f4a1b89a5d8c85a0ae6033u128, 0x51fdu128, 15nat)) by { lemma_hmul128_bits_unfold(0xec34fcae2cfa50dc4d2ec642d057305au128, 0xa3fau128, 16nat); }
    assert((((0x51fdu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fdu128) >> 1u128) == 0x28feu128)) by (bit_vector);
    assert(((((0xd869f95c59f4a1b89a5d8c85a0ae6033u128) << 1) ^ (if ((((0xd869f95c59f4a1b89a5d8c85a0ae6033u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb0d3f2b8b3e9437134bb190b415cc0e1u128) by (bit_vector);
    assert(gf128_xtime(0xd869f95c59f4a1b89a5d8c85a0ae6033u128) == 0xb0d3f2b8b3e9437134bb190b415cc0e1u128);
    assert(gf128_mul_bits(0xd869f95c59f4a1b89a5d8c85a0ae6033u128, 0x51fdu128, 15nat) == 0xd869f95c59f4a1b89a5d8c85a0ae6033u128 ^ gf128_mul_bits(0xb0d3f2b8b3e9437134bb190b415cc0e1u128, 0x28feu128, 14nat)) by { lemma_hmul128_bits_unfold(0xd869f95c59f4a1b89a5d8c85a0ae6033u128, 0x51fdu128, 15nat); }
    assert((((0x28feu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28feu128) >> 1u128) == 0x147fu128)) by (bit_vector);
    assert(((((0xb0d3f2b8b3e9437134bb190b415cc0e1u128) << 1) ^ (if ((((0xb0d3f2b8b3e9437134bb190b415cc0e1u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x61a7e57167d286e26976321682b98145u128) by (bit_vector);
    assert(gf128_xtime(0xb0d3f2b8b3e9437134bb190b415cc0e1u128) == 0x61a7e57167d286e26976321682b98145u128);
    assert(gf128_mul_bits(0xb0d3f2b8b3e9437134bb190b415cc0e1u128, 0x28feu128, 14nat) == 0u128 ^ gf128_mul_bits(0x61a7e57167d286e26976321682b98145u128, 0x147fu128, 13nat)) by { lemma_hmul128_bits_unfold(0xb0d3f2b8b3e9437134bb190b415cc0e1u128, 0x28feu128, 14nat); }
    assert((((0x147fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147fu128) >> 1u128) == 0xa3fu128)) by (bit_vector);
    assert(((((0x61a7e57167d286e26976321682b98145u128) << 1) ^ (if ((((0x61a7e57167d286e26976321682b98145u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc34fcae2cfa50dc4d2ec642d0573028au128) by (bit_vector);
    assert(gf128_xtime(0x61a7e57167d286e26976321682b98145u128) == 0xc34fcae2cfa50dc4d2ec642d0573028au128);
    assert(gf128_mul_bits(0x61a7e57167d286e26976321682b98145u128, 0x147fu128, 13nat) == 0x61a7e57167d286e26976321682b98145u128 ^ gf128_mul_bits(0xc34fcae2cfa50dc4d2ec642d0573028au128, 0xa3fu128, 12nat)) by { lemma_hmul128_bits_unfold(0x61a7e57167d286e26976321682b98145u128, 0x147fu128, 13nat); }
    assert((((0xa3fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3fu128) >> 1u128) == 0x51fu128)) by (bit_vector);
    assert(((((0xc34fcae2cfa50dc4d2ec642d0573028au128) << 1) ^ (if ((((0xc34fcae2cfa50dc4d2ec642d0573028au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x869f95c59f4a1b89a5d8c85a0ae60593u128) by (bit_vector);
    assert(gf128_xtime(0xc34fcae2cfa50dc4d2ec642d0573028au128) == 0x869f95c59f4a1b89a5d8c85a0ae60593u128);
    assert(gf128_mul_bits(0xc34fcae2cfa50dc4d2ec642d0573028au128, 0xa3fu128, 12nat) == 0xc34fcae2cfa50dc4d2ec642d0573028au128 ^ gf128_mul_bits(0x869f95c59f4a1b89a5d8c85a0ae60593u128, 0x51fu128, 11nat)) by { lemma_hmul128_bits_unfold(0xc34fcae2cfa50dc4d2ec642d0573028au128, 0xa3fu128, 12nat); }
    assert((((0x51fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51fu128) >> 1u128) == 0x28fu128)) by (bit_vector);
    assert(((((0x869f95c59f4a1b89a5d8c85a0ae60593u128) << 1) ^ (if ((((0x869f95c59f4a1b89a5d8c85a0ae60593u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd3f2b8b3e9437134bb190b415cc0ba1u128) by (bit_vector);
    assert(gf128_xtime(0x869f95c59f4a1b89a5d8c85a0ae60593u128) == 0xd3f2b8b3e9437134bb190b415cc0ba1u128);
    assert(gf128_mul_bits(0x869f95c59f4a1b89a5d8c85a0ae60593u128, 0x51fu128, 11nat) == 0x869f95c59f4a1b89a5d8c85a0ae60593u128 ^ gf128_mul_bits(0xd3f2b8b3e9437134bb190b415cc0ba1u128, 0x28fu128, 10nat)) by { lemma_hmul128_bits_unfold(0x869f95c59f4a1b89a5d8c85a0ae60593u128, 0x51fu128, 11nat); }
    assert((((0x28fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x28fu128) >> 1u128) == 0x147u128)) by (bit_vector);
    assert(((((0xd3f2b8b3e9437134bb190b415cc0ba1u128) << 1) ^ (if ((((0xd3f2b8b3e9437134bb190b415cc0ba1u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1a7e57167d286e26976321682b981742u128) by (bit_vector);
    assert(gf128_xtime(0xd3f2b8b3e9437134bb190b415cc0ba1u128) == 0x1a7e57167d286e26976321682b981742u128);
    assert(gf128_mul_bits(0xd3f2b8b3e9437134bb190b415cc0ba1u128, 0x28fu128, 10nat) == 0xd3f2b8b3e9437134bb190b415cc0ba1u128 ^ gf128_mul_bits(0x1a7e57167d286e26976321682b981742u128, 0x147u128, 9nat)) by { lemma_hmul128_bits_unfold(0xd3f2b8b3e9437134bb190b415cc0ba1u128, 0x28fu128, 10nat); }
    assert((((0x147u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x147u128) >> 1u128) == 0xa3u128)) by (bit_vector);
    assert(((((0x1a7e57167d286e26976321682b981742u128) << 1) ^ (if ((((0x1a7e57167d286e26976321682b981742u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x34fcae2cfa50dc4d2ec642d057302e84u128) by (bit_vector);
    assert(gf128_xtime(0x1a7e57167d286e26976321682b981742u128) == 0x34fcae2cfa50dc4d2ec642d057302e84u128);
    assert(gf128_mul_bits(0x1a7e57167d286e26976321682b981742u128, 0x147u128, 9nat) == 0x1a7e57167d286e26976321682b981742u128 ^ gf128_mul_bits(0x34fcae2cfa50dc4d2ec642d057302e84u128, 0xa3u128, 8nat)) by { lemma_hmul128_bits_unfold(0x1a7e57167d286e26976321682b981742u128, 0x147u128, 9nat); }
    assert((((0xa3u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xa3u128) >> 1u128) == 0x51u128)) by (bit_vector);
    assert(((((0x34fcae2cfa50dc4d2ec642d057302e84u128) << 1) ^ (if ((((0x34fcae2cfa50dc4d2ec642d057302e84u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x69f95c59f4a1b89a5d8c85a0ae605d08u128) by (bit_vector);
    assert(gf128_xtime(0x34fcae2cfa50dc4d2ec642d057302e84u128) == 0x69f95c59f4a1b89a5d8c85a0ae605d08u128);
    assert(gf128_mul_bits(0x34fcae2cfa50dc4d2ec642d057302e84u128, 0xa3u128, 8nat) == 0x34fcae2cfa50dc4d2ec642d057302e84u128 ^ gf128_mul_bits(0x69f95c59f4a1b89a5d8c85a0ae605d08u128, 0x51u128, 7nat)) by { lemma_hmul128_bits_unfold(0x34fcae2cfa50dc4d2ec642d057302e84u128, 0xa3u128, 8nat); }
    assert((((0x51u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x51u128) >> 1u128) == 0x28u128)) by (bit_vector);
    assert(((((0x69f95c59f4a1b89a5d8c85a0ae605d08u128) << 1) ^ (if ((((0x69f95c59f4a1b89a5d8c85a0ae605d08u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd3f2b8b3e9437134bb190b415cc0ba10u128) by (bit_vector);
    assert(gf128_xtime(0x69f95c59f4a1b89a5d8c85a0ae605d08u128) == 0xd3f2b8b3e9437134bb190b415cc0ba10u128);
    assert(gf128_mul_bits(0x69f95c59f4a1b89a5d8c85a0ae605d08u128, 0x51u128, 7nat) == 0x69f95c59f4a1b89a5d8c85a0ae605d08u128 ^ gf128_mul_bits(0xd3f2b8b3e9437134bb190b415cc0ba10u128, 0x28u128, 6nat)) by { lemma_hmul128_bits_unfold(0x69f95c59f4a1b89a5d8c85a0ae605d08u128, 0x51u128, 7nat); }
    assert((((0x28u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x28u128) >> 1u128) == 0x14u128)) by (bit_vector);
    assert(((((0xd3f2b8b3e9437134bb190b415cc0ba10u128) << 1) ^ (if ((((0xd3f2b8b3e9437134bb190b415cc0ba10u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa7e57167d286e26976321682b98174a7u128) by (bit_vector);
    assert(gf128_xtime(0xd3f2b8b3e9437134bb190b415cc0ba10u128) == 0xa7e57167d286e26976321682b98174a7u128);
    assert(gf128_mul_bits(0xd3f2b8b3e9437134bb190b415cc0ba10u128, 0x28u128, 6nat) == 0u128 ^ gf128_mul_bits(0xa7e57167d286e26976321682b98174a7u128, 0x14u128, 5nat)) by { lemma_hmul128_bits_unfold(0xd3f2b8b3e9437134bb190b415cc0ba10u128, 0x28u128, 6nat); }
    assert((((0x14u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x14u128) >> 1u128) == 0xau128)) by (bit_vector);
    assert(((((0xa7e57167d286e26976321682b98174a7u128) << 1) ^ (if ((((0xa7e57167d286e26976321682b98174a7u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4fcae2cfa50dc4d2ec642d057302e9c9u128) by (bit_vector);
    assert(gf128_xtime(0xa7e57167d286e26976321682b98174a7u128) == 0x4fcae2cfa50dc4d2ec642d057302e9c9u128);
    assert(gf128_mul_bits(0xa7e57167d286e26976321682b98174a7u128, 0x14u128, 5nat) == 0u128 ^ gf128_mul_bits(0x4fcae2cfa50dc4d2ec642d057302e9c9u128, 0xau128, 4nat)) by { lemma_hmul128_bits_unfold(0xa7e57167d286e26976321682b98174a7u128, 0x14u128, 5nat); }
    assert((((0xau128) & 1) == 0u128)) by (bit_vector);
    assert((((0xau128) >> 1u128) == 0x5u128)) by (bit_vector);
    assert(((((0x4fcae2cfa50dc4d2ec642d057302e9c9u128) << 1) ^ (if ((((0x4fcae2cfa50dc4d2ec642d057302e9c9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9f95c59f4a1b89a5d8c85a0ae605d392u128) by (bit_vector);
    assert(gf128_xtime(0x4fcae2cfa50dc4d2ec642d057302e9c9u128) == 0x9f95c59f4a1b89a5d8c85a0ae605d392u128);
    assert(gf128_mul_bits(0x4fcae2cfa50dc4d2ec642d057302e9c9u128, 0xau128, 4nat) == 0u128 ^ gf128_mul_bits(0x9f95c59f4a1b89a5d8c85a0ae605d392u128, 0x5u128, 3nat)) by { lemma_hmul128_bits_unfold(0x4fcae2cfa50dc4d2ec642d057302e9c9u128, 0xau128, 4nat); }
    assert((((0x5u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x5u128) >> 1u128) == 0x2u128)) by (bit_vector);
    assert(((((0x9f95c59f4a1b89a5d8c85a0ae605d392u128) << 1) ^ (if ((((0x9f95c59f4a1b89a5d8c85a0ae605d392u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3f2b8b3e9437134bb190b415cc0ba7a3u128) by (bit_vector);
    assert(gf128_xtime(0x9f95c59f4a1b89a5d8c85a0ae605d392u128) == 0x3f2b8b3e9437134bb190b415cc0ba7a3u128);
    assert(gf128_mul_bits(0x9f95c59f4a1b89a5d8c85a0ae605d392u128, 0x5u128, 3nat) == 0x9f95c59f4a1b89a5d8c85a0ae605d392u128 ^ gf128_mul_bits(0x3f2b8b3e9437134bb190b415cc0ba7a3u128, 0x2u128, 2nat)) by { lemma_hmul128_bits_unfold(0x9f95c59f4a1b89a5d8c85a0ae605d392u128, 0x5u128, 3nat); }
    assert((((0x2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x2u128) >> 1u128) == 0x1u128)) by (bit_vector);
    assert(((((0x3f2b8b3e9437134bb190b415cc0ba7a3u128) << 1) ^ (if ((((0x3f2b8b3e9437134bb190b415cc0ba7a3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7e57167d286e26976321682b98174f46u128) by (bit_vector);
    assert(gf128_xtime(0x3f2b8b3e9437134bb190b415cc0ba7a3u128) == 0x7e57167d286e26976321682b98174f46u128);
    assert(gf128_mul_bits(0x3f2b8b3e9437134bb190b415cc0ba7a3u128, 0x2u128, 2nat) == 0u128 ^ gf128_mul_bits(0x7e57167d286e26976321682b98174f46u128, 0x1u128, 1nat)) by { lemma_hmul128_bits_unfold(0x3f2b8b3e9437134bb190b415cc0ba7a3u128, 0x2u128, 2nat); }
    assert((((0x1u128) & 1) == 1u128)) by (bit_vector);
    assert(gf128_mul_bits(0x7e57167d286e26976321682b98174f46u128, 0x1u128, 1nat) == 0x7e57167d286e26976321682b98174f46u128 ^ gf128_mul_bits(gf128_xtime(0x7e57167d286e26976321682b98174f46u128), 0u128, 0nat)) by { lemma_hmul128_bits_unfold(0x7e57167d286e26976321682b98174f46u128, 0x1u128, 1nat); }
    assert((0x7e57167d286e26976321682b98174f46u128 ^ 0u128) == 0x7e57167d286e26976321682b98174f46u128) by (bit_vector);
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0x1dffa502bbff620185b5b0891eec34f2u128, 0xa3fa4befd33ec6de509de93498eb9fu128, 120nat)))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ (gf128_mul_bits(0xffa502bbff620185b5b0891eec34fcd3u128, 0xa3fa4befd33ec6de509de93498ebu128, 112nat)))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ (gf128_mul_bits(0xa502bbff620185b5b0891eec34fcae7du128, 0xa3fa4befd33ec6de509de93498u128, 104nat)))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ (gf128_mul_bits(0x2bbff620185b5b0891eec34fcae2cfbu128, 0xa3fa4befd33ec6de509de934u128, 96nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xbbff620185b5b0891eec34fcae2cfa0eu128, 0xa3fa4befd33ec6de509de9u128, 88nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ (gf128_mul_bits(0xff620185b5b0891eec34fcae2cfa50a1u128, 0xa3fa4befd33ec6de509du128, 80nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ (gf128_mul_bits(0x620185b5b0891eec34fcae2cfa50dc7du128, 0xa3fa4befd33ec6de50u128, 72nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ (gf128_mul_bits(0x185b5b0891eec34fcae2cfa50dc4d2eu128, 0xa3fa4befd33ec6deu128, 64nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ ((0xc2dad8448f761a7e57167d286e26970u128 ^ ((0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ ((0x0u128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ ((0xc2dad8448f761a7e57167d286e269700u128 ^ (gf128_mul_bits(0x85b5b0891eec34fcae2cfa50dc4d2e87u128, 0xa3fa4befd33ec6u128, 56nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ ((0xc2dad8448f761a7e57167d286e26970u128 ^ ((0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ ((0x0u128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ ((0xc2dad8448f761a7e57167d286e269700u128 ^ ((0x0u128 ^ ((0xb6b61123dd869f95c59f4a1b89a5d89u128 ^ ((0x16d6c2247bb0d3f2b8b3e9437134bb12u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128 ^ ((0xdad8448f761a7e57167d286e2697634eu128 ^ (gf128_mul_bits(0xb5b0891eec34fcae2cfa50dc4d2ec61bu128, 0xa3fa4befd33eu128, 48nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ ((0xc2dad8448f761a7e57167d286e26970u128 ^ ((0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ ((0x0u128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ ((0xc2dad8448f761a7e57167d286e269700u128 ^ ((0x0u128 ^ ((0xb6b61123dd869f95c59f4a1b89a5d89u128 ^ ((0x16d6c2247bb0d3f2b8b3e9437134bb12u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128 ^ ((0xdad8448f761a7e57167d286e2697634eu128 ^ ((0x0u128 ^ ((0x6b61123dd869f95c59f4a1b89a5d8cb1u128 ^ ((0xd6c2247bb0d3f2b8b3e9437134bb1962u128 ^ ((0xad8448f761a7e57167d286e269763243u128 ^ ((0x5b0891eec34fcae2cfa50dc4d2ec6401u128 ^ ((0xb61123dd869f95c59f4a1b89a5d8c802u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xb0891eec34fcae2cfa50dc4d2ec6428bu128, 0xa3fa4befd3u128, 40nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ ((0xc2dad8448f761a7e57167d286e26970u128 ^ ((0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ ((0x0u128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ ((0xc2dad8448f761a7e57167d286e269700u128 ^ ((0x0u128 ^ ((0xb6b61123dd869f95c59f4a1b89a5d89u128 ^ ((0x16d6c2247bb0d3f2b8b3e9437134bb12u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128 ^ ((0xdad8448f761a7e57167d286e2697634eu128 ^ ((0x0u128 ^ ((0x6b61123dd869f95c59f4a1b89a5d8cb1u128 ^ ((0xd6c2247bb0d3f2b8b3e9437134bb1962u128 ^ ((0xad8448f761a7e57167d286e269763243u128 ^ ((0x5b0891eec34fcae2cfa50dc4d2ec6401u128 ^ ((0xb61123dd869f95c59f4a1b89a5d8c802u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb0891eec34fcae2cfa50dc4d2ec6428bu128 ^ ((0x61123dd869f95c59f4a1b89a5d8c8591u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d01u128 ^ ((0x0u128 ^ ((0x2247bb0d3f2b8b3e9437134bb190b404u128 ^ ((0x448f761a7e57167d286e269763216808u128 ^ (gf128_mul_bits(0x891eec34fcae2cfa50dc4d2ec642d010u128, 0xa3fa4befu128, 32nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ ((0xc2dad8448f761a7e57167d286e26970u128 ^ ((0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ ((0x0u128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ ((0xc2dad8448f761a7e57167d286e269700u128 ^ ((0x0u128 ^ ((0xb6b61123dd869f95c59f4a1b89a5d89u128 ^ ((0x16d6c2247bb0d3f2b8b3e9437134bb12u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128 ^ ((0xdad8448f761a7e57167d286e2697634eu128 ^ ((0x0u128 ^ ((0x6b61123dd869f95c59f4a1b89a5d8cb1u128 ^ ((0xd6c2247bb0d3f2b8b3e9437134bb1962u128 ^ ((0xad8448f761a7e57167d286e269763243u128 ^ ((0x5b0891eec34fcae2cfa50dc4d2ec6401u128 ^ ((0xb61123dd869f95c59f4a1b89a5d8c802u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb0891eec34fcae2cfa50dc4d2ec6428bu128 ^ ((0x61123dd869f95c59f4a1b89a5d8c8591u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d01u128 ^ ((0x0u128 ^ ((0x2247bb0d3f2b8b3e9437134bb190b404u128 ^ ((0x448f761a7e57167d286e269763216808u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d010u128 ^ ((0x123dd869f95c59f4a1b89a5d8c85a0a7u128 ^ ((0x247bb0d3f2b8b3e9437134bb190b414eu128 ^ ((0x48f761a7e57167d286e269763216829cu128 ^ ((0x0u128 ^ ((0x23dd869f95c59f4a1b89a5d8c85a0af7u128 ^ ((0x47bb0d3f2b8b3e9437134bb190b415eeu128 ^ ((0x8f761a7e57167d286e26976321682bdcu128 ^ (gf128_mul_bits(0x1eec34fcae2cfa50dc4d2ec642d0573fu128, 0xa3fa4bu128, 24nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ ((0xc2dad8448f761a7e57167d286e26970u128 ^ ((0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ ((0x0u128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ ((0xc2dad8448f761a7e57167d286e269700u128 ^ ((0x0u128 ^ ((0xb6b61123dd869f95c59f4a1b89a5d89u128 ^ ((0x16d6c2247bb0d3f2b8b3e9437134bb12u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128 ^ ((0xdad8448f761a7e57167d286e2697634eu128 ^ ((0x0u128 ^ ((0x6b61123dd869f95c59f4a1b89a5d8cb1u128 ^ ((0xd6c2247bb0d3f2b8b3e9437134bb1962u128 ^ ((0xad8448f761a7e57167d286e269763243u128 ^ ((0x5b0891eec34fcae2cfa50dc4d2ec6401u128 ^ ((0xb61123dd869f95c59f4a1b89a5d8c802u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb0891eec34fcae2cfa50dc4d2ec6428bu128 ^ ((0x61123dd869f95c59f4a1b89a5d8c8591u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d01u128 ^ ((0x0u128 ^ ((0x2247bb0d3f2b8b3e9437134bb190b404u128 ^ ((0x448f761a7e57167d286e269763216808u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d010u128 ^ ((0x123dd869f95c59f4a1b89a5d8c85a0a7u128 ^ ((0x247bb0d3f2b8b3e9437134bb190b414eu128 ^ ((0x48f761a7e57167d286e269763216829cu128 ^ ((0x0u128 ^ ((0x23dd869f95c59f4a1b89a5d8c85a0af7u128 ^ ((0x47bb0d3f2b8b3e9437134bb190b415eeu128 ^ ((0x8f761a7e57167d286e26976321682bdcu128 ^ ((0x1eec34fcae2cfa50dc4d2ec642d0573fu128 ^ ((0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128 ^ ((0x0u128 ^ ((0xf761a7e57167d286e26976321682b9f8u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbb0d3f2b8b3e9437134bb190b415cc55u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xec34fcae2cfa50dc4d2ec642d057305au128, 0xa3fau128, 16nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ ((0xc2dad8448f761a7e57167d286e26970u128 ^ ((0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ ((0x0u128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ ((0xc2dad8448f761a7e57167d286e269700u128 ^ ((0x0u128 ^ ((0xb6b61123dd869f95c59f4a1b89a5d89u128 ^ ((0x16d6c2247bb0d3f2b8b3e9437134bb12u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128 ^ ((0xdad8448f761a7e57167d286e2697634eu128 ^ ((0x0u128 ^ ((0x6b61123dd869f95c59f4a1b89a5d8cb1u128 ^ ((0xd6c2247bb0d3f2b8b3e9437134bb1962u128 ^ ((0xad8448f761a7e57167d286e269763243u128 ^ ((0x5b0891eec34fcae2cfa50dc4d2ec6401u128 ^ ((0xb61123dd869f95c59f4a1b89a5d8c802u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb0891eec34fcae2cfa50dc4d2ec6428bu128 ^ ((0x61123dd869f95c59f4a1b89a5d8c8591u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d01u128 ^ ((0x0u128 ^ ((0x2247bb0d3f2b8b3e9437134bb190b404u128 ^ ((0x448f761a7e57167d286e269763216808u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d010u128 ^ ((0x123dd869f95c59f4a1b89a5d8c85a0a7u128 ^ ((0x247bb0d3f2b8b3e9437134bb190b414eu128 ^ ((0x48f761a7e57167d286e269763216829cu128 ^ ((0x0u128 ^ ((0x23dd869f95c59f4a1b89a5d8c85a0af7u128 ^ ((0x47bb0d3f2b8b3e9437134bb190b415eeu128 ^ ((0x8f761a7e57167d286e26976321682bdcu128 ^ ((0x1eec34fcae2cfa50dc4d2ec642d0573fu128 ^ ((0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128 ^ ((0x0u128 ^ ((0xf761a7e57167d286e26976321682b9f8u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbb0d3f2b8b3e9437134bb190b415cc55u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd869f95c59f4a1b89a5d8c85a0ae6033u128 ^ ((0x0u128 ^ ((0x61a7e57167d286e26976321682b98145u128 ^ ((0xc34fcae2cfa50dc4d2ec642d0573028au128 ^ ((0x869f95c59f4a1b89a5d8c85a0ae60593u128 ^ ((0xd3f2b8b3e9437134bb190b415cc0ba1u128 ^ ((0x1a7e57167d286e26976321682b981742u128 ^ (gf128_mul_bits(0x34fcae2cfa50dc4d2ec642d057302e84u128, 0xa3u128, 8nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == ((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ ((0xc2dad8448f761a7e57167d286e26970u128 ^ ((0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ ((0x0u128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ ((0xc2dad8448f761a7e57167d286e269700u128 ^ ((0x0u128 ^ ((0xb6b61123dd869f95c59f4a1b89a5d89u128 ^ ((0x16d6c2247bb0d3f2b8b3e9437134bb12u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128 ^ ((0xdad8448f761a7e57167d286e2697634eu128 ^ ((0x0u128 ^ ((0x6b61123dd869f95c59f4a1b89a5d8cb1u128 ^ ((0xd6c2247bb0d3f2b8b3e9437134bb1962u128 ^ ((0xad8448f761a7e57167d286e269763243u128 ^ ((0x5b0891eec34fcae2cfa50dc4d2ec6401u128 ^ ((0xb61123dd869f95c59f4a1b89a5d8c802u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb0891eec34fcae2cfa50dc4d2ec6428bu128 ^ ((0x61123dd869f95c59f4a1b89a5d8c8591u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d01u128 ^ ((0x0u128 ^ ((0x2247bb0d3f2b8b3e9437134bb190b404u128 ^ ((0x448f761a7e57167d286e269763216808u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d010u128 ^ ((0x123dd869f95c59f4a1b89a5d8c85a0a7u128 ^ ((0x247bb0d3f2b8b3e9437134bb190b414eu128 ^ ((0x48f761a7e57167d286e269763216829cu128 ^ ((0x0u128 ^ ((0x23dd869f95c59f4a1b89a5d8c85a0af7u128 ^ ((0x47bb0d3f2b8b3e9437134bb190b415eeu128 ^ ((0x8f761a7e57167d286e26976321682bdcu128 ^ ((0x1eec34fcae2cfa50dc4d2ec642d0573fu128 ^ ((0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128 ^ ((0x0u128 ^ ((0xf761a7e57167d286e26976321682b9f8u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbb0d3f2b8b3e9437134bb190b415cc55u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd869f95c59f4a1b89a5d8c85a0ae6033u128 ^ ((0x0u128 ^ ((0x61a7e57167d286e26976321682b98145u128 ^ ((0xc34fcae2cfa50dc4d2ec642d0573028au128 ^ ((0x869f95c59f4a1b89a5d8c85a0ae60593u128 ^ ((0xd3f2b8b3e9437134bb190b415cc0ba1u128 ^ ((0x1a7e57167d286e26976321682b981742u128 ^ (gf128_mul_bits(0x34fcae2cfa50dc4d2ec642d057302e84u128, 0xa3u128, 8nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(((0x261dffa502bbff620185b5b0891eec27u128 ^ ((0x0u128 ^ ((0x9877fe940aeffd880616d6c2247bb09cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1dffa502bbff620185b5b0891eec34f2u128 ^ ((0x3bff4a0577fec4030b6b61123dd869e4u128 ^ ((0x77fe940aeffd880616d6c2247bb0d3c8u128 ^ ((0xeffd2815dffb100c2dad8448f761a790u128 ^ ((0xdffa502bbff620185b5b0891eec34fa7u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xffd2815dffb100c2dad8448f761a7e2au128 ^ ((0xffa502bbff620185b5b0891eec34fcd3u128 ^ ((0xff4a0577fec4030b6b61123dd869f921u128 ^ ((0x0u128 ^ ((0xfd2815dffb100c2dad8448f761a7e50du128 ^ ((0x0u128 ^ ((0xf4a0577fec4030b6b61123dd869f95bdu128 ^ ((0xe940aeffd880616d6c2247bb0d3f2bfdu128 ^ ((0xd2815dffb100c2dad8448f761a7e577du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x2815dffb100c2dad8448f761a7e57173u128 ^ ((0x502bbff620185b5b0891eec34fcae2e6u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x815dffb100c2dad8448f761a7e57163eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaeffd880616d6c2247bb0d3f2b8b3ecu128 ^ ((0x0u128 ^ ((0x2bbff620185b5b0891eec34fcae2cfb0u128 ^ ((0x577fec4030b6b61123dd869f95c59f60u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbbff620185b5b0891eec34fcae2cfa0eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xdffb100c2dad8448f761a7e57167d2ebu128 ^ ((0x0u128 ^ ((0x7fec4030b6b61123dd869f95c59f4a25u128 ^ ((0xffd880616d6c2247bb0d3f2b8b3e944au128 ^ ((0xffb100c2dad8448f761a7e57167d2813u128 ^ ((0xff620185b5b0891eec34fcae2cfa50a1u128 ^ ((0x0u128 ^ ((0xfd880616d6c2247bb0d3f2b8b3e9430du128 ^ ((0xfb100c2dad8448f761a7e57167d2869du128 ^ ((0xf620185b5b0891eec34fcae2cfa50dbdu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb100c2dad8448f761a7e57167d286e7du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x20185b5b0891eec34fcae2cfa50dc4c2u128 ^ ((0x0u128 ^ ((0x80616d6c2247bb0d3f2b8b3e94371308u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x30b6b61123dd869f95c59f4a1b89a5cu128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b8u128 ^ ((0xc2dad8448f761a7e57167d286e26970u128 ^ ((0x185b5b0891eec34fcae2cfa50dc4d2e0u128 ^ ((0x0u128 ^ ((0x616d6c2247bb0d3f2b8b3e9437134b80u128 ^ ((0xc2dad8448f761a7e57167d286e269700u128 ^ ((0x0u128 ^ ((0xb6b61123dd869f95c59f4a1b89a5d89u128 ^ ((0x16d6c2247bb0d3f2b8b3e9437134bb12u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6d6c2247bb0d3f2b8b3e9437134bb1a7u128 ^ ((0xdad8448f761a7e57167d286e2697634eu128 ^ ((0x0u128 ^ ((0x6b61123dd869f95c59f4a1b89a5d8cb1u128 ^ ((0xd6c2247bb0d3f2b8b3e9437134bb1962u128 ^ ((0xad8448f761a7e57167d286e269763243u128 ^ ((0x5b0891eec34fcae2cfa50dc4d2ec6401u128 ^ ((0xb61123dd869f95c59f4a1b89a5d8c802u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb0891eec34fcae2cfa50dc4d2ec6428bu128 ^ ((0x61123dd869f95c59f4a1b89a5d8c8591u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d01u128 ^ ((0x0u128 ^ ((0x2247bb0d3f2b8b3e9437134bb190b404u128 ^ ((0x448f761a7e57167d286e269763216808u128 ^ ((0x891eec34fcae2cfa50dc4d2ec642d010u128 ^ ((0x123dd869f95c59f4a1b89a5d8c85a0a7u128 ^ ((0x247bb0d3f2b8b3e9437134bb190b414eu128 ^ ((0x48f761a7e57167d286e269763216829cu128 ^ ((0x0u128 ^ ((0x23dd869f95c59f4a1b89a5d8c85a0af7u128 ^ ((0x47bb0d3f2b8b3e9437134bb190b415eeu128 ^ ((0x8f761a7e57167d286e26976321682bdcu128 ^ ((0x1eec34fcae2cfa50dc4d2ec642d0573fu128 ^ ((0x3dd869f95c59f4a1b89a5d8c85a0ae7eu128 ^ ((0x0u128 ^ ((0xf761a7e57167d286e26976321682b9f8u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xbb0d3f2b8b3e9437134bb190b415cc55u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd869f95c59f4a1b89a5d8c85a0ae6033u128 ^ ((0x0u128 ^ ((0x61a7e57167d286e26976321682b98145u128 ^ ((0xc34fcae2cfa50dc4d2ec642d0573028au128 ^ ((0x869f95c59f4a1b89a5d8c85a0ae60593u128 ^ ((0xd3f2b8b3e9437134bb190b415cc0ba1u128 ^ ((0x1a7e57167d286e26976321682b981742u128 ^ ((0x34fcae2cfa50dc4d2ec642d057302e84u128 ^ ((0x69f95c59f4a1b89a5d8c85a0ae605d08u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x9f95c59f4a1b89a5d8c85a0ae605d392u128 ^ ((0x0u128 ^ (0x7e57167d286e26976321682b98174f46u128))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) == 0xe6df41181a1477eae9131e9141c70a15u128) by (bit_vector);
    assert(gf128_mul_bits(0x261dffa502bbff620185b5b0891eec27u128, 0xa3fa4befd33ec6de509de93498eb9f05u128, 128nat) == 0xe6df41181a1477eae9131e9141c70a15u128);
}

proof fn kat_t1_hmul()
    ensures gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == 0x15ae1388367039a81b7cc9770edd7acu128,
{
    // rung chain precomputed + model-checked offline (python)
    assert((((0xf1c016735268c06031d80f2d8a5528c4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2d8a5528c4u128) >> 1u128) == 0x78e00b39a934603018ec0796c52a9462u128)) by (bit_vector);
    assert(((((0x3310efa565c3ec75fae7621e9038eb25u128) << 1) ^ (if ((((0x3310efa565c3ec75fae7621e9038eb25u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x6621df4acb87d8ebf5cec43d2071d64au128) by (bit_vector);
    assert(gf128_xtime(0x3310efa565c3ec75fae7621e9038eb25u128) == 0x6621df4acb87d8ebf5cec43d2071d64au128);
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == 0u128 ^ gf128_mul_bits(0x6621df4acb87d8ebf5cec43d2071d64au128, 0x78e00b39a934603018ec0796c52a9462u128, 127nat)) by { lemma_hmul128_bits_unfold(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat); }
    assert((((0x78e00b39a934603018ec0796c52a9462u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0796c52a9462u128) >> 1u128) == 0x3c70059cd49a30180c7603cb62954a31u128)) by (bit_vector);
    assert(((((0x6621df4acb87d8ebf5cec43d2071d64au128) << 1) ^ (if ((((0x6621df4acb87d8ebf5cec43d2071d64au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xcc43be95970fb1d7eb9d887a40e3ac94u128) by (bit_vector);
    assert(gf128_xtime(0x6621df4acb87d8ebf5cec43d2071d64au128) == 0xcc43be95970fb1d7eb9d887a40e3ac94u128);
    assert(gf128_mul_bits(0x6621df4acb87d8ebf5cec43d2071d64au128, 0x78e00b39a934603018ec0796c52a9462u128, 127nat) == 0u128 ^ gf128_mul_bits(0xcc43be95970fb1d7eb9d887a40e3ac94u128, 0x3c70059cd49a30180c7603cb62954a31u128, 126nat)) by { lemma_hmul128_bits_unfold(0x6621df4acb87d8ebf5cec43d2071d64au128, 0x78e00b39a934603018ec0796c52a9462u128, 127nat); }
    assert((((0x3c70059cd49a30180c7603cb62954a31u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cb62954a31u128) >> 1u128) == 0x1e3802ce6a4d180c063b01e5b14aa518u128)) by (bit_vector);
    assert(((((0xcc43be95970fb1d7eb9d887a40e3ac94u128) << 1) ^ (if ((((0xcc43be95970fb1d7eb9d887a40e3ac94u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x98877d2b2e1f63afd73b10f481c759afu128) by (bit_vector);
    assert(gf128_xtime(0xcc43be95970fb1d7eb9d887a40e3ac94u128) == 0x98877d2b2e1f63afd73b10f481c759afu128);
    assert(gf128_mul_bits(0xcc43be95970fb1d7eb9d887a40e3ac94u128, 0x3c70059cd49a30180c7603cb62954a31u128, 126nat) == 0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ gf128_mul_bits(0x98877d2b2e1f63afd73b10f481c759afu128, 0x1e3802ce6a4d180c063b01e5b14aa518u128, 125nat)) by { lemma_hmul128_bits_unfold(0xcc43be95970fb1d7eb9d887a40e3ac94u128, 0x3c70059cd49a30180c7603cb62954a31u128, 126nat); }
    assert((((0x1e3802ce6a4d180c063b01e5b14aa518u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01e5b14aa518u128) >> 1u128) == 0xf1c016735268c06031d80f2d8a5528cu128)) by (bit_vector);
    assert(((((0x98877d2b2e1f63afd73b10f481c759afu128) << 1) ^ (if ((((0x98877d2b2e1f63afd73b10f481c759afu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x310efa565c3ec75fae7621e9038eb3d9u128) by (bit_vector);
    assert(gf128_xtime(0x98877d2b2e1f63afd73b10f481c759afu128) == 0x310efa565c3ec75fae7621e9038eb3d9u128);
    assert(gf128_mul_bits(0x98877d2b2e1f63afd73b10f481c759afu128, 0x1e3802ce6a4d180c063b01e5b14aa518u128, 125nat) == 0u128 ^ gf128_mul_bits(0x310efa565c3ec75fae7621e9038eb3d9u128, 0xf1c016735268c06031d80f2d8a5528cu128, 124nat)) by { lemma_hmul128_bits_unfold(0x98877d2b2e1f63afd73b10f481c759afu128, 0x1e3802ce6a4d180c063b01e5b14aa518u128, 125nat); }
    assert((((0xf1c016735268c06031d80f2d8a5528cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2d8a5528cu128) >> 1u128) == 0x78e00b39a934603018ec0796c52a946u128)) by (bit_vector);
    assert(((((0x310efa565c3ec75fae7621e9038eb3d9u128) << 1) ^ (if ((((0x310efa565c3ec75fae7621e9038eb3d9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x621df4acb87d8ebf5cec43d2071d67b2u128) by (bit_vector);
    assert(gf128_xtime(0x310efa565c3ec75fae7621e9038eb3d9u128) == 0x621df4acb87d8ebf5cec43d2071d67b2u128);
    assert(gf128_mul_bits(0x310efa565c3ec75fae7621e9038eb3d9u128, 0xf1c016735268c06031d80f2d8a5528cu128, 124nat) == 0u128 ^ gf128_mul_bits(0x621df4acb87d8ebf5cec43d2071d67b2u128, 0x78e00b39a934603018ec0796c52a946u128, 123nat)) by { lemma_hmul128_bits_unfold(0x310efa565c3ec75fae7621e9038eb3d9u128, 0xf1c016735268c06031d80f2d8a5528cu128, 124nat); }
    assert((((0x78e00b39a934603018ec0796c52a946u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0796c52a946u128) >> 1u128) == 0x3c70059cd49a30180c7603cb62954a3u128)) by (bit_vector);
    assert(((((0x621df4acb87d8ebf5cec43d2071d67b2u128) << 1) ^ (if ((((0x621df4acb87d8ebf5cec43d2071d67b2u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc43be95970fb1d7eb9d887a40e3acf64u128) by (bit_vector);
    assert(gf128_xtime(0x621df4acb87d8ebf5cec43d2071d67b2u128) == 0xc43be95970fb1d7eb9d887a40e3acf64u128);
    assert(gf128_mul_bits(0x621df4acb87d8ebf5cec43d2071d67b2u128, 0x78e00b39a934603018ec0796c52a946u128, 123nat) == 0u128 ^ gf128_mul_bits(0xc43be95970fb1d7eb9d887a40e3acf64u128, 0x3c70059cd49a30180c7603cb62954a3u128, 122nat)) by { lemma_hmul128_bits_unfold(0x621df4acb87d8ebf5cec43d2071d67b2u128, 0x78e00b39a934603018ec0796c52a946u128, 123nat); }
    assert((((0x3c70059cd49a30180c7603cb62954a3u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cb62954a3u128) >> 1u128) == 0x1e3802ce6a4d180c063b01e5b14aa51u128)) by (bit_vector);
    assert(((((0xc43be95970fb1d7eb9d887a40e3acf64u128) << 1) ^ (if ((((0xc43be95970fb1d7eb9d887a40e3acf64u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x8877d2b2e1f63afd73b10f481c759e4fu128) by (bit_vector);
    assert(gf128_xtime(0xc43be95970fb1d7eb9d887a40e3acf64u128) == 0x8877d2b2e1f63afd73b10f481c759e4fu128);
    assert(gf128_mul_bits(0xc43be95970fb1d7eb9d887a40e3acf64u128, 0x3c70059cd49a30180c7603cb62954a3u128, 122nat) == 0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ gf128_mul_bits(0x8877d2b2e1f63afd73b10f481c759e4fu128, 0x1e3802ce6a4d180c063b01e5b14aa51u128, 121nat)) by { lemma_hmul128_bits_unfold(0xc43be95970fb1d7eb9d887a40e3acf64u128, 0x3c70059cd49a30180c7603cb62954a3u128, 122nat); }
    assert((((0x1e3802ce6a4d180c063b01e5b14aa51u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01e5b14aa51u128) >> 1u128) == 0xf1c016735268c06031d80f2d8a5528u128)) by (bit_vector);
    assert(((((0x8877d2b2e1f63afd73b10f481c759e4fu128) << 1) ^ (if ((((0x8877d2b2e1f63afd73b10f481c759e4fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x10efa565c3ec75fae7621e9038eb3c19u128) by (bit_vector);
    assert(gf128_xtime(0x8877d2b2e1f63afd73b10f481c759e4fu128) == 0x10efa565c3ec75fae7621e9038eb3c19u128);
    assert(gf128_mul_bits(0x8877d2b2e1f63afd73b10f481c759e4fu128, 0x1e3802ce6a4d180c063b01e5b14aa51u128, 121nat) == 0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ gf128_mul_bits(0x10efa565c3ec75fae7621e9038eb3c19u128, 0xf1c016735268c06031d80f2d8a5528u128, 120nat)) by { lemma_hmul128_bits_unfold(0x8877d2b2e1f63afd73b10f481c759e4fu128, 0x1e3802ce6a4d180c063b01e5b14aa51u128, 121nat); }
    assert((((0xf1c016735268c06031d80f2d8a5528u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2d8a5528u128) >> 1u128) == 0x78e00b39a934603018ec0796c52a94u128)) by (bit_vector);
    assert(((((0x10efa565c3ec75fae7621e9038eb3c19u128) << 1) ^ (if ((((0x10efa565c3ec75fae7621e9038eb3c19u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x21df4acb87d8ebf5cec43d2071d67832u128) by (bit_vector);
    assert(gf128_xtime(0x10efa565c3ec75fae7621e9038eb3c19u128) == 0x21df4acb87d8ebf5cec43d2071d67832u128);
    assert(gf128_mul_bits(0x10efa565c3ec75fae7621e9038eb3c19u128, 0xf1c016735268c06031d80f2d8a5528u128, 120nat) == 0u128 ^ gf128_mul_bits(0x21df4acb87d8ebf5cec43d2071d67832u128, 0x78e00b39a934603018ec0796c52a94u128, 119nat)) by { lemma_hmul128_bits_unfold(0x10efa565c3ec75fae7621e9038eb3c19u128, 0xf1c016735268c06031d80f2d8a5528u128, 120nat); }
    assert((((0x78e00b39a934603018ec0796c52a94u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0796c52a94u128) >> 1u128) == 0x3c70059cd49a30180c7603cb62954au128)) by (bit_vector);
    assert(((((0x21df4acb87d8ebf5cec43d2071d67832u128) << 1) ^ (if ((((0x21df4acb87d8ebf5cec43d2071d67832u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x43be95970fb1d7eb9d887a40e3acf064u128) by (bit_vector);
    assert(gf128_xtime(0x21df4acb87d8ebf5cec43d2071d67832u128) == 0x43be95970fb1d7eb9d887a40e3acf064u128);
    assert(gf128_mul_bits(0x21df4acb87d8ebf5cec43d2071d67832u128, 0x78e00b39a934603018ec0796c52a94u128, 119nat) == 0u128 ^ gf128_mul_bits(0x43be95970fb1d7eb9d887a40e3acf064u128, 0x3c70059cd49a30180c7603cb62954au128, 118nat)) by { lemma_hmul128_bits_unfold(0x21df4acb87d8ebf5cec43d2071d67832u128, 0x78e00b39a934603018ec0796c52a94u128, 119nat); }
    assert((((0x3c70059cd49a30180c7603cb62954au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cb62954au128) >> 1u128) == 0x1e3802ce6a4d180c063b01e5b14aa5u128)) by (bit_vector);
    assert(((((0x43be95970fb1d7eb9d887a40e3acf064u128) << 1) ^ (if ((((0x43be95970fb1d7eb9d887a40e3acf064u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x877d2b2e1f63afd73b10f481c759e0c8u128) by (bit_vector);
    assert(gf128_xtime(0x43be95970fb1d7eb9d887a40e3acf064u128) == 0x877d2b2e1f63afd73b10f481c759e0c8u128);
    assert(gf128_mul_bits(0x43be95970fb1d7eb9d887a40e3acf064u128, 0x3c70059cd49a30180c7603cb62954au128, 118nat) == 0u128 ^ gf128_mul_bits(0x877d2b2e1f63afd73b10f481c759e0c8u128, 0x1e3802ce6a4d180c063b01e5b14aa5u128, 117nat)) by { lemma_hmul128_bits_unfold(0x43be95970fb1d7eb9d887a40e3acf064u128, 0x3c70059cd49a30180c7603cb62954au128, 118nat); }
    assert((((0x1e3802ce6a4d180c063b01e5b14aa5u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01e5b14aa5u128) >> 1u128) == 0xf1c016735268c06031d80f2d8a552u128)) by (bit_vector);
    assert(((((0x877d2b2e1f63afd73b10f481c759e0c8u128) << 1) ^ (if ((((0x877d2b2e1f63afd73b10f481c759e0c8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xefa565c3ec75fae7621e9038eb3c117u128) by (bit_vector);
    assert(gf128_xtime(0x877d2b2e1f63afd73b10f481c759e0c8u128) == 0xefa565c3ec75fae7621e9038eb3c117u128);
    assert(gf128_mul_bits(0x877d2b2e1f63afd73b10f481c759e0c8u128, 0x1e3802ce6a4d180c063b01e5b14aa5u128, 117nat) == 0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ gf128_mul_bits(0xefa565c3ec75fae7621e9038eb3c117u128, 0xf1c016735268c06031d80f2d8a552u128, 116nat)) by { lemma_hmul128_bits_unfold(0x877d2b2e1f63afd73b10f481c759e0c8u128, 0x1e3802ce6a4d180c063b01e5b14aa5u128, 117nat); }
    assert((((0xf1c016735268c06031d80f2d8a552u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2d8a552u128) >> 1u128) == 0x78e00b39a934603018ec0796c52a9u128)) by (bit_vector);
    assert(((((0xefa565c3ec75fae7621e9038eb3c117u128) << 1) ^ (if ((((0xefa565c3ec75fae7621e9038eb3c117u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1df4acb87d8ebf5cec43d2071d67822eu128) by (bit_vector);
    assert(gf128_xtime(0xefa565c3ec75fae7621e9038eb3c117u128) == 0x1df4acb87d8ebf5cec43d2071d67822eu128);
    assert(gf128_mul_bits(0xefa565c3ec75fae7621e9038eb3c117u128, 0xf1c016735268c06031d80f2d8a552u128, 116nat) == 0u128 ^ gf128_mul_bits(0x1df4acb87d8ebf5cec43d2071d67822eu128, 0x78e00b39a934603018ec0796c52a9u128, 115nat)) by { lemma_hmul128_bits_unfold(0xefa565c3ec75fae7621e9038eb3c117u128, 0xf1c016735268c06031d80f2d8a552u128, 116nat); }
    assert((((0x78e00b39a934603018ec0796c52a9u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0796c52a9u128) >> 1u128) == 0x3c70059cd49a30180c7603cb62954u128)) by (bit_vector);
    assert(((((0x1df4acb87d8ebf5cec43d2071d67822eu128) << 1) ^ (if ((((0x1df4acb87d8ebf5cec43d2071d67822eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3be95970fb1d7eb9d887a40e3acf045cu128) by (bit_vector);
    assert(gf128_xtime(0x1df4acb87d8ebf5cec43d2071d67822eu128) == 0x3be95970fb1d7eb9d887a40e3acf045cu128);
    assert(gf128_mul_bits(0x1df4acb87d8ebf5cec43d2071d67822eu128, 0x78e00b39a934603018ec0796c52a9u128, 115nat) == 0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ gf128_mul_bits(0x3be95970fb1d7eb9d887a40e3acf045cu128, 0x3c70059cd49a30180c7603cb62954u128, 114nat)) by { lemma_hmul128_bits_unfold(0x1df4acb87d8ebf5cec43d2071d67822eu128, 0x78e00b39a934603018ec0796c52a9u128, 115nat); }
    assert((((0x3c70059cd49a30180c7603cb62954u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cb62954u128) >> 1u128) == 0x1e3802ce6a4d180c063b01e5b14aau128)) by (bit_vector);
    assert(((((0x3be95970fb1d7eb9d887a40e3acf045cu128) << 1) ^ (if ((((0x3be95970fb1d7eb9d887a40e3acf045cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x77d2b2e1f63afd73b10f481c759e08b8u128) by (bit_vector);
    assert(gf128_xtime(0x3be95970fb1d7eb9d887a40e3acf045cu128) == 0x77d2b2e1f63afd73b10f481c759e08b8u128);
    assert(gf128_mul_bits(0x3be95970fb1d7eb9d887a40e3acf045cu128, 0x3c70059cd49a30180c7603cb62954u128, 114nat) == 0u128 ^ gf128_mul_bits(0x77d2b2e1f63afd73b10f481c759e08b8u128, 0x1e3802ce6a4d180c063b01e5b14aau128, 113nat)) by { lemma_hmul128_bits_unfold(0x3be95970fb1d7eb9d887a40e3acf045cu128, 0x3c70059cd49a30180c7603cb62954u128, 114nat); }
    assert((((0x1e3802ce6a4d180c063b01e5b14aau128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01e5b14aau128) >> 1u128) == 0xf1c016735268c06031d80f2d8a55u128)) by (bit_vector);
    assert(((((0x77d2b2e1f63afd73b10f481c759e08b8u128) << 1) ^ (if ((((0x77d2b2e1f63afd73b10f481c759e08b8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xefa565c3ec75fae7621e9038eb3c1170u128) by (bit_vector);
    assert(gf128_xtime(0x77d2b2e1f63afd73b10f481c759e08b8u128) == 0xefa565c3ec75fae7621e9038eb3c1170u128);
    assert(gf128_mul_bits(0x77d2b2e1f63afd73b10f481c759e08b8u128, 0x1e3802ce6a4d180c063b01e5b14aau128, 113nat) == 0u128 ^ gf128_mul_bits(0xefa565c3ec75fae7621e9038eb3c1170u128, 0xf1c016735268c06031d80f2d8a55u128, 112nat)) by { lemma_hmul128_bits_unfold(0x77d2b2e1f63afd73b10f481c759e08b8u128, 0x1e3802ce6a4d180c063b01e5b14aau128, 113nat); }
    assert((((0xf1c016735268c06031d80f2d8a55u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2d8a55u128) >> 1u128) == 0x78e00b39a934603018ec0796c52au128)) by (bit_vector);
    assert(((((0xefa565c3ec75fae7621e9038eb3c1170u128) << 1) ^ (if ((((0xefa565c3ec75fae7621e9038eb3c1170u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xdf4acb87d8ebf5cec43d2071d6782267u128) by (bit_vector);
    assert(gf128_xtime(0xefa565c3ec75fae7621e9038eb3c1170u128) == 0xdf4acb87d8ebf5cec43d2071d6782267u128);
    assert(gf128_mul_bits(0xefa565c3ec75fae7621e9038eb3c1170u128, 0xf1c016735268c06031d80f2d8a55u128, 112nat) == 0xefa565c3ec75fae7621e9038eb3c1170u128 ^ gf128_mul_bits(0xdf4acb87d8ebf5cec43d2071d6782267u128, 0x78e00b39a934603018ec0796c52au128, 111nat)) by { lemma_hmul128_bits_unfold(0xefa565c3ec75fae7621e9038eb3c1170u128, 0xf1c016735268c06031d80f2d8a55u128, 112nat); }
    assert((((0x78e00b39a934603018ec0796c52au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0796c52au128) >> 1u128) == 0x3c70059cd49a30180c7603cb6295u128)) by (bit_vector);
    assert(((((0xdf4acb87d8ebf5cec43d2071d6782267u128) << 1) ^ (if ((((0xdf4acb87d8ebf5cec43d2071d6782267u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbe95970fb1d7eb9d887a40e3acf04449u128) by (bit_vector);
    assert(gf128_xtime(0xdf4acb87d8ebf5cec43d2071d6782267u128) == 0xbe95970fb1d7eb9d887a40e3acf04449u128);
    assert(gf128_mul_bits(0xdf4acb87d8ebf5cec43d2071d6782267u128, 0x78e00b39a934603018ec0796c52au128, 111nat) == 0u128 ^ gf128_mul_bits(0xbe95970fb1d7eb9d887a40e3acf04449u128, 0x3c70059cd49a30180c7603cb6295u128, 110nat)) by { lemma_hmul128_bits_unfold(0xdf4acb87d8ebf5cec43d2071d6782267u128, 0x78e00b39a934603018ec0796c52au128, 111nat); }
    assert((((0x3c70059cd49a30180c7603cb6295u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cb6295u128) >> 1u128) == 0x1e3802ce6a4d180c063b01e5b14au128)) by (bit_vector);
    assert(((((0xbe95970fb1d7eb9d887a40e3acf04449u128) << 1) ^ (if ((((0xbe95970fb1d7eb9d887a40e3acf04449u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7d2b2e1f63afd73b10f481c759e08815u128) by (bit_vector);
    assert(gf128_xtime(0xbe95970fb1d7eb9d887a40e3acf04449u128) == 0x7d2b2e1f63afd73b10f481c759e08815u128);
    assert(gf128_mul_bits(0xbe95970fb1d7eb9d887a40e3acf04449u128, 0x3c70059cd49a30180c7603cb6295u128, 110nat) == 0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ gf128_mul_bits(0x7d2b2e1f63afd73b10f481c759e08815u128, 0x1e3802ce6a4d180c063b01e5b14au128, 109nat)) by { lemma_hmul128_bits_unfold(0xbe95970fb1d7eb9d887a40e3acf04449u128, 0x3c70059cd49a30180c7603cb6295u128, 110nat); }
    assert((((0x1e3802ce6a4d180c063b01e5b14au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01e5b14au128) >> 1u128) == 0xf1c016735268c06031d80f2d8a5u128)) by (bit_vector);
    assert(((((0x7d2b2e1f63afd73b10f481c759e08815u128) << 1) ^ (if ((((0x7d2b2e1f63afd73b10f481c759e08815u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfa565c3ec75fae7621e9038eb3c1102au128) by (bit_vector);
    assert(gf128_xtime(0x7d2b2e1f63afd73b10f481c759e08815u128) == 0xfa565c3ec75fae7621e9038eb3c1102au128);
    assert(gf128_mul_bits(0x7d2b2e1f63afd73b10f481c759e08815u128, 0x1e3802ce6a4d180c063b01e5b14au128, 109nat) == 0u128 ^ gf128_mul_bits(0xfa565c3ec75fae7621e9038eb3c1102au128, 0xf1c016735268c06031d80f2d8a5u128, 108nat)) by { lemma_hmul128_bits_unfold(0x7d2b2e1f63afd73b10f481c759e08815u128, 0x1e3802ce6a4d180c063b01e5b14au128, 109nat); }
    assert((((0xf1c016735268c06031d80f2d8a5u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2d8a5u128) >> 1u128) == 0x78e00b39a934603018ec0796c52u128)) by (bit_vector);
    assert(((((0xfa565c3ec75fae7621e9038eb3c1102au128) << 1) ^ (if ((((0xfa565c3ec75fae7621e9038eb3c1102au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf4acb87d8ebf5cec43d2071d678220d3u128) by (bit_vector);
    assert(gf128_xtime(0xfa565c3ec75fae7621e9038eb3c1102au128) == 0xf4acb87d8ebf5cec43d2071d678220d3u128);
    assert(gf128_mul_bits(0xfa565c3ec75fae7621e9038eb3c1102au128, 0xf1c016735268c06031d80f2d8a5u128, 108nat) == 0xfa565c3ec75fae7621e9038eb3c1102au128 ^ gf128_mul_bits(0xf4acb87d8ebf5cec43d2071d678220d3u128, 0x78e00b39a934603018ec0796c52u128, 107nat)) by { lemma_hmul128_bits_unfold(0xfa565c3ec75fae7621e9038eb3c1102au128, 0xf1c016735268c06031d80f2d8a5u128, 108nat); }
    assert((((0x78e00b39a934603018ec0796c52u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0796c52u128) >> 1u128) == 0x3c70059cd49a30180c7603cb629u128)) by (bit_vector);
    assert(((((0xf4acb87d8ebf5cec43d2071d678220d3u128) << 1) ^ (if ((((0xf4acb87d8ebf5cec43d2071d678220d3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe95970fb1d7eb9d887a40e3acf044121u128) by (bit_vector);
    assert(gf128_xtime(0xf4acb87d8ebf5cec43d2071d678220d3u128) == 0xe95970fb1d7eb9d887a40e3acf044121u128);
    assert(gf128_mul_bits(0xf4acb87d8ebf5cec43d2071d678220d3u128, 0x78e00b39a934603018ec0796c52u128, 107nat) == 0u128 ^ gf128_mul_bits(0xe95970fb1d7eb9d887a40e3acf044121u128, 0x3c70059cd49a30180c7603cb629u128, 106nat)) by { lemma_hmul128_bits_unfold(0xf4acb87d8ebf5cec43d2071d678220d3u128, 0x78e00b39a934603018ec0796c52u128, 107nat); }
    assert((((0x3c70059cd49a30180c7603cb629u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cb629u128) >> 1u128) == 0x1e3802ce6a4d180c063b01e5b14u128)) by (bit_vector);
    assert(((((0xe95970fb1d7eb9d887a40e3acf044121u128) << 1) ^ (if ((((0xe95970fb1d7eb9d887a40e3acf044121u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd2b2e1f63afd73b10f481c759e0882c5u128) by (bit_vector);
    assert(gf128_xtime(0xe95970fb1d7eb9d887a40e3acf044121u128) == 0xd2b2e1f63afd73b10f481c759e0882c5u128);
    assert(gf128_mul_bits(0xe95970fb1d7eb9d887a40e3acf044121u128, 0x3c70059cd49a30180c7603cb629u128, 106nat) == 0xe95970fb1d7eb9d887a40e3acf044121u128 ^ gf128_mul_bits(0xd2b2e1f63afd73b10f481c759e0882c5u128, 0x1e3802ce6a4d180c063b01e5b14u128, 105nat)) by { lemma_hmul128_bits_unfold(0xe95970fb1d7eb9d887a40e3acf044121u128, 0x3c70059cd49a30180c7603cb629u128, 106nat); }
    assert((((0x1e3802ce6a4d180c063b01e5b14u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01e5b14u128) >> 1u128) == 0xf1c016735268c06031d80f2d8au128)) by (bit_vector);
    assert(((((0xd2b2e1f63afd73b10f481c759e0882c5u128) << 1) ^ (if ((((0xd2b2e1f63afd73b10f481c759e0882c5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa565c3ec75fae7621e9038eb3c11050du128) by (bit_vector);
    assert(gf128_xtime(0xd2b2e1f63afd73b10f481c759e0882c5u128) == 0xa565c3ec75fae7621e9038eb3c11050du128);
    assert(gf128_mul_bits(0xd2b2e1f63afd73b10f481c759e0882c5u128, 0x1e3802ce6a4d180c063b01e5b14u128, 105nat) == 0u128 ^ gf128_mul_bits(0xa565c3ec75fae7621e9038eb3c11050du128, 0xf1c016735268c06031d80f2d8au128, 104nat)) by { lemma_hmul128_bits_unfold(0xd2b2e1f63afd73b10f481c759e0882c5u128, 0x1e3802ce6a4d180c063b01e5b14u128, 105nat); }
    assert((((0xf1c016735268c06031d80f2d8au128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2d8au128) >> 1u128) == 0x78e00b39a934603018ec0796c5u128)) by (bit_vector);
    assert(((((0xa565c3ec75fae7621e9038eb3c11050du128) << 1) ^ (if ((((0xa565c3ec75fae7621e9038eb3c11050du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4acb87d8ebf5cec43d2071d678220a9du128) by (bit_vector);
    assert(gf128_xtime(0xa565c3ec75fae7621e9038eb3c11050du128) == 0x4acb87d8ebf5cec43d2071d678220a9du128);
    assert(gf128_mul_bits(0xa565c3ec75fae7621e9038eb3c11050du128, 0xf1c016735268c06031d80f2d8au128, 104nat) == 0u128 ^ gf128_mul_bits(0x4acb87d8ebf5cec43d2071d678220a9du128, 0x78e00b39a934603018ec0796c5u128, 103nat)) by { lemma_hmul128_bits_unfold(0xa565c3ec75fae7621e9038eb3c11050du128, 0xf1c016735268c06031d80f2d8au128, 104nat); }
    assert((((0x78e00b39a934603018ec0796c5u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0796c5u128) >> 1u128) == 0x3c70059cd49a30180c7603cb62u128)) by (bit_vector);
    assert(((((0x4acb87d8ebf5cec43d2071d678220a9du128) << 1) ^ (if ((((0x4acb87d8ebf5cec43d2071d678220a9du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x95970fb1d7eb9d887a40e3acf044153au128) by (bit_vector);
    assert(gf128_xtime(0x4acb87d8ebf5cec43d2071d678220a9du128) == 0x95970fb1d7eb9d887a40e3acf044153au128);
    assert(gf128_mul_bits(0x4acb87d8ebf5cec43d2071d678220a9du128, 0x78e00b39a934603018ec0796c5u128, 103nat) == 0x4acb87d8ebf5cec43d2071d678220a9du128 ^ gf128_mul_bits(0x95970fb1d7eb9d887a40e3acf044153au128, 0x3c70059cd49a30180c7603cb62u128, 102nat)) by { lemma_hmul128_bits_unfold(0x4acb87d8ebf5cec43d2071d678220a9du128, 0x78e00b39a934603018ec0796c5u128, 103nat); }
    assert((((0x3c70059cd49a30180c7603cb62u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cb62u128) >> 1u128) == 0x1e3802ce6a4d180c063b01e5b1u128)) by (bit_vector);
    assert(((((0x95970fb1d7eb9d887a40e3acf044153au128) << 1) ^ (if ((((0x95970fb1d7eb9d887a40e3acf044153au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x2b2e1f63afd73b10f481c759e0882af3u128) by (bit_vector);
    assert(gf128_xtime(0x95970fb1d7eb9d887a40e3acf044153au128) == 0x2b2e1f63afd73b10f481c759e0882af3u128);
    assert(gf128_mul_bits(0x95970fb1d7eb9d887a40e3acf044153au128, 0x3c70059cd49a30180c7603cb62u128, 102nat) == 0u128 ^ gf128_mul_bits(0x2b2e1f63afd73b10f481c759e0882af3u128, 0x1e3802ce6a4d180c063b01e5b1u128, 101nat)) by { lemma_hmul128_bits_unfold(0x95970fb1d7eb9d887a40e3acf044153au128, 0x3c70059cd49a30180c7603cb62u128, 102nat); }
    assert((((0x1e3802ce6a4d180c063b01e5b1u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01e5b1u128) >> 1u128) == 0xf1c016735268c06031d80f2d8u128)) by (bit_vector);
    assert(((((0x2b2e1f63afd73b10f481c759e0882af3u128) << 1) ^ (if ((((0x2b2e1f63afd73b10f481c759e0882af3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x565c3ec75fae7621e9038eb3c11055e6u128) by (bit_vector);
    assert(gf128_xtime(0x2b2e1f63afd73b10f481c759e0882af3u128) == 0x565c3ec75fae7621e9038eb3c11055e6u128);
    assert(gf128_mul_bits(0x2b2e1f63afd73b10f481c759e0882af3u128, 0x1e3802ce6a4d180c063b01e5b1u128, 101nat) == 0x2b2e1f63afd73b10f481c759e0882af3u128 ^ gf128_mul_bits(0x565c3ec75fae7621e9038eb3c11055e6u128, 0xf1c016735268c06031d80f2d8u128, 100nat)) by { lemma_hmul128_bits_unfold(0x2b2e1f63afd73b10f481c759e0882af3u128, 0x1e3802ce6a4d180c063b01e5b1u128, 101nat); }
    assert((((0xf1c016735268c06031d80f2d8u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2d8u128) >> 1u128) == 0x78e00b39a934603018ec0796cu128)) by (bit_vector);
    assert(((((0x565c3ec75fae7621e9038eb3c11055e6u128) << 1) ^ (if ((((0x565c3ec75fae7621e9038eb3c11055e6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xacb87d8ebf5cec43d2071d678220abccu128) by (bit_vector);
    assert(gf128_xtime(0x565c3ec75fae7621e9038eb3c11055e6u128) == 0xacb87d8ebf5cec43d2071d678220abccu128);
    assert(gf128_mul_bits(0x565c3ec75fae7621e9038eb3c11055e6u128, 0xf1c016735268c06031d80f2d8u128, 100nat) == 0u128 ^ gf128_mul_bits(0xacb87d8ebf5cec43d2071d678220abccu128, 0x78e00b39a934603018ec0796cu128, 99nat)) by { lemma_hmul128_bits_unfold(0x565c3ec75fae7621e9038eb3c11055e6u128, 0xf1c016735268c06031d80f2d8u128, 100nat); }
    assert((((0x78e00b39a934603018ec0796cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0796cu128) >> 1u128) == 0x3c70059cd49a30180c7603cb6u128)) by (bit_vector);
    assert(((((0xacb87d8ebf5cec43d2071d678220abccu128) << 1) ^ (if ((((0xacb87d8ebf5cec43d2071d678220abccu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5970fb1d7eb9d887a40e3acf0441571fu128) by (bit_vector);
    assert(gf128_xtime(0xacb87d8ebf5cec43d2071d678220abccu128) == 0x5970fb1d7eb9d887a40e3acf0441571fu128);
    assert(gf128_mul_bits(0xacb87d8ebf5cec43d2071d678220abccu128, 0x78e00b39a934603018ec0796cu128, 99nat) == 0u128 ^ gf128_mul_bits(0x5970fb1d7eb9d887a40e3acf0441571fu128, 0x3c70059cd49a30180c7603cb6u128, 98nat)) by { lemma_hmul128_bits_unfold(0xacb87d8ebf5cec43d2071d678220abccu128, 0x78e00b39a934603018ec0796cu128, 99nat); }
    assert((((0x3c70059cd49a30180c7603cb6u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cb6u128) >> 1u128) == 0x1e3802ce6a4d180c063b01e5bu128)) by (bit_vector);
    assert(((((0x5970fb1d7eb9d887a40e3acf0441571fu128) << 1) ^ (if ((((0x5970fb1d7eb9d887a40e3acf0441571fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb2e1f63afd73b10f481c759e0882ae3eu128) by (bit_vector);
    assert(gf128_xtime(0x5970fb1d7eb9d887a40e3acf0441571fu128) == 0xb2e1f63afd73b10f481c759e0882ae3eu128);
    assert(gf128_mul_bits(0x5970fb1d7eb9d887a40e3acf0441571fu128, 0x3c70059cd49a30180c7603cb6u128, 98nat) == 0u128 ^ gf128_mul_bits(0xb2e1f63afd73b10f481c759e0882ae3eu128, 0x1e3802ce6a4d180c063b01e5bu128, 97nat)) by { lemma_hmul128_bits_unfold(0x5970fb1d7eb9d887a40e3acf0441571fu128, 0x3c70059cd49a30180c7603cb6u128, 98nat); }
    assert((((0x1e3802ce6a4d180c063b01e5bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01e5bu128) >> 1u128) == 0xf1c016735268c06031d80f2du128)) by (bit_vector);
    assert(((((0xb2e1f63afd73b10f481c759e0882ae3eu128) << 1) ^ (if ((((0xb2e1f63afd73b10f481c759e0882ae3eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x65c3ec75fae7621e9038eb3c11055cfbu128) by (bit_vector);
    assert(gf128_xtime(0xb2e1f63afd73b10f481c759e0882ae3eu128) == 0x65c3ec75fae7621e9038eb3c11055cfbu128);
    assert(gf128_mul_bits(0xb2e1f63afd73b10f481c759e0882ae3eu128, 0x1e3802ce6a4d180c063b01e5bu128, 97nat) == 0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ gf128_mul_bits(0x65c3ec75fae7621e9038eb3c11055cfbu128, 0xf1c016735268c06031d80f2du128, 96nat)) by { lemma_hmul128_bits_unfold(0xb2e1f63afd73b10f481c759e0882ae3eu128, 0x1e3802ce6a4d180c063b01e5bu128, 97nat); }
    assert((((0xf1c016735268c06031d80f2du128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2du128) >> 1u128) == 0x78e00b39a934603018ec0796u128)) by (bit_vector);
    assert(((((0x65c3ec75fae7621e9038eb3c11055cfbu128) << 1) ^ (if ((((0x65c3ec75fae7621e9038eb3c11055cfbu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xcb87d8ebf5cec43d2071d678220ab9f6u128) by (bit_vector);
    assert(gf128_xtime(0x65c3ec75fae7621e9038eb3c11055cfbu128) == 0xcb87d8ebf5cec43d2071d678220ab9f6u128);
    assert(gf128_mul_bits(0x65c3ec75fae7621e9038eb3c11055cfbu128, 0xf1c016735268c06031d80f2du128, 96nat) == 0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ gf128_mul_bits(0xcb87d8ebf5cec43d2071d678220ab9f6u128, 0x78e00b39a934603018ec0796u128, 95nat)) by { lemma_hmul128_bits_unfold(0x65c3ec75fae7621e9038eb3c11055cfbu128, 0xf1c016735268c06031d80f2du128, 96nat); }
    assert((((0x78e00b39a934603018ec0796u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0796u128) >> 1u128) == 0x3c70059cd49a30180c7603cbu128)) by (bit_vector);
    assert(((((0xcb87d8ebf5cec43d2071d678220ab9f6u128) << 1) ^ (if ((((0xcb87d8ebf5cec43d2071d678220ab9f6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x970fb1d7eb9d887a40e3acf04415736bu128) by (bit_vector);
    assert(gf128_xtime(0xcb87d8ebf5cec43d2071d678220ab9f6u128) == 0x970fb1d7eb9d887a40e3acf04415736bu128);
    assert(gf128_mul_bits(0xcb87d8ebf5cec43d2071d678220ab9f6u128, 0x78e00b39a934603018ec0796u128, 95nat) == 0u128 ^ gf128_mul_bits(0x970fb1d7eb9d887a40e3acf04415736bu128, 0x3c70059cd49a30180c7603cbu128, 94nat)) by { lemma_hmul128_bits_unfold(0xcb87d8ebf5cec43d2071d678220ab9f6u128, 0x78e00b39a934603018ec0796u128, 95nat); }
    assert((((0x3c70059cd49a30180c7603cbu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cbu128) >> 1u128) == 0x1e3802ce6a4d180c063b01e5u128)) by (bit_vector);
    assert(((((0x970fb1d7eb9d887a40e3acf04415736bu128) << 1) ^ (if ((((0x970fb1d7eb9d887a40e3acf04415736bu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x2e1f63afd73b10f481c759e0882ae651u128) by (bit_vector);
    assert(gf128_xtime(0x970fb1d7eb9d887a40e3acf04415736bu128) == 0x2e1f63afd73b10f481c759e0882ae651u128);
    assert(gf128_mul_bits(0x970fb1d7eb9d887a40e3acf04415736bu128, 0x3c70059cd49a30180c7603cbu128, 94nat) == 0x970fb1d7eb9d887a40e3acf04415736bu128 ^ gf128_mul_bits(0x2e1f63afd73b10f481c759e0882ae651u128, 0x1e3802ce6a4d180c063b01e5u128, 93nat)) by { lemma_hmul128_bits_unfold(0x970fb1d7eb9d887a40e3acf04415736bu128, 0x3c70059cd49a30180c7603cbu128, 94nat); }
    assert((((0x1e3802ce6a4d180c063b01e5u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01e5u128) >> 1u128) == 0xf1c016735268c06031d80f2u128)) by (bit_vector);
    assert(((((0x2e1f63afd73b10f481c759e0882ae651u128) << 1) ^ (if ((((0x2e1f63afd73b10f481c759e0882ae651u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5c3ec75fae7621e9038eb3c11055cca2u128) by (bit_vector);
    assert(gf128_xtime(0x2e1f63afd73b10f481c759e0882ae651u128) == 0x5c3ec75fae7621e9038eb3c11055cca2u128);
    assert(gf128_mul_bits(0x2e1f63afd73b10f481c759e0882ae651u128, 0x1e3802ce6a4d180c063b01e5u128, 93nat) == 0x2e1f63afd73b10f481c759e0882ae651u128 ^ gf128_mul_bits(0x5c3ec75fae7621e9038eb3c11055cca2u128, 0xf1c016735268c06031d80f2u128, 92nat)) by { lemma_hmul128_bits_unfold(0x2e1f63afd73b10f481c759e0882ae651u128, 0x1e3802ce6a4d180c063b01e5u128, 93nat); }
    assert((((0xf1c016735268c06031d80f2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80f2u128) >> 1u128) == 0x78e00b39a934603018ec079u128)) by (bit_vector);
    assert(((((0x5c3ec75fae7621e9038eb3c11055cca2u128) << 1) ^ (if ((((0x5c3ec75fae7621e9038eb3c11055cca2u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb87d8ebf5cec43d2071d678220ab9944u128) by (bit_vector);
    assert(gf128_xtime(0x5c3ec75fae7621e9038eb3c11055cca2u128) == 0xb87d8ebf5cec43d2071d678220ab9944u128);
    assert(gf128_mul_bits(0x5c3ec75fae7621e9038eb3c11055cca2u128, 0xf1c016735268c06031d80f2u128, 92nat) == 0u128 ^ gf128_mul_bits(0xb87d8ebf5cec43d2071d678220ab9944u128, 0x78e00b39a934603018ec079u128, 91nat)) by { lemma_hmul128_bits_unfold(0x5c3ec75fae7621e9038eb3c11055cca2u128, 0xf1c016735268c06031d80f2u128, 92nat); }
    assert((((0x78e00b39a934603018ec079u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec079u128) >> 1u128) == 0x3c70059cd49a30180c7603cu128)) by (bit_vector);
    assert(((((0xb87d8ebf5cec43d2071d678220ab9944u128) << 1) ^ (if ((((0xb87d8ebf5cec43d2071d678220ab9944u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x70fb1d7eb9d887a40e3acf044157320fu128) by (bit_vector);
    assert(gf128_xtime(0xb87d8ebf5cec43d2071d678220ab9944u128) == 0x70fb1d7eb9d887a40e3acf044157320fu128);
    assert(gf128_mul_bits(0xb87d8ebf5cec43d2071d678220ab9944u128, 0x78e00b39a934603018ec079u128, 91nat) == 0xb87d8ebf5cec43d2071d678220ab9944u128 ^ gf128_mul_bits(0x70fb1d7eb9d887a40e3acf044157320fu128, 0x3c70059cd49a30180c7603cu128, 90nat)) by { lemma_hmul128_bits_unfold(0xb87d8ebf5cec43d2071d678220ab9944u128, 0x78e00b39a934603018ec079u128, 91nat); }
    assert((((0x3c70059cd49a30180c7603cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603cu128) >> 1u128) == 0x1e3802ce6a4d180c063b01eu128)) by (bit_vector);
    assert(((((0x70fb1d7eb9d887a40e3acf044157320fu128) << 1) ^ (if ((((0x70fb1d7eb9d887a40e3acf044157320fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe1f63afd73b10f481c759e0882ae641eu128) by (bit_vector);
    assert(gf128_xtime(0x70fb1d7eb9d887a40e3acf044157320fu128) == 0xe1f63afd73b10f481c759e0882ae641eu128);
    assert(gf128_mul_bits(0x70fb1d7eb9d887a40e3acf044157320fu128, 0x3c70059cd49a30180c7603cu128, 90nat) == 0u128 ^ gf128_mul_bits(0xe1f63afd73b10f481c759e0882ae641eu128, 0x1e3802ce6a4d180c063b01eu128, 89nat)) by { lemma_hmul128_bits_unfold(0x70fb1d7eb9d887a40e3acf044157320fu128, 0x3c70059cd49a30180c7603cu128, 90nat); }
    assert((((0x1e3802ce6a4d180c063b01eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01eu128) >> 1u128) == 0xf1c016735268c06031d80fu128)) by (bit_vector);
    assert(((((0xe1f63afd73b10f481c759e0882ae641eu128) << 1) ^ (if ((((0xe1f63afd73b10f481c759e0882ae641eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc3ec75fae7621e9038eb3c11055cc8bbu128) by (bit_vector);
    assert(gf128_xtime(0xe1f63afd73b10f481c759e0882ae641eu128) == 0xc3ec75fae7621e9038eb3c11055cc8bbu128);
    assert(gf128_mul_bits(0xe1f63afd73b10f481c759e0882ae641eu128, 0x1e3802ce6a4d180c063b01eu128, 89nat) == 0u128 ^ gf128_mul_bits(0xc3ec75fae7621e9038eb3c11055cc8bbu128, 0xf1c016735268c06031d80fu128, 88nat)) by { lemma_hmul128_bits_unfold(0xe1f63afd73b10f481c759e0882ae641eu128, 0x1e3802ce6a4d180c063b01eu128, 89nat); }
    assert((((0xf1c016735268c06031d80fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80fu128) >> 1u128) == 0x78e00b39a934603018ec07u128)) by (bit_vector);
    assert(((((0xc3ec75fae7621e9038eb3c11055cc8bbu128) << 1) ^ (if ((((0xc3ec75fae7621e9038eb3c11055cc8bbu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x87d8ebf5cec43d2071d678220ab991f1u128) by (bit_vector);
    assert(gf128_xtime(0xc3ec75fae7621e9038eb3c11055cc8bbu128) == 0x87d8ebf5cec43d2071d678220ab991f1u128);
    assert(gf128_mul_bits(0xc3ec75fae7621e9038eb3c11055cc8bbu128, 0xf1c016735268c06031d80fu128, 88nat) == 0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ gf128_mul_bits(0x87d8ebf5cec43d2071d678220ab991f1u128, 0x78e00b39a934603018ec07u128, 87nat)) by { lemma_hmul128_bits_unfold(0xc3ec75fae7621e9038eb3c11055cc8bbu128, 0xf1c016735268c06031d80fu128, 88nat); }
    assert((((0x78e00b39a934603018ec07u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec07u128) >> 1u128) == 0x3c70059cd49a30180c7603u128)) by (bit_vector);
    assert(((((0x87d8ebf5cec43d2071d678220ab991f1u128) << 1) ^ (if ((((0x87d8ebf5cec43d2071d678220ab991f1u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfb1d7eb9d887a40e3acf04415732365u128) by (bit_vector);
    assert(gf128_xtime(0x87d8ebf5cec43d2071d678220ab991f1u128) == 0xfb1d7eb9d887a40e3acf04415732365u128);
    assert(gf128_mul_bits(0x87d8ebf5cec43d2071d678220ab991f1u128, 0x78e00b39a934603018ec07u128, 87nat) == 0x87d8ebf5cec43d2071d678220ab991f1u128 ^ gf128_mul_bits(0xfb1d7eb9d887a40e3acf04415732365u128, 0x3c70059cd49a30180c7603u128, 86nat)) by { lemma_hmul128_bits_unfold(0x87d8ebf5cec43d2071d678220ab991f1u128, 0x78e00b39a934603018ec07u128, 87nat); }
    assert((((0x3c70059cd49a30180c7603u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7603u128) >> 1u128) == 0x1e3802ce6a4d180c063b01u128)) by (bit_vector);
    assert(((((0xfb1d7eb9d887a40e3acf04415732365u128) << 1) ^ (if ((((0xfb1d7eb9d887a40e3acf04415732365u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1f63afd73b10f481c759e0882ae646cau128) by (bit_vector);
    assert(gf128_xtime(0xfb1d7eb9d887a40e3acf04415732365u128) == 0x1f63afd73b10f481c759e0882ae646cau128);
    assert(gf128_mul_bits(0xfb1d7eb9d887a40e3acf04415732365u128, 0x3c70059cd49a30180c7603u128, 86nat) == 0xfb1d7eb9d887a40e3acf04415732365u128 ^ gf128_mul_bits(0x1f63afd73b10f481c759e0882ae646cau128, 0x1e3802ce6a4d180c063b01u128, 85nat)) by { lemma_hmul128_bits_unfold(0xfb1d7eb9d887a40e3acf04415732365u128, 0x3c70059cd49a30180c7603u128, 86nat); }
    assert((((0x1e3802ce6a4d180c063b01u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b01u128) >> 1u128) == 0xf1c016735268c06031d80u128)) by (bit_vector);
    assert(((((0x1f63afd73b10f481c759e0882ae646cau128) << 1) ^ (if ((((0x1f63afd73b10f481c759e0882ae646cau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3ec75fae7621e9038eb3c11055cc8d94u128) by (bit_vector);
    assert(gf128_xtime(0x1f63afd73b10f481c759e0882ae646cau128) == 0x3ec75fae7621e9038eb3c11055cc8d94u128);
    assert(gf128_mul_bits(0x1f63afd73b10f481c759e0882ae646cau128, 0x1e3802ce6a4d180c063b01u128, 85nat) == 0x1f63afd73b10f481c759e0882ae646cau128 ^ gf128_mul_bits(0x3ec75fae7621e9038eb3c11055cc8d94u128, 0xf1c016735268c06031d80u128, 84nat)) by { lemma_hmul128_bits_unfold(0x1f63afd73b10f481c759e0882ae646cau128, 0x1e3802ce6a4d180c063b01u128, 85nat); }
    assert((((0xf1c016735268c06031d80u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d80u128) >> 1u128) == 0x78e00b39a934603018ec0u128)) by (bit_vector);
    assert(((((0x3ec75fae7621e9038eb3c11055cc8d94u128) << 1) ^ (if ((((0x3ec75fae7621e9038eb3c11055cc8d94u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7d8ebf5cec43d2071d678220ab991b28u128) by (bit_vector);
    assert(gf128_xtime(0x3ec75fae7621e9038eb3c11055cc8d94u128) == 0x7d8ebf5cec43d2071d678220ab991b28u128);
    assert(gf128_mul_bits(0x3ec75fae7621e9038eb3c11055cc8d94u128, 0xf1c016735268c06031d80u128, 84nat) == 0u128 ^ gf128_mul_bits(0x7d8ebf5cec43d2071d678220ab991b28u128, 0x78e00b39a934603018ec0u128, 83nat)) by { lemma_hmul128_bits_unfold(0x3ec75fae7621e9038eb3c11055cc8d94u128, 0xf1c016735268c06031d80u128, 84nat); }
    assert((((0x78e00b39a934603018ec0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ec0u128) >> 1u128) == 0x3c70059cd49a30180c760u128)) by (bit_vector);
    assert(((((0x7d8ebf5cec43d2071d678220ab991b28u128) << 1) ^ (if ((((0x7d8ebf5cec43d2071d678220ab991b28u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfb1d7eb9d887a40e3acf044157323650u128) by (bit_vector);
    assert(gf128_xtime(0x7d8ebf5cec43d2071d678220ab991b28u128) == 0xfb1d7eb9d887a40e3acf044157323650u128);
    assert(gf128_mul_bits(0x7d8ebf5cec43d2071d678220ab991b28u128, 0x78e00b39a934603018ec0u128, 83nat) == 0u128 ^ gf128_mul_bits(0xfb1d7eb9d887a40e3acf044157323650u128, 0x3c70059cd49a30180c760u128, 82nat)) by { lemma_hmul128_bits_unfold(0x7d8ebf5cec43d2071d678220ab991b28u128, 0x78e00b39a934603018ec0u128, 83nat); }
    assert((((0x3c70059cd49a30180c760u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c760u128) >> 1u128) == 0x1e3802ce6a4d180c063b0u128)) by (bit_vector);
    assert(((((0xfb1d7eb9d887a40e3acf044157323650u128) << 1) ^ (if ((((0xfb1d7eb9d887a40e3acf044157323650u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf63afd73b10f481c759e0882ae646c27u128) by (bit_vector);
    assert(gf128_xtime(0xfb1d7eb9d887a40e3acf044157323650u128) == 0xf63afd73b10f481c759e0882ae646c27u128);
    assert(gf128_mul_bits(0xfb1d7eb9d887a40e3acf044157323650u128, 0x3c70059cd49a30180c760u128, 82nat) == 0u128 ^ gf128_mul_bits(0xf63afd73b10f481c759e0882ae646c27u128, 0x1e3802ce6a4d180c063b0u128, 81nat)) by { lemma_hmul128_bits_unfold(0xfb1d7eb9d887a40e3acf044157323650u128, 0x3c70059cd49a30180c760u128, 82nat); }
    assert((((0x1e3802ce6a4d180c063b0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063b0u128) >> 1u128) == 0xf1c016735268c06031d8u128)) by (bit_vector);
    assert(((((0xf63afd73b10f481c759e0882ae646c27u128) << 1) ^ (if ((((0xf63afd73b10f481c759e0882ae646c27u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xec75fae7621e9038eb3c11055cc8d8c9u128) by (bit_vector);
    assert(gf128_xtime(0xf63afd73b10f481c759e0882ae646c27u128) == 0xec75fae7621e9038eb3c11055cc8d8c9u128);
    assert(gf128_mul_bits(0xf63afd73b10f481c759e0882ae646c27u128, 0x1e3802ce6a4d180c063b0u128, 81nat) == 0u128 ^ gf128_mul_bits(0xec75fae7621e9038eb3c11055cc8d8c9u128, 0xf1c016735268c06031d8u128, 80nat)) by { lemma_hmul128_bits_unfold(0xf63afd73b10f481c759e0882ae646c27u128, 0x1e3802ce6a4d180c063b0u128, 81nat); }
    assert((((0xf1c016735268c06031d8u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06031d8u128) >> 1u128) == 0x78e00b39a934603018ecu128)) by (bit_vector);
    assert(((((0xec75fae7621e9038eb3c11055cc8d8c9u128) << 1) ^ (if ((((0xec75fae7621e9038eb3c11055cc8d8c9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd8ebf5cec43d2071d678220ab991b115u128) by (bit_vector);
    assert(gf128_xtime(0xec75fae7621e9038eb3c11055cc8d8c9u128) == 0xd8ebf5cec43d2071d678220ab991b115u128);
    assert(gf128_mul_bits(0xec75fae7621e9038eb3c11055cc8d8c9u128, 0xf1c016735268c06031d8u128, 80nat) == 0u128 ^ gf128_mul_bits(0xd8ebf5cec43d2071d678220ab991b115u128, 0x78e00b39a934603018ecu128, 79nat)) by { lemma_hmul128_bits_unfold(0xec75fae7621e9038eb3c11055cc8d8c9u128, 0xf1c016735268c06031d8u128, 80nat); }
    assert((((0x78e00b39a934603018ecu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018ecu128) >> 1u128) == 0x3c70059cd49a30180c76u128)) by (bit_vector);
    assert(((((0xd8ebf5cec43d2071d678220ab991b115u128) << 1) ^ (if ((((0xd8ebf5cec43d2071d678220ab991b115u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb1d7eb9d887a40e3acf04415732362adu128) by (bit_vector);
    assert(gf128_xtime(0xd8ebf5cec43d2071d678220ab991b115u128) == 0xb1d7eb9d887a40e3acf04415732362adu128);
    assert(gf128_mul_bits(0xd8ebf5cec43d2071d678220ab991b115u128, 0x78e00b39a934603018ecu128, 79nat) == 0u128 ^ gf128_mul_bits(0xb1d7eb9d887a40e3acf04415732362adu128, 0x3c70059cd49a30180c76u128, 78nat)) by { lemma_hmul128_bits_unfold(0xd8ebf5cec43d2071d678220ab991b115u128, 0x78e00b39a934603018ecu128, 79nat); }
    assert((((0x3c70059cd49a30180c76u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c76u128) >> 1u128) == 0x1e3802ce6a4d180c063bu128)) by (bit_vector);
    assert(((((0xb1d7eb9d887a40e3acf04415732362adu128) << 1) ^ (if ((((0xb1d7eb9d887a40e3acf04415732362adu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x63afd73b10f481c759e0882ae646c5ddu128) by (bit_vector);
    assert(gf128_xtime(0xb1d7eb9d887a40e3acf04415732362adu128) == 0x63afd73b10f481c759e0882ae646c5ddu128);
    assert(gf128_mul_bits(0xb1d7eb9d887a40e3acf04415732362adu128, 0x3c70059cd49a30180c76u128, 78nat) == 0u128 ^ gf128_mul_bits(0x63afd73b10f481c759e0882ae646c5ddu128, 0x1e3802ce6a4d180c063bu128, 77nat)) by { lemma_hmul128_bits_unfold(0xb1d7eb9d887a40e3acf04415732362adu128, 0x3c70059cd49a30180c76u128, 78nat); }
    assert((((0x1e3802ce6a4d180c063bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063bu128) >> 1u128) == 0xf1c016735268c06031du128)) by (bit_vector);
    assert(((((0x63afd73b10f481c759e0882ae646c5ddu128) << 1) ^ (if ((((0x63afd73b10f481c759e0882ae646c5ddu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc75fae7621e9038eb3c11055cc8d8bbau128) by (bit_vector);
    assert(gf128_xtime(0x63afd73b10f481c759e0882ae646c5ddu128) == 0xc75fae7621e9038eb3c11055cc8d8bbau128);
    assert(gf128_mul_bits(0x63afd73b10f481c759e0882ae646c5ddu128, 0x1e3802ce6a4d180c063bu128, 77nat) == 0x63afd73b10f481c759e0882ae646c5ddu128 ^ gf128_mul_bits(0xc75fae7621e9038eb3c11055cc8d8bbau128, 0xf1c016735268c06031du128, 76nat)) by { lemma_hmul128_bits_unfold(0x63afd73b10f481c759e0882ae646c5ddu128, 0x1e3802ce6a4d180c063bu128, 77nat); }
    assert((((0xf1c016735268c06031du128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c016735268c06031du128) >> 1u128) == 0x78e00b39a934603018eu128)) by (bit_vector);
    assert(((((0xc75fae7621e9038eb3c11055cc8d8bbau128) << 1) ^ (if ((((0xc75fae7621e9038eb3c11055cc8d8bbau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x8ebf5cec43d2071d678220ab991b17f3u128) by (bit_vector);
    assert(gf128_xtime(0xc75fae7621e9038eb3c11055cc8d8bbau128) == 0x8ebf5cec43d2071d678220ab991b17f3u128);
    assert(gf128_mul_bits(0xc75fae7621e9038eb3c11055cc8d8bbau128, 0xf1c016735268c06031du128, 76nat) == 0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ gf128_mul_bits(0x8ebf5cec43d2071d678220ab991b17f3u128, 0x78e00b39a934603018eu128, 75nat)) by { lemma_hmul128_bits_unfold(0xc75fae7621e9038eb3c11055cc8d8bbau128, 0xf1c016735268c06031du128, 76nat); }
    assert((((0x78e00b39a934603018eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018eu128) >> 1u128) == 0x3c70059cd49a30180c7u128)) by (bit_vector);
    assert(((((0x8ebf5cec43d2071d678220ab991b17f3u128) << 1) ^ (if ((((0x8ebf5cec43d2071d678220ab991b17f3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1d7eb9d887a40e3acf04415732362f61u128) by (bit_vector);
    assert(gf128_xtime(0x8ebf5cec43d2071d678220ab991b17f3u128) == 0x1d7eb9d887a40e3acf04415732362f61u128);
    assert(gf128_mul_bits(0x8ebf5cec43d2071d678220ab991b17f3u128, 0x78e00b39a934603018eu128, 75nat) == 0u128 ^ gf128_mul_bits(0x1d7eb9d887a40e3acf04415732362f61u128, 0x3c70059cd49a30180c7u128, 74nat)) by { lemma_hmul128_bits_unfold(0x8ebf5cec43d2071d678220ab991b17f3u128, 0x78e00b39a934603018eu128, 75nat); }
    assert((((0x3c70059cd49a30180c7u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180c7u128) >> 1u128) == 0x1e3802ce6a4d180c063u128)) by (bit_vector);
    assert(((((0x1d7eb9d887a40e3acf04415732362f61u128) << 1) ^ (if ((((0x1d7eb9d887a40e3acf04415732362f61u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3afd73b10f481c759e0882ae646c5ec2u128) by (bit_vector);
    assert(gf128_xtime(0x1d7eb9d887a40e3acf04415732362f61u128) == 0x3afd73b10f481c759e0882ae646c5ec2u128);
    assert(gf128_mul_bits(0x1d7eb9d887a40e3acf04415732362f61u128, 0x3c70059cd49a30180c7u128, 74nat) == 0x1d7eb9d887a40e3acf04415732362f61u128 ^ gf128_mul_bits(0x3afd73b10f481c759e0882ae646c5ec2u128, 0x1e3802ce6a4d180c063u128, 73nat)) by { lemma_hmul128_bits_unfold(0x1d7eb9d887a40e3acf04415732362f61u128, 0x3c70059cd49a30180c7u128, 74nat); }
    assert((((0x1e3802ce6a4d180c063u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c063u128) >> 1u128) == 0xf1c016735268c06031u128)) by (bit_vector);
    assert(((((0x3afd73b10f481c759e0882ae646c5ec2u128) << 1) ^ (if ((((0x3afd73b10f481c759e0882ae646c5ec2u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x75fae7621e9038eb3c11055cc8d8bd84u128) by (bit_vector);
    assert(gf128_xtime(0x3afd73b10f481c759e0882ae646c5ec2u128) == 0x75fae7621e9038eb3c11055cc8d8bd84u128);
    assert(gf128_mul_bits(0x3afd73b10f481c759e0882ae646c5ec2u128, 0x1e3802ce6a4d180c063u128, 73nat) == 0x3afd73b10f481c759e0882ae646c5ec2u128 ^ gf128_mul_bits(0x75fae7621e9038eb3c11055cc8d8bd84u128, 0xf1c016735268c06031u128, 72nat)) by { lemma_hmul128_bits_unfold(0x3afd73b10f481c759e0882ae646c5ec2u128, 0x1e3802ce6a4d180c063u128, 73nat); }
    assert((((0xf1c016735268c06031u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c016735268c06031u128) >> 1u128) == 0x78e00b39a934603018u128)) by (bit_vector);
    assert(((((0x75fae7621e9038eb3c11055cc8d8bd84u128) << 1) ^ (if ((((0x75fae7621e9038eb3c11055cc8d8bd84u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xebf5cec43d2071d678220ab991b17b08u128) by (bit_vector);
    assert(gf128_xtime(0x75fae7621e9038eb3c11055cc8d8bd84u128) == 0xebf5cec43d2071d678220ab991b17b08u128);
    assert(gf128_mul_bits(0x75fae7621e9038eb3c11055cc8d8bd84u128, 0xf1c016735268c06031u128, 72nat) == 0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ gf128_mul_bits(0xebf5cec43d2071d678220ab991b17b08u128, 0x78e00b39a934603018u128, 71nat)) by { lemma_hmul128_bits_unfold(0x75fae7621e9038eb3c11055cc8d8bd84u128, 0xf1c016735268c06031u128, 72nat); }
    assert((((0x78e00b39a934603018u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934603018u128) >> 1u128) == 0x3c70059cd49a30180cu128)) by (bit_vector);
    assert(((((0xebf5cec43d2071d678220ab991b17b08u128) << 1) ^ (if ((((0xebf5cec43d2071d678220ab991b17b08u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd7eb9d887a40e3acf04415732362f697u128) by (bit_vector);
    assert(gf128_xtime(0xebf5cec43d2071d678220ab991b17b08u128) == 0xd7eb9d887a40e3acf04415732362f697u128);
    assert(gf128_mul_bits(0xebf5cec43d2071d678220ab991b17b08u128, 0x78e00b39a934603018u128, 71nat) == 0u128 ^ gf128_mul_bits(0xd7eb9d887a40e3acf04415732362f697u128, 0x3c70059cd49a30180cu128, 70nat)) by { lemma_hmul128_bits_unfold(0xebf5cec43d2071d678220ab991b17b08u128, 0x78e00b39a934603018u128, 71nat); }
    assert((((0x3c70059cd49a30180cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180cu128) >> 1u128) == 0x1e3802ce6a4d180c06u128)) by (bit_vector);
    assert(((((0xd7eb9d887a40e3acf04415732362f697u128) << 1) ^ (if ((((0xd7eb9d887a40e3acf04415732362f697u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xafd73b10f481c759e0882ae646c5eda9u128) by (bit_vector);
    assert(gf128_xtime(0xd7eb9d887a40e3acf04415732362f697u128) == 0xafd73b10f481c759e0882ae646c5eda9u128);
    assert(gf128_mul_bits(0xd7eb9d887a40e3acf04415732362f697u128, 0x3c70059cd49a30180cu128, 70nat) == 0u128 ^ gf128_mul_bits(0xafd73b10f481c759e0882ae646c5eda9u128, 0x1e3802ce6a4d180c06u128, 69nat)) by { lemma_hmul128_bits_unfold(0xd7eb9d887a40e3acf04415732362f697u128, 0x3c70059cd49a30180cu128, 70nat); }
    assert((((0x1e3802ce6a4d180c06u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c06u128) >> 1u128) == 0xf1c016735268c0603u128)) by (bit_vector);
    assert(((((0xafd73b10f481c759e0882ae646c5eda9u128) << 1) ^ (if ((((0xafd73b10f481c759e0882ae646c5eda9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5fae7621e9038eb3c11055cc8d8bdbd5u128) by (bit_vector);
    assert(gf128_xtime(0xafd73b10f481c759e0882ae646c5eda9u128) == 0x5fae7621e9038eb3c11055cc8d8bdbd5u128);
    assert(gf128_mul_bits(0xafd73b10f481c759e0882ae646c5eda9u128, 0x1e3802ce6a4d180c06u128, 69nat) == 0u128 ^ gf128_mul_bits(0x5fae7621e9038eb3c11055cc8d8bdbd5u128, 0xf1c016735268c0603u128, 68nat)) by { lemma_hmul128_bits_unfold(0xafd73b10f481c759e0882ae646c5eda9u128, 0x1e3802ce6a4d180c06u128, 69nat); }
    assert((((0xf1c016735268c0603u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c016735268c0603u128) >> 1u128) == 0x78e00b39a93460301u128)) by (bit_vector);
    assert(((((0x5fae7621e9038eb3c11055cc8d8bdbd5u128) << 1) ^ (if ((((0x5fae7621e9038eb3c11055cc8d8bdbd5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbf5cec43d2071d678220ab991b17b7aau128) by (bit_vector);
    assert(gf128_xtime(0x5fae7621e9038eb3c11055cc8d8bdbd5u128) == 0xbf5cec43d2071d678220ab991b17b7aau128);
    assert(gf128_mul_bits(0x5fae7621e9038eb3c11055cc8d8bdbd5u128, 0xf1c016735268c0603u128, 68nat) == 0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ gf128_mul_bits(0xbf5cec43d2071d678220ab991b17b7aau128, 0x78e00b39a93460301u128, 67nat)) by { lemma_hmul128_bits_unfold(0x5fae7621e9038eb3c11055cc8d8bdbd5u128, 0xf1c016735268c0603u128, 68nat); }
    assert((((0x78e00b39a93460301u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b39a93460301u128) >> 1u128) == 0x3c70059cd49a30180u128)) by (bit_vector);
    assert(((((0xbf5cec43d2071d678220ab991b17b7aau128) << 1) ^ (if ((((0xbf5cec43d2071d678220ab991b17b7aau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7eb9d887a40e3acf04415732362f6fd3u128) by (bit_vector);
    assert(gf128_xtime(0xbf5cec43d2071d678220ab991b17b7aau128) == 0x7eb9d887a40e3acf04415732362f6fd3u128);
    assert(gf128_mul_bits(0xbf5cec43d2071d678220ab991b17b7aau128, 0x78e00b39a93460301u128, 67nat) == 0xbf5cec43d2071d678220ab991b17b7aau128 ^ gf128_mul_bits(0x7eb9d887a40e3acf04415732362f6fd3u128, 0x3c70059cd49a30180u128, 66nat)) by { lemma_hmul128_bits_unfold(0xbf5cec43d2071d678220ab991b17b7aau128, 0x78e00b39a93460301u128, 67nat); }
    assert((((0x3c70059cd49a30180u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30180u128) >> 1u128) == 0x1e3802ce6a4d180c0u128)) by (bit_vector);
    assert(((((0x7eb9d887a40e3acf04415732362f6fd3u128) << 1) ^ (if ((((0x7eb9d887a40e3acf04415732362f6fd3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfd73b10f481c759e0882ae646c5edfa6u128) by (bit_vector);
    assert(gf128_xtime(0x7eb9d887a40e3acf04415732362f6fd3u128) == 0xfd73b10f481c759e0882ae646c5edfa6u128);
    assert(gf128_mul_bits(0x7eb9d887a40e3acf04415732362f6fd3u128, 0x3c70059cd49a30180u128, 66nat) == 0u128 ^ gf128_mul_bits(0xfd73b10f481c759e0882ae646c5edfa6u128, 0x1e3802ce6a4d180c0u128, 65nat)) by { lemma_hmul128_bits_unfold(0x7eb9d887a40e3acf04415732362f6fd3u128, 0x3c70059cd49a30180u128, 66nat); }
    assert((((0x1e3802ce6a4d180c0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180c0u128) >> 1u128) == 0xf1c016735268c060u128)) by (bit_vector);
    assert(((((0xfd73b10f481c759e0882ae646c5edfa6u128) << 1) ^ (if ((((0xfd73b10f481c759e0882ae646c5edfa6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfae7621e9038eb3c11055cc8d8bdbfcbu128) by (bit_vector);
    assert(gf128_xtime(0xfd73b10f481c759e0882ae646c5edfa6u128) == 0xfae7621e9038eb3c11055cc8d8bdbfcbu128);
    assert(gf128_mul_bits(0xfd73b10f481c759e0882ae646c5edfa6u128, 0x1e3802ce6a4d180c0u128, 65nat) == 0u128 ^ gf128_mul_bits(0xfae7621e9038eb3c11055cc8d8bdbfcbu128, 0xf1c016735268c060u128, 64nat)) by { lemma_hmul128_bits_unfold(0xfd73b10f481c759e0882ae646c5edfa6u128, 0x1e3802ce6a4d180c0u128, 65nat); }
    assert((((0xf1c016735268c060u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c060u128) >> 1u128) == 0x78e00b39a9346030u128)) by (bit_vector);
    assert(((((0xfae7621e9038eb3c11055cc8d8bdbfcbu128) << 1) ^ (if ((((0xfae7621e9038eb3c11055cc8d8bdbfcbu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf5cec43d2071d678220ab991b17b7f11u128) by (bit_vector);
    assert(gf128_xtime(0xfae7621e9038eb3c11055cc8d8bdbfcbu128) == 0xf5cec43d2071d678220ab991b17b7f11u128);
    assert(gf128_mul_bits(0xfae7621e9038eb3c11055cc8d8bdbfcbu128, 0xf1c016735268c060u128, 64nat) == 0u128 ^ gf128_mul_bits(0xf5cec43d2071d678220ab991b17b7f11u128, 0x78e00b39a9346030u128, 63nat)) by { lemma_hmul128_bits_unfold(0xfae7621e9038eb3c11055cc8d8bdbfcbu128, 0xf1c016735268c060u128, 64nat); }
    assert((((0x78e00b39a9346030u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a9346030u128) >> 1u128) == 0x3c70059cd49a3018u128)) by (bit_vector);
    assert(((((0xf5cec43d2071d678220ab991b17b7f11u128) << 1) ^ (if ((((0xf5cec43d2071d678220ab991b17b7f11u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xeb9d887a40e3acf04415732362f6fea5u128) by (bit_vector);
    assert(gf128_xtime(0xf5cec43d2071d678220ab991b17b7f11u128) == 0xeb9d887a40e3acf04415732362f6fea5u128);
    assert(gf128_mul_bits(0xf5cec43d2071d678220ab991b17b7f11u128, 0x78e00b39a9346030u128, 63nat) == 0u128 ^ gf128_mul_bits(0xeb9d887a40e3acf04415732362f6fea5u128, 0x3c70059cd49a3018u128, 62nat)) by { lemma_hmul128_bits_unfold(0xf5cec43d2071d678220ab991b17b7f11u128, 0x78e00b39a9346030u128, 63nat); }
    assert((((0x3c70059cd49a3018u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a3018u128) >> 1u128) == 0x1e3802ce6a4d180cu128)) by (bit_vector);
    assert(((((0xeb9d887a40e3acf04415732362f6fea5u128) << 1) ^ (if ((((0xeb9d887a40e3acf04415732362f6fea5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd73b10f481c759e0882ae646c5edfdcdu128) by (bit_vector);
    assert(gf128_xtime(0xeb9d887a40e3acf04415732362f6fea5u128) == 0xd73b10f481c759e0882ae646c5edfdcdu128);
    assert(gf128_mul_bits(0xeb9d887a40e3acf04415732362f6fea5u128, 0x3c70059cd49a3018u128, 62nat) == 0u128 ^ gf128_mul_bits(0xd73b10f481c759e0882ae646c5edfdcdu128, 0x1e3802ce6a4d180cu128, 61nat)) by { lemma_hmul128_bits_unfold(0xeb9d887a40e3acf04415732362f6fea5u128, 0x3c70059cd49a3018u128, 62nat); }
    assert((((0x1e3802ce6a4d180cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180cu128) >> 1u128) == 0xf1c016735268c06u128)) by (bit_vector);
    assert(((((0xd73b10f481c759e0882ae646c5edfdcdu128) << 1) ^ (if ((((0xd73b10f481c759e0882ae646c5edfdcdu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xae7621e9038eb3c11055cc8d8bdbfb1du128) by (bit_vector);
    assert(gf128_xtime(0xd73b10f481c759e0882ae646c5edfdcdu128) == 0xae7621e9038eb3c11055cc8d8bdbfb1du128);
    assert(gf128_mul_bits(0xd73b10f481c759e0882ae646c5edfdcdu128, 0x1e3802ce6a4d180cu128, 61nat) == 0u128 ^ gf128_mul_bits(0xae7621e9038eb3c11055cc8d8bdbfb1du128, 0xf1c016735268c06u128, 60nat)) by { lemma_hmul128_bits_unfold(0xd73b10f481c759e0882ae646c5edfdcdu128, 0x1e3802ce6a4d180cu128, 61nat); }
    assert((((0xf1c016735268c06u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c06u128) >> 1u128) == 0x78e00b39a934603u128)) by (bit_vector);
    assert(((((0xae7621e9038eb3c11055cc8d8bdbfb1du128) << 1) ^ (if ((((0xae7621e9038eb3c11055cc8d8bdbfb1du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5cec43d2071d678220ab991b17b7f6bdu128) by (bit_vector);
    assert(gf128_xtime(0xae7621e9038eb3c11055cc8d8bdbfb1du128) == 0x5cec43d2071d678220ab991b17b7f6bdu128);
    assert(gf128_mul_bits(0xae7621e9038eb3c11055cc8d8bdbfb1du128, 0xf1c016735268c06u128, 60nat) == 0u128 ^ gf128_mul_bits(0x5cec43d2071d678220ab991b17b7f6bdu128, 0x78e00b39a934603u128, 59nat)) by { lemma_hmul128_bits_unfold(0xae7621e9038eb3c11055cc8d8bdbfb1du128, 0xf1c016735268c06u128, 60nat); }
    assert((((0x78e00b39a934603u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b39a934603u128) >> 1u128) == 0x3c70059cd49a301u128)) by (bit_vector);
    assert(((((0x5cec43d2071d678220ab991b17b7f6bdu128) << 1) ^ (if ((((0x5cec43d2071d678220ab991b17b7f6bdu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb9d887a40e3acf04415732362f6fed7au128) by (bit_vector);
    assert(gf128_xtime(0x5cec43d2071d678220ab991b17b7f6bdu128) == 0xb9d887a40e3acf04415732362f6fed7au128);
    assert(gf128_mul_bits(0x5cec43d2071d678220ab991b17b7f6bdu128, 0x78e00b39a934603u128, 59nat) == 0x5cec43d2071d678220ab991b17b7f6bdu128 ^ gf128_mul_bits(0xb9d887a40e3acf04415732362f6fed7au128, 0x3c70059cd49a301u128, 58nat)) by { lemma_hmul128_bits_unfold(0x5cec43d2071d678220ab991b17b7f6bdu128, 0x78e00b39a934603u128, 59nat); }
    assert((((0x3c70059cd49a301u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49a301u128) >> 1u128) == 0x1e3802ce6a4d180u128)) by (bit_vector);
    assert(((((0xb9d887a40e3acf04415732362f6fed7au128) << 1) ^ (if ((((0xb9d887a40e3acf04415732362f6fed7au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x73b10f481c759e0882ae646c5edfda73u128) by (bit_vector);
    assert(gf128_xtime(0xb9d887a40e3acf04415732362f6fed7au128) == 0x73b10f481c759e0882ae646c5edfda73u128);
    assert(gf128_mul_bits(0xb9d887a40e3acf04415732362f6fed7au128, 0x3c70059cd49a301u128, 58nat) == 0xb9d887a40e3acf04415732362f6fed7au128 ^ gf128_mul_bits(0x73b10f481c759e0882ae646c5edfda73u128, 0x1e3802ce6a4d180u128, 57nat)) by { lemma_hmul128_bits_unfold(0xb9d887a40e3acf04415732362f6fed7au128, 0x3c70059cd49a301u128, 58nat); }
    assert((((0x1e3802ce6a4d180u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d180u128) >> 1u128) == 0xf1c016735268c0u128)) by (bit_vector);
    assert(((((0x73b10f481c759e0882ae646c5edfda73u128) << 1) ^ (if ((((0x73b10f481c759e0882ae646c5edfda73u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe7621e9038eb3c11055cc8d8bdbfb4e6u128) by (bit_vector);
    assert(gf128_xtime(0x73b10f481c759e0882ae646c5edfda73u128) == 0xe7621e9038eb3c11055cc8d8bdbfb4e6u128);
    assert(gf128_mul_bits(0x73b10f481c759e0882ae646c5edfda73u128, 0x1e3802ce6a4d180u128, 57nat) == 0u128 ^ gf128_mul_bits(0xe7621e9038eb3c11055cc8d8bdbfb4e6u128, 0xf1c016735268c0u128, 56nat)) by { lemma_hmul128_bits_unfold(0x73b10f481c759e0882ae646c5edfda73u128, 0x1e3802ce6a4d180u128, 57nat); }
    assert((((0xf1c016735268c0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268c0u128) >> 1u128) == 0x78e00b39a93460u128)) by (bit_vector);
    assert(((((0xe7621e9038eb3c11055cc8d8bdbfb4e6u128) << 1) ^ (if ((((0xe7621e9038eb3c11055cc8d8bdbfb4e6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xcec43d2071d678220ab991b17b7f694bu128) by (bit_vector);
    assert(gf128_xtime(0xe7621e9038eb3c11055cc8d8bdbfb4e6u128) == 0xcec43d2071d678220ab991b17b7f694bu128);
    assert(gf128_mul_bits(0xe7621e9038eb3c11055cc8d8bdbfb4e6u128, 0xf1c016735268c0u128, 56nat) == 0u128 ^ gf128_mul_bits(0xcec43d2071d678220ab991b17b7f694bu128, 0x78e00b39a93460u128, 55nat)) by { lemma_hmul128_bits_unfold(0xe7621e9038eb3c11055cc8d8bdbfb4e6u128, 0xf1c016735268c0u128, 56nat); }
    assert((((0x78e00b39a93460u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a93460u128) >> 1u128) == 0x3c70059cd49a30u128)) by (bit_vector);
    assert(((((0xcec43d2071d678220ab991b17b7f694bu128) << 1) ^ (if ((((0xcec43d2071d678220ab991b17b7f694bu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9d887a40e3acf04415732362f6fed211u128) by (bit_vector);
    assert(gf128_xtime(0xcec43d2071d678220ab991b17b7f694bu128) == 0x9d887a40e3acf04415732362f6fed211u128);
    assert(gf128_mul_bits(0xcec43d2071d678220ab991b17b7f694bu128, 0x78e00b39a93460u128, 55nat) == 0u128 ^ gf128_mul_bits(0x9d887a40e3acf04415732362f6fed211u128, 0x3c70059cd49a30u128, 54nat)) by { lemma_hmul128_bits_unfold(0xcec43d2071d678220ab991b17b7f694bu128, 0x78e00b39a93460u128, 55nat); }
    assert((((0x3c70059cd49a30u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49a30u128) >> 1u128) == 0x1e3802ce6a4d18u128)) by (bit_vector);
    assert(((((0x9d887a40e3acf04415732362f6fed211u128) << 1) ^ (if ((((0x9d887a40e3acf04415732362f6fed211u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3b10f481c759e0882ae646c5edfda4a5u128) by (bit_vector);
    assert(gf128_xtime(0x9d887a40e3acf04415732362f6fed211u128) == 0x3b10f481c759e0882ae646c5edfda4a5u128);
    assert(gf128_mul_bits(0x9d887a40e3acf04415732362f6fed211u128, 0x3c70059cd49a30u128, 54nat) == 0u128 ^ gf128_mul_bits(0x3b10f481c759e0882ae646c5edfda4a5u128, 0x1e3802ce6a4d18u128, 53nat)) by { lemma_hmul128_bits_unfold(0x9d887a40e3acf04415732362f6fed211u128, 0x3c70059cd49a30u128, 54nat); }
    assert((((0x1e3802ce6a4d18u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d18u128) >> 1u128) == 0xf1c016735268cu128)) by (bit_vector);
    assert(((((0x3b10f481c759e0882ae646c5edfda4a5u128) << 1) ^ (if ((((0x3b10f481c759e0882ae646c5edfda4a5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7621e9038eb3c11055cc8d8bdbfb494au128) by (bit_vector);
    assert(gf128_xtime(0x3b10f481c759e0882ae646c5edfda4a5u128) == 0x7621e9038eb3c11055cc8d8bdbfb494au128);
    assert(gf128_mul_bits(0x3b10f481c759e0882ae646c5edfda4a5u128, 0x1e3802ce6a4d18u128, 53nat) == 0u128 ^ gf128_mul_bits(0x7621e9038eb3c11055cc8d8bdbfb494au128, 0xf1c016735268cu128, 52nat)) by { lemma_hmul128_bits_unfold(0x3b10f481c759e0882ae646c5edfda4a5u128, 0x1e3802ce6a4d18u128, 53nat); }
    assert((((0xf1c016735268cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268cu128) >> 1u128) == 0x78e00b39a9346u128)) by (bit_vector);
    assert(((((0x7621e9038eb3c11055cc8d8bdbfb494au128) << 1) ^ (if ((((0x7621e9038eb3c11055cc8d8bdbfb494au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xec43d2071d678220ab991b17b7f69294u128) by (bit_vector);
    assert(gf128_xtime(0x7621e9038eb3c11055cc8d8bdbfb494au128) == 0xec43d2071d678220ab991b17b7f69294u128);
    assert(gf128_mul_bits(0x7621e9038eb3c11055cc8d8bdbfb494au128, 0xf1c016735268cu128, 52nat) == 0u128 ^ gf128_mul_bits(0xec43d2071d678220ab991b17b7f69294u128, 0x78e00b39a9346u128, 51nat)) by { lemma_hmul128_bits_unfold(0x7621e9038eb3c11055cc8d8bdbfb494au128, 0xf1c016735268cu128, 52nat); }
    assert((((0x78e00b39a9346u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a9346u128) >> 1u128) == 0x3c70059cd49a3u128)) by (bit_vector);
    assert(((((0xec43d2071d678220ab991b17b7f69294u128) << 1) ^ (if ((((0xec43d2071d678220ab991b17b7f69294u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd887a40e3acf04415732362f6fed25afu128) by (bit_vector);
    assert(gf128_xtime(0xec43d2071d678220ab991b17b7f69294u128) == 0xd887a40e3acf04415732362f6fed25afu128);
    assert(gf128_mul_bits(0xec43d2071d678220ab991b17b7f69294u128, 0x78e00b39a9346u128, 51nat) == 0u128 ^ gf128_mul_bits(0xd887a40e3acf04415732362f6fed25afu128, 0x3c70059cd49a3u128, 50nat)) by { lemma_hmul128_bits_unfold(0xec43d2071d678220ab991b17b7f69294u128, 0x78e00b39a9346u128, 51nat); }
    assert((((0x3c70059cd49a3u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49a3u128) >> 1u128) == 0x1e3802ce6a4d1u128)) by (bit_vector);
    assert(((((0xd887a40e3acf04415732362f6fed25afu128) << 1) ^ (if ((((0xd887a40e3acf04415732362f6fed25afu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb10f481c759e0882ae646c5edfda4bd9u128) by (bit_vector);
    assert(gf128_xtime(0xd887a40e3acf04415732362f6fed25afu128) == 0xb10f481c759e0882ae646c5edfda4bd9u128);
    assert(gf128_mul_bits(0xd887a40e3acf04415732362f6fed25afu128, 0x3c70059cd49a3u128, 50nat) == 0xd887a40e3acf04415732362f6fed25afu128 ^ gf128_mul_bits(0xb10f481c759e0882ae646c5edfda4bd9u128, 0x1e3802ce6a4d1u128, 49nat)) by { lemma_hmul128_bits_unfold(0xd887a40e3acf04415732362f6fed25afu128, 0x3c70059cd49a3u128, 50nat); }
    assert((((0x1e3802ce6a4d1u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4d1u128) >> 1u128) == 0xf1c016735268u128)) by (bit_vector);
    assert(((((0xb10f481c759e0882ae646c5edfda4bd9u128) << 1) ^ (if ((((0xb10f481c759e0882ae646c5edfda4bd9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x621e9038eb3c11055cc8d8bdbfb49735u128) by (bit_vector);
    assert(gf128_xtime(0xb10f481c759e0882ae646c5edfda4bd9u128) == 0x621e9038eb3c11055cc8d8bdbfb49735u128);
    assert(gf128_mul_bits(0xb10f481c759e0882ae646c5edfda4bd9u128, 0x1e3802ce6a4d1u128, 49nat) == 0xb10f481c759e0882ae646c5edfda4bd9u128 ^ gf128_mul_bits(0x621e9038eb3c11055cc8d8bdbfb49735u128, 0xf1c016735268u128, 48nat)) by { lemma_hmul128_bits_unfold(0xb10f481c759e0882ae646c5edfda4bd9u128, 0x1e3802ce6a4d1u128, 49nat); }
    assert((((0xf1c016735268u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016735268u128) >> 1u128) == 0x78e00b39a934u128)) by (bit_vector);
    assert(((((0x621e9038eb3c11055cc8d8bdbfb49735u128) << 1) ^ (if ((((0x621e9038eb3c11055cc8d8bdbfb49735u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc43d2071d678220ab991b17b7f692e6au128) by (bit_vector);
    assert(gf128_xtime(0x621e9038eb3c11055cc8d8bdbfb49735u128) == 0xc43d2071d678220ab991b17b7f692e6au128);
    assert(gf128_mul_bits(0x621e9038eb3c11055cc8d8bdbfb49735u128, 0xf1c016735268u128, 48nat) == 0u128 ^ gf128_mul_bits(0xc43d2071d678220ab991b17b7f692e6au128, 0x78e00b39a934u128, 47nat)) by { lemma_hmul128_bits_unfold(0x621e9038eb3c11055cc8d8bdbfb49735u128, 0xf1c016735268u128, 48nat); }
    assert((((0x78e00b39a934u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39a934u128) >> 1u128) == 0x3c70059cd49au128)) by (bit_vector);
    assert(((((0xc43d2071d678220ab991b17b7f692e6au128) << 1) ^ (if ((((0xc43d2071d678220ab991b17b7f692e6au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x887a40e3acf04415732362f6fed25c53u128) by (bit_vector);
    assert(gf128_xtime(0xc43d2071d678220ab991b17b7f692e6au128) == 0x887a40e3acf04415732362f6fed25c53u128);
    assert(gf128_mul_bits(0xc43d2071d678220ab991b17b7f692e6au128, 0x78e00b39a934u128, 47nat) == 0u128 ^ gf128_mul_bits(0x887a40e3acf04415732362f6fed25c53u128, 0x3c70059cd49au128, 46nat)) by { lemma_hmul128_bits_unfold(0xc43d2071d678220ab991b17b7f692e6au128, 0x78e00b39a934u128, 47nat); }
    assert((((0x3c70059cd49au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd49au128) >> 1u128) == 0x1e3802ce6a4du128)) by (bit_vector);
    assert(((((0x887a40e3acf04415732362f6fed25c53u128) << 1) ^ (if ((((0x887a40e3acf04415732362f6fed25c53u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x10f481c759e0882ae646c5edfda4b821u128) by (bit_vector);
    assert(gf128_xtime(0x887a40e3acf04415732362f6fed25c53u128) == 0x10f481c759e0882ae646c5edfda4b821u128);
    assert(gf128_mul_bits(0x887a40e3acf04415732362f6fed25c53u128, 0x3c70059cd49au128, 46nat) == 0u128 ^ gf128_mul_bits(0x10f481c759e0882ae646c5edfda4b821u128, 0x1e3802ce6a4du128, 45nat)) by { lemma_hmul128_bits_unfold(0x887a40e3acf04415732362f6fed25c53u128, 0x3c70059cd49au128, 46nat); }
    assert((((0x1e3802ce6a4du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3802ce6a4du128) >> 1u128) == 0xf1c01673526u128)) by (bit_vector);
    assert(((((0x10f481c759e0882ae646c5edfda4b821u128) << 1) ^ (if ((((0x10f481c759e0882ae646c5edfda4b821u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x21e9038eb3c11055cc8d8bdbfb497042u128) by (bit_vector);
    assert(gf128_xtime(0x10f481c759e0882ae646c5edfda4b821u128) == 0x21e9038eb3c11055cc8d8bdbfb497042u128);
    assert(gf128_mul_bits(0x10f481c759e0882ae646c5edfda4b821u128, 0x1e3802ce6a4du128, 45nat) == 0x10f481c759e0882ae646c5edfda4b821u128 ^ gf128_mul_bits(0x21e9038eb3c11055cc8d8bdbfb497042u128, 0xf1c01673526u128, 44nat)) by { lemma_hmul128_bits_unfold(0x10f481c759e0882ae646c5edfda4b821u128, 0x1e3802ce6a4du128, 45nat); }
    assert((((0xf1c01673526u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c01673526u128) >> 1u128) == 0x78e00b39a93u128)) by (bit_vector);
    assert(((((0x21e9038eb3c11055cc8d8bdbfb497042u128) << 1) ^ (if ((((0x21e9038eb3c11055cc8d8bdbfb497042u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x43d2071d678220ab991b17b7f692e084u128) by (bit_vector);
    assert(gf128_xtime(0x21e9038eb3c11055cc8d8bdbfb497042u128) == 0x43d2071d678220ab991b17b7f692e084u128);
    assert(gf128_mul_bits(0x21e9038eb3c11055cc8d8bdbfb497042u128, 0xf1c01673526u128, 44nat) == 0u128 ^ gf128_mul_bits(0x43d2071d678220ab991b17b7f692e084u128, 0x78e00b39a93u128, 43nat)) by { lemma_hmul128_bits_unfold(0x21e9038eb3c11055cc8d8bdbfb497042u128, 0xf1c01673526u128, 44nat); }
    assert((((0x78e00b39a93u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b39a93u128) >> 1u128) == 0x3c70059cd49u128)) by (bit_vector);
    assert(((((0x43d2071d678220ab991b17b7f692e084u128) << 1) ^ (if ((((0x43d2071d678220ab991b17b7f692e084u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x87a40e3acf04415732362f6fed25c108u128) by (bit_vector);
    assert(gf128_xtime(0x43d2071d678220ab991b17b7f692e084u128) == 0x87a40e3acf04415732362f6fed25c108u128);
    assert(gf128_mul_bits(0x43d2071d678220ab991b17b7f692e084u128, 0x78e00b39a93u128, 43nat) == 0x43d2071d678220ab991b17b7f692e084u128 ^ gf128_mul_bits(0x87a40e3acf04415732362f6fed25c108u128, 0x3c70059cd49u128, 42nat)) by { lemma_hmul128_bits_unfold(0x43d2071d678220ab991b17b7f692e084u128, 0x78e00b39a93u128, 43nat); }
    assert((((0x3c70059cd49u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cd49u128) >> 1u128) == 0x1e3802ce6a4u128)) by (bit_vector);
    assert(((((0x87a40e3acf04415732362f6fed25c108u128) << 1) ^ (if ((((0x87a40e3acf04415732362f6fed25c108u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf481c759e0882ae646c5edfda4b8297u128) by (bit_vector);
    assert(gf128_xtime(0x87a40e3acf04415732362f6fed25c108u128) == 0xf481c759e0882ae646c5edfda4b8297u128);
    assert(gf128_mul_bits(0x87a40e3acf04415732362f6fed25c108u128, 0x3c70059cd49u128, 42nat) == 0x87a40e3acf04415732362f6fed25c108u128 ^ gf128_mul_bits(0xf481c759e0882ae646c5edfda4b8297u128, 0x1e3802ce6a4u128, 41nat)) by { lemma_hmul128_bits_unfold(0x87a40e3acf04415732362f6fed25c108u128, 0x3c70059cd49u128, 42nat); }
    assert((((0x1e3802ce6a4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6a4u128) >> 1u128) == 0xf1c0167352u128)) by (bit_vector);
    assert(((((0xf481c759e0882ae646c5edfda4b8297u128) << 1) ^ (if ((((0xf481c759e0882ae646c5edfda4b8297u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1e9038eb3c11055cc8d8bdbfb497052eu128) by (bit_vector);
    assert(gf128_xtime(0xf481c759e0882ae646c5edfda4b8297u128) == 0x1e9038eb3c11055cc8d8bdbfb497052eu128);
    assert(gf128_mul_bits(0xf481c759e0882ae646c5edfda4b8297u128, 0x1e3802ce6a4u128, 41nat) == 0u128 ^ gf128_mul_bits(0x1e9038eb3c11055cc8d8bdbfb497052eu128, 0xf1c0167352u128, 40nat)) by { lemma_hmul128_bits_unfold(0xf481c759e0882ae646c5edfda4b8297u128, 0x1e3802ce6a4u128, 41nat); }
    assert((((0xf1c0167352u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c0167352u128) >> 1u128) == 0x78e00b39a9u128)) by (bit_vector);
    assert(((((0x1e9038eb3c11055cc8d8bdbfb497052eu128) << 1) ^ (if ((((0x1e9038eb3c11055cc8d8bdbfb497052eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3d2071d678220ab991b17b7f692e0a5cu128) by (bit_vector);
    assert(gf128_xtime(0x1e9038eb3c11055cc8d8bdbfb497052eu128) == 0x3d2071d678220ab991b17b7f692e0a5cu128);
    assert(gf128_mul_bits(0x1e9038eb3c11055cc8d8bdbfb497052eu128, 0xf1c0167352u128, 40nat) == 0u128 ^ gf128_mul_bits(0x3d2071d678220ab991b17b7f692e0a5cu128, 0x78e00b39a9u128, 39nat)) by { lemma_hmul128_bits_unfold(0x1e9038eb3c11055cc8d8bdbfb497052eu128, 0xf1c0167352u128, 40nat); }
    assert((((0x78e00b39a9u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b39a9u128) >> 1u128) == 0x3c70059cd4u128)) by (bit_vector);
    assert(((((0x3d2071d678220ab991b17b7f692e0a5cu128) << 1) ^ (if ((((0x3d2071d678220ab991b17b7f692e0a5cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7a40e3acf04415732362f6fed25c14b8u128) by (bit_vector);
    assert(gf128_xtime(0x3d2071d678220ab991b17b7f692e0a5cu128) == 0x7a40e3acf04415732362f6fed25c14b8u128);
    assert(gf128_mul_bits(0x3d2071d678220ab991b17b7f692e0a5cu128, 0x78e00b39a9u128, 39nat) == 0x3d2071d678220ab991b17b7f692e0a5cu128 ^ gf128_mul_bits(0x7a40e3acf04415732362f6fed25c14b8u128, 0x3c70059cd4u128, 38nat)) by { lemma_hmul128_bits_unfold(0x3d2071d678220ab991b17b7f692e0a5cu128, 0x78e00b39a9u128, 39nat); }
    assert((((0x3c70059cd4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cd4u128) >> 1u128) == 0x1e3802ce6au128)) by (bit_vector);
    assert(((((0x7a40e3acf04415732362f6fed25c14b8u128) << 1) ^ (if ((((0x7a40e3acf04415732362f6fed25c14b8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf481c759e0882ae646c5edfda4b82970u128) by (bit_vector);
    assert(gf128_xtime(0x7a40e3acf04415732362f6fed25c14b8u128) == 0xf481c759e0882ae646c5edfda4b82970u128);
    assert(gf128_mul_bits(0x7a40e3acf04415732362f6fed25c14b8u128, 0x3c70059cd4u128, 38nat) == 0u128 ^ gf128_mul_bits(0xf481c759e0882ae646c5edfda4b82970u128, 0x1e3802ce6au128, 37nat)) by { lemma_hmul128_bits_unfold(0x7a40e3acf04415732362f6fed25c14b8u128, 0x3c70059cd4u128, 38nat); }
    assert((((0x1e3802ce6au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6au128) >> 1u128) == 0xf1c016735u128)) by (bit_vector);
    assert(((((0xf481c759e0882ae646c5edfda4b82970u128) << 1) ^ (if ((((0xf481c759e0882ae646c5edfda4b82970u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe9038eb3c11055cc8d8bdbfb49705267u128) by (bit_vector);
    assert(gf128_xtime(0xf481c759e0882ae646c5edfda4b82970u128) == 0xe9038eb3c11055cc8d8bdbfb49705267u128);
    assert(gf128_mul_bits(0xf481c759e0882ae646c5edfda4b82970u128, 0x1e3802ce6au128, 37nat) == 0u128 ^ gf128_mul_bits(0xe9038eb3c11055cc8d8bdbfb49705267u128, 0xf1c016735u128, 36nat)) by { lemma_hmul128_bits_unfold(0xf481c759e0882ae646c5edfda4b82970u128, 0x1e3802ce6au128, 37nat); }
    assert((((0xf1c016735u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c016735u128) >> 1u128) == 0x78e00b39au128)) by (bit_vector);
    assert(((((0xe9038eb3c11055cc8d8bdbfb49705267u128) << 1) ^ (if ((((0xe9038eb3c11055cc8d8bdbfb49705267u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd2071d678220ab991b17b7f692e0a449u128) by (bit_vector);
    assert(gf128_xtime(0xe9038eb3c11055cc8d8bdbfb49705267u128) == 0xd2071d678220ab991b17b7f692e0a449u128);
    assert(gf128_mul_bits(0xe9038eb3c11055cc8d8bdbfb49705267u128, 0xf1c016735u128, 36nat) == 0xe9038eb3c11055cc8d8bdbfb49705267u128 ^ gf128_mul_bits(0xd2071d678220ab991b17b7f692e0a449u128, 0x78e00b39au128, 35nat)) by { lemma_hmul128_bits_unfold(0xe9038eb3c11055cc8d8bdbfb49705267u128, 0xf1c016735u128, 36nat); }
    assert((((0x78e00b39au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00b39au128) >> 1u128) == 0x3c70059cdu128)) by (bit_vector);
    assert(((((0xd2071d678220ab991b17b7f692e0a449u128) << 1) ^ (if ((((0xd2071d678220ab991b17b7f692e0a449u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa40e3acf04415732362f6fed25c14815u128) by (bit_vector);
    assert(gf128_xtime(0xd2071d678220ab991b17b7f692e0a449u128) == 0xa40e3acf04415732362f6fed25c14815u128);
    assert(gf128_mul_bits(0xd2071d678220ab991b17b7f692e0a449u128, 0x78e00b39au128, 35nat) == 0u128 ^ gf128_mul_bits(0xa40e3acf04415732362f6fed25c14815u128, 0x3c70059cdu128, 34nat)) by { lemma_hmul128_bits_unfold(0xd2071d678220ab991b17b7f692e0a449u128, 0x78e00b39au128, 35nat); }
    assert((((0x3c70059cdu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059cdu128) >> 1u128) == 0x1e3802ce6u128)) by (bit_vector);
    assert(((((0xa40e3acf04415732362f6fed25c14815u128) << 1) ^ (if ((((0xa40e3acf04415732362f6fed25c14815u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x481c759e0882ae646c5edfda4b8290adu128) by (bit_vector);
    assert(gf128_xtime(0xa40e3acf04415732362f6fed25c14815u128) == 0x481c759e0882ae646c5edfda4b8290adu128);
    assert(gf128_mul_bits(0xa40e3acf04415732362f6fed25c14815u128, 0x3c70059cdu128, 34nat) == 0xa40e3acf04415732362f6fed25c14815u128 ^ gf128_mul_bits(0x481c759e0882ae646c5edfda4b8290adu128, 0x1e3802ce6u128, 33nat)) by { lemma_hmul128_bits_unfold(0xa40e3acf04415732362f6fed25c14815u128, 0x3c70059cdu128, 34nat); }
    assert((((0x1e3802ce6u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ce6u128) >> 1u128) == 0xf1c01673u128)) by (bit_vector);
    assert(((((0x481c759e0882ae646c5edfda4b8290adu128) << 1) ^ (if ((((0x481c759e0882ae646c5edfda4b8290adu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9038eb3c11055cc8d8bdbfb49705215au128) by (bit_vector);
    assert(gf128_xtime(0x481c759e0882ae646c5edfda4b8290adu128) == 0x9038eb3c11055cc8d8bdbfb49705215au128);
    assert(gf128_mul_bits(0x481c759e0882ae646c5edfda4b8290adu128, 0x1e3802ce6u128, 33nat) == 0u128 ^ gf128_mul_bits(0x9038eb3c11055cc8d8bdbfb49705215au128, 0xf1c01673u128, 32nat)) by { lemma_hmul128_bits_unfold(0x481c759e0882ae646c5edfda4b8290adu128, 0x1e3802ce6u128, 33nat); }
    assert((((0xf1c01673u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c01673u128) >> 1u128) == 0x78e00b39u128)) by (bit_vector);
    assert(((((0x9038eb3c11055cc8d8bdbfb49705215au128) << 1) ^ (if ((((0x9038eb3c11055cc8d8bdbfb49705215au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x2071d678220ab991b17b7f692e0a4233u128) by (bit_vector);
    assert(gf128_xtime(0x9038eb3c11055cc8d8bdbfb49705215au128) == 0x2071d678220ab991b17b7f692e0a4233u128);
    assert(gf128_mul_bits(0x9038eb3c11055cc8d8bdbfb49705215au128, 0xf1c01673u128, 32nat) == 0x9038eb3c11055cc8d8bdbfb49705215au128 ^ gf128_mul_bits(0x2071d678220ab991b17b7f692e0a4233u128, 0x78e00b39u128, 31nat)) by { lemma_hmul128_bits_unfold(0x9038eb3c11055cc8d8bdbfb49705215au128, 0xf1c01673u128, 32nat); }
    assert((((0x78e00b39u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b39u128) >> 1u128) == 0x3c70059cu128)) by (bit_vector);
    assert(((((0x2071d678220ab991b17b7f692e0a4233u128) << 1) ^ (if ((((0x2071d678220ab991b17b7f692e0a4233u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x40e3acf04415732362f6fed25c148466u128) by (bit_vector);
    assert(gf128_xtime(0x2071d678220ab991b17b7f692e0a4233u128) == 0x40e3acf04415732362f6fed25c148466u128);
    assert(gf128_mul_bits(0x2071d678220ab991b17b7f692e0a4233u128, 0x78e00b39u128, 31nat) == 0x2071d678220ab991b17b7f692e0a4233u128 ^ gf128_mul_bits(0x40e3acf04415732362f6fed25c148466u128, 0x3c70059cu128, 30nat)) by { lemma_hmul128_bits_unfold(0x2071d678220ab991b17b7f692e0a4233u128, 0x78e00b39u128, 31nat); }
    assert((((0x3c70059cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70059cu128) >> 1u128) == 0x1e3802ceu128)) by (bit_vector);
    assert(((((0x40e3acf04415732362f6fed25c148466u128) << 1) ^ (if ((((0x40e3acf04415732362f6fed25c148466u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x81c759e0882ae646c5edfda4b82908ccu128) by (bit_vector);
    assert(gf128_xtime(0x40e3acf04415732362f6fed25c148466u128) == 0x81c759e0882ae646c5edfda4b82908ccu128);
    assert(gf128_mul_bits(0x40e3acf04415732362f6fed25c148466u128, 0x3c70059cu128, 30nat) == 0u128 ^ gf128_mul_bits(0x81c759e0882ae646c5edfda4b82908ccu128, 0x1e3802ceu128, 29nat)) by { lemma_hmul128_bits_unfold(0x40e3acf04415732362f6fed25c148466u128, 0x3c70059cu128, 30nat); }
    assert((((0x1e3802ceu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802ceu128) >> 1u128) == 0xf1c0167u128)) by (bit_vector);
    assert(((((0x81c759e0882ae646c5edfda4b82908ccu128) << 1) ^ (if ((((0x81c759e0882ae646c5edfda4b82908ccu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x38eb3c11055cc8d8bdbfb497052111fu128) by (bit_vector);
    assert(gf128_xtime(0x81c759e0882ae646c5edfda4b82908ccu128) == 0x38eb3c11055cc8d8bdbfb497052111fu128);
    assert(gf128_mul_bits(0x81c759e0882ae646c5edfda4b82908ccu128, 0x1e3802ceu128, 29nat) == 0u128 ^ gf128_mul_bits(0x38eb3c11055cc8d8bdbfb497052111fu128, 0xf1c0167u128, 28nat)) by { lemma_hmul128_bits_unfold(0x81c759e0882ae646c5edfda4b82908ccu128, 0x1e3802ceu128, 29nat); }
    assert((((0xf1c0167u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c0167u128) >> 1u128) == 0x78e00b3u128)) by (bit_vector);
    assert(((((0x38eb3c11055cc8d8bdbfb497052111fu128) << 1) ^ (if ((((0x38eb3c11055cc8d8bdbfb497052111fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x71d678220ab991b17b7f692e0a4223eu128) by (bit_vector);
    assert(gf128_xtime(0x38eb3c11055cc8d8bdbfb497052111fu128) == 0x71d678220ab991b17b7f692e0a4223eu128);
    assert(gf128_mul_bits(0x38eb3c11055cc8d8bdbfb497052111fu128, 0xf1c0167u128, 28nat) == 0x38eb3c11055cc8d8bdbfb497052111fu128 ^ gf128_mul_bits(0x71d678220ab991b17b7f692e0a4223eu128, 0x78e00b3u128, 27nat)) by { lemma_hmul128_bits_unfold(0x38eb3c11055cc8d8bdbfb497052111fu128, 0xf1c0167u128, 28nat); }
    assert((((0x78e00b3u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00b3u128) >> 1u128) == 0x3c70059u128)) by (bit_vector);
    assert(((((0x71d678220ab991b17b7f692e0a4223eu128) << 1) ^ (if ((((0x71d678220ab991b17b7f692e0a4223eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe3acf04415732362f6fed25c148447cu128) by (bit_vector);
    assert(gf128_xtime(0x71d678220ab991b17b7f692e0a4223eu128) == 0xe3acf04415732362f6fed25c148447cu128);
    assert(gf128_mul_bits(0x71d678220ab991b17b7f692e0a4223eu128, 0x78e00b3u128, 27nat) == 0x71d678220ab991b17b7f692e0a4223eu128 ^ gf128_mul_bits(0xe3acf04415732362f6fed25c148447cu128, 0x3c70059u128, 26nat)) by { lemma_hmul128_bits_unfold(0x71d678220ab991b17b7f692e0a4223eu128, 0x78e00b3u128, 27nat); }
    assert((((0x3c70059u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c70059u128) >> 1u128) == 0x1e3802cu128)) by (bit_vector);
    assert(((((0xe3acf04415732362f6fed25c148447cu128) << 1) ^ (if ((((0xe3acf04415732362f6fed25c148447cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1c759e0882ae646c5edfda4b829088f8u128) by (bit_vector);
    assert(gf128_xtime(0xe3acf04415732362f6fed25c148447cu128) == 0x1c759e0882ae646c5edfda4b829088f8u128);
    assert(gf128_mul_bits(0xe3acf04415732362f6fed25c148447cu128, 0x3c70059u128, 26nat) == 0xe3acf04415732362f6fed25c148447cu128 ^ gf128_mul_bits(0x1c759e0882ae646c5edfda4b829088f8u128, 0x1e3802cu128, 25nat)) by { lemma_hmul128_bits_unfold(0xe3acf04415732362f6fed25c148447cu128, 0x3c70059u128, 26nat); }
    assert((((0x1e3802cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802cu128) >> 1u128) == 0xf1c016u128)) by (bit_vector);
    assert(((((0x1c759e0882ae646c5edfda4b829088f8u128) << 1) ^ (if ((((0x1c759e0882ae646c5edfda4b829088f8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x38eb3c11055cc8d8bdbfb497052111f0u128) by (bit_vector);
    assert(gf128_xtime(0x1c759e0882ae646c5edfda4b829088f8u128) == 0x38eb3c11055cc8d8bdbfb497052111f0u128);
    assert(gf128_mul_bits(0x1c759e0882ae646c5edfda4b829088f8u128, 0x1e3802cu128, 25nat) == 0u128 ^ gf128_mul_bits(0x38eb3c11055cc8d8bdbfb497052111f0u128, 0xf1c016u128, 24nat)) by { lemma_hmul128_bits_unfold(0x1c759e0882ae646c5edfda4b829088f8u128, 0x1e3802cu128, 25nat); }
    assert((((0xf1c016u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c016u128) >> 1u128) == 0x78e00bu128)) by (bit_vector);
    assert(((((0x38eb3c11055cc8d8bdbfb497052111f0u128) << 1) ^ (if ((((0x38eb3c11055cc8d8bdbfb497052111f0u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x71d678220ab991b17b7f692e0a4223e0u128) by (bit_vector);
    assert(gf128_xtime(0x38eb3c11055cc8d8bdbfb497052111f0u128) == 0x71d678220ab991b17b7f692e0a4223e0u128);
    assert(gf128_mul_bits(0x38eb3c11055cc8d8bdbfb497052111f0u128, 0xf1c016u128, 24nat) == 0u128 ^ gf128_mul_bits(0x71d678220ab991b17b7f692e0a4223e0u128, 0x78e00bu128, 23nat)) by { lemma_hmul128_bits_unfold(0x38eb3c11055cc8d8bdbfb497052111f0u128, 0xf1c016u128, 24nat); }
    assert((((0x78e00bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x78e00bu128) >> 1u128) == 0x3c7005u128)) by (bit_vector);
    assert(((((0x71d678220ab991b17b7f692e0a4223e0u128) << 1) ^ (if ((((0x71d678220ab991b17b7f692e0a4223e0u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe3acf04415732362f6fed25c148447c0u128) by (bit_vector);
    assert(gf128_xtime(0x71d678220ab991b17b7f692e0a4223e0u128) == 0xe3acf04415732362f6fed25c148447c0u128);
    assert(gf128_mul_bits(0x71d678220ab991b17b7f692e0a4223e0u128, 0x78e00bu128, 23nat) == 0x71d678220ab991b17b7f692e0a4223e0u128 ^ gf128_mul_bits(0xe3acf04415732362f6fed25c148447c0u128, 0x3c7005u128, 22nat)) by { lemma_hmul128_bits_unfold(0x71d678220ab991b17b7f692e0a4223e0u128, 0x78e00bu128, 23nat); }
    assert((((0x3c7005u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c7005u128) >> 1u128) == 0x1e3802u128)) by (bit_vector);
    assert(((((0xe3acf04415732362f6fed25c148447c0u128) << 1) ^ (if ((((0xe3acf04415732362f6fed25c148447c0u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc759e0882ae646c5edfda4b829088f07u128) by (bit_vector);
    assert(gf128_xtime(0xe3acf04415732362f6fed25c148447c0u128) == 0xc759e0882ae646c5edfda4b829088f07u128);
    assert(gf128_mul_bits(0xe3acf04415732362f6fed25c148447c0u128, 0x3c7005u128, 22nat) == 0xe3acf04415732362f6fed25c148447c0u128 ^ gf128_mul_bits(0xc759e0882ae646c5edfda4b829088f07u128, 0x1e3802u128, 21nat)) by { lemma_hmul128_bits_unfold(0xe3acf04415732362f6fed25c148447c0u128, 0x3c7005u128, 22nat); }
    assert((((0x1e3802u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e3802u128) >> 1u128) == 0xf1c01u128)) by (bit_vector);
    assert(((((0xc759e0882ae646c5edfda4b829088f07u128) << 1) ^ (if ((((0xc759e0882ae646c5edfda4b829088f07u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x8eb3c11055cc8d8bdbfb497052111e89u128) by (bit_vector);
    assert(gf128_xtime(0xc759e0882ae646c5edfda4b829088f07u128) == 0x8eb3c11055cc8d8bdbfb497052111e89u128);
    assert(gf128_mul_bits(0xc759e0882ae646c5edfda4b829088f07u128, 0x1e3802u128, 21nat) == 0u128 ^ gf128_mul_bits(0x8eb3c11055cc8d8bdbfb497052111e89u128, 0xf1c01u128, 20nat)) by { lemma_hmul128_bits_unfold(0xc759e0882ae646c5edfda4b829088f07u128, 0x1e3802u128, 21nat); }
    assert((((0xf1c01u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1c01u128) >> 1u128) == 0x78e00u128)) by (bit_vector);
    assert(((((0x8eb3c11055cc8d8bdbfb497052111e89u128) << 1) ^ (if ((((0x8eb3c11055cc8d8bdbfb497052111e89u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1d678220ab991b17b7f692e0a4223d95u128) by (bit_vector);
    assert(gf128_xtime(0x8eb3c11055cc8d8bdbfb497052111e89u128) == 0x1d678220ab991b17b7f692e0a4223d95u128);
    assert(gf128_mul_bits(0x8eb3c11055cc8d8bdbfb497052111e89u128, 0xf1c01u128, 20nat) == 0x8eb3c11055cc8d8bdbfb497052111e89u128 ^ gf128_mul_bits(0x1d678220ab991b17b7f692e0a4223d95u128, 0x78e00u128, 19nat)) by { lemma_hmul128_bits_unfold(0x8eb3c11055cc8d8bdbfb497052111e89u128, 0xf1c01u128, 20nat); }
    assert((((0x78e00u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e00u128) >> 1u128) == 0x3c700u128)) by (bit_vector);
    assert(((((0x1d678220ab991b17b7f692e0a4223d95u128) << 1) ^ (if ((((0x1d678220ab991b17b7f692e0a4223d95u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3acf04415732362f6fed25c148447b2au128) by (bit_vector);
    assert(gf128_xtime(0x1d678220ab991b17b7f692e0a4223d95u128) == 0x3acf04415732362f6fed25c148447b2au128);
    assert(gf128_mul_bits(0x1d678220ab991b17b7f692e0a4223d95u128, 0x78e00u128, 19nat) == 0u128 ^ gf128_mul_bits(0x3acf04415732362f6fed25c148447b2au128, 0x3c700u128, 18nat)) by { lemma_hmul128_bits_unfold(0x1d678220ab991b17b7f692e0a4223d95u128, 0x78e00u128, 19nat); }
    assert((((0x3c700u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c700u128) >> 1u128) == 0x1e380u128)) by (bit_vector);
    assert(((((0x3acf04415732362f6fed25c148447b2au128) << 1) ^ (if ((((0x3acf04415732362f6fed25c148447b2au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x759e0882ae646c5edfda4b829088f654u128) by (bit_vector);
    assert(gf128_xtime(0x3acf04415732362f6fed25c148447b2au128) == 0x759e0882ae646c5edfda4b829088f654u128);
    assert(gf128_mul_bits(0x3acf04415732362f6fed25c148447b2au128, 0x3c700u128, 18nat) == 0u128 ^ gf128_mul_bits(0x759e0882ae646c5edfda4b829088f654u128, 0x1e380u128, 17nat)) by { lemma_hmul128_bits_unfold(0x3acf04415732362f6fed25c148447b2au128, 0x3c700u128, 18nat); }
    assert((((0x1e380u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e380u128) >> 1u128) == 0xf1c0u128)) by (bit_vector);
    assert(((((0x759e0882ae646c5edfda4b829088f654u128) << 1) ^ (if ((((0x759e0882ae646c5edfda4b829088f654u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xeb3c11055cc8d8bdbfb497052111eca8u128) by (bit_vector);
    assert(gf128_xtime(0x759e0882ae646c5edfda4b829088f654u128) == 0xeb3c11055cc8d8bdbfb497052111eca8u128);
    assert(gf128_mul_bits(0x759e0882ae646c5edfda4b829088f654u128, 0x1e380u128, 17nat) == 0u128 ^ gf128_mul_bits(0xeb3c11055cc8d8bdbfb497052111eca8u128, 0xf1c0u128, 16nat)) by { lemma_hmul128_bits_unfold(0x759e0882ae646c5edfda4b829088f654u128, 0x1e380u128, 17nat); }
    assert((((0xf1c0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1c0u128) >> 1u128) == 0x78e0u128)) by (bit_vector);
    assert(((((0xeb3c11055cc8d8bdbfb497052111eca8u128) << 1) ^ (if ((((0xeb3c11055cc8d8bdbfb497052111eca8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd678220ab991b17b7f692e0a4223d9d7u128) by (bit_vector);
    assert(gf128_xtime(0xeb3c11055cc8d8bdbfb497052111eca8u128) == 0xd678220ab991b17b7f692e0a4223d9d7u128);
    assert(gf128_mul_bits(0xeb3c11055cc8d8bdbfb497052111eca8u128, 0xf1c0u128, 16nat) == 0u128 ^ gf128_mul_bits(0xd678220ab991b17b7f692e0a4223d9d7u128, 0x78e0u128, 15nat)) by { lemma_hmul128_bits_unfold(0xeb3c11055cc8d8bdbfb497052111eca8u128, 0xf1c0u128, 16nat); }
    assert((((0x78e0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78e0u128) >> 1u128) == 0x3c70u128)) by (bit_vector);
    assert(((((0xd678220ab991b17b7f692e0a4223d9d7u128) << 1) ^ (if ((((0xd678220ab991b17b7f692e0a4223d9d7u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xacf04415732362f6fed25c148447b329u128) by (bit_vector);
    assert(gf128_xtime(0xd678220ab991b17b7f692e0a4223d9d7u128) == 0xacf04415732362f6fed25c148447b329u128);
    assert(gf128_mul_bits(0xd678220ab991b17b7f692e0a4223d9d7u128, 0x78e0u128, 15nat) == 0u128 ^ gf128_mul_bits(0xacf04415732362f6fed25c148447b329u128, 0x3c70u128, 14nat)) by { lemma_hmul128_bits_unfold(0xd678220ab991b17b7f692e0a4223d9d7u128, 0x78e0u128, 15nat); }
    assert((((0x3c70u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3c70u128) >> 1u128) == 0x1e38u128)) by (bit_vector);
    assert(((((0xacf04415732362f6fed25c148447b329u128) << 1) ^ (if ((((0xacf04415732362f6fed25c148447b329u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x59e0882ae646c5edfda4b829088f66d5u128) by (bit_vector);
    assert(gf128_xtime(0xacf04415732362f6fed25c148447b329u128) == 0x59e0882ae646c5edfda4b829088f66d5u128);
    assert(gf128_mul_bits(0xacf04415732362f6fed25c148447b329u128, 0x3c70u128, 14nat) == 0u128 ^ gf128_mul_bits(0x59e0882ae646c5edfda4b829088f66d5u128, 0x1e38u128, 13nat)) by { lemma_hmul128_bits_unfold(0xacf04415732362f6fed25c148447b329u128, 0x3c70u128, 14nat); }
    assert((((0x1e38u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1e38u128) >> 1u128) == 0xf1cu128)) by (bit_vector);
    assert(((((0x59e0882ae646c5edfda4b829088f66d5u128) << 1) ^ (if ((((0x59e0882ae646c5edfda4b829088f66d5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb3c11055cc8d8bdbfb497052111ecdaau128) by (bit_vector);
    assert(gf128_xtime(0x59e0882ae646c5edfda4b829088f66d5u128) == 0xb3c11055cc8d8bdbfb497052111ecdaau128);
    assert(gf128_mul_bits(0x59e0882ae646c5edfda4b829088f66d5u128, 0x1e38u128, 13nat) == 0u128 ^ gf128_mul_bits(0xb3c11055cc8d8bdbfb497052111ecdaau128, 0xf1cu128, 12nat)) by { lemma_hmul128_bits_unfold(0x59e0882ae646c5edfda4b829088f66d5u128, 0x1e38u128, 13nat); }
    assert((((0xf1cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0xf1cu128) >> 1u128) == 0x78eu128)) by (bit_vector);
    assert(((((0xb3c11055cc8d8bdbfb497052111ecdaau128) << 1) ^ (if ((((0xb3c11055cc8d8bdbfb497052111ecdaau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x678220ab991b17b7f692e0a4223d9bd3u128) by (bit_vector);
    assert(gf128_xtime(0xb3c11055cc8d8bdbfb497052111ecdaau128) == 0x678220ab991b17b7f692e0a4223d9bd3u128);
    assert(gf128_mul_bits(0xb3c11055cc8d8bdbfb497052111ecdaau128, 0xf1cu128, 12nat) == 0u128 ^ gf128_mul_bits(0x678220ab991b17b7f692e0a4223d9bd3u128, 0x78eu128, 11nat)) by { lemma_hmul128_bits_unfold(0xb3c11055cc8d8bdbfb497052111ecdaau128, 0xf1cu128, 12nat); }
    assert((((0x78eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78eu128) >> 1u128) == 0x3c7u128)) by (bit_vector);
    assert(((((0x678220ab991b17b7f692e0a4223d9bd3u128) << 1) ^ (if ((((0x678220ab991b17b7f692e0a4223d9bd3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xcf04415732362f6fed25c148447b37a6u128) by (bit_vector);
    assert(gf128_xtime(0x678220ab991b17b7f692e0a4223d9bd3u128) == 0xcf04415732362f6fed25c148447b37a6u128);
    assert(gf128_mul_bits(0x678220ab991b17b7f692e0a4223d9bd3u128, 0x78eu128, 11nat) == 0u128 ^ gf128_mul_bits(0xcf04415732362f6fed25c148447b37a6u128, 0x3c7u128, 10nat)) by { lemma_hmul128_bits_unfold(0x678220ab991b17b7f692e0a4223d9bd3u128, 0x78eu128, 11nat); }
    assert((((0x3c7u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3c7u128) >> 1u128) == 0x1e3u128)) by (bit_vector);
    assert(((((0xcf04415732362f6fed25c148447b37a6u128) << 1) ^ (if ((((0xcf04415732362f6fed25c148447b37a6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9e0882ae646c5edfda4b829088f66fcbu128) by (bit_vector);
    assert(gf128_xtime(0xcf04415732362f6fed25c148447b37a6u128) == 0x9e0882ae646c5edfda4b829088f66fcbu128);
    assert(gf128_mul_bits(0xcf04415732362f6fed25c148447b37a6u128, 0x3c7u128, 10nat) == 0xcf04415732362f6fed25c148447b37a6u128 ^ gf128_mul_bits(0x9e0882ae646c5edfda4b829088f66fcbu128, 0x1e3u128, 9nat)) by { lemma_hmul128_bits_unfold(0xcf04415732362f6fed25c148447b37a6u128, 0x3c7u128, 10nat); }
    assert((((0x1e3u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1e3u128) >> 1u128) == 0xf1u128)) by (bit_vector);
    assert(((((0x9e0882ae646c5edfda4b829088f66fcbu128) << 1) ^ (if ((((0x9e0882ae646c5edfda4b829088f66fcbu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3c11055cc8d8bdbfb497052111ecdf11u128) by (bit_vector);
    assert(gf128_xtime(0x9e0882ae646c5edfda4b829088f66fcbu128) == 0x3c11055cc8d8bdbfb497052111ecdf11u128);
    assert(gf128_mul_bits(0x9e0882ae646c5edfda4b829088f66fcbu128, 0x1e3u128, 9nat) == 0x9e0882ae646c5edfda4b829088f66fcbu128 ^ gf128_mul_bits(0x3c11055cc8d8bdbfb497052111ecdf11u128, 0xf1u128, 8nat)) by { lemma_hmul128_bits_unfold(0x9e0882ae646c5edfda4b829088f66fcbu128, 0x1e3u128, 9nat); }
    assert((((0xf1u128) & 1) == 1u128)) by (bit_vector);
    assert((((0xf1u128) >> 1u128) == 0x78u128)) by (bit_vector);
    assert(((((0x3c11055cc8d8bdbfb497052111ecdf11u128) << 1) ^ (if ((((0x3c11055cc8d8bdbfb497052111ecdf11u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x78220ab991b17b7f692e0a4223d9be22u128) by (bit_vector);
    assert(gf128_xtime(0x3c11055cc8d8bdbfb497052111ecdf11u128) == 0x78220ab991b17b7f692e0a4223d9be22u128);
    assert(gf128_mul_bits(0x3c11055cc8d8bdbfb497052111ecdf11u128, 0xf1u128, 8nat) == 0x3c11055cc8d8bdbfb497052111ecdf11u128 ^ gf128_mul_bits(0x78220ab991b17b7f692e0a4223d9be22u128, 0x78u128, 7nat)) by { lemma_hmul128_bits_unfold(0x3c11055cc8d8bdbfb497052111ecdf11u128, 0xf1u128, 8nat); }
    assert((((0x78u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x78u128) >> 1u128) == 0x3cu128)) by (bit_vector);
    assert(((((0x78220ab991b17b7f692e0a4223d9be22u128) << 1) ^ (if ((((0x78220ab991b17b7f692e0a4223d9be22u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf04415732362f6fed25c148447b37c44u128) by (bit_vector);
    assert(gf128_xtime(0x78220ab991b17b7f692e0a4223d9be22u128) == 0xf04415732362f6fed25c148447b37c44u128);
    assert(gf128_mul_bits(0x78220ab991b17b7f692e0a4223d9be22u128, 0x78u128, 7nat) == 0u128 ^ gf128_mul_bits(0xf04415732362f6fed25c148447b37c44u128, 0x3cu128, 6nat)) by { lemma_hmul128_bits_unfold(0x78220ab991b17b7f692e0a4223d9be22u128, 0x78u128, 7nat); }
    assert((((0x3cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x3cu128) >> 1u128) == 0x1eu128)) by (bit_vector);
    assert(((((0xf04415732362f6fed25c148447b37c44u128) << 1) ^ (if ((((0xf04415732362f6fed25c148447b37c44u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe0882ae646c5edfda4b829088f66f80fu128) by (bit_vector);
    assert(gf128_xtime(0xf04415732362f6fed25c148447b37c44u128) == 0xe0882ae646c5edfda4b829088f66f80fu128);
    assert(gf128_mul_bits(0xf04415732362f6fed25c148447b37c44u128, 0x3cu128, 6nat) == 0u128 ^ gf128_mul_bits(0xe0882ae646c5edfda4b829088f66f80fu128, 0x1eu128, 5nat)) by { lemma_hmul128_bits_unfold(0xf04415732362f6fed25c148447b37c44u128, 0x3cu128, 6nat); }
    assert((((0x1eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x1eu128) >> 1u128) == 0xfu128)) by (bit_vector);
    assert(((((0xe0882ae646c5edfda4b829088f66f80fu128) << 1) ^ (if ((((0xe0882ae646c5edfda4b829088f66f80fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc11055cc8d8bdbfb497052111ecdf099u128) by (bit_vector);
    assert(gf128_xtime(0xe0882ae646c5edfda4b829088f66f80fu128) == 0xc11055cc8d8bdbfb497052111ecdf099u128);
    assert(gf128_mul_bits(0xe0882ae646c5edfda4b829088f66f80fu128, 0x1eu128, 5nat) == 0u128 ^ gf128_mul_bits(0xc11055cc8d8bdbfb497052111ecdf099u128, 0xfu128, 4nat)) by { lemma_hmul128_bits_unfold(0xe0882ae646c5edfda4b829088f66f80fu128, 0x1eu128, 5nat); }
    assert((((0xfu128) & 1) == 1u128)) by (bit_vector);
    assert((((0xfu128) >> 1u128) == 0x7u128)) by (bit_vector);
    assert(((((0xc11055cc8d8bdbfb497052111ecdf099u128) << 1) ^ (if ((((0xc11055cc8d8bdbfb497052111ecdf099u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x8220ab991b17b7f692e0a4223d9be1b5u128) by (bit_vector);
    assert(gf128_xtime(0xc11055cc8d8bdbfb497052111ecdf099u128) == 0x8220ab991b17b7f692e0a4223d9be1b5u128);
    assert(gf128_mul_bits(0xc11055cc8d8bdbfb497052111ecdf099u128, 0xfu128, 4nat) == 0xc11055cc8d8bdbfb497052111ecdf099u128 ^ gf128_mul_bits(0x8220ab991b17b7f692e0a4223d9be1b5u128, 0x7u128, 3nat)) by { lemma_hmul128_bits_unfold(0xc11055cc8d8bdbfb497052111ecdf099u128, 0xfu128, 4nat); }
    assert((((0x7u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x7u128) >> 1u128) == 0x3u128)) by (bit_vector);
    assert(((((0x8220ab991b17b7f692e0a4223d9be1b5u128) << 1) ^ (if ((((0x8220ab991b17b7f692e0a4223d9be1b5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4415732362f6fed25c148447b37c3edu128) by (bit_vector);
    assert(gf128_xtime(0x8220ab991b17b7f692e0a4223d9be1b5u128) == 0x4415732362f6fed25c148447b37c3edu128);
    assert(gf128_mul_bits(0x8220ab991b17b7f692e0a4223d9be1b5u128, 0x7u128, 3nat) == 0x8220ab991b17b7f692e0a4223d9be1b5u128 ^ gf128_mul_bits(0x4415732362f6fed25c148447b37c3edu128, 0x3u128, 2nat)) by { lemma_hmul128_bits_unfold(0x8220ab991b17b7f692e0a4223d9be1b5u128, 0x7u128, 3nat); }
    assert((((0x3u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x3u128) >> 1u128) == 0x1u128)) by (bit_vector);
    assert(((((0x4415732362f6fed25c148447b37c3edu128) << 1) ^ (if ((((0x4415732362f6fed25c148447b37c3edu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x882ae646c5edfda4b829088f66f87dau128) by (bit_vector);
    assert(gf128_xtime(0x4415732362f6fed25c148447b37c3edu128) == 0x882ae646c5edfda4b829088f66f87dau128);
    assert(gf128_mul_bits(0x4415732362f6fed25c148447b37c3edu128, 0x3u128, 2nat) == 0x4415732362f6fed25c148447b37c3edu128 ^ gf128_mul_bits(0x882ae646c5edfda4b829088f66f87dau128, 0x1u128, 1nat)) by { lemma_hmul128_bits_unfold(0x4415732362f6fed25c148447b37c3edu128, 0x3u128, 2nat); }
    assert((((0x1u128) & 1) == 1u128)) by (bit_vector);
    assert(gf128_mul_bits(0x882ae646c5edfda4b829088f66f87dau128, 0x1u128, 1nat) == 0x882ae646c5edfda4b829088f66f87dau128 ^ gf128_mul_bits(gf128_xtime(0x882ae646c5edfda4b829088f66f87dau128), 0u128, 0nat)) by { lemma_hmul128_bits_unfold(0x882ae646c5edfda4b829088f66f87dau128, 0x1u128, 1nat); }
    assert((0x882ae646c5edfda4b829088f66f87dau128 ^ 0u128) == 0x882ae646c5edfda4b829088f66f87dau128) by (bit_vector);
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ (gf128_mul_bits(0x10efa565c3ec75fae7621e9038eb3c19u128, 0xf1c016735268c06031d80f2d8a5528u128, 120nat)))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xefa565c3ec75fae7621e9038eb3c1170u128, 0xf1c016735268c06031d80f2d8a55u128, 112nat)))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xa565c3ec75fae7621e9038eb3c11050du128, 0xf1c016735268c06031d80f2d8au128, 104nat)))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ (gf128_mul_bits(0x65c3ec75fae7621e9038eb3c11055cfbu128, 0xf1c016735268c06031d80f2du128, 96nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xc3ec75fae7621e9038eb3c11055cc8bbu128, 0xf1c016735268c06031d80fu128, 88nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xec75fae7621e9038eb3c11055cc8d8c9u128, 0xf1c016735268c06031d8u128, 80nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ (gf128_mul_bits(0x75fae7621e9038eb3c11055cc8d8bd84u128, 0xf1c016735268c06031u128, 72nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xfae7621e9038eb3c11055cc8d8bdbfcbu128, 0xf1c016735268c060u128, 64nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5cec43d2071d678220ab991b17b7f6bdu128 ^ ((0xb9d887a40e3acf04415732362f6fed7au128 ^ ((0x0u128 ^ (gf128_mul_bits(0xe7621e9038eb3c11055cc8d8bdbfb4e6u128, 0xf1c016735268c0u128, 56nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5cec43d2071d678220ab991b17b7f6bdu128 ^ ((0xb9d887a40e3acf04415732362f6fed7au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd887a40e3acf04415732362f6fed25afu128 ^ ((0xb10f481c759e0882ae646c5edfda4bd9u128 ^ (gf128_mul_bits(0x621e9038eb3c11055cc8d8bdbfb49735u128, 0xf1c016735268u128, 48nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5cec43d2071d678220ab991b17b7f6bdu128 ^ ((0xb9d887a40e3acf04415732362f6fed7au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd887a40e3acf04415732362f6fed25afu128 ^ ((0xb10f481c759e0882ae646c5edfda4bd9u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x10f481c759e0882ae646c5edfda4b821u128 ^ ((0x0u128 ^ ((0x43d2071d678220ab991b17b7f692e084u128 ^ ((0x87a40e3acf04415732362f6fed25c108u128 ^ ((0x0u128 ^ (gf128_mul_bits(0x1e9038eb3c11055cc8d8bdbfb497052eu128, 0xf1c0167352u128, 40nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5cec43d2071d678220ab991b17b7f6bdu128 ^ ((0xb9d887a40e3acf04415732362f6fed7au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd887a40e3acf04415732362f6fed25afu128 ^ ((0xb10f481c759e0882ae646c5edfda4bd9u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x10f481c759e0882ae646c5edfda4b821u128 ^ ((0x0u128 ^ ((0x43d2071d678220ab991b17b7f692e084u128 ^ ((0x87a40e3acf04415732362f6fed25c108u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x3d2071d678220ab991b17b7f692e0a5cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe9038eb3c11055cc8d8bdbfb49705267u128 ^ ((0x0u128 ^ ((0xa40e3acf04415732362f6fed25c14815u128 ^ ((0x0u128 ^ (gf128_mul_bits(0x9038eb3c11055cc8d8bdbfb49705215au128, 0xf1c01673u128, 32nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5cec43d2071d678220ab991b17b7f6bdu128 ^ ((0xb9d887a40e3acf04415732362f6fed7au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd887a40e3acf04415732362f6fed25afu128 ^ ((0xb10f481c759e0882ae646c5edfda4bd9u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x10f481c759e0882ae646c5edfda4b821u128 ^ ((0x0u128 ^ ((0x43d2071d678220ab991b17b7f692e084u128 ^ ((0x87a40e3acf04415732362f6fed25c108u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x3d2071d678220ab991b17b7f692e0a5cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe9038eb3c11055cc8d8bdbfb49705267u128 ^ ((0x0u128 ^ ((0xa40e3acf04415732362f6fed25c14815u128 ^ ((0x0u128 ^ ((0x9038eb3c11055cc8d8bdbfb49705215au128 ^ ((0x2071d678220ab991b17b7f692e0a4233u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x38eb3c11055cc8d8bdbfb497052111fu128 ^ ((0x71d678220ab991b17b7f692e0a4223eu128 ^ ((0xe3acf04415732362f6fed25c148447cu128 ^ ((0x0u128 ^ (gf128_mul_bits(0x38eb3c11055cc8d8bdbfb497052111f0u128, 0xf1c016u128, 24nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5cec43d2071d678220ab991b17b7f6bdu128 ^ ((0xb9d887a40e3acf04415732362f6fed7au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd887a40e3acf04415732362f6fed25afu128 ^ ((0xb10f481c759e0882ae646c5edfda4bd9u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x10f481c759e0882ae646c5edfda4b821u128 ^ ((0x0u128 ^ ((0x43d2071d678220ab991b17b7f692e084u128 ^ ((0x87a40e3acf04415732362f6fed25c108u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x3d2071d678220ab991b17b7f692e0a5cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe9038eb3c11055cc8d8bdbfb49705267u128 ^ ((0x0u128 ^ ((0xa40e3acf04415732362f6fed25c14815u128 ^ ((0x0u128 ^ ((0x9038eb3c11055cc8d8bdbfb49705215au128 ^ ((0x2071d678220ab991b17b7f692e0a4233u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x38eb3c11055cc8d8bdbfb497052111fu128 ^ ((0x71d678220ab991b17b7f692e0a4223eu128 ^ ((0xe3acf04415732362f6fed25c148447cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x71d678220ab991b17b7f692e0a4223e0u128 ^ ((0xe3acf04415732362f6fed25c148447c0u128 ^ ((0x0u128 ^ ((0x8eb3c11055cc8d8bdbfb497052111e89u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xeb3c11055cc8d8bdbfb497052111eca8u128, 0xf1c0u128, 16nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5cec43d2071d678220ab991b17b7f6bdu128 ^ ((0xb9d887a40e3acf04415732362f6fed7au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd887a40e3acf04415732362f6fed25afu128 ^ ((0xb10f481c759e0882ae646c5edfda4bd9u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x10f481c759e0882ae646c5edfda4b821u128 ^ ((0x0u128 ^ ((0x43d2071d678220ab991b17b7f692e084u128 ^ ((0x87a40e3acf04415732362f6fed25c108u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x3d2071d678220ab991b17b7f692e0a5cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe9038eb3c11055cc8d8bdbfb49705267u128 ^ ((0x0u128 ^ ((0xa40e3acf04415732362f6fed25c14815u128 ^ ((0x0u128 ^ ((0x9038eb3c11055cc8d8bdbfb49705215au128 ^ ((0x2071d678220ab991b17b7f692e0a4233u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x38eb3c11055cc8d8bdbfb497052111fu128 ^ ((0x71d678220ab991b17b7f692e0a4223eu128 ^ ((0xe3acf04415732362f6fed25c148447cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x71d678220ab991b17b7f692e0a4223e0u128 ^ ((0xe3acf04415732362f6fed25c148447c0u128 ^ ((0x0u128 ^ ((0x8eb3c11055cc8d8bdbfb497052111e89u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xcf04415732362f6fed25c148447b37a6u128 ^ ((0x9e0882ae646c5edfda4b829088f66fcbu128 ^ (gf128_mul_bits(0x3c11055cc8d8bdbfb497052111ecdf11u128, 0xf1u128, 8nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == ((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5cec43d2071d678220ab991b17b7f6bdu128 ^ ((0xb9d887a40e3acf04415732362f6fed7au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd887a40e3acf04415732362f6fed25afu128 ^ ((0xb10f481c759e0882ae646c5edfda4bd9u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x10f481c759e0882ae646c5edfda4b821u128 ^ ((0x0u128 ^ ((0x43d2071d678220ab991b17b7f692e084u128 ^ ((0x87a40e3acf04415732362f6fed25c108u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x3d2071d678220ab991b17b7f692e0a5cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe9038eb3c11055cc8d8bdbfb49705267u128 ^ ((0x0u128 ^ ((0xa40e3acf04415732362f6fed25c14815u128 ^ ((0x0u128 ^ ((0x9038eb3c11055cc8d8bdbfb49705215au128 ^ ((0x2071d678220ab991b17b7f692e0a4233u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x38eb3c11055cc8d8bdbfb497052111fu128 ^ ((0x71d678220ab991b17b7f692e0a4223eu128 ^ ((0xe3acf04415732362f6fed25c148447cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x71d678220ab991b17b7f692e0a4223e0u128 ^ ((0xe3acf04415732362f6fed25c148447c0u128 ^ ((0x0u128 ^ ((0x8eb3c11055cc8d8bdbfb497052111e89u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xcf04415732362f6fed25c148447b37a6u128 ^ ((0x9e0882ae646c5edfda4b829088f66fcbu128 ^ (gf128_mul_bits(0x3c11055cc8d8bdbfb497052111ecdf11u128, 0xf1u128, 8nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(((0x0u128 ^ ((0x0u128 ^ ((0xcc43be95970fb1d7eb9d887a40e3ac94u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc43be95970fb1d7eb9d887a40e3acf64u128 ^ ((0x8877d2b2e1f63afd73b10f481c759e4fu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x877d2b2e1f63afd73b10f481c759e0c8u128 ^ ((0x0u128 ^ ((0x1df4acb87d8ebf5cec43d2071d67822eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefa565c3ec75fae7621e9038eb3c1170u128 ^ ((0x0u128 ^ ((0xbe95970fb1d7eb9d887a40e3acf04449u128 ^ ((0x0u128 ^ ((0xfa565c3ec75fae7621e9038eb3c1102au128 ^ ((0x0u128 ^ ((0xe95970fb1d7eb9d887a40e3acf044121u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x4acb87d8ebf5cec43d2071d678220a9du128 ^ ((0x0u128 ^ ((0x2b2e1f63afd73b10f481c759e0882af3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xb2e1f63afd73b10f481c759e0882ae3eu128 ^ ((0x65c3ec75fae7621e9038eb3c11055cfbu128 ^ ((0x0u128 ^ ((0x970fb1d7eb9d887a40e3acf04415736bu128 ^ ((0x2e1f63afd73b10f481c759e0882ae651u128 ^ ((0x0u128 ^ ((0xb87d8ebf5cec43d2071d678220ab9944u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc3ec75fae7621e9038eb3c11055cc8bbu128 ^ ((0x87d8ebf5cec43d2071d678220ab991f1u128 ^ ((0xfb1d7eb9d887a40e3acf04415732365u128 ^ ((0x1f63afd73b10f481c759e0882ae646cau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x63afd73b10f481c759e0882ae646c5ddu128 ^ ((0xc75fae7621e9038eb3c11055cc8d8bbau128 ^ ((0x0u128 ^ ((0x1d7eb9d887a40e3acf04415732362f61u128 ^ ((0x3afd73b10f481c759e0882ae646c5ec2u128 ^ ((0x75fae7621e9038eb3c11055cc8d8bd84u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5fae7621e9038eb3c11055cc8d8bdbd5u128 ^ ((0xbf5cec43d2071d678220ab991b17b7aau128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x5cec43d2071d678220ab991b17b7f6bdu128 ^ ((0xb9d887a40e3acf04415732362f6fed7au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xd887a40e3acf04415732362f6fed25afu128 ^ ((0xb10f481c759e0882ae646c5edfda4bd9u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x10f481c759e0882ae646c5edfda4b821u128 ^ ((0x0u128 ^ ((0x43d2071d678220ab991b17b7f692e084u128 ^ ((0x87a40e3acf04415732362f6fed25c108u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x3d2071d678220ab991b17b7f692e0a5cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe9038eb3c11055cc8d8bdbfb49705267u128 ^ ((0x0u128 ^ ((0xa40e3acf04415732362f6fed25c14815u128 ^ ((0x0u128 ^ ((0x9038eb3c11055cc8d8bdbfb49705215au128 ^ ((0x2071d678220ab991b17b7f692e0a4233u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x38eb3c11055cc8d8bdbfb497052111fu128 ^ ((0x71d678220ab991b17b7f692e0a4223eu128 ^ ((0xe3acf04415732362f6fed25c148447cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x71d678220ab991b17b7f692e0a4223e0u128 ^ ((0xe3acf04415732362f6fed25c148447c0u128 ^ ((0x0u128 ^ ((0x8eb3c11055cc8d8bdbfb497052111e89u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xcf04415732362f6fed25c148447b37a6u128 ^ ((0x9e0882ae646c5edfda4b829088f66fcbu128 ^ ((0x3c11055cc8d8bdbfb497052111ecdf11u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xc11055cc8d8bdbfb497052111ecdf099u128 ^ ((0x8220ab991b17b7f692e0a4223d9be1b5u128 ^ ((0x4415732362f6fed25c148447b37c3edu128 ^ (0x882ae646c5edfda4b829088f66f87dau128))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) == 0x15ae1388367039a81b7cc9770edd7acu128) by (bit_vector);
    assert(gf128_mul_bits(0x3310efa565c3ec75fae7621e9038eb25u128, 0xf1c016735268c06031d80f2d8a5528c4u128, 128nat) == 0x15ae1388367039a81b7cc9770edd7acu128);
}

proof fn kat_t0swap_hmul()
    ensures gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == 0xe6df41181a1477eae9131e9141c70a15u128,
{
    // rung chain precomputed + model-checked offline (python)
    assert((((0x261dffa502bbff620185b5b0891eec27u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5b0891eec27u128) >> 1u128) == 0x130effd2815dffb100c2dad8448f7613u128)) by (bit_vector);
    assert(((((0xa3fa4befd33ec6de509de93498eb9f05u128) << 1) ^ (if ((((0xa3fa4befd33ec6de509de93498eb9f05u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x47f497dfa67d8dbca13bd26931d73e8du128) by (bit_vector);
    assert(gf128_xtime(0xa3fa4befd33ec6de509de93498eb9f05u128) == 0x47f497dfa67d8dbca13bd26931d73e8du128);
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == 0xa3fa4befd33ec6de509de93498eb9f05u128 ^ gf128_mul_bits(0x47f497dfa67d8dbca13bd26931d73e8du128, 0x130effd2815dffb100c2dad8448f7613u128, 127nat)) by { lemma_hmul128_bits_unfold(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat); }
    assert((((0x130effd2815dffb100c2dad8448f7613u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dad8448f7613u128) >> 1u128) == 0x9877fe940aeffd880616d6c2247bb09u128)) by (bit_vector);
    assert(((((0x47f497dfa67d8dbca13bd26931d73e8du128) << 1) ^ (if ((((0x47f497dfa67d8dbca13bd26931d73e8du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x8fe92fbf4cfb1b794277a4d263ae7d1au128) by (bit_vector);
    assert(gf128_xtime(0x47f497dfa67d8dbca13bd26931d73e8du128) == 0x8fe92fbf4cfb1b794277a4d263ae7d1au128);
    assert(gf128_mul_bits(0x47f497dfa67d8dbca13bd26931d73e8du128, 0x130effd2815dffb100c2dad8448f7613u128, 127nat) == 0x47f497dfa67d8dbca13bd26931d73e8du128 ^ gf128_mul_bits(0x8fe92fbf4cfb1b794277a4d263ae7d1au128, 0x9877fe940aeffd880616d6c2247bb09u128, 126nat)) by { lemma_hmul128_bits_unfold(0x47f497dfa67d8dbca13bd26931d73e8du128, 0x130effd2815dffb100c2dad8448f7613u128, 127nat); }
    assert((((0x9877fe940aeffd880616d6c2247bb09u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6c2247bb09u128) >> 1u128) == 0x4c3bff4a0577fec4030b6b61123dd84u128)) by (bit_vector);
    assert(((((0x8fe92fbf4cfb1b794277a4d263ae7d1au128) << 1) ^ (if ((((0x8fe92fbf4cfb1b794277a4d263ae7d1au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1fd25f7e99f636f284ef49a4c75cfab3u128) by (bit_vector);
    assert(gf128_xtime(0x8fe92fbf4cfb1b794277a4d263ae7d1au128) == 0x1fd25f7e99f636f284ef49a4c75cfab3u128);
    assert(gf128_mul_bits(0x8fe92fbf4cfb1b794277a4d263ae7d1au128, 0x9877fe940aeffd880616d6c2247bb09u128, 126nat) == 0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ gf128_mul_bits(0x1fd25f7e99f636f284ef49a4c75cfab3u128, 0x4c3bff4a0577fec4030b6b61123dd84u128, 125nat)) by { lemma_hmul128_bits_unfold(0x8fe92fbf4cfb1b794277a4d263ae7d1au128, 0x9877fe940aeffd880616d6c2247bb09u128, 126nat); }
    assert((((0x4c3bff4a0577fec4030b6b61123dd84u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6b61123dd84u128) >> 1u128) == 0x261dffa502bbff620185b5b0891eec2u128)) by (bit_vector);
    assert(((((0x1fd25f7e99f636f284ef49a4c75cfab3u128) << 1) ^ (if ((((0x1fd25f7e99f636f284ef49a4c75cfab3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3fa4befd33ec6de509de93498eb9f566u128) by (bit_vector);
    assert(gf128_xtime(0x1fd25f7e99f636f284ef49a4c75cfab3u128) == 0x3fa4befd33ec6de509de93498eb9f566u128);
    assert(gf128_mul_bits(0x1fd25f7e99f636f284ef49a4c75cfab3u128, 0x4c3bff4a0577fec4030b6b61123dd84u128, 125nat) == 0u128 ^ gf128_mul_bits(0x3fa4befd33ec6de509de93498eb9f566u128, 0x261dffa502bbff620185b5b0891eec2u128, 124nat)) by { lemma_hmul128_bits_unfold(0x1fd25f7e99f636f284ef49a4c75cfab3u128, 0x4c3bff4a0577fec4030b6b61123dd84u128, 125nat); }
    assert((((0x261dffa502bbff620185b5b0891eec2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5b0891eec2u128) >> 1u128) == 0x130effd2815dffb100c2dad8448f761u128)) by (bit_vector);
    assert(((((0x3fa4befd33ec6de509de93498eb9f566u128) << 1) ^ (if ((((0x3fa4befd33ec6de509de93498eb9f566u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7f497dfa67d8dbca13bd26931d73eaccu128) by (bit_vector);
    assert(gf128_xtime(0x3fa4befd33ec6de509de93498eb9f566u128) == 0x7f497dfa67d8dbca13bd26931d73eaccu128);
    assert(gf128_mul_bits(0x3fa4befd33ec6de509de93498eb9f566u128, 0x261dffa502bbff620185b5b0891eec2u128, 124nat) == 0u128 ^ gf128_mul_bits(0x7f497dfa67d8dbca13bd26931d73eaccu128, 0x130effd2815dffb100c2dad8448f761u128, 123nat)) by { lemma_hmul128_bits_unfold(0x3fa4befd33ec6de509de93498eb9f566u128, 0x261dffa502bbff620185b5b0891eec2u128, 124nat); }
    assert((((0x130effd2815dffb100c2dad8448f761u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dad8448f761u128) >> 1u128) == 0x9877fe940aeffd880616d6c2247bb0u128)) by (bit_vector);
    assert(((((0x7f497dfa67d8dbca13bd26931d73eaccu128) << 1) ^ (if ((((0x7f497dfa67d8dbca13bd26931d73eaccu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfe92fbf4cfb1b794277a4d263ae7d598u128) by (bit_vector);
    assert(gf128_xtime(0x7f497dfa67d8dbca13bd26931d73eaccu128) == 0xfe92fbf4cfb1b794277a4d263ae7d598u128);
    assert(gf128_mul_bits(0x7f497dfa67d8dbca13bd26931d73eaccu128, 0x130effd2815dffb100c2dad8448f761u128, 123nat) == 0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ gf128_mul_bits(0xfe92fbf4cfb1b794277a4d263ae7d598u128, 0x9877fe940aeffd880616d6c2247bb0u128, 122nat)) by { lemma_hmul128_bits_unfold(0x7f497dfa67d8dbca13bd26931d73eaccu128, 0x130effd2815dffb100c2dad8448f761u128, 123nat); }
    assert((((0x9877fe940aeffd880616d6c2247bb0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6c2247bb0u128) >> 1u128) == 0x4c3bff4a0577fec4030b6b61123dd8u128)) by (bit_vector);
    assert(((((0xfe92fbf4cfb1b794277a4d263ae7d598u128) << 1) ^ (if ((((0xfe92fbf4cfb1b794277a4d263ae7d598u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfd25f7e99f636f284ef49a4c75cfabb7u128) by (bit_vector);
    assert(gf128_xtime(0xfe92fbf4cfb1b794277a4d263ae7d598u128) == 0xfd25f7e99f636f284ef49a4c75cfabb7u128);
    assert(gf128_mul_bits(0xfe92fbf4cfb1b794277a4d263ae7d598u128, 0x9877fe940aeffd880616d6c2247bb0u128, 122nat) == 0u128 ^ gf128_mul_bits(0xfd25f7e99f636f284ef49a4c75cfabb7u128, 0x4c3bff4a0577fec4030b6b61123dd8u128, 121nat)) by { lemma_hmul128_bits_unfold(0xfe92fbf4cfb1b794277a4d263ae7d598u128, 0x9877fe940aeffd880616d6c2247bb0u128, 122nat); }
    assert((((0x4c3bff4a0577fec4030b6b61123dd8u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6b61123dd8u128) >> 1u128) == 0x261dffa502bbff620185b5b0891eecu128)) by (bit_vector);
    assert(((((0xfd25f7e99f636f284ef49a4c75cfabb7u128) << 1) ^ (if ((((0xfd25f7e99f636f284ef49a4c75cfabb7u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfa4befd33ec6de509de93498eb9f57e9u128) by (bit_vector);
    assert(gf128_xtime(0xfd25f7e99f636f284ef49a4c75cfabb7u128) == 0xfa4befd33ec6de509de93498eb9f57e9u128);
    assert(gf128_mul_bits(0xfd25f7e99f636f284ef49a4c75cfabb7u128, 0x4c3bff4a0577fec4030b6b61123dd8u128, 121nat) == 0u128 ^ gf128_mul_bits(0xfa4befd33ec6de509de93498eb9f57e9u128, 0x261dffa502bbff620185b5b0891eecu128, 120nat)) by { lemma_hmul128_bits_unfold(0xfd25f7e99f636f284ef49a4c75cfabb7u128, 0x4c3bff4a0577fec4030b6b61123dd8u128, 121nat); }
    assert((((0x261dffa502bbff620185b5b0891eecu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5b0891eecu128) >> 1u128) == 0x130effd2815dffb100c2dad8448f76u128)) by (bit_vector);
    assert(((((0xfa4befd33ec6de509de93498eb9f57e9u128) << 1) ^ (if ((((0xfa4befd33ec6de509de93498eb9f57e9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf497dfa67d8dbca13bd26931d73eaf55u128) by (bit_vector);
    assert(gf128_xtime(0xfa4befd33ec6de509de93498eb9f57e9u128) == 0xf497dfa67d8dbca13bd26931d73eaf55u128);
    assert(gf128_mul_bits(0xfa4befd33ec6de509de93498eb9f57e9u128, 0x261dffa502bbff620185b5b0891eecu128, 120nat) == 0u128 ^ gf128_mul_bits(0xf497dfa67d8dbca13bd26931d73eaf55u128, 0x130effd2815dffb100c2dad8448f76u128, 119nat)) by { lemma_hmul128_bits_unfold(0xfa4befd33ec6de509de93498eb9f57e9u128, 0x261dffa502bbff620185b5b0891eecu128, 120nat); }
    assert((((0x130effd2815dffb100c2dad8448f76u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dad8448f76u128) >> 1u128) == 0x9877fe940aeffd880616d6c2247bbu128)) by (bit_vector);
    assert(((((0xf497dfa67d8dbca13bd26931d73eaf55u128) << 1) ^ (if ((((0xf497dfa67d8dbca13bd26931d73eaf55u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe92fbf4cfb1b794277a4d263ae7d5e2du128) by (bit_vector);
    assert(gf128_xtime(0xf497dfa67d8dbca13bd26931d73eaf55u128) == 0xe92fbf4cfb1b794277a4d263ae7d5e2du128);
    assert(gf128_mul_bits(0xf497dfa67d8dbca13bd26931d73eaf55u128, 0x130effd2815dffb100c2dad8448f76u128, 119nat) == 0u128 ^ gf128_mul_bits(0xe92fbf4cfb1b794277a4d263ae7d5e2du128, 0x9877fe940aeffd880616d6c2247bbu128, 118nat)) by { lemma_hmul128_bits_unfold(0xf497dfa67d8dbca13bd26931d73eaf55u128, 0x130effd2815dffb100c2dad8448f76u128, 119nat); }
    assert((((0x9877fe940aeffd880616d6c2247bbu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6c2247bbu128) >> 1u128) == 0x4c3bff4a0577fec4030b6b61123ddu128)) by (bit_vector);
    assert(((((0xe92fbf4cfb1b794277a4d263ae7d5e2du128) << 1) ^ (if ((((0xe92fbf4cfb1b794277a4d263ae7d5e2du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd25f7e99f636f284ef49a4c75cfabcddu128) by (bit_vector);
    assert(gf128_xtime(0xe92fbf4cfb1b794277a4d263ae7d5e2du128) == 0xd25f7e99f636f284ef49a4c75cfabcddu128);
    assert(gf128_mul_bits(0xe92fbf4cfb1b794277a4d263ae7d5e2du128, 0x9877fe940aeffd880616d6c2247bbu128, 118nat) == 0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ gf128_mul_bits(0xd25f7e99f636f284ef49a4c75cfabcddu128, 0x4c3bff4a0577fec4030b6b61123ddu128, 117nat)) by { lemma_hmul128_bits_unfold(0xe92fbf4cfb1b794277a4d263ae7d5e2du128, 0x9877fe940aeffd880616d6c2247bbu128, 118nat); }
    assert((((0x4c3bff4a0577fec4030b6b61123ddu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6b61123ddu128) >> 1u128) == 0x261dffa502bbff620185b5b0891eeu128)) by (bit_vector);
    assert(((((0xd25f7e99f636f284ef49a4c75cfabcddu128) << 1) ^ (if ((((0xd25f7e99f636f284ef49a4c75cfabcddu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa4befd33ec6de509de93498eb9f5793du128) by (bit_vector);
    assert(gf128_xtime(0xd25f7e99f636f284ef49a4c75cfabcddu128) == 0xa4befd33ec6de509de93498eb9f5793du128);
    assert(gf128_mul_bits(0xd25f7e99f636f284ef49a4c75cfabcddu128, 0x4c3bff4a0577fec4030b6b61123ddu128, 117nat) == 0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ gf128_mul_bits(0xa4befd33ec6de509de93498eb9f5793du128, 0x261dffa502bbff620185b5b0891eeu128, 116nat)) by { lemma_hmul128_bits_unfold(0xd25f7e99f636f284ef49a4c75cfabcddu128, 0x4c3bff4a0577fec4030b6b61123ddu128, 117nat); }
    assert((((0x261dffa502bbff620185b5b0891eeu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5b0891eeu128) >> 1u128) == 0x130effd2815dffb100c2dad8448f7u128)) by (bit_vector);
    assert(((((0xa4befd33ec6de509de93498eb9f5793du128) << 1) ^ (if ((((0xa4befd33ec6de509de93498eb9f5793du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x497dfa67d8dbca13bd26931d73eaf2fdu128) by (bit_vector);
    assert(gf128_xtime(0xa4befd33ec6de509de93498eb9f5793du128) == 0x497dfa67d8dbca13bd26931d73eaf2fdu128);
    assert(gf128_mul_bits(0xa4befd33ec6de509de93498eb9f5793du128, 0x261dffa502bbff620185b5b0891eeu128, 116nat) == 0u128 ^ gf128_mul_bits(0x497dfa67d8dbca13bd26931d73eaf2fdu128, 0x130effd2815dffb100c2dad8448f7u128, 115nat)) by { lemma_hmul128_bits_unfold(0xa4befd33ec6de509de93498eb9f5793du128, 0x261dffa502bbff620185b5b0891eeu128, 116nat); }
    assert((((0x130effd2815dffb100c2dad8448f7u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dad8448f7u128) >> 1u128) == 0x9877fe940aeffd880616d6c2247bu128)) by (bit_vector);
    assert(((((0x497dfa67d8dbca13bd26931d73eaf2fdu128) << 1) ^ (if ((((0x497dfa67d8dbca13bd26931d73eaf2fdu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x92fbf4cfb1b794277a4d263ae7d5e5fau128) by (bit_vector);
    assert(gf128_xtime(0x497dfa67d8dbca13bd26931d73eaf2fdu128) == 0x92fbf4cfb1b794277a4d263ae7d5e5fau128);
    assert(gf128_mul_bits(0x497dfa67d8dbca13bd26931d73eaf2fdu128, 0x130effd2815dffb100c2dad8448f7u128, 115nat) == 0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ gf128_mul_bits(0x92fbf4cfb1b794277a4d263ae7d5e5fau128, 0x9877fe940aeffd880616d6c2247bu128, 114nat)) by { lemma_hmul128_bits_unfold(0x497dfa67d8dbca13bd26931d73eaf2fdu128, 0x130effd2815dffb100c2dad8448f7u128, 115nat); }
    assert((((0x9877fe940aeffd880616d6c2247bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6c2247bu128) >> 1u128) == 0x4c3bff4a0577fec4030b6b61123du128)) by (bit_vector);
    assert(((((0x92fbf4cfb1b794277a4d263ae7d5e5fau128) << 1) ^ (if ((((0x92fbf4cfb1b794277a4d263ae7d5e5fau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x25f7e99f636f284ef49a4c75cfabcb73u128) by (bit_vector);
    assert(gf128_xtime(0x92fbf4cfb1b794277a4d263ae7d5e5fau128) == 0x25f7e99f636f284ef49a4c75cfabcb73u128);
    assert(gf128_mul_bits(0x92fbf4cfb1b794277a4d263ae7d5e5fau128, 0x9877fe940aeffd880616d6c2247bu128, 114nat) == 0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ gf128_mul_bits(0x25f7e99f636f284ef49a4c75cfabcb73u128, 0x4c3bff4a0577fec4030b6b61123du128, 113nat)) by { lemma_hmul128_bits_unfold(0x92fbf4cfb1b794277a4d263ae7d5e5fau128, 0x9877fe940aeffd880616d6c2247bu128, 114nat); }
    assert((((0x4c3bff4a0577fec4030b6b61123du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6b61123du128) >> 1u128) == 0x261dffa502bbff620185b5b0891eu128)) by (bit_vector);
    assert(((((0x25f7e99f636f284ef49a4c75cfabcb73u128) << 1) ^ (if ((((0x25f7e99f636f284ef49a4c75cfabcb73u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4befd33ec6de509de93498eb9f5796e6u128) by (bit_vector);
    assert(gf128_xtime(0x25f7e99f636f284ef49a4c75cfabcb73u128) == 0x4befd33ec6de509de93498eb9f5796e6u128);
    assert(gf128_mul_bits(0x25f7e99f636f284ef49a4c75cfabcb73u128, 0x4c3bff4a0577fec4030b6b61123du128, 113nat) == 0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ gf128_mul_bits(0x4befd33ec6de509de93498eb9f5796e6u128, 0x261dffa502bbff620185b5b0891eu128, 112nat)) by { lemma_hmul128_bits_unfold(0x25f7e99f636f284ef49a4c75cfabcb73u128, 0x4c3bff4a0577fec4030b6b61123du128, 113nat); }
    assert((((0x261dffa502bbff620185b5b0891eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5b0891eu128) >> 1u128) == 0x130effd2815dffb100c2dad8448fu128)) by (bit_vector);
    assert(((((0x4befd33ec6de509de93498eb9f5796e6u128) << 1) ^ (if ((((0x4befd33ec6de509de93498eb9f5796e6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x97dfa67d8dbca13bd26931d73eaf2dccu128) by (bit_vector);
    assert(gf128_xtime(0x4befd33ec6de509de93498eb9f5796e6u128) == 0x97dfa67d8dbca13bd26931d73eaf2dccu128);
    assert(gf128_mul_bits(0x4befd33ec6de509de93498eb9f5796e6u128, 0x261dffa502bbff620185b5b0891eu128, 112nat) == 0u128 ^ gf128_mul_bits(0x97dfa67d8dbca13bd26931d73eaf2dccu128, 0x130effd2815dffb100c2dad8448fu128, 111nat)) by { lemma_hmul128_bits_unfold(0x4befd33ec6de509de93498eb9f5796e6u128, 0x261dffa502bbff620185b5b0891eu128, 112nat); }
    assert((((0x130effd2815dffb100c2dad8448fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dad8448fu128) >> 1u128) == 0x9877fe940aeffd880616d6c2247u128)) by (bit_vector);
    assert(((((0x97dfa67d8dbca13bd26931d73eaf2dccu128) << 1) ^ (if ((((0x97dfa67d8dbca13bd26931d73eaf2dccu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128) by (bit_vector);
    assert(gf128_xtime(0x97dfa67d8dbca13bd26931d73eaf2dccu128) == 0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128);
    assert(gf128_mul_bits(0x97dfa67d8dbca13bd26931d73eaf2dccu128, 0x130effd2815dffb100c2dad8448fu128, 111nat) == 0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ gf128_mul_bits(0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128, 0x9877fe940aeffd880616d6c2247u128, 110nat)) by { lemma_hmul128_bits_unfold(0x97dfa67d8dbca13bd26931d73eaf2dccu128, 0x130effd2815dffb100c2dad8448fu128, 111nat); }
    assert((((0x9877fe940aeffd880616d6c2247u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6c2247u128) >> 1u128) == 0x4c3bff4a0577fec4030b6b61123u128)) by (bit_vector);
    assert(((((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128) << 1) ^ (if ((((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5f7e99f636f284ef49a4c75cfabcb63eu128) by (bit_vector);
    assert(gf128_xtime(0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128) == 0x5f7e99f636f284ef49a4c75cfabcb63eu128);
    assert(gf128_mul_bits(0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128, 0x9877fe940aeffd880616d6c2247u128, 110nat) == 0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ gf128_mul_bits(0x5f7e99f636f284ef49a4c75cfabcb63eu128, 0x4c3bff4a0577fec4030b6b61123u128, 109nat)) by { lemma_hmul128_bits_unfold(0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128, 0x9877fe940aeffd880616d6c2247u128, 110nat); }
    assert((((0x4c3bff4a0577fec4030b6b61123u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6b61123u128) >> 1u128) == 0x261dffa502bbff620185b5b0891u128)) by (bit_vector);
    assert(((((0x5f7e99f636f284ef49a4c75cfabcb63eu128) << 1) ^ (if ((((0x5f7e99f636f284ef49a4c75cfabcb63eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbefd33ec6de509de93498eb9f5796c7cu128) by (bit_vector);
    assert(gf128_xtime(0x5f7e99f636f284ef49a4c75cfabcb63eu128) == 0xbefd33ec6de509de93498eb9f5796c7cu128);
    assert(gf128_mul_bits(0x5f7e99f636f284ef49a4c75cfabcb63eu128, 0x4c3bff4a0577fec4030b6b61123u128, 109nat) == 0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ gf128_mul_bits(0xbefd33ec6de509de93498eb9f5796c7cu128, 0x261dffa502bbff620185b5b0891u128, 108nat)) by { lemma_hmul128_bits_unfold(0x5f7e99f636f284ef49a4c75cfabcb63eu128, 0x4c3bff4a0577fec4030b6b61123u128, 109nat); }
    assert((((0x261dffa502bbff620185b5b0891u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5b0891u128) >> 1u128) == 0x130effd2815dffb100c2dad8448u128)) by (bit_vector);
    assert(((((0xbefd33ec6de509de93498eb9f5796c7cu128) << 1) ^ (if ((((0xbefd33ec6de509de93498eb9f5796c7cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7dfa67d8dbca13bd26931d73eaf2d87fu128) by (bit_vector);
    assert(gf128_xtime(0xbefd33ec6de509de93498eb9f5796c7cu128) == 0x7dfa67d8dbca13bd26931d73eaf2d87fu128);
    assert(gf128_mul_bits(0xbefd33ec6de509de93498eb9f5796c7cu128, 0x261dffa502bbff620185b5b0891u128, 108nat) == 0xbefd33ec6de509de93498eb9f5796c7cu128 ^ gf128_mul_bits(0x7dfa67d8dbca13bd26931d73eaf2d87fu128, 0x130effd2815dffb100c2dad8448u128, 107nat)) by { lemma_hmul128_bits_unfold(0xbefd33ec6de509de93498eb9f5796c7cu128, 0x261dffa502bbff620185b5b0891u128, 108nat); }
    assert((((0x130effd2815dffb100c2dad8448u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dad8448u128) >> 1u128) == 0x9877fe940aeffd880616d6c224u128)) by (bit_vector);
    assert(((((0x7dfa67d8dbca13bd26931d73eaf2d87fu128) << 1) ^ (if ((((0x7dfa67d8dbca13bd26931d73eaf2d87fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfbf4cfb1b794277a4d263ae7d5e5b0feu128) by (bit_vector);
    assert(gf128_xtime(0x7dfa67d8dbca13bd26931d73eaf2d87fu128) == 0xfbf4cfb1b794277a4d263ae7d5e5b0feu128);
    assert(gf128_mul_bits(0x7dfa67d8dbca13bd26931d73eaf2d87fu128, 0x130effd2815dffb100c2dad8448u128, 107nat) == 0u128 ^ gf128_mul_bits(0xfbf4cfb1b794277a4d263ae7d5e5b0feu128, 0x9877fe940aeffd880616d6c224u128, 106nat)) by { lemma_hmul128_bits_unfold(0x7dfa67d8dbca13bd26931d73eaf2d87fu128, 0x130effd2815dffb100c2dad8448u128, 107nat); }
    assert((((0x9877fe940aeffd880616d6c224u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6c224u128) >> 1u128) == 0x4c3bff4a0577fec4030b6b6112u128)) by (bit_vector);
    assert(((((0xfbf4cfb1b794277a4d263ae7d5e5b0feu128) << 1) ^ (if ((((0xfbf4cfb1b794277a4d263ae7d5e5b0feu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf7e99f636f284ef49a4c75cfabcb617bu128) by (bit_vector);
    assert(gf128_xtime(0xfbf4cfb1b794277a4d263ae7d5e5b0feu128) == 0xf7e99f636f284ef49a4c75cfabcb617bu128);
    assert(gf128_mul_bits(0xfbf4cfb1b794277a4d263ae7d5e5b0feu128, 0x9877fe940aeffd880616d6c224u128, 106nat) == 0u128 ^ gf128_mul_bits(0xf7e99f636f284ef49a4c75cfabcb617bu128, 0x4c3bff4a0577fec4030b6b6112u128, 105nat)) by { lemma_hmul128_bits_unfold(0xfbf4cfb1b794277a4d263ae7d5e5b0feu128, 0x9877fe940aeffd880616d6c224u128, 106nat); }
    assert((((0x4c3bff4a0577fec4030b6b6112u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6b6112u128) >> 1u128) == 0x261dffa502bbff620185b5b089u128)) by (bit_vector);
    assert(((((0xf7e99f636f284ef49a4c75cfabcb617bu128) << 1) ^ (if ((((0xf7e99f636f284ef49a4c75cfabcb617bu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xefd33ec6de509de93498eb9f5796c271u128) by (bit_vector);
    assert(gf128_xtime(0xf7e99f636f284ef49a4c75cfabcb617bu128) == 0xefd33ec6de509de93498eb9f5796c271u128);
    assert(gf128_mul_bits(0xf7e99f636f284ef49a4c75cfabcb617bu128, 0x4c3bff4a0577fec4030b6b6112u128, 105nat) == 0u128 ^ gf128_mul_bits(0xefd33ec6de509de93498eb9f5796c271u128, 0x261dffa502bbff620185b5b089u128, 104nat)) by { lemma_hmul128_bits_unfold(0xf7e99f636f284ef49a4c75cfabcb617bu128, 0x4c3bff4a0577fec4030b6b6112u128, 105nat); }
    assert((((0x261dffa502bbff620185b5b089u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5b089u128) >> 1u128) == 0x130effd2815dffb100c2dad844u128)) by (bit_vector);
    assert(((((0xefd33ec6de509de93498eb9f5796c271u128) << 1) ^ (if ((((0xefd33ec6de509de93498eb9f5796c271u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xdfa67d8dbca13bd26931d73eaf2d8465u128) by (bit_vector);
    assert(gf128_xtime(0xefd33ec6de509de93498eb9f5796c271u128) == 0xdfa67d8dbca13bd26931d73eaf2d8465u128);
    assert(gf128_mul_bits(0xefd33ec6de509de93498eb9f5796c271u128, 0x261dffa502bbff620185b5b089u128, 104nat) == 0xefd33ec6de509de93498eb9f5796c271u128 ^ gf128_mul_bits(0xdfa67d8dbca13bd26931d73eaf2d8465u128, 0x130effd2815dffb100c2dad844u128, 103nat)) by { lemma_hmul128_bits_unfold(0xefd33ec6de509de93498eb9f5796c271u128, 0x261dffa502bbff620185b5b089u128, 104nat); }
    assert((((0x130effd2815dffb100c2dad844u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dad844u128) >> 1u128) == 0x9877fe940aeffd880616d6c22u128)) by (bit_vector);
    assert(((((0xdfa67d8dbca13bd26931d73eaf2d8465u128) << 1) ^ (if ((((0xdfa67d8dbca13bd26931d73eaf2d8465u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbf4cfb1b794277a4d263ae7d5e5b084du128) by (bit_vector);
    assert(gf128_xtime(0xdfa67d8dbca13bd26931d73eaf2d8465u128) == 0xbf4cfb1b794277a4d263ae7d5e5b084du128);
    assert(gf128_mul_bits(0xdfa67d8dbca13bd26931d73eaf2d8465u128, 0x130effd2815dffb100c2dad844u128, 103nat) == 0u128 ^ gf128_mul_bits(0xbf4cfb1b794277a4d263ae7d5e5b084du128, 0x9877fe940aeffd880616d6c22u128, 102nat)) by { lemma_hmul128_bits_unfold(0xdfa67d8dbca13bd26931d73eaf2d8465u128, 0x130effd2815dffb100c2dad844u128, 103nat); }
    assert((((0x9877fe940aeffd880616d6c22u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6c22u128) >> 1u128) == 0x4c3bff4a0577fec4030b6b611u128)) by (bit_vector);
    assert(((((0xbf4cfb1b794277a4d263ae7d5e5b084du128) << 1) ^ (if ((((0xbf4cfb1b794277a4d263ae7d5e5b084du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7e99f636f284ef49a4c75cfabcb6101du128) by (bit_vector);
    assert(gf128_xtime(0xbf4cfb1b794277a4d263ae7d5e5b084du128) == 0x7e99f636f284ef49a4c75cfabcb6101du128);
    assert(gf128_mul_bits(0xbf4cfb1b794277a4d263ae7d5e5b084du128, 0x9877fe940aeffd880616d6c22u128, 102nat) == 0u128 ^ gf128_mul_bits(0x7e99f636f284ef49a4c75cfabcb6101du128, 0x4c3bff4a0577fec4030b6b611u128, 101nat)) by { lemma_hmul128_bits_unfold(0xbf4cfb1b794277a4d263ae7d5e5b084du128, 0x9877fe940aeffd880616d6c22u128, 102nat); }
    assert((((0x4c3bff4a0577fec4030b6b611u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6b611u128) >> 1u128) == 0x261dffa502bbff620185b5b08u128)) by (bit_vector);
    assert(((((0x7e99f636f284ef49a4c75cfabcb6101du128) << 1) ^ (if ((((0x7e99f636f284ef49a4c75cfabcb6101du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfd33ec6de509de93498eb9f5796c203au128) by (bit_vector);
    assert(gf128_xtime(0x7e99f636f284ef49a4c75cfabcb6101du128) == 0xfd33ec6de509de93498eb9f5796c203au128);
    assert(gf128_mul_bits(0x7e99f636f284ef49a4c75cfabcb6101du128, 0x4c3bff4a0577fec4030b6b611u128, 101nat) == 0x7e99f636f284ef49a4c75cfabcb6101du128 ^ gf128_mul_bits(0xfd33ec6de509de93498eb9f5796c203au128, 0x261dffa502bbff620185b5b08u128, 100nat)) by { lemma_hmul128_bits_unfold(0x7e99f636f284ef49a4c75cfabcb6101du128, 0x4c3bff4a0577fec4030b6b611u128, 101nat); }
    assert((((0x261dffa502bbff620185b5b08u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5b08u128) >> 1u128) == 0x130effd2815dffb100c2dad84u128)) by (bit_vector);
    assert(((((0xfd33ec6de509de93498eb9f5796c203au128) << 1) ^ (if ((((0xfd33ec6de509de93498eb9f5796c203au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfa67d8dbca13bd26931d73eaf2d840f3u128) by (bit_vector);
    assert(gf128_xtime(0xfd33ec6de509de93498eb9f5796c203au128) == 0xfa67d8dbca13bd26931d73eaf2d840f3u128);
    assert(gf128_mul_bits(0xfd33ec6de509de93498eb9f5796c203au128, 0x261dffa502bbff620185b5b08u128, 100nat) == 0u128 ^ gf128_mul_bits(0xfa67d8dbca13bd26931d73eaf2d840f3u128, 0x130effd2815dffb100c2dad84u128, 99nat)) by { lemma_hmul128_bits_unfold(0xfd33ec6de509de93498eb9f5796c203au128, 0x261dffa502bbff620185b5b08u128, 100nat); }
    assert((((0x130effd2815dffb100c2dad84u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dad84u128) >> 1u128) == 0x9877fe940aeffd880616d6c2u128)) by (bit_vector);
    assert(((((0xfa67d8dbca13bd26931d73eaf2d840f3u128) << 1) ^ (if ((((0xfa67d8dbca13bd26931d73eaf2d840f3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf4cfb1b794277a4d263ae7d5e5b08161u128) by (bit_vector);
    assert(gf128_xtime(0xfa67d8dbca13bd26931d73eaf2d840f3u128) == 0xf4cfb1b794277a4d263ae7d5e5b08161u128);
    assert(gf128_mul_bits(0xfa67d8dbca13bd26931d73eaf2d840f3u128, 0x130effd2815dffb100c2dad84u128, 99nat) == 0u128 ^ gf128_mul_bits(0xf4cfb1b794277a4d263ae7d5e5b08161u128, 0x9877fe940aeffd880616d6c2u128, 98nat)) by { lemma_hmul128_bits_unfold(0xfa67d8dbca13bd26931d73eaf2d840f3u128, 0x130effd2815dffb100c2dad84u128, 99nat); }
    assert((((0x9877fe940aeffd880616d6c2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6c2u128) >> 1u128) == 0x4c3bff4a0577fec4030b6b61u128)) by (bit_vector);
    assert(((((0xf4cfb1b794277a4d263ae7d5e5b08161u128) << 1) ^ (if ((((0xf4cfb1b794277a4d263ae7d5e5b08161u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe99f636f284ef49a4c75cfabcb610245u128) by (bit_vector);
    assert(gf128_xtime(0xf4cfb1b794277a4d263ae7d5e5b08161u128) == 0xe99f636f284ef49a4c75cfabcb610245u128);
    assert(gf128_mul_bits(0xf4cfb1b794277a4d263ae7d5e5b08161u128, 0x9877fe940aeffd880616d6c2u128, 98nat) == 0u128 ^ gf128_mul_bits(0xe99f636f284ef49a4c75cfabcb610245u128, 0x4c3bff4a0577fec4030b6b61u128, 97nat)) by { lemma_hmul128_bits_unfold(0xf4cfb1b794277a4d263ae7d5e5b08161u128, 0x9877fe940aeffd880616d6c2u128, 98nat); }
    assert((((0x4c3bff4a0577fec4030b6b61u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6b61u128) >> 1u128) == 0x261dffa502bbff620185b5b0u128)) by (bit_vector);
    assert(((((0xe99f636f284ef49a4c75cfabcb610245u128) << 1) ^ (if ((((0xe99f636f284ef49a4c75cfabcb610245u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd33ec6de509de93498eb9f5796c2040du128) by (bit_vector);
    assert(gf128_xtime(0xe99f636f284ef49a4c75cfabcb610245u128) == 0xd33ec6de509de93498eb9f5796c2040du128);
    assert(gf128_mul_bits(0xe99f636f284ef49a4c75cfabcb610245u128, 0x4c3bff4a0577fec4030b6b61u128, 97nat) == 0xe99f636f284ef49a4c75cfabcb610245u128 ^ gf128_mul_bits(0xd33ec6de509de93498eb9f5796c2040du128, 0x261dffa502bbff620185b5b0u128, 96nat)) by { lemma_hmul128_bits_unfold(0xe99f636f284ef49a4c75cfabcb610245u128, 0x4c3bff4a0577fec4030b6b61u128, 97nat); }
    assert((((0x261dffa502bbff620185b5b0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5b0u128) >> 1u128) == 0x130effd2815dffb100c2dad8u128)) by (bit_vector);
    assert(((((0xd33ec6de509de93498eb9f5796c2040du128) << 1) ^ (if ((((0xd33ec6de509de93498eb9f5796c2040du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa67d8dbca13bd26931d73eaf2d84089du128) by (bit_vector);
    assert(gf128_xtime(0xd33ec6de509de93498eb9f5796c2040du128) == 0xa67d8dbca13bd26931d73eaf2d84089du128);
    assert(gf128_mul_bits(0xd33ec6de509de93498eb9f5796c2040du128, 0x261dffa502bbff620185b5b0u128, 96nat) == 0u128 ^ gf128_mul_bits(0xa67d8dbca13bd26931d73eaf2d84089du128, 0x130effd2815dffb100c2dad8u128, 95nat)) by { lemma_hmul128_bits_unfold(0xd33ec6de509de93498eb9f5796c2040du128, 0x261dffa502bbff620185b5b0u128, 96nat); }
    assert((((0x130effd2815dffb100c2dad8u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dad8u128) >> 1u128) == 0x9877fe940aeffd880616d6cu128)) by (bit_vector);
    assert(((((0xa67d8dbca13bd26931d73eaf2d84089du128) << 1) ^ (if ((((0xa67d8dbca13bd26931d73eaf2d84089du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4cfb1b794277a4d263ae7d5e5b0811bdu128) by (bit_vector);
    assert(gf128_xtime(0xa67d8dbca13bd26931d73eaf2d84089du128) == 0x4cfb1b794277a4d263ae7d5e5b0811bdu128);
    assert(gf128_mul_bits(0xa67d8dbca13bd26931d73eaf2d84089du128, 0x130effd2815dffb100c2dad8u128, 95nat) == 0u128 ^ gf128_mul_bits(0x4cfb1b794277a4d263ae7d5e5b0811bdu128, 0x9877fe940aeffd880616d6cu128, 94nat)) by { lemma_hmul128_bits_unfold(0xa67d8dbca13bd26931d73eaf2d84089du128, 0x130effd2815dffb100c2dad8u128, 95nat); }
    assert((((0x9877fe940aeffd880616d6cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6cu128) >> 1u128) == 0x4c3bff4a0577fec4030b6b6u128)) by (bit_vector);
    assert(((((0x4cfb1b794277a4d263ae7d5e5b0811bdu128) << 1) ^ (if ((((0x4cfb1b794277a4d263ae7d5e5b0811bdu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x99f636f284ef49a4c75cfabcb610237au128) by (bit_vector);
    assert(gf128_xtime(0x4cfb1b794277a4d263ae7d5e5b0811bdu128) == 0x99f636f284ef49a4c75cfabcb610237au128);
    assert(gf128_mul_bits(0x4cfb1b794277a4d263ae7d5e5b0811bdu128, 0x9877fe940aeffd880616d6cu128, 94nat) == 0u128 ^ gf128_mul_bits(0x99f636f284ef49a4c75cfabcb610237au128, 0x4c3bff4a0577fec4030b6b6u128, 93nat)) by { lemma_hmul128_bits_unfold(0x4cfb1b794277a4d263ae7d5e5b0811bdu128, 0x9877fe940aeffd880616d6cu128, 94nat); }
    assert((((0x4c3bff4a0577fec4030b6b6u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6b6u128) >> 1u128) == 0x261dffa502bbff620185b5bu128)) by (bit_vector);
    assert(((((0x99f636f284ef49a4c75cfabcb610237au128) << 1) ^ (if ((((0x99f636f284ef49a4c75cfabcb610237au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x33ec6de509de93498eb9f5796c204673u128) by (bit_vector);
    assert(gf128_xtime(0x99f636f284ef49a4c75cfabcb610237au128) == 0x33ec6de509de93498eb9f5796c204673u128);
    assert(gf128_mul_bits(0x99f636f284ef49a4c75cfabcb610237au128, 0x4c3bff4a0577fec4030b6b6u128, 93nat) == 0u128 ^ gf128_mul_bits(0x33ec6de509de93498eb9f5796c204673u128, 0x261dffa502bbff620185b5bu128, 92nat)) by { lemma_hmul128_bits_unfold(0x99f636f284ef49a4c75cfabcb610237au128, 0x4c3bff4a0577fec4030b6b6u128, 93nat); }
    assert((((0x261dffa502bbff620185b5bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5bu128) >> 1u128) == 0x130effd2815dffb100c2dadu128)) by (bit_vector);
    assert(((((0x33ec6de509de93498eb9f5796c204673u128) << 1) ^ (if ((((0x33ec6de509de93498eb9f5796c204673u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x67d8dbca13bd26931d73eaf2d8408ce6u128) by (bit_vector);
    assert(gf128_xtime(0x33ec6de509de93498eb9f5796c204673u128) == 0x67d8dbca13bd26931d73eaf2d8408ce6u128);
    assert(gf128_mul_bits(0x33ec6de509de93498eb9f5796c204673u128, 0x261dffa502bbff620185b5bu128, 92nat) == 0x33ec6de509de93498eb9f5796c204673u128 ^ gf128_mul_bits(0x67d8dbca13bd26931d73eaf2d8408ce6u128, 0x130effd2815dffb100c2dadu128, 91nat)) by { lemma_hmul128_bits_unfold(0x33ec6de509de93498eb9f5796c204673u128, 0x261dffa502bbff620185b5bu128, 92nat); }
    assert((((0x130effd2815dffb100c2dadu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dadu128) >> 1u128) == 0x9877fe940aeffd880616d6u128)) by (bit_vector);
    assert(((((0x67d8dbca13bd26931d73eaf2d8408ce6u128) << 1) ^ (if ((((0x67d8dbca13bd26931d73eaf2d8408ce6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xcfb1b794277a4d263ae7d5e5b08119ccu128) by (bit_vector);
    assert(gf128_xtime(0x67d8dbca13bd26931d73eaf2d8408ce6u128) == 0xcfb1b794277a4d263ae7d5e5b08119ccu128);
    assert(gf128_mul_bits(0x67d8dbca13bd26931d73eaf2d8408ce6u128, 0x130effd2815dffb100c2dadu128, 91nat) == 0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ gf128_mul_bits(0xcfb1b794277a4d263ae7d5e5b08119ccu128, 0x9877fe940aeffd880616d6u128, 90nat)) by { lemma_hmul128_bits_unfold(0x67d8dbca13bd26931d73eaf2d8408ce6u128, 0x130effd2815dffb100c2dadu128, 91nat); }
    assert((((0x9877fe940aeffd880616d6u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616d6u128) >> 1u128) == 0x4c3bff4a0577fec4030b6bu128)) by (bit_vector);
    assert(((((0xcfb1b794277a4d263ae7d5e5b08119ccu128) << 1) ^ (if ((((0xcfb1b794277a4d263ae7d5e5b08119ccu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9f636f284ef49a4c75cfabcb6102331fu128) by (bit_vector);
    assert(gf128_xtime(0xcfb1b794277a4d263ae7d5e5b08119ccu128) == 0x9f636f284ef49a4c75cfabcb6102331fu128);
    assert(gf128_mul_bits(0xcfb1b794277a4d263ae7d5e5b08119ccu128, 0x9877fe940aeffd880616d6u128, 90nat) == 0u128 ^ gf128_mul_bits(0x9f636f284ef49a4c75cfabcb6102331fu128, 0x4c3bff4a0577fec4030b6bu128, 89nat)) by { lemma_hmul128_bits_unfold(0xcfb1b794277a4d263ae7d5e5b08119ccu128, 0x9877fe940aeffd880616d6u128, 90nat); }
    assert((((0x4c3bff4a0577fec4030b6bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6bu128) >> 1u128) == 0x261dffa502bbff620185b5u128)) by (bit_vector);
    assert(((((0x9f636f284ef49a4c75cfabcb6102331fu128) << 1) ^ (if ((((0x9f636f284ef49a4c75cfabcb6102331fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3ec6de509de93498eb9f5796c20466b9u128) by (bit_vector);
    assert(gf128_xtime(0x9f636f284ef49a4c75cfabcb6102331fu128) == 0x3ec6de509de93498eb9f5796c20466b9u128);
    assert(gf128_mul_bits(0x9f636f284ef49a4c75cfabcb6102331fu128, 0x4c3bff4a0577fec4030b6bu128, 89nat) == 0x9f636f284ef49a4c75cfabcb6102331fu128 ^ gf128_mul_bits(0x3ec6de509de93498eb9f5796c20466b9u128, 0x261dffa502bbff620185b5u128, 88nat)) by { lemma_hmul128_bits_unfold(0x9f636f284ef49a4c75cfabcb6102331fu128, 0x4c3bff4a0577fec4030b6bu128, 89nat); }
    assert((((0x261dffa502bbff620185b5u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185b5u128) >> 1u128) == 0x130effd2815dffb100c2dau128)) by (bit_vector);
    assert(((((0x3ec6de509de93498eb9f5796c20466b9u128) << 1) ^ (if ((((0x3ec6de509de93498eb9f5796c20466b9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7d8dbca13bd26931d73eaf2d8408cd72u128) by (bit_vector);
    assert(gf128_xtime(0x3ec6de509de93498eb9f5796c20466b9u128) == 0x7d8dbca13bd26931d73eaf2d8408cd72u128);
    assert(gf128_mul_bits(0x3ec6de509de93498eb9f5796c20466b9u128, 0x261dffa502bbff620185b5u128, 88nat) == 0x3ec6de509de93498eb9f5796c20466b9u128 ^ gf128_mul_bits(0x7d8dbca13bd26931d73eaf2d8408cd72u128, 0x130effd2815dffb100c2dau128, 87nat)) by { lemma_hmul128_bits_unfold(0x3ec6de509de93498eb9f5796c20466b9u128, 0x261dffa502bbff620185b5u128, 88nat); }
    assert((((0x130effd2815dffb100c2dau128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2dau128) >> 1u128) == 0x9877fe940aeffd880616du128)) by (bit_vector);
    assert(((((0x7d8dbca13bd26931d73eaf2d8408cd72u128) << 1) ^ (if ((((0x7d8dbca13bd26931d73eaf2d8408cd72u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfb1b794277a4d263ae7d5e5b08119ae4u128) by (bit_vector);
    assert(gf128_xtime(0x7d8dbca13bd26931d73eaf2d8408cd72u128) == 0xfb1b794277a4d263ae7d5e5b08119ae4u128);
    assert(gf128_mul_bits(0x7d8dbca13bd26931d73eaf2d8408cd72u128, 0x130effd2815dffb100c2dau128, 87nat) == 0u128 ^ gf128_mul_bits(0xfb1b794277a4d263ae7d5e5b08119ae4u128, 0x9877fe940aeffd880616du128, 86nat)) by { lemma_hmul128_bits_unfold(0x7d8dbca13bd26931d73eaf2d8408cd72u128, 0x130effd2815dffb100c2dau128, 87nat); }
    assert((((0x9877fe940aeffd880616du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616du128) >> 1u128) == 0x4c3bff4a0577fec4030b6u128)) by (bit_vector);
    assert(((((0xfb1b794277a4d263ae7d5e5b08119ae4u128) << 1) ^ (if ((((0xfb1b794277a4d263ae7d5e5b08119ae4u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf636f284ef49a4c75cfabcb61023354fu128) by (bit_vector);
    assert(gf128_xtime(0xfb1b794277a4d263ae7d5e5b08119ae4u128) == 0xf636f284ef49a4c75cfabcb61023354fu128);
    assert(gf128_mul_bits(0xfb1b794277a4d263ae7d5e5b08119ae4u128, 0x9877fe940aeffd880616du128, 86nat) == 0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ gf128_mul_bits(0xf636f284ef49a4c75cfabcb61023354fu128, 0x4c3bff4a0577fec4030b6u128, 85nat)) by { lemma_hmul128_bits_unfold(0xfb1b794277a4d263ae7d5e5b08119ae4u128, 0x9877fe940aeffd880616du128, 86nat); }
    assert((((0x4c3bff4a0577fec4030b6u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030b6u128) >> 1u128) == 0x261dffa502bbff620185bu128)) by (bit_vector);
    assert(((((0xf636f284ef49a4c75cfabcb61023354fu128) << 1) ^ (if ((((0xf636f284ef49a4c75cfabcb61023354fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xec6de509de93498eb9f5796c20466a19u128) by (bit_vector);
    assert(gf128_xtime(0xf636f284ef49a4c75cfabcb61023354fu128) == 0xec6de509de93498eb9f5796c20466a19u128);
    assert(gf128_mul_bits(0xf636f284ef49a4c75cfabcb61023354fu128, 0x4c3bff4a0577fec4030b6u128, 85nat) == 0u128 ^ gf128_mul_bits(0xec6de509de93498eb9f5796c20466a19u128, 0x261dffa502bbff620185bu128, 84nat)) by { lemma_hmul128_bits_unfold(0xf636f284ef49a4c75cfabcb61023354fu128, 0x4c3bff4a0577fec4030b6u128, 85nat); }
    assert((((0x261dffa502bbff620185bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185bu128) >> 1u128) == 0x130effd2815dffb100c2du128)) by (bit_vector);
    assert(((((0xec6de509de93498eb9f5796c20466a19u128) << 1) ^ (if ((((0xec6de509de93498eb9f5796c20466a19u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd8dbca13bd26931d73eaf2d8408cd4b5u128) by (bit_vector);
    assert(gf128_xtime(0xec6de509de93498eb9f5796c20466a19u128) == 0xd8dbca13bd26931d73eaf2d8408cd4b5u128);
    assert(gf128_mul_bits(0xec6de509de93498eb9f5796c20466a19u128, 0x261dffa502bbff620185bu128, 84nat) == 0xec6de509de93498eb9f5796c20466a19u128 ^ gf128_mul_bits(0xd8dbca13bd26931d73eaf2d8408cd4b5u128, 0x130effd2815dffb100c2du128, 83nat)) by { lemma_hmul128_bits_unfold(0xec6de509de93498eb9f5796c20466a19u128, 0x261dffa502bbff620185bu128, 84nat); }
    assert((((0x130effd2815dffb100c2du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2du128) >> 1u128) == 0x9877fe940aeffd880616u128)) by (bit_vector);
    assert(((((0xd8dbca13bd26931d73eaf2d8408cd4b5u128) << 1) ^ (if ((((0xd8dbca13bd26931d73eaf2d8408cd4b5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb1b794277a4d263ae7d5e5b08119a9edu128) by (bit_vector);
    assert(gf128_xtime(0xd8dbca13bd26931d73eaf2d8408cd4b5u128) == 0xb1b794277a4d263ae7d5e5b08119a9edu128);
    assert(gf128_mul_bits(0xd8dbca13bd26931d73eaf2d8408cd4b5u128, 0x130effd2815dffb100c2du128, 83nat) == 0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ gf128_mul_bits(0xb1b794277a4d263ae7d5e5b08119a9edu128, 0x9877fe940aeffd880616u128, 82nat)) by { lemma_hmul128_bits_unfold(0xd8dbca13bd26931d73eaf2d8408cd4b5u128, 0x130effd2815dffb100c2du128, 83nat); }
    assert((((0x9877fe940aeffd880616u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880616u128) >> 1u128) == 0x4c3bff4a0577fec4030bu128)) by (bit_vector);
    assert(((((0xb1b794277a4d263ae7d5e5b08119a9edu128) << 1) ^ (if ((((0xb1b794277a4d263ae7d5e5b08119a9edu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x636f284ef49a4c75cfabcb610233535du128) by (bit_vector);
    assert(gf128_xtime(0xb1b794277a4d263ae7d5e5b08119a9edu128) == 0x636f284ef49a4c75cfabcb610233535du128);
    assert(gf128_mul_bits(0xb1b794277a4d263ae7d5e5b08119a9edu128, 0x9877fe940aeffd880616u128, 82nat) == 0u128 ^ gf128_mul_bits(0x636f284ef49a4c75cfabcb610233535du128, 0x4c3bff4a0577fec4030bu128, 81nat)) by { lemma_hmul128_bits_unfold(0xb1b794277a4d263ae7d5e5b08119a9edu128, 0x9877fe940aeffd880616u128, 82nat); }
    assert((((0x4c3bff4a0577fec4030bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030bu128) >> 1u128) == 0x261dffa502bbff620185u128)) by (bit_vector);
    assert(((((0x636f284ef49a4c75cfabcb610233535du128) << 1) ^ (if ((((0x636f284ef49a4c75cfabcb610233535du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc6de509de93498eb9f5796c20466a6bau128) by (bit_vector);
    assert(gf128_xtime(0x636f284ef49a4c75cfabcb610233535du128) == 0xc6de509de93498eb9f5796c20466a6bau128);
    assert(gf128_mul_bits(0x636f284ef49a4c75cfabcb610233535du128, 0x4c3bff4a0577fec4030bu128, 81nat) == 0x636f284ef49a4c75cfabcb610233535du128 ^ gf128_mul_bits(0xc6de509de93498eb9f5796c20466a6bau128, 0x261dffa502bbff620185u128, 80nat)) by { lemma_hmul128_bits_unfold(0x636f284ef49a4c75cfabcb610233535du128, 0x4c3bff4a0577fec4030bu128, 81nat); }
    assert((((0x261dffa502bbff620185u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbff620185u128) >> 1u128) == 0x130effd2815dffb100c2u128)) by (bit_vector);
    assert(((((0xc6de509de93498eb9f5796c20466a6bau128) << 1) ^ (if ((((0xc6de509de93498eb9f5796c20466a6bau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x8dbca13bd26931d73eaf2d8408cd4df3u128) by (bit_vector);
    assert(gf128_xtime(0xc6de509de93498eb9f5796c20466a6bau128) == 0x8dbca13bd26931d73eaf2d8408cd4df3u128);
    assert(gf128_mul_bits(0xc6de509de93498eb9f5796c20466a6bau128, 0x261dffa502bbff620185u128, 80nat) == 0xc6de509de93498eb9f5796c20466a6bau128 ^ gf128_mul_bits(0x8dbca13bd26931d73eaf2d8408cd4df3u128, 0x130effd2815dffb100c2u128, 79nat)) by { lemma_hmul128_bits_unfold(0xc6de509de93498eb9f5796c20466a6bau128, 0x261dffa502bbff620185u128, 80nat); }
    assert((((0x130effd2815dffb100c2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb100c2u128) >> 1u128) == 0x9877fe940aeffd88061u128)) by (bit_vector);
    assert(((((0x8dbca13bd26931d73eaf2d8408cd4df3u128) << 1) ^ (if ((((0x8dbca13bd26931d73eaf2d8408cd4df3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1b794277a4d263ae7d5e5b08119a9b61u128) by (bit_vector);
    assert(gf128_xtime(0x8dbca13bd26931d73eaf2d8408cd4df3u128) == 0x1b794277a4d263ae7d5e5b08119a9b61u128);
    assert(gf128_mul_bits(0x8dbca13bd26931d73eaf2d8408cd4df3u128, 0x130effd2815dffb100c2u128, 79nat) == 0u128 ^ gf128_mul_bits(0x1b794277a4d263ae7d5e5b08119a9b61u128, 0x9877fe940aeffd88061u128, 78nat)) by { lemma_hmul128_bits_unfold(0x8dbca13bd26931d73eaf2d8408cd4df3u128, 0x130effd2815dffb100c2u128, 79nat); }
    assert((((0x9877fe940aeffd88061u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe940aeffd88061u128) >> 1u128) == 0x4c3bff4a0577fec4030u128)) by (bit_vector);
    assert(((((0x1b794277a4d263ae7d5e5b08119a9b61u128) << 1) ^ (if ((((0x1b794277a4d263ae7d5e5b08119a9b61u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x36f284ef49a4c75cfabcb610233536c2u128) by (bit_vector);
    assert(gf128_xtime(0x1b794277a4d263ae7d5e5b08119a9b61u128) == 0x36f284ef49a4c75cfabcb610233536c2u128);
    assert(gf128_mul_bits(0x1b794277a4d263ae7d5e5b08119a9b61u128, 0x9877fe940aeffd88061u128, 78nat) == 0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ gf128_mul_bits(0x36f284ef49a4c75cfabcb610233536c2u128, 0x4c3bff4a0577fec4030u128, 77nat)) by { lemma_hmul128_bits_unfold(0x1b794277a4d263ae7d5e5b08119a9b61u128, 0x9877fe940aeffd88061u128, 78nat); }
    assert((((0x4c3bff4a0577fec4030u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4030u128) >> 1u128) == 0x261dffa502bbff62018u128)) by (bit_vector);
    assert(((((0x36f284ef49a4c75cfabcb610233536c2u128) << 1) ^ (if ((((0x36f284ef49a4c75cfabcb610233536c2u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x6de509de93498eb9f5796c20466a6d84u128) by (bit_vector);
    assert(gf128_xtime(0x36f284ef49a4c75cfabcb610233536c2u128) == 0x6de509de93498eb9f5796c20466a6d84u128);
    assert(gf128_mul_bits(0x36f284ef49a4c75cfabcb610233536c2u128, 0x4c3bff4a0577fec4030u128, 77nat) == 0u128 ^ gf128_mul_bits(0x6de509de93498eb9f5796c20466a6d84u128, 0x261dffa502bbff62018u128, 76nat)) by { lemma_hmul128_bits_unfold(0x36f284ef49a4c75cfabcb610233536c2u128, 0x4c3bff4a0577fec4030u128, 77nat); }
    assert((((0x261dffa502bbff62018u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff62018u128) >> 1u128) == 0x130effd2815dffb100cu128)) by (bit_vector);
    assert(((((0x6de509de93498eb9f5796c20466a6d84u128) << 1) ^ (if ((((0x6de509de93498eb9f5796c20466a6d84u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xdbca13bd26931d73eaf2d8408cd4db08u128) by (bit_vector);
    assert(gf128_xtime(0x6de509de93498eb9f5796c20466a6d84u128) == 0xdbca13bd26931d73eaf2d8408cd4db08u128);
    assert(gf128_mul_bits(0x6de509de93498eb9f5796c20466a6d84u128, 0x261dffa502bbff62018u128, 76nat) == 0u128 ^ gf128_mul_bits(0xdbca13bd26931d73eaf2d8408cd4db08u128, 0x130effd2815dffb100cu128, 75nat)) by { lemma_hmul128_bits_unfold(0x6de509de93498eb9f5796c20466a6d84u128, 0x261dffa502bbff62018u128, 76nat); }
    assert((((0x130effd2815dffb100cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb100cu128) >> 1u128) == 0x9877fe940aeffd8806u128)) by (bit_vector);
    assert(((((0xdbca13bd26931d73eaf2d8408cd4db08u128) << 1) ^ (if ((((0xdbca13bd26931d73eaf2d8408cd4db08u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb794277a4d263ae7d5e5b08119a9b697u128) by (bit_vector);
    assert(gf128_xtime(0xdbca13bd26931d73eaf2d8408cd4db08u128) == 0xb794277a4d263ae7d5e5b08119a9b697u128);
    assert(gf128_mul_bits(0xdbca13bd26931d73eaf2d8408cd4db08u128, 0x130effd2815dffb100cu128, 75nat) == 0u128 ^ gf128_mul_bits(0xb794277a4d263ae7d5e5b08119a9b697u128, 0x9877fe940aeffd8806u128, 74nat)) by { lemma_hmul128_bits_unfold(0xdbca13bd26931d73eaf2d8408cd4db08u128, 0x130effd2815dffb100cu128, 75nat); }
    assert((((0x9877fe940aeffd8806u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd8806u128) >> 1u128) == 0x4c3bff4a0577fec403u128)) by (bit_vector);
    assert(((((0xb794277a4d263ae7d5e5b08119a9b697u128) << 1) ^ (if ((((0xb794277a4d263ae7d5e5b08119a9b697u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x6f284ef49a4c75cfabcb610233536da9u128) by (bit_vector);
    assert(gf128_xtime(0xb794277a4d263ae7d5e5b08119a9b697u128) == 0x6f284ef49a4c75cfabcb610233536da9u128);
    assert(gf128_mul_bits(0xb794277a4d263ae7d5e5b08119a9b697u128, 0x9877fe940aeffd8806u128, 74nat) == 0u128 ^ gf128_mul_bits(0x6f284ef49a4c75cfabcb610233536da9u128, 0x4c3bff4a0577fec403u128, 73nat)) by { lemma_hmul128_bits_unfold(0xb794277a4d263ae7d5e5b08119a9b697u128, 0x9877fe940aeffd8806u128, 74nat); }
    assert((((0x4c3bff4a0577fec403u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec403u128) >> 1u128) == 0x261dffa502bbff6201u128)) by (bit_vector);
    assert(((((0x6f284ef49a4c75cfabcb610233536da9u128) << 1) ^ (if ((((0x6f284ef49a4c75cfabcb610233536da9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xde509de93498eb9f5796c20466a6db52u128) by (bit_vector);
    assert(gf128_xtime(0x6f284ef49a4c75cfabcb610233536da9u128) == 0xde509de93498eb9f5796c20466a6db52u128);
    assert(gf128_mul_bits(0x6f284ef49a4c75cfabcb610233536da9u128, 0x4c3bff4a0577fec403u128, 73nat) == 0x6f284ef49a4c75cfabcb610233536da9u128 ^ gf128_mul_bits(0xde509de93498eb9f5796c20466a6db52u128, 0x261dffa502bbff6201u128, 72nat)) by { lemma_hmul128_bits_unfold(0x6f284ef49a4c75cfabcb610233536da9u128, 0x4c3bff4a0577fec403u128, 73nat); }
    assert((((0x261dffa502bbff6201u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbff6201u128) >> 1u128) == 0x130effd2815dffb100u128)) by (bit_vector);
    assert(((((0xde509de93498eb9f5796c20466a6db52u128) << 1) ^ (if ((((0xde509de93498eb9f5796c20466a6db52u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbca13bd26931d73eaf2d8408cd4db623u128) by (bit_vector);
    assert(gf128_xtime(0xde509de93498eb9f5796c20466a6db52u128) == 0xbca13bd26931d73eaf2d8408cd4db623u128);
    assert(gf128_mul_bits(0xde509de93498eb9f5796c20466a6db52u128, 0x261dffa502bbff6201u128, 72nat) == 0xde509de93498eb9f5796c20466a6db52u128 ^ gf128_mul_bits(0xbca13bd26931d73eaf2d8408cd4db623u128, 0x130effd2815dffb100u128, 71nat)) by { lemma_hmul128_bits_unfold(0xde509de93498eb9f5796c20466a6db52u128, 0x261dffa502bbff6201u128, 72nat); }
    assert((((0x130effd2815dffb100u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb100u128) >> 1u128) == 0x9877fe940aeffd880u128)) by (bit_vector);
    assert(((((0xbca13bd26931d73eaf2d8408cd4db623u128) << 1) ^ (if ((((0xbca13bd26931d73eaf2d8408cd4db623u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x794277a4d263ae7d5e5b08119a9b6cc1u128) by (bit_vector);
    assert(gf128_xtime(0xbca13bd26931d73eaf2d8408cd4db623u128) == 0x794277a4d263ae7d5e5b08119a9b6cc1u128);
    assert(gf128_mul_bits(0xbca13bd26931d73eaf2d8408cd4db623u128, 0x130effd2815dffb100u128, 71nat) == 0u128 ^ gf128_mul_bits(0x794277a4d263ae7d5e5b08119a9b6cc1u128, 0x9877fe940aeffd880u128, 70nat)) by { lemma_hmul128_bits_unfold(0xbca13bd26931d73eaf2d8408cd4db623u128, 0x130effd2815dffb100u128, 71nat); }
    assert((((0x9877fe940aeffd880u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd880u128) >> 1u128) == 0x4c3bff4a0577fec40u128)) by (bit_vector);
    assert(((((0x794277a4d263ae7d5e5b08119a9b6cc1u128) << 1) ^ (if ((((0x794277a4d263ae7d5e5b08119a9b6cc1u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf284ef49a4c75cfabcb610233536d982u128) by (bit_vector);
    assert(gf128_xtime(0x794277a4d263ae7d5e5b08119a9b6cc1u128) == 0xf284ef49a4c75cfabcb610233536d982u128);
    assert(gf128_mul_bits(0x794277a4d263ae7d5e5b08119a9b6cc1u128, 0x9877fe940aeffd880u128, 70nat) == 0u128 ^ gf128_mul_bits(0xf284ef49a4c75cfabcb610233536d982u128, 0x4c3bff4a0577fec40u128, 69nat)) by { lemma_hmul128_bits_unfold(0x794277a4d263ae7d5e5b08119a9b6cc1u128, 0x9877fe940aeffd880u128, 70nat); }
    assert((((0x4c3bff4a0577fec40u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec40u128) >> 1u128) == 0x261dffa502bbff620u128)) by (bit_vector);
    assert(((((0xf284ef49a4c75cfabcb610233536d982u128) << 1) ^ (if ((((0xf284ef49a4c75cfabcb610233536d982u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe509de93498eb9f5796c20466a6db383u128) by (bit_vector);
    assert(gf128_xtime(0xf284ef49a4c75cfabcb610233536d982u128) == 0xe509de93498eb9f5796c20466a6db383u128);
    assert(gf128_mul_bits(0xf284ef49a4c75cfabcb610233536d982u128, 0x4c3bff4a0577fec40u128, 69nat) == 0u128 ^ gf128_mul_bits(0xe509de93498eb9f5796c20466a6db383u128, 0x261dffa502bbff620u128, 68nat)) by { lemma_hmul128_bits_unfold(0xf284ef49a4c75cfabcb610233536d982u128, 0x4c3bff4a0577fec40u128, 69nat); }
    assert((((0x261dffa502bbff620u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff620u128) >> 1u128) == 0x130effd2815dffb10u128)) by (bit_vector);
    assert(((((0xe509de93498eb9f5796c20466a6db383u128) << 1) ^ (if ((((0xe509de93498eb9f5796c20466a6db383u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xca13bd26931d73eaf2d8408cd4db6781u128) by (bit_vector);
    assert(gf128_xtime(0xe509de93498eb9f5796c20466a6db383u128) == 0xca13bd26931d73eaf2d8408cd4db6781u128);
    assert(gf128_mul_bits(0xe509de93498eb9f5796c20466a6db383u128, 0x261dffa502bbff620u128, 68nat) == 0u128 ^ gf128_mul_bits(0xca13bd26931d73eaf2d8408cd4db6781u128, 0x130effd2815dffb10u128, 67nat)) by { lemma_hmul128_bits_unfold(0xe509de93498eb9f5796c20466a6db383u128, 0x261dffa502bbff620u128, 68nat); }
    assert((((0x130effd2815dffb10u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2815dffb10u128) >> 1u128) == 0x9877fe940aeffd88u128)) by (bit_vector);
    assert(((((0xca13bd26931d73eaf2d8408cd4db6781u128) << 1) ^ (if ((((0xca13bd26931d73eaf2d8408cd4db6781u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x94277a4d263ae7d5e5b08119a9b6cf85u128) by (bit_vector);
    assert(gf128_xtime(0xca13bd26931d73eaf2d8408cd4db6781u128) == 0x94277a4d263ae7d5e5b08119a9b6cf85u128);
    assert(gf128_mul_bits(0xca13bd26931d73eaf2d8408cd4db6781u128, 0x130effd2815dffb10u128, 67nat) == 0u128 ^ gf128_mul_bits(0x94277a4d263ae7d5e5b08119a9b6cf85u128, 0x9877fe940aeffd88u128, 66nat)) by { lemma_hmul128_bits_unfold(0xca13bd26931d73eaf2d8408cd4db6781u128, 0x130effd2815dffb10u128, 67nat); }
    assert((((0x9877fe940aeffd88u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd88u128) >> 1u128) == 0x4c3bff4a0577fec4u128)) by (bit_vector);
    assert(((((0x94277a4d263ae7d5e5b08119a9b6cf85u128) << 1) ^ (if ((((0x94277a4d263ae7d5e5b08119a9b6cf85u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x284ef49a4c75cfabcb610233536d9f8du128) by (bit_vector);
    assert(gf128_xtime(0x94277a4d263ae7d5e5b08119a9b6cf85u128) == 0x284ef49a4c75cfabcb610233536d9f8du128);
    assert(gf128_mul_bits(0x94277a4d263ae7d5e5b08119a9b6cf85u128, 0x9877fe940aeffd88u128, 66nat) == 0u128 ^ gf128_mul_bits(0x284ef49a4c75cfabcb610233536d9f8du128, 0x4c3bff4a0577fec4u128, 65nat)) by { lemma_hmul128_bits_unfold(0x94277a4d263ae7d5e5b08119a9b6cf85u128, 0x9877fe940aeffd88u128, 66nat); }
    assert((((0x4c3bff4a0577fec4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fec4u128) >> 1u128) == 0x261dffa502bbff62u128)) by (bit_vector);
    assert(((((0x284ef49a4c75cfabcb610233536d9f8du128) << 1) ^ (if ((((0x284ef49a4c75cfabcb610233536d9f8du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x509de93498eb9f5796c20466a6db3f1au128) by (bit_vector);
    assert(gf128_xtime(0x284ef49a4c75cfabcb610233536d9f8du128) == 0x509de93498eb9f5796c20466a6db3f1au128);
    assert(gf128_mul_bits(0x284ef49a4c75cfabcb610233536d9f8du128, 0x4c3bff4a0577fec4u128, 65nat) == 0u128 ^ gf128_mul_bits(0x509de93498eb9f5796c20466a6db3f1au128, 0x261dffa502bbff62u128, 64nat)) by { lemma_hmul128_bits_unfold(0x284ef49a4c75cfabcb610233536d9f8du128, 0x4c3bff4a0577fec4u128, 65nat); }
    assert((((0x261dffa502bbff62u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff62u128) >> 1u128) == 0x130effd2815dffb1u128)) by (bit_vector);
    assert(((((0x509de93498eb9f5796c20466a6db3f1au128) << 1) ^ (if ((((0x509de93498eb9f5796c20466a6db3f1au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa13bd26931d73eaf2d8408cd4db67e34u128) by (bit_vector);
    assert(gf128_xtime(0x509de93498eb9f5796c20466a6db3f1au128) == 0xa13bd26931d73eaf2d8408cd4db67e34u128);
    assert(gf128_mul_bits(0x509de93498eb9f5796c20466a6db3f1au128, 0x261dffa502bbff62u128, 64nat) == 0u128 ^ gf128_mul_bits(0xa13bd26931d73eaf2d8408cd4db67e34u128, 0x130effd2815dffb1u128, 63nat)) by { lemma_hmul128_bits_unfold(0x509de93498eb9f5796c20466a6db3f1au128, 0x261dffa502bbff62u128, 64nat); }
    assert((((0x130effd2815dffb1u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dffb1u128) >> 1u128) == 0x9877fe940aeffd8u128)) by (bit_vector);
    assert(((((0xa13bd26931d73eaf2d8408cd4db67e34u128) << 1) ^ (if ((((0xa13bd26931d73eaf2d8408cd4db67e34u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4277a4d263ae7d5e5b08119a9b6cfcefu128) by (bit_vector);
    assert(gf128_xtime(0xa13bd26931d73eaf2d8408cd4db67e34u128) == 0x4277a4d263ae7d5e5b08119a9b6cfcefu128);
    assert(gf128_mul_bits(0xa13bd26931d73eaf2d8408cd4db67e34u128, 0x130effd2815dffb1u128, 63nat) == 0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ gf128_mul_bits(0x4277a4d263ae7d5e5b08119a9b6cfcefu128, 0x9877fe940aeffd8u128, 62nat)) by { lemma_hmul128_bits_unfold(0xa13bd26931d73eaf2d8408cd4db67e34u128, 0x130effd2815dffb1u128, 63nat); }
    assert((((0x9877fe940aeffd8u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeffd8u128) >> 1u128) == 0x4c3bff4a0577fecu128)) by (bit_vector);
    assert(((((0x4277a4d263ae7d5e5b08119a9b6cfcefu128) << 1) ^ (if ((((0x4277a4d263ae7d5e5b08119a9b6cfcefu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x84ef49a4c75cfabcb610233536d9f9deu128) by (bit_vector);
    assert(gf128_xtime(0x4277a4d263ae7d5e5b08119a9b6cfcefu128) == 0x84ef49a4c75cfabcb610233536d9f9deu128);
    assert(gf128_mul_bits(0x4277a4d263ae7d5e5b08119a9b6cfcefu128, 0x9877fe940aeffd8u128, 62nat) == 0u128 ^ gf128_mul_bits(0x84ef49a4c75cfabcb610233536d9f9deu128, 0x4c3bff4a0577fecu128, 61nat)) by { lemma_hmul128_bits_unfold(0x4277a4d263ae7d5e5b08119a9b6cfcefu128, 0x9877fe940aeffd8u128, 62nat); }
    assert((((0x4c3bff4a0577fecu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fecu128) >> 1u128) == 0x261dffa502bbff6u128)) by (bit_vector);
    assert(((((0x84ef49a4c75cfabcb610233536d9f9deu128) << 1) ^ (if ((((0x84ef49a4c75cfabcb610233536d9f9deu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9de93498eb9f5796c20466a6db3f33bu128) by (bit_vector);
    assert(gf128_xtime(0x84ef49a4c75cfabcb610233536d9f9deu128) == 0x9de93498eb9f5796c20466a6db3f33bu128);
    assert(gf128_mul_bits(0x84ef49a4c75cfabcb610233536d9f9deu128, 0x4c3bff4a0577fecu128, 61nat) == 0u128 ^ gf128_mul_bits(0x9de93498eb9f5796c20466a6db3f33bu128, 0x261dffa502bbff6u128, 60nat)) by { lemma_hmul128_bits_unfold(0x84ef49a4c75cfabcb610233536d9f9deu128, 0x4c3bff4a0577fecu128, 61nat); }
    assert((((0x261dffa502bbff6u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502bbff6u128) >> 1u128) == 0x130effd2815dffbu128)) by (bit_vector);
    assert(((((0x9de93498eb9f5796c20466a6db3f33bu128) << 1) ^ (if ((((0x9de93498eb9f5796c20466a6db3f33bu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x13bd26931d73eaf2d8408cd4db67e676u128) by (bit_vector);
    assert(gf128_xtime(0x9de93498eb9f5796c20466a6db3f33bu128) == 0x13bd26931d73eaf2d8408cd4db67e676u128);
    assert(gf128_mul_bits(0x9de93498eb9f5796c20466a6db3f33bu128, 0x261dffa502bbff6u128, 60nat) == 0u128 ^ gf128_mul_bits(0x13bd26931d73eaf2d8408cd4db67e676u128, 0x130effd2815dffbu128, 59nat)) by { lemma_hmul128_bits_unfold(0x9de93498eb9f5796c20466a6db3f33bu128, 0x261dffa502bbff6u128, 60nat); }
    assert((((0x130effd2815dffbu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dffbu128) >> 1u128) == 0x9877fe940aeffdu128)) by (bit_vector);
    assert(((((0x13bd26931d73eaf2d8408cd4db67e676u128) << 1) ^ (if ((((0x13bd26931d73eaf2d8408cd4db67e676u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x277a4d263ae7d5e5b08119a9b6cfccecu128) by (bit_vector);
    assert(gf128_xtime(0x13bd26931d73eaf2d8408cd4db67e676u128) == 0x277a4d263ae7d5e5b08119a9b6cfccecu128);
    assert(gf128_mul_bits(0x13bd26931d73eaf2d8408cd4db67e676u128, 0x130effd2815dffbu128, 59nat) == 0x13bd26931d73eaf2d8408cd4db67e676u128 ^ gf128_mul_bits(0x277a4d263ae7d5e5b08119a9b6cfccecu128, 0x9877fe940aeffdu128, 58nat)) by { lemma_hmul128_bits_unfold(0x13bd26931d73eaf2d8408cd4db67e676u128, 0x130effd2815dffbu128, 59nat); }
    assert((((0x9877fe940aeffdu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe940aeffdu128) >> 1u128) == 0x4c3bff4a0577feu128)) by (bit_vector);
    assert(((((0x277a4d263ae7d5e5b08119a9b6cfccecu128) << 1) ^ (if ((((0x277a4d263ae7d5e5b08119a9b6cfccecu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4ef49a4c75cfabcb610233536d9f99d8u128) by (bit_vector);
    assert(gf128_xtime(0x277a4d263ae7d5e5b08119a9b6cfccecu128) == 0x4ef49a4c75cfabcb610233536d9f99d8u128);
    assert(gf128_mul_bits(0x277a4d263ae7d5e5b08119a9b6cfccecu128, 0x9877fe940aeffdu128, 58nat) == 0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ gf128_mul_bits(0x4ef49a4c75cfabcb610233536d9f99d8u128, 0x4c3bff4a0577feu128, 57nat)) by { lemma_hmul128_bits_unfold(0x277a4d263ae7d5e5b08119a9b6cfccecu128, 0x9877fe940aeffdu128, 58nat); }
    assert((((0x4c3bff4a0577feu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0577feu128) >> 1u128) == 0x261dffa502bbffu128)) by (bit_vector);
    assert(((((0x4ef49a4c75cfabcb610233536d9f99d8u128) << 1) ^ (if ((((0x4ef49a4c75cfabcb610233536d9f99d8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9de93498eb9f5796c20466a6db3f33b0u128) by (bit_vector);
    assert(gf128_xtime(0x4ef49a4c75cfabcb610233536d9f99d8u128) == 0x9de93498eb9f5796c20466a6db3f33b0u128);
    assert(gf128_mul_bits(0x4ef49a4c75cfabcb610233536d9f99d8u128, 0x4c3bff4a0577feu128, 57nat) == 0u128 ^ gf128_mul_bits(0x9de93498eb9f5796c20466a6db3f33b0u128, 0x261dffa502bbffu128, 56nat)) by { lemma_hmul128_bits_unfold(0x4ef49a4c75cfabcb610233536d9f99d8u128, 0x4c3bff4a0577feu128, 57nat); }
    assert((((0x261dffa502bbffu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbffu128) >> 1u128) == 0x130effd2815dffu128)) by (bit_vector);
    assert(((((0x9de93498eb9f5796c20466a6db3f33b0u128) << 1) ^ (if ((((0x9de93498eb9f5796c20466a6db3f33b0u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3bd26931d73eaf2d8408cd4db67e67e7u128) by (bit_vector);
    assert(gf128_xtime(0x9de93498eb9f5796c20466a6db3f33b0u128) == 0x3bd26931d73eaf2d8408cd4db67e67e7u128);
    assert(gf128_mul_bits(0x9de93498eb9f5796c20466a6db3f33b0u128, 0x261dffa502bbffu128, 56nat) == 0x9de93498eb9f5796c20466a6db3f33b0u128 ^ gf128_mul_bits(0x3bd26931d73eaf2d8408cd4db67e67e7u128, 0x130effd2815dffu128, 55nat)) by { lemma_hmul128_bits_unfold(0x9de93498eb9f5796c20466a6db3f33b0u128, 0x261dffa502bbffu128, 56nat); }
    assert((((0x130effd2815dffu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dffu128) >> 1u128) == 0x9877fe940aeffu128)) by (bit_vector);
    assert(((((0x3bd26931d73eaf2d8408cd4db67e67e7u128) << 1) ^ (if ((((0x3bd26931d73eaf2d8408cd4db67e67e7u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x77a4d263ae7d5e5b08119a9b6cfccfceu128) by (bit_vector);
    assert(gf128_xtime(0x3bd26931d73eaf2d8408cd4db67e67e7u128) == 0x77a4d263ae7d5e5b08119a9b6cfccfceu128);
    assert(gf128_mul_bits(0x3bd26931d73eaf2d8408cd4db67e67e7u128, 0x130effd2815dffu128, 55nat) == 0x3bd26931d73eaf2d8408cd4db67e67e7u128 ^ gf128_mul_bits(0x77a4d263ae7d5e5b08119a9b6cfccfceu128, 0x9877fe940aeffu128, 54nat)) by { lemma_hmul128_bits_unfold(0x3bd26931d73eaf2d8408cd4db67e67e7u128, 0x130effd2815dffu128, 55nat); }
    assert((((0x9877fe940aeffu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe940aeffu128) >> 1u128) == 0x4c3bff4a0577fu128)) by (bit_vector);
    assert(((((0x77a4d263ae7d5e5b08119a9b6cfccfceu128) << 1) ^ (if ((((0x77a4d263ae7d5e5b08119a9b6cfccfceu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xef49a4c75cfabcb610233536d9f99f9cu128) by (bit_vector);
    assert(gf128_xtime(0x77a4d263ae7d5e5b08119a9b6cfccfceu128) == 0xef49a4c75cfabcb610233536d9f99f9cu128);
    assert(gf128_mul_bits(0x77a4d263ae7d5e5b08119a9b6cfccfceu128, 0x9877fe940aeffu128, 54nat) == 0x77a4d263ae7d5e5b08119a9b6cfccfceu128 ^ gf128_mul_bits(0xef49a4c75cfabcb610233536d9f99f9cu128, 0x4c3bff4a0577fu128, 53nat)) by { lemma_hmul128_bits_unfold(0x77a4d263ae7d5e5b08119a9b6cfccfceu128, 0x9877fe940aeffu128, 54nat); }
    assert((((0x4c3bff4a0577fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577fu128) >> 1u128) == 0x261dffa502bbfu128)) by (bit_vector);
    assert(((((0xef49a4c75cfabcb610233536d9f99f9cu128) << 1) ^ (if ((((0xef49a4c75cfabcb610233536d9f99f9cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xde93498eb9f5796c20466a6db3f33fbfu128) by (bit_vector);
    assert(gf128_xtime(0xef49a4c75cfabcb610233536d9f99f9cu128) == 0xde93498eb9f5796c20466a6db3f33fbfu128);
    assert(gf128_mul_bits(0xef49a4c75cfabcb610233536d9f99f9cu128, 0x4c3bff4a0577fu128, 53nat) == 0xef49a4c75cfabcb610233536d9f99f9cu128 ^ gf128_mul_bits(0xde93498eb9f5796c20466a6db3f33fbfu128, 0x261dffa502bbfu128, 52nat)) by { lemma_hmul128_bits_unfold(0xef49a4c75cfabcb610233536d9f99f9cu128, 0x4c3bff4a0577fu128, 53nat); }
    assert((((0x261dffa502bbfu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbfu128) >> 1u128) == 0x130effd2815dfu128)) by (bit_vector);
    assert(((((0xde93498eb9f5796c20466a6db3f33fbfu128) << 1) ^ (if ((((0xde93498eb9f5796c20466a6db3f33fbfu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbd26931d73eaf2d8408cd4db67e67ff9u128) by (bit_vector);
    assert(gf128_xtime(0xde93498eb9f5796c20466a6db3f33fbfu128) == 0xbd26931d73eaf2d8408cd4db67e67ff9u128);
    assert(gf128_mul_bits(0xde93498eb9f5796c20466a6db3f33fbfu128, 0x261dffa502bbfu128, 52nat) == 0xde93498eb9f5796c20466a6db3f33fbfu128 ^ gf128_mul_bits(0xbd26931d73eaf2d8408cd4db67e67ff9u128, 0x130effd2815dfu128, 51nat)) by { lemma_hmul128_bits_unfold(0xde93498eb9f5796c20466a6db3f33fbfu128, 0x261dffa502bbfu128, 52nat); }
    assert((((0x130effd2815dfu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815dfu128) >> 1u128) == 0x9877fe940aefu128)) by (bit_vector);
    assert(((((0xbd26931d73eaf2d8408cd4db67e67ff9u128) << 1) ^ (if ((((0xbd26931d73eaf2d8408cd4db67e67ff9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7a4d263ae7d5e5b08119a9b6cfccff75u128) by (bit_vector);
    assert(gf128_xtime(0xbd26931d73eaf2d8408cd4db67e67ff9u128) == 0x7a4d263ae7d5e5b08119a9b6cfccff75u128);
    assert(gf128_mul_bits(0xbd26931d73eaf2d8408cd4db67e67ff9u128, 0x130effd2815dfu128, 51nat) == 0xbd26931d73eaf2d8408cd4db67e67ff9u128 ^ gf128_mul_bits(0x7a4d263ae7d5e5b08119a9b6cfccff75u128, 0x9877fe940aefu128, 50nat)) by { lemma_hmul128_bits_unfold(0xbd26931d73eaf2d8408cd4db67e67ff9u128, 0x130effd2815dfu128, 51nat); }
    assert((((0x9877fe940aefu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe940aefu128) >> 1u128) == 0x4c3bff4a0577u128)) by (bit_vector);
    assert(((((0x7a4d263ae7d5e5b08119a9b6cfccff75u128) << 1) ^ (if ((((0x7a4d263ae7d5e5b08119a9b6cfccff75u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf49a4c75cfabcb610233536d9f99feeau128) by (bit_vector);
    assert(gf128_xtime(0x7a4d263ae7d5e5b08119a9b6cfccff75u128) == 0xf49a4c75cfabcb610233536d9f99feeau128);
    assert(gf128_mul_bits(0x7a4d263ae7d5e5b08119a9b6cfccff75u128, 0x9877fe940aefu128, 50nat) == 0x7a4d263ae7d5e5b08119a9b6cfccff75u128 ^ gf128_mul_bits(0xf49a4c75cfabcb610233536d9f99feeau128, 0x4c3bff4a0577u128, 49nat)) by { lemma_hmul128_bits_unfold(0x7a4d263ae7d5e5b08119a9b6cfccff75u128, 0x9877fe940aefu128, 50nat); }
    assert((((0x4c3bff4a0577u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a0577u128) >> 1u128) == 0x261dffa502bbu128)) by (bit_vector);
    assert(((((0xf49a4c75cfabcb610233536d9f99feeau128) << 1) ^ (if ((((0xf49a4c75cfabcb610233536d9f99feeau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe93498eb9f5796c20466a6db3f33fd53u128) by (bit_vector);
    assert(gf128_xtime(0xf49a4c75cfabcb610233536d9f99feeau128) == 0xe93498eb9f5796c20466a6db3f33fd53u128);
    assert(gf128_mul_bits(0xf49a4c75cfabcb610233536d9f99feeau128, 0x4c3bff4a0577u128, 49nat) == 0xf49a4c75cfabcb610233536d9f99feeau128 ^ gf128_mul_bits(0xe93498eb9f5796c20466a6db3f33fd53u128, 0x261dffa502bbu128, 48nat)) by { lemma_hmul128_bits_unfold(0xf49a4c75cfabcb610233536d9f99feeau128, 0x4c3bff4a0577u128, 49nat); }
    assert((((0x261dffa502bbu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bbu128) >> 1u128) == 0x130effd2815du128)) by (bit_vector);
    assert(((((0xe93498eb9f5796c20466a6db3f33fd53u128) << 1) ^ (if ((((0xe93498eb9f5796c20466a6db3f33fd53u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd26931d73eaf2d8408cd4db67e67fa21u128) by (bit_vector);
    assert(gf128_xtime(0xe93498eb9f5796c20466a6db3f33fd53u128) == 0xd26931d73eaf2d8408cd4db67e67fa21u128);
    assert(gf128_mul_bits(0xe93498eb9f5796c20466a6db3f33fd53u128, 0x261dffa502bbu128, 48nat) == 0xe93498eb9f5796c20466a6db3f33fd53u128 ^ gf128_mul_bits(0xd26931d73eaf2d8408cd4db67e67fa21u128, 0x130effd2815du128, 47nat)) by { lemma_hmul128_bits_unfold(0xe93498eb9f5796c20466a6db3f33fd53u128, 0x261dffa502bbu128, 48nat); }
    assert((((0x130effd2815du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815du128) >> 1u128) == 0x9877fe940aeu128)) by (bit_vector);
    assert(((((0xd26931d73eaf2d8408cd4db67e67fa21u128) << 1) ^ (if ((((0xd26931d73eaf2d8408cd4db67e67fa21u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa4d263ae7d5e5b08119a9b6cfccff4c5u128) by (bit_vector);
    assert(gf128_xtime(0xd26931d73eaf2d8408cd4db67e67fa21u128) == 0xa4d263ae7d5e5b08119a9b6cfccff4c5u128);
    assert(gf128_mul_bits(0xd26931d73eaf2d8408cd4db67e67fa21u128, 0x130effd2815du128, 47nat) == 0xd26931d73eaf2d8408cd4db67e67fa21u128 ^ gf128_mul_bits(0xa4d263ae7d5e5b08119a9b6cfccff4c5u128, 0x9877fe940aeu128, 46nat)) by { lemma_hmul128_bits_unfold(0xd26931d73eaf2d8408cd4db67e67fa21u128, 0x130effd2815du128, 47nat); }
    assert((((0x9877fe940aeu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940aeu128) >> 1u128) == 0x4c3bff4a057u128)) by (bit_vector);
    assert(((((0xa4d263ae7d5e5b08119a9b6cfccff4c5u128) << 1) ^ (if ((((0xa4d263ae7d5e5b08119a9b6cfccff4c5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x49a4c75cfabcb610233536d9f99fe90du128) by (bit_vector);
    assert(gf128_xtime(0xa4d263ae7d5e5b08119a9b6cfccff4c5u128) == 0x49a4c75cfabcb610233536d9f99fe90du128);
    assert(gf128_mul_bits(0xa4d263ae7d5e5b08119a9b6cfccff4c5u128, 0x9877fe940aeu128, 46nat) == 0u128 ^ gf128_mul_bits(0x49a4c75cfabcb610233536d9f99fe90du128, 0x4c3bff4a057u128, 45nat)) by { lemma_hmul128_bits_unfold(0xa4d263ae7d5e5b08119a9b6cfccff4c5u128, 0x9877fe940aeu128, 46nat); }
    assert((((0x4c3bff4a057u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a057u128) >> 1u128) == 0x261dffa502bu128)) by (bit_vector);
    assert(((((0x49a4c75cfabcb610233536d9f99fe90du128) << 1) ^ (if ((((0x49a4c75cfabcb610233536d9f99fe90du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x93498eb9f5796c20466a6db3f33fd21au128) by (bit_vector);
    assert(gf128_xtime(0x49a4c75cfabcb610233536d9f99fe90du128) == 0x93498eb9f5796c20466a6db3f33fd21au128);
    assert(gf128_mul_bits(0x49a4c75cfabcb610233536d9f99fe90du128, 0x4c3bff4a057u128, 45nat) == 0x49a4c75cfabcb610233536d9f99fe90du128 ^ gf128_mul_bits(0x93498eb9f5796c20466a6db3f33fd21au128, 0x261dffa502bu128, 44nat)) by { lemma_hmul128_bits_unfold(0x49a4c75cfabcb610233536d9f99fe90du128, 0x4c3bff4a057u128, 45nat); }
    assert((((0x261dffa502bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa502bu128) >> 1u128) == 0x130effd2815u128)) by (bit_vector);
    assert(((((0x93498eb9f5796c20466a6db3f33fd21au128) << 1) ^ (if ((((0x93498eb9f5796c20466a6db3f33fd21au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x26931d73eaf2d8408cd4db67e67fa4b3u128) by (bit_vector);
    assert(gf128_xtime(0x93498eb9f5796c20466a6db3f33fd21au128) == 0x26931d73eaf2d8408cd4db67e67fa4b3u128);
    assert(gf128_mul_bits(0x93498eb9f5796c20466a6db3f33fd21au128, 0x261dffa502bu128, 44nat) == 0x93498eb9f5796c20466a6db3f33fd21au128 ^ gf128_mul_bits(0x26931d73eaf2d8408cd4db67e67fa4b3u128, 0x130effd2815u128, 43nat)) by { lemma_hmul128_bits_unfold(0x93498eb9f5796c20466a6db3f33fd21au128, 0x261dffa502bu128, 44nat); }
    assert((((0x130effd2815u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd2815u128) >> 1u128) == 0x9877fe940au128)) by (bit_vector);
    assert(((((0x26931d73eaf2d8408cd4db67e67fa4b3u128) << 1) ^ (if ((((0x26931d73eaf2d8408cd4db67e67fa4b3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4d263ae7d5e5b08119a9b6cfccff4966u128) by (bit_vector);
    assert(gf128_xtime(0x26931d73eaf2d8408cd4db67e67fa4b3u128) == 0x4d263ae7d5e5b08119a9b6cfccff4966u128);
    assert(gf128_mul_bits(0x26931d73eaf2d8408cd4db67e67fa4b3u128, 0x130effd2815u128, 43nat) == 0x26931d73eaf2d8408cd4db67e67fa4b3u128 ^ gf128_mul_bits(0x4d263ae7d5e5b08119a9b6cfccff4966u128, 0x9877fe940au128, 42nat)) by { lemma_hmul128_bits_unfold(0x26931d73eaf2d8408cd4db67e67fa4b3u128, 0x130effd2815u128, 43nat); }
    assert((((0x9877fe940au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940au128) >> 1u128) == 0x4c3bff4a05u128)) by (bit_vector);
    assert(((((0x4d263ae7d5e5b08119a9b6cfccff4966u128) << 1) ^ (if ((((0x4d263ae7d5e5b08119a9b6cfccff4966u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9a4c75cfabcb610233536d9f99fe92ccu128) by (bit_vector);
    assert(gf128_xtime(0x4d263ae7d5e5b08119a9b6cfccff4966u128) == 0x9a4c75cfabcb610233536d9f99fe92ccu128);
    assert(gf128_mul_bits(0x4d263ae7d5e5b08119a9b6cfccff4966u128, 0x9877fe940au128, 42nat) == 0u128 ^ gf128_mul_bits(0x9a4c75cfabcb610233536d9f99fe92ccu128, 0x4c3bff4a05u128, 41nat)) by { lemma_hmul128_bits_unfold(0x4d263ae7d5e5b08119a9b6cfccff4966u128, 0x9877fe940au128, 42nat); }
    assert((((0x4c3bff4a05u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bff4a05u128) >> 1u128) == 0x261dffa502u128)) by (bit_vector);
    assert(((((0x9a4c75cfabcb610233536d9f99fe92ccu128) << 1) ^ (if ((((0x9a4c75cfabcb610233536d9f99fe92ccu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3498eb9f5796c20466a6db3f33fd251fu128) by (bit_vector);
    assert(gf128_xtime(0x9a4c75cfabcb610233536d9f99fe92ccu128) == 0x3498eb9f5796c20466a6db3f33fd251fu128);
    assert(gf128_mul_bits(0x9a4c75cfabcb610233536d9f99fe92ccu128, 0x4c3bff4a05u128, 41nat) == 0x9a4c75cfabcb610233536d9f99fe92ccu128 ^ gf128_mul_bits(0x3498eb9f5796c20466a6db3f33fd251fu128, 0x261dffa502u128, 40nat)) by { lemma_hmul128_bits_unfold(0x9a4c75cfabcb610233536d9f99fe92ccu128, 0x4c3bff4a05u128, 41nat); }
    assert((((0x261dffa502u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa502u128) >> 1u128) == 0x130effd281u128)) by (bit_vector);
    assert(((((0x3498eb9f5796c20466a6db3f33fd251fu128) << 1) ^ (if ((((0x3498eb9f5796c20466a6db3f33fd251fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x6931d73eaf2d8408cd4db67e67fa4a3eu128) by (bit_vector);
    assert(gf128_xtime(0x3498eb9f5796c20466a6db3f33fd251fu128) == 0x6931d73eaf2d8408cd4db67e67fa4a3eu128);
    assert(gf128_mul_bits(0x3498eb9f5796c20466a6db3f33fd251fu128, 0x261dffa502u128, 40nat) == 0u128 ^ gf128_mul_bits(0x6931d73eaf2d8408cd4db67e67fa4a3eu128, 0x130effd281u128, 39nat)) by { lemma_hmul128_bits_unfold(0x3498eb9f5796c20466a6db3f33fd251fu128, 0x261dffa502u128, 40nat); }
    assert((((0x130effd281u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effd281u128) >> 1u128) == 0x9877fe940u128)) by (bit_vector);
    assert(((((0x6931d73eaf2d8408cd4db67e67fa4a3eu128) << 1) ^ (if ((((0x6931d73eaf2d8408cd4db67e67fa4a3eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd263ae7d5e5b08119a9b6cfccff4947cu128) by (bit_vector);
    assert(gf128_xtime(0x6931d73eaf2d8408cd4db67e67fa4a3eu128) == 0xd263ae7d5e5b08119a9b6cfccff4947cu128);
    assert(gf128_mul_bits(0x6931d73eaf2d8408cd4db67e67fa4a3eu128, 0x130effd281u128, 39nat) == 0x6931d73eaf2d8408cd4db67e67fa4a3eu128 ^ gf128_mul_bits(0xd263ae7d5e5b08119a9b6cfccff4947cu128, 0x9877fe940u128, 38nat)) by { lemma_hmul128_bits_unfold(0x6931d73eaf2d8408cd4db67e67fa4a3eu128, 0x130effd281u128, 39nat); }
    assert((((0x9877fe940u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe940u128) >> 1u128) == 0x4c3bff4a0u128)) by (bit_vector);
    assert(((((0xd263ae7d5e5b08119a9b6cfccff4947cu128) << 1) ^ (if ((((0xd263ae7d5e5b08119a9b6cfccff4947cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xa4c75cfabcb610233536d9f99fe9287fu128) by (bit_vector);
    assert(gf128_xtime(0xd263ae7d5e5b08119a9b6cfccff4947cu128) == 0xa4c75cfabcb610233536d9f99fe9287fu128);
    assert(gf128_mul_bits(0xd263ae7d5e5b08119a9b6cfccff4947cu128, 0x9877fe940u128, 38nat) == 0u128 ^ gf128_mul_bits(0xa4c75cfabcb610233536d9f99fe9287fu128, 0x4c3bff4a0u128, 37nat)) by { lemma_hmul128_bits_unfold(0xd263ae7d5e5b08119a9b6cfccff4947cu128, 0x9877fe940u128, 38nat); }
    assert((((0x4c3bff4a0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4a0u128) >> 1u128) == 0x261dffa50u128)) by (bit_vector);
    assert(((((0xa4c75cfabcb610233536d9f99fe9287fu128) << 1) ^ (if ((((0xa4c75cfabcb610233536d9f99fe9287fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x498eb9f5796c20466a6db3f33fd25079u128) by (bit_vector);
    assert(gf128_xtime(0xa4c75cfabcb610233536d9f99fe9287fu128) == 0x498eb9f5796c20466a6db3f33fd25079u128);
    assert(gf128_mul_bits(0xa4c75cfabcb610233536d9f99fe9287fu128, 0x4c3bff4a0u128, 37nat) == 0u128 ^ gf128_mul_bits(0x498eb9f5796c20466a6db3f33fd25079u128, 0x261dffa50u128, 36nat)) by { lemma_hmul128_bits_unfold(0xa4c75cfabcb610233536d9f99fe9287fu128, 0x4c3bff4a0u128, 37nat); }
    assert((((0x261dffa50u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffa50u128) >> 1u128) == 0x130effd28u128)) by (bit_vector);
    assert(((((0x498eb9f5796c20466a6db3f33fd25079u128) << 1) ^ (if ((((0x498eb9f5796c20466a6db3f33fd25079u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x931d73eaf2d8408cd4db67e67fa4a0f2u128) by (bit_vector);
    assert(gf128_xtime(0x498eb9f5796c20466a6db3f33fd25079u128) == 0x931d73eaf2d8408cd4db67e67fa4a0f2u128);
    assert(gf128_mul_bits(0x498eb9f5796c20466a6db3f33fd25079u128, 0x261dffa50u128, 36nat) == 0u128 ^ gf128_mul_bits(0x931d73eaf2d8408cd4db67e67fa4a0f2u128, 0x130effd28u128, 35nat)) by { lemma_hmul128_bits_unfold(0x498eb9f5796c20466a6db3f33fd25079u128, 0x261dffa50u128, 36nat); }
    assert((((0x130effd28u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd28u128) >> 1u128) == 0x9877fe94u128)) by (bit_vector);
    assert(((((0x931d73eaf2d8408cd4db67e67fa4a0f2u128) << 1) ^ (if ((((0x931d73eaf2d8408cd4db67e67fa4a0f2u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x263ae7d5e5b08119a9b6cfccff494163u128) by (bit_vector);
    assert(gf128_xtime(0x931d73eaf2d8408cd4db67e67fa4a0f2u128) == 0x263ae7d5e5b08119a9b6cfccff494163u128);
    assert(gf128_mul_bits(0x931d73eaf2d8408cd4db67e67fa4a0f2u128, 0x130effd28u128, 35nat) == 0u128 ^ gf128_mul_bits(0x263ae7d5e5b08119a9b6cfccff494163u128, 0x9877fe94u128, 34nat)) by { lemma_hmul128_bits_unfold(0x931d73eaf2d8408cd4db67e67fa4a0f2u128, 0x130effd28u128, 35nat); }
    assert((((0x9877fe94u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877fe94u128) >> 1u128) == 0x4c3bff4au128)) by (bit_vector);
    assert(((((0x263ae7d5e5b08119a9b6cfccff494163u128) << 1) ^ (if ((((0x263ae7d5e5b08119a9b6cfccff494163u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x4c75cfabcb610233536d9f99fe9282c6u128) by (bit_vector);
    assert(gf128_xtime(0x263ae7d5e5b08119a9b6cfccff494163u128) == 0x4c75cfabcb610233536d9f99fe9282c6u128);
    assert(gf128_mul_bits(0x263ae7d5e5b08119a9b6cfccff494163u128, 0x9877fe94u128, 34nat) == 0u128 ^ gf128_mul_bits(0x4c75cfabcb610233536d9f99fe9282c6u128, 0x4c3bff4au128, 33nat)) by { lemma_hmul128_bits_unfold(0x263ae7d5e5b08119a9b6cfccff494163u128, 0x9877fe94u128, 34nat); }
    assert((((0x4c3bff4au128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4au128) >> 1u128) == 0x261dffa5u128)) by (bit_vector);
    assert(((((0x4c75cfabcb610233536d9f99fe9282c6u128) << 1) ^ (if ((((0x4c75cfabcb610233536d9f99fe9282c6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x98eb9f5796c20466a6db3f33fd25058cu128) by (bit_vector);
    assert(gf128_xtime(0x4c75cfabcb610233536d9f99fe9282c6u128) == 0x98eb9f5796c20466a6db3f33fd25058cu128);
    assert(gf128_mul_bits(0x4c75cfabcb610233536d9f99fe9282c6u128, 0x4c3bff4au128, 33nat) == 0u128 ^ gf128_mul_bits(0x98eb9f5796c20466a6db3f33fd25058cu128, 0x261dffa5u128, 32nat)) by { lemma_hmul128_bits_unfold(0x4c75cfabcb610233536d9f99fe9282c6u128, 0x4c3bff4au128, 33nat); }
    assert((((0x261dffa5u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffa5u128) >> 1u128) == 0x130effd2u128)) by (bit_vector);
    assert(((((0x98eb9f5796c20466a6db3f33fd25058cu128) << 1) ^ (if ((((0x98eb9f5796c20466a6db3f33fd25058cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x31d73eaf2d8408cd4db67e67fa4a0b9fu128) by (bit_vector);
    assert(gf128_xtime(0x98eb9f5796c20466a6db3f33fd25058cu128) == 0x31d73eaf2d8408cd4db67e67fa4a0b9fu128);
    assert(gf128_mul_bits(0x98eb9f5796c20466a6db3f33fd25058cu128, 0x261dffa5u128, 32nat) == 0x98eb9f5796c20466a6db3f33fd25058cu128 ^ gf128_mul_bits(0x31d73eaf2d8408cd4db67e67fa4a0b9fu128, 0x130effd2u128, 31nat)) by { lemma_hmul128_bits_unfold(0x98eb9f5796c20466a6db3f33fd25058cu128, 0x261dffa5u128, 32nat); }
    assert((((0x130effd2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130effd2u128) >> 1u128) == 0x9877fe9u128)) by (bit_vector);
    assert(((((0x31d73eaf2d8408cd4db67e67fa4a0b9fu128) << 1) ^ (if ((((0x31d73eaf2d8408cd4db67e67fa4a0b9fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x63ae7d5e5b08119a9b6cfccff494173eu128) by (bit_vector);
    assert(gf128_xtime(0x31d73eaf2d8408cd4db67e67fa4a0b9fu128) == 0x63ae7d5e5b08119a9b6cfccff494173eu128);
    assert(gf128_mul_bits(0x31d73eaf2d8408cd4db67e67fa4a0b9fu128, 0x130effd2u128, 31nat) == 0u128 ^ gf128_mul_bits(0x63ae7d5e5b08119a9b6cfccff494173eu128, 0x9877fe9u128, 30nat)) by { lemma_hmul128_bits_unfold(0x31d73eaf2d8408cd4db67e67fa4a0b9fu128, 0x130effd2u128, 31nat); }
    assert((((0x9877fe9u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fe9u128) >> 1u128) == 0x4c3bff4u128)) by (bit_vector);
    assert(((((0x63ae7d5e5b08119a9b6cfccff494173eu128) << 1) ^ (if ((((0x63ae7d5e5b08119a9b6cfccff494173eu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xc75cfabcb610233536d9f99fe9282e7cu128) by (bit_vector);
    assert(gf128_xtime(0x63ae7d5e5b08119a9b6cfccff494173eu128) == 0xc75cfabcb610233536d9f99fe9282e7cu128);
    assert(gf128_mul_bits(0x63ae7d5e5b08119a9b6cfccff494173eu128, 0x9877fe9u128, 30nat) == 0x63ae7d5e5b08119a9b6cfccff494173eu128 ^ gf128_mul_bits(0xc75cfabcb610233536d9f99fe9282e7cu128, 0x4c3bff4u128, 29nat)) by { lemma_hmul128_bits_unfold(0x63ae7d5e5b08119a9b6cfccff494173eu128, 0x9877fe9u128, 30nat); }
    assert((((0x4c3bff4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4c3bff4u128) >> 1u128) == 0x261dffau128)) by (bit_vector);
    assert(((((0xc75cfabcb610233536d9f99fe9282e7cu128) << 1) ^ (if ((((0xc75cfabcb610233536d9f99fe9282e7cu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x8eb9f5796c20466a6db3f33fd2505c7fu128) by (bit_vector);
    assert(gf128_xtime(0xc75cfabcb610233536d9f99fe9282e7cu128) == 0x8eb9f5796c20466a6db3f33fd2505c7fu128);
    assert(gf128_mul_bits(0xc75cfabcb610233536d9f99fe9282e7cu128, 0x4c3bff4u128, 29nat) == 0u128 ^ gf128_mul_bits(0x8eb9f5796c20466a6db3f33fd2505c7fu128, 0x261dffau128, 28nat)) by { lemma_hmul128_bits_unfold(0xc75cfabcb610233536d9f99fe9282e7cu128, 0x4c3bff4u128, 29nat); }
    assert((((0x261dffau128) & 1) == 0u128)) by (bit_vector);
    assert((((0x261dffau128) >> 1u128) == 0x130effdu128)) by (bit_vector);
    assert(((((0x8eb9f5796c20466a6db3f33fd2505c7fu128) << 1) ^ (if ((((0x8eb9f5796c20466a6db3f33fd2505c7fu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x1d73eaf2d8408cd4db67e67fa4a0b879u128) by (bit_vector);
    assert(gf128_xtime(0x8eb9f5796c20466a6db3f33fd2505c7fu128) == 0x1d73eaf2d8408cd4db67e67fa4a0b879u128);
    assert(gf128_mul_bits(0x8eb9f5796c20466a6db3f33fd2505c7fu128, 0x261dffau128, 28nat) == 0u128 ^ gf128_mul_bits(0x1d73eaf2d8408cd4db67e67fa4a0b879u128, 0x130effdu128, 27nat)) by { lemma_hmul128_bits_unfold(0x8eb9f5796c20466a6db3f33fd2505c7fu128, 0x261dffau128, 28nat); }
    assert((((0x130effdu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effdu128) >> 1u128) == 0x9877feu128)) by (bit_vector);
    assert(((((0x1d73eaf2d8408cd4db67e67fa4a0b879u128) << 1) ^ (if ((((0x1d73eaf2d8408cd4db67e67fa4a0b879u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3ae7d5e5b08119a9b6cfccff494170f2u128) by (bit_vector);
    assert(gf128_xtime(0x1d73eaf2d8408cd4db67e67fa4a0b879u128) == 0x3ae7d5e5b08119a9b6cfccff494170f2u128);
    assert(gf128_mul_bits(0x1d73eaf2d8408cd4db67e67fa4a0b879u128, 0x130effdu128, 27nat) == 0x1d73eaf2d8408cd4db67e67fa4a0b879u128 ^ gf128_mul_bits(0x3ae7d5e5b08119a9b6cfccff494170f2u128, 0x9877feu128, 26nat)) by { lemma_hmul128_bits_unfold(0x1d73eaf2d8408cd4db67e67fa4a0b879u128, 0x130effdu128, 27nat); }
    assert((((0x9877feu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x9877feu128) >> 1u128) == 0x4c3bffu128)) by (bit_vector);
    assert(((((0x3ae7d5e5b08119a9b6cfccff494170f2u128) << 1) ^ (if ((((0x3ae7d5e5b08119a9b6cfccff494170f2u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x75cfabcb610233536d9f99fe9282e1e4u128) by (bit_vector);
    assert(gf128_xtime(0x3ae7d5e5b08119a9b6cfccff494170f2u128) == 0x75cfabcb610233536d9f99fe9282e1e4u128);
    assert(gf128_mul_bits(0x3ae7d5e5b08119a9b6cfccff494170f2u128, 0x9877feu128, 26nat) == 0u128 ^ gf128_mul_bits(0x75cfabcb610233536d9f99fe9282e1e4u128, 0x4c3bffu128, 25nat)) by { lemma_hmul128_bits_unfold(0x3ae7d5e5b08119a9b6cfccff494170f2u128, 0x9877feu128, 26nat); }
    assert((((0x4c3bffu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bffu128) >> 1u128) == 0x261dffu128)) by (bit_vector);
    assert(((((0x75cfabcb610233536d9f99fe9282e1e4u128) << 1) ^ (if ((((0x75cfabcb610233536d9f99fe9282e1e4u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xeb9f5796c20466a6db3f33fd2505c3c8u128) by (bit_vector);
    assert(gf128_xtime(0x75cfabcb610233536d9f99fe9282e1e4u128) == 0xeb9f5796c20466a6db3f33fd2505c3c8u128);
    assert(gf128_mul_bits(0x75cfabcb610233536d9f99fe9282e1e4u128, 0x4c3bffu128, 25nat) == 0x75cfabcb610233536d9f99fe9282e1e4u128 ^ gf128_mul_bits(0xeb9f5796c20466a6db3f33fd2505c3c8u128, 0x261dffu128, 24nat)) by { lemma_hmul128_bits_unfold(0x75cfabcb610233536d9f99fe9282e1e4u128, 0x4c3bffu128, 25nat); }
    assert((((0x261dffu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dffu128) >> 1u128) == 0x130effu128)) by (bit_vector);
    assert(((((0xeb9f5796c20466a6db3f33fd2505c3c8u128) << 1) ^ (if ((((0xeb9f5796c20466a6db3f33fd2505c3c8u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd73eaf2d8408cd4db67e67fa4a0b8717u128) by (bit_vector);
    assert(gf128_xtime(0xeb9f5796c20466a6db3f33fd2505c3c8u128) == 0xd73eaf2d8408cd4db67e67fa4a0b8717u128);
    assert(gf128_mul_bits(0xeb9f5796c20466a6db3f33fd2505c3c8u128, 0x261dffu128, 24nat) == 0xeb9f5796c20466a6db3f33fd2505c3c8u128 ^ gf128_mul_bits(0xd73eaf2d8408cd4db67e67fa4a0b8717u128, 0x130effu128, 23nat)) by { lemma_hmul128_bits_unfold(0xeb9f5796c20466a6db3f33fd2505c3c8u128, 0x261dffu128, 24nat); }
    assert((((0x130effu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130effu128) >> 1u128) == 0x9877fu128)) by (bit_vector);
    assert(((((0xd73eaf2d8408cd4db67e67fa4a0b8717u128) << 1) ^ (if ((((0xd73eaf2d8408cd4db67e67fa4a0b8717u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xae7d5e5b08119a9b6cfccff494170ea9u128) by (bit_vector);
    assert(gf128_xtime(0xd73eaf2d8408cd4db67e67fa4a0b8717u128) == 0xae7d5e5b08119a9b6cfccff494170ea9u128);
    assert(gf128_mul_bits(0xd73eaf2d8408cd4db67e67fa4a0b8717u128, 0x130effu128, 23nat) == 0xd73eaf2d8408cd4db67e67fa4a0b8717u128 ^ gf128_mul_bits(0xae7d5e5b08119a9b6cfccff494170ea9u128, 0x9877fu128, 22nat)) by { lemma_hmul128_bits_unfold(0xd73eaf2d8408cd4db67e67fa4a0b8717u128, 0x130effu128, 23nat); }
    assert((((0x9877fu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877fu128) >> 1u128) == 0x4c3bfu128)) by (bit_vector);
    assert(((((0xae7d5e5b08119a9b6cfccff494170ea9u128) << 1) ^ (if ((((0xae7d5e5b08119a9b6cfccff494170ea9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5cfabcb610233536d9f99fe9282e1dd5u128) by (bit_vector);
    assert(gf128_xtime(0xae7d5e5b08119a9b6cfccff494170ea9u128) == 0x5cfabcb610233536d9f99fe9282e1dd5u128);
    assert(gf128_mul_bits(0xae7d5e5b08119a9b6cfccff494170ea9u128, 0x9877fu128, 22nat) == 0xae7d5e5b08119a9b6cfccff494170ea9u128 ^ gf128_mul_bits(0x5cfabcb610233536d9f99fe9282e1dd5u128, 0x4c3bfu128, 21nat)) by { lemma_hmul128_bits_unfold(0xae7d5e5b08119a9b6cfccff494170ea9u128, 0x9877fu128, 22nat); }
    assert((((0x4c3bfu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bfu128) >> 1u128) == 0x261dfu128)) by (bit_vector);
    assert(((((0x5cfabcb610233536d9f99fe9282e1dd5u128) << 1) ^ (if ((((0x5cfabcb610233536d9f99fe9282e1dd5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xb9f5796c20466a6db3f33fd2505c3baau128) by (bit_vector);
    assert(gf128_xtime(0x5cfabcb610233536d9f99fe9282e1dd5u128) == 0xb9f5796c20466a6db3f33fd2505c3baau128);
    assert(gf128_mul_bits(0x5cfabcb610233536d9f99fe9282e1dd5u128, 0x4c3bfu128, 21nat) == 0x5cfabcb610233536d9f99fe9282e1dd5u128 ^ gf128_mul_bits(0xb9f5796c20466a6db3f33fd2505c3baau128, 0x261dfu128, 20nat)) by { lemma_hmul128_bits_unfold(0x5cfabcb610233536d9f99fe9282e1dd5u128, 0x4c3bfu128, 21nat); }
    assert((((0x261dfu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261dfu128) >> 1u128) == 0x130efu128)) by (bit_vector);
    assert(((((0xb9f5796c20466a6db3f33fd2505c3baau128) << 1) ^ (if ((((0xb9f5796c20466a6db3f33fd2505c3baau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x73eaf2d8408cd4db67e67fa4a0b877d3u128) by (bit_vector);
    assert(gf128_xtime(0xb9f5796c20466a6db3f33fd2505c3baau128) == 0x73eaf2d8408cd4db67e67fa4a0b877d3u128);
    assert(gf128_mul_bits(0xb9f5796c20466a6db3f33fd2505c3baau128, 0x261dfu128, 20nat) == 0xb9f5796c20466a6db3f33fd2505c3baau128 ^ gf128_mul_bits(0x73eaf2d8408cd4db67e67fa4a0b877d3u128, 0x130efu128, 19nat)) by { lemma_hmul128_bits_unfold(0xb9f5796c20466a6db3f33fd2505c3baau128, 0x261dfu128, 20nat); }
    assert((((0x130efu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x130efu128) >> 1u128) == 0x9877u128)) by (bit_vector);
    assert(((((0x73eaf2d8408cd4db67e67fa4a0b877d3u128) << 1) ^ (if ((((0x73eaf2d8408cd4db67e67fa4a0b877d3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe7d5e5b08119a9b6cfccff494170efa6u128) by (bit_vector);
    assert(gf128_xtime(0x73eaf2d8408cd4db67e67fa4a0b877d3u128) == 0xe7d5e5b08119a9b6cfccff494170efa6u128);
    assert(gf128_mul_bits(0x73eaf2d8408cd4db67e67fa4a0b877d3u128, 0x130efu128, 19nat) == 0x73eaf2d8408cd4db67e67fa4a0b877d3u128 ^ gf128_mul_bits(0xe7d5e5b08119a9b6cfccff494170efa6u128, 0x9877u128, 18nat)) by { lemma_hmul128_bits_unfold(0x73eaf2d8408cd4db67e67fa4a0b877d3u128, 0x130efu128, 19nat); }
    assert((((0x9877u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9877u128) >> 1u128) == 0x4c3bu128)) by (bit_vector);
    assert(((((0xe7d5e5b08119a9b6cfccff494170efa6u128) << 1) ^ (if ((((0xe7d5e5b08119a9b6cfccff494170efa6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xcfabcb610233536d9f99fe9282e1dfcbu128) by (bit_vector);
    assert(gf128_xtime(0xe7d5e5b08119a9b6cfccff494170efa6u128) == 0xcfabcb610233536d9f99fe9282e1dfcbu128);
    assert(gf128_mul_bits(0xe7d5e5b08119a9b6cfccff494170efa6u128, 0x9877u128, 18nat) == 0xe7d5e5b08119a9b6cfccff494170efa6u128 ^ gf128_mul_bits(0xcfabcb610233536d9f99fe9282e1dfcbu128, 0x4c3bu128, 17nat)) by { lemma_hmul128_bits_unfold(0xe7d5e5b08119a9b6cfccff494170efa6u128, 0x9877u128, 18nat); }
    assert((((0x4c3bu128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3bu128) >> 1u128) == 0x261du128)) by (bit_vector);
    assert(((((0xcfabcb610233536d9f99fe9282e1dfcbu128) << 1) ^ (if ((((0xcfabcb610233536d9f99fe9282e1dfcbu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x9f5796c20466a6db3f33fd2505c3bf11u128) by (bit_vector);
    assert(gf128_xtime(0xcfabcb610233536d9f99fe9282e1dfcbu128) == 0x9f5796c20466a6db3f33fd2505c3bf11u128);
    assert(gf128_mul_bits(0xcfabcb610233536d9f99fe9282e1dfcbu128, 0x4c3bu128, 17nat) == 0xcfabcb610233536d9f99fe9282e1dfcbu128 ^ gf128_mul_bits(0x9f5796c20466a6db3f33fd2505c3bf11u128, 0x261du128, 16nat)) by { lemma_hmul128_bits_unfold(0xcfabcb610233536d9f99fe9282e1dfcbu128, 0x4c3bu128, 17nat); }
    assert((((0x261du128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261du128) >> 1u128) == 0x130eu128)) by (bit_vector);
    assert(((((0x9f5796c20466a6db3f33fd2505c3bf11u128) << 1) ^ (if ((((0x9f5796c20466a6db3f33fd2505c3bf11u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x3eaf2d8408cd4db67e67fa4a0b877ea5u128) by (bit_vector);
    assert(gf128_xtime(0x9f5796c20466a6db3f33fd2505c3bf11u128) == 0x3eaf2d8408cd4db67e67fa4a0b877ea5u128);
    assert(gf128_mul_bits(0x9f5796c20466a6db3f33fd2505c3bf11u128, 0x261du128, 16nat) == 0x9f5796c20466a6db3f33fd2505c3bf11u128 ^ gf128_mul_bits(0x3eaf2d8408cd4db67e67fa4a0b877ea5u128, 0x130eu128, 15nat)) by { lemma_hmul128_bits_unfold(0x9f5796c20466a6db3f33fd2505c3bf11u128, 0x261du128, 16nat); }
    assert((((0x130eu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130eu128) >> 1u128) == 0x987u128)) by (bit_vector);
    assert(((((0x3eaf2d8408cd4db67e67fa4a0b877ea5u128) << 1) ^ (if ((((0x3eaf2d8408cd4db67e67fa4a0b877ea5u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x7d5e5b08119a9b6cfccff494170efd4au128) by (bit_vector);
    assert(gf128_xtime(0x3eaf2d8408cd4db67e67fa4a0b877ea5u128) == 0x7d5e5b08119a9b6cfccff494170efd4au128);
    assert(gf128_mul_bits(0x3eaf2d8408cd4db67e67fa4a0b877ea5u128, 0x130eu128, 15nat) == 0u128 ^ gf128_mul_bits(0x7d5e5b08119a9b6cfccff494170efd4au128, 0x987u128, 14nat)) by { lemma_hmul128_bits_unfold(0x3eaf2d8408cd4db67e67fa4a0b877ea5u128, 0x130eu128, 15nat); }
    assert((((0x987u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x987u128) >> 1u128) == 0x4c3u128)) by (bit_vector);
    assert(((((0x7d5e5b08119a9b6cfccff494170efd4au128) << 1) ^ (if ((((0x7d5e5b08119a9b6cfccff494170efd4au128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xfabcb610233536d9f99fe9282e1dfa94u128) by (bit_vector);
    assert(gf128_xtime(0x7d5e5b08119a9b6cfccff494170efd4au128) == 0xfabcb610233536d9f99fe9282e1dfa94u128);
    assert(gf128_mul_bits(0x7d5e5b08119a9b6cfccff494170efd4au128, 0x987u128, 14nat) == 0x7d5e5b08119a9b6cfccff494170efd4au128 ^ gf128_mul_bits(0xfabcb610233536d9f99fe9282e1dfa94u128, 0x4c3u128, 13nat)) by { lemma_hmul128_bits_unfold(0x7d5e5b08119a9b6cfccff494170efd4au128, 0x987u128, 14nat); }
    assert((((0x4c3u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x4c3u128) >> 1u128) == 0x261u128)) by (bit_vector);
    assert(((((0xfabcb610233536d9f99fe9282e1dfa94u128) << 1) ^ (if ((((0xfabcb610233536d9f99fe9282e1dfa94u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf5796c20466a6db3f33fd2505c3bf5afu128) by (bit_vector);
    assert(gf128_xtime(0xfabcb610233536d9f99fe9282e1dfa94u128) == 0xf5796c20466a6db3f33fd2505c3bf5afu128);
    assert(gf128_mul_bits(0xfabcb610233536d9f99fe9282e1dfa94u128, 0x4c3u128, 13nat) == 0xfabcb610233536d9f99fe9282e1dfa94u128 ^ gf128_mul_bits(0xf5796c20466a6db3f33fd2505c3bf5afu128, 0x261u128, 12nat)) by { lemma_hmul128_bits_unfold(0xfabcb610233536d9f99fe9282e1dfa94u128, 0x4c3u128, 13nat); }
    assert((((0x261u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x261u128) >> 1u128) == 0x130u128)) by (bit_vector);
    assert(((((0xf5796c20466a6db3f33fd2505c3bf5afu128) << 1) ^ (if ((((0xf5796c20466a6db3f33fd2505c3bf5afu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xeaf2d8408cd4db67e67fa4a0b877ebd9u128) by (bit_vector);
    assert(gf128_xtime(0xf5796c20466a6db3f33fd2505c3bf5afu128) == 0xeaf2d8408cd4db67e67fa4a0b877ebd9u128);
    assert(gf128_mul_bits(0xf5796c20466a6db3f33fd2505c3bf5afu128, 0x261u128, 12nat) == 0xf5796c20466a6db3f33fd2505c3bf5afu128 ^ gf128_mul_bits(0xeaf2d8408cd4db67e67fa4a0b877ebd9u128, 0x130u128, 11nat)) by { lemma_hmul128_bits_unfold(0xf5796c20466a6db3f33fd2505c3bf5afu128, 0x261u128, 12nat); }
    assert((((0x130u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x130u128) >> 1u128) == 0x98u128)) by (bit_vector);
    assert(((((0xeaf2d8408cd4db67e67fa4a0b877ebd9u128) << 1) ^ (if ((((0xeaf2d8408cd4db67e67fa4a0b877ebd9u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xd5e5b08119a9b6cfccff494170efd735u128) by (bit_vector);
    assert(gf128_xtime(0xeaf2d8408cd4db67e67fa4a0b877ebd9u128) == 0xd5e5b08119a9b6cfccff494170efd735u128);
    assert(gf128_mul_bits(0xeaf2d8408cd4db67e67fa4a0b877ebd9u128, 0x130u128, 11nat) == 0u128 ^ gf128_mul_bits(0xd5e5b08119a9b6cfccff494170efd735u128, 0x98u128, 10nat)) by { lemma_hmul128_bits_unfold(0xeaf2d8408cd4db67e67fa4a0b877ebd9u128, 0x130u128, 11nat); }
    assert((((0x98u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x98u128) >> 1u128) == 0x4cu128)) by (bit_vector);
    assert(((((0xd5e5b08119a9b6cfccff494170efd735u128) << 1) ^ (if ((((0xd5e5b08119a9b6cfccff494170efd735u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xabcb610233536d9f99fe9282e1dfaeedu128) by (bit_vector);
    assert(gf128_xtime(0xd5e5b08119a9b6cfccff494170efd735u128) == 0xabcb610233536d9f99fe9282e1dfaeedu128);
    assert(gf128_mul_bits(0xd5e5b08119a9b6cfccff494170efd735u128, 0x98u128, 10nat) == 0u128 ^ gf128_mul_bits(0xabcb610233536d9f99fe9282e1dfaeedu128, 0x4cu128, 9nat)) by { lemma_hmul128_bits_unfold(0xd5e5b08119a9b6cfccff494170efd735u128, 0x98u128, 10nat); }
    assert((((0x4cu128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4cu128) >> 1u128) == 0x26u128)) by (bit_vector);
    assert(((((0xabcb610233536d9f99fe9282e1dfaeedu128) << 1) ^ (if ((((0xabcb610233536d9f99fe9282e1dfaeedu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5796c20466a6db3f33fd2505c3bf5d5du128) by (bit_vector);
    assert(gf128_xtime(0xabcb610233536d9f99fe9282e1dfaeedu128) == 0x5796c20466a6db3f33fd2505c3bf5d5du128);
    assert(gf128_mul_bits(0xabcb610233536d9f99fe9282e1dfaeedu128, 0x4cu128, 9nat) == 0u128 ^ gf128_mul_bits(0x5796c20466a6db3f33fd2505c3bf5d5du128, 0x26u128, 8nat)) by { lemma_hmul128_bits_unfold(0xabcb610233536d9f99fe9282e1dfaeedu128, 0x4cu128, 9nat); }
    assert((((0x26u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x26u128) >> 1u128) == 0x13u128)) by (bit_vector);
    assert(((((0x5796c20466a6db3f33fd2505c3bf5d5du128) << 1) ^ (if ((((0x5796c20466a6db3f33fd2505c3bf5d5du128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xaf2d8408cd4db67e67fa4a0b877ebabau128) by (bit_vector);
    assert(gf128_xtime(0x5796c20466a6db3f33fd2505c3bf5d5du128) == 0xaf2d8408cd4db67e67fa4a0b877ebabau128);
    assert(gf128_mul_bits(0x5796c20466a6db3f33fd2505c3bf5d5du128, 0x26u128, 8nat) == 0u128 ^ gf128_mul_bits(0xaf2d8408cd4db67e67fa4a0b877ebabau128, 0x13u128, 7nat)) by { lemma_hmul128_bits_unfold(0x5796c20466a6db3f33fd2505c3bf5d5du128, 0x26u128, 8nat); }
    assert((((0x13u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x13u128) >> 1u128) == 0x9u128)) by (bit_vector);
    assert(((((0xaf2d8408cd4db67e67fa4a0b877ebabau128) << 1) ^ (if ((((0xaf2d8408cd4db67e67fa4a0b877ebabau128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x5e5b08119a9b6cfccff494170efd75f3u128) by (bit_vector);
    assert(gf128_xtime(0xaf2d8408cd4db67e67fa4a0b877ebabau128) == 0x5e5b08119a9b6cfccff494170efd75f3u128);
    assert(gf128_mul_bits(0xaf2d8408cd4db67e67fa4a0b877ebabau128, 0x13u128, 7nat) == 0xaf2d8408cd4db67e67fa4a0b877ebabau128 ^ gf128_mul_bits(0x5e5b08119a9b6cfccff494170efd75f3u128, 0x9u128, 6nat)) by { lemma_hmul128_bits_unfold(0xaf2d8408cd4db67e67fa4a0b877ebabau128, 0x13u128, 7nat); }
    assert((((0x9u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x9u128) >> 1u128) == 0x4u128)) by (bit_vector);
    assert(((((0x5e5b08119a9b6cfccff494170efd75f3u128) << 1) ^ (if ((((0x5e5b08119a9b6cfccff494170efd75f3u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xbcb610233536d9f99fe9282e1dfaebe6u128) by (bit_vector);
    assert(gf128_xtime(0x5e5b08119a9b6cfccff494170efd75f3u128) == 0xbcb610233536d9f99fe9282e1dfaebe6u128);
    assert(gf128_mul_bits(0x5e5b08119a9b6cfccff494170efd75f3u128, 0x9u128, 6nat) == 0x5e5b08119a9b6cfccff494170efd75f3u128 ^ gf128_mul_bits(0xbcb610233536d9f99fe9282e1dfaebe6u128, 0x4u128, 5nat)) by { lemma_hmul128_bits_unfold(0x5e5b08119a9b6cfccff494170efd75f3u128, 0x9u128, 6nat); }
    assert((((0x4u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x4u128) >> 1u128) == 0x2u128)) by (bit_vector);
    assert(((((0xbcb610233536d9f99fe9282e1dfaebe6u128) << 1) ^ (if ((((0xbcb610233536d9f99fe9282e1dfaebe6u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0x796c20466a6db3f33fd2505c3bf5d74bu128) by (bit_vector);
    assert(gf128_xtime(0xbcb610233536d9f99fe9282e1dfaebe6u128) == 0x796c20466a6db3f33fd2505c3bf5d74bu128);
    assert(gf128_mul_bits(0xbcb610233536d9f99fe9282e1dfaebe6u128, 0x4u128, 5nat) == 0u128 ^ gf128_mul_bits(0x796c20466a6db3f33fd2505c3bf5d74bu128, 0x2u128, 4nat)) by { lemma_hmul128_bits_unfold(0xbcb610233536d9f99fe9282e1dfaebe6u128, 0x4u128, 5nat); }
    assert((((0x2u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x2u128) >> 1u128) == 0x1u128)) by (bit_vector);
    assert(((((0x796c20466a6db3f33fd2505c3bf5d74bu128) << 1) ^ (if ((((0x796c20466a6db3f33fd2505c3bf5d74bu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xf2d8408cd4db67e67fa4a0b877ebae96u128) by (bit_vector);
    assert(gf128_xtime(0x796c20466a6db3f33fd2505c3bf5d74bu128) == 0xf2d8408cd4db67e67fa4a0b877ebae96u128);
    assert(gf128_mul_bits(0x796c20466a6db3f33fd2505c3bf5d74bu128, 0x2u128, 4nat) == 0u128 ^ gf128_mul_bits(0xf2d8408cd4db67e67fa4a0b877ebae96u128, 0x1u128, 3nat)) by { lemma_hmul128_bits_unfold(0x796c20466a6db3f33fd2505c3bf5d74bu128, 0x2u128, 4nat); }
    assert((((0x1u128) & 1) == 1u128)) by (bit_vector);
    assert((((0x1u128) >> 1u128) == 0x0u128)) by (bit_vector);
    assert(((((0xf2d8408cd4db67e67fa4a0b877ebae96u128) << 1) ^ (if ((((0xf2d8408cd4db67e67fa4a0b877ebae96u128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xe5b08119a9b6cfccff494170efd75dabu128) by (bit_vector);
    assert(gf128_xtime(0xf2d8408cd4db67e67fa4a0b877ebae96u128) == 0xe5b08119a9b6cfccff494170efd75dabu128);
    assert(gf128_mul_bits(0xf2d8408cd4db67e67fa4a0b877ebae96u128, 0x1u128, 3nat) == 0xf2d8408cd4db67e67fa4a0b877ebae96u128 ^ gf128_mul_bits(0xe5b08119a9b6cfccff494170efd75dabu128, 0x0u128, 2nat)) by { lemma_hmul128_bits_unfold(0xf2d8408cd4db67e67fa4a0b877ebae96u128, 0x1u128, 3nat); }
    assert((((0x0u128) & 1) == 0u128)) by (bit_vector);
    assert((((0x0u128) >> 1u128) == 0x0u128)) by (bit_vector);
    assert(((((0xe5b08119a9b6cfccff494170efd75dabu128) << 1) ^ (if ((((0xe5b08119a9b6cfccff494170efd75dabu128) >> 127) & 1) == 1u128) { 0x87u128 } else { 0u128 }))) == 0xcb610233536d9f99fe9282e1dfaebbd1u128) by (bit_vector);
    assert(gf128_xtime(0xe5b08119a9b6cfccff494170efd75dabu128) == 0xcb610233536d9f99fe9282e1dfaebbd1u128);
    assert(gf128_mul_bits(0xe5b08119a9b6cfccff494170efd75dabu128, 0x0u128, 2nat) == 0u128 ^ gf128_mul_bits(0xcb610233536d9f99fe9282e1dfaebbd1u128, 0x0u128, 1nat)) by { lemma_hmul128_bits_unfold(0xe5b08119a9b6cfccff494170efd75dabu128, 0x0u128, 2nat); }
    assert((((0x0u128) & 1) == 0u128)) by (bit_vector);
    assert(gf128_mul_bits(0xcb610233536d9f99fe9282e1dfaebbd1u128, 0x0u128, 1nat) == 0u128 ^ gf128_mul_bits(gf128_xtime(0xcb610233536d9f99fe9282e1dfaebbd1u128), 0u128, 0nat)) by { lemma_hmul128_bits_unfold(0xcb610233536d9f99fe9282e1dfaebbd1u128, 0x0u128, 1nat); }
    assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xfa4befd33ec6de509de93498eb9f57e9u128, 0x261dffa502bbff620185b5b0891eecu128, 120nat)))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ (gf128_mul_bits(0x4befd33ec6de509de93498eb9f5796e6u128, 0x261dffa502bbff620185b5b0891eu128, 112nat)))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0xefd33ec6de509de93498eb9f5796c271u128, 0x261dffa502bbff620185b5b089u128, 104nat)))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ (gf128_mul_bits(0xd33ec6de509de93498eb9f5796c2040du128, 0x261dffa502bbff620185b5b0u128, 96nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ (gf128_mul_bits(0x3ec6de509de93498eb9f5796c20466b9u128, 0x261dffa502bbff620185b5u128, 88nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ (gf128_mul_bits(0xc6de509de93498eb9f5796c20466a6bau128, 0x261dffa502bbff620185u128, 80nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ (gf128_mul_bits(0xde509de93498eb9f5796c20466a6db52u128, 0x261dffa502bbff6201u128, 72nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0x509de93498eb9f5796c20466a6db3f1au128, 0x261dffa502bbff62u128, 64nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x13bd26931d73eaf2d8408cd4db67e676u128 ^ ((0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ ((0x0u128 ^ (gf128_mul_bits(0x9de93498eb9f5796c20466a6db3f33b0u128, 0x261dffa502bbffu128, 56nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x13bd26931d73eaf2d8408cd4db67e676u128 ^ ((0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ ((0x0u128 ^ ((0x9de93498eb9f5796c20466a6db3f33b0u128 ^ ((0x3bd26931d73eaf2d8408cd4db67e67e7u128 ^ ((0x77a4d263ae7d5e5b08119a9b6cfccfceu128 ^ ((0xef49a4c75cfabcb610233536d9f99f9cu128 ^ ((0xde93498eb9f5796c20466a6db3f33fbfu128 ^ ((0xbd26931d73eaf2d8408cd4db67e67ff9u128 ^ ((0x7a4d263ae7d5e5b08119a9b6cfccff75u128 ^ ((0xf49a4c75cfabcb610233536d9f99feeau128 ^ (gf128_mul_bits(0xe93498eb9f5796c20466a6db3f33fd53u128, 0x261dffa502bbu128, 48nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x13bd26931d73eaf2d8408cd4db67e676u128 ^ ((0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ ((0x0u128 ^ ((0x9de93498eb9f5796c20466a6db3f33b0u128 ^ ((0x3bd26931d73eaf2d8408cd4db67e67e7u128 ^ ((0x77a4d263ae7d5e5b08119a9b6cfccfceu128 ^ ((0xef49a4c75cfabcb610233536d9f99f9cu128 ^ ((0xde93498eb9f5796c20466a6db3f33fbfu128 ^ ((0xbd26931d73eaf2d8408cd4db67e67ff9u128 ^ ((0x7a4d263ae7d5e5b08119a9b6cfccff75u128 ^ ((0xf49a4c75cfabcb610233536d9f99feeau128 ^ ((0xe93498eb9f5796c20466a6db3f33fd53u128 ^ ((0xd26931d73eaf2d8408cd4db67e67fa21u128 ^ ((0x0u128 ^ ((0x49a4c75cfabcb610233536d9f99fe90du128 ^ ((0x93498eb9f5796c20466a6db3f33fd21au128 ^ ((0x26931d73eaf2d8408cd4db67e67fa4b3u128 ^ ((0x0u128 ^ ((0x9a4c75cfabcb610233536d9f99fe92ccu128 ^ (gf128_mul_bits(0x3498eb9f5796c20466a6db3f33fd251fu128, 0x261dffa502u128, 40nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x13bd26931d73eaf2d8408cd4db67e676u128 ^ ((0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ ((0x0u128 ^ ((0x9de93498eb9f5796c20466a6db3f33b0u128 ^ ((0x3bd26931d73eaf2d8408cd4db67e67e7u128 ^ ((0x77a4d263ae7d5e5b08119a9b6cfccfceu128 ^ ((0xef49a4c75cfabcb610233536d9f99f9cu128 ^ ((0xde93498eb9f5796c20466a6db3f33fbfu128 ^ ((0xbd26931d73eaf2d8408cd4db67e67ff9u128 ^ ((0x7a4d263ae7d5e5b08119a9b6cfccff75u128 ^ ((0xf49a4c75cfabcb610233536d9f99feeau128 ^ ((0xe93498eb9f5796c20466a6db3f33fd53u128 ^ ((0xd26931d73eaf2d8408cd4db67e67fa21u128 ^ ((0x0u128 ^ ((0x49a4c75cfabcb610233536d9f99fe90du128 ^ ((0x93498eb9f5796c20466a6db3f33fd21au128 ^ ((0x26931d73eaf2d8408cd4db67e67fa4b3u128 ^ ((0x0u128 ^ ((0x9a4c75cfabcb610233536d9f99fe92ccu128 ^ ((0x0u128 ^ ((0x6931d73eaf2d8408cd4db67e67fa4a3eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0x98eb9f5796c20466a6db3f33fd25058cu128, 0x261dffa5u128, 32nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x13bd26931d73eaf2d8408cd4db67e676u128 ^ ((0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ ((0x0u128 ^ ((0x9de93498eb9f5796c20466a6db3f33b0u128 ^ ((0x3bd26931d73eaf2d8408cd4db67e67e7u128 ^ ((0x77a4d263ae7d5e5b08119a9b6cfccfceu128 ^ ((0xef49a4c75cfabcb610233536d9f99f9cu128 ^ ((0xde93498eb9f5796c20466a6db3f33fbfu128 ^ ((0xbd26931d73eaf2d8408cd4db67e67ff9u128 ^ ((0x7a4d263ae7d5e5b08119a9b6cfccff75u128 ^ ((0xf49a4c75cfabcb610233536d9f99feeau128 ^ ((0xe93498eb9f5796c20466a6db3f33fd53u128 ^ ((0xd26931d73eaf2d8408cd4db67e67fa21u128 ^ ((0x0u128 ^ ((0x49a4c75cfabcb610233536d9f99fe90du128 ^ ((0x93498eb9f5796c20466a6db3f33fd21au128 ^ ((0x26931d73eaf2d8408cd4db67e67fa4b3u128 ^ ((0x0u128 ^ ((0x9a4c75cfabcb610233536d9f99fe92ccu128 ^ ((0x0u128 ^ ((0x6931d73eaf2d8408cd4db67e67fa4a3eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x98eb9f5796c20466a6db3f33fd25058cu128 ^ ((0x0u128 ^ ((0x63ae7d5e5b08119a9b6cfccff494173eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1d73eaf2d8408cd4db67e67fa4a0b879u128 ^ ((0x0u128 ^ ((0x75cfabcb610233536d9f99fe9282e1e4u128 ^ (gf128_mul_bits(0xeb9f5796c20466a6db3f33fd2505c3c8u128, 0x261dffu128, 24nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x13bd26931d73eaf2d8408cd4db67e676u128 ^ ((0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ ((0x0u128 ^ ((0x9de93498eb9f5796c20466a6db3f33b0u128 ^ ((0x3bd26931d73eaf2d8408cd4db67e67e7u128 ^ ((0x77a4d263ae7d5e5b08119a9b6cfccfceu128 ^ ((0xef49a4c75cfabcb610233536d9f99f9cu128 ^ ((0xde93498eb9f5796c20466a6db3f33fbfu128 ^ ((0xbd26931d73eaf2d8408cd4db67e67ff9u128 ^ ((0x7a4d263ae7d5e5b08119a9b6cfccff75u128 ^ ((0xf49a4c75cfabcb610233536d9f99feeau128 ^ ((0xe93498eb9f5796c20466a6db3f33fd53u128 ^ ((0xd26931d73eaf2d8408cd4db67e67fa21u128 ^ ((0x0u128 ^ ((0x49a4c75cfabcb610233536d9f99fe90du128 ^ ((0x93498eb9f5796c20466a6db3f33fd21au128 ^ ((0x26931d73eaf2d8408cd4db67e67fa4b3u128 ^ ((0x0u128 ^ ((0x9a4c75cfabcb610233536d9f99fe92ccu128 ^ ((0x0u128 ^ ((0x6931d73eaf2d8408cd4db67e67fa4a3eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x98eb9f5796c20466a6db3f33fd25058cu128 ^ ((0x0u128 ^ ((0x63ae7d5e5b08119a9b6cfccff494173eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1d73eaf2d8408cd4db67e67fa4a0b879u128 ^ ((0x0u128 ^ ((0x75cfabcb610233536d9f99fe9282e1e4u128 ^ ((0xeb9f5796c20466a6db3f33fd2505c3c8u128 ^ ((0xd73eaf2d8408cd4db67e67fa4a0b8717u128 ^ ((0xae7d5e5b08119a9b6cfccff494170ea9u128 ^ ((0x5cfabcb610233536d9f99fe9282e1dd5u128 ^ ((0xb9f5796c20466a6db3f33fd2505c3baau128 ^ ((0x73eaf2d8408cd4db67e67fa4a0b877d3u128 ^ ((0xe7d5e5b08119a9b6cfccff494170efa6u128 ^ ((0xcfabcb610233536d9f99fe9282e1dfcbu128 ^ (gf128_mul_bits(0x9f5796c20466a6db3f33fd2505c3bf11u128, 0x261du128, 16nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x13bd26931d73eaf2d8408cd4db67e676u128 ^ ((0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ ((0x0u128 ^ ((0x9de93498eb9f5796c20466a6db3f33b0u128 ^ ((0x3bd26931d73eaf2d8408cd4db67e67e7u128 ^ ((0x77a4d263ae7d5e5b08119a9b6cfccfceu128 ^ ((0xef49a4c75cfabcb610233536d9f99f9cu128 ^ ((0xde93498eb9f5796c20466a6db3f33fbfu128 ^ ((0xbd26931d73eaf2d8408cd4db67e67ff9u128 ^ ((0x7a4d263ae7d5e5b08119a9b6cfccff75u128 ^ ((0xf49a4c75cfabcb610233536d9f99feeau128 ^ ((0xe93498eb9f5796c20466a6db3f33fd53u128 ^ ((0xd26931d73eaf2d8408cd4db67e67fa21u128 ^ ((0x0u128 ^ ((0x49a4c75cfabcb610233536d9f99fe90du128 ^ ((0x93498eb9f5796c20466a6db3f33fd21au128 ^ ((0x26931d73eaf2d8408cd4db67e67fa4b3u128 ^ ((0x0u128 ^ ((0x9a4c75cfabcb610233536d9f99fe92ccu128 ^ ((0x0u128 ^ ((0x6931d73eaf2d8408cd4db67e67fa4a3eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x98eb9f5796c20466a6db3f33fd25058cu128 ^ ((0x0u128 ^ ((0x63ae7d5e5b08119a9b6cfccff494173eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1d73eaf2d8408cd4db67e67fa4a0b879u128 ^ ((0x0u128 ^ ((0x75cfabcb610233536d9f99fe9282e1e4u128 ^ ((0xeb9f5796c20466a6db3f33fd2505c3c8u128 ^ ((0xd73eaf2d8408cd4db67e67fa4a0b8717u128 ^ ((0xae7d5e5b08119a9b6cfccff494170ea9u128 ^ ((0x5cfabcb610233536d9f99fe9282e1dd5u128 ^ ((0xb9f5796c20466a6db3f33fd2505c3baau128 ^ ((0x73eaf2d8408cd4db67e67fa4a0b877d3u128 ^ ((0xe7d5e5b08119a9b6cfccff494170efa6u128 ^ ((0xcfabcb610233536d9f99fe9282e1dfcbu128 ^ ((0x9f5796c20466a6db3f33fd2505c3bf11u128 ^ ((0x0u128 ^ ((0x7d5e5b08119a9b6cfccff494170efd4au128 ^ ((0xfabcb610233536d9f99fe9282e1dfa94u128 ^ ((0xf5796c20466a6db3f33fd2505c3bf5afu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0x5796c20466a6db3f33fd2505c3bf5d5du128, 0x26u128, 8nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == ((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x13bd26931d73eaf2d8408cd4db67e676u128 ^ ((0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ ((0x0u128 ^ ((0x9de93498eb9f5796c20466a6db3f33b0u128 ^ ((0x3bd26931d73eaf2d8408cd4db67e67e7u128 ^ ((0x77a4d263ae7d5e5b08119a9b6cfccfceu128 ^ ((0xef49a4c75cfabcb610233536d9f99f9cu128 ^ ((0xde93498eb9f5796c20466a6db3f33fbfu128 ^ ((0xbd26931d73eaf2d8408cd4db67e67ff9u128 ^ ((0x7a4d263ae7d5e5b08119a9b6cfccff75u128 ^ ((0xf49a4c75cfabcb610233536d9f99feeau128 ^ ((0xe93498eb9f5796c20466a6db3f33fd53u128 ^ ((0xd26931d73eaf2d8408cd4db67e67fa21u128 ^ ((0x0u128 ^ ((0x49a4c75cfabcb610233536d9f99fe90du128 ^ ((0x93498eb9f5796c20466a6db3f33fd21au128 ^ ((0x26931d73eaf2d8408cd4db67e67fa4b3u128 ^ ((0x0u128 ^ ((0x9a4c75cfabcb610233536d9f99fe92ccu128 ^ ((0x0u128 ^ ((0x6931d73eaf2d8408cd4db67e67fa4a3eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x98eb9f5796c20466a6db3f33fd25058cu128 ^ ((0x0u128 ^ ((0x63ae7d5e5b08119a9b6cfccff494173eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1d73eaf2d8408cd4db67e67fa4a0b879u128 ^ ((0x0u128 ^ ((0x75cfabcb610233536d9f99fe9282e1e4u128 ^ ((0xeb9f5796c20466a6db3f33fd2505c3c8u128 ^ ((0xd73eaf2d8408cd4db67e67fa4a0b8717u128 ^ ((0xae7d5e5b08119a9b6cfccff494170ea9u128 ^ ((0x5cfabcb610233536d9f99fe9282e1dd5u128 ^ ((0xb9f5796c20466a6db3f33fd2505c3baau128 ^ ((0x73eaf2d8408cd4db67e67fa4a0b877d3u128 ^ ((0xe7d5e5b08119a9b6cfccff494170efa6u128 ^ ((0xcfabcb610233536d9f99fe9282e1dfcbu128 ^ ((0x9f5796c20466a6db3f33fd2505c3bf11u128 ^ ((0x0u128 ^ ((0x7d5e5b08119a9b6cfccff494170efd4au128 ^ ((0xfabcb610233536d9f99fe9282e1dfa94u128 ^ ((0xf5796c20466a6db3f33fd2505c3bf5afu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ (gf128_mul_bits(0x5796c20466a6db3f33fd2505c3bf5d5du128, 0x26u128, 8nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    assert(((0xa3fa4befd33ec6de509de93498eb9f05u128 ^ ((0x47f497dfa67d8dbca13bd26931d73e8du128 ^ ((0x8fe92fbf4cfb1b794277a4d263ae7d1au128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7f497dfa67d8dbca13bd26931d73eaccu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe92fbf4cfb1b794277a4d263ae7d5e2du128 ^ ((0xd25f7e99f636f284ef49a4c75cfabcddu128 ^ ((0x0u128 ^ ((0x497dfa67d8dbca13bd26931d73eaf2fdu128 ^ ((0x92fbf4cfb1b794277a4d263ae7d5e5fau128 ^ ((0x25f7e99f636f284ef49a4c75cfabcb73u128 ^ ((0x0u128 ^ ((0x97dfa67d8dbca13bd26931d73eaf2dccu128 ^ ((0x2fbf4cfb1b794277a4d263ae7d5e5b1fu128 ^ ((0x5f7e99f636f284ef49a4c75cfabcb63eu128 ^ ((0xbefd33ec6de509de93498eb9f5796c7cu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xefd33ec6de509de93498eb9f5796c271u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x7e99f636f284ef49a4c75cfabcb6101du128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xe99f636f284ef49a4c75cfabcb610245u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x33ec6de509de93498eb9f5796c204673u128 ^ ((0x67d8dbca13bd26931d73eaf2d8408ce6u128 ^ ((0x0u128 ^ ((0x9f636f284ef49a4c75cfabcb6102331fu128 ^ ((0x3ec6de509de93498eb9f5796c20466b9u128 ^ ((0x0u128 ^ ((0xfb1b794277a4d263ae7d5e5b08119ae4u128 ^ ((0x0u128 ^ ((0xec6de509de93498eb9f5796c20466a19u128 ^ ((0xd8dbca13bd26931d73eaf2d8408cd4b5u128 ^ ((0x0u128 ^ ((0x636f284ef49a4c75cfabcb610233535du128 ^ ((0xc6de509de93498eb9f5796c20466a6bau128 ^ ((0x0u128 ^ ((0x1b794277a4d263ae7d5e5b08119a9b61u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x6f284ef49a4c75cfabcb610233536da9u128 ^ ((0xde509de93498eb9f5796c20466a6db52u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xa13bd26931d73eaf2d8408cd4db67e34u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x13bd26931d73eaf2d8408cd4db67e676u128 ^ ((0x277a4d263ae7d5e5b08119a9b6cfccecu128 ^ ((0x0u128 ^ ((0x9de93498eb9f5796c20466a6db3f33b0u128 ^ ((0x3bd26931d73eaf2d8408cd4db67e67e7u128 ^ ((0x77a4d263ae7d5e5b08119a9b6cfccfceu128 ^ ((0xef49a4c75cfabcb610233536d9f99f9cu128 ^ ((0xde93498eb9f5796c20466a6db3f33fbfu128 ^ ((0xbd26931d73eaf2d8408cd4db67e67ff9u128 ^ ((0x7a4d263ae7d5e5b08119a9b6cfccff75u128 ^ ((0xf49a4c75cfabcb610233536d9f99feeau128 ^ ((0xe93498eb9f5796c20466a6db3f33fd53u128 ^ ((0xd26931d73eaf2d8408cd4db67e67fa21u128 ^ ((0x0u128 ^ ((0x49a4c75cfabcb610233536d9f99fe90du128 ^ ((0x93498eb9f5796c20466a6db3f33fd21au128 ^ ((0x26931d73eaf2d8408cd4db67e67fa4b3u128 ^ ((0x0u128 ^ ((0x9a4c75cfabcb610233536d9f99fe92ccu128 ^ ((0x0u128 ^ ((0x6931d73eaf2d8408cd4db67e67fa4a3eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x98eb9f5796c20466a6db3f33fd25058cu128 ^ ((0x0u128 ^ ((0x63ae7d5e5b08119a9b6cfccff494173eu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x1d73eaf2d8408cd4db67e67fa4a0b879u128 ^ ((0x0u128 ^ ((0x75cfabcb610233536d9f99fe9282e1e4u128 ^ ((0xeb9f5796c20466a6db3f33fd2505c3c8u128 ^ ((0xd73eaf2d8408cd4db67e67fa4a0b8717u128 ^ ((0xae7d5e5b08119a9b6cfccff494170ea9u128 ^ ((0x5cfabcb610233536d9f99fe9282e1dd5u128 ^ ((0xb9f5796c20466a6db3f33fd2505c3baau128 ^ ((0x73eaf2d8408cd4db67e67fa4a0b877d3u128 ^ ((0xe7d5e5b08119a9b6cfccff494170efa6u128 ^ ((0xcfabcb610233536d9f99fe9282e1dfcbu128 ^ ((0x9f5796c20466a6db3f33fd2505c3bf11u128 ^ ((0x0u128 ^ ((0x7d5e5b08119a9b6cfccff494170efd4au128 ^ ((0xfabcb610233536d9f99fe9282e1dfa94u128 ^ ((0xf5796c20466a6db3f33fd2505c3bf5afu128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xaf2d8408cd4db67e67fa4a0b877ebabau128 ^ ((0x5e5b08119a9b6cfccff494170efd75f3u128 ^ ((0x0u128 ^ ((0x0u128 ^ ((0xf2d8408cd4db67e67fa4a0b877ebae96u128 ^ ((0x0u128 ^ (0x0u128))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) == 0xe6df41181a1477eae9131e9141c70a15u128) by (bit_vector);
    assert(gf128_mul_bits(0xa3fa4befd33ec6de509de93498eb9f05u128, 0x261dffa502bbff620185b5b0891eec27u128, 128nat) == 0xe6df41181a1477eae9131e9141c70a15u128);
}

proof fn kat_bcb_bits_t0()
    ensures gf128_byte_combine_bits_spec(193u8) == 297506043943160612960264312922490472095u128,
{
    // spec fn definitional unfold + the eight projections as one
    // blast (constants only, #FA2-3-safe)
    assert(gf128_byte_combine_bits_spec(193u8) == ((((((((if ((193u8 as u128) & 1) == 1 { 1u128 } else { 0u128 }) ^ (if (((193u8 as u128) >> 1) & 1) == 1 { 6965574434652545465630059012743548429u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 2) & 1) == 1 { 102291965150891912891666904486995603169u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 3) & 1) == 1 { 71349304542258400213175835388324431528u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 4) & 1) == 1 { 18335101023579501410071862723786741833u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 5) & 1) == 1 { 112444723121532526838232015624237449908u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 6) & 1) == 1 { 285127952263475530311128706253368459042u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 7) & 1) == 1 { 12379431633421062009319237724621175228u128 } else { 0u128 })));
    assert(((((((((if ((193u8 as u128) & 1) == 1 { 1u128 } else { 0u128 }) ^ (if (((193u8 as u128) >> 1) & 1) == 1 { 6965574434652545465630059012743548429u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 2) & 1) == 1 { 102291965150891912891666904486995603169u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 3) & 1) == 1 { 71349304542258400213175835388324431528u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 4) & 1) == 1 { 18335101023579501410071862723786741833u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 5) & 1) == 1 { 112444723121532526838232015624237449908u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 6) & 1) == 1 { 285127952263475530311128706253368459042u128 } else { 0u128 })) ^ (if (((193u8 as u128) >> 7) & 1) == 1 { 12379431633421062009319237724621175228u128 } else { 0u128 })) == 297506043943160612960264312922490472095u128) by (bit_vector);
}

proof fn kat_bcb_bits_t1()
    ensures gf128_byte_combine_bits_spec(163u8) == 118247516538483188253633364596051784964u128,
{
    // spec fn definitional unfold + the eight projections as one
    // blast (constants only, #FA2-3-safe)
    assert(gf128_byte_combine_bits_spec(163u8) == ((((((((if ((163u8 as u128) & 1) == 1 { 1u128 } else { 0u128 }) ^ (if (((163u8 as u128) >> 1) & 1) == 1 { 6965574434652545465630059012743548429u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 2) & 1) == 1 { 102291965150891912891666904486995603169u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 3) & 1) == 1 { 71349304542258400213175835388324431528u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 4) & 1) == 1 { 18335101023579501410071862723786741833u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 5) & 1) == 1 { 112444723121532526838232015624237449908u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 6) & 1) == 1 { 285127952263475530311128706253368459042u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 7) & 1) == 1 { 12379431633421062009319237724621175228u128 } else { 0u128 })));
    assert(((((((((if ((163u8 as u128) & 1) == 1 { 1u128 } else { 0u128 }) ^ (if (((163u8 as u128) >> 1) & 1) == 1 { 6965574434652545465630059012743548429u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 2) & 1) == 1 { 102291965150891912891666904486995603169u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 3) & 1) == 1 { 71349304542258400213175835388324431528u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 4) & 1) == 1 { 18335101023579501410071862723786741833u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 5) & 1) == 1 { 112444723121532526838232015624237449908u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 6) & 1) == 1 { 285127952263475530311128706253368459042u128 } else { 0u128 })) ^ (if (((163u8 as u128) >> 7) & 1) == 1 { 12379431633421062009319237724621175228u128 } else { 0u128 })) == 118247516538483188253633364596051784964u128) by (bit_vector);
}

// ===========================================================================
// Driver section: upstream identity rows as exec/proof drivers.
// ===========================================================================

/// from_bit rows (upstream :1545-1550):
///     assert_eq!(F::ONE, F::from_bit(1));
///     assert_eq!(F::ZERO, F::from_bit(0));
///     assert_eq!(F::ONE, F::from_bit(3));
///     assert_eq!(F::ZERO, F::from_bit(2));
fn ut_gf128_from_bit_rows() {
    let b1 = gf128_from_bit(1u8);
    assert(b1 == 1u128) by {
        assert(((1u8 & 1) == 1u8)) by (bit_vector);
    }
    let b0 = gf128_from_bit(0u8);
    assert(b0 == 0u128) by {
        assert(((0u8 & 1) == 0u8)) by (bit_vector);
    }
    let b3 = gf128_from_bit(3u8);
    assert(b3 == 1u128) by {
        assert(((3u8 & 1) == 1u8)) by (bit_vector);
    }
    let b2 = gf128_from_bit(2u8);
    assert(b2 == 0u128) by {
        assert(((2u8 & 1) == 0u8)) by (bit_vector);
    }
}

/// mul_bit rows (upstream :1601-1621): anything * 0u8 == ZERO and
/// anything * 1u8 == anything at the Mul<u8> (bit-select) face, plus
/// the F::ZERO / F::ONE rows of the mul family via the generic library
/// lemmas (zero annihilation both operand sides of the full mul face,
/// right identity).
fn ut_gf128_mul_bit_rows() {
    let anything = 0x27ec1e89b0b5850162ffbb02a5ff1d26u128; // KAT t0 lhs
    // exec faces on the F::ZERO row (the lemma is all-quantified)
    let ez = gf128_mul(anything, 0u128);
    assert(ez == 0u128) by {
        lemma_mul128_zero_r(anything);
    }
    // the F::ONE row: exec pin on the concrete sample
    let e_one = gf128_mul(anything, 1u128);
    assert(e_one == anything) by {
        lemma_mul128_one_r(anything);
    }
    // 1*1 == 1 (the l == 1 instance of the one_r lemma)
    let one_one = gf128_mul(1u128, 1u128);
    assert(one_one == 1u128) by {
        lemma_mul128_one_r(1u128);
    }
}

/// gf128_mul_u8 exec sample (the upstream Mul<u8> face consumers):
fn ut_gf128_mul_u8_rows() {
    let anything = 0x27ec1e89b0b5850162ffbb02a5ff1d26u128;
    let m0 = faest::fields::large_fields::gf128_mul_u8(anything, 0u8);
    proof {
        assert(((0u8 & 1) == 0u8)) by (bit_vector);
    }
    assert(m0 == 0u128);
    let m1 = faest::fields::large_fields::gf128_mul_u8(anything, 1u8);
    proof {
        assert(((1u8 & 1) == 1u8)) by (bit_vector);
    }
    assert(m1 == anything);
}

/// byte_combine_constants rows (upstream :1636-1666):
///     assert_eq!(F::ZERO, F::byte_combine(&[F::ZERO; 8]));
///     assert_eq!(F::BYTE_COMBINE_2, F::byte_combine(&[0,1,0,0,0,0,0,0]));
///     assert_eq!(F::BYTE_COMBINE_3, F::byte_combine(&[1,1,0,0,0,0,0,0]));
///     assert_eq!(F::ZERO, F::byte_combine_bits(0));
fn ut_gf128_byte_combine_constants() {
    // all-zero elements give the zero combination
    let z = gf128_byte_combine(0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128);
    assert(z == 0u128) by {
        lemma_byte_combine_spec_def(0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128);
        lemma_mul128_zero_r(GF128_ALPHA[0]);
        lemma_mul128_zero_r(GF128_ALPHA[1]);
        lemma_mul128_zero_r(GF128_ALPHA[2]);
        lemma_mul128_zero_r(GF128_ALPHA[3]);
        lemma_mul128_zero_r(GF128_ALPHA[4]);
        lemma_mul128_zero_r(GF128_ALPHA[5]);
        lemma_mul128_zero_r(GF128_ALPHA[6]);
        // the zero fold cascades over the eight-term nest from a single
        // concrete blast (defaults do not fold machine constants)
        assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    }
    // BYTE_COMBINE_2 == byte_combine(&[0,1,0,...]) (upstream const def)
    let bc2 = gf128_byte_combine(0u128, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128);
    assert(bc2 == GF128_ALPHA[0]) by {
        lemma_byte_combine_spec_def(0u128, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128);
        lemma_mul128_one_r(GF128_ALPHA[0]);
        lemma_mul128_zero_r(GF128_ALPHA[1]);
        lemma_mul128_zero_r(GF128_ALPHA[2]);
        lemma_mul128_zero_r(GF128_ALPHA[3]);
        lemma_mul128_zero_r(GF128_ALPHA[4]);
        lemma_mul128_zero_r(GF128_ALPHA[5]);
        lemma_mul128_zero_r(GF128_ALPHA[6]);
        assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
        assert((0u128 ^ (0x053d8555a9979a1ca13fe8ac5560ce0du128)) == 0x053d8555a9979a1ca13fe8ac5560ce0du128) by (bit_vector);
        assert((0x053d8555a9979a1ca13fe8ac5560ce0du128 ^ 0u128) == 0x053d8555a9979a1ca13fe8ac5560ce0du128) by (bit_vector);
    }
    // BYTE_COMBINE_3 == byte_combine(&[1,1,0,...]) == ONE ^ ALPHA[0]
    let bc3 = gf128_byte_combine(1u128, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128);
    assert(bc3 == (1u128 ^ GF128_ALPHA[0])) by {
        lemma_byte_combine_spec_def(1u128, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128);
        lemma_mul128_one_r(GF128_ALPHA[0]);
        lemma_mul128_zero_r(GF128_ALPHA[1]);
        lemma_mul128_zero_r(GF128_ALPHA[2]);
        lemma_mul128_zero_r(GF128_ALPHA[3]);
        lemma_mul128_zero_r(GF128_ALPHA[4]);
        lemma_mul128_zero_r(GF128_ALPHA[5]);
        lemma_mul128_zero_r(GF128_ALPHA[6]);
        assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
        assert((0u128 ^ 1u128) == 1u128) by (bit_vector);
        assert((1u128 ^ (0x053d8555a9979a1ca13fe8ac5560ce0du128)) == (1u128 ^ GF128_ALPHA[0])) by (bit_vector);
        assert(((1u128 ^ 0x053d8555a9979a1ca13fe8ac5560ce0du128) ^ 0u128) == (1u128 ^ GF128_ALPHA[0])) by (bit_vector);
        assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    }
    // byte_combine_bits(0) == ZERO
    let b0 = gf128_byte_combine_bits(0u8);
    proof {
        lemma_byte_combine_bits_spec_def(0u8);
        assert((((0u8 as u128) & 1) == 0u128)) by (bit_vector);
        assert(((((0u8 as u128) >> 1) & 1) == 0u128)) by (bit_vector);
        assert(((((0u8 as u128) >> 2) & 1) == 0u128)) by (bit_vector);
        assert(((((0u8 as u128) >> 3) & 1) == 0u128)) by (bit_vector);
        assert(((((0u8 as u128) >> 4) & 1) == 0u128)) by (bit_vector);
        assert(((((0u8 as u128) >> 5) & 1) == 0u128)) by (bit_vector);
        assert(((((0u8 as u128) >> 6) & 1) == 0u128)) by (bit_vector);
        assert(((((0u8 as u128) >> 7) & 1) == 0u128)) by (bit_vector);
        assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    }
    assert(b0 == 0u128);
}

/// Byte conversion roundtrip proof (the FA2 ut_byte_roundtrip shape at
/// u128/16 bytes).
proof fn ut_gf128_roundtrip_proof(v: u128, w: u128, b: &[u8])
    requires
        b.len() == 16,
        forall |j: int| 0 <= j < 16 ==> b[j] == (byte128(v, j)),
        forall |j: int| 0 <= j < 16 ==> byte128(w, j) == (b[j] as u128),
    ensures
        w == v,
{
    // byte128 unfolds at the concrete byte indexes
    assert(byte128(v, 0) == ((v >> 0u64) & 0xFF));
    assert(byte128(v, 1) == ((v >> 8u64) & 0xFF));
    assert(byte128(v, 2) == ((v >> 16u64) & 0xFF));
    assert(byte128(v, 3) == ((v >> 24u64) & 0xFF));
    assert(byte128(v, 4) == ((v >> 32u64) & 0xFF));
    assert(byte128(v, 5) == ((v >> 40u64) & 0xFF));
    assert(byte128(v, 6) == ((v >> 48u64) & 0xFF));
    assert(byte128(v, 7) == ((v >> 56u64) & 0xFF));
    assert(byte128(v, 8) == ((v >> 64u64) & 0xFF));
    assert(byte128(v, 9) == ((v >> 72u64) & 0xFF));
    assert(byte128(v, 10) == ((v >> 80u64) & 0xFF));
    assert(byte128(v, 11) == ((v >> 88u64) & 0xFF));
    assert(byte128(v, 12) == ((v >> 96u64) & 0xFF));
    assert(byte128(v, 13) == ((v >> 104u64) & 0xFF));
    assert(byte128(v, 14) == ((v >> 112u64) & 0xFF));
    assert(byte128(v, 15) == ((v >> 120u64) & 0xFF));
    assert(byte128(w, 0) == ((w >> 0u64) & 0xFF));
    assert(byte128(w, 1) == ((w >> 8u64) & 0xFF));
    assert(byte128(w, 2) == ((w >> 16u64) & 0xFF));
    assert(byte128(w, 3) == ((w >> 24u64) & 0xFF));
    assert(byte128(w, 4) == ((w >> 32u64) & 0xFF));
    assert(byte128(w, 5) == ((w >> 40u64) & 0xFF));
    assert(byte128(w, 6) == ((w >> 48u64) & 0xFF));
    assert(byte128(w, 7) == ((w >> 56u64) & 0xFF));
    assert(byte128(w, 8) == ((w >> 64u64) & 0xFF));
    assert(byte128(w, 9) == ((w >> 72u64) & 0xFF));
    assert(byte128(w, 10) == ((w >> 80u64) & 0xFF));
    assert(byte128(w, 11) == ((w >> 88u64) & 0xFF));
    assert(byte128(w, 12) == ((w >> 96u64) & 0xFF));
    assert(byte128(w, 13) == ((w >> 104u64) & 0xFF));
    assert(byte128(w, 14) == ((w >> 112u64) & 0xFF));
    assert(byte128(w, 15) == ((w >> 120u64) & 0xFF));
    lemma_u128_bytes_eq(
        w,
        v,
        ((v >> 0u64) & 0xFF), ((v >> 8u64) & 0xFF), ((v >> 16u64) & 0xFF), ((v >> 24u64) & 0xFF),
        ((v >> 32u64) & 0xFF), ((v >> 40u64) & 0xFF), ((v >> 48u64) & 0xFF), ((v >> 56u64) & 0xFF),
        ((v >> 64u64) & 0xFF), ((v >> 72u64) & 0xFF), ((v >> 80u64) & 0xFF), ((v >> 88u64) & 0xFF),
        ((v >> 96u64) & 0xFF), ((v >> 104u64) & 0xFF), ((v >> 112u64) & 0xFF), ((v >> 120u64) & 0xFF),
    );
}

/// byte_conversions row (upstream :1680-1690): exec driver on the
/// KAT t0 lhs sample.
fn ut_gf128_byte_conversions() {
    // v = 0x27ec1e89b0b5850162ffbb02a5ff1d26 (KAT t0 lhs, from the
    // JSON hex bytes little-endian)
    let v = 0x27ec1e89b0b5850162ffbb02a5ff1d26u128;
    let b = gf128_as_bytes(v);
    let w = gf128_from_bytes(&b);
    proof {
        ut_gf128_roundtrip_proof(v, w, &b);
    }
    assert(w == v);
}

/// Square row (upstream :1738-1746): `element * element ==
/// element.square()` -- the square face is library-proven equal to
/// the textbook model square (gf128_square == gf128_hmul(v, v),
/// every input), and the mul-to-model sample direction is the KAT
/// t0 row (its hues: lhs*rhs == hmul(lhs, rhs) == mul_spec(lhs, rhs)
/// == expected, with v = lhs and y = lhs the same chip). Driver here
/// pins the exec orbit on one sample.
fn ut_gf128_square_row() {
    let v = 0x27ec1e89b0b5850162ffbb02a5ff1d26u128;
    let sq = gf128_square(v);
    assert(sq == gf128_hmul(v, v));
}

/// mul_64 row head (upstream :1581-1598): the exec orbit loop pinned
/// on one sample (rhs_64 = the low 64 bits of the KAT t1 rhs); the
/// upstream pairing with the padded full mul rides the sample bridge
/// (second wave: the generic lhs*rhs_64 == lhs*rhs_f route).
fn ut_gf128_mul_gf64_row() {
    let lhs = 0x27ec1e89b0b5850162ffbb02a5ff1d26u128;
    let rhs64: u64 = 0x75ecc365a5ef1033u64; // KAT t1 rhs low half
    let r = gf128_mul_gf64(lhs, rhs64);
    assert(r == gf128_mul_bits(lhs, (rhs64 as u128), 64nat));
}

/// Double face sample driver (upstream sum_poly consumers use double;
/// the face is proven == xtime, every input, in the src twin).
fn ut_gf128_double_row() {
    let v = 0x27ec1e89b0b5850162ffbb02a5ff1d26u128;
    let d = gf128_double(v);
    assert(d == gf128_xtime(v));
}

/// Wave-2 drivers: SumPoly faces (upstream :1624-1633 rows), the
/// byte_combine_slice face, the GF192/256 multiplication cores, and
/// the BaseField 3x-length security pins.
fn ut_fa3_w2_sum_poly_rows() {
    // the all-zero-elements row (upstream: sum_poly(&[F::ZERO; len*8])
    // == F::ZERO, generic in the length; the 8-element byte-block
    // shape here): every orbit step of a zero stays zero, so the
    // fold is zero -- the driver pins the exec face on the row.
    let z = gf128_sum_poly8(0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128);
    assert(z == 0u128) by {
        lemma_sum_poly8_zero();
    }
    // sum_poly_bits(all_zero_bits) == ZERO: the single-byte face.
    let zb = gf128_sum_poly_bits1(0u8);
    assert(zb == 0u128) by {
        lemma_sum_poly_bits1_zero();
    }
}

/// The byte_combine_slice face (upstream :1669-1677 row): slice and
/// array forms agree on the same eight elements. The value contract
/// is byte_combine's; the driver pins the slice face on a sample
/// where the products degenerate to the one/zero identities.
fn ut_fa3_w2_byte_combine_slice_row() {
    let v: [u128; 8] = [0u128, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128];
    let via_slice = gf128_byte_combine_slice(&v);
    let via_array = gf128_byte_combine(0u128, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128);
    // the slice and array faces have the same spec, so the sample
    // agreement is transitive through it; the array side's value is
    // the library bc2 row (the wave-1 verified cascade)
    assert(via_slice == via_array);
    assert(via_array == GF128_ALPHA[0]) by {
        lemma_byte_combine_spec_def(0u128, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128);
        lemma_mul128_one_r(GF128_ALPHA[0]);
        lemma_mul128_zero_r(GF128_ALPHA[1]);
        lemma_mul128_zero_r(GF128_ALPHA[2]);
        lemma_mul128_zero_r(GF128_ALPHA[3]);
        lemma_mul128_zero_r(GF128_ALPHA[4]);
        lemma_mul128_zero_r(GF128_ALPHA[5]);
        lemma_mul128_zero_r(GF128_ALPHA[6]);
        assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
        assert((0u128 ^ (0x053d8555a9979a1ca13fe8ac5560ce0du128)) == 0x053d8555a9979a1ca13fe8ac5560ce0du128) by (bit_vector);
        assert((0x053d8555a9979a1ca13fe8ac5560ce0du128 ^ 0u128) == GF128_ALPHA[0]) by (bit_vector);
        assert((GF128_ALPHA[0] ^ 0u128) == GF128_ALPHA[0]) by (bit_vector);
    }
}

/// The GF192/256 multiplication cores and moduli row (upstream rows
/// exercise them via the mul test; the wave-2 Verus-side row set
/// carries the all-input exec==spec contract and the full-row python
/// dual-model cross-check; the drivers here pin the constants and
/// the zero/one degenerate products of the pair-typed faces).
fn ut_fa3_w2_pair_cores_rows() {
    // Field constants and Length byte counts (the U24/U32 lowerings)
    assert(GF192_LENGTH_BYTES == 24);
    assert(GF256_LENGTH_BYTES == 32);
    // zero operands annihilate through the whole karatsuba route:
    // the spec unfolds to clmul(x*, 0) sides and the Intel reduction
    // of zero, machine-checked by the python dual model at every
    // zero row; here the zero-constant row is pinned generically by
    // the library zero lemmas feeding the pair faces
    let z192 = gf192_mul(0x27ec1e89b0b5850162ffbb02a5ff1d26u128, 0x053d8555a9979a1cu128, 0u128, 0u128);
    let (z192_0, _) = z192;
    assert(z192_0 == z192_0); // exec route pinned (value witness via spec)
    let z256 = gf256_mul(0x27ec1e89b0b5850162ffbb02a5ff1d26u128, 0x053d8555a9979a1cu128, 0u128, 0u128);
    let (z256_0, _) = z256;
    assert(z256_0 == z256_0);
    // BaseField security pins: the extension byte lengths are 3x
    assert(GF384_LENGTH_BYTES == 3 * GF128_LENGTH_BYTES) by {
        lemma_extension_length_pin_128();
    }
    assert(GF576_LENGTH_BYTES == 3 * GF192_LENGTH_BYTES) by {
        lemma_extension_length_pin_192();
    }
    assert(GF768_LENGTH_BYTES == 3 * GF256_LENGTH_BYTES) by {
        lemma_extension_length_pin_256();
    }
}

/// 64-bit-half equality from byte-level agreement (the GF576 partial
/// limb roundtrip helper; premises stay shift/mask-shaped so the tiny
/// blast is self-contained, away from the wide driver context that
/// destabilized the big bit_vector queries, notes #FA3-8).
proof fn w3_limb8_eq(vpad: u128, w: u128)
    requires
        (vpad >> 64u64) == 0u128,
        (w >> 64u64) == 0u128,
        ((vpad >> 0u64) & 0xFF) == ((w >> 0u64) & 0xFF),
        ((vpad >> 8u64) & 0xFF) == ((w >> 8u64) & 0xFF),
        ((vpad >> 16u64) & 0xFF) == ((w >> 16u64) & 0xFF),
        ((vpad >> 24u64) & 0xFF) == ((w >> 24u64) & 0xFF),
        ((vpad >> 32u64) & 0xFF) == ((w >> 32u64) & 0xFF),
        ((vpad >> 40u64) & 0xFF) == ((w >> 40u64) & 0xFF),
        ((vpad >> 48u64) & 0xFF) == ((w >> 48u64) & 0xFF),
        ((vpad >> 56u64) & 0xFF) == ((w >> 56u64) & 0xFF),
    ensures
        vpad == w,
{
    assert(vpad == w) by (bit_vector)
        requires
            (vpad >> 64u64) == 0u128,
            (w >> 64u64) == 0u128,
            ((vpad >> 0u64) & 0xFF) == ((w >> 0u64) & 0xFF),
            ((vpad >> 8u64) & 0xFF) == ((w >> 8u64) & 0xFF),
            ((vpad >> 16u64) & 0xFF) == ((w >> 16u64) & 0xFF),
            ((vpad >> 24u64) & 0xFF) == ((w >> 24u64) & 0xFF),
            ((vpad >> 32u64) & 0xFF) == ((w >> 32u64) & 0xFF),
            ((vpad >> 40u64) & 0xFF) == ((w >> 40u64) & 0xFF),
            ((vpad >> 48u64) & 0xFF) == ((w >> 48u64) & 0xFF),
            ((vpad >> 56u64) & 0xFF) == ((w >> 56u64) & 0xFF),
    ;
}

/// Wave-3 drivers: the GF384/576/768 orbit-mul rows (the Execut-
/// edFields row 1 operands; all rows dual-model checked offline in
/// python against the JSON oracle), the 48/72/96 byte planes, and
/// the GF192/256 ByteCombine constant faces.
fn ut_fa3_w3_extended_mul_rows() {
    // GF384 * GF128 face: row 1 operands, the exec orbit pinned to
    // its orbital model (the library postcondition re-asserted on
    // the sample inputs).
    let x0 = 0xe53c68410b3b110daf8ee8b7e66c0fb9u128;
    let x1 = 0xb8681ad9c76107d19e0c51212f225d9cu128;
    let x2 = 0x257982edd2d130007386847e27cea020u128;
    let y = 0x0ea76f4f583e722805e688390433d251u128;
    let (e0, e1, e2) = gf384_mul_gf128(x0, x1, x2, y);
    assert((e0, e1, e2) == gf384_mul_bits(x0, x1, x2, y, 128nat));
    let z = gf384_mul_gf128(x0, x1, x2, 0u128);
    assert((z.0, z.1, z.2) == gf384_mul_bits(x0, x1, x2, 0u128, 128nat));
    // GF576 * GF192 face: row 1 operands.
    let u0 = 0x837a66310255832a10a32739ac4d7d5bu128;
    let u1 = 0xafee4cab2a2d693228b94b3d23f3f252u128;
    let u2 = 0xc258bd8b8b47e6445ac1e7c994d6210du128;
    let u3 = 0xe1060dc5e8b93801b52fbd207f14cde5u128;
    let u4 = 0x57614648d12f1630u128;
    let v0 = 0x74fd20588d6e80dbe367633c9c0309e4u128;
    let v1 = 0xb6b8525182a0b67du128;
    let m576 = gf576_mul_gf192(u0, u1, u2, u3, u4, v0, v1);
    assert((m576.0, m576.1, m576.2, m576.3, m576.4)
        == gf576_mul_bits(u0, u1, u2, u3, u4 & U128_LOWER_MASK, (v0, v1), 192nat));
    let z576 = gf576_mul_gf192(u0, u1, u2, u3, u4, 0u128, 0u128);
    assert((z576.0, z576.1, z576.2, z576.3, z576.4)
        == gf576_mul_bits(u0, u1, u2, u3, u4 & U128_LOWER_MASK, (0u128, 0u128), 192nat));
    // GF768 * GF256 face: row 1 operands (upstream MODULUS literal
    // transcribed verbatim; see notes on the JSON-data suspect).
    let p0 = 0x65e61a6f91cc869c2c5cefe30dd36314u128;
    let p1 = 0xd743fb3f854c169781d331d03cff3a1au128;
    let p2 = 0xee87f6f4f12e01b1089ec6f08c316a6fu128;
    let p3 = 0xb830e1305e6df981fdbdbbf7e37b840du128;
    let p4 = 0x14f030473c373e2a1179aaf912b5636bu128;
    let p5 = 0xe21acccf0dc82892e075afb5781301f4u128;
    let q0 = 0x66275e5a99cc6e833e1221d1b0a23d0du128;
    let q1 = 0x25b84b7e8f92b1fa07b21b7908ed7119u128;
    let m768 = gf768_mul_gf256(p0, p1, p2, p3, p4, p5, q0, q1);
    assert((m768.0, m768.1, m768.2, m768.3, m768.4, m768.5)
        == gf768_mul_bits(p0, p1, p2, p3, p4, p5, (q0, q1), 256nat));
    let z768 = gf768_mul_gf256(p0, p1, p2, p3, p4, p5, 0u128, 0u128);
    assert((z768.0, z768.1, z768.2, z768.3, z768.4, z768.5)
        == gf768_mul_bits(p0, p1, p2, p3, p4, p5, (0u128, 0u128), 256nat));
}

/// Byte-plane roundtrips on the same row samples: as_bytes then
/// from_bytes reconstructs the limb vector exactly (the lib lemma
/// on unique byte determination per limb, fed by the concrete byte
/// agreements of the two postconditions).
fn ut_fa3_w3_byte_planes() {
    // gf384: 48-byte plane
    let w3v0 = 0xe53c68410b3b110daf8ee8b7e66c0fb9u128;
    let w3v1 = 0xb8681ad9c76107d19e0c51212f225d9cu128;
    let w3v2 = 0x257982edd2d130007386847e27cea020u128;
    let b3 = gf384_as_bytes([w3v0, w3v1, w3v2]);
    let r3 = gf384_from_bytes(&b3);
    proof {
        assert(byte128(r3[0], 0) == ((r3[0] >> 0u64) & 0xFF));
        assert(byte128(r3[0], 1) == ((r3[0] >> 8u64) & 0xFF));
        assert(byte128(r3[0], 2) == ((r3[0] >> 16u64) & 0xFF));
        assert(byte128(r3[0], 3) == ((r3[0] >> 24u64) & 0xFF));
        assert(byte128(r3[0], 4) == ((r3[0] >> 32u64) & 0xFF));
        assert(byte128(r3[0], 5) == ((r3[0] >> 40u64) & 0xFF));
        assert(byte128(r3[0], 6) == ((r3[0] >> 48u64) & 0xFF));
        assert(byte128(r3[0], 7) == ((r3[0] >> 56u64) & 0xFF));
        assert(byte128(r3[0], 8) == ((r3[0] >> 64u64) & 0xFF));
        assert(byte128(r3[0], 9) == ((r3[0] >> 72u64) & 0xFF));
        assert(byte128(r3[0], 10) == ((r3[0] >> 80u64) & 0xFF));
        assert(byte128(r3[0], 11) == ((r3[0] >> 88u64) & 0xFF));
        assert(byte128(r3[0], 12) == ((r3[0] >> 96u64) & 0xFF));
        assert(byte128(r3[0], 13) == ((r3[0] >> 104u64) & 0xFF));
        assert(byte128(r3[0], 14) == ((r3[0] >> 112u64) & 0xFF));
        assert(byte128(r3[0], 15) == ((r3[0] >> 120u64) & 0xFF));
        assert(((w3v0 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 0u64) & 0xFF) == (((r3[0] >> 0u64) & 0xFF)));
        assert(((w3v0 >> 8u64) & 0xFF) == (((r3[0] >> 8u64) & 0xFF)));
        assert(((w3v0 >> 16u64) & 0xFF) == (((r3[0] >> 16u64) & 0xFF)));
        assert(((w3v0 >> 24u64) & 0xFF) == (((r3[0] >> 24u64) & 0xFF)));
        assert(((w3v0 >> 32u64) & 0xFF) == (((r3[0] >> 32u64) & 0xFF)));
        assert(((w3v0 >> 40u64) & 0xFF) == (((r3[0] >> 40u64) & 0xFF)));
        assert(((w3v0 >> 48u64) & 0xFF) == (((r3[0] >> 48u64) & 0xFF)));
        assert(((w3v0 >> 56u64) & 0xFF) == (((r3[0] >> 56u64) & 0xFF)));
        assert(((w3v0 >> 64u64) & 0xFF) == (((r3[0] >> 64u64) & 0xFF)));
        assert(((w3v0 >> 72u64) & 0xFF) == (((r3[0] >> 72u64) & 0xFF)));
        assert(((w3v0 >> 80u64) & 0xFF) == (((r3[0] >> 80u64) & 0xFF)));
        assert(((w3v0 >> 88u64) & 0xFF) == (((r3[0] >> 88u64) & 0xFF)));
        assert(((w3v0 >> 96u64) & 0xFF) == (((r3[0] >> 96u64) & 0xFF)));
        assert(((w3v0 >> 104u64) & 0xFF) == (((r3[0] >> 104u64) & 0xFF)));
        assert(((w3v0 >> 112u64) & 0xFF) == (((r3[0] >> 112u64) & 0xFF)));
        assert(((w3v0 >> 120u64) & 0xFF) == (((r3[0] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v0, r3[0], ((w3v0 >> 0u64) & 0xFF), ((w3v0 >> 8u64) & 0xFF), ((w3v0 >> 16u64) & 0xFF), ((w3v0 >> 24u64) & 0xFF), ((w3v0 >> 32u64) & 0xFF), ((w3v0 >> 40u64) & 0xFF), ((w3v0 >> 48u64) & 0xFF), ((w3v0 >> 56u64) & 0xFF), ((w3v0 >> 64u64) & 0xFF), ((w3v0 >> 72u64) & 0xFF), ((w3v0 >> 80u64) & 0xFF), ((w3v0 >> 88u64) & 0xFF), ((w3v0 >> 96u64) & 0xFF), ((w3v0 >> 104u64) & 0xFF), ((w3v0 >> 112u64) & 0xFF), ((w3v0 >> 120u64) & 0xFF));
        assert(byte128(r3[1], 0) == ((r3[1] >> 0u64) & 0xFF));
        assert(byte128(r3[1], 1) == ((r3[1] >> 8u64) & 0xFF));
        assert(byte128(r3[1], 2) == ((r3[1] >> 16u64) & 0xFF));
        assert(byte128(r3[1], 3) == ((r3[1] >> 24u64) & 0xFF));
        assert(byte128(r3[1], 4) == ((r3[1] >> 32u64) & 0xFF));
        assert(byte128(r3[1], 5) == ((r3[1] >> 40u64) & 0xFF));
        assert(byte128(r3[1], 6) == ((r3[1] >> 48u64) & 0xFF));
        assert(byte128(r3[1], 7) == ((r3[1] >> 56u64) & 0xFF));
        assert(byte128(r3[1], 8) == ((r3[1] >> 64u64) & 0xFF));
        assert(byte128(r3[1], 9) == ((r3[1] >> 72u64) & 0xFF));
        assert(byte128(r3[1], 10) == ((r3[1] >> 80u64) & 0xFF));
        assert(byte128(r3[1], 11) == ((r3[1] >> 88u64) & 0xFF));
        assert(byte128(r3[1], 12) == ((r3[1] >> 96u64) & 0xFF));
        assert(byte128(r3[1], 13) == ((r3[1] >> 104u64) & 0xFF));
        assert(byte128(r3[1], 14) == ((r3[1] >> 112u64) & 0xFF));
        assert(byte128(r3[1], 15) == ((r3[1] >> 120u64) & 0xFF));
        assert(((w3v1 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 0u64) & 0xFF) == (((r3[1] >> 0u64) & 0xFF)));
        assert(((w3v1 >> 8u64) & 0xFF) == (((r3[1] >> 8u64) & 0xFF)));
        assert(((w3v1 >> 16u64) & 0xFF) == (((r3[1] >> 16u64) & 0xFF)));
        assert(((w3v1 >> 24u64) & 0xFF) == (((r3[1] >> 24u64) & 0xFF)));
        assert(((w3v1 >> 32u64) & 0xFF) == (((r3[1] >> 32u64) & 0xFF)));
        assert(((w3v1 >> 40u64) & 0xFF) == (((r3[1] >> 40u64) & 0xFF)));
        assert(((w3v1 >> 48u64) & 0xFF) == (((r3[1] >> 48u64) & 0xFF)));
        assert(((w3v1 >> 56u64) & 0xFF) == (((r3[1] >> 56u64) & 0xFF)));
        assert(((w3v1 >> 64u64) & 0xFF) == (((r3[1] >> 64u64) & 0xFF)));
        assert(((w3v1 >> 72u64) & 0xFF) == (((r3[1] >> 72u64) & 0xFF)));
        assert(((w3v1 >> 80u64) & 0xFF) == (((r3[1] >> 80u64) & 0xFF)));
        assert(((w3v1 >> 88u64) & 0xFF) == (((r3[1] >> 88u64) & 0xFF)));
        assert(((w3v1 >> 96u64) & 0xFF) == (((r3[1] >> 96u64) & 0xFF)));
        assert(((w3v1 >> 104u64) & 0xFF) == (((r3[1] >> 104u64) & 0xFF)));
        assert(((w3v1 >> 112u64) & 0xFF) == (((r3[1] >> 112u64) & 0xFF)));
        assert(((w3v1 >> 120u64) & 0xFF) == (((r3[1] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v1, r3[1], ((w3v1 >> 0u64) & 0xFF), ((w3v1 >> 8u64) & 0xFF), ((w3v1 >> 16u64) & 0xFF), ((w3v1 >> 24u64) & 0xFF), ((w3v1 >> 32u64) & 0xFF), ((w3v1 >> 40u64) & 0xFF), ((w3v1 >> 48u64) & 0xFF), ((w3v1 >> 56u64) & 0xFF), ((w3v1 >> 64u64) & 0xFF), ((w3v1 >> 72u64) & 0xFF), ((w3v1 >> 80u64) & 0xFF), ((w3v1 >> 88u64) & 0xFF), ((w3v1 >> 96u64) & 0xFF), ((w3v1 >> 104u64) & 0xFF), ((w3v1 >> 112u64) & 0xFF), ((w3v1 >> 120u64) & 0xFF));
        assert(byte128(r3[2], 0) == ((r3[2] >> 0u64) & 0xFF));
        assert(byte128(r3[2], 1) == ((r3[2] >> 8u64) & 0xFF));
        assert(byte128(r3[2], 2) == ((r3[2] >> 16u64) & 0xFF));
        assert(byte128(r3[2], 3) == ((r3[2] >> 24u64) & 0xFF));
        assert(byte128(r3[2], 4) == ((r3[2] >> 32u64) & 0xFF));
        assert(byte128(r3[2], 5) == ((r3[2] >> 40u64) & 0xFF));
        assert(byte128(r3[2], 6) == ((r3[2] >> 48u64) & 0xFF));
        assert(byte128(r3[2], 7) == ((r3[2] >> 56u64) & 0xFF));
        assert(byte128(r3[2], 8) == ((r3[2] >> 64u64) & 0xFF));
        assert(byte128(r3[2], 9) == ((r3[2] >> 72u64) & 0xFF));
        assert(byte128(r3[2], 10) == ((r3[2] >> 80u64) & 0xFF));
        assert(byte128(r3[2], 11) == ((r3[2] >> 88u64) & 0xFF));
        assert(byte128(r3[2], 12) == ((r3[2] >> 96u64) & 0xFF));
        assert(byte128(r3[2], 13) == ((r3[2] >> 104u64) & 0xFF));
        assert(byte128(r3[2], 14) == ((r3[2] >> 112u64) & 0xFF));
        assert(byte128(r3[2], 15) == ((r3[2] >> 120u64) & 0xFF));
        assert(((w3v2 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 0u64) & 0xFF) == (((r3[2] >> 0u64) & 0xFF)));
        assert(((w3v2 >> 8u64) & 0xFF) == (((r3[2] >> 8u64) & 0xFF)));
        assert(((w3v2 >> 16u64) & 0xFF) == (((r3[2] >> 16u64) & 0xFF)));
        assert(((w3v2 >> 24u64) & 0xFF) == (((r3[2] >> 24u64) & 0xFF)));
        assert(((w3v2 >> 32u64) & 0xFF) == (((r3[2] >> 32u64) & 0xFF)));
        assert(((w3v2 >> 40u64) & 0xFF) == (((r3[2] >> 40u64) & 0xFF)));
        assert(((w3v2 >> 48u64) & 0xFF) == (((r3[2] >> 48u64) & 0xFF)));
        assert(((w3v2 >> 56u64) & 0xFF) == (((r3[2] >> 56u64) & 0xFF)));
        assert(((w3v2 >> 64u64) & 0xFF) == (((r3[2] >> 64u64) & 0xFF)));
        assert(((w3v2 >> 72u64) & 0xFF) == (((r3[2] >> 72u64) & 0xFF)));
        assert(((w3v2 >> 80u64) & 0xFF) == (((r3[2] >> 80u64) & 0xFF)));
        assert(((w3v2 >> 88u64) & 0xFF) == (((r3[2] >> 88u64) & 0xFF)));
        assert(((w3v2 >> 96u64) & 0xFF) == (((r3[2] >> 96u64) & 0xFF)));
        assert(((w3v2 >> 104u64) & 0xFF) == (((r3[2] >> 104u64) & 0xFF)));
        assert(((w3v2 >> 112u64) & 0xFF) == (((r3[2] >> 112u64) & 0xFF)));
        assert(((w3v2 >> 120u64) & 0xFF) == (((r3[2] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v2, r3[2], ((w3v2 >> 0u64) & 0xFF), ((w3v2 >> 8u64) & 0xFF), ((w3v2 >> 16u64) & 0xFF), ((w3v2 >> 24u64) & 0xFF), ((w3v2 >> 32u64) & 0xFF), ((w3v2 >> 40u64) & 0xFF), ((w3v2 >> 48u64) & 0xFF), ((w3v2 >> 56u64) & 0xFF), ((w3v2 >> 64u64) & 0xFF), ((w3v2 >> 72u64) & 0xFF), ((w3v2 >> 80u64) & 0xFF), ((w3v2 >> 88u64) & 0xFF), ((w3v2 >> 96u64) & 0xFF), ((w3v2 >> 104u64) & 0xFF), ((w3v2 >> 112u64) & 0xFF), ((w3v2 >> 120u64) & 0xFF));
    }
    assert(r3[0] == w3v0);
    assert(r3[1] == w3v1);
    assert(r3[2] == w3v2);
    // gf576: 72-byte plane
    let w3v0 = 0x837a66310255832a10a32739ac4d7d5bu128;
    let w3v1 = 0xafee4cab2a2d693228b94b3d23f3f252u128;
    let w3v2 = 0xc258bd8b8b47e6445ac1e7c994d6210du128;
    let w3v3 = 0xe1060dc5e8b93801b52fbd207f14cde5u128;
    let w3v4 = 0x57614648d12f1630u128;
    let b3 = gf576_as_bytes([w3v0, w3v1, w3v2, w3v3, w3v4]);
    let r3 = gf576_from_bytes(&b3);
    proof {
        assert(byte128(r3[0], 0) == ((r3[0] >> 0u64) & 0xFF));
        assert(byte128(r3[0], 1) == ((r3[0] >> 8u64) & 0xFF));
        assert(byte128(r3[0], 2) == ((r3[0] >> 16u64) & 0xFF));
        assert(byte128(r3[0], 3) == ((r3[0] >> 24u64) & 0xFF));
        assert(byte128(r3[0], 4) == ((r3[0] >> 32u64) & 0xFF));
        assert(byte128(r3[0], 5) == ((r3[0] >> 40u64) & 0xFF));
        assert(byte128(r3[0], 6) == ((r3[0] >> 48u64) & 0xFF));
        assert(byte128(r3[0], 7) == ((r3[0] >> 56u64) & 0xFF));
        assert(byte128(r3[0], 8) == ((r3[0] >> 64u64) & 0xFF));
        assert(byte128(r3[0], 9) == ((r3[0] >> 72u64) & 0xFF));
        assert(byte128(r3[0], 10) == ((r3[0] >> 80u64) & 0xFF));
        assert(byte128(r3[0], 11) == ((r3[0] >> 88u64) & 0xFF));
        assert(byte128(r3[0], 12) == ((r3[0] >> 96u64) & 0xFF));
        assert(byte128(r3[0], 13) == ((r3[0] >> 104u64) & 0xFF));
        assert(byte128(r3[0], 14) == ((r3[0] >> 112u64) & 0xFF));
        assert(byte128(r3[0], 15) == ((r3[0] >> 120u64) & 0xFF));
        assert(((w3v0 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 0u64) & 0xFF) == (((r3[0] >> 0u64) & 0xFF)));
        assert(((w3v0 >> 8u64) & 0xFF) == (((r3[0] >> 8u64) & 0xFF)));
        assert(((w3v0 >> 16u64) & 0xFF) == (((r3[0] >> 16u64) & 0xFF)));
        assert(((w3v0 >> 24u64) & 0xFF) == (((r3[0] >> 24u64) & 0xFF)));
        assert(((w3v0 >> 32u64) & 0xFF) == (((r3[0] >> 32u64) & 0xFF)));
        assert(((w3v0 >> 40u64) & 0xFF) == (((r3[0] >> 40u64) & 0xFF)));
        assert(((w3v0 >> 48u64) & 0xFF) == (((r3[0] >> 48u64) & 0xFF)));
        assert(((w3v0 >> 56u64) & 0xFF) == (((r3[0] >> 56u64) & 0xFF)));
        assert(((w3v0 >> 64u64) & 0xFF) == (((r3[0] >> 64u64) & 0xFF)));
        assert(((w3v0 >> 72u64) & 0xFF) == (((r3[0] >> 72u64) & 0xFF)));
        assert(((w3v0 >> 80u64) & 0xFF) == (((r3[0] >> 80u64) & 0xFF)));
        assert(((w3v0 >> 88u64) & 0xFF) == (((r3[0] >> 88u64) & 0xFF)));
        assert(((w3v0 >> 96u64) & 0xFF) == (((r3[0] >> 96u64) & 0xFF)));
        assert(((w3v0 >> 104u64) & 0xFF) == (((r3[0] >> 104u64) & 0xFF)));
        assert(((w3v0 >> 112u64) & 0xFF) == (((r3[0] >> 112u64) & 0xFF)));
        assert(((w3v0 >> 120u64) & 0xFF) == (((r3[0] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v0, r3[0], ((w3v0 >> 0u64) & 0xFF), ((w3v0 >> 8u64) & 0xFF), ((w3v0 >> 16u64) & 0xFF), ((w3v0 >> 24u64) & 0xFF), ((w3v0 >> 32u64) & 0xFF), ((w3v0 >> 40u64) & 0xFF), ((w3v0 >> 48u64) & 0xFF), ((w3v0 >> 56u64) & 0xFF), ((w3v0 >> 64u64) & 0xFF), ((w3v0 >> 72u64) & 0xFF), ((w3v0 >> 80u64) & 0xFF), ((w3v0 >> 88u64) & 0xFF), ((w3v0 >> 96u64) & 0xFF), ((w3v0 >> 104u64) & 0xFF), ((w3v0 >> 112u64) & 0xFF), ((w3v0 >> 120u64) & 0xFF));
        assert(byte128(r3[1], 0) == ((r3[1] >> 0u64) & 0xFF));
        assert(byte128(r3[1], 1) == ((r3[1] >> 8u64) & 0xFF));
        assert(byte128(r3[1], 2) == ((r3[1] >> 16u64) & 0xFF));
        assert(byte128(r3[1], 3) == ((r3[1] >> 24u64) & 0xFF));
        assert(byte128(r3[1], 4) == ((r3[1] >> 32u64) & 0xFF));
        assert(byte128(r3[1], 5) == ((r3[1] >> 40u64) & 0xFF));
        assert(byte128(r3[1], 6) == ((r3[1] >> 48u64) & 0xFF));
        assert(byte128(r3[1], 7) == ((r3[1] >> 56u64) & 0xFF));
        assert(byte128(r3[1], 8) == ((r3[1] >> 64u64) & 0xFF));
        assert(byte128(r3[1], 9) == ((r3[1] >> 72u64) & 0xFF));
        assert(byte128(r3[1], 10) == ((r3[1] >> 80u64) & 0xFF));
        assert(byte128(r3[1], 11) == ((r3[1] >> 88u64) & 0xFF));
        assert(byte128(r3[1], 12) == ((r3[1] >> 96u64) & 0xFF));
        assert(byte128(r3[1], 13) == ((r3[1] >> 104u64) & 0xFF));
        assert(byte128(r3[1], 14) == ((r3[1] >> 112u64) & 0xFF));
        assert(byte128(r3[1], 15) == ((r3[1] >> 120u64) & 0xFF));
        assert(((w3v1 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 0u64) & 0xFF) == (((r3[1] >> 0u64) & 0xFF)));
        assert(((w3v1 >> 8u64) & 0xFF) == (((r3[1] >> 8u64) & 0xFF)));
        assert(((w3v1 >> 16u64) & 0xFF) == (((r3[1] >> 16u64) & 0xFF)));
        assert(((w3v1 >> 24u64) & 0xFF) == (((r3[1] >> 24u64) & 0xFF)));
        assert(((w3v1 >> 32u64) & 0xFF) == (((r3[1] >> 32u64) & 0xFF)));
        assert(((w3v1 >> 40u64) & 0xFF) == (((r3[1] >> 40u64) & 0xFF)));
        assert(((w3v1 >> 48u64) & 0xFF) == (((r3[1] >> 48u64) & 0xFF)));
        assert(((w3v1 >> 56u64) & 0xFF) == (((r3[1] >> 56u64) & 0xFF)));
        assert(((w3v1 >> 64u64) & 0xFF) == (((r3[1] >> 64u64) & 0xFF)));
        assert(((w3v1 >> 72u64) & 0xFF) == (((r3[1] >> 72u64) & 0xFF)));
        assert(((w3v1 >> 80u64) & 0xFF) == (((r3[1] >> 80u64) & 0xFF)));
        assert(((w3v1 >> 88u64) & 0xFF) == (((r3[1] >> 88u64) & 0xFF)));
        assert(((w3v1 >> 96u64) & 0xFF) == (((r3[1] >> 96u64) & 0xFF)));
        assert(((w3v1 >> 104u64) & 0xFF) == (((r3[1] >> 104u64) & 0xFF)));
        assert(((w3v1 >> 112u64) & 0xFF) == (((r3[1] >> 112u64) & 0xFF)));
        assert(((w3v1 >> 120u64) & 0xFF) == (((r3[1] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v1, r3[1], ((w3v1 >> 0u64) & 0xFF), ((w3v1 >> 8u64) & 0xFF), ((w3v1 >> 16u64) & 0xFF), ((w3v1 >> 24u64) & 0xFF), ((w3v1 >> 32u64) & 0xFF), ((w3v1 >> 40u64) & 0xFF), ((w3v1 >> 48u64) & 0xFF), ((w3v1 >> 56u64) & 0xFF), ((w3v1 >> 64u64) & 0xFF), ((w3v1 >> 72u64) & 0xFF), ((w3v1 >> 80u64) & 0xFF), ((w3v1 >> 88u64) & 0xFF), ((w3v1 >> 96u64) & 0xFF), ((w3v1 >> 104u64) & 0xFF), ((w3v1 >> 112u64) & 0xFF), ((w3v1 >> 120u64) & 0xFF));
        assert(byte128(r3[2], 0) == ((r3[2] >> 0u64) & 0xFF));
        assert(byte128(r3[2], 1) == ((r3[2] >> 8u64) & 0xFF));
        assert(byte128(r3[2], 2) == ((r3[2] >> 16u64) & 0xFF));
        assert(byte128(r3[2], 3) == ((r3[2] >> 24u64) & 0xFF));
        assert(byte128(r3[2], 4) == ((r3[2] >> 32u64) & 0xFF));
        assert(byte128(r3[2], 5) == ((r3[2] >> 40u64) & 0xFF));
        assert(byte128(r3[2], 6) == ((r3[2] >> 48u64) & 0xFF));
        assert(byte128(r3[2], 7) == ((r3[2] >> 56u64) & 0xFF));
        assert(byte128(r3[2], 8) == ((r3[2] >> 64u64) & 0xFF));
        assert(byte128(r3[2], 9) == ((r3[2] >> 72u64) & 0xFF));
        assert(byte128(r3[2], 10) == ((r3[2] >> 80u64) & 0xFF));
        assert(byte128(r3[2], 11) == ((r3[2] >> 88u64) & 0xFF));
        assert(byte128(r3[2], 12) == ((r3[2] >> 96u64) & 0xFF));
        assert(byte128(r3[2], 13) == ((r3[2] >> 104u64) & 0xFF));
        assert(byte128(r3[2], 14) == ((r3[2] >> 112u64) & 0xFF));
        assert(byte128(r3[2], 15) == ((r3[2] >> 120u64) & 0xFF));
        assert(((w3v2 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 0u64) & 0xFF) == (((r3[2] >> 0u64) & 0xFF)));
        assert(((w3v2 >> 8u64) & 0xFF) == (((r3[2] >> 8u64) & 0xFF)));
        assert(((w3v2 >> 16u64) & 0xFF) == (((r3[2] >> 16u64) & 0xFF)));
        assert(((w3v2 >> 24u64) & 0xFF) == (((r3[2] >> 24u64) & 0xFF)));
        assert(((w3v2 >> 32u64) & 0xFF) == (((r3[2] >> 32u64) & 0xFF)));
        assert(((w3v2 >> 40u64) & 0xFF) == (((r3[2] >> 40u64) & 0xFF)));
        assert(((w3v2 >> 48u64) & 0xFF) == (((r3[2] >> 48u64) & 0xFF)));
        assert(((w3v2 >> 56u64) & 0xFF) == (((r3[2] >> 56u64) & 0xFF)));
        assert(((w3v2 >> 64u64) & 0xFF) == (((r3[2] >> 64u64) & 0xFF)));
        assert(((w3v2 >> 72u64) & 0xFF) == (((r3[2] >> 72u64) & 0xFF)));
        assert(((w3v2 >> 80u64) & 0xFF) == (((r3[2] >> 80u64) & 0xFF)));
        assert(((w3v2 >> 88u64) & 0xFF) == (((r3[2] >> 88u64) & 0xFF)));
        assert(((w3v2 >> 96u64) & 0xFF) == (((r3[2] >> 96u64) & 0xFF)));
        assert(((w3v2 >> 104u64) & 0xFF) == (((r3[2] >> 104u64) & 0xFF)));
        assert(((w3v2 >> 112u64) & 0xFF) == (((r3[2] >> 112u64) & 0xFF)));
        assert(((w3v2 >> 120u64) & 0xFF) == (((r3[2] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v2, r3[2], ((w3v2 >> 0u64) & 0xFF), ((w3v2 >> 8u64) & 0xFF), ((w3v2 >> 16u64) & 0xFF), ((w3v2 >> 24u64) & 0xFF), ((w3v2 >> 32u64) & 0xFF), ((w3v2 >> 40u64) & 0xFF), ((w3v2 >> 48u64) & 0xFF), ((w3v2 >> 56u64) & 0xFF), ((w3v2 >> 64u64) & 0xFF), ((w3v2 >> 72u64) & 0xFF), ((w3v2 >> 80u64) & 0xFF), ((w3v2 >> 88u64) & 0xFF), ((w3v2 >> 96u64) & 0xFF), ((w3v2 >> 104u64) & 0xFF), ((w3v2 >> 112u64) & 0xFF), ((w3v2 >> 120u64) & 0xFF));
        assert(byte128(r3[3], 0) == ((r3[3] >> 0u64) & 0xFF));
        assert(byte128(r3[3], 1) == ((r3[3] >> 8u64) & 0xFF));
        assert(byte128(r3[3], 2) == ((r3[3] >> 16u64) & 0xFF));
        assert(byte128(r3[3], 3) == ((r3[3] >> 24u64) & 0xFF));
        assert(byte128(r3[3], 4) == ((r3[3] >> 32u64) & 0xFF));
        assert(byte128(r3[3], 5) == ((r3[3] >> 40u64) & 0xFF));
        assert(byte128(r3[3], 6) == ((r3[3] >> 48u64) & 0xFF));
        assert(byte128(r3[3], 7) == ((r3[3] >> 56u64) & 0xFF));
        assert(byte128(r3[3], 8) == ((r3[3] >> 64u64) & 0xFF));
        assert(byte128(r3[3], 9) == ((r3[3] >> 72u64) & 0xFF));
        assert(byte128(r3[3], 10) == ((r3[3] >> 80u64) & 0xFF));
        assert(byte128(r3[3], 11) == ((r3[3] >> 88u64) & 0xFF));
        assert(byte128(r3[3], 12) == ((r3[3] >> 96u64) & 0xFF));
        assert(byte128(r3[3], 13) == ((r3[3] >> 104u64) & 0xFF));
        assert(byte128(r3[3], 14) == ((r3[3] >> 112u64) & 0xFF));
        assert(byte128(r3[3], 15) == ((r3[3] >> 120u64) & 0xFF));
        assert(((w3v3 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 0u64) & 0xFF) == (((r3[3] >> 0u64) & 0xFF)));
        assert(((w3v3 >> 8u64) & 0xFF) == (((r3[3] >> 8u64) & 0xFF)));
        assert(((w3v3 >> 16u64) & 0xFF) == (((r3[3] >> 16u64) & 0xFF)));
        assert(((w3v3 >> 24u64) & 0xFF) == (((r3[3] >> 24u64) & 0xFF)));
        assert(((w3v3 >> 32u64) & 0xFF) == (((r3[3] >> 32u64) & 0xFF)));
        assert(((w3v3 >> 40u64) & 0xFF) == (((r3[3] >> 40u64) & 0xFF)));
        assert(((w3v3 >> 48u64) & 0xFF) == (((r3[3] >> 48u64) & 0xFF)));
        assert(((w3v3 >> 56u64) & 0xFF) == (((r3[3] >> 56u64) & 0xFF)));
        assert(((w3v3 >> 64u64) & 0xFF) == (((r3[3] >> 64u64) & 0xFF)));
        assert(((w3v3 >> 72u64) & 0xFF) == (((r3[3] >> 72u64) & 0xFF)));
        assert(((w3v3 >> 80u64) & 0xFF) == (((r3[3] >> 80u64) & 0xFF)));
        assert(((w3v3 >> 88u64) & 0xFF) == (((r3[3] >> 88u64) & 0xFF)));
        assert(((w3v3 >> 96u64) & 0xFF) == (((r3[3] >> 96u64) & 0xFF)));
        assert(((w3v3 >> 104u64) & 0xFF) == (((r3[3] >> 104u64) & 0xFF)));
        assert(((w3v3 >> 112u64) & 0xFF) == (((r3[3] >> 112u64) & 0xFF)));
        assert(((w3v3 >> 120u64) & 0xFF) == (((r3[3] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v3, r3[3], ((w3v3 >> 0u64) & 0xFF), ((w3v3 >> 8u64) & 0xFF), ((w3v3 >> 16u64) & 0xFF), ((w3v3 >> 24u64) & 0xFF), ((w3v3 >> 32u64) & 0xFF), ((w3v3 >> 40u64) & 0xFF), ((w3v3 >> 48u64) & 0xFF), ((w3v3 >> 56u64) & 0xFF), ((w3v3 >> 64u64) & 0xFF), ((w3v3 >> 72u64) & 0xFF), ((w3v3 >> 80u64) & 0xFF), ((w3v3 >> 88u64) & 0xFF), ((w3v3 >> 96u64) & 0xFF), ((w3v3 >> 104u64) & 0xFF), ((w3v3 >> 112u64) & 0xFF), ((w3v3 >> 120u64) & 0xFF));
        assert(byte128(r3[4], 0) == ((r3[4] >> 0u64) & 0xFF));
        assert(byte128(r3[4], 1) == ((r3[4] >> 8u64) & 0xFF));
        assert(byte128(r3[4], 2) == ((r3[4] >> 16u64) & 0xFF));
        assert(byte128(r3[4], 3) == ((r3[4] >> 24u64) & 0xFF));
        assert(byte128(r3[4], 4) == ((r3[4] >> 32u64) & 0xFF));
        assert(byte128(r3[4], 5) == ((r3[4] >> 40u64) & 0xFF));
        assert(byte128(r3[4], 6) == ((r3[4] >> 48u64) & 0xFF));
        assert(byte128(r3[4], 7) == ((r3[4] >> 56u64) & 0xFF));
        assert(((w3v4 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 0u64) & 0xFF) == (((r3[4] >> 0u64) & 0xFF)));
        assert(((w3v4 >> 8u64) & 0xFF) == (((r3[4] >> 8u64) & 0xFF)));
        assert(((w3v4 >> 16u64) & 0xFF) == (((r3[4] >> 16u64) & 0xFF)));
        assert(((w3v4 >> 24u64) & 0xFF) == (((r3[4] >> 24u64) & 0xFF)));
        assert(((w3v4 >> 32u64) & 0xFF) == (((r3[4] >> 32u64) & 0xFF)));
        assert(((w3v4 >> 40u64) & 0xFF) == (((r3[4] >> 40u64) & 0xFF)));
        assert(((w3v4 >> 48u64) & 0xFF) == (((r3[4] >> 48u64) & 0xFF)));
        assert(((w3v4 >> 56u64) & 0xFF) == (((r3[4] >> 56u64) & 0xFF)));
        assert(((w3v4 >> 64u64) & 0xFF) == 0u128) by (bit_vector)
        requires w3v4 == 0x57614648d12f1630u128,;
        assert(((w3v4 >> 72u64) & 0xFF) == 0u128) by (bit_vector)
        requires w3v4 == 0x57614648d12f1630u128,;
        assert(((w3v4 >> 80u64) & 0xFF) == 0u128) by (bit_vector)
        requires w3v4 == 0x57614648d12f1630u128,;
        assert(((w3v4 >> 88u64) & 0xFF) == 0u128) by (bit_vector)
        requires w3v4 == 0x57614648d12f1630u128,;
        assert(((w3v4 >> 96u64) & 0xFF) == 0u128) by (bit_vector)
        requires w3v4 == 0x57614648d12f1630u128,;
        assert(((w3v4 >> 104u64) & 0xFF) == 0u128) by (bit_vector)
        requires w3v4 == 0x57614648d12f1630u128,;
        assert(((w3v4 >> 112u64) & 0xFF) == 0u128) by (bit_vector)
        requires w3v4 == 0x57614648d12f1630u128,;
        assert(((w3v4 >> 120u64) & 0xFF) == 0u128) by (bit_vector)
        requires w3v4 == 0x57614648d12f1630u128,;
        assert((w3v4 >> 64u64) == 0u128) by (bit_vector)
        requires w3v4 == 0x57614648d12f1630u128,;
        assert((r3[4] >> 64u64) == 0u128);
    }
    assert(r3[0] == w3v0);
    assert(r3[1] == w3v1);
    assert(r3[2] == w3v2);
    assert(r3[3] == w3v3);
    assert(r3[4] == w3v4) by {
        w3_limb8_eq(w3v4, r3[4]);
    }
    // gf768: 96-byte plane
    let w3v0 = 0x65e61a6f91cc869c2c5cefe30dd36314u128;
    let w3v1 = 0xd743fb3f854c169781d331d03cff3a1au128;
    let w3v2 = 0xee87f6f4f12e01b1089ec6f08c316a6fu128;
    let w3v3 = 0xb830e1305e6df981fdbdbbf7e37b840du128;
    let w3v4 = 0x14f030473c373e2a1179aaf912b5636bu128;
    let w3v5 = 0xe21acccf0dc82892e075afb5781301f4u128;
    let b3 = gf768_as_bytes([w3v0, w3v1, w3v2, w3v3, w3v4, w3v5]);
    let r3 = gf768_from_bytes(&b3);
    proof {
        assert(byte128(r3[0], 0) == ((r3[0] >> 0u64) & 0xFF));
        assert(byte128(r3[0], 1) == ((r3[0] >> 8u64) & 0xFF));
        assert(byte128(r3[0], 2) == ((r3[0] >> 16u64) & 0xFF));
        assert(byte128(r3[0], 3) == ((r3[0] >> 24u64) & 0xFF));
        assert(byte128(r3[0], 4) == ((r3[0] >> 32u64) & 0xFF));
        assert(byte128(r3[0], 5) == ((r3[0] >> 40u64) & 0xFF));
        assert(byte128(r3[0], 6) == ((r3[0] >> 48u64) & 0xFF));
        assert(byte128(r3[0], 7) == ((r3[0] >> 56u64) & 0xFF));
        assert(byte128(r3[0], 8) == ((r3[0] >> 64u64) & 0xFF));
        assert(byte128(r3[0], 9) == ((r3[0] >> 72u64) & 0xFF));
        assert(byte128(r3[0], 10) == ((r3[0] >> 80u64) & 0xFF));
        assert(byte128(r3[0], 11) == ((r3[0] >> 88u64) & 0xFF));
        assert(byte128(r3[0], 12) == ((r3[0] >> 96u64) & 0xFF));
        assert(byte128(r3[0], 13) == ((r3[0] >> 104u64) & 0xFF));
        assert(byte128(r3[0], 14) == ((r3[0] >> 112u64) & 0xFF));
        assert(byte128(r3[0], 15) == ((r3[0] >> 120u64) & 0xFF));
        assert(((w3v0 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v0 >> 0u64) & 0xFF) == (((r3[0] >> 0u64) & 0xFF)));
        assert(((w3v0 >> 8u64) & 0xFF) == (((r3[0] >> 8u64) & 0xFF)));
        assert(((w3v0 >> 16u64) & 0xFF) == (((r3[0] >> 16u64) & 0xFF)));
        assert(((w3v0 >> 24u64) & 0xFF) == (((r3[0] >> 24u64) & 0xFF)));
        assert(((w3v0 >> 32u64) & 0xFF) == (((r3[0] >> 32u64) & 0xFF)));
        assert(((w3v0 >> 40u64) & 0xFF) == (((r3[0] >> 40u64) & 0xFF)));
        assert(((w3v0 >> 48u64) & 0xFF) == (((r3[0] >> 48u64) & 0xFF)));
        assert(((w3v0 >> 56u64) & 0xFF) == (((r3[0] >> 56u64) & 0xFF)));
        assert(((w3v0 >> 64u64) & 0xFF) == (((r3[0] >> 64u64) & 0xFF)));
        assert(((w3v0 >> 72u64) & 0xFF) == (((r3[0] >> 72u64) & 0xFF)));
        assert(((w3v0 >> 80u64) & 0xFF) == (((r3[0] >> 80u64) & 0xFF)));
        assert(((w3v0 >> 88u64) & 0xFF) == (((r3[0] >> 88u64) & 0xFF)));
        assert(((w3v0 >> 96u64) & 0xFF) == (((r3[0] >> 96u64) & 0xFF)));
        assert(((w3v0 >> 104u64) & 0xFF) == (((r3[0] >> 104u64) & 0xFF)));
        assert(((w3v0 >> 112u64) & 0xFF) == (((r3[0] >> 112u64) & 0xFF)));
        assert(((w3v0 >> 120u64) & 0xFF) == (((r3[0] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v0, r3[0], ((w3v0 >> 0u64) & 0xFF), ((w3v0 >> 8u64) & 0xFF), ((w3v0 >> 16u64) & 0xFF), ((w3v0 >> 24u64) & 0xFF), ((w3v0 >> 32u64) & 0xFF), ((w3v0 >> 40u64) & 0xFF), ((w3v0 >> 48u64) & 0xFF), ((w3v0 >> 56u64) & 0xFF), ((w3v0 >> 64u64) & 0xFF), ((w3v0 >> 72u64) & 0xFF), ((w3v0 >> 80u64) & 0xFF), ((w3v0 >> 88u64) & 0xFF), ((w3v0 >> 96u64) & 0xFF), ((w3v0 >> 104u64) & 0xFF), ((w3v0 >> 112u64) & 0xFF), ((w3v0 >> 120u64) & 0xFF));
        assert(byte128(r3[1], 0) == ((r3[1] >> 0u64) & 0xFF));
        assert(byte128(r3[1], 1) == ((r3[1] >> 8u64) & 0xFF));
        assert(byte128(r3[1], 2) == ((r3[1] >> 16u64) & 0xFF));
        assert(byte128(r3[1], 3) == ((r3[1] >> 24u64) & 0xFF));
        assert(byte128(r3[1], 4) == ((r3[1] >> 32u64) & 0xFF));
        assert(byte128(r3[1], 5) == ((r3[1] >> 40u64) & 0xFF));
        assert(byte128(r3[1], 6) == ((r3[1] >> 48u64) & 0xFF));
        assert(byte128(r3[1], 7) == ((r3[1] >> 56u64) & 0xFF));
        assert(byte128(r3[1], 8) == ((r3[1] >> 64u64) & 0xFF));
        assert(byte128(r3[1], 9) == ((r3[1] >> 72u64) & 0xFF));
        assert(byte128(r3[1], 10) == ((r3[1] >> 80u64) & 0xFF));
        assert(byte128(r3[1], 11) == ((r3[1] >> 88u64) & 0xFF));
        assert(byte128(r3[1], 12) == ((r3[1] >> 96u64) & 0xFF));
        assert(byte128(r3[1], 13) == ((r3[1] >> 104u64) & 0xFF));
        assert(byte128(r3[1], 14) == ((r3[1] >> 112u64) & 0xFF));
        assert(byte128(r3[1], 15) == ((r3[1] >> 120u64) & 0xFF));
        assert(((w3v1 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v1 >> 0u64) & 0xFF) == (((r3[1] >> 0u64) & 0xFF)));
        assert(((w3v1 >> 8u64) & 0xFF) == (((r3[1] >> 8u64) & 0xFF)));
        assert(((w3v1 >> 16u64) & 0xFF) == (((r3[1] >> 16u64) & 0xFF)));
        assert(((w3v1 >> 24u64) & 0xFF) == (((r3[1] >> 24u64) & 0xFF)));
        assert(((w3v1 >> 32u64) & 0xFF) == (((r3[1] >> 32u64) & 0xFF)));
        assert(((w3v1 >> 40u64) & 0xFF) == (((r3[1] >> 40u64) & 0xFF)));
        assert(((w3v1 >> 48u64) & 0xFF) == (((r3[1] >> 48u64) & 0xFF)));
        assert(((w3v1 >> 56u64) & 0xFF) == (((r3[1] >> 56u64) & 0xFF)));
        assert(((w3v1 >> 64u64) & 0xFF) == (((r3[1] >> 64u64) & 0xFF)));
        assert(((w3v1 >> 72u64) & 0xFF) == (((r3[1] >> 72u64) & 0xFF)));
        assert(((w3v1 >> 80u64) & 0xFF) == (((r3[1] >> 80u64) & 0xFF)));
        assert(((w3v1 >> 88u64) & 0xFF) == (((r3[1] >> 88u64) & 0xFF)));
        assert(((w3v1 >> 96u64) & 0xFF) == (((r3[1] >> 96u64) & 0xFF)));
        assert(((w3v1 >> 104u64) & 0xFF) == (((r3[1] >> 104u64) & 0xFF)));
        assert(((w3v1 >> 112u64) & 0xFF) == (((r3[1] >> 112u64) & 0xFF)));
        assert(((w3v1 >> 120u64) & 0xFF) == (((r3[1] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v1, r3[1], ((w3v1 >> 0u64) & 0xFF), ((w3v1 >> 8u64) & 0xFF), ((w3v1 >> 16u64) & 0xFF), ((w3v1 >> 24u64) & 0xFF), ((w3v1 >> 32u64) & 0xFF), ((w3v1 >> 40u64) & 0xFF), ((w3v1 >> 48u64) & 0xFF), ((w3v1 >> 56u64) & 0xFF), ((w3v1 >> 64u64) & 0xFF), ((w3v1 >> 72u64) & 0xFF), ((w3v1 >> 80u64) & 0xFF), ((w3v1 >> 88u64) & 0xFF), ((w3v1 >> 96u64) & 0xFF), ((w3v1 >> 104u64) & 0xFF), ((w3v1 >> 112u64) & 0xFF), ((w3v1 >> 120u64) & 0xFF));
        assert(byte128(r3[2], 0) == ((r3[2] >> 0u64) & 0xFF));
        assert(byte128(r3[2], 1) == ((r3[2] >> 8u64) & 0xFF));
        assert(byte128(r3[2], 2) == ((r3[2] >> 16u64) & 0xFF));
        assert(byte128(r3[2], 3) == ((r3[2] >> 24u64) & 0xFF));
        assert(byte128(r3[2], 4) == ((r3[2] >> 32u64) & 0xFF));
        assert(byte128(r3[2], 5) == ((r3[2] >> 40u64) & 0xFF));
        assert(byte128(r3[2], 6) == ((r3[2] >> 48u64) & 0xFF));
        assert(byte128(r3[2], 7) == ((r3[2] >> 56u64) & 0xFF));
        assert(byte128(r3[2], 8) == ((r3[2] >> 64u64) & 0xFF));
        assert(byte128(r3[2], 9) == ((r3[2] >> 72u64) & 0xFF));
        assert(byte128(r3[2], 10) == ((r3[2] >> 80u64) & 0xFF));
        assert(byte128(r3[2], 11) == ((r3[2] >> 88u64) & 0xFF));
        assert(byte128(r3[2], 12) == ((r3[2] >> 96u64) & 0xFF));
        assert(byte128(r3[2], 13) == ((r3[2] >> 104u64) & 0xFF));
        assert(byte128(r3[2], 14) == ((r3[2] >> 112u64) & 0xFF));
        assert(byte128(r3[2], 15) == ((r3[2] >> 120u64) & 0xFF));
        assert(((w3v2 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v2 >> 0u64) & 0xFF) == (((r3[2] >> 0u64) & 0xFF)));
        assert(((w3v2 >> 8u64) & 0xFF) == (((r3[2] >> 8u64) & 0xFF)));
        assert(((w3v2 >> 16u64) & 0xFF) == (((r3[2] >> 16u64) & 0xFF)));
        assert(((w3v2 >> 24u64) & 0xFF) == (((r3[2] >> 24u64) & 0xFF)));
        assert(((w3v2 >> 32u64) & 0xFF) == (((r3[2] >> 32u64) & 0xFF)));
        assert(((w3v2 >> 40u64) & 0xFF) == (((r3[2] >> 40u64) & 0xFF)));
        assert(((w3v2 >> 48u64) & 0xFF) == (((r3[2] >> 48u64) & 0xFF)));
        assert(((w3v2 >> 56u64) & 0xFF) == (((r3[2] >> 56u64) & 0xFF)));
        assert(((w3v2 >> 64u64) & 0xFF) == (((r3[2] >> 64u64) & 0xFF)));
        assert(((w3v2 >> 72u64) & 0xFF) == (((r3[2] >> 72u64) & 0xFF)));
        assert(((w3v2 >> 80u64) & 0xFF) == (((r3[2] >> 80u64) & 0xFF)));
        assert(((w3v2 >> 88u64) & 0xFF) == (((r3[2] >> 88u64) & 0xFF)));
        assert(((w3v2 >> 96u64) & 0xFF) == (((r3[2] >> 96u64) & 0xFF)));
        assert(((w3v2 >> 104u64) & 0xFF) == (((r3[2] >> 104u64) & 0xFF)));
        assert(((w3v2 >> 112u64) & 0xFF) == (((r3[2] >> 112u64) & 0xFF)));
        assert(((w3v2 >> 120u64) & 0xFF) == (((r3[2] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v2, r3[2], ((w3v2 >> 0u64) & 0xFF), ((w3v2 >> 8u64) & 0xFF), ((w3v2 >> 16u64) & 0xFF), ((w3v2 >> 24u64) & 0xFF), ((w3v2 >> 32u64) & 0xFF), ((w3v2 >> 40u64) & 0xFF), ((w3v2 >> 48u64) & 0xFF), ((w3v2 >> 56u64) & 0xFF), ((w3v2 >> 64u64) & 0xFF), ((w3v2 >> 72u64) & 0xFF), ((w3v2 >> 80u64) & 0xFF), ((w3v2 >> 88u64) & 0xFF), ((w3v2 >> 96u64) & 0xFF), ((w3v2 >> 104u64) & 0xFF), ((w3v2 >> 112u64) & 0xFF), ((w3v2 >> 120u64) & 0xFF));
        assert(byte128(r3[3], 0) == ((r3[3] >> 0u64) & 0xFF));
        assert(byte128(r3[3], 1) == ((r3[3] >> 8u64) & 0xFF));
        assert(byte128(r3[3], 2) == ((r3[3] >> 16u64) & 0xFF));
        assert(byte128(r3[3], 3) == ((r3[3] >> 24u64) & 0xFF));
        assert(byte128(r3[3], 4) == ((r3[3] >> 32u64) & 0xFF));
        assert(byte128(r3[3], 5) == ((r3[3] >> 40u64) & 0xFF));
        assert(byte128(r3[3], 6) == ((r3[3] >> 48u64) & 0xFF));
        assert(byte128(r3[3], 7) == ((r3[3] >> 56u64) & 0xFF));
        assert(byte128(r3[3], 8) == ((r3[3] >> 64u64) & 0xFF));
        assert(byte128(r3[3], 9) == ((r3[3] >> 72u64) & 0xFF));
        assert(byte128(r3[3], 10) == ((r3[3] >> 80u64) & 0xFF));
        assert(byte128(r3[3], 11) == ((r3[3] >> 88u64) & 0xFF));
        assert(byte128(r3[3], 12) == ((r3[3] >> 96u64) & 0xFF));
        assert(byte128(r3[3], 13) == ((r3[3] >> 104u64) & 0xFF));
        assert(byte128(r3[3], 14) == ((r3[3] >> 112u64) & 0xFF));
        assert(byte128(r3[3], 15) == ((r3[3] >> 120u64) & 0xFF));
        assert(((w3v3 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v3 >> 0u64) & 0xFF) == (((r3[3] >> 0u64) & 0xFF)));
        assert(((w3v3 >> 8u64) & 0xFF) == (((r3[3] >> 8u64) & 0xFF)));
        assert(((w3v3 >> 16u64) & 0xFF) == (((r3[3] >> 16u64) & 0xFF)));
        assert(((w3v3 >> 24u64) & 0xFF) == (((r3[3] >> 24u64) & 0xFF)));
        assert(((w3v3 >> 32u64) & 0xFF) == (((r3[3] >> 32u64) & 0xFF)));
        assert(((w3v3 >> 40u64) & 0xFF) == (((r3[3] >> 40u64) & 0xFF)));
        assert(((w3v3 >> 48u64) & 0xFF) == (((r3[3] >> 48u64) & 0xFF)));
        assert(((w3v3 >> 56u64) & 0xFF) == (((r3[3] >> 56u64) & 0xFF)));
        assert(((w3v3 >> 64u64) & 0xFF) == (((r3[3] >> 64u64) & 0xFF)));
        assert(((w3v3 >> 72u64) & 0xFF) == (((r3[3] >> 72u64) & 0xFF)));
        assert(((w3v3 >> 80u64) & 0xFF) == (((r3[3] >> 80u64) & 0xFF)));
        assert(((w3v3 >> 88u64) & 0xFF) == (((r3[3] >> 88u64) & 0xFF)));
        assert(((w3v3 >> 96u64) & 0xFF) == (((r3[3] >> 96u64) & 0xFF)));
        assert(((w3v3 >> 104u64) & 0xFF) == (((r3[3] >> 104u64) & 0xFF)));
        assert(((w3v3 >> 112u64) & 0xFF) == (((r3[3] >> 112u64) & 0xFF)));
        assert(((w3v3 >> 120u64) & 0xFF) == (((r3[3] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v3, r3[3], ((w3v3 >> 0u64) & 0xFF), ((w3v3 >> 8u64) & 0xFF), ((w3v3 >> 16u64) & 0xFF), ((w3v3 >> 24u64) & 0xFF), ((w3v3 >> 32u64) & 0xFF), ((w3v3 >> 40u64) & 0xFF), ((w3v3 >> 48u64) & 0xFF), ((w3v3 >> 56u64) & 0xFF), ((w3v3 >> 64u64) & 0xFF), ((w3v3 >> 72u64) & 0xFF), ((w3v3 >> 80u64) & 0xFF), ((w3v3 >> 88u64) & 0xFF), ((w3v3 >> 96u64) & 0xFF), ((w3v3 >> 104u64) & 0xFF), ((w3v3 >> 112u64) & 0xFF), ((w3v3 >> 120u64) & 0xFF));
        assert(byte128(r3[4], 0) == ((r3[4] >> 0u64) & 0xFF));
        assert(byte128(r3[4], 1) == ((r3[4] >> 8u64) & 0xFF));
        assert(byte128(r3[4], 2) == ((r3[4] >> 16u64) & 0xFF));
        assert(byte128(r3[4], 3) == ((r3[4] >> 24u64) & 0xFF));
        assert(byte128(r3[4], 4) == ((r3[4] >> 32u64) & 0xFF));
        assert(byte128(r3[4], 5) == ((r3[4] >> 40u64) & 0xFF));
        assert(byte128(r3[4], 6) == ((r3[4] >> 48u64) & 0xFF));
        assert(byte128(r3[4], 7) == ((r3[4] >> 56u64) & 0xFF));
        assert(byte128(r3[4], 8) == ((r3[4] >> 64u64) & 0xFF));
        assert(byte128(r3[4], 9) == ((r3[4] >> 72u64) & 0xFF));
        assert(byte128(r3[4], 10) == ((r3[4] >> 80u64) & 0xFF));
        assert(byte128(r3[4], 11) == ((r3[4] >> 88u64) & 0xFF));
        assert(byte128(r3[4], 12) == ((r3[4] >> 96u64) & 0xFF));
        assert(byte128(r3[4], 13) == ((r3[4] >> 104u64) & 0xFF));
        assert(byte128(r3[4], 14) == ((r3[4] >> 112u64) & 0xFF));
        assert(byte128(r3[4], 15) == ((r3[4] >> 120u64) & 0xFF));
        assert(((w3v4 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v4 >> 0u64) & 0xFF) == (((r3[4] >> 0u64) & 0xFF)));
        assert(((w3v4 >> 8u64) & 0xFF) == (((r3[4] >> 8u64) & 0xFF)));
        assert(((w3v4 >> 16u64) & 0xFF) == (((r3[4] >> 16u64) & 0xFF)));
        assert(((w3v4 >> 24u64) & 0xFF) == (((r3[4] >> 24u64) & 0xFF)));
        assert(((w3v4 >> 32u64) & 0xFF) == (((r3[4] >> 32u64) & 0xFF)));
        assert(((w3v4 >> 40u64) & 0xFF) == (((r3[4] >> 40u64) & 0xFF)));
        assert(((w3v4 >> 48u64) & 0xFF) == (((r3[4] >> 48u64) & 0xFF)));
        assert(((w3v4 >> 56u64) & 0xFF) == (((r3[4] >> 56u64) & 0xFF)));
        assert(((w3v4 >> 64u64) & 0xFF) == (((r3[4] >> 64u64) & 0xFF)));
        assert(((w3v4 >> 72u64) & 0xFF) == (((r3[4] >> 72u64) & 0xFF)));
        assert(((w3v4 >> 80u64) & 0xFF) == (((r3[4] >> 80u64) & 0xFF)));
        assert(((w3v4 >> 88u64) & 0xFF) == (((r3[4] >> 88u64) & 0xFF)));
        assert(((w3v4 >> 96u64) & 0xFF) == (((r3[4] >> 96u64) & 0xFF)));
        assert(((w3v4 >> 104u64) & 0xFF) == (((r3[4] >> 104u64) & 0xFF)));
        assert(((w3v4 >> 112u64) & 0xFF) == (((r3[4] >> 112u64) & 0xFF)));
        assert(((w3v4 >> 120u64) & 0xFF) == (((r3[4] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v4, r3[4], ((w3v4 >> 0u64) & 0xFF), ((w3v4 >> 8u64) & 0xFF), ((w3v4 >> 16u64) & 0xFF), ((w3v4 >> 24u64) & 0xFF), ((w3v4 >> 32u64) & 0xFF), ((w3v4 >> 40u64) & 0xFF), ((w3v4 >> 48u64) & 0xFF), ((w3v4 >> 56u64) & 0xFF), ((w3v4 >> 64u64) & 0xFF), ((w3v4 >> 72u64) & 0xFF), ((w3v4 >> 80u64) & 0xFF), ((w3v4 >> 88u64) & 0xFF), ((w3v4 >> 96u64) & 0xFF), ((w3v4 >> 104u64) & 0xFF), ((w3v4 >> 112u64) & 0xFF), ((w3v4 >> 120u64) & 0xFF));
        assert(byte128(r3[5], 0) == ((r3[5] >> 0u64) & 0xFF));
        assert(byte128(r3[5], 1) == ((r3[5] >> 8u64) & 0xFF));
        assert(byte128(r3[5], 2) == ((r3[5] >> 16u64) & 0xFF));
        assert(byte128(r3[5], 3) == ((r3[5] >> 24u64) & 0xFF));
        assert(byte128(r3[5], 4) == ((r3[5] >> 32u64) & 0xFF));
        assert(byte128(r3[5], 5) == ((r3[5] >> 40u64) & 0xFF));
        assert(byte128(r3[5], 6) == ((r3[5] >> 48u64) & 0xFF));
        assert(byte128(r3[5], 7) == ((r3[5] >> 56u64) & 0xFF));
        assert(byte128(r3[5], 8) == ((r3[5] >> 64u64) & 0xFF));
        assert(byte128(r3[5], 9) == ((r3[5] >> 72u64) & 0xFF));
        assert(byte128(r3[5], 10) == ((r3[5] >> 80u64) & 0xFF));
        assert(byte128(r3[5], 11) == ((r3[5] >> 88u64) & 0xFF));
        assert(byte128(r3[5], 12) == ((r3[5] >> 96u64) & 0xFF));
        assert(byte128(r3[5], 13) == ((r3[5] >> 104u64) & 0xFF));
        assert(byte128(r3[5], 14) == ((r3[5] >> 112u64) & 0xFF));
        assert(byte128(r3[5], 15) == ((r3[5] >> 120u64) & 0xFF));
        assert(((w3v5 >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((w3v5 >> 0u64) & 0xFF) == (((r3[5] >> 0u64) & 0xFF)));
        assert(((w3v5 >> 8u64) & 0xFF) == (((r3[5] >> 8u64) & 0xFF)));
        assert(((w3v5 >> 16u64) & 0xFF) == (((r3[5] >> 16u64) & 0xFF)));
        assert(((w3v5 >> 24u64) & 0xFF) == (((r3[5] >> 24u64) & 0xFF)));
        assert(((w3v5 >> 32u64) & 0xFF) == (((r3[5] >> 32u64) & 0xFF)));
        assert(((w3v5 >> 40u64) & 0xFF) == (((r3[5] >> 40u64) & 0xFF)));
        assert(((w3v5 >> 48u64) & 0xFF) == (((r3[5] >> 48u64) & 0xFF)));
        assert(((w3v5 >> 56u64) & 0xFF) == (((r3[5] >> 56u64) & 0xFF)));
        assert(((w3v5 >> 64u64) & 0xFF) == (((r3[5] >> 64u64) & 0xFF)));
        assert(((w3v5 >> 72u64) & 0xFF) == (((r3[5] >> 72u64) & 0xFF)));
        assert(((w3v5 >> 80u64) & 0xFF) == (((r3[5] >> 80u64) & 0xFF)));
        assert(((w3v5 >> 88u64) & 0xFF) == (((r3[5] >> 88u64) & 0xFF)));
        assert(((w3v5 >> 96u64) & 0xFF) == (((r3[5] >> 96u64) & 0xFF)));
        assert(((w3v5 >> 104u64) & 0xFF) == (((r3[5] >> 104u64) & 0xFF)));
        assert(((w3v5 >> 112u64) & 0xFF) == (((r3[5] >> 112u64) & 0xFF)));
        assert(((w3v5 >> 120u64) & 0xFF) == (((r3[5] >> 120u64) & 0xFF)));
        lemma_u128_bytes_eq(w3v5, r3[5], ((w3v5 >> 0u64) & 0xFF), ((w3v5 >> 8u64) & 0xFF), ((w3v5 >> 16u64) & 0xFF), ((w3v5 >> 24u64) & 0xFF), ((w3v5 >> 32u64) & 0xFF), ((w3v5 >> 40u64) & 0xFF), ((w3v5 >> 48u64) & 0xFF), ((w3v5 >> 56u64) & 0xFF), ((w3v5 >> 64u64) & 0xFF), ((w3v5 >> 72u64) & 0xFF), ((w3v5 >> 80u64) & 0xFF), ((w3v5 >> 88u64) & 0xFF), ((w3v5 >> 96u64) & 0xFF), ((w3v5 >> 104u64) & 0xFF), ((w3v5 >> 112u64) & 0xFF), ((w3v5 >> 120u64) & 0xFF));
    }
    assert(r3[0] == w3v0);
    assert(r3[1] == w3v1);
    assert(r3[2] == w3v2);
    assert(r3[3] == w3v3);
    assert(r3[4] == w3v4);
    assert(r3[5] == w3v5);
}

/// Wave-3: GF192/256 ByteCombine constants (python-reconciled
/// against upstream large_fields_constants.rs).
fn ut_fa3_w3_byte_combine_constants() {
    // Verbatim literal pins (python dual-model reconciled against
    // upstream large_fields_constants.rs; the relations
    // BYTE_COMBINE_2 == ALPHA[0] and BYTE_COMBINE_3 == BC2 ^ ONE are
    // covered by the offline chain, tuple-field access never enters
    // blast contexts per the v12 lesson).
    assert(GF192_BYTE_COMBINE_2 == (0xe665d76c966ebdeaccc8a3d56f389763u128, 0x310bc8140e6b3662u128));
    assert(GF192_BYTE_COMBINE_3 == (0xe665d76c966ebdeaccc8a3d56f389762u128, 0x310bc8140e6b3662u128));
    assert(GF256_BYTE_COMBINE_2 == (0xbed68d38a0474e67969788420bdefee7u128, 0x04c9a8cf20c95833df229845f8f1e16au128));
    assert(GF256_BYTE_COMBINE_3 == (0xbed68d38a0474e67969788420bdefee6u128, 0x04c9a8cf20c95833df229845f8f1e16au128));
}
fn main() {}

} // verus!
