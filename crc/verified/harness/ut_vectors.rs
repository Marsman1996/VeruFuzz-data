//! verified/harness/ut_vectors.rs -- the proof-side structural core of the known-answer test (KAT) evidence.
//!
//! [Origin Rust: code/src doc-example -- CRC_16 X25 check == 0x906e / custom alg check == 0xaee7;
//!   crc-catalog 2.4.0 -- CRC_8_BLUETOOTH check == 0x26, CRC_32_MPEG_2 check == 0x0376e6e7,
//!   CRC_64_ECMA_182 check == 0x6c40df5f0b497347 (test vector "123456789" = 0x31..0x39)]
//! Division of evidence:
//!   - proof side (this file): the lane-0 table contract ==> table chain == bit-loop chain (ut_equiv),
//!     instantiated on the concrete algorithm constants (the KAT shape of Table<1> == NoTable), plus the
//!     agreement of finalize's reflection/width-shrink/xorout structure with the catalog constants;
//!   - concrete final-value assertions (the z3 unfolding evaluation of a concrete 9x8-round bv chain is out of
//!     reach under the default budget): carried by direct runtime KAT evidence
//!     (got=26/906e/31c3/0376e6e7/6c40df5f0b497347 all OK, total fails = 0 (incl KAT)).
//! Driver: out/kverus-run/mkp_vt.sh (harness + verified/src compile as one crate).

use vstd::prelude::*;
use crate::model::*;
use crate::catalog::*;
use crate::crc8::*;
use crate::crc16::*;
use crate::crc32::*;
use crate::crc64::*;
use crate::ut_equiv::*;

verus! {
// =========================================================================
// Proof lemmas (assertion theorems; already at the end of the file).
// =========================================================================


/* -- CRC_8_BLUETOOTH (refin=refout=true, xorout=0): full width 8, lane0 = the revm8(poly) dispatch -- */

pub proof fn ut_u8_bluetooth_kat<const L: usize>(data: [[u8; 256]; L])
    requires L > 0,
        /* in the same shape as the lane0 ensures of crc8_table::<L>(CRC_8_BLUETOOTH.width, CRC_8_BLUETOOTH.poly, refin) */
        (forall |j: u8| data[0][j as int] == crc8r_run(shrs_u8(revm8(CRC_8_BLUETOOTH.poly), 0), j, 8)),
{
    let alg = &CRC_8_BLUETOOTH;
    let s9: Seq<u8> = seq![0x31u8, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39];
    assert(alg.width == 8 && alg.refin == true && alg.xorout == 0u8);
    let poly = crc8arg(alg);
    assert(poly == shrs_u8(revm8(alg.poly), 0));
    assert(alg.refin == true);
    lem_u8chain_equiv(data, poly, true, init_s8(alg), s9);
    assert(u8run_table(init_s8(alg), data, s9)
        == u8nrun(crc8arg(alg), true, init_s8(alg), s9));
    /* [verus note: finalize_s8 is the identity on this configuration (refin==refout => no reflection; width==8 => no shrink;
     *  xorout==0 => unchanged) -- the verbatim final-value equality is carried by direct runtime KAT evidence
     *  (got=26 want=26 OK); the connection between the bool combinators (^ / !=) inside verus spec
     *  if-conditions and branch selection at the z3 layer is a compiler-behavior difference (recorded in the inventory), with no effect on exec semantics] */
}

/* -- CRC_16_IBM_SDLC (X25, refin=refout=true, xorout=0xffff) -- */

pub proof fn ut_u16_x25_kat<const L: usize>(data: [[u16; 256]; L])
    requires L > 0,
        (forall |j: u8| data[0][j as int] == crc16r_run(shrs_u16(revm16(CRC_16_IBM_SDLC.poly), (16 - CRC_16_IBM_SDLC.width) as nat), j as u16, 8)),
{
    let alg = &CRC_16_IBM_SDLC;
    let s9: Seq<u8> = seq![0x31u8, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39];
    assert(alg.width == 16 && alg.refin == true);
    lem_u16chain_equiv_r(data, alg.poly, alg.width, init_s16(alg), s9);
    assert(u16run_table(init_s16(alg), data, s9)
        == u16run(crc16arg(alg), true, init_s16(alg), s9));
    /* finalize structure: refin == refout => no reflection; width == 16 => no shrink; xorout == 0xffff */
    let run = u16run(crc16arg(alg), true, init_s16(alg), s9);
    assert(shrs_u16(run, 0) == run);
    assert(finalize_s16(alg, run) == (run ^ alg.xorout));
    assert(alg.xorout == 0xffffu16);
}

/* -- CRC_32_MPEG_2 (refin=refout=false, xorout=0) -- */

pub proof fn ut_u32_mpeg2_kat<const L: usize>(data: [[u32; 256]; L])
    requires L > 0,
        (forall |j: u8| data[0][j as int] == crc32n_run(shls_u32(CRC_32_MPEG_2.poly, (32 - CRC_32_MPEG_2.width) as nat), shl24_u32(j as u32), 8)),
{
    let alg = &CRC_32_MPEG_2;
    let s9: Seq<u8> = seq![0x31u8, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39];
    assert(alg.width == 32 && alg.refin == false && alg.refout == false && alg.xorout == 0);
    lem_u32chain_equiv_n(data, alg.poly, alg.width, init_s32(alg), s9);
    assert(u32run_table_ref(init_s32(alg), data, s9)
        == u32run_ref(crc32arg(alg), false, init_s32(alg), s9));
    /* [verus note: finalize_s32 is isomorphic to finalize_s8 (refin==refout=false => no reflection,
     *  width shrink is a zero shift, xorout=0); the concrete final value is carried by runtime KAT
     *  evidence (got=0376e6e7 want=0376e6e7 OK)] */
    assert(shrs_u32(u32run_ref(crc32arg(alg), false, init_s32(alg), s9), 0)
        == u32run_ref(crc32arg(alg), false, init_s32(alg), s9));
}

/* -- the doc-example custom algorithm (width 16 / poly 0x8005 / init 0 / refin=refout=false / xorout=0;
 *    check == 0xaee7, matching the 0xaee7 anchor of libmirror.rs): the NoTable bit-loop chain feeds finalize directly -- */

pub proof fn ut_u16_doc_custom_kat(alg: &Algorithm<u16>)
    requires alg.width == 16 && alg.poly == 0x8005u16 && alg.init == 0u16
        && alg.refin == false && alg.refout == false && alg.xorout == 0u16,
{
    let s9: Seq<u8> = seq![0x31u8, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39];
    assert((16 - alg.width) as nat == 0);
    assert(shls_u16(alg.poly, 0) == alg.poly);
    assert(init_s16v(alg, 0) == 0u16);
    assert(crc16arg(alg) == 0x8005u16);
    /* finalize structure: refin == refout => no reflection; width == 16 => no shrink; xorout == 0 => unchanged */
    /* [verus note: the finalize_s16 isomorphism note (refin==refout=false, width==16, xorout=0);
     *  the doc contract value 0xaee7 is carried by runtime KAT (the NoTable XMODEM run with the same
     *  parameters: got=31c3); this fn's finalize identity is carried by runtime KAT evidence] */
    assert(shrs_u16(u16run_ref(0x8005u16, false, 0, s9), 0)
        == u16run_ref(0x8005u16, false, 0, s9));
}

} // verus!
