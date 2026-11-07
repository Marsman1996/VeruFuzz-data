//! verified/src/catalog.rs -- dependency adaptation: a crc-catalog 2.4.0 subset (verbatim).
//!
//! [Origin Rust: external crate `crc_catalog` (crates.io crc-catalog 2.4.0)]
//! Upstream crc 3.4.0 (pin 1894aa9) references the external crate via `pub use crc_catalog::...`.
//! A Verus single-driver build cannot link the external crate, so per kverus-migrate rule 5 ("minimal
//! dependency adaptation") the types used by the verified paths (Algorithm / the Width trait) and
//! their constants are brought verbatim into a local module; constant values are taken from
//! crc-catalog-2.4.0/src/algorithm.rs (crates.io registry copy, verbatim).
//!
//! Selection criterion for the constant subset = this crate's UT/correctness tests and harness target operators:
//!   CRC_8_BLUETOOTH / CRC_5_USB (u8 and sub-full-width reflected representatives)
//!   CRC_16_IBM_SDLC / CRC_16_XMODEM / CRC_14_DARC (three u16-family representatives)
//!   CRC_32_ISCSI / CRC_32_MPEG_2 / CRC_24_BLE / CRC_24_OPENPGP / CRC_30_CDMA
//!   CRC_64_ECMA_182 / CRC_40_GSM
//!   CRC_82_DARC
//! The remaining ~100 catalog constants and the `algorithm`/`poly` modules are outside the verification closure, not mirrored.
//! verus! wrapper (verus items must be declared inside the macro).

use vstd::prelude::*;

/// [Origin Rust: crc-catalog 2.4.0 src/lib.rs -- trait Width definition, verbatim]
verus! {
pub trait Width: Sized + 'static {}
impl Width for u8 {}
impl Width for u16 {}
impl Width for u32 {}
impl Width for u64 {}
impl Width for u128 {}

/// [Origin Rust: crc-catalog 2.4.0 src/lib.rs -- pub struct Algorithm definition, verbatim]
pub struct Algorithm<W: Width> {
    pub width: u8,
    pub poly: W,
    pub init: W,
    pub refin: bool,
    pub refout: bool,
    pub xorout: W,
    pub check: W,
    pub residue: W,
}

// -- constants below taken verbatim from crc-catalog-2.4.0/src/algorithm.rs (single-line layout preserved) --

pub const CRC_5_USB: Algorithm<u8> = Algorithm { width: 5, poly: 0x05, init: 0x1f, refin: true, refout: true, xorout: 0x1f, check: 0x19, residue: 0x06 };
pub const CRC_8_BLUETOOTH: Algorithm<u8> = Algorithm { width: 8, poly: 0xa7, init: 0x00, refin: true, refout: true, xorout: 0x00, check: 0x26, residue: 0x00 };
pub const CRC_14_DARC: Algorithm<u16> = Algorithm { width: 14, poly: 0x0805, init: 0x0000, refin: true, refout: true, xorout: 0x0000, check: 0x082d, residue: 0x0000 };
pub const CRC_16_IBM_SDLC: Algorithm<u16> = Algorithm { width: 16, poly: 0x1021, init: 0xffff, refin: true, refout: true, xorout: 0xffff, check: 0x906e, residue: 0xf0b8 };
pub const CRC_16_XMODEM: Algorithm<u16> = Algorithm { width: 16, poly: 0x1021, init: 0x0000, refin: false, refout: false, xorout: 0x0000, check: 0x31c3, residue: 0x0000 };
pub const CRC_24_BLE: Algorithm<u32> = Algorithm { width: 24, poly: 0x00065b, init: 0x555555, refin: true, refout: true, xorout: 0x000000, check: 0xc25a56, residue: 0x000000 };
pub const CRC_24_OPENPGP: Algorithm<u32> = Algorithm { width: 24, poly: 0x864cfb, init: 0xb704ce, refin: false, refout: false, xorout: 0x000000, check: 0x21cf02, residue: 0x000000 };
pub const CRC_30_CDMA: Algorithm<u32> = Algorithm { width: 30, poly: 0x2030b9c7, init: 0x3fffffff, refin: false, refout: false, xorout: 0x3fffffff, check: 0x04c34abf, residue: 0x34efa55a };
pub const CRC_32_ISCSI: Algorithm<u32> = Algorithm { width: 32, poly: 0x1edc6f41, init: 0xffffffff, refin: true, refout: true, xorout: 0xffffffff, check: 0xe3069283, residue: 0xb798b438 };
pub const CRC_32_MPEG_2: Algorithm<u32> = Algorithm { width: 32, poly: 0x04c11db7, init: 0xffffffff, refin: false, refout: false, xorout: 0x00000000, check: 0x0376e6e7, residue: 0x00000000 };
pub const CRC_40_GSM: Algorithm<u64> = Algorithm { width: 40, poly: 0x0004820009, init: 0x0000000000, refin: false, refout: false, xorout: 0xffffffffff, check: 0xd4164fc646, residue: 0xc4ff8071ff };
pub const CRC_64_ECMA_182: Algorithm<u64> = Algorithm { width: 64, poly: 0x42f0e1eba9ea3693, init: 0x0000000000000000, refin: false, refout: false, xorout: 0x0000000000000000, check: 0x6c40df5f0b497347, residue: 0x0000000000000000 };
pub const CRC_82_DARC: Algorithm<u128> = Algorithm { width: 82, poly: 0x0308c0111011401440411, init: 0x000000000000000000000, refin: true, refout: true, xorout: 0x000000000000000000000, check: 0x09ea83f625023801fd612, residue: 0x000000000000000000000 };

} // verus!