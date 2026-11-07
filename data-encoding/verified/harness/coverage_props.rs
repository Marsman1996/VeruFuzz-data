//! harness: auto-generated -- the coverage difference set (the Encoding
//! public-face APIs neither directly exercised by the UTs nor covered by batches 2/3):
//!  - Character + is_symbol/is_padding/is_ignored/is_invalid (lib.rs:843-891)
//!  - Encoding::interpret_byte (lib.rs:1659-1667, the HEXLOWER/HEXUPPER table special case)
//!  - Encoding::is_canonical (lib.rs:1668-1697, the L2 contract that always holds for the hex family)
//!  - Encoding::bit_width / encode_align / decode_align (lib.rs:1343/1655/1562)
//! Reference-style organization: `#[path]` pulls in verified/src/lib.rs, without copying its spec.
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod data_encoding;

use data_encoding::*;

verus! {

/* ---------- Character (Origin: lib.rs:849-891) ---------- */

/// Origin: lib.rs:849-864 `pub enum Character`
#[derive(PartialEq, Eq)]
pub enum Character {
    Symbol { value: usize },
    Padding,
    Ignored,
    Invalid,
}

/// Origin: lib.rs:866-875 `Character::is_symbol(self) -> Option<usize>`
/// Upstream doc (lib.rs:867-869):
///   Returns whether the character is a symbol
///   If the character is a symbol, its value is returned.
pub exec fn character_is_symbol(self_: Character) -> (r: Option<usize>)
    ensures
        ({
            match self_ {
                Character::Symbol { value } => r == Option::Some(value),
                _ => r == Option::None,
            }
        })
{
    match self_ {
        Character::Symbol { value } => Option::Some(value),
        _ => Option::None,
    }
}

/// Origin: lib.rs:877-880 `Character::is_padding`
/// Upstream doc (lib.rs:877-877):
///   Returns whether the character is padding
pub exec fn character_is_padding(self_: Character) -> (r: bool)
    ensures
        ({
            match self_ {
                Character::Padding => r == true,
                _ => r == false,
            }
        })
{
    match self_ {
        Character::Padding => true,
        _ => false,
    }
}

/// Origin: lib.rs:882-885 `Character::is_ignored`
/// Upstream doc (lib.rs:882-882):
///   Returns whether the character is ignored
pub exec fn character_is_ignored(self_: Character) -> (r: bool)
    ensures
        ({
            match self_ {
                Character::Ignored => r == true,
                _ => r == false,
            }
        })
{
    match self_ {
        Character::Ignored => true,
        _ => false,
    }
}

/// Origin: lib.rs:887-890 `Character::is_invalid`
/// Upstream doc (lib.rs:887-887):
///   Returns whether the character is invalid
pub exec fn character_is_invalid(self_: Character) -> (r: bool)
    ensures
        ({
            match self_ {
                Character::Invalid => r == true,
                _ => r == false,
            }
        })
{
    match self_ {
        Character::Invalid => true,
        _ => false,
    }
}

/* ---------- interpret_byte (Origin: lib.rs:1659-1667) ---------- */

/// Origin: lib.rs:1660-1667 `Encoding::interpret_byte(&self, byte)`
///   match self.val()[byte as usize] { INVALID=>Invalid, ... value=>Symbol };
/// The HEXLOWER/HEXUPPER val table has no IGNORE(129)/PADDING(130) entries (interval
/// logic; the table <=> interval equivalence is witnessed at runtime against the upstream
/// pin tree), => Character::Symbol
/// Upstream doc (lib.rs:1659-1659):
///   Interprets a byte as a character
pub exec fn interpret_byte_hex(byte: u8, upper: bool) -> (r: Character)
    ensures
        ({
            let v = hex_val(byte, upper);
            (v == INVALID ==> r == Character::Invalid)
                && (v != INVALID ==> r == Character::Symbol { value: v as usize })
        })
{
    let v = hex_value(byte, upper);
    if v == INVALID {
        Character::Invalid
    } else {
        Character::Symbol { value: v as usize }
    }
}

/* ---------- is_canonical (Origin: lib.rs:1668-1697) ---------- */

/// spec site: the hex family satisfies the canonical clause of the encoding invariants
///   (lib.rs:903-922 "values and symbols are inverse" + ctb)
pub open spec fn hex_canonical(upper: bool) -> bool {
    forall|c: u8|
        hex_val(c, upper) != INVALID ==> hex_sym(hex_val(c, upper), upper) == c
}

/// Origin: lib.rs:1678-1697 `Encoding::is_canonical(&self) -> bool`
///   ctb==true; the loop scans the 256-byte table (after the interval-logic rewrite exactly the equivalent model above);
///   lemma_hex_val_sym_inverse => always true
/// Upstream doc (lib.rs:1669-1676):
///   Returns whether the encoding is canonical
///   An encoding is not canonical if one of the following conditions holds:
///   - trailing bits are not checked
///   - padding is used
///   - characters are ignored
///   - characters are translated
pub exec fn is_canonical_hex(upper: bool) -> (r: bool)
    ensures r == hex_canonical(upper)
{
    proof { lemma_hex_val_sym_inverse(upper); }
    true
}

/* ---------- bit_width / align family (Origin: lib.rs:1343/1655/1562) ---------- */

exec fn ut_align_rows()
{
    // BASE64: decode_align==4, encode_align==3, bit_width==6
    let d6 = decode_align(6);
    assert(d6 == 4);
    let e6 = encoding_encode_align(6, Option::None);
    assert(e6 == 3);
    let w6 = bit_width(6);
    assert(w6 == 6);
    // BASE32: dec==8 enc==5; HEXLOWER: 2/1; binary bit=1: 8/1
    let d5 = decode_align(5);
    assert(d5 == 8);
    let e5 = encoding_encode_align(5, Option::None);
    assert(e5 == 5);
    let d4 = decode_align(4);
    assert(d4 == 2);
    let e4 = encoding_encode_align(4, Option::None);
    assert(e4 == 1);
    let d1 = decode_align(1);
    assert(d1 == 8);
    let e1 = encoding_encode_align(1, Option::None);
    assert(e1 == 1);
    // with a wrap present encode_align = col*bit/8 (e.g. base64 wrap col=8 => 6)
    let ew = encoding_encode_align(6, Some((8, &[][..])));
    assert(ew == 6);
}


// ===========================================================================
// Proof lemmas (the hex val/sym inverse lemma backing is_canonical_hex)
// ===========================================================================
/// Out-of-range bytes are all Invalid (the first guard of the canonical check always passes: the val[i]==INVALID entries are skipped)
pub proof fn lemma_hex_val_sym_inverse(upper: bool)
    ensures hex_canonical(upper)
{
    assert forall|c: u8| hex_val(c, upper) != INVALID implies hex_sym(
        hex_val(c, upper),
        upper,
    ) == c by {
        let v = hex_val(c, upper);
        assert(v < 16);
        let sym = hex_sym(v, upper);
        if v < 10 {
            assert(sym == (0x30 + v as int) as u8);
            if upper {
                assert(0x30 <= c <= 0x39);
            } else {
                assert(0x30 <= c <= 0x39);
            }
            assert(c == (0x30 + v as int) as u8);
        } else if upper {
            assert(sym == (0x41 + (v as int - 10)) as u8);
            assert(0x41 <= c <= 0x46);
            assert(c == (0x41 + (v as int - 10)) as u8);
        } else {
            assert(sym == (0x61 + (v as int - 10)) as u8);
            assert(0x61 <= c <= 0x66);
            assert(c == (0x61 + (v as int - 10)) as u8);
        }
    }
}
}

fn main() {}
