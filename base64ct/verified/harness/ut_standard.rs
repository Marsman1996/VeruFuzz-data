//! harness: the formalization of tests/standard.rs (UT A1/A2)
//! -- the encode vectors of Base64 (padded) / Base64Unpadded (at the pos-model level)
//!   plus provable-reject cases (the %4 channel).
//! Composition: encode_std's verified general contract links the model to the runtime output
//! (val point 1: `forall j < elen: final(dst)@[j] == b64_encode_model_std(src@, ...)[j]`),
//! so this per-group formalization of "model == upstream vector string" is exactly the _UT assertion over encode_std.
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod base64ct_v;

use base64ct_v::alphabet::standard::b64_encode_pos_std;
use base64ct_v::alphabet::standard::lemma_enc_index;
use base64ct_v::encoding::decode_std;
use base64ct_v::encoding::encode_std;
use base64ct_v::errors::Error;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ============ provable rejects (a %4_face+ channel instance of padded) ============ */

/// Reject face (padded): an input with trailing whitespace and len == 1 (mod 4) is judged Err on the structural face.
/// Note: the original upstream reject_trailing_whitespace vector (43+\n, == 0 mod 4, goes through the
/// invalid-character channel, not closed here) -- this file provides a provable instance of the same family.
pub exec fn reject_trailing_whitespace_padded()
{
    let input: &[u8] = b"AA==\n";
    assert(input.len() == 5);
    assert(input.len() % 4 != 0);
    let mut dst = [0u8; 1024];
    let r = decode_std(input, &mut dst, true);
    assert(r == Result::Err(Error::InvalidEncoding));
}

/// Capacity face: pad OK + dlen > capacity ==> Err(InvalidLength) -- the undersized-buffer
/// corner of the upstream `encode_and_decode_various_lengths` (via the decode-capacity model)
pub exec fn insufficient_dst()
{
    let mut dst = [0u8; 2];
    let mut input: [u8; 8] = [0x41, 0x51, 0x49, 0x44, 0x42, 0x41, 0x3D, 0x3D];
    proof {
        assert(input@.len() == 8);
        assert(input@ [6] == 0x3D);
        assert(input@ [7] == 0x3D);
    }
    let r = decode_std(&input, &mut dst, true);
    assert(r == Result::Err(Error::InvalidLength));
}

// ===========================================================================
// Vector case lemmas (placed at the file end; signatures and contracts untouched)
// ===========================================================================
pub proof fn vec_padded_empty() {
    let src: Seq<u8> = Seq::empty();
    let want: Seq<u8> = Seq::empty();
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, true);
    assert(m.len() as int == 0);
    assert forall|j: int| 0 <= j < 0 implies m[j] == want[j] by {
        lemma_enc_index(src, true, j);

    }
    assert(m == want);
}

pub proof fn vec_padded_1() {
    let src: Seq<u8> = seq![0x0];
    let want: Seq<u8> = seq![0x41, 0x41, 0x3d, 0x3d];
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, true);
    assert(m.len() as int == 4);
    assert forall|j: int| 0 <= j < 4 implies m[j] == want[j] by {
        lemma_enc_index(src, true, j);
        assert(b64_encode_pos_std(src, true, 0) == 0x41);
        assert(b64_encode_pos_std(src, true, 1) == 0x41);
        assert(b64_encode_pos_std(src, true, 2) == 0x3d);
        assert(b64_encode_pos_std(src, true, 3) == 0x3d);
    }
    assert(m == want);
}

pub proof fn vec_padded_3() {
    let src: Seq<u8> = seq![0x2a, 0x2a, 0x2a];
    let want: Seq<u8> = seq![0x4b, 0x69, 0x6f, 0x71];
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, true);
    assert(m.len() as int == 4);
    assert forall|j: int| 0 <= j < 4 implies m[j] == want[j] by {
        lemma_enc_index(src, true, j);
        assert(b64_encode_pos_std(src, true, 0) == 0x4b);
        assert(b64_encode_pos_std(src, true, 1) == 0x69);
        assert(b64_encode_pos_std(src, true, 2) == 0x6f);
        assert(b64_encode_pos_std(src, true, 3) == 0x71);
    }
    assert(m == want);
}

pub proof fn vec_padded_4() {
    let src: Seq<u8> = seq![0x1, 0x2, 0x3, 0x4];
    let want: Seq<u8> = seq![0x41, 0x51, 0x49, 0x44, 0x42, 0x41, 0x3d, 0x3d];
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, true);
    assert(m.len() as int == 8);
    assert forall|j: int| 0 <= j < 8 implies m[j] == want[j] by {
        lemma_enc_index(src, true, j);
        assert(b64_encode_pos_std(src, true, 0) == 0x41);
        assert(b64_encode_pos_std(src, true, 1) == 0x51);
        assert(b64_encode_pos_std(src, true, 2) == 0x49);
        assert(b64_encode_pos_std(src, true, 3) == 0x44);
        assert(b64_encode_pos_std(src, true, 4) == 0x42);
        assert(b64_encode_pos_std(src, true, 5) == 0x41);
        assert(b64_encode_pos_std(src, true, 6) == 0x3d);
        assert(b64_encode_pos_std(src, true, 7) == 0x3d);
    }
    assert(m == want);
}

pub proof fn vec_padded_5() {
    let src: Seq<u8> = seq![0xad, 0xad, 0xad, 0xad, 0xad];
    let want: Seq<u8> = seq![0x72, 0x61, 0x32, 0x74, 0x72, 0x61, 0x30, 0x3d];
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, true);
    assert(m.len() as int == 8);
    assert forall|j: int| 0 <= j < 8 implies m[j] == want[j] by {
        lemma_enc_index(src, true, j);
        assert(b64_encode_pos_std(src, true, 0) == 0x72);
        assert(b64_encode_pos_std(src, true, 1) == 0x61);
        assert(b64_encode_pos_std(src, true, 2) == 0x32);
        assert(b64_encode_pos_std(src, true, 3) == 0x74);
        assert(b64_encode_pos_std(src, true, 4) == 0x72);
        assert(b64_encode_pos_std(src, true, 5) == 0x61);
        assert(b64_encode_pos_std(src, true, 6) == 0x30);
        assert(b64_encode_pos_std(src, true, 7) == 0x3d);
    }
    assert(m == want);
}

pub proof fn vec_padded_6() {
    let src: Seq<u8> = seq![0xff, 0xef, 0xfe, 0xff, 0xef, 0xfe];
    let want: Seq<u8> = seq![0x2f, 0x2b, 0x2f, 0x2b, 0x2f, 0x2b, 0x2f, 0x2b];
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, true);
    assert(m.len() as int == 8);
    assert forall|j: int| 0 <= j < 8 implies m[j] == want[j] by {
        lemma_enc_index(src, true, j);
        assert(b64_encode_pos_std(src, true, 0) == 0x2f);
        assert(b64_encode_pos_std(src, true, 1) == 0x2b);
        assert(b64_encode_pos_std(src, true, 2) == 0x2f);
        assert(b64_encode_pos_std(src, true, 3) == 0x2b);
        assert(b64_encode_pos_std(src, true, 4) == 0x2f);
        assert(b64_encode_pos_std(src, true, 5) == 0x2b);
        assert(b64_encode_pos_std(src, true, 6) == 0x2f);
        assert(b64_encode_pos_std(src, true, 7) == 0x2b);
    }
    assert(m == want);
}

pub proof fn vec_padded_7() {
    let src: Seq<u8> = seq![0xff, 0xff, 0xff, 0xff, 0xff];
    let want: Seq<u8> = seq![0x2f, 0x2f, 0x2f, 0x2f, 0x2f, 0x2f, 0x38, 0x3d];
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, true);
    assert(m.len() as int == 8);
    assert forall|j: int| 0 <= j < 8 implies m[j] == want[j] by {
        lemma_enc_index(src, true, j);
        assert(b64_encode_pos_std(src, true, 0) == 0x2f);
        assert(b64_encode_pos_std(src, true, 1) == 0x2f);
        assert(b64_encode_pos_std(src, true, 2) == 0x2f);
        assert(b64_encode_pos_std(src, true, 3) == 0x2f);
        assert(b64_encode_pos_std(src, true, 4) == 0x2f);
        assert(b64_encode_pos_std(src, true, 5) == 0x2f);
        assert(b64_encode_pos_std(src, true, 6) == 0x38);
        assert(b64_encode_pos_std(src, true, 7) == 0x3d);
    }
    assert(m == want);
}

pub proof fn vec_unpadded_empty() {
    let src: Seq<u8> = Seq::empty();
    let want: Seq<u8> = Seq::empty();
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, false);
    assert(m.len() as int == 0);
    assert forall|j: int| 0 <= j < 0 implies m[j] == want[j] by {
        lemma_enc_index(src, false, j);

    }
    assert(m == want);
}

pub proof fn vec_unpadded_1() {
    let src: Seq<u8> = seq![0x0];
    let want: Seq<u8> = seq![0x41, 0x41];
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, false);
    assert(m.len() as int == 2);
    assert forall|j: int| 0 <= j < 2 implies m[j] == want[j] by {
        lemma_enc_index(src, false, j);
        assert(b64_encode_pos_std(src, false, 0) == 0x41);
        assert(b64_encode_pos_std(src, false, 1) == 0x41);
    }
    assert(m == want);
}

pub proof fn vec_unpadded_4() {
    let src: Seq<u8> = seq![0x1, 0x2, 0x3, 0x4];
    let want: Seq<u8> = seq![0x41, 0x51, 0x49, 0x44, 0x42, 0x41];
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, false);
    assert(m.len() as int == 6);
    assert forall|j: int| 0 <= j < 6 implies m[j] == want[j] by {
        lemma_enc_index(src, false, j);
        assert(b64_encode_pos_std(src, false, 0) == 0x41);
        assert(b64_encode_pos_std(src, false, 1) == 0x51);
        assert(b64_encode_pos_std(src, false, 2) == 0x49);
        assert(b64_encode_pos_std(src, false, 3) == 0x44);
        assert(b64_encode_pos_std(src, false, 4) == 0x42);
        assert(b64_encode_pos_std(src, false, 5) == 0x41);
    }
    assert(m == want);
}

pub proof fn vec_unpadded_5() {
    let src: Seq<u8> = seq![0xff, 0xff, 0xff, 0xff, 0xff];
    let want: Seq<u8> = seq![0x2f, 0x2f, 0x2f, 0x2f, 0x2f, 0x2f, 0x38];
    let m = base64ct_v::alphabet::standard::b64_encode_model_std(src, false);
    assert(m.len() as int == 7);
    assert forall|j: int| 0 <= j < 7 implies m[j] == want[j] by {
        lemma_enc_index(src, false, j);
        assert(b64_encode_pos_std(src, false, 0) == 0x2f);
        assert(b64_encode_pos_std(src, false, 1) == 0x2f);
        assert(b64_encode_pos_std(src, false, 2) == 0x2f);
        assert(b64_encode_pos_std(src, false, 3) == 0x2f);
        assert(b64_encode_pos_std(src, false, 4) == 0x2f);
        assert(b64_encode_pos_std(src, false, 5) == 0x2f);
        assert(b64_encode_pos_std(src, false, 6) == 0x38);
    }
    assert(m == want);
}
} // verus!

fn main() {}
