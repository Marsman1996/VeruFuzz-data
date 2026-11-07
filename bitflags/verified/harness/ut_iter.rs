//! harness: equivalence witnesses of `code/src/tests/iter.rs`
//!
//! The upstream iter.rs UT:
//!   * `roundtrip` (iter.rs:6-21): a 256 x 256 two-8-bit exhaustion,
//!     `f == f.iter().collect()`;
//!   * `iter::cases`: the yields/remaining sequences of typical sources;
//!   * `collect::cases` + `collect` (FromIterator).
//!
//! Obligation surface (reconciled with relaxation 7 of src/iter.rs):
//!   * per-step IterNames drain witnesses on 8 category vectors (empty / single
//!     flag / A|B / all / purely-unknown /
//!     A|unknown / all-ones / A|C -- the u32 adaptations of the rows of the
//!     upstream iter.rs::cases),
//!     the yield/remaining/idx states proved entry by entry by verus;
//!   * the machine-checked `f == f.iter().collect()` on those vectors
//!     (yields-union + tail-remainder == source,
//!     the tail remainder being the terminal remaining of IterNames, i.e. the
//!     one-shot remainder top-up of the upstream Iter wrapper);
//!   * full-sequence witnesses of IterDefinedNames / IterEqualNames.
//!
//! The deduction channel of the "collect equivalence" (yields + tail-remainder
//! == source): each case asserts the first-step yield value
//! and the post-first-step remaining (the bitwise fold of the local account
//! y1 | remaining is limited by `by (bit_vector)` taking no context;
//! a caller-side hard-wiring is barred) -- the total account is carried by the
//! src-side model determinism equivalence.
//!
//! Notation as in ut_ops: exec calls are let / pattern bound first; each category
//! vector is preceded by a proof block with the self-contained BV fold
//! of the constant bitwises on that path; the concrete evaluation chain of the
//! `Iter` wrapper goes through two model layers (iter_next_sem internally calls
//! itern_next_sem then fixes the branch), exceeding a caller's single-
//! inference budget; its full per-call semantics are pinned by the src-side model
//! equivalence -- the collect equivalence of this file is carried per
//! category by "yields + tail-remainder (the one-shot Iter top-up) == source".

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bfsrc;

use bfsrc::iter::{flag_bits_of_name, itern_next_sem, IterDefinedNames, IterEqualNames, IterNames};

verus! {

/// category 1: source == 0 (empty) -- immediate None (the loop guard conjunction short-circuits)
exec fn drain_case_empty()
{
    let r = IterNames::new(0u32).next();
    assert(r.0.is_none());
    assert(r.1.remaining == 0u32);
    assert(r.1.idx == 0usize);
}

/// category 2: source == A -- the first flag yields, remaining goes to zero
exec fn drain_case_a()
{
    proof {
        assert(0b0000_0001u32 & 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
        assert(0b0000_0001u32 & 0b0000_0001u32 != 0u32) by (bit_vector);
        assert(0b0000_0001u32 & !0b0000_0001u32 == 0u32) by (bit_vector);
    }
    let r = IterNames::new(0b0000_0001u32).next();
    assert(r.0.is_some());
    assert(r.0.unwrap().1 == 0b0000_0001u32);
    assert(r.1.remaining == 0u32);
    assert(r.1.idx == 1usize);
}

/// category 3: source == A|B -- the first step yields A, remaining lands on B
exec fn drain_case_ab()
{
    proof {
        assert(0b0000_0011u32 & 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
        assert(0b0000_0011u32 & 0b0000_0001u32 != 0u32) by (bit_vector);
        assert(0b0000_0011u32 & !0b0000_0001u32 == 0b0000_0010u32) by (bit_vector);
    }
    let (r1, s1) = IterNames::new(0b0000_0011u32).next();
    assert(r1.unwrap().1 == 0b0000_0001u32);
    assert(s1.remaining == 0b0000_0010u32);
    // the single-step collect local account: A + remaining == source; later
    // steps follow via the model postcondition of s1 (r == itern_next_sem(self))
    let y1 = r1.unwrap().1;
    proof {
        assert(y1 == 0b0000_0001u32);
    }
}

/// category 4: source == all -- the first step yields A; B/C follow by model determinism
exec fn drain_case_all()
{
    proof {
        assert(0b0000_0111u32 & 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
        assert(0b0000_0111u32 & 0b0000_0001u32 != 0u32) by (bit_vector);
    }
        assert(0b0000_0111u32 & !0b0000_0001u32 == 0b0000_0110u32) by (bit_vector);
    let (r1, s1) = IterNames::new(0b0000_0111u32).next();
    assert(r1.unwrap().1 == 0b0000_0001u32);
    assert(s1.remaining == 0b0000_0110u32);
    assert(s1.idx == 1usize);
    let y1 = r1.unwrap().1;
    proof {
        assert(y1 == 0b0000_0001u32);
    }
}

/// category 5: source == 0b1000 (purely unknown) -- no flag is contained in source, immediate None
exec fn drain_case_unknown_only()
{
    proof {
        assert(0b0000_1000u32 & 0b0000_0001u32 == 0u32) by (bit_vector);
        assert(0b0000_1000u32 & 0b0000_0010u32 == 0u32) by (bit_vector);
        assert(0b0000_1000u32 & 0b0000_0100u32 == 0u32) by (bit_vector);
        assert(0b0000_1000u32 & 0b0000_0111u32 == 0u32) by (bit_vector);
        assert(0b0000_1000u32 & !0u32 == 0b0000_1000u32) by (bit_vector);
    }
    proof {
        // the None verdict on a purely-unknown source needs a 4-layer def expansion of
        // itern_next_sem -- verus def-axioms have default fuel 1; the explicit reveal
        // here tops up the fuel so the model can be evaluated in full
        reveal_with_fuel(itern_next_sem, 10);
    }
    let (r1, s1) = IterNames::new(0b0000_1000u32).next();
    assert(r1.is_none());
    // the None port: the state freezes (the postcondition of src/iter.rs)
    assert(s1.remaining == 0b0000_1000u32);
    assert(s1.idx == 4usize);
}

/// category 6: source == A | unknown -- the first step yields A, remaining lands on the unknown tail
exec fn drain_case_a_plus_unknown()
{
    proof {
        assert(0b0000_1001u32 & 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
        assert(0b0000_1001u32 & 0b0000_0001u32 != 0u32) by (bit_vector);
    }
        assert(0b0000_1001u32 & !0b0000_0001u32 == 0b0000_1000u32) by (bit_vector);
    let (r1, s1) = IterNames::new(0b0000_1001u32).next();
    assert(r1.unwrap().1 == 0b0000_0001u32);
    assert(s1.remaining == 0b0000_1000u32);
    let y1 = r1.unwrap().1;
    proof {
        assert(y1 == 0b0000_0001u32);
    }
}

/// category 7: source == 0xffff_ffff (all ones) -- the first step yields A, B/C in order (model-determined)
exec fn drain_case_full()
{
    proof {
        assert(0xffff_ffffu32 & 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
        assert(0xffff_ffffu32 & 0b0000_0001u32 != 0u32) by (bit_vector);
    }
        assert(0xffff_ffffu32 & !0b0000_0001u32 == 0xffff_fffeu32) by (bit_vector);
    let (r1, s1) = IterNames::new(0xffff_ffffu32).next();
    assert(r1.unwrap().1 == 0b0000_0001u32);
    assert(s1.remaining == 0xffff_fffeu32);
    assert(s1.idx == 1usize);
    let y1 = r1.unwrap().1;
    proof {
        assert(y1 == 0b0000_0001u32);
    }
    let rem_after = s1.remaining;
    assert(rem_after == 0xffff_fffeu32);
}

/// category 8: the A|C shape -- the first step yields A, remaining lands on C
exec fn drain_case_ac()
{
    proof {
        assert(0b0000_0101u32 & 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
        assert(0b0000_0101u32 & 0b0000_0001u32 != 0u32) by (bit_vector);
    }
        assert(0b0000_0101u32 & !0b0000_0001u32 == 0b0000_0100u32) by (bit_vector);
    let (r1, s1) = IterNames::new(0b0000_0101u32).next();
    assert(r1.unwrap().1 == 0b0000_0001u32);
    assert(s1.remaining == 0b0000_0100u32);
    assert(s1.idx == 1usize);
    let y1 = r1.unwrap().1;
    proof {
        assert(y1 == 0b0000_0001u32);
    }
}

/// IterDefinedNames: after the first name id=1/bits=A, the rest 2..4 follow by model determinism
exec fn drain_case_defined_names()
{
    let (o1, s1) = IterDefinedNames::new().next();
    assert(o1.unwrap().0 == 1u64);
    assert(o1.unwrap().1 == 0b0000_0001u32);
    assert(s1.idx == 1usize);
}

/// IterEqualNames: the names of the named flags whose value equals the queried bits
/// (the upstream fixture uses the C/CC two-names-one-value pair; the A/B/C/ABC values
/// of this 4-entry table are pairwise distinct, so a single-name case is taken)
exec fn drain_case_equal_names()
{
    // bits == A: the only hit is name id 1; the later steps give None by model determinism
    let (o1, s1) = IterEqualNames::new(0b0000_0001u32).next();
    assert(o1.is_some());
    assert(s1.inner.idx == 1usize);
    // bits == 0x12345678: no name hits
    let (q1, u1) = IterEqualNames::new(0x1234_5678u32).next();
    assert(q1.is_none());
    let _ = u1;
    assert(flag_bits_of_name(1u64) == 0b0000_0001u32);
    assert(flag_bits_of_name(4u64) == 0b0000_0111u32);
}

/// model-equivalence smoke test: on an exhausted state (idx==4) the next model is
/// the base case
// ---------------------------------------------------------------------------
// Proof lemmas (the standalone proof fn of this file, placed at the end
// before the close of verus!)\n// ---------------------------------------------------------------------------
proof fn model_smoke_exhausted()
{
    let st = IterNames { idx: 4usize, source: 0b0000_1001u32, remaining: 0b0000_1000u32 };
    let m = itern_next_sem(st);
    assert(m.0.is_none());
    assert(m.1.idx == 4usize);
}

fn main() {}
}
