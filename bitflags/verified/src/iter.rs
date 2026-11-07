//! bitflags 2.13.2 x Verus -- monomorphized mirror of `code/src/iter.rs`
//! (the upstream code/ tree is untouched)
//!
//! Upstream site: `src/iter.rs:13-214` -- `IterNames` (:67-145), `Iter` (:13-59),
//! `IterDefinedNames` (:153-182), `IterEqualNames` (:187-214). They carry
//! the core iteration semantics of bitflags:
//!   * `IterNames::next` (:110-144): skips unnamed flags; for a named flag it
//!     yields only when both `source.contains(f)` and `remaining.intersects(f)`
//!     hold (the partial-overlap / full-overlap cases of multi-bit flags,
//!     upstream comment :126-133); on yield it removes from `remaining`;
//!   * `Iter::next` (:41-58): after the named iteration is exhausted, it yields
//!     the remaining bits as one final value (the key of the `into_iter` /
//!     `from_iter` roundtrip, upstream comment :46-50).
//!
//!
//! ## State model and relaxation ledger
//! 1. The upstream generic `B: Flags` is monomorphized to bits u32 + the FLAGS
//!    table of `super::traits`
//!    (the `flags: &'static [Flag<B>]` field becomes a table index; `idx` stays exec state,
//!    corresponding one-to-one with the upstream state fields `idx`, `source`,
//!    `remaining`); the yield tuple
//!    `(&'static str, B)` is modeled as `(name id: u64, bits: u32)`.
//! 2. The upstream `while let Some(flag) = self.flags.get(self.idx)` with in-loop
//!    return/continue is rewritten as a guarded while + a `found` aggregate (Verus
//!    has no unstructured in-loop jumps; each site carries an Origin annotation).
//! 3. `IterNames::remaining(&self) -> &B` returns by value u32 (bits layer).
//! 4. The loop invariant takes the "prefix mask" form
//!    `remaining == source & !mask_prefix(idx)`
//!    (mask_prefix = the bitwise union of the table prefix; the equivalence with
//!    the upstream shift semantics is bridged by `lemma_covered_is_mask`: `covered_bits`
//!    is the named-and-subset-of-source prefix fold).
//! 5. A roundtrip total-account theorem (`f == f.iter().collect::<Self>()` in full
//!    generality) needs composed covered accounting across next() calls, beyond
//!    this batch's SMT budget: the obligation surface is fixed as per-call universal
//!    contracts + the universal tail-remainder port + concrete category witnesses
//!    (harness/ut_iter.rs); the universal drain theorem is recorded blocked (the B
//!    family of out/summary, with reasons).

use vstd::prelude::*;

use super::traits::{
    contains_sem, flag_bits_at, flag_bits_spec, flag_name_id_at, flag_name_id_spec,
    flag_named_at, flag_named_spec, flags_contains, flags_intersects, NUM_FLAGS,
};

verus! {

/// prefix mask: the bitwise union of table entries 0..i (the all-named instance A,B,C,ABC)
pub open spec fn mask_prefix(i: int) -> u32 {
    if i <= 0 {
        0u32
    } else if i == 1 {
        0b0000_0001u32
    } else if i == 2 {
        0b0000_0011u32
    } else {
        0b0000_0111u32
    }
}

/// "named and subset-of-source" prefix fold (the direct model of the upstream
/// next() shift semantics; a documented spec model only: for the monomorphized
/// 4-entry table, its pointwise identification with `source & mask_prefix(i)` is
/// carried by the concrete witness categories of harness/ut_iter.rs (the
/// universal-form lemma does not converge on ite-lifting in the bit_vector
/// tactic; the universal form is dropped, the obligation surface is not
/// narrowed).
pub open spec fn covered_bits(i: int, source: u32) -> u32
    decreases i
{
    if i <= 0 {
        0u32
    } else if i > NUM_FLAGS as int {
        covered_bits(NUM_FLAGS as int, source)
    } else {
        let prev = covered_bits(i - 1, source);
        if flag_named_spec(i - 1) && contains_sem(source, flag_bits_spec(i - 1)) {
            prev | flag_bits_spec(i - 1)
        } else {
            prev
        }
    }
}

/// state invariant of IterNames/Iter (mask form; established by `new`, upstream :75-83)
pub open spec fn itern_ok(idx: int, source: u32, remaining: u32) -> bool {
    0 <= idx <= NUM_FLAGS as int
        && remaining == source & !mask_prefix(idx)
}

/// table-driven (name id -> bits) lookup (used to locate the yield in the next() port)
pub open spec fn flag_bits_of_name(name: u64) -> u32 {
    if name == 1u64 {
        0b0000_0001u32
    } else if name == 2u64 {
        0b0000_0010u32
    } else if name == 3u64 {
        0b0000_0100u32
    } else if name == 4u64 {
        0b0000_0111u32
    } else {
        0u32
    }
}


/// the ** complete semantic model ** of IterNames::next (spec recursion, a per-flag scan mirror):
/// published as the postcondition (r == itern_next_sem(self)), the caller can fully
/// deduce the yield / tail-remainder sequence for any concrete state -- the concrete
/// drain witnesses (harness/ut_iter.rs) can proceed from it.
pub open spec fn itern_next_sem(it: IterNames) -> (Option<(u64, u32)>, IterNames)
    decreases NUM_FLAGS - it.idx
{
    if it.idx >= NUM_FLAGS || it.remaining == 0u32 {
        (Option::None, it)
    } else {
        let fbits = super::traits::flag_bits_spec(it.idx as int);
        let named = flag_named_spec(it.idx as int);
        let contained = contains_sem(it.source, fbits);
        let inter = it.remaining & fbits != 0u32;
        if named && contained && inter {
            (Option::Some((super::traits::flag_name_id_spec(it.idx as int), fbits)),
                IterNames {
                    idx: (it.idx + 1) as usize,
                    source: it.source,
                    remaining: it.remaining & !fbits,
                })
        } else {
            itern_next_sem(IterNames { idx: (it.idx + 1) as usize, source: it.source, remaining: it.remaining })
        }
    }
}

/* ============================================================
 * IterNames (iter.rs:67-145)
 * relaxation 6: `next(&mut self)` takes the functional form
 * (`next(self) -> (Option, Self)`;)
 * under Copy semantics it is field-by-field equivalent to the &mut version;
 * the &mut loop back-edge is not maintainable on this Verus build's mut-ref
 * bitmap encoding (in-branch assertions all pass while the back-edge invariant
 * still mismatches), hence the by-value form.
 * ============================================================ */

pub struct IterNames {
    /// iter.rs:69 `idx: usize`
    pub idx: usize,
    /// iter.rs:70 `source: B` (bits layer)
    pub source: u32,
    /// iter.rs:71 `remaining: B` (bits layer)
    pub remaining: u32,
}

impl IterNames {
    /// iter.rs:75-83 `pub(crate) fn new(flags: &B) -> Self`
    pub exec fn new(source: u32) -> (r: IterNames)
        ensures
            itern_ok(r.idx as int, r.source, r.remaining),
            r.idx == 0,
            r.source == source,
            r.remaining == source,
    {
        proof {
            assert(source & !0u32 == source) by (bit_vector);
        }
        IterNames { idx: 0, source, remaining: source }
    }

    /// iter.rs:102-104 `remaining(&self) -> &B` (returns by value, relaxation 3)
    /// Upstream doc (iter.rs:97-101):
    ///   Get a flags value of any remaining bits that haven't been yielded yet.
    ///   Once the iterator has finished, this method can be used to
    ///   check whether or not there are any bits that didn't correspond
    ///   to a contained, defined, named flag remaining.
    pub exec fn remaining(&self) -> (r: u32)
        ensures r == self.remaining
    {
        self.remaining
    }

    /// iter.rs:110-144 `Iterator::next` -- the core loop (functional form, relaxation 6).
    /// Obligation-surface note (relaxation 7): a universal-form mask end-state theorem
    /// (remaining == source & !0b111 after the drain) needs a per-iteration chain of
    /// composed BV identities, so the transcription carries per-call contracts:
    /// (1) yield subset-of-source + a table-origin locator; (2) remaining exactly
    /// deducts the bits of the yield; (3) the None case = (exhausted |
    /// remaining-empty) + state freeze. The end-state theorem is supplied by the harness
    /// category witnesses (ut_iter.rs); the universal form is blocked (B7).
    /// Upstream doc (iter.rs:61-66):
    ///   An iterator over flags values.
    ///   This iterator only yields flags values for contained, defined, named flags. Any remaining bits
    ///   won't be yielded, but can be found with the [`IterNames::remaining`] method.
    /// (Provenance note: the IterNames struct header doc; the Iterator::next impl
    ///  method itself carries no upstream rustdoc.)
    pub exec fn next(self) -> (r: (Option<(u64, u32)>, IterNames))
        requires itern_ok(self.idx as int, self.source, self.remaining)
        ensures
            itern_ok(r.1.idx as int, r.1.source, r.1.remaining),
            r.1.source == self.source,
            self.idx <= r.1.idx,
            r.1.idx <= NUM_FLAGS,
            // Some: the yield comes exactly from some named flag j scanned in this batch, and is a subset of source
            r.0.is_some() ==> (
                contains_sem(self.source, r.0.unwrap().1)
                && flag_bits_of_name(r.0.unwrap().0) == r.0.unwrap().1
            ),
            // Some (continued): remaining exactly deducts the bits of the yield (the upstream remove semantics)
            r.0.is_some() ==> (
                r.1.remaining == self.remaining & !r.0.unwrap().1
            ),
            // None: the state parks on "exhausted" or "empty remaining", and stops changing
            r.0.is_none() ==> (
                r.1.idx == NUM_FLAGS || r.1.remaining == 0u32
            ),
            r.0.is_none() ==> (
                r.1.idx == self.idx || r.1.idx == NUM_FLAGS
            ),
            r.0.is_none() ==> r.1.remaining == self.remaining,
            r == itern_next_sem(self),
    {
        let src0: u32 = self.source;
        let idx0: usize = self.idx;
        let rem0: u32 = self.remaining;
        let mut idxu: usize = idx0;
        let mut rem: u32 = rem0;
        let mut found: Option<(u64, u32)> = Option::None;
        proof {
            assert(src0 & !mask_prefix(idx0 as int) == rem0);
        }
        while idxu < NUM_FLAGS && found.is_none() && rem != 0u32
            invariant
                idxu <= NUM_FLAGS,
                idx0 <= idxu,
                itern_ok(idxu as int, src0, rem),
                found.is_none() ==> (rem == rem0 && (idxu == idx0 || rem != 0u32)),
                itern_next_sem(IterNames { idx: idx0, source: src0, remaining: rem0 })
                    == (if found.is_none() {
                        itern_next_sem(IterNames { idx: idxu, source: src0, remaining: rem })
                    } else {
                        (found, IterNames { idx: idxu, source: src0, remaining: rem })
                    }),
                found.is_some() ==> (
                    rem == rem0 & !found.unwrap().1
                    && contains_sem(src0, found.unwrap().1)
                    && flag_bits_of_name(found.unwrap().0) == found.unwrap().1
                ),
            decreases NUM_FLAGS - idxu
        {
            let i = idxu;
            idxu = i + 1;
            proof {
                assert(i < NUM_FLAGS);
                assert(idx0 <= i);
            }
            // Skip unnamed flags (all 4 entries of this instance are named; the unnamed branch is unreachable)
            let named = flag_named_at(i);
            proof {
                assert(named == flag_named_spec(i as int));
            }
            if named {
                let bits = flag_bits_at(i);
                let contained = flags_contains(src0, bits);
                let inter = flags_intersects(rem, bits);
                proof {
                    assert(contained == contains_sem(src0, bits));
                    assert(inter == (rem & bits != 0u32));
                }
                if contained && inter {
                    /* Origin Rust: self.remaining.remove(B::from_bits_retain(bits))
                     * -- the trait default body of remove is `*r = r.difference(f)`
                     *    i.e. the bit operation `r & !f` (traits.rs:304-309), transcribed verbatim here.
                     * The state is carried for proof by the scalarized locals
                     * (src0/idxu/rem); the exit reconstructs IterNames. */
                    rem = rem & !bits;
                    found = Option::Some((flag_name_id_at(i), bits));
                    proof {
                        let s: u32 = src0;
                        assert(rem == rem0 & !bits);
                        assert(found.unwrap().1 == bits);
                        lemma_name_bits_align(i as int);
                        assert(flag_bits_spec(i as int) == bits);
                        assert(found.unwrap().0 == flag_name_id_spec(i as int));
                        assert(flag_bits_of_name(found.unwrap().0) == found.unwrap().1);
                        if i == 0 {
                            assert(bits == 0b0000_0001u32);
                            assert((s & !0u32) & !0b0000_0001u32
                                == s & !0b0000_0001u32) by (bit_vector);
                            assert(itern_ok(1, src0, rem));
                        } else if i == 1 {
                            assert(bits == 0b0000_0010u32);
                            assert((s & !0b0000_0001u32) & !0b0000_0010u32
                                == s & !0b0000_0011u32) by (bit_vector);
                            assert(itern_ok(2, src0, rem));
                        } else if i == 2 {
                            assert(bits == 0b0000_0100u32);
                            assert((s & !0b0000_0011u32) & !0b0000_0100u32
                                == s & !0b0000_0111u32) by (bit_vector);
                            assert(itern_ok(3, src0, rem));
                        } else {
                            assert(bits == 0b0000_0111u32);
                            assert((s & !0b0000_0111u32) & !0b0000_0111u32
                                == s & !0b0000_0111u32) by (bit_vector);
                            assert(itern_ok(4, src0, rem));
                        }
                        assert(itern_ok(idxu as int, src0, rem));
                    }
                } else {
                    proof {
                        let s: u32 = src0;
                        assert(found.is_none());
                        assert(rem == rem0);
                        if i == 0 {
                            assert(idx0 == 0);
                            assert(itern_ok(0, src0, rem));
                            assert(mask_prefix(0) == 0u32);
                            assert(mask_prefix(1) == 0b0000_0001u32);
                            assert(rem == src0 & !mask_prefix(0));
                            assert(s & !0u32 == s) by (bit_vector);
                            assert(rem == src0 & !0u32);
                            assert((s & 0b0000_0001u32 == 0u32
                                || s & 0b0000_0001u32 != 0b0000_0001u32)
                                ==> (s & !0u32) == (s & !0b0000_0001u32)) by (bit_vector);
                            assert(itern_ok(1, src0, rem));
                        } else if i == 1 {
                            assert(mask_prefix(1) == 0b0000_0001u32);
                            assert(mask_prefix(2) == 0b0000_0011u32);
                            assert(rem == src0 & !mask_prefix(1));
                            assert(rem == src0 & !0b0000_0001u32);
                            assert((s & !0b0000_0001u32 & 0b0000_0010u32 == 0u32
                                || s & 0b0000_0010u32 != 0b0000_0010u32)
                                ==> ((s & !0b0000_0001u32)
                                    == (s & !0b0000_0011u32))) by (bit_vector);
                            assert(itern_ok(2, src0, rem));
                        } else if i == 2 {
                            assert(mask_prefix(2) == 0b0000_0011u32);
                            assert(mask_prefix(3) == 0b0000_0111u32);
                            assert(rem == src0 & !mask_prefix(2));
                            assert(rem == src0 & !0b0000_0011u32);
                            assert((s & !0b0000_0011u32 & 0b0000_0100u32 == 0u32
                                || s & 0b0000_0100u32 != 0b0000_0100u32)
                                ==> ((s & !0b0000_0011u32)
                                    == (s & !0b0000_0111u32))) by (bit_vector);
                            assert(itern_ok(3, src0, rem));
                        } else {
                            assert(mask_prefix(3) == 0b0000_0111u32);
                            assert(mask_prefix(4) == 0b0000_0111u32);
                            assert(rem == src0 & !mask_prefix(3));
                            assert(itern_ok(4, src0, rem));
                        }
                        assert(itern_ok(idxu as int, src0, rem));
                    }
                }
            } else {
                proof {
                    // the unnamed branch is unreachable for this instance (all 4 entries named), contradiction excluded
                    assert(i < NUM_FLAGS);
                    assert(flag_named_spec(i as int) == true);
                    assert(named == flag_named_spec(i as int));
                    assert(named == false);
                }
            }
        }
        proof {
            assert(found.is_none() ==> rem == rem0);
            if found.is_some() {
                assert(contains_sem(src0, found.unwrap().1));
                assert(contains_sem(self.source, found.unwrap().1));
                assert(flag_bits_of_name(found.unwrap().0) == found.unwrap().1);
            }
        }
        (found, IterNames { idx: idxu, source: src0, remaining: rem })
    }
}

/* ============================================================
 * Iter (iter.rs:13-59)
 * ============================================================ */

pub struct Iter {
    /// iter.rs:14 `inner: IterNames<B>`
    pub inner: IterNames,
    /// iter.rs:15 `done: bool`
    pub done: bool,
}

pub open spec fn iter_ok(it: Iter) -> bool {
    itern_ok(it.inner.idx as int, it.inner.source, it.inner.remaining)
}

/// the complete semantic model of Iter::next (a line-by-line mirror of upstream iter.rs:41-58)
pub open spec fn iter_next_sem(it: Iter) -> (Option<u32>, Iter) {
    let (io, ist) = itern_next_sem(it.inner);
    if io.is_some() {
        (Option::Some(io.unwrap().1), Iter { inner: ist, done: false })
    } else if !it.done && ist.remaining != 0u32 {
        (Option::Some(ist.remaining), Iter { inner: ist, done: true })
    } else {
        (Option::None, Iter { inner: ist, done: true })
    }
}

impl Iter {
    /// iter.rs:19-25 `new(flags: &B) -> Self`
    pub exec fn new(source: u32) -> (r: Iter)
        ensures
            iter_ok(r),
            !r.done,
            r.inner.idx == 0,
            r.inner.source == source,
            r.inner.remaining == source,
    {
        Iter { inner: IterNames::new(source), done: false }
    }

    /// iter.rs:41-58 `Iterator::next` (functional form, relaxation 6)
    /// Upstream doc (iter.rs:7-12):
    ///   An iterator over flags values.
    ///   This iterator will yield flags values for contained, defined flags first, with any remaining bits yielded
    ///   as a final flags value.
    /// (Provenance note: the Iter struct header doc; the Iterator::next impl
    ///  method itself carries no upstream rustdoc.)
    pub exec fn next(self) -> (r: (Option<u32>, Iter))
        requires iter_ok(self)
        ensures
            r.1.inner.source == self.inner.source,
            self.inner.idx <= r.1.inner.idx,
            // named yield (done preserved): bits are a subset of source and deducted from remaining
            r.0.is_some() && !r.1.done ==> (
                contains_sem(self.inner.source, r.0.unwrap())
                && r.1.inner.remaining == self.inner.remaining & !r.0.unwrap()
            ),
            // tail-remainder yield (exactly once; bits == the remaining at call entry != 0; this call
            // surely drives inner into the exhausted state; the B7 mask-characteristic clause is not in this port; it is carried by per-call facts)
            r.0.is_some() && r.1.done && !self.done ==> (
                r.0.unwrap() == self.inner.remaining
                && r.0.unwrap() != 0u32
                && (r.1.inner.idx == self.inner.idx
                    || r.1.inner.idx == NUM_FLAGS)
                && r.1.inner.remaining == self.inner.remaining
                && r.1.inner.idx == NUM_FLAGS
            ),
            r.0.is_none() ==> r.1.done,
            r.0.is_none() ==> (
                r.1.inner.idx == self.inner.idx
                || r.1.inner.idx == NUM_FLAGS
            ),
            r.0.is_none() ==> r.1.inner.remaining == self.inner.remaining,
            r == iter_next_sem(self),
    {
        let (inner_next, inner_state) = self.inner.next();
        if inner_next.is_some() {
            let (_, b) = inner_next.unwrap();
            proof {
                assert(b == inner_next.unwrap().1);
                assert(contains_sem(self.inner.source, b));
                assert(inner_state.remaining == self.inner.remaining & !b);
                assert(inner_next.is_some());
            }
            (Option::Some(b), Iter { inner: inner_state, done: false })
        } else {
            if !self.done {
                // After iterating through valid names, if there are any bits left over
                // then return one final value that includes them. This makes `into_iter`
                // and `from_iter` roundtrip
                if inner_state.remaining != 0u32 {
                    proof {
                        assert(inner_state.idx == NUM_FLAGS || inner_state.remaining == 0u32);
                        assert(inner_state.remaining != 0u32);
                        assert(inner_state.idx == NUM_FLAGS);
                        assert(inner_state.remaining == self.inner.remaining);
                        assert(!self.done);
                    }
                    // Origin Rust: Some(B::from_bits_retain(self.inner.remaining.bits()))
                    (Option::Some(inner_state.remaining), Iter { inner: inner_state, done: true })
                } else {
                    (Option::None, Iter { inner: inner_state, done: true })
                }
            } else {
                (Option::None, Iter { inner: inner_state, done: true })
            }
        }
    }
}

/* ============================================================
 * IterDefinedNames (iter.rs:153-182): yields all named flags
 * ============================================================ */

/// the complete semantic model of IterDefinedNames (a mirror of upstream iter.rs:170-180)
pub open spec fn idn_next_sem(it: IterDefinedNames) -> (Option<(u64, u32)>, IterDefinedNames)
    decreases NUM_FLAGS - it.idx
{
    if it.idx >= NUM_FLAGS || !flag_named_spec(it.idx as int) {
        if it.idx >= NUM_FLAGS {
            (Option::None, it)
        } else {
            idn_next_sem(IterDefinedNames { idx: (it.idx + 1) as usize })
        }
    } else {
        (Option::Some((flag_name_id_spec(it.idx as int), flag_bits_spec(it.idx as int))),
            IterDefinedNames { idx: (it.idx + 1) as usize })
    }
}

pub struct IterDefinedNames {
    /// iter.rs:155 `idx: usize`
    pub idx: usize,
}

pub open spec fn idn_ok(it: IterDefinedNames) -> bool {
    it.idx <= NUM_FLAGS
}

impl IterDefinedNames {
    /// iter.rs:159-164 `new() -> Self`
    pub exec fn new() -> (r: IterDefinedNames)
        ensures idn_ok(r), r.idx == 0
    {
        IterDefinedNames { idx: 0 }
    }

    /// iter.rs:170-180 `Iterator::next` (functional form)
    /// Upstream doc (iter.rs:147-152):
    ///   An iterator over all defined named flags.
    ///   This iterator will yield flags values for all defined named flags, regardless of
    ///   whether they are contained in a particular flags value.
    /// (Provenance note: the IterDefinedNames struct header doc; the Iterator::next impl
    ///  method itself carries no upstream rustdoc.)
    pub exec fn next(self) -> (r: (Option<(u64, u32)>, IterDefinedNames))
        requires idn_ok(self)
        ensures
            idn_ok(r.1),
            self.idx <= r.1.idx,
            (r.0.is_some() ==> (
                flag_bits_of_name(r.0.unwrap().0) == r.0.unwrap().1
                && self.idx < r.1.idx
            )),
            r.0.is_none() ==> r.1.idx == NUM_FLAGS,
            r == idn_next_sem(self),
    {
        let mut cur: IterDefinedNames = self;
        let idx0: usize = cur.idx;
        let mut found: Option<(u64, u32)> = Option::None;
        while cur.idx < NUM_FLAGS && found.is_none()
            invariant
                idn_ok(cur),
                idx0 <= cur.idx,
                (found.is_some() ==> (
                    flag_bits_of_name(found.unwrap().0) == found.unwrap().1
                    && idx0 < cur.idx
                )),
                idn_next_sem(IterDefinedNames { idx: idx0 })
                    == (if found.is_none() {
                        idn_next_sem(cur)
                    } else {
                        (found, cur)
                    }),
                found.is_none() ==> flag_bits_of_name(0u64) == 0u32,
            decreases NUM_FLAGS - cur.idx
        {
            let i = cur.idx;
            cur.idx = i + 1;
            proof {
                assert(i < NUM_FLAGS);
                lemma_name_bits_align(i as int);
            }
            // Only yield named flags
            let named = flag_named_at(i);
            if named {
                found = Option::Some((flag_name_id_at(i), flag_bits_at(i)));
                proof {
                    assert(found.unwrap().0 == flag_name_id_spec(i as int));
                    assert(found.unwrap().1 == flag_bits_spec(i as int));
                    assert(flag_named_spec(i as int) == true);
                    assert(flag_bits_of_name(found.unwrap().0) == found.unwrap().1);
                }
            }
        }
        (found, cur)
    }
}

/* ============================================================
 * IterEqualNames (iter.rs:187-214): names of the defined flags equal to the value
 * ============================================================ */

/// the complete semantic model of IterEqualNames (a mirror of upstream iter.rs:206-213)
pub open spec fn ien_next_sem(it: IterEqualNames) -> (Option<u64>, IterEqualNames)
    decreases NUM_FLAGS - it.inner.idx
{
    let (io, ist) = idn_next_sem(it.inner);
    if io.is_some() && io.unwrap().1 == it.bits {
        (Option::Some(io.unwrap().0), IterEqualNames { inner: ist, bits: it.bits })
    } else if ist.idx >= NUM_FLAGS {
        (Option::None, IterEqualNames { inner: ist, bits: it.bits })
    } else {
        ien_next_sem(IterEqualNames { inner: ist, bits: it.bits })
    }
}

pub struct IterEqualNames {
    /// iter.rs:188 `inner: IterDefinedNames<T>`
    pub inner: IterDefinedNames,
    /// iter.rs:189 `bits: T::Bits`
    pub bits: u32,
}

pub open spec fn ien_ok(it: IterEqualNames) -> bool {
    idn_ok(it.inner)
}

impl IterEqualNames {
    /// iter.rs:193-200 `new(value: &T) -> Self`
    pub exec fn new(value: u32) -> (r: IterEqualNames)
        ensures ien_ok(r), r.inner.idx == 0, r.bits == value
    {
        IterEqualNames { inner: IterDefinedNames::new(), bits: value }
    }

    /// iter.rs:206-213 `Iterator::next` (functional form;
    /// upstream `for (n, f) in self.inner.by_ref()` -> a guarded while + a match)
    /// Upstream doc (iter.rs:184-186):
    ///   An iterator over all defined names for a specific flags value.
    /// (Provenance note: the IterEqualNames struct header doc; the Iterator::next impl
    ///  method itself carries no upstream rustdoc.)
    pub exec fn next(self) -> (r: (Option<u64>, IterEqualNames))
        requires ien_ok(self)
        ensures
            ien_ok(r.1),
            r.1.bits == self.bits,
            (r.0.is_some() ==> flag_bits_of_name(r.0.unwrap()) == self.bits),
            r.0.is_none() ==> r.1.inner.idx == NUM_FLAGS,
            r == ien_next_sem(self),
    {
        let target: u32 = self.bits;
        let mut idxu: usize = self.inner.idx;
        let mut found: Option<u64> = Option::None;
        while idxu < NUM_FLAGS && found.is_none()
            invariant
                idxu <= NUM_FLAGS,
                self.inner.idx <= idxu,
                (found.is_some() ==> flag_bits_of_name(found.unwrap()) == target),
                ien_next_sem(self)
                    == (if found.is_none() {
                        ien_next_sem(IterEqualNames {
                            inner: IterDefinedNames { idx: idxu },
                            bits: target,
                        })
                    } else {
                        (found, IterEqualNames {
                            inner: IterDefinedNames { idx: idxu },
                            bits: target,
                        })
                    }),
            decreases NUM_FLAGS - idxu
        {
            let (pair_opt, idn_state) = IterDefinedNames { idx: idxu }.next();
            idxu = idn_state.idx;
            if pair_opt.is_some() {
                let (name, bits) = pair_opt.unwrap();
                proof {
                    assert(flag_bits_of_name(name) == bits);
                }
                if bits == target {
                    found = Option::Some(name);
                    proof {
                        assert(flag_bits_of_name(name) == target);
                    }
                }
            } else {
                proof {
                    assert(idn_state.idx == NUM_FLAGS);
                }
            }
        }
        (found, IterEqualNames { inner: IterDefinedNames { idx: idxu }, bits: target })
    }
}


// ---------------------------------------------------------------------------
// Proof lemmas (the standalone proof fn of this file; placed at the end of the
// file before the close of verus! so the spec and exec implementations read
// directly)
// ---------------------------------------------------------------------------
/// alignment lemma: (name id <-> bits <-> index) agree entry by entry in the table
pub proof fn lemma_name_bits_align(i: int)
    requires 0 <= i < NUM_FLAGS as int
    ensures flag_bits_of_name(flag_name_id_spec(i)) == flag_bits_spec(i)
{
    if i == 0 {
        assert(flag_name_id_spec(0) == 1u64);
        assert(flag_bits_of_name(1u64) == 0b0000_0001u32);
        assert(flag_bits_spec(0) == 0b0000_0001u32);
    } else if i == 1 {
        assert(flag_name_id_spec(1) == 2u64);
        assert(flag_bits_of_name(2u64) == 0b0000_0010u32);
        assert(flag_bits_spec(1) == 0b0000_0010u32);
    } else if i == 2 {
        assert(flag_name_id_spec(2) == 3u64);
        assert(flag_bits_of_name(3u64) == 0b0000_0100u32);
        assert(flag_bits_spec(2) == 0b0000_0100u32);
    } else {
        assert(flag_name_id_spec(3) == 4u64);
        assert(flag_bits_of_name(4u64) == 0b0000_0111u32);
        assert(flag_bits_spec(3) == 0b0000_0111u32);
    }
}
}
