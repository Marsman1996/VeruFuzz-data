//! globset 0.4.21 (upstream ripgrep monorepo, crates/globset/src/lib.rs)
//! -- Verus transcription tree, crate root.
//!
//! Upstream pin: github.com/BurntSushi/ripgrep @
//! 178cc027e283fd965cb72d0a7395b219eada170c (fetch.conf); the code/ tree
//! is read-only. This root currently carries the leaf-utilities batch
//! GL1 only: the `escape` twin below plus the mounted pathutil/fnv
//! modules. The parser (glob.rs), candidate prep and the strategy/set
//! tiers mount in later batches per out/harness-inventory.md section 6.
//!
//! # Base-transcription notes (the standin ledger)
//!
//! | Upstream structure | Verification-tree base | Rationale |
//! | --- | --- | --- |
//! | `std::borrow::Cow<'a, [u8]>` | `CowBytes<'a>` twin enum below (Borrowed keeps a borrowed slice, Owned keeps a Vec) | std Cow has no verus spec; the twin carries the same two ownership modes with a Seq view + mode predicates, so the study discipline "Borrowed stays borrowed" is stated and proved per site |
//! | `&str::chars()` / `String` (escape) | `&[char]` / `Vec<char>` (the strsim base: chars() is per-character iteration, the slice base turns that contract into a type fact) | the wrapper forms converge onto the same parameter shape in later batches |
//! | `b'/'` b'.' etc in specs | `0x2F` / `0x2E` (same ASCII bytes) | byte-char literals are respelled as hex u8 to keep spec terms literal |
//!
//! No `# Panics` doc section exists on this batch's surface.

use pathutil::{
    file_name,
    file_name_ext,
    normalize_path,
    rfind_pref,
    spec_dotdot,
    spec_final_component,
    spec_final_ext,
};
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;
use vstd::seq::Seq;

pub mod fnv;
pub mod glob;
pub mod pathutil;

verus! {

// ===========================================================================
// The Cow twin (std::borrow::Cow over [u8]).
// Origin Rust (std): `enum Cow<'a, B> { Borrowed(Borrowed<'a, B>),
// Owned(<B as ToOwned>::Owned>) }` instantiated at B = [u8] by every
// globset consumer (Candidate::path, the pathutil trio). The twin keeps
// exactly the two modes with their two carriers.
// ===========================================================================

pub enum CowBytes<'a> {
    Borrowed(&'a [u8]),
    Owned(Vec<u8>),
}

impl<'a> CowBytes<'a> {
    /// Seq view: the byte sequence either mode carries.
    pub open spec fn view(&self) -> Seq<u8> {
        match self {
            CowBytes::Borrowed(b) => b@,
            CowBytes::Owned(v) => v@,
        }
    }

    /// Mode predicate (the Borrowed arm).
    pub open spec fn is_borrowed_mode(&self) -> bool {
        match self {
            CowBytes::Borrowed(_) => true,
            CowBytes::Owned(_) => false,
        }
    }

    /// Mode predicate (the Owned arm).
    pub open spec fn is_owned_mode(&self) -> bool {
        !self.is_borrowed_mode()
    }

    /// exec view of the byte data (read-only; both arms slice out).
    pub fn as_slice(&self) -> (s: &[u8])
        ensures
            s@ == self.view(),
    {
        match self {
            CowBytes::Borrowed(b) => b,
            CowBytes::Owned(v) => v.as_slice(),
        }
    }
}

// ===========================================================================
// escape (upstream lib.rs:1133-1150; the pub API of this batch).
//
// Upstream doc (lib.rs:1116-1131, quoted; the # Example section's
// assertions are pinned in harness/ut_escape.rs per the KAT plan):
//   Escape meta-characters within the given glob pattern.
//   The escaping works by surrounding meta-characters with brackets. For
//   example, `*` becomes `[*]`.
// ===========================================================================

/// The upstream metacharacter set (`'?' | '*' | '[' | ']' | '{' | '}'`,
/// the escape match arms at lib.rs:1139).
pub open spec fn is_escape_meta(c: char) -> bool {
    c == '?' || c == '*' || c == '[' || c == ']' || c == '{' || c == '}'
}

pub fn is_escape_meta_exec(c: char) -> (b: bool)
    ensures
        b == is_escape_meta(c),
{
    c == '?' || c == '*' || c == '[' || c == ']' || c == '{' || c == '}'
}

/// Value model of escape: the first `i` chars, each metachar wrapped in
/// brackets (`[*]` shape), processed in order.
pub open spec fn spec_escape_upto(s: Seq<char>, i: int) -> Seq<char>
    decreases i,
{
    if i <= 0 {
        Seq::empty()
    } else {
        let c = s.index(i - 1);
        let prev = spec_escape_upto(s, i - 1);
        if is_escape_meta(c) {
            prev.push('[').push(c).push(']')
        } else {
            prev.push(c)
        }
    }
}

/// Doc-face spec: "surrounding meta-characters with brackets" over the
/// whole pattern.
pub open spec fn spec_escape(s: Seq<char>) -> Seq<char> {
    spec_escape_upto(s, s.len() as int)
}

/// Escape meta-characters within the given glob pattern.
///
/// The escaping works by surrounding meta-characters with brackets. For
/// example, `*` becomes `[*]`.
///
/// (Upstream signature `escape(s: &str) -> String` rides the chars base
/// mapping: s.chars() == the &[char] parameter, String == Vec<char>.)
pub fn escape(s: &[char]) -> (r: Vec<char>)
    ensures
        r@ == spec_escape(s@),
{
    // Origin Rust (lib.rs:1134-1148):
    //     let mut escaped = String::with_capacity(s.len());
    //     for c in s.chars() {
    //         match c {
    //             // note that ! does not need escaping because it is only
    //             // special inside brackets
    //             '?' | '*' | '[' | ']' | '{' | '}' => {
    //                 escaped.push('['); escaped.push(c); escaped.push(']');
    //             }
    //             c => { escaped.push(c); }
    //         }
    //     }
    //     escaped
    // (capacity is not observable; the push order and the unchanged
    // non-metachar pass-through are carried verbatim)
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == spec_escape_upto(s@, i as int),
        decreases s.len() - i,
    {
        let c = s[i];
        if is_escape_meta_exec(c) {
            out.push('[');
            proof {
                escape_upto_step_meta(s@, i as int);
            }
            out.push(c);
            out.push(']');
        } else {
            out.push(c);
            proof {
                escape_upto_step_plain(s@, i as int);
            }
        }
        i += 1;
    }
    out
}

// ===========================================================================
// spec-step lemmas for the escape loop (loop-start invariant == the
// recursive model applied to the processed prefix).
// ===========================================================================

proof fn escape_upto_step_meta(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        is_escape_meta(s.index(i as int)),
    ensures
        spec_escape_upto(s, i + 1)
            == spec_escape_upto(s, i).push('[')
                .push(s.index(i as int))
                .push(']'),
{
}

proof fn escape_upto_step_plain(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        !is_escape_meta(s.index(i as int)),
    ensures
        spec_escape_upto(s, i + 1) == spec_escape_upto(s, i).push(s.index(i as int)),
{
}

// ===========================================================================
// GL6 -- Candidate preparation, the mod-64 length bitmask, and the fnv
// container face (upstream lib.rs:603-672 Candidate, 742-784
// LiteralStrategy, 786-822 ExtensionStrategy; the container face is
// the fnv::HashMap alias GL1 deferred to this batch, its first
// consumer per the inventory's section-5 container ruling).
//
// Container ruling (D6 carried): "the fireable behavior never depends
// on digest values, only on byte equality of the hashed keys." The
// twin below carries that membership semantics as a fully verified
// flat store, so the trusted-container face planned in the inventory
// never materializes as trust -- it downgrades to a verified semantic
// twin; GL1's digest pins remain the constant-transcription record
// for the hasher behind std's BuildHasherDefault.
// ===========================================================================

// ---------------------------------------------------------------------------
// Byte-equality helper (the map's only comparison face; std's HashMap
// routes by digest then re-checks by ==, so byte equality is the whole
// observable membership contract).
// ---------------------------------------------------------------------------

/// Scan two byte slices for view equality, keeping a concrete first-
/// mismatch index on the negative arm (no existential).
pub fn bytes_slice_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    proof {
        assert(a@.len() == a.len());
        assert(b@.len() == b.len());
    }
    if a.len() != b.len() {
        proof {
            assert(a@.len() != b@.len());
            assert(a@ != b@);
        }
        return false;
    }
    let mut i: usize = 0;
    let mut eq: bool = true;
    let mut mism: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a@.len() == a.len(),
            b@.len() == b.len(),
            a@.len() == b@.len(),
            eq ==> forall|k: int| 0 <= k < i ==> a@.index(k) == b@.index(k),
            !eq ==> (mism < i && a@.index(mism as int) != b@.index(mism as int)),
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            proof {
                assert(a@.index(i as int) != b@.index(i as int));
            }
            eq = false;
            mism = i;
        } else {
            proof {
                assert(a@.index(i as int) == b@.index(i as int));
            }
        }
        i += 1;
    }
    if eq {
        proof {
            assert(i == a.len());
            assert forall|k: int| 0 <= k < a@.len() implies
                a@.index(k) == b@.index(k) by {
            }
            ext_equal(a@, b@);
            assert(a@ == b@);
        }
        true
    } else {
        proof {
            assert(a@.len() == b@.len());
            assert(a@.index(mism as int) != b@.index(mism as int));
            assert(a@ != b@);
        }
        false
    }
}

/// View equality between a stored Vec key and a query slice (the
/// map's per-element comparison face; Vec fields index directly so the
/// element specs stay in the vec/axiom lane).
pub fn bytes_vec_slice_eq(a: &Vec<u8>, b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    proof {
        assert(a@.len() == a.len());
        assert(b@.len() == b.len());
    }
    if a.len() != b.len() {
        proof {
            assert(a@.len() != b@.len());
            assert(a@ != b@);
        }
        return false;
    }
    let mut i: usize = 0;
    let mut eq: bool = true;
    let mut mism: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a@.len() == a.len(),
            b@.len() == b.len(),
            a@.len() == b@.len(),
            eq ==> forall|k: int| 0 <= k < i ==> a@.index(k) == b@.index(k),
            !eq ==> (mism < i && a@.index(mism as int) != b@.index(mism as int)),
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            proof {
                assert(a@.index(i as int) != b@.index(i as int));
            }
            eq = false;
            mism = i;
        } else {
            proof {
                assert(a@.index(i as int) == b@.index(i as int));
            }
        }
        i += 1;
    }
    if eq {
        proof {
            assert(i == a.len());
            assert forall|k: int| 0 <= k < a@.len() implies
                a@.index(k) == b@.index(k) by {
            }
            ext_equal(a@, b@);
            assert(a@ == b@);
        }
        true
    } else {
        proof {
            assert(a@.len() == b@.len());
            assert(a@.index(mism as int) != b@.index(mism as int));
            assert(a@ != b@);
        }
        false
    }
}

// ---------------------------------------------------------------------------
// FnvByteMap -- upstream field type `fnv::HashMap<Vec<u8>, Vec<usize>>`
// (the alias GL1 recorded; consumer sites lib.rs:744, 787).
//
// Deviation from the std hash table, recorded (semantic twin per the
// D6 ruling): the store is a flat (distinct-key column, ordered event
// log) pair --
//   keys:   every distinct key that was added, first-insertion order;
//   events: every add, in push order, as (key column position, glob
//           index);
// a key's value list is its filtered event log. All fireable queries
// (contains_key / get / len / keyed extend) observe exactly byte
// equality of keys and push order of indexes -- the std table's
// behavior for every one of those queries -- while the extra freedom
// std has (iteration order over different keys) stays unobservable in
// this crate: every consumer queries one key at a time. Both columns
// take only top-level pushes, which vstd specifies directly.
//
// Origin Rust (fnv.rs:20-31, the alias, and the two add sites):
//   pub type HashMap<K, V> =
//       std::collections::HashMap<K, V, BuildHasherDefault<Hasher>>;
//   (lib.rs:756-759)  self.literals.entry(lit.into_bytes())
//                        .or_insert(vec![]).push(global_index);
//   (lib.rs:794-795)  self.0.entry(ext.into_bytes())
//                        .or_insert(vec![]).push(global_index);
// ---------------------------------------------------------------------------

/// The byte view of column position `q` (the canonical key term; every
/// quantifier over map columns triggers on its application).
pub open spec fn spec_key_view(keys: Seq<Vec<u8>>, q: int) -> Seq<u8> {
    keys.index(q)@
}

pub struct FnvByteMap {
    pub keys: Vec<Vec<u8>>,
    pub events: Vec<(usize, usize)>,
}

/// The last `keys`-column position whose key is byte-equal to `k`
/// among the first `n` keys (the rfind discipline).
pub open spec fn spec_map_find_key_upto(keys: Seq<Vec<u8>>, k: Seq<u8>, n: nat) -> Option<int>
    decreases n
{
    if n == 0 {
        None
    } else {
        let kv = keys.index((n - 1) as int);
        if kv@ == k {
            Some((n - 1) as int)
        } else {
            spec_map_find_key_upto(keys, k, (n - 1) as nat)
        }
    }
}

pub open spec fn spec_map_find(keys: Seq<Vec<u8>>, k: Seq<u8>) -> Option<int> {
    spec_map_find_key_upto(keys, k, keys.len() as nat)
}

pub open spec fn spec_map_has(keys: Seq<Vec<u8>>, k: Seq<u8>) -> bool {
    spec_map_find(keys, k) is Some
}

/// The index list for column position `key_pos` among the first `n`
/// events, in push order (the merged order std keeps per key).
pub open spec fn spec_map_hits_upto(evs: Seq<(usize, usize)>, key_pos: int, n: nat) -> Seq<usize>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let (p, i) = evs.index((n - 1) as int);
        let base = spec_map_hits_upto(evs, key_pos, (n - 1) as nat);
        if (p as int) == key_pos {
            base.push(i)
        } else {
            base
        }
    }
}

pub open spec fn spec_map_hits(evs: Seq<(usize, usize)>, key_pos: int) -> Seq<usize> {
    spec_map_hits_upto(evs, key_pos, evs.len() as nat)
}

/// The merged hit list a get sees: found position's log, else empty.
pub open spec fn spec_hit_list(keys: Seq<Vec<u8>>, evs: Seq<(usize, usize)>, k: Seq<u8>) -> Seq<usize> {
    match spec_map_find(keys, k) {
        Some(j) => spec_map_hits(evs, j),
        None => Seq::empty(),
    }
}

/// get's total return shape.
pub open spec fn spec_map_get_opt(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    k: Seq<u8>,
) -> Option<Seq<usize>> {
    match spec_map_find(keys, k) {
        Some(j) => Some(spec_map_hits(evs, j)),
        None => None,
    }
}

/// len: the distinct-key count (std HashMap::len, the matches_all
/// singleton gate at lib.rs:767/806).
pub open spec fn spec_map_len(keys: Seq<Vec<u8>>) -> nat {
    keys.len() as nat
}

impl FnvByteMap {
    /// Origin Rust (`fnv::HashMap::default()`): the empty map.
    pub fn new() -> (r: FnvByteMap)
        ensures
            r.keys@ == Seq::empty(),
            r.events@ == Seq::empty(),
    {
        FnvByteMap { keys: Vec::new(), events: Vec::new() }
    }

    /// Origin Rust (std HashMap::contains_key; consumer sites
    /// lib.rs:763 `self.literals.contains_key(path)`,
    /// lib.rs:802 `self.0.contains_key(candidate.ext.as_bytes())`).
    pub fn contains_key(&self, k: &[u8]) -> (r: bool)
        ensures
            r == spec_map_has(self.keys@, k@),
    {
        let ks: &[Vec<u8>] = self.keys.as_slice();
        let mut i: usize = ks.len();
        let mut found: bool = false;
        let mut fpos: usize = 0;
        while !found && i > 0
            invariant
                i <= ks.len(),
                ks@ == self.keys@,
                ks.len() == self.keys@.len(),
                ks.len() == ks@.len(),
                !found ==> forall|n: nat|
                    (i as int) <= n < ks.len() ==> spec_key_view(self.keys@, n as int) != k@,
                found ==> {
                    &&& fpos == i - 1
                    &&& self.keys@.index(fpos as int)@ == k@
                    &&& spec_map_find_key_upto(self.keys@, k@, ks.len() as nat)
                        == Some(fpos as int)
                },
            decreases (if found { 0int } else { 1int }), i,
        {
            if bytes_vec_slice_eq(&self.keys[i - 1], k) {
                let ipos: usize = i - 1;
                proof {
                    assert(i >= 1);
                    assert(ks.len() == self.keys@.len());
                    assert(self.keys@.index(ipos as int)@ == k@);
                    assert(forall|q: int|
                        (ipos as int) < q < ks.len() as int
                            ==> spec_key_view(self.keys@, q) != k@);
                    lemma_find_key_hit_at(
                        self.keys@,
                        k@,
                        ks.len() as nat,
                        ipos as int,
                    );
                }
                fpos = i - 1;
                found = true;
            } else {
                proof {
                    assert(self.keys[i - 1]@ == self.keys@.index((i - 1) as int)@);
                    assert(self.keys@.index((i - 1) as int)@ != k@);
                }
                i -= 1;
            }
        }
        proof {
            if !found {
                assert(i == 0) by {
                    assert(i >= 0);
                }
                assert(forall|q: int| 0 <= q < ks.len() as int
                    ==> spec_key_view(self.keys@, q) != k@);
                lemma_find_key_none(self.keys@, k@, ks.len() as nat);
            }
        }
        found
    }

    /// Origin Rust (std HashMap::get; consumer sites lib.rs:775
    /// `self.literals.get(path)`, lib.rs:818
    /// `self.0.get(candidate.ext.as_bytes())`).
    pub fn get(&self, k: &[u8]) -> (r: Option<Vec<usize>>)
        ensures
            r is Some <==> spec_map_has(self.keys@, k@),
            r is Some ==> r.get_Some_0()@ == spec_map_get_opt(self.keys@, self.events@, k@).get_Some_0(),
    {
        let ks: &[Vec<u8>] = self.keys.as_slice();
        let mut i: usize = ks.len();
        let mut result: Option<Vec<usize>> = None;
        let mut scanning: bool = true;
        while scanning && i > 0
            invariant
                i <= ks.len(),
                ks@ == self.keys@,
                ks.len() == ks@.len(),
                ks.len() == self.keys@.len(),
                scanning <==> result is None,
                result is Some ==> {
                    &&& spec_map_find(self.keys@, k@) is Some
                    &&& spec_map_get_opt(self.keys@, self.events@, k@).get_Some_0()
                        == result.get_Some_0()@
                },
                result is None ==> forall|n: nat|
                    (i as int) <= n < ks.len() ==> spec_key_view(self.keys@, n as int) != k@,
            decreases (if scanning { 1int } else { 0int }), i,
        {
            if bytes_vec_slice_eq(&self.keys[i - 1], k) {
                let ipos: usize = i - 1;
                proof {
                    assert(i >= 1);
                    assert(ks.len() == self.keys@.len());
                    assert(self.keys@.index(ipos as int)@ == k@);
                    assert(forall|q: int|
                        (ipos as int) < q < ks.len() as int
                            ==> spec_key_view(self.keys@, q) != k@);
                    lemma_find_key_hit_at(
                        self.keys@,
                        k@,
                        ks.len() as nat,
                        ipos as int,
                    );
                }
                let j: usize = i - 1;
                let evs: &[(usize, usize)] = self.events.as_slice();
                let mut out: Vec<usize> = Vec::new();
                let mut q: usize = 0;
                while q < evs.len()
                    invariant
                        q <= evs.len(),
                        evs@ == self.events@,
                        evs.len() == self.events@.len(),
                        j < ks.len(),
                        ks@ == self.keys@,
                        self.keys@.index(j as int)@ == k@,
                        spec_map_find_key_upto(self.keys@, k@, ks.len() as nat)
                            == Some(j as int),
                        out@ == spec_map_hits_upto(self.events@, j as int, q as nat),
                    decreases evs.len() - q,
                {
                    let pair: (usize, usize) = evs[q];
                    if pair.0 == j {
                        proof {
                            lemma_hits_step(self.events@, j as int, (q + 1) as nat);
                        }
                        out.push(pair.1);
                    } else {
                        proof {
                            assert((self.events@.index(q as int).0 as int) != (j as int));
                            lemma_hits_step(self.events@, j as int, (q + 1) as nat);
                        }
                    }
                    q += 1;
                }
                proof {
                    assert(spec_map_find(self.keys@, k@) == Some(j as int));
                    assert(spec_map_hits(self.events@, j as int) == out@);
                    assert(spec_map_get_opt(self.keys@, self.events@, k@) == Some(out@));
                }
                result = Some(out);
                scanning = false;
            } else {
                proof {
                    assert(self.keys[i - 1]@ == self.keys@.index((i - 1) as int)@);
                    assert(self.keys@.index((i - 1) as int)@ != k@);
                }
                i -= 1;
            }
        }
        proof {
            if result is None {
                assert(i == 0) by {
                    assert(i >= 0);
                }
                assert(forall|q: int| 0 <= q < ks.len() as int
                    ==> spec_key_view(self.keys@, q) != k@);
                lemma_find_key_none(self.keys@, k@, ks.len() as nat);
            }
        }
        result
    }

    /// Origin Rust (lib.rs:756-759 / 794-795):
    ///   self.literals.entry(lit.into_bytes()).or_insert(vec![])
    ///       .push(global_index);
    ///   self.0.entry(ext.into_bytes()).or_insert(vec![])
    ///       .push(global_index);
    /// (byte-equal keys merge their index lists in push order; a fresh
    /// key opens a new column slot at the end)
    pub fn add(&mut self, k: Vec<u8>, global_index: usize)
        requires
            // the event log names live column slots (threaded by every
            // add; the map starts empty)
            forall|e: int|
                0 <= e < self.events@.len()
                    ==> (self.events@.index(e).0 as int) < self.keys@.len(),
        ensures
            final(self).events@.len() == old(self).events@.len() + 1,
            final(self).events@.subrange(0, old(self).events@.len() as int) == old(self).events@,
            final(self).events@.index(old(self).events@.len() as int).1 == global_index,
            final(self).events@.index(old(self).events@.len() as int).0 == (if spec_map_find(
                old(self).keys@,
                k@,
            ) is Some {
                spec_map_find(old(self).keys@, k@).get_Some_0() as usize
            } else {
                old(self).keys@.len() as usize
            }),
            // key column: merge keeps, fresh extends with k at the end
            (spec_map_find(old(self).keys@, k@) is Some) ==> final(self).keys@ == old(self).keys@,
            (spec_map_find(old(self).keys@, k@) is None) ==> {
                &&& final(self).keys@.len() == old(self).keys@.len() + 1
                &&& final(self).keys@.subrange(0, old(self).keys@.len() as int) == old(self).keys@
                &&& final(self).keys@.index(old(self).keys@.len() as int)@ == k@
                &&& final(self).keys@ == old(self).keys@.push(k)
                &&& spec_map_find(final(self).keys@, k@) == Some(old(self).keys@.len() as int)
            },
            // the queried key's hit list, merge vs fresh
            (spec_map_find(old(self).keys@, k@) is Some) ==> spec_hit_list(
                final(self).keys@,
                final(self).events@,
                k@,
            ) == spec_hit_list(old(self).keys@, old(self).events@, k@).push(
                global_index as usize,
            ),
            (spec_map_find(old(self).keys@, k@) is None) ==> spec_hit_list(
                final(self).keys@,
                final(self).events@,
                k@,
            ) == seq![global_index as usize],
            // every byte-unequal key keeps its hit list
            forall|kb: Seq<u8>|
                kb != k@ ==> spec_hit_list(final(self).keys@, final(self).events@, kb)
                    == spec_hit_list(old(self).keys@, old(self).events@, kb),
            // every event names a position inside the key column
            forall|q: int|
                0 <= q < final(self).events@.len()
                    ==> (final(self).events@.index(q).0 as int) < final(self).keys@.len(),
    {
        let old_keys_len: usize = self.keys.len();
        let old_events_len: usize = self.events.len();
        let ks: &[Vec<u8>] = self.keys.as_slice();
        let mut i: usize = ks.len();
        let mut hit: Option<usize> = None;
        let mut scanning: bool = true;
        while scanning && i > 0
            invariant
                scanning <==> hit is None,
                i <= ks.len(),
                ks@ == self.keys@,
                ks.len() == ks@.len(),
                ks.len() == old_keys_len,
                ks.len() == self.keys@.len(),
                old_keys_len == self.keys@.len(),
                old_events_len == self.events@.len(),
                hit is None ==> forall|n: nat|
                    (i as int) <= n < ks.len() ==> spec_key_view(self.keys@, n as int) != k@,
                hit is Some ==> {
                    let j = hit.get_Some_0();
                    &&& j < i
                    &&& j < old_keys_len
                    &&& self.keys@.index(j as int)@ == k@
                    &&& spec_map_find(self.keys@, k@) == Some(j as int)
                },
            decreases (if hit is Some { 0int } else { 1int }), i,
        {
            if bytes_vec_slice_eq(&self.keys[i - 1], &k) {
                let ipos: usize = i - 1;
                proof {
                    assert(i >= 1);
                    assert(ks.len() == self.keys@.len());
                    assert(self.keys@.index(ipos as int)@ == k@);
                    assert(forall|q: int|
                        (ipos as int) < q < ks.len() as int
                            ==> spec_key_view(self.keys@, q) != k@);
                    lemma_find_key_hit_at(self.keys@, k@, ks.len() as nat, ipos as int);
                }
                hit = Some(ipos);
                scanning = false;
            } else {
                let ipos: usize = i - 1;
                proof {
                    assert(self.keys@.index(ipos as int)@ != k@);
                }
                i -= 1;
            }
        }
        proof {
            if hit is None {
                assert(i == 0) by {
                    assert(i >= 0);
                }
                assert(forall|q: int| 0 <= q < ks.len() as int
                    ==> spec_key_view(self.keys@, q) != k@);
                lemma_find_key_none(self.keys@, k@, ks.len() as nat);
            }
        }
        match hit {
            Some(j) => {
                self.events.push((j, global_index));
                proof {
                    assert(self.events@.len() == (old(self).events@.len() as int) + 1);
                    assert(self.events@.index(old(self).events@.len() as int)
                        == (j, global_index));
                    assert(self.keys@ == old(self).keys@);
                    assert((j as int) < (self.keys.len() as int));
                    assert forall|q: int|
                        0 <= q < self.events@.len()
                            implies (self.events@.index(q).0 as int) < self.keys@.len() by {
                        if (q as int) < old(self).events@.len() {
                            assert(self.events@.index(q) == old(self).events@.index(q));
                        } else {
                            assert(self.events@.index(q).0 == j);
                        }
                    }
                    lemma_merge_add_effects(
                        old(self).keys@,
                        old(self).events@,
                        self.keys@,
                        self.events@,
                        k@,
                        j as int,
                        j,
                        global_index,
                    );
                }
            },
            None => {
                let slot: usize = old_keys_len;
                self.keys.push(k);
                self.events.push((slot, global_index));
                proof {
                    assert((slot as int) == old(self).keys@.len());
                    assert(self.keys@ == old(self).keys@.push(k));
                    assert(self.events@ == old(self).events@.push((slot, global_index)));
                    assert(self.events@.len() == (old(self).events@.len() as int) + 1);
                    assert(self.events@.index(old(self).events@.len() as int)
                        == (slot, global_index));
                    assert(self.keys.len() == (self.keys@.len() as usize));
                    assert(self.keys@.len() == (old(self).keys@.len() as int) + 1);
                    assert forall|q: int|
                        0 <= q < self.events@.len()
                            implies (self.events@.index(q).0 as int) < self.keys@.len() by {
                        if (q as int) < old(self).events@.len() {
                            assert(self.events@.index(q) == old(self).events@.index(q));
                        } else {
                            assert(self.events@.index(q).0 == slot);
                        }
                    }
                    lemma_fresh_add_effects(
                        old(self).keys@,
                        old(self).events@,
                        self.keys@,
                        self.events@,
                        k,
                        k@,
                        slot,
                        global_index,
                    );
                }
            },
        }
    }

    /// Origin Rust (std HashMap::len; the matches_all singleton gate at
    /// lib.rs:767 `self.literals.len() == 1`,
    /// lib.rs:806 `self.0.len() == 1`).
    pub fn len(&self) -> (r: usize)
        ensures
            r == self.keys.len(),
            r as int == spec_map_len(self.keys@) as int,
    {
        self.keys.len()
    }
}

// ---------------------------------------------------------------------------
// Map scan lemmas (the rfind family discipline of GL1's pathutil).
// ---------------------------------------------------------------------------

/// A concrete byte-equal column slot at j, with nothing byte-equal
/// after it, IS the find result.
proof fn lemma_find_key_hit_at(keys: Seq<Vec<u8>>, k: Seq<u8>, n: nat, j: int)
    requires
        0 <= j < (n as int),
        n as int <= keys.len(),
        keys.index(j)@ == k,
        forall|q: int| j < q < n as int ==> spec_key_view(keys, q) != k,
    ensures
        spec_map_find_key_upto(keys, k, n) == Some(j),
    decreases n,
{
    if n > 0 {
        assert(spec_key_view(keys, (n - 1) as int) == keys.index((n - 1) as int)@);
        if (n as int) - 1 == j {
            // the def lands on this top position
            assert(spec_map_find_key_upto(keys, k, n) == Some((n - 1) as int));
        } else {
            assert((n as int) - 1 > j);
            assert(keys.index((n - 1) as int)@ != k);
            assert(spec_map_find_key_upto(keys, k, n)
                == spec_map_find_key_upto(keys, k, (n - 1) as nat));
            lemma_find_key_hit_at(keys, k, (n - 1) as nat, j);
        }
    }
}

/// No byte-equal column slot anywhere up to n: find is None.
proof fn lemma_find_key_none(keys: Seq<Vec<u8>>, k: Seq<u8>, n: nat)
    requires
        n as int <= keys.len(),
        forall|q: int| 0 <= q < n as int ==> spec_key_view(keys, q) != k,
    ensures
        spec_map_find_key_upto(keys, k, n) is None,
    decreases n,
{
    if n > 0 {
        assert(spec_key_view(keys, (n - 1) as int) == keys.index((n - 1) as int)@);
        assert(keys.index((n - 1) as int)@ != k);
        lemma_find_key_none(keys, k, (n - 1) as nat);
    }
}

/// None means no byte-equal position anywhere below n (the per-position
/// companion to lemma_find_key_none).
proof fn lemma_find_none_no_pos(keys: Seq<Vec<u8>>, k: Seq<u8>, n: nat)
    requires
        n as int <= keys.len(),
        spec_map_find_key_upto(keys, k, n) is None,
    ensures
        forall|q: int| 0 <= q < n as int ==> spec_key_view(keys, q) != k,
    decreases n,
{
    if n > 0 {
        assert(spec_key_view(keys, (n - 1) as int) == keys.index((n - 1) as int)@);
        assert(keys.index((n - 1) as int)@ != k);
        lemma_find_none_no_pos(keys, k, (n - 1) as nat);
    }
}

/// No event names the column position: the filtered log is empty.
proof fn lemma_hits_all_skip(evs: Seq<(usize, usize)>, pos: int, n: nat)
    requires
        n as int <= evs.len(),
        forall|e: int| 0 <= e < n as int ==> (evs.index(e).0 as int) != pos,
    ensures
        spec_map_hits_upto(evs, pos, n) == Seq::empty(),
    decreases n,
{
    if n > 0 {
        assert((evs.index((n - 1) as int).0 as int) != pos);
        lemma_hits_step(evs, pos, n);
        lemma_hits_all_skip(evs, pos, (n - 1) as nat);
    }
}

/// What a Some find says about the found position (the converse
/// companion to lemma_find_key_hit_at).
proof fn lemma_find_hit_property(keys: Seq<Vec<u8>>, k: Seq<u8>, n: nat, j: int)
    requires
        n as int <= keys.len(),
        spec_map_find_key_upto(keys, k, n) == Some(j),
    ensures
        j < (n as int),
        keys.index(j)@ == k,
        forall|q: int| j < q < n as int ==> spec_key_view(keys, q) != k,
    decreases n,
{
    if n > 0 {
        assert(spec_key_view(keys, (n - 1) as int) == keys.index((n - 1) as int)@);
        let top = keys.index((n - 1) as int);
        if top@ == k {
            // the def landed on this top position
            assert(spec_map_find_key_upto(keys, k, n) == Some((n - 1) as int));
            assert(j == (n - 1) as int);
        } else {
            // it recursed below: j stays below n-1 and the top position
            // is byte-unequal
            assert(spec_map_find_key_upto(keys, k, n)
                == spec_map_find_key_upto(keys, k, (n - 1) as nat));
            lemma_find_hit_property(keys, k, (n - 1) as nat, j);
            assert(j < ((n - 1) as int));
        }
    }
}

/// The log-filter step at event count n (hit or skip, one step).
proof fn lemma_hits_step(evs: Seq<(usize, usize)>, key_pos: int, n: nat)
    requires
        0 < n,
        n as int <= evs.len(),
    ensures
        spec_map_hits_upto(evs, key_pos, n)
            == (if (evs.index((n - 1) as int).0 as int) == key_pos {
                spec_map_hits_upto(evs, key_pos, (n - 1) as nat).push(evs.index((n - 1) as int).1)
            } else {
                spec_map_hits_upto(evs, key_pos, (n - 1) as nat)
            }),
{
}

/// Evaluating the filter over a pushed log agrees on the untouched
/// prefix (push-index axiom, by induction).
proof fn lemma_hits_push_irrelevant(
    evs: Seq<(usize, usize)>,
    t: (usize, usize),
    key_pos: int,
    n: nat,
)
    requires
        0 <= n <= evs.len(),
    ensures
        spec_map_hits_upto(evs.push(t), key_pos, n) == spec_map_hits_upto(evs, key_pos, n),
    decreases n,
{
    if n > 0 {
        assert(evs.push(t).index((n - 1) as int) == evs.index((n - 1) as int));
        lemma_hits_push_irrelevant(evs, t, key_pos, (n - 1) as nat);
        lemma_hits_step(evs.push(t), key_pos, n);
        lemma_hits_step(evs, key_pos, n);
    }
}

/// Extending ends a merge: the new event lands at the end of the hit
/// list for its column position.
proof fn lemma_hits_push_extend(evs: Seq<(usize, usize)>, t: (usize, usize), key_pos: int)
    requires
        t.0 as int == key_pos,
    ensures
        spec_map_hits_upto(evs.push(t), key_pos, (evs.len() + 1) as nat)
            == spec_map_hits_upto(evs, key_pos, evs.len() as nat).push(t.1),
{
    lemma_hits_push_irrelevant(evs, t, key_pos, evs.len() as nat);
    lemma_hits_step(evs.push(t), key_pos, (evs.len() + 1) as nat);
}

/// Find over a column extended at the end (prefix `keys`, appended
/// element `kv` byte-unequal to `k`) keeps the find result: the
/// push-index axioms fold the recursive scans onto each other.
proof fn lemma_find_extend_stable(
    keys: Seq<Vec<u8>>,
    kv: Vec<u8>,
    k: Seq<u8>,
    n: nat,
)
    requires
        n <= keys.len(),
        kv@ != k,
    ensures
        spec_map_find_key_upto(keys.push(kv), k, n) == spec_map_find_key_upto(keys, k, n),
    decreases n,
{
    if n > 0 {
        assert(keys.push(kv).index((n - 1) as int)@ == keys.index((n - 1) as int)@);
        lemma_find_extend_stable(keys, kv, k, (n - 1) as nat);
    }
}

/// The merge-add consequences (k already has column slot j; every other
/// key keeps its find result and hit list, e.g. the fresh event column
/// is untouched by construction).
proof fn lemma_merge_add_effects(
    old_keys: Seq<Vec<u8>>,
    old_evs: Seq<(usize, usize)>,
    new_keys: Seq<Vec<u8>>,
    new_evs: Seq<(usize, usize)>,
    k: Seq<u8>,
    j: int,
    ju: usize,
    gi: usize,
)
    requires
        new_keys == old_keys,
        0 <= j < old_keys.len(),
        spec_map_find(old_keys, k) == Some(j),
        ju as int == j,
        new_evs == old_evs.push((ju, gi)),
    ensures
        spec_hit_list(new_keys, new_evs, k) == spec_hit_list(old_keys, old_evs, k).push(gi as usize),
        forall|kb: Seq<u8>|
            kb != k ==> spec_hit_list(new_keys, new_evs, kb)
                == spec_hit_list(old_keys, old_evs, kb),
{
    lemma_hits_push_extend(old_evs, (ju, gi), j);
    assert(spec_map_hits(new_evs, j) == spec_map_hits(old_evs, j).push(gi));
    assert(spec_map_find(new_keys, k) == spec_map_find(old_keys, k));
    assert forall|kb: Seq<u8>|
        kb != k implies spec_hit_list(new_keys, new_evs, kb)
            == spec_hit_list(old_keys, old_evs, kb)
    by {
        if spec_map_find(old_keys, kb) is Some {
            let j2 = spec_map_find(old_keys, kb).get_Some_0();
            lemma_find_hit_property(old_keys, kb, old_keys.len() as nat, j2);
            lemma_find_hit_property(old_keys, k, old_keys.len() as nat, j);
            // positions holding different byte keys are different
            assert(j2 != j) by {
                assert(spec_key_view(old_keys, j2) == kb);
                assert(kb != k);
            }
            assert(spec_map_find(new_keys, kb) == Some(j2));
            lemma_hits_push_irrelevant(old_evs, (ju, gi), j2, old_evs.len() as nat);
            assert(spec_map_hits(new_evs, j2) == spec_map_hits(old_evs, j2));
        } else {
            assert(spec_map_find(new_keys, kb) is None);
        }
    }
}

/// The fresh-add consequences (k opens the new end slot; every other key
/// keeps its find result and hit list).
proof fn lemma_fresh_add_effects(
    old_keys: Seq<Vec<u8>>,
    old_evs: Seq<(usize, usize)>,
    new_keys: Seq<Vec<u8>>,
    new_evs: Seq<(usize, usize)>,
    kv: Vec<u8>,
    k: Seq<u8>,
    lu: usize,
    gi: usize,
)
    requires
        kv@ == k,
        spec_map_find(old_keys, k) is None,
        lu as int == old_keys.len(),
        new_keys == old_keys.push(kv),
        new_evs == old_evs.push((lu, gi)),
        forall|e: int|
            0 <= e < old_evs.len() ==> (old_evs.index(e).0 as int) < old_keys.len(),
    ensures
        spec_map_find(new_keys, k) == Some(old_keys.len() as int),
        spec_hit_list(new_keys, new_evs, k) == seq![gi as usize],
        forall|kb: Seq<u8>|
            kb != k ==> spec_hit_list(new_keys, new_evs, kb)
                == spec_hit_list(old_keys, old_evs, kb),
{
    reveal_with_fuel(spec_map_hits_upto, 4);
    reveal_with_fuel(spec_map_find_key_upto, 3);
    lemma_find_none_no_pos(old_keys, k, old_keys.len() as nat);
    lemma_find_key_none(old_keys, k, old_keys.len() as nat);
    assert(new_keys.index(old_keys.len() as int)@ == kv@);
    lemma_find_key_hit_at(new_keys, k, (old_keys.len() + 1) as nat, old_keys.len() as int);
    // k's hits: only the final event names the fresh slot, so the old
    // prefix filters to empty and the final event lands as the only hit
    assert forall|e: int| 0 <= e < old_evs.len()
        implies (old_evs.index(e).0 as int) != (lu as int) by {
        assert((old_evs.index(e).0 as int) < old_keys.len());
        assert(lu as int == old_keys.len());
    }
    lemma_hits_push_irrelevant(
        old_evs,
        (lu, gi),
        old_keys.len() as int,
        old_evs.len() as nat,
    );
    lemma_hits_all_skip(old_evs, old_keys.len() as int, old_evs.len() as nat);
    assert(spec_map_hits_upto(old_evs, old_keys.len() as int, old_evs.len() as nat)
        == Seq::empty());
    assert(new_evs.len() == (old_evs.len() as int) + 1);
    assert(new_evs.index(old_evs.len() as int) == (lu, gi));
    assert(spec_map_hits_upto(new_evs, old_keys.len() as int, old_evs.len() as nat)
        == Seq::empty());
    assert(spec_map_hits_upto(new_evs, old_keys.len() as int, (old_evs.len() + 1) as nat)
        == spec_map_hits_upto(new_evs, old_keys.len() as int, old_evs.len() as nat).push(gi))
    by {
        lemma_hits_step(new_evs, old_keys.len() as int, (old_evs.len() + 1) as nat);
        assert(new_evs.index(old_evs.len() as int).0 as int == old_keys.len() as int);
    }
    assert(spec_map_hits(new_evs, old_keys.len() as int)
        == spec_map_hits_upto(new_evs, old_keys.len() as int, new_evs.len() as nat));
    assert(spec_map_hits(new_evs, old_keys.len() as int) == seq![gi as usize]);
    assert(spec_map_find(new_keys, k) == Some(old_keys.len() as int));
    assert(spec_hit_list(new_keys, new_evs, k) == seq![gi as usize]);
    assert forall|kb: Seq<u8>|
        kb != k implies spec_hit_list(new_keys, new_evs, kb)
            == spec_hit_list(old_keys, old_evs, kb)
    by {
        // the extended column's top holds kv's bytes, unequal to kb:
        // the find def folds one step, then the prefix scans agree
        assert(new_keys.index(old_keys.len() as int)@ == kv@);
        assert(kv@ != kb);
        assert(spec_map_find_key_upto(new_keys, kb, (old_keys.len() + 1) as nat)
            == spec_map_find_key_upto(new_keys, kb, old_keys.len() as nat));
        lemma_find_extend_stable(old_keys, kv, kb, old_keys.len() as nat);
        if spec_map_find(old_keys, kb) is Some {
            let j2 = spec_map_find(old_keys, kb).get_Some_0();
            lemma_find_hit_property(old_keys, kb, old_keys.len() as nat, j2);
            assert(j2 != old_keys.len());
            lemma_find_extend_stable(old_keys, kv, kb, old_keys.len() as nat);
            lemma_hits_push_irrelevant(
                old_evs,
                (lu, gi),
                j2,
                old_evs.len() as nat,
            );
            assert(spec_map_hits(new_evs, j2) == spec_map_hits(old_evs, j2));
        } else {
            assert(spec_map_find(new_keys, kb) is None);
        }
    }
}


// ===========================================================================
// Candidate -- upstream lib.rs:603-672.
// ===========================================================================

/// The basename column of a candidate path: the final component if it
/// is a normal file name, else empty (the from_cow unwrap_or(B(""))
/// column, lib.rs:646).
pub open spec fn spec_cand_basename(p: Seq<u8>) -> Seq<u8> {
    if p.len() == 0 || spec_final_component(p) == spec_dotdot() {
        Seq::empty()
    } else {
        spec_final_component(p)
    }
}

/// The candidate's extension: the basename's final-dot suffix if it
/// has one, else empty (the from_cow unwrap_or(B("")) column over
/// file_name_ext, lib.rs:647).
pub open spec fn spec_cand_ext(p: Seq<u8>) -> Seq<u8> {
    let b = spec_cand_basename(p);
    if b.len() == 0 || rfind_pref(b, 0x2e, b.len() as int) < 0 {
        Seq::empty()
    } else {
        spec_final_ext(b)
    }
}

/// The candidate's file-name Option column (the underlying model:
/// None exactly when the path is empty or the final component is `..`
/// -- GL1's file_name none-iff contract, restated over the candidate).
pub open spec fn spec_cand_name_opt(p: Seq<u8>) -> Option<Seq<u8>> {
    if p.len() == 0 || spec_final_component(p) == spec_dotdot() {
        None
    } else {
        Some(spec_final_component(p))
    }
}

/// The basename_for_regex arm condition, index-read form (the raw
/// path-ends_with of lib.rs:658).
pub open spec fn spec_cand_base_for_regex_arm(p: Seq<u8>) -> bool {
    let base = spec_cand_basename(p);
    base.len() == 0
        && p.len() >= 2
        && p.index(p.len() - 2) == 0x2e
        && p.index(p.len() - 1) == 0x2e
}

/// The window slicers (Candidate::path_prefix at lib.rs:651-653 and
/// Candidate::path_suffix at lib.rs:665-671; the prefix/suffix window
// anchors, NOT the glob.rs:1086-1096 cfg(test) starts_with/ends_with).
pub open spec fn spec_window(p: Seq<u8>, max: int, from_end: bool) -> Seq<u8> {
    if p.len() <= max {
        p
    } else if from_end {
        p.subrange(p.len() - max, p.len() as int)
    } else {
        p.subrange(0, max)
    }
}

/// Candidate well-formedness: the field columns agree with the path
/// (what every constructor guarantees; the methods read it).
pub open spec fn spec_cand_wf(c: &Candidate) -> bool {
    &&& c.basename.view() == spec_cand_basename(c.path.view())
    &&& c.ext.view() == spec_cand_ext(c.path.view())
}

pub struct Candidate<'a> {
    pub path: CowBytes<'a>,
    pub basename: CowBytes<'a>,
    pub ext: CowBytes<'a>,
}

impl<'a> Candidate<'a> {
    /// Origin Rust (lib.rs:644-649, from_cow -- private upstream, the
    /// constructor all three public entry points feed):
    ///     fn from_cow(path: Cow<'a, [u8]>) -> Candidate<'a> {
    ///         let path = normalize_path(path);
    ///         let basename = file_name(&path).unwrap_or(Cow::Borrowed(B("")));
    ///         let ext = file_name_ext(&basename).unwrap_or(Cow::Borrowed(B("")));
    ///         Candidate { path, basename, ext }
    ///     }
    pub fn from_cow(path: CowBytes<'a>) -> (r: Candidate<'a>)
        ensures
            spec_cand_wf(&r),
            r.path.view() == path.view(),
            r.basename.view() == spec_cand_basename(path.view()),
            r.ext.view() == spec_cand_ext(path.view()),
            r.path.is_borrowed_mode() <==> path.is_borrowed_mode(),
            spec_cand_name_opt(path.view()) is Some
                ==> (r.basename.is_borrowed_mode() <==> path.is_borrowed_mode()),
            spec_cand_name_opt(path.view()) is None ==> r.basename.is_borrowed_mode(),
            spec_cand_ext(path.view()).len() > 0
                ==> (r.ext.is_borrowed_mode() <==> r.basename.is_borrowed_mode()),
            spec_cand_ext(path.view()).len() == 0 ==> r.ext.is_borrowed_mode(),
    {
        // Origin Rust: `let path = normalize_path(path);` -- the unix
        // arm is the identity (pathutil.rs:58-62, GL1 twin).
        let path = normalize_path(path);
        // Origin Rust: `file_name(&path).unwrap_or(Cow::Borrowed(B("")))`
        let basename: CowBytes<'a> = match file_name(&path) {
            Some(b) => b,
            None => CowBytes::Borrowed(&[]),
        };
        // Origin Rust: `file_name_ext(&basename).unwrap_or(Cow::Borrowed(B("")))`
        let ext: CowBytes<'a> = match file_name_ext(&basename) {
            Some(e) => e,
            None => CowBytes::Borrowed(&[]),
        };
        proof {
            // the wf columns fold case-by-case from the GL1 contracts
            if spec_cand_name_opt(path.view()) is Some {
                assert(spec_cand_basename(path.view()) == spec_final_component(path.view()));
            } else {
                assert(spec_cand_basename(path.view()) == Seq::empty());
            }
            assert(basename.view() == spec_cand_basename(path.view()));
            if spec_cand_basename(path.view()).len() == 0
                || rfind_pref(spec_cand_basename(path.view()), 0x2e, spec_cand_basename(path.view()).len() as int) < 0
            {
                assert(spec_cand_ext(path.view()) == Seq::empty());
                assert(ext.view() == spec_cand_ext(path.view()));
            } else {
                assert(
                    spec_cand_ext(path.view())
                        == spec_final_ext(spec_cand_basename(path.view()))
                );
                assert(ext.view() == spec_cand_ext(path.view()));
            }
        }
        Candidate { path, basename, ext }
    }

    /// Create a new candidate for matching from the given path.
    ///
    /// Origin Rust (lib.rs:626-630 + the bstr face, recon completed):
    ///     pub fn new<P: AsRef<Path> + ?Sized>(path: &'a P) -> Candidate<'a> {
    ///         Self::from_cow(Vec::from_path_lossy(path.as_ref()))
    ///     }
    /// bstr 1.13.0 ext_vec.rs:306-313: on unix `from_os_str_lossy`
    /// returns `Cow::Borrowed(os_str.as_bytes())` -- the byte-for-byte
    /// identity over the raw path, so `new` equals `from_bytes` on the
    /// host-live platform; the not-unix arm (to_string_lossy transcoding)
    /// stays in the D2 windows-oracle deferred set. Param shape: the
    /// twin takes the already-decoded bytes (AsRef<Path> -> OsStr ->
    /// bytes is the unix identity; recorded, GL1's deferred bstr face
    /// closes here without a trust grant).
    pub fn new(path: &'a [u8]) -> (r: Candidate<'a>)
        ensures
            spec_cand_wf(&r),
            r.path.view() == path@,
            r.basename.view() == spec_cand_basename(path@),
            r.ext.view() == spec_cand_ext(path@),
            r.path.is_borrowed_mode(),
            r.basename.is_borrowed_mode(),
            r.ext.is_borrowed_mode(),
    {
        Candidate::from_bytes(path)
    }

    /// Create a new candidate for matching from the given path as a
    /// sequence of bytes.
    ///
    /// Generally speaking, this routine expects the bytes to be
    /// _conventionally_ UTF-8. It is legal for the byte sequence to
    /// contain invalid UTF-8. However, if the bytes are in some other
    /// encoding that isn't ASCII compatible (for example, UTF-16), then
    /// the results of matching are unspecified.
    ///
    /// Origin Rust (lib.rs:640-642, upstream quotes above doc verbatim):
    ///     pub fn from_bytes<P: AsRef<[u8]> + ?Sized>(path: &'a P) -> Candidate<'a> {
    ///         Self::from_cow(Cow::Borrowed(path.as_ref()))
    ///     }
    /// (Borrowed keeps Borrowed -- the Cow ghost discipline: a borrowed
    ///  query stays borrowed through normalize/file_name/file_name_ext
    ///  per the mode contracts above.)
    pub fn from_bytes(path: &'a [u8]) -> (r: Candidate<'a>)
        ensures
            spec_cand_wf(&r),
            r.path.view() == path@,
            r.basename.view() == spec_cand_basename(path@),
            r.ext.view() == spec_cand_ext(path@),
            r.path.is_borrowed_mode(),
            r.basename.is_borrowed_mode(),
            r.ext.is_borrowed_mode(),
    {
        Candidate::from_cow(CowBytes::Borrowed(path))
    }

    /// Origin Rust (lib.rs:651-653):
    ///     fn path_prefix(&self, max: usize) -> &[u8] {
    ///         if self.path.len() <= max { &*self.path } else { &self.path[..max] }
    ///     }
    /// (consumer: PrefixStrategy's is_match at lib.rs:833)
    pub fn path_prefix(&self, max: usize) -> (r: &[u8])
        ensures
            r@ == spec_window(self.path.view(), max as int, false),
    {
        let bs: &[u8] = self.path.as_slice();
        if bs.len() <= max {
            bs
        } else {
            vstd::slice::slice_subrange(bs, 0, max)
        }
    }

    /// Origin Rust (lib.rs:655-663, GM14's carrier -- code comment
    /// quoted):
    ///     /// Returns the final component, including `..` for regex matching.
    ///     fn basename_for_regex(&self) -> &[u8] {
    ///         // Literal basename strategies skip `..`, but a regex can match it.
    ///         if self.basename.is_empty() && self.path.ends_with(b"..") {
    ///             b".."
    ///         } else {
    ///             &self.basename
    ///         }
    ///     }
    /// (twin returns an owned Vec; the lifetime shape differs, the
    ///  value contract carries)
    pub fn basename_for_regex(&self) -> (r: Vec<u8>)
        requires
            spec_cand_wf(self),
        ensures
            r@ == ({
                let base = spec_cand_basename(self.path.view());
                if spec_cand_base_for_regex_arm(self.path.view()) {
                    spec_dotdot()
                } else {
                    base
                }
            }),
    {
        let b: &[u8] = self.basename.as_slice();
        let p: &[u8] = self.path.as_slice();
        if b.len() == 0
            && p.len() >= 2
            && p[p.len() - 2] == 0x2e
            && p[p.len() - 1] == 0x2e
        {
            proof {
                assert(spec_cand_base_for_regex_arm(p@));
            }
            let mut v: Vec<u8> = Vec::new();
            v.push(0x2e);
            v.push(0x2e);
            proof {
                assert(v@ == spec_dotdot());
                assert(spec_dotdot().len() == 2);
            }
            v
        } else {
            // the basename bytes carry the else arm (the index-read
            // guard condition lives solely in the spec arm form)
            proof {
                assert(!spec_cand_base_for_regex_arm(p@));
                assert(spec_cand_basename(p@) == b@);
            }
            vstd::slice::slice_to_vec(b)
        }
    }

    /// Origin Rust (lib.rs:665-671):
    ///     fn path_suffix(&self, max: usize) -> &[u8] {
    ///         if self.path.len() <= max {
    ///             &*self.path
    ///         } else {
    ///             &self.path[self.path.len() - max..]
    ///         }
    ///     }
    /// (consumer: SuffixStrategy's is_match at lib.rs:910)
    pub fn path_suffix(&self, max: usize) -> (r: &[u8])
        ensures
            r@ == spec_window(self.path.view(), max as int, true),
    {
        let bs: &[u8] = self.path.as_slice();
        if bs.len() <= max {
            bs
        } else {
            let start: usize = bs.len() - max;
            proof {
                assert(start + max == bs.len());
            }
            vstd::slice::slice_subrange(bs, start, bs.len())
        }
    }
}

// ===========================================================================
// LiteralStrategy -- upstream lib.rs:742-784 (the mod-64 length
// bitmask plus the fnv map; the KAT backbone is the literal_length
// filter regression at lib.rs:1361-1391).
// ===========================================================================

/// The mask query model, quoted verbatim from the upstream expression
/// (lib.rs:782): `self.lengths & (1 << (len % 64)) != 0`.
pub open spec fn spec_may_len(lengths: u64, len: int) -> bool {
    lengths & (1u64 << ((len % 64) as u64)) != 0
}

/// The add-side bit (lib.rs:755): `1 << (lit.len() % 64)`.
pub open spec fn spec_lenbit(len: int) -> u64 {
    1u64 << ((len % 64) as u64)
}

/// The is_match composite (lib.rs:762-763): the length filter gate
/// and byte-equality membership.
pub open spec fn spec_lit_is_match(
    lengths: u64,
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    path: Seq<u8>,
) -> bool {
    spec_may_len(lengths, path.len() as int) && spec_map_has(keys, path)
}

/// The merged hit list a matches_into extends by (the get postface).
pub open spec fn spec_lit_get(
    lengths: u64,
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    path: Seq<u8>,
) -> Seq<usize> {
    spec_hit_list(keys, evs, path)
}

/// matches_all (lib.rs:766-768): a single stored literal that matches.
pub open spec fn spec_lit_matches_all(lengths: u64, keys: Seq<Vec<u8>>, evs: Seq<(usize, usize)>, path: Seq<u8>) -> bool {
    keys.len() == 1 && spec_lit_is_match(lengths, keys, evs, path)
}

pub struct LiteralStrategy {
    /// Origin comment (lib.rs:745): Literal byte lengths modulo 64,
    /// checked before hashing the path.
    pub literals: FnvByteMap,
    pub lengths: u64,
}

impl LiteralStrategy {
    /// Origin Rust (lib.rs:750-752):
    ///     fn new() -> LiteralStrategy {
    ///         LiteralStrategy { literals: fnv::HashMap::default(), lengths: 0 }
    ///     }
    pub fn new() -> (r: LiteralStrategy)
        ensures
            r.literals.keys@ == Seq::empty(),
            r.literals.events@ == Seq::empty(),
            r.lengths == 0,
    {
        LiteralStrategy { literals: FnvByteMap::new(), lengths: 0 }
    }

    /// Origin Rust (lib.rs:754-760):
    ///     fn add(&mut self, global_index: usize, lit: String) {
    ///         self.lengths |= 1 << (lit.len() % 64);
    ///         self.literals.entry(lit.into_bytes())
    ///             .or_insert(vec![]).push(global_index);
    ///     }
    /// (param shape: the extractor output arrives as its byte key)
    pub fn add(&mut self, global_index: usize, lit: Vec<u8>)
        requires
            forall|e: int|
                0 <= e < self.literals.events@.len()
                    ==> (self.literals.events@.index(e).0 as int) < self.literals.keys@.len(),
        ensures
            final(self).lengths == old(self).lengths| spec_lenbit(lit@.len() as int),
            final(self).literals.keys@.len()
                == ((old(self).literals.keys@.len() as int)
                    + (if spec_map_has(old(self).literals.keys@, lit@) { 0int } else { 1int })),
            final(self).literals.events@.subrange(0, old(self).literals.events@.len() as int)
                == old(self).literals.events@,
            spec_map_has(old(self).literals.keys@, lit@) ==> {
                &&& final(self).literals.keys@ == old(self).literals.keys@
                &&& spec_hit_list(final(self).literals.keys@, final(self).literals.events@, lit@)
                    == spec_hit_list(old(self).literals.keys@, old(self).literals.events@, lit@)
                        .push(global_index as usize)
            },
            !spec_map_has(old(self).literals.keys@, lit@) ==> {
                &&& final(self).literals.keys@ == old(self).literals.keys@.push(lit)
                &&& final(self).literals.keys@.len() == old(self).literals.keys@.len() + 1
                &&& spec_map_find(final(self).literals.keys@, lit@)
                    == Some(old(self).literals.keys@.len() as int)
                &&& spec_hit_list(final(self).literals.keys@, final(self).literals.events@, lit@)
                    == seq![global_index as usize]
            },
            forall|kb: Seq<u8>|
                kb != lit@ ==> spec_hit_list(final(self).literals.keys@, final(self).literals.events@, kb)
                    == spec_hit_list(old(self).literals.keys@, old(self).literals.events@, kb),
            forall|e: int|
                0 <= e < final(self).literals.events@.len()
                    ==> (final(self).literals.events@.index(e).0 as int) < final(self).literals.keys@.len(),
    {
        let bitlen: u64 = (lit.len() % 64) as u64;
        proof {
            assert(bitlen < 64);
        }
        self.literals.add(lit, global_index);
        self.lengths = self.lengths | (1u64 << bitlen);
    }

    /// Origin Rust (lib.rs:762-763):
    ///     fn is_match(&self, path: &[u8]) -> bool {
    ///         self.may_match_length(path.len()) && self.literals.contains_key(path)
    ///     }
    pub fn is_match(&self, path: &[u8]) -> (r: bool)
        ensures
            r == spec_lit_is_match(
                self.lengths,
                self.literals.keys@,
                self.literals.events@,
                path@,
            ),
    {
        self.may_match_length(path.len()) && self.literals.contains_key(path)
    }

    /// Origin Rust (lib.rs:766-768):
    ///     fn matches_all(&self, path: &[u8]) -> bool {
    ///         self.literals.len() == 1 && self.is_match(path)
    ///     }
    pub fn matches_all(&self, path: &[u8]) -> (r: bool)
        ensures
            r == spec_lit_matches_all(
                self.lengths,
                self.literals.keys@,
                self.literals.events@,
                path@,
            ),
    {
        self.literals.len() == 1 && self.is_match(path)
    }

    /// Origin Rust (lib.rs:770-778; the #[inline(never)] attribute is
    /// not observable):
    ///     fn matches_into(&self, path: &[u8], matches: &mut Vec<usize>) {
    ///         if !self.may_match_length(path.len()) { return; }
    ///         if let Some(hits) = self.literals.get(path) { matches.extend(hits); }
    ///     }
    pub fn matches_into(&self, path: &[u8], matches: &mut Vec<usize>)
        ensures
            final(matches)@
                == (if spec_may_len(self.lengths, path.len() as int)
                && spec_map_has(self.literals.keys@, path@)
            {
                old(matches)@.add(spec_hit_list(self.literals.keys@, self.literals.events@, path@))
            } else {
                old(matches)@
            }),
    {
        if !self.may_match_length(path.len()) {
            return;
        }
        let maybe_hits: Option<Vec<usize>> = self.literals.get(path);
        match maybe_hits {
            None => {}
            Some(hits) => {
                let start_len: usize = matches.len();
                let hist: &[usize] = hits.as_slice();
                let mut q: usize = 0;
                while q < hist.len()
                    invariant
                        q <= hist.len(),
                        hist@ == spec_hit_list(self.literals.keys@, self.literals.events@, path@),
                        matches@.len() == start_len + q,
                        forall|k: int|
                            0 <= k < start_len as int
                                ==> matches@.index(k) == old(matches)@.index(k),
                        forall|k: int|
                            start_len as int <= k < matches@.len() as int
                                ==> matches@.index(k) == hist@.index(k - start_len as int),
                    decreases hist.len() - q,
                {
                    matches.push(hist[q]);
                    q += 1;
                }
                proof {
                    // concat shape: per-index stones + ext_equal
                    assert forall|k: int| 0 <= k < matches@.len() as int implies
                        matches@.index(k) == old(matches)@.add(hist@).index(k)
                    by {
                        if k < start_len as int {
                            assert(matches@.index(k) == old(matches)@.index(k));
                        } else {
                            assert(matches@.index(k) == hist@.index(k - start_len as int));
                        }
                    }
                    ext_equal(matches@, old(matches)@.add(hist@));
                    assert(matches@ == old(matches)@.add(hist@));
                }
            }
        }
    }

    /// Returns whether a length could match, allowing collisions
    /// modulo 64. (Origin doc, lib.rs:780, quoted verbatim)
    ///
    /// Origin Rust (lib.rs:781-783):
    ///     fn may_match_length(&self, len: usize) -> bool {
    ///         self.lengths & (1 << (len % 64)) != 0
    ///     }
    pub fn may_match_length(&self, len: usize) -> (r: bool)
        ensures
            r == spec_may_len(self.lengths, len as int),
    {
        self.lengths & (1u64 << ((len % 64) as u64)) != 0
    }
}

// ---------------------------------------------------------------------------
// The mod-64 length-filter soundness family (the GL6 namesake theorem
// set; all proofs ride the bit_vector strategy plus the vstd::bits
// pow2 lemmas -- see the probe evidence p_bits1..p_bits4).
// ---------------------------------------------------------------------------

/// The filter never rejects a storable length: after adding a literal,
/// a path of the same byte length always passes the gate (the
/// collision-tolerant promise on lib.rs:745/780).
pub proof fn lemma_len_filter_never_rejects(old_lengths: u64, lit_len: int, path_len: int)
    requires
        0 <= lit_len,
        lit_len == path_len,
    ensures
        (old_lengths | spec_lenbit(lit_len)) & spec_lenbit(path_len) != 0,
{
    let r: u64 = (lit_len % 64) as u64;
    vstd::bits::lemma_u64_pow2_no_overflow(r as nat);
    assert(pow2(r as nat) <= u64::MAX);
    vstd::bits::lemma_u64_shl_is_mul(1u64, r);
    vstd::arithmetic::power2::lemma_pow2_pos(r as nat);
    assert(pow2(r as nat) > 0);
    assert((1u64 << r) == (1 * pow2(r as nat)));
    assert(
        (old_lengths | (1u64 << r)) & (1u64 << r) == (1u64 << r)
    ) by (bit_vector);
    assert(spec_lenbit(lit_len) == 1u64 << r);
    assert(spec_lenbit(path_len) == 1u64 << r);
    assert((old_lengths | spec_lenbit(lit_len)) & spec_lenbit(path_len) != 0);
}


/// The same filter soundness at equal RESIDUE (the collision-tolerant
/// face the doc promises: 65- and 1-length keys share bit 1, so a stored
/// 65-length literal re-opens the gate for every 1-length query and vice
/// versa).
pub proof fn lemma_len_filter_never_rejects_res(old_lengths: u64, lit_len: int, path_len: int)
    requires
        0 <= lit_len,
        0 <= path_len,
        (lit_len % 64) == (path_len % 64),
    ensures
        (old_lengths | spec_lenbit(lit_len)) & spec_lenbit(path_len) != 0,
{
    let r: u64 = (lit_len % 64) as u64;
    vstd::bits::lemma_u64_pow2_no_overflow(r as nat);
    assert(pow2(r as nat) <= u64::MAX);
    vstd::bits::lemma_u64_shl_is_mul(1u64, r);
    vstd::arithmetic::power2::lemma_pow2_pos(r as nat);
    assert(pow2(r as nat) > 0);
    assert((1u64 << r) == (1 * pow2(r as nat)));
    assert(
        (old_lengths | (1u64 << r)) & (1u64 << r) == (1u64 << r)
    ) by (bit_vector);
    assert(spec_lenbit(lit_len) == 1u64 << r);
    assert(spec_lenbit(path_len) == 1u64 << r);
    assert((old_lengths | spec_lenbit(lit_len)) & spec_lenbit(path_len) != 0);
}

/// The strategy-level statement of the same soundness: an added
/// literal's own bytes always match after the add -- both conjuncts
/// of is_match for the added key. (The requires clauses are the add
/// semantics' postconditions, so GL7 can instantiate this straight off
/// a LiteralStrategy::add call site.)
pub proof fn lemma_add_then_is_match(
    old_lengths: u64,
    new_lengths: u64,
    old_keys: Seq<Vec<u8>>,
    new_keys: Seq<Vec<u8>>,
    old_evs: Seq<(usize, usize)>,
    new_evs: Seq<(usize, usize)>,
    lit: Seq<u8>,
    gi: usize,
)
    requires
        forall|e: int|
            0 <= e < old_evs.len() ==> (old_evs.index(e).0 as int) < old_keys.len(),
        new_lengths == old_lengths | spec_lenbit(lit.len() as int),
        (spec_map_find(old_keys, lit) is Some) ==> {
            &&& new_keys == old_keys
            &&& spec_map_find(new_keys, lit) == spec_map_find(old_keys, lit)
            &&& spec_hit_list(new_keys, new_evs, lit)
                == spec_hit_list(old_keys, old_evs, lit).push(gi as usize)
        },
        (spec_map_find(old_keys, lit) is None) ==> {
            &&& spec_map_find(new_keys, lit) == Some(old_keys.len() as int)
        },
    ensures
        spec_lit_is_match(new_lengths, new_keys, new_evs, lit),
{
    lemma_len_filter_never_rejects(old_lengths, lit.len() as int, lit.len() as int);
    // membership: post-state find is Some in both arms
    if spec_map_find(old_keys, lit) is Some {
        assert(spec_map_find(new_keys, lit) is Some);
    } else {
        assert(spec_map_find(new_keys, lit) is Some);
    }
}

// ===========================================================================
// ExtensionStrategy -- upstream lib.rs:786-822; the ext tier over the
// same fnv map (the GM9 semantics live in the Candidate ext column).
// ===========================================================================

/// The is_match composite (lib.rs:798-803): a non-empty ext that is
/// membership-present.
pub open spec fn spec_ext_is_match(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    ext: Seq<u8>,
) -> bool {
    ext.len() > 0 && spec_map_has(keys, ext)
}

/// matches_all (lib.rs:805-807).
pub open spec fn spec_ext_matches_all(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    ext: Seq<u8>,
) -> bool {
    keys.len() == 1 && spec_ext_is_match(keys, evs, ext)
}

pub struct ExtensionStrategy(pub FnvByteMap);

impl ExtensionStrategy {
    /// Origin Rust (lib.rs:790-792):
    ///     fn new() -> ExtensionStrategy { ExtensionStrategy(fnv::HashMap::default()) }
    pub fn new() -> (r: ExtensionStrategy)
        ensures
            r.0.keys@ == Seq::empty(),
            r.0.events@ == Seq::empty(),
    {
        ExtensionStrategy(FnvByteMap::new())
    }

    /// Origin Rust (lib.rs:794-796):
    ///     fn add(&mut self, global_index: usize, ext: String) {
    ///         self.0.entry(ext.into_bytes()).or_insert(vec![]).push(global_index);
    ///     }
    pub fn add(&mut self, global_index: usize, ext: Vec<u8>)
        requires
            forall|e: int|
                0 <= e < self.0.events@.len()
                    ==> (self.0.events@.index(e).0 as int) < self.0.keys@.len(),
        ensures
            final(self).0.events@.subrange(0, old(self).0.events@.len() as int)
                == old(self).0.events@,
            final(self).0.keys@.len()
                == ((old(self).0.keys@.len() as int)
                    + (if spec_map_has(old(self).0.keys@, ext@) { 0int } else { 1int })),
            spec_map_has(old(self).0.keys@, ext@) ==> {
                &&& final(self).0.keys@ == old(self).0.keys@
                &&& spec_hit_list(final(self).0.keys@, final(self).0.events@, ext@)
                    == spec_hit_list(old(self).0.keys@, old(self).0.events@, ext@)
                        .push(global_index as usize)
            },
            !spec_map_has(old(self).0.keys@, ext@) ==> {
                &&& final(self).0.keys@ == old(self).0.keys@.push(ext)
                &&& final(self).0.keys@.len() == old(self).0.keys@.len() + 1
                &&& spec_map_find(final(self).0.keys@, ext@) == Some(old(self).0.keys@.len() as int)
                &&& spec_hit_list(final(self).0.keys@, final(self).0.events@, ext@)
                    == seq![global_index as usize]
            },
            forall|kb: Seq<u8>|
                kb != ext@ ==> spec_hit_list(final(self).0.keys@, final(self).0.events@, kb)
                    == spec_hit_list(old(self).0.keys@, old(self).0.events@, kb),
            forall|e: int|
                0 <= e < final(self).0.events@.len()
                    ==> (final(self).0.events@.index(e).0 as int) < final(self).0.keys@.len(),
    {
        self.0.add(ext, global_index);
    }

    /// Origin Rust (lib.rs:798-803):
    ///     fn is_match(&self, candidate: &Candidate<'_>) -> bool {
    ///         if candidate.ext.is_empty() { return false; }
    ///         self.0.contains_key(candidate.ext.as_bytes())
    ///     }
    pub fn is_match(&self, candidate: &Candidate) -> (r: bool)
        ensures
            r == spec_ext_is_match(self.0.keys@, self.0.events@, candidate.ext.view()),
    {
        let ext: &[u8] = candidate.ext.as_slice();
        if ext.len() == 0 {
            return false;
        }
        self.0.contains_key(ext)
    }

    /// Origin Rust (lib.rs:805-807):
    ///     fn matches_all(&self, candidate: &Candidate<'_>) -> bool {
    ///         self.0.len() == 1 && self.is_match(candidate)
    ///     }
    pub fn matches_all(&self, candidate: &Candidate) -> (r: bool)
        ensures
            r == spec_ext_matches_all(
                self.0.keys@,
                self.0.events@,
                candidate.ext.view(),
            ),
    {
        self.0.len() == 1 && self.is_match(candidate)
    }

    /// Origin Rust (lib.rs:809-821, #[inline(never)]):
    ///     fn matches_into(&self, candidate: &Candidate<'_>, matches: &mut Vec<usize>) {
    ///         if candidate.ext.is_empty() { return; }
    ///         if let Some(hits) = self.0.get(candidate.ext.as_bytes()) {
    ///             matches.extend(hits);
    ///         }
    ///     }
    pub fn matches_into(&self, candidate: &Candidate, matches: &mut Vec<usize>)
        ensures
            final(matches)@
                == (if candidate.ext.view().len() > 0
                && spec_map_has(self.0.keys@, candidate.ext.view())
            {
                old(matches)@.add(spec_hit_list(self.0.keys@, self.0.events@, candidate.ext.view()))
            } else {
                old(matches)@
            }),
    {
        let ext: &[u8] = candidate.ext.as_slice();
        if ext.len() == 0 {
            return;
        }
        let maybe_hits: Option<Vec<usize>> = self.0.get(ext);
        match maybe_hits {
            None => {}
            Some(hits) => {
                let start_len: usize = matches.len();
                let hist: &[usize] = hits.as_slice();
                let mut q: usize = 0;
                while q < hist.len()
                    invariant
                        q <= hist.len(),
                        hist@ == spec_hit_list(self.0.keys@, self.0.events@, ext@),
                        matches@.len() == start_len + q,
                        forall|k: int|
                            0 <= k < start_len as int
                                ==> matches@.index(k) == old(matches)@.index(k),
                        forall|k: int|
                            start_len as int <= k < matches@.len() as int
                                ==> matches@.index(k) == hist@.index(k - start_len as int),
                    decreases hist.len() - q,
                {
                    matches.push(hist[q]);
                    q += 1;
                }
                proof {
                    assert forall|k: int| 0 <= k < matches@.len() as int implies
                        matches@.index(k) == old(matches)@.add(hist@).index(k)
                    by {
                        if k < start_len as int {
                            assert(matches@.index(k) == old(matches)@.index(k));
                        } else {
                            assert(matches@.index(k) == hist@.index(k - start_len as int));
                        }
                    }
                    ext_equal(matches@, old(matches)@.add(hist@));
                    assert(matches@ == old(matches)@.add(hist@));
                }
            }
        }
    }
}

// NOTE (the strategy-method set names mirror the GL5 char-twin table:
//  the GL6 byte face runs over CowBytes-backed Candidate values; the
//  GL5 spec_c_* family over Seq<char> paths remains the token-model
//  side. The UTF-8 injective bridge is recorded as the deferred lemma
//  family; harness-level agreement rows pin sample vectors.)

// ===========================================================================
// GL7 -- the UTF-8 encode bridge family (GL6 deferred #1, opened here
// for the fan-out weld), the AC prefix/suffix consumption twins, the
// regex oracle face, the RequiredExtension tier, the RegexSet tier,
// and the GlobSet orchestration with the sort+dedup post-condition
// (GM15).
//
// Upstream anchors: lib.rs:425-565 (GlobSet::new classification +
// builder merge), 685-1114 (dispatch, Prefix/Suffix +/- AC wiring,
// RequiredExtension + builders, MultiStrategyBuilder, the
// suffix-component literal strip at lib.rs:497-501).
//
// Mount rulings of this batch:
//  * the aho-corasick automaton face (inventory section 4: a hit
//    (p, i, j) exists iff literals[p] == haystack[i..j], positional
//    pattern ids) downgrades to a VERIFIED scan twin, exactly the
//    GL6 fnv-container precedent: under that contract the
//    m.start()==0 / m.end()==len filtered occurrence set IS the
//    per-pattern byte prefix/suffix relation, so every strategy
//    query is a verified scan (probe p_scan evidence; the automaton
//    itself remains a trusted contract face the twin never calls);
//  * the regex oracle (contract face (a)) enters as ONE uninterpreted
//    spec predicate over (regex-string chars, haystack bytes) with
//    its harness-level KAT axioms; the twin stores regex STRINGS and
//    never compiles (upstream's new_regex/new_regex_set are trusted
//    entry points, Error::Regex mapping noted as trusted content);
//  * the sort+dedup twin (GM15) builds the canonical
//    strictly-ascending value-set enumeration by a VERIFIED domain
//    walk (probes p_canon/p_canon2 evidence); std's Vec::sort/dedup
//    has no spec, so the twin does not call it (deviation recorded,
//    the FnvByteMap precedent restated).
// ===========================================================================

/// The key-view alias over the map columns (the GL6 spec_key_view;
/// re-exposed for this zone's invariant triggers).
pub open spec fn lib_key_view(keys: Seq<Vec<u8>>, q: int) -> Seq<u8> {
    keys.index(q)@
}

// ---------------------------------------------------------------------------
// Part A: the UTF-8 encode bridge.
// ---------------------------------------------------------------------------

/// One char's utf8 bytes (GL3's spec_utf8_encode carried over chars).
pub open spec fn spec_enc_char(c: char) -> Seq<u8> {
    glob::spec_utf8_encode(c as u32)
}

/// The encode of the first i chars, in order (the upto discipline).
pub open spec fn spec_encode_upto(cs: Seq<char>, i: int) -> Seq<u8>
    decreases i
{
    if i <= 0 {
        Seq::empty()
    } else {
        spec_encode_upto(cs, i - 1).add(spec_enc_char(cs.index(i - 1)))
    }
}

/// The whole-sequence encode.
pub open spec fn spec_encode(cs: Seq<char>) -> Seq<u8> {
    spec_encode_upto(cs, cs.len() as int)
}

/// The definitional push step (fuel-free; probe p_enc).
pub proof fn lemma_enc_push_step(cs: Seq<char>, i: int)
    requires
        0 <= i < cs.len(),
    ensures
        spec_encode_upto(cs, i + 1)
            == spec_encode_upto(cs, i).add(spec_enc_char(cs.index(i))),
{
}

/// upto over a pushed tail agrees on the untouched prefix (probe p_enc).
pub proof fn lemma_enc_upto_irrelevant(cs: Seq<char>, c: char, i: nat)
    requires
        i as int <= cs.len(),
    ensures
        spec_encode_upto(cs.push(c), i as int)
            == spec_encode_upto(cs, i as int),
    decreases i,
{
    if i == 0 {
    } else {
        assert(cs.push(c).len() == cs.len() + 1);
        assert(cs.push(c).index((i - 1) as int) == cs.index((i - 1) as int));
        lemma_enc_upto_irrelevant(cs, c, (i - 1) as nat);
        lemma_enc_push_step(cs.push(c), (i - 1) as int);
        lemma_enc_push_step(cs, (i - 1) as int);
    }
}

/// The whole-sequence push homomorphism (probe p_enc).
pub proof fn lemma_enc_push_whole(cs: Seq<char>, c: char)
    ensures
        spec_encode(cs.push(c)) == spec_encode(cs).add(spec_enc_char(c)),
{
    lemma_enc_upto_irrelevant(cs, c, cs.len() as nat);
    assert(cs.push(c).index(cs.len() as int) == c);
    assert(spec_encode_upto(cs.push(c), (cs.len() + 1) as int)
        == spec_encode_upto(cs.push(c), cs.len() as int).add(spec_enc_char(c)));
}

/// The ASCII lane: the one-byte table arm (probe p_enc).
pub proof fn lemma_enc_ascii(c: char)
    requires
        glob::spec_is_ascii(c),
    ensures
        spec_enc_char(c) == seq![(c as u32) as u8],
{
}

/// The exec encoder (the fan-out arm's into_bytes twin; probe
/// p_enc's loop shape, byte-carry via the per-char piece fn).
pub fn utf8_encode_chars(cs: &[char]) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode(cs@),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < cs.len()
        invariant
            i <= cs.len(),
            cs@.len() == cs.len(),
            out@ == spec_encode_upto(cs@, i as int),
        decreases cs.len() - i,
    {
        let piece = glob::utf8_bytes_exec(cs[i]);
        let px: &[u8] = piece.as_slice();
        let mut j: usize = 0;
        while j < px.len()
            invariant
                j <= px.len(),
                px@.len() == px.len(),
                px@ == piece@,
                out@ == spec_encode_upto(cs@, i as int).add(px@.subrange(0, j as int)),
            decreases px.len() - j,
        {
            out.push(px[j]);
            j += 1;
        }
        proof {
            assert(px@.subrange(0, px.len() as int) == px@);
            assert(px@ == spec_enc_char(cs@.index(i as int)));
            lemma_enc_push_step(cs@, i as int);
        }
        i += 1;
    }
    proof {
        assert(spec_encode_upto(cs@, cs.len() as int) == spec_encode(cs@));
    }
    out
}

// ---------------------------------------------------------------------------
// Part B: the AC prefix/suffix consumption twins (lib.rs:824-912; the
// filtered occurrence set under the trusted contract face, verified
// as the per-pattern byte relation -- SubStrategyProof evidence in
// probe p_scan).
// ---------------------------------------------------------------------------

/// Pattern q's literal occurs at window position 0 (the m.start()==0
/// filtered occurrence). The subrange term is guarded by the length
/// conjunct: spec calls are well-formedness-checked at every call
/// site, and an unguarded subrange beyond the window would violate
/// Seq::subrange's requires even on the false path (probe p_scan
/// ruling; no redundant `as int` casts on Seq::len(), which is nat,
/// casts live only at subrange argument positions).
pub open spec fn spec_pre_hit(lits: Seq<Vec<u8>>, w: Seq<u8>, q: int) -> bool {
    0 <= q < lits.len()
        && ({
            if lits.index(q)@.len() > w.len() {
                false
            } else {
                w.subrange(0, lits.index(q)@.len() as int) == lits.index(q)@
            }
        })
}

/// is_match (lib.rs:832-840's filtered-any).
pub open spec fn spec_pre_is_match(lits: Seq<Vec<u8>>, w: Seq<u8>) -> bool {
    exists|q: int| spec_pre_hit(lits, w, q)
}

/// The hit count among the first n patterns (the matches_all count,
/// lib.rs:842-853's count == map.len() gate).
pub open spec fn spec_pre_count_upto(lits: Seq<Vec<u8>>, w: Seq<u8>, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        (if spec_pre_hit(lits, w, n - 1) { 1int } else { 0int })
            + spec_pre_count_upto(lits, w, n - 1)
    }
}

pub open spec fn spec_pre_count(lits: Seq<Vec<u8>>, w: Seq<u8>) -> int {
    spec_pre_count_upto(lits, w, lits.len() as int)
}

/// The ordered matches_into list (push map[q] per hitting q, in
/// positional pattern-id order -- the contract's iteration order).
pub open spec fn spec_pre_hits_upto(
    lits: Seq<Vec<u8>>,
    map: Seq<usize>,
    w: Seq<u8>,
    n: int,
) -> Seq<usize>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        let base = spec_pre_hits_upto(lits, map, w, n - 1);
        if spec_pre_hit(lits, w, n - 1) {
            base.push(map.index(n - 1))
        } else {
            base
        }
    }
}

pub open spec fn spec_pre_hits(lits: Seq<Vec<u8>>, map: Seq<usize>, w: Seq<u8>) -> Seq<usize> {
    spec_pre_hits_upto(lits, map, w, lits.len() as int)
}

/// count == n means every one of the first n patterns hits (GM16's
/// count-each reasoning; probe p_scan).
pub proof fn lemma_pre_count_all(lits: Seq<Vec<u8>>, w: Seq<u8>, n: int)
    requires
        0 <= n <= lits.len(),
    ensures
        spec_pre_count_upto(lits, w, n) == n
            ==> (forall|q: int| 0 <= q < n ==> spec_pre_hit(lits, w, q)),
    decreases n,
{
    if n > 0 {
        let rest = spec_pre_count_upto(lits, w, n - 1);
        assert(spec_pre_count_upto(lits, w, n)
            == (if spec_pre_hit(lits, w, n - 1) { 1int } else { 0int }) + rest);
        lemma_pre_count_bound(lits, w, n - 1);
        if spec_pre_count_upto(lits, w, n) == n {
            assert(rest == n - 1);
            assert(spec_pre_hit(lits, w, n - 1));
            lemma_pre_count_all(lits, w, n - 1);
        }
    }
}

/// The count never exceeds the cell count (probe p_scan).
pub proof fn lemma_pre_count_bound(lits: Seq<Vec<u8>>, w: Seq<u8>, n: int)
    ensures
        0 <= n ==> spec_pre_count_upto(lits, w, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_pre_count_bound(lits, w, n - 1);
    }
}

/// count > 0 means some pattern hits (probe p_scan).
pub proof fn lemma_pre_count_pos(lits: Seq<Vec<u8>>, w: Seq<u8>, n: int)
    requires
        0 <= n <= lits.len(),
    ensures
        spec_pre_count_upto(lits, w, n) > 0
            ==> exists|q: int| 0 <= q < n && spec_pre_hit(lits, w, q),
    decreases n,
{
    if n > 0 {
        if spec_pre_count_upto(lits, w, n) > 0 {
            if spec_pre_hit(lits, w, n - 1) {
            } else {
                lemma_pre_count_pos(lits, w, n - 1);
            }
        }
    }
}

/// Compare w[0..lq.len()] against lq (the m.start()==0 occurrence;
/// the guard form's twin; probe p_scan).
pub fn window_starts_with(w: &[u8], lq: &Vec<u8>) -> (r: bool)
    ensures
        r <==>({
            if lq@.len() > w@.len() {
                false
            } else {
                w@.subrange(0, lq@.len() as int) == lq@
            }
        }),
{
    if lq.len() > w.len() {
        proof {
            assert(lq@.len() == lq.len());
            assert(w@.len() == w.len());
        }
        // the guarded-else spec form picks its false branch
        return false;
    }
    let mut k: usize = 0;
    let mut eq: bool = true;
    let mut mism: usize = 0;
    while k < lq.len()
        invariant
            k <= lq.len(),
            lq.len() <= w.len(),
            lq@.len() == lq.len(),
            w@.len() == w.len(),
            eq ==> forall|t: int| 0 <= t < k ==> w@.index(t) == lq@.index(t),
            !eq ==> (mism < k && w@.index(mism as int) != lq@.index(mism as int)),
        decreases lq.len() - k,
    {
        if w[k] != lq[k] {
            proof {
                assert(w@.index(k as int) != lq@.index(k as int));
            }
            eq = false;
            mism = k;
        } else {
            proof {
                assert(w@.index(k as int) == lq@.index(k as int));
            }
        }
        k += 1;
    }
    proof {
        if eq {
            assert forall|t: int| 0 <= t < lq@.len() as int implies
                w@.subrange(0, lq@.len() as int).index(t) == lq@.index(t) by {
                assert(w@.subrange(0, lq@.len() as int).index(t) == w@.index(t));
            }
            ext_equal(w@.subrange(0, lq@.len() as int), lq@);
            assert(w@.subrange(0, lq@.len() as int) == lq@);
        } else {
            assert(w@.subrange(0, lq@.len() as int).index(mism as int) == w@.index(mism as int));
            assert(w@.subrange(0, lq@.len() as int).index(mism as int) != lq@.index(mism as int));
            assert(w@.subrange(0, lq@.len() as int) != lq@);
        }
    }
    eq
}

/// The m.end()==len filtered occurrence (pattern q's literal occurs
/// ending at the window end; the suffix tier's pane).
pub open spec fn spec_suf_hit(lits: Seq<Vec<u8>>, w: Seq<u8>, q: int) -> bool {
    0 <= q < lits.len()
        && ({
            if lits.index(q)@.len() > w.len() {
                false
            } else {
                w.subrange(
                    w.len() as int - lits.index(q)@.len() as int,
                    w.len() as int,
                ) == lits.index(q)@
            }
        })
}

pub open spec fn spec_suf_is_match(lits: Seq<Vec<u8>>, w: Seq<u8>) -> bool {
    exists|q: int| spec_suf_hit(lits, w, q)
}

pub open spec fn spec_suf_count_upto(lits: Seq<Vec<u8>>, w: Seq<u8>, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        (if spec_suf_hit(lits, w, n - 1) { 1int } else { 0int })
            + spec_suf_count_upto(lits, w, n - 1)
    }
}

pub open spec fn spec_suf_count(lits: Seq<Vec<u8>>, w: Seq<u8>) -> int {
    spec_suf_count_upto(lits, w, lits.len() as int)
}

pub open spec fn spec_suf_hits_upto(
    lits: Seq<Vec<u8>>,
    map: Seq<usize>,
    w: Seq<u8>,
    n: int,
) -> Seq<usize>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        let base = spec_suf_hits_upto(lits, map, w, n - 1);
        if spec_suf_hit(lits, w, n - 1) {
            base.push(map.index(n - 1))
        } else {
            base
        }
    }
}

pub open spec fn spec_suf_hits(lits: Seq<Vec<u8>>, map: Seq<usize>, w: Seq<u8>) -> Seq<usize> {
    spec_suf_hits_upto(lits, map, w, lits.len() as int)
}

/// The suffix side of the count lemmas (mirroring the prefix pair).
pub proof fn lemma_suf_count_bound(lits: Seq<Vec<u8>>, w: Seq<u8>, n: int)
    ensures
        0 <= n ==> spec_suf_count_upto(lits, w, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_suf_count_bound(lits, w, n - 1);
    }
}

pub proof fn lemma_suf_count_all(lits: Seq<Vec<u8>>, w: Seq<u8>, n: int)
    requires
        0 <= n <= lits.len(),
    ensures
        spec_suf_count_upto(lits, w, n) == n
            ==> (forall|q: int| 0 <= q < n ==> spec_suf_hit(lits, w, q)),
    decreases n,
{
    if n > 0 {
        let rest = spec_suf_count_upto(lits, w, n - 1);
        assert(spec_suf_count_upto(lits, w, n)
            == (if spec_suf_hit(lits, w, n - 1) { 1int } else { 0int }) + rest);
        lemma_suf_count_bound(lits, w, n - 1);
        if spec_suf_count_upto(lits, w, n) == n {
            assert(rest == n - 1);
            assert(spec_suf_hit(lits, w, n - 1));
            lemma_suf_count_all(lits, w, n - 1);
        }
    }
}

/// Compare w[w.len()-lq.len()..] against lq (the m.end()==len pane).
pub fn window_ends_with(w: &[u8], lq: &Vec<u8>) -> (r: bool)
    ensures
        r <==>({
            if lq@.len() > w@.len() {
                false
            } else {
                w@.subrange(w@.len() as int - lq@.len() as int, w@.len() as int) == lq@
            }
        }),
{
    if lq.len() > w.len() {
        proof {
            assert(lq@.len() == lq.len());
            assert(w@.len() == w.len());
        }
        return false;
    }
    let start: usize = w.len() - lq.len();
    let mut k: usize = 0;
    let mut eq: bool = true;
    let mut mism: usize = 0;
    while k < lq.len()
        invariant
            k <= lq.len(),
            lq.len() <= w.len(),
            start == w.len() - lq.len(),
            lq@.len() == lq.len(),
            w@.len() == w.len(),
            eq ==> forall|t: int| 0 <= t < k ==>
                w@.index(start as int + t) == lq@.index(t),
            !eq ==> (mism < k && w@.index(start as int + mism as int) != lq@.index(mism as int)),
        decreases lq.len() - k,
    {
        if w[start + k] != lq[k] {
            proof {
                assert(w@.index(start as int + k as int) != lq@.index(k as int));
            }
            eq = false;
            mism = k;
        } else {
            proof {
                assert(w@.index(start as int + k as int) == lq@.index(k as int));
            }
        }
        k += 1;
    }
    proof {
        let lo = w@.len() as int - lq@.len() as int;
        assert forall|t: int| 0 <= t < lq@.len() implies
            w@.subrange(lo, w@.len() as int).index(t) == w@.index(lo + t) by {
        }
        if eq {
            assert(w@.subrange(lo, w@.len() as int) == lq@);
        } else {
            assert(w@.subrange(lo, w@.len() as int).index(mism as int)
                == w@.index(lo + mism as int));
            assert(w@.subrange(lo, w@.len() as int) != lq@);
        }
    }
    eq
}

// ---------------------------------------------------------------------------
// Part C: the regex oracle face (inventory contract face (a), the
// one uninterpreted predicate of this batch; the KAT axioms that pin
// it per vector ride the harnesses, and the origin table records it
// as trusted content with its upstream anchor).
// ---------------------------------------------------------------------------

/// Whether the regex compiled from the (already synthesized) regex
/// string re matches the haystack bytes. Trusted face: upstream
/// compiles via new_regex/new_regex_set (lib.rs:271-304, trusted
/// entry points; Error::Regex mapping is their only verified
/// content per the inventory's disposition) and evaluates over
/// regex-automata; the twin stores the string and queries this
/// predicate, never compiling (the GL5 strategic-model weld carried
/// the token-side faithfulness, GM10's oracle-assertion domain).
pub uninterp spec fn spec_regex_hits(re: Seq<char>, hay: Seq<u8>) -> bool;

// ---------------------------------------------------------------------------
// Part D: the scan membership family (the sort+dedup twin's substrate;
// probe p_canon2's parked-proven pieces).
// ---------------------------------------------------------------------------

/// Membership, scan form (the exists form admits no witness
/// extraction in proof fns; the GL6 spec_map_hits lesson holds over
/// Seq<usize>).
pub open spec fn spec_has_scan(s: Seq<usize>, x: int, n: int) -> bool
    decreases n
{
    if n <= 0 {
        false
    } else if n > s.len() as int {
        // out-of-range heads never contribute
        false
    } else if s.index(n - 1) == x {
        true
    } else {
        spec_has_scan(s, x, n - 1)
    }
}

/// Full-bag membership.
pub open spec fn spec_bag_has(s: Seq<usize>, x: int) -> bool {
    spec_has_scan(s, x, s.len() as int)
}

/// The one-step hit (the cell at k plus the budget up to k+1).
pub proof fn lemma_scan_step_hit(s: Seq<usize>, x: int, k: int)
    requires
        0 <= k < s.len() as int,
        s.index(k) == x,
    ensures
        spec_has_scan(s, x, k + 1),
{
}

/// The one-step miss (the budget step over a non-matching cell).
pub proof fn lemma_scan_step_miss(s: Seq<usize>, x: int, n: int)
    requires
        1 <= n <= s.len() as int,
        s.index(n - 1) != x,
    ensures
        spec_has_scan(s, x, n) == spec_has_scan(s, x, n - 1),
{
}

/// A scan miss at budget n means every cell below n misses.
pub proof fn lemma_scan_miss_cell(s: Seq<usize>, x: int, n: int, k: int)
    requires
        0 <= k < n,
        n <= s.len() as int,
        !spec_has_scan(s, x, n),
    ensures
        s.index(k) != x,
    decreases n,
{
    if k == n - 1 {
        assert(s.index(n - 1) != x);
    } else {
        assert(k < n - 1);
        assert(s.index(n - 1) != x);
        assert(spec_has_scan(s, x, n) == (spec_has_scan(s, x, n - 1)));
        assert(!spec_has_scan(s, x, n - 1));
        lemma_scan_miss_cell(s, x, n - 1, k);
    }
}

/// A hit budget grows to any larger budget.
pub proof fn lemma_scan_hit_grows(s: Seq<usize>, x: int, n: int, m: int)
    requires
        0 <= n <= m <= s.len() as int,
        spec_has_scan(s, x, n),
    ensures
        spec_has_scan(s, x, m),
    decreases m - n,
{
    if n < m {
        lemma_scan_hit_grows(s, x, n, m - 1);
        assert(1 <= m <= s.len() as int);
        if s.index(m - 1) == x {
            lemma_scan_step_hit(s, x, m - 1);
        } else {
            lemma_scan_step_miss(s, x, m);
        }
    }
}

/// No matching cell in the first n: the scan is false.
pub proof fn lemma_scan_all_miss(s: Seq<usize>, x: int, n: int)
    requires
        0 <= n <= s.len() as int,
        forall|k: int| 0 <= k < n ==> s.index(k) != x,
    ensures
        !spec_has_scan(s, x, n),
    decreases n,
{
    if n > 0 {
        assert(s.index(n - 1) != x);
        lemma_scan_step_miss(s, x, n);
        lemma_scan_all_miss(s, x, n - 1);
    }
}

// ---------------------------------------------------------------------------
// Part E: MultiStrategyBuilder + the Prefix/Suffix strategies
// (lib.rs:824-912 + 1032-1084; the automaton twin carries the same
// three columns upstream builds -- literals, map, longest -- and the
// scan twin consumes them per pattern id).
// ---------------------------------------------------------------------------

/// Origin Rust (lib.rs:1032-1037):
///     struct MultiStrategyBuilder {
///         literals: Vec<String>, map: Vec<usize>, longest: usize,
///     }
/// (literals' String payloads arrive here already as their byte
/// columns; the twin stores Vec<u8> and never re-encodes)
pub struct MultiStrategyBuilder {
    pub literals: Vec<Vec<u8>>,
    pub map: Vec<usize>,
    pub longest: usize,
}

impl MultiStrategyBuilder {
    /// Origin Rust (lib.rs:1040-1041):
    ///     fn new() -> MultiStrategyBuilder {
    ///         MultiStrategyBuilder { literals: vec![], map: vec![], longest: 0 }
    ///     }
    pub fn new() -> (r: MultiStrategyBuilder)
        ensures
            r.literals@ == Seq::empty(),
            r.map@ == Seq::empty(),
            r.longest == 0,
    {
        MultiStrategyBuilder { literals: Vec::new(), map: Vec::new(), longest: 0 }
    }

    /// Origin Rust (lib.rs:1044-1050):
    ///     fn add(&mut self, global_index: usize, literal: String) {
    ///         if literal.len() > self.longest { self.longest = literal.len(); }
    ///         self.map.push(global_index);
    ///         self.literals.push(literal);
    ///     }
    pub fn add(&mut self, global_index: usize, literal: Vec<u8>)
        ensures
            final(self).literals@.len() == old(self).literals@.len() + 1,
            final(self).literals@.subrange(0, old(self).literals@.len() as int)
                == old(self).literals@,
            final(self).literals@.index(old(self).literals@.len() as int)@ == literal@,
            final(self).map@ == old(self).map@.push(global_index),
            final(self).map@.len() == old(self).map@.len() + 1,
            final(self).longest
                == (if literal.len() > old(self).longest { literal.len() } else { old(self).longest }),
    {
        if literal.len() > self.longest {
            self.longest = literal.len();
        }
        self.map.push(global_index);
        self.literals.push(literal);
    }

    /// Origin Rust (lib.rs:1052-1058):
    ///     fn prefix(self) -> PrefixStrategy {
    ///         PrefixStrategy { matcher: AhoCorasick::new(&self.literals).unwrap(),
    ///                        map: self.map, longest: self.longest }
    ///     }
    /// (the automaton construction is the trusted face; the twin
    ///  keeps the literal column itself -- the contract's
    ///  positional pattern ids are the column indexes)
    pub fn prefix(self) -> (r: PrefixStrategy)
        ensures
            r.lits@ == self.literals@,
            r.map@ == self.map@,
            r.longest == self.longest,
    {
        PrefixStrategy { lits: self.literals, map: self.map, longest: self.longest }
    }

    /// Origin Rust (lib.rs:1060-1066): the suffix variant of the
    /// same constructor body.
    pub fn suffix(self) -> (r: SuffixStrategy)
        ensures
            r.lits@ == self.literals@,
            r.map@ == self.map@,
            r.longest == self.longest,
    {
        SuffixStrategy { lits: self.literals, map: self.map, longest: self.longest }
    }

    /// Origin Rust (lib.rs:1081-1083):
    ///     fn is_empty(&self) -> bool { self.literals.is_empty() }
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r <==> self.literals@.len() == 0,
    {
        self.literals.len() == 0
    }
}

// ---------------------------------------------------------------------------
// PrefixStrategy (lib.rs:824-867; the scan twin under the AC
// contract: the m.start()==0 filtered occurrence of pattern q is
// exactly "lits[q] is a byte prefix of the window").
// ---------------------------------------------------------------------------

pub struct PrefixStrategy {
    /// Origin column (lib.rs:826 + 833): the automaton's literal set
    /// and the window cap; the twin keeps the literals themselves.
    pub lits: Vec<Vec<u8>>,
    pub map: Vec<usize>,
    pub longest: usize,
}

impl PrefixStrategy {
    /// Origin Rust (lib.rs:832-840):
    ///     fn is_match(&self, candidate: &Candidate<'_>) -> bool {
    ///         let path = candidate.path_prefix(self.longest);
    ///         for m in self.matcher.find_overlapping_iter(path) {
    ///             if m.start() == 0 { return true; }
    ///         }
    ///         false
    ///     }
    pub fn is_match(&self, cand: &Candidate) -> (r: bool)
        requires
            self.map.len() == self.lits.len(),
        ensures
            r == spec_pre_is_match(
                self.lits@,
                spec_window(cand.path.view(), self.longest as int, false),
            ),
    {
        let w: &[u8] = cand.path_prefix(self.longest);
        proof {
            assert(w@ == spec_window(cand.path.view(), self.longest as int, false));
        }
        let mut q: usize = 0;
        let mut hit: bool = false;
        let mut hitq: usize = 0;
        while !hit && q < self.lits.len()
            invariant
                q <= self.lits.len(),
                self.lits@.len() == self.lits.len(),
                w@.len() == w.len(),
                hit ==> (hitq <= q && spec_pre_hit(self.lits@, w@, hitq as int)),
                !hit ==> forall|t: int| 0 <= t < q ==> !spec_pre_hit(self.lits@, w@, t),
            decreases (if hit { 0int } else { 1int }), self.lits.len() - q,
        {
            let lq: &Vec<u8> = &self.lits[q];
            if window_starts_with(w, lq) {
                proof {
                    assert(lq@ == self.lits@.index(q as int)@);
                    assert(spec_pre_hit(self.lits@, w@, q as int));
                }
                hit = true;
                hitq = q;
            } else {
                q += 1;
            }
        }
        proof {
            if hit {
                assert(spec_pre_is_match(self.lits@, w@));
            } else {
                assert(q == self.lits.len()) by {
                    assert(q >= self.lits.len());
                }
                assert forall|q2: int| 0 <= q2 < self.lits@.len() implies
                    !spec_pre_hit(self.lits@, w@, q2) by {
                    assert(q2 < q as int);
                }
                assert(!spec_pre_is_match(self.lits@, w@));
            }
        }
        hit
    }

    /// Origin Rust (lib.rs:842-853): the count-each matches_all.
    pub fn matches_all(&self, cand: &Candidate) -> (r: bool)
        requires
            self.map.len() == self.lits.len(),
        ensures
            r <==> (spec_pre_count(
                self.lits@,
                spec_window(cand.path.view(), self.longest as int, false),
            ) == self.map@.len() as int),
    {
        let w: &[u8] = cand.path_prefix(self.longest);
        proof {
            assert(w@ == spec_window(cand.path.view(), self.longest as int, false));
        }
        let mut q: usize = 0;
        let mut count: usize = 0;
        while q < self.lits.len()
            invariant
                q <= self.lits.len(),
                self.lits@.len() == self.lits.len(),
                w@.len() == w.len(),
                count as int == spec_pre_count_upto(self.lits@, w@, q as int),
                count <= q,
            decreases self.lits.len() - q,
        {
            let lq: &Vec<u8> = &self.lits[q];
            if window_starts_with(w, lq) {
                proof {
                    assert(lq@ == self.lits@.index(q as int)@);
                    assert(spec_pre_hit(self.lits@, w@, q as int));
                }
                count += 1;
            }
            q += 1;
        }
        proof {
            assert(count as int == spec_pre_count(self.lits@, w@));
        }
        count == self.map.len()
    }

    /// Origin Rust (lib.rs:855-866): push map[q] per hitting q.
    pub fn matches_into(&self, cand: &Candidate, matches: &mut Vec<usize>)
        requires
            self.map.len() == self.lits.len(),
        ensures
            final(matches)@ == old(matches)@.add(spec_pre_hits(
                self.lits@,
                self.map@,
                spec_window(cand.path.view(), self.longest as int, false),
            )),
    {
        let w: &[u8] = cand.path_prefix(self.longest);
        proof {
            assert(w@ == spec_window(cand.path.view(), self.longest as int, false));
        }
        let mut q: usize = 0;
        while q < self.lits.len()
            invariant
                q <= self.lits.len(),
                self.lits@.len() == self.lits.len(),
                self.map.len() == self.lits.len(),
                self.map@.len() == self.map.len(),
                w@.len() == w.len(),
                matches@ == old(matches)@.add(spec_pre_hits_upto(
                    self.lits@,
                    self.map@,
                    w@,
                    q as int,
                )),
            decreases self.lits.len() - q,
        {
            let lq: &Vec<u8> = &self.lits[q];
            let gq: usize = self.map[q];
            if window_starts_with(w, lq) {
                proof {
                    assert(lq@ == self.lits@.index(q as int)@);
                    assert(self.map@.index(q as int) == gq);
                    assert(spec_pre_hit(self.lits@, w@, q as int));
                    assert(spec_pre_hits_upto(self.lits@, self.map@, w@, (q + 1) as int)
                        == spec_pre_hits_upto(self.lits@, self.map@, w@, q as int)
                            .push(gq));
                }
                matches.push(gq);
            } else {
                proof {
                    assert(!spec_pre_hit(self.lits@, w@, q as int));
                    assert(spec_pre_hits_upto(self.lits@, self.map@, w@, (q + 1) as int)
                        == spec_pre_hits_upto(self.lits@, self.map@, w@, q as int));
                }
            }
            q += 1;
        }
        proof {
            assert(spec_pre_hits_upto(self.lits@, self.map@, w@, self.lits.len() as int)
                == spec_pre_hits(self.lits@, self.map@, w@));
        }
    }
}

// ---------------------------------------------------------------------------
// SuffixStrategy (lib.rs:869-912; the m.end()==len pane twin).
// ---------------------------------------------------------------------------

pub struct SuffixStrategy {
    pub lits: Vec<Vec<u8>>,
    pub map: Vec<usize>,
    pub longest: usize,
}

impl SuffixStrategy {
    /// Origin Rust (lib.rs:877-885): the suffix-any query.
    pub fn is_match(&self, cand: &Candidate) -> (r: bool)
        requires
            self.map.len() == self.lits.len(),
        ensures
            r == spec_suf_is_match(
                self.lits@,
                spec_window(cand.path.view(), self.longest as int, true),
            ),
    {
        let w: &[u8] = cand.path_suffix(self.longest);
        proof {
            assert(w@ == spec_window(cand.path.view(), self.longest as int, true));
        }
        let mut q: usize = 0;
        let mut hit: bool = false;
        let mut hitq: usize = 0;
        while !hit && q < self.lits.len()
            invariant
                q <= self.lits.len(),
                self.lits@.len() == self.lits.len(),
                w@.len() == w.len(),
                hit ==> (hitq <= q && spec_suf_hit(self.lits@, w@, hitq as int)),
                !hit ==> forall|t: int| 0 <= t < q ==> !spec_suf_hit(self.lits@, w@, t),
            decreases (if hit { 0int } else { 1int }), self.lits.len() - q,
        {
            let lq: &Vec<u8> = &self.lits[q];
            if window_ends_with(w, lq) {
                proof {
                    assert(lq@ == self.lits@.index(q as int)@);
                    assert(spec_suf_hit(self.lits@, w@, q as int));
                }
                hit = true;
                hitq = q;
            } else {
                q += 1;
            }
        }
        proof {
            if hit {
                assert(spec_suf_is_match(self.lits@, w@));
            } else {
                assert(q == self.lits.len()) by {
                    assert(q >= self.lits.len());
                }
                assert forall|q2: int| 0 <= q2 < self.lits@.len() implies
                    !spec_suf_hit(self.lits@, w@, q2) by {
                    assert(q2 < q as int);
                }
                assert(!spec_suf_is_match(self.lits@, w@));
            }
        }
        hit
    }

    /// Origin Rust (lib.rs:887-898): the count-each matches_all.
    pub fn matches_all(&self, cand: &Candidate) -> (r: bool)
        requires
            self.map.len() == self.lits.len(),
        ensures
            r <==> (spec_suf_count(
                self.lits@,
                spec_window(cand.path.view(), self.longest as int, true),
            ) == self.map@.len() as int),
    {
        let w: &[u8] = cand.path_suffix(self.longest);
        proof {
            assert(w@ == spec_window(cand.path.view(), self.longest as int, true));
        }
        let mut q: usize = 0;
        let mut count: usize = 0;
        while q < self.lits.len()
            invariant
                q <= self.lits.len(),
                self.lits@.len() == self.lits.len(),
                w@.len() == w.len(),
                count as int == spec_suf_count_upto(self.lits@, w@, q as int),
                count <= q,
            decreases self.lits.len() - q,
        {
            let lq: &Vec<u8> = &self.lits[q];
            if window_ends_with(w, lq) {
                proof {
                    assert(lq@ == self.lits@.index(q as int)@);
                    assert(spec_suf_hit(self.lits@, w@, q as int));
                }
                count += 1;
            }
            q += 1;
        }
        proof {
            assert(count as int == spec_suf_count(self.lits@, w@));
        }
        count == self.map.len()
    }

    /// Origin Rust (lib.rs:900-911): push map[q] per hitting q.
    pub fn matches_into(&self, cand: &Candidate, matches: &mut Vec<usize>)
        requires
            self.map.len() == self.lits.len(),
        ensures
            final(matches)@ == old(matches)@.add(spec_suf_hits(
                self.lits@,
                self.map@,
                spec_window(cand.path.view(), self.longest as int, true),
            )),
    {
        let w: &[u8] = cand.path_suffix(self.longest);
        proof {
            assert(w@ == spec_window(cand.path.view(), self.longest as int, true));
        }
        let mut q: usize = 0;
        while q < self.lits.len()
            invariant
                q <= self.lits.len(),
                self.lits@.len() == self.lits.len(),
                self.map.len() == self.lits.len(),
                self.map@.len() == self.map.len(),
                w@.len() == w.len(),
                matches@ == old(matches)@.add(spec_suf_hits_upto(
                    self.lits@,
                    self.map@,
                    w@,
                    q as int,
                )),
            decreases self.lits.len() - q,
        {
            let lq: &Vec<u8> = &self.lits[q];
            let gq: usize = self.map[q];
            if window_ends_with(w, lq) {
                proof {
                    assert(lq@ == self.lits@.index(q as int)@);
                    assert(self.map@.index(q as int) == gq);
                    assert(spec_suf_hit(self.lits@, w@, q as int));
                    assert(spec_suf_hits_upto(self.lits@, self.map@, w@, (q + 1) as int)
                        == spec_suf_hits_upto(self.lits@, self.map@, w@, q as int)
                            .push(gq));
                }
                matches.push(gq);
            } else {
                proof {
                    assert(!spec_suf_hit(self.lits@, w@, q as int));
                    assert(spec_suf_hits_upto(self.lits@, self.map@, w@, (q + 1) as int)
                        == spec_suf_hits_upto(self.lits@, self.map@, w@, q as int));
                }
            }
            q += 1;
        }
        proof {
            assert(spec_suf_hits_upto(self.lits@, self.map@, w@, self.lits.len() as int)
                == spec_suf_hits(self.lits@, self.map@, w@));
        }
    }
}

// ---------------------------------------------------------------------------
// Part F: the push-preservation family (the canonicalization walk's
// substrate; the p_canon/p_canon2 parked-proven pieces restated at
// lib level).
// ---------------------------------------------------------------------------

/// The scan over a pushed sequence agrees with the old scan on every
/// prefix budget (every looked-at cell lies in the shared prefix).
pub proof fn lemma_scan_push_irrelevant(s: Seq<usize>, t: usize, x: int, n: int)
    requires
        0 <= n <= s.len() as int,
    ensures
        spec_has_scan(s.push(t), x, n) <==> spec_has_scan(s, x, n),
    decreases n,
{
    if n > 0 {
        assert(s.push(t).len() == s.len() + 1);
        assert((s.len() as int) < (s.push(t).len() as int));
    assert(n <= s.len() as int);
    assert(n <= s.push(t).len() as int);
        assert(s.push(t).index(n - 1) == s.index(n - 1));
        lemma_scan_push_irrelevant(s, t, x, n - 1);
    }
}

/// Pushing a non-matching domain value keeps full-bag membership.
pub proof fn lemma_push_preserves_miss(s: Seq<usize>, t: usize, x: int)
    requires
        x != t as int,
    ensures
        spec_bag_has(s.push(t), x) <==> spec_bag_has(s, x),
{
    assert(s.push(t).len() == s.len() + 1);
    assert(s.push(t).index(s.len() as int) == t);
    assert(s.push(t).index(s.len() as int) != x);
    assert(spec_has_scan(s.push(t), x, s.push(t).len() as int)
        == spec_has_scan(s.push(t), x, s.len() as int));
    lemma_scan_push_irrelevant(s, t, x, s.len() as int);
    assert(spec_has_scan(s.push(t), x, s.len() as int)
        <==> spec_has_scan(s, x, s.len() as int));
}

/// The neighbor pair check (trigger carrier for the ascending
/// quantifier; two bare s.index terms defeat trigger inference).
pub open spec fn spec_lt_at(s: Seq<usize>, k: int) -> bool {
    s.index(k) < s.index(k + 1)
}

/// Strictly ascending (the sort+dedup output shape). The neighbor
/// pairs live strictly inside the view (k+1 <= len-1; the
/// off-by-one band k+1 <= len admits an out-of-range pair and
/// poisons every downstream fold -- probe p_canon2's ruling).
pub open spec fn spec_ascending(s: Seq<usize>) -> bool {
    forall|k: int| 1 <= k + 1 <= s.len() - 1 ==> spec_lt_at(s, k)
}

/// Pushing a domain value above the whole tail keeps the ascending
/// shape (probe-proven; note vstd's naming trap: push_index_SAME is
/// the pushed head, requiring i == len; push_index_DIFFERENT carries
/// the prefix, requiring i < len).
pub proof fn lemma_push_ascending(pre: Seq<usize>, v: usize)
    requires
        spec_ascending(pre),
        forall|k: int| 0 <= k < pre.len() as int ==> pre.index(k) < v,
    ensures
        spec_ascending(pre.push(v)),
{
    let post = pre.push(v);
    assert(post.len() == pre.len() + 1);
    assert forall|k: int| 1 <= k + 1 <= post.len() - 1 implies
        spec_lt_at(post, k) by {
        if k + 1 <= pre.len() - 1 {
            // interior pair: both cells shared with the prefix
            assert(k + 1 <= pre.len() - 1);
            assert(k < pre.len() as int);
            assert(post.index(k) == pre.index(k));
            assert(post.index(k + 1) == pre.index(k + 1));
            assert(spec_lt_at(pre, k));
        } else {
            // tail pair: the old top against the pushed cell
            assert(k + 1 == pre.len());
            assert(k < pre.len() as int);
            assert(post.index(k) == pre.index(k));
            assert(post.index(k + 1) == v);
            assert(pre.index(k) < v);
        }
        assert(spec_lt_at(post, k));
    }
}

/// The push-add flatten law (entry.push(v).add(rest) == entry.add(
/// seq![v].add(rest)); per-index via the vstd add/push lemma pair).
pub proof fn lemma_push_add_flatten(entry: Seq<usize>, v: usize, rest: Seq<usize>)
    ensures
        entry.push(v).add(rest) == entry.add(seq![v].add(rest)),
{
    let lhs = entry.push(v).add(rest);
    let rhs = entry.add(seq![v].add(rest));
    vstd::seq::lemma_seq_push_len(entry, v);
    vstd::seq::lemma_seq_add_len(entry.push(v), rest);
    vstd::seq::lemma_seq_add_len(seq![v], rest);
    vstd::seq::lemma_seq_add_len(entry, seq![v].add(rest));
    assert(seq![v].len() == 1);
    assert(lhs.len() == entry.len() + 1 + rest.len());
    assert(rhs.len() == entry.len() + 1 + rest.len());
    assert forall|i: int|
        #![trigger lhs.index(i)]
        0 <= i < lhs.len() implies lhs.index(i) == rhs.index(i) by {
        if i < entry.len() {
            assert(0 <= i < entry.len());
            vstd::seq::lemma_seq_add_index1(entry.push(v), rest, i);
            // different carries the prefix (i < entry.len())
            vstd::seq::lemma_seq_push_index_different(entry, v, i);
            vstd::seq::lemma_seq_add_index1(entry, seq![v].add(rest), i);
            assert(lhs.index(i) == entry.index(i));
            assert(rhs.index(i) == entry.index(i));
        } else {
            assert(i >= entry.len());
            assert(i < lhs.len());
            assert(entry.len() <= i < entry.len() + 1 + rest.len());
            vstd::seq::lemma_seq_add_len(entry.push(v), rest);
            assert(entry.push(v).len() as int == entry.len() + 1);
            if i < entry.len() + 1 {
                // the pushed-head boundary cell
                assert(i == entry.len());
                assert(i < entry.push(v).len());
                vstd::seq::lemma_seq_add_index1(entry.push(v), rest, i);
                vstd::seq::lemma_seq_push_index_same(entry, v, entry.len() as int);
                assert(lhs.index(i) == v);
                let rhsinner = seq![v].add(rest);
                assert(rhsinner.len() == 1 + rest.len());
                vstd::seq::lemma_seq_add_index2(entry, rhsinner, i);
                assert(rhs.index(i) == rhsinner.index(i - entry.len()));
                assert(rhsinner.index(0) == v);
            } else {
                vstd::seq::lemma_seq_add_index2(entry.push(v), rest, i);
                vstd::seq::lemma_seq_add_index2(entry, seq![v].add(rest), i);
                let rhsinner = seq![v].add(rest);
                assert(rhsinner.len() == 1 + rest.len());
                vstd::seq::lemma_seq_add_index2(seq![v], rest, i - entry.len());
                assert(lhs.index(i) == rest.index(i - entry.len() - 1));
                assert(rhs.index(i) == rhsinner.index(i - entry.len()));
                assert(rhsinner.index(i - entry.len())
                    == rest.index(i - entry.len() - 1));
            }
        }
    }
    ext_equal(lhs, rhs);
}

/// Push membership split: the pushed cell itself, or the old bag.
pub proof fn lemma_push_membership(s: Seq<usize>, t: usize, x: int)
    ensures
        spec_bag_has(s.push(t), x) <==> (x == t as int || spec_bag_has(s, x)),
{
    if x == t as int {
        // the pushed top cell hits under the full budget
        assert(s.push(t).len() == s.len() + 1);
        assert(s.push(t).index(s.len() as int) == t);
        assert(s.push(t).index(s.len() as int) == x);
        vstd::seq::lemma_seq_push_len(s, t);
        lemma_scan_step_hit(s.push(t), x, s.len() as int);
        lemma_scan_hit_grows(s.push(t), x, (s.len() + 1) as int, s.push(t).len() as int);
        assert(spec_bag_has(s.push(t), x));
    } else {
        lemma_push_preserves_miss(s, t, x);
    }
}

/// The exec membership scan (rides the step lemmas; the canonical
/// walk's per-domain-cell bag test).
pub fn bag_has_scan_exec(bag: &[usize], v: usize) -> (r: bool)
    ensures
        r <==> spec_bag_has(bag@, v as int),
{
    let mut i: usize = 0;
    let mut open: bool = true;
    while open && i < bag.len()
        invariant
            i <= bag.len(),
            bag@.len() == bag.len(),
            open ==> !spec_has_scan(bag@, v as int, i as int),
            !open ==> spec_bag_has(bag@, v as int),
        decreases bag.len() - i,
    {
        if bag[i] == v {
            proof {
                assert(bag@.index(i as int) == v);
                lemma_scan_step_hit(bag@, v as int, i as int);
                lemma_scan_hit_grows(bag@, v as int, (i + 1) as int, bag@.len() as int);
                assert(spec_bag_has(bag@, v as int));
            }
            open = false;
            // park the variant (the guard exits next check)
            i = bag.len();
        } else {
            proof {
                assert(bag@.index(i as int) != v);
                assert(spec_has_scan(bag@, v as int, (i + 1) as int)
                    == spec_has_scan(bag@, v as int, i as int));
            }
            i += 1;
        }
    }
    proof {
        if open {
            assert(i == bag.len()) by {
                assert(i >= bag.len());
            }
            reveal_with_fuel(spec_has_scan, 8);
            assert forall|k: int| 0 <= k < bag@.len() implies bag@.index(k) != v by {
                assert(0 <= k);
                assert(k < bag@.len());
                assert(k < i as int);
                if k == i as int - 1 {
                    assert(bag@.index(i as int - 1) != v);
                    assert(bag@.index(k) == bag@.index(i as int - 1));
                } else {
                    assert(k < i as int - 1);
                    lemma_scan_miss_cell(bag@, v as int, i as int, k);
                }
            }
            lemma_scan_all_miss(bag@, v as int, bag@.len() as int);
            assert(!spec_bag_has(bag@, v as int));
        }
    }
    !open
}

// ---------------------------------------------------------------------------
// Part G: the canonicalization walk (GM15's twin), return form.
// std's Vec::sort and Vec::dedup have no spec, so the twin builds the
// same value -- the strictly-ascending value-set enumeration of the
// collected bag over the index domain [v, bound) -- by a VERIFIED
// recursive walk whose postconditions bind the returned value
// directly (the lane ruling from probe p_recpost: a recursive exec
// fn's quantified postcondition instantiates at the call site
// through RETURN-value bindings, not &mut final-state placeholders;
// recorded in the batch notes).
//
// The produced value equals upstream's collect-then-sort/dedup
// (lib.rs:451-455): strictly ascending, deduped, exactly the bag's
// kept domain cells.
// ---------------------------------------------------------------------------

/// The add identities against the empty sequence.
pub proof fn lemma_add_empty_right(a: Seq<usize>)
    ensures
        a.add(Seq::empty()) == a,
{
    assert(a.add(Seq::empty()).len() == a.len());
    assert forall|i: int|
        #![trigger a.add(Seq::empty()).index(i)]
        0 <= i < a.len() implies a.add(Seq::empty()).index(i) == a.index(i) by {
        vstd::seq::lemma_seq_add_index1(a, Seq::empty(), i);
    }
    ext_equal(a.add(Seq::empty()), a);
}

pub proof fn lemma_add_empty_left(a: Seq<usize>)
    ensures
        spec_empty_add(a) == a,
{

    let e: Seq<usize> = Seq::empty();
    assert(e.len() == 0);
    assert(e.add(a).len() == a.len());
    assert forall|i: int|
        #![trigger e.add(a).index(i)]
        0 <= i < a.len() implies e.add(a).index(i) == a.index(i) by {
        vstd::seq::lemma_seq_add_index2(e, a, i);
        assert(e.add(a).index(i) == a.index(i - 0));
    }
    ext_equal(e.add(a), a);
    assert(spec_empty_add(a) == a);
}

/// Left-add of the empty sequence (carrier form for the ensures
/// clause; Seq::empty accepts no turbofish).
pub open spec fn spec_empty_add(a: Seq<usize>) -> Seq<usize> {
    let e: Seq<usize> = Seq::empty();
    e.add(a)
}

/// The add/push commutation (app(A, B.push(t)) == (A.add(B)).push(t)).
pub proof fn lemma_add_push_commute(a: Seq<usize>, b: Seq<usize>, t: usize)
    ensures
        a.add(b.push(t)) == (a.add(b)).push(t),
{
    let lhs = a.add(b.push(t));
    let rhs = (a.add(b)).push(t);
    vstd::seq::lemma_seq_push_len(b, t);
    vstd::seq::lemma_seq_add_len(a, b.push(t));
    vstd::seq::lemma_seq_add_len(a, b);
    vstd::seq::lemma_seq_push_len(a.add(b), t);
    assert(lhs.len() == (a.len() + b.len() + 1) as int);
    assert(rhs.len() == (a.len() + b.len() + 1) as int);
    assert forall|i: int|
        #![trigger lhs.index(i)]
        0 <= i < lhs.len() implies lhs.index(i) == rhs.index(i) by {
        if i < a.len() {
            vstd::seq::lemma_seq_add_index1(a, b.push(t), i);
            vstd::seq::lemma_seq_add_index1(a, b, i);
            vstd::seq::lemma_seq_push_index_different(a.add(b), t, i);
            assert(lhs.index(i) == a.index(i));
            assert(rhs.index(i) == a.add(b).index(i));
        } else if i < (a.len() + b.len()) as int {
            vstd::seq::lemma_seq_add_index2(a, b.push(t), i);
            vstd::seq::lemma_seq_add_index2(a, b, i);
            vstd::seq::lemma_seq_push_index_different(b, t, i - a.len());
            assert(lhs.index(i) == b.push(t).index(i - a.len()));
            assert(rhs.index(i) == b.index(i - a.len()));
            assert(b.push(t).index(i - a.len()) == b.index(i - a.len()));
        } else {
            assert(i == (a.len() + b.len()) as int);
            vstd::seq::lemma_seq_add_index2(a, b.push(t), i);
            assert(b.push(t).index(i - a.len()) == t);
            vstd::seq::lemma_seq_push_index_same(a.add(b), t, (a.len() + b.len()) as int);
            assert(lhs.index(i) == t);
            assert(rhs.index(i) == t);
        }
    }
    ext_equal(lhs, rhs);
}

/// The singleton membership.
pub proof fn lemma_singleton_has(v: usize, x: int)
    ensures
        spec_bag_has(seq![v], x) <==> (x == v as int),
{
    assert(seq![v].len() == 1);
    if x == v as int {
        assert(spec_has_scan(seq![v], x, 1));
        assert(spec_bag_has(seq![v], x));
    } else {
        assert(seq![v].index(0) != x);
        reveal_with_fuel(spec_has_scan, 3);
        assert(!spec_has_scan(seq![v], x, 1));
        assert(!spec_bag_has(seq![v], x));
    }
}

/// The singleton-lead ascending carry.
pub proof fn lemma_singleton_add_ascending(v: usize, rest: Seq<usize>)
    requires
        spec_ascending(rest),
        forall|k: int| 0 <= k < rest.len() as int ==> v < rest.index(k),
    ensures
        spec_ascending(seq![v].add(rest)),
{
    let cells = seq![v].add(rest);
    assert(seq![v].len() == 1);
    assert(cells.len() == 1 + rest.len());
    assert forall|k: int| 1 <= k + 1 <= cells.len() - 1 implies
        spec_lt_at(cells, k) by {
        if k == 0 {
            // the pair (0, 1): the singleton rides below the tail
            vstd::seq::lemma_seq_add_index1(seq![v], rest, 0);
            vstd::seq::lemma_seq_add_index2(seq![v], rest, 1);
            assert(cells.index(0) == v);
            assert(cells.index(1) == rest.index(0));
            assert(v < rest.index(0));
        } else if k + 1 < rest.len() {
            // interior pair: two shared rest cells (shifted by the
            // singleton lead)
            assert(k + 1 <= rest.len() - 1);
            assert(k >= 1);
            assert(1 <= k < rest.len());
            assert(1 <= k + 1 < rest.len() + 1);
            vstd::seq::lemma_seq_add_index2(seq![v], rest, k + 1);
            vstd::seq::lemma_seq_add_index2(seq![v], rest, k);
            assert(cells.index(k + 1) == rest.index(k + 1 - 1));
            assert(cells.index(k) == rest.index(k - 1));
            assert(k - 1 >= 0);
            assert(k - 1 <= rest.len() - 1);
            assert(spec_lt_at(rest, k - 1));
        } else {
            // the tail pair: two shared rest cells, shifted by the
            // singleton lead (cells.index(j) == rest.index(j - 1))
            assert(k >= 1);
            assert(k + 1 == rest.len());
            assert(rest.len() >= 2);
            assert(1 <= k < rest.len() + 1);
            assert(0 <= k - 1);
            assert(k - 1 < rest.len());
            assert(seq![v].len() == 1);
            assert(1 <= k < seq![v].len() + rest.len());
            assert(1 <= k + 1 < seq![v].len() + rest.len() + 1 - 1 + 1);
            assert(k + 1 <= seq![v].len() + rest.len() - 1 + 1);
            vstd::seq::lemma_seq_add_index2(seq![v], rest, k);
            vstd::seq::lemma_seq_add_index2(seq![v], rest, k + 1);
            assert(cells.index(k) == rest.index(k - 1));
            assert(cells.index(k + 1) == rest.index(k));
            assert(k - 1 + 1 <= rest.len() - 1 + 1);
            assert(k - 1 + 1 - 1 <= rest.len() - 1);
            assert(spec_lt_at(rest, k - 1));
        }
        assert(spec_lt_at(cells, k));
    }
}

/// One walk frame, return form (GM15's post-value).
pub fn canonicalize_rec(bag: &[usize], v: usize, bound: usize) -> (r: Vec<usize>)
    requires
        v <= bound,
        forall|k: int| 0 <= k < bag@.len() ==> spec_bag_bounded(bag@, k, bound as int),
    ensures
        // the walk output is strictly ascending
        spec_ascending(r@),
        // every cell lives in the walked band [v, bound)
        forall|k: int|
            #![trigger r@.index(k)]
            0 <= k < r@.len() ==> (v <= r@.index(k) && r@.index(k) < bound),
        // the membership iff (GL8's fourth face, the exercised form
        // of the GL7 deferred item): the walk's value contains
        // exactly the bag's cells inside the walked band [v, bound)
        forall|x: int|
            #![trigger spec_bag_has(r@, x)]
            spec_bag_has(r@, x) <==> (v <= x && x < bound as int && spec_bag_has(bag@, x)),

        // at most one cell per band step
        r@.len() <= (bound as int) - (v as int),
    decreases (bound as int) - (v as int),
{
    if v == bound {
        let r: Vec<usize> = Vec::new();
        assert(r@ == Seq::<usize>::empty());
        assert forall|x: int|
            #![trigger spec_bag_has(r@, x)]
            spec_bag_has(r@, x) <==> (v <= x && x < bound as int && spec_bag_has(bag@, x)) by {
            reveal_with_fuel(spec_has_scan, 2);
            assert(spec_bag_has(Seq::<usize>::empty(), x) == false);
            assert(v == bound);
        }
        r
    } else {
        let child = canonicalize_rec(bag, v + 1, bound);
        let h: bool = bag_has_scan_exec(bag, v);
        let ghost lead: Seq<usize> = if h { seq![v] } else { Seq::empty() };
        let mut out: Vec<usize> = Vec::new();
        if h {
            out.push(v);
        }
        let ch: &[usize] = child.as_slice();
        let mut i: usize = 0;
        while i < ch.len()
            invariant
                i <= ch.len(),
                ch@ == child@,
                ch.len() == child@.len(),
                lead == (if h { seq![v] } else { Seq::empty() }),
                out@ == lead.add(child@.subrange(0, i as int)),
            decreases ch.len() - i,
        {
            out.push(ch[i]);
            proof {
                // pushing the walked prefix cell extends the added
                // prefix view by exactly that cell
                let pre = lead.add(child@.subrange(0, i as int));
                let postv = lead.add(child@.subrange(0, (i + 1) as int));
                assert(pre.push(child@.index(i as int)) == postv) by {
                    assert(pre.len() == lead.len() + i as int);
                    assert(pre.push(child@.index(i as int)).len()
                        == lead.len() + i as int + 1);
                    assert(lead.add(child@.subrange(0, (i + 1) as int)).len()
                        == lead.len() + i as int + 1);
                    assert forall|j: int|
                        #![trigger pre.push(child@.index(i as int)).index(j)]
                        0 <= j < lead.len() + i as int + 1 implies
                        pre.push(child@.index(i as int)).index(j)
                            == lead.add(child@.subrange(0, (i + 1) as int)).index(j) by {
                        if j < lead.len() {
                            vstd::seq::lemma_seq_add_index1(lead, child@.subrange(0, i as int), j);
                            vstd::seq::lemma_seq_add_index1(lead, child@.subrange(0, (i + 1) as int), j);
                        } else if j < lead.len() + i as int {
                            let inner_pre_j = j - lead.len();
                            vstd::seq::lemma_seq_add_index2(lead, child@.subrange(0, i as int), j);
                            vstd::seq::lemma_seq_add_index2(lead, child@.subrange(0, (i + 1) as int), j);
                            vstd::seq::lemma_seq_push_index_different(child@.subrange(0, i as int), child@.index(i as int), inner_pre_j);
                        } else {
                            assert(j == (lead.len() + i as int));
                            vstd::seq::lemma_seq_push_index_same(pre, child@.index(i as int), pre.len() as int);
                            assert(pre.push(child@.index(i as int)).index(j)
                                == child@.index(i as int));
                            vstd::seq::lemma_seq_add_index2(lead, child@.subrange(0, (i + 1) as int), j);
                            let inner = j - lead.len();
                            assert(inner == i as int);
                            assert(lead.add(child@.subrange(0, (i + 1) as int)).index(j)
                                == child@.subrange(0, (i + 1) as int).index(inner));
                            vstd::seq::lemma_seq_subrange_index(child@, 0, (i + 1) as int, inner);
                            assert(child@.subrange(0, (i + 1) as int).index(inner)
                                == child@.index(0 + inner));
                        }
                    }
                    ext_equal(pre.push(child@.index(i as int)), postv);
                }
            }
            i += 1;
        }
        proof {
            assert(child@.subrange(0, ch.len() as int) == child@);
            assert(out@ == lead.add(child@));
            // the frame's assembly: every cell stays in-band
            assert forall|k: int|
                #![trigger out@.index(k)]
                0 <= k < out@.len() implies
                out@.index(k) >= v && out@.index(k) < bound by {
                if k < lead.len() {
                    assert(lead.len() == 1);
                    assert(lead.index(0) == v);
                    assert(v < bound);
                } else {
                    // the child's cells: its own band [v+1, bound)
                    let kk = k - lead.len();
                    assert(kk < child@.len());
                    vstd::seq::lemma_seq_add_index2(lead, child@, k);
                    assert(out@.index(k) == child@.index(kk));
                    assert(child@.index(kk) >= (v + 1));
                    assert(child@.index(kk) < bound);
                }
            }
            // the length face
            assert(out@.len() == lead.len() + child@.len());
            assert(child@.len() <= (bound as int) - ((v + 1) as int));
            assert(out@.len() <= (bound as int) - (v as int));
            // the ascending face: the lead singleton tops nothing and
            // every child cell tops v
            assert forall|k: int|
                #![trigger child@.index(k)]
                0 <= k < child@.len() implies v < child@.index(k) by {
                assert(child@.index(k) >= (v + 1));
            }
            if h {
                lemma_singleton_add_ascending(v, child@);
                assert(spec_ascending(seq![v].add(child@)));
                assert(out@ == seq![v].add(child@));
                // the iff frame (A7): the kept lead's membership
                // splits (A2) over the singleton (lemma_singleton_has)
                // and the child's recursive fourth postcondition
                // (the return-form call-site instantiation, p_recpost);
                // h's ensures tie the x == v case to has(bag, v)
                assert(h <==> spec_bag_has(bag@, v as int));
                assert forall|x: int|
                    spec_bag_has(out@, x) <==> (v <= x && x < bound as int && spec_bag_has(bag@, x)) by {
                    lemma_add_has_split(seq![v], child@, x);
                    lemma_singleton_has(v, x);
                }
            } else {
                lemma_add_empty_left(child@);
                assert(out@ == child@);
                // the iff frame (A7): no lead; the child's recursive
                // postcondition is the frame fact whole, and the
                // x == v case is barred by has(bag, v) == h == false
                assert(!spec_bag_has(bag@, v as int));
                assert forall|x: int|
                    spec_bag_has(out@, x) <==> (v <= x && x < bound as int && spec_bag_has(bag@, x)) by {
                    assert(out@ == child@);
                }
            }
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Part H: RequiredExtensionStrategy (lib.rs:914-968) + its builder
// (lib.rs:1086-1114). Upstream's value is fnv::HashMap<Vec<u8>,
// Vec<(usize, Regex)>>: the ext key -> the (index, regex) entries.
// The twin keeps the FnvByteMap flat-store discipline with ONE
// added column -- the regex string per event (the builder's value
// kind); the regexes are consumed only through the oracle face
// (Part C), never compiled (upstream's new_regex is a trusted entry
// point; the twin's build() therefore cannot fail and the
// Error::Regex arm is trusted-content -- recorded in the Origin
// note).
// ---------------------------------------------------------------------------

/// All entries' global indices under column key_pos j among the
/// first n events, in push order (the hit list of the reqext scans;
/// the regex strings ride the aligned res column, read per event).
pub open spec fn spec_reqext_entries_upto(
    evs: Seq<(usize, usize)>,
    j: int,
    n: int,
) -> Seq<usize>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        let base = spec_reqext_entries_upto(evs, j, n - 1);
        if (evs.index(n - 1).0 as int) == j {
            base.push(evs.index(n - 1).1)
        } else {
            base
        }
    }
}

pub open spec fn spec_reqext_entries(evs: Seq<(usize, usize)>, j: int) -> Seq<usize> {
    spec_reqext_entries_upto(evs, j, evs.len() as int)
}

/// is_match (lib.rs:917-933): a non-empty ext, a present key, and
/// some entry's regex hitting the path:
///     if candidate.ext.is_empty() { return false; }
///     match self.0.get(candidate.ext.as_bytes()) {
///         None => false,
///         Some(regexes) => any re.is_match(candidate.path),
///     }
pub open spec fn spec_reqext_is_match(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
) -> bool {
    ext.len() > 0
        && (match spec_map_find(keys, ext) {
            Some(j) => spec_reqext_any_hit(evs, res, j, path),
            None => false,
        })
}

/// matches_all, the keyed walk (the pin lib.rs:936-949 body, the
/// pre-PR3613 form): a non-empty ext, a present key, and every
/// regex under that one key hitting. Kept as its own face because
/// the PR3613 guard routes the single-bucket case through this
/// body unchanged (Part H2's guard-positive lemma pins that
/// replay), and because this unguarded walk IS the F1 defect's
/// cross-key skip when the store holds more than one bucket.
pub open spec fn spec_reqext_matches_all_keyed(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
) -> bool {
    ext.len() > 0
        && (match spec_map_find(keys, ext) {
            Some(j) => spec_reqext_all_hit(evs, res, j, path),
            None => false,
        })
}

/// matches_all, the PR3613 patched form of lib.rs:935-949:
///     if self.0.len() != 1 || candidate.ext.is_empty() {
///         return false;
///     }
///     if let Some(regexes) = self.0.get(candidate.ext.as_bytes()) {
///         every regex hits
///     } else { false }
/// The guard answers false upfront when the store holds anything
/// other than exactly one ext bucket; the single-bucket case keeps
/// the keyed walk verbatim. Part H2 carries the theorems: the
/// guard-positive cases, the unconditional false-positive
/// impossibility (patched true implies the whole-map
/// enumeration), and the conditional equivalence with the
/// all-buckets enumeration under the extractor invariant.
pub open spec fn spec_reqext_matches_all(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
) -> bool {
    keys.len() == 1 && spec_reqext_matches_all_keyed(keys, evs, res, ext, path)
}

/// matches_into's list (lib.rs:951-967): the hitting entries'
/// global indices under the found key, in order.
pub open spec fn spec_reqext_hits(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
) -> Seq<usize> {
    match spec_map_find(keys, ext) {
        Some(j) => spec_reqext_hit_upto(evs, res, j, path, evs.len() as int),
        None => Seq::empty(),
    }
}

// ---------------------------------------------------------------------------
// The per-column scans (upto forms; the pre/suf probe discipline).
// ---------------------------------------------------------------------------

/// Any entry under j whose regex hits (the filtered-any scan).
pub open spec fn spec_reqext_any_hit_upto(
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    j: int,
    path: Seq<u8>,
    n: int,
) -> bool
    decreases n
{
    if n <= 0 {
        false
    } else {
        spec_reqext_any_hit_upto(evs, res, j, path, n - 1)
            || ((evs.index(n - 1).0 as int) == j
                && spec_regex_hits(res.index(n - 1)@, path))
    }
}

pub open spec fn spec_reqext_any_hit(
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    j: int,
    path: Seq<u8>,
) -> bool {
    spec_reqext_any_hit_upto(evs, res, j, path, evs.len() as int)
}

/// Every entry under j's regex hits (the matches_all scan).
pub open spec fn spec_reqext_all_hit_upto(
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    j: int,
    path: Seq<u8>,
    n: int,
) -> bool
    decreases n
{
    if n <= 0 {
        true
    } else {
        spec_reqext_all_hit_upto(evs, res, j, path, n - 1)
            && ((evs.index(n - 1).0 as int) != j
                || spec_regex_hits(res.index(n - 1)@, path))
    }
}

pub open spec fn spec_reqext_all_hit(
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    j: int,
    path: Seq<u8>,
) -> bool {
    spec_reqext_all_hit_upto(evs, res, j, path, evs.len() as int)
}

/// The hitting entries' global indices under j among the first n
/// events, in order (the matches_into list).
pub open spec fn spec_reqext_hit_upto(
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    j: int,
    path: Seq<u8>,
    n: int,
) -> Seq<usize>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        let base = spec_reqext_hit_upto(evs, res, j, path, n - 1);
        if (evs.index(n - 1).0 as int) == j
            && spec_regex_hits(res.index(n - 1)@, path)
        {
            base.push(evs.index(n - 1).1)
        } else {
            base
        }
    }
}

// ---------------------------------------------------------------------------
// ReqExt exec layer: the flat store (the FnvByteMap discipline with
// the aligned regex column) and the builder (lib.rs:1086-1114's
// wiring). The regex queries ride the oracle spec faces above; the
// verified content of this tier is the container and the routing
// (the inventory's disposition row, "container wiring verified;
// regex predicates are oracle queries").
// ---------------------------------------------------------------------------

/// The key-position finder (the twin's private routing scan; the
/// columns are pub and this helper restates FnvByteMap's contains_
/// key internals so the j it returns can thread the spec find).
// (The exec key-position finder is cut: the ReqExt/RegexSet query
// faces are spec-oracle composites per the inventory's disposition
// row -- "container wiring verified; regex predicates are oracle
// queries" -- and no exec path consumes the position. The GL6
// contains_key scan remains the verified membership face.)

/// The strategy value (the flat twin of lib.rs:914's
/// fnv::HashMap<Vec<u8>, Vec<(usize, Regex)>>).
pub struct RequiredExtensionStrategy {
    pub exts: FnvByteMap,
    /// The per-event regex strings, aligned with exts.events.
    pub regexes: Vec<Vec<char>>,
}

impl RequiredExtensionStrategy {
    /// Query spec dispatch (upstream lib.rs:917-933 evaluated over
    /// the oracle face; the twin carries the triple).
    pub open spec fn is_match_of(&self, cand: &Candidate) -> bool {
        spec_reqext_is_match(
            self.exts.keys@,
            self.exts.events@,
            self.regexes@,
            cand.ext.view(),
            cand.path.view(),
        )
    }

    pub open spec fn matches_all_of(&self, cand: &Candidate) -> bool {
        spec_reqext_matches_all(
            self.exts.keys@,
            self.exts.events@,
            self.regexes@,
            cand.ext.view(),
            cand.path.view(),
        )
    }

    pub open spec fn matches_list_of(&self, cand: &Candidate) -> Seq<usize> {
        spec_reqext_hits(
            self.exts.keys@,
            self.exts.events@,
            self.regexes@,
            cand.ext.view(),
            cand.path.view(),
        )
    }
}

/// Origin Rust (lib.rs:1086-1101):
///     struct RequiredExtensionStrategyBuilder(
///         fnv::HashMap<Vec<u8>, Vec<(usize, String)>>);
///     fn add(&mut self, global_index, ext, regex) {
///         self.0.entry(ext.into_bytes()).or_insert(vec![])
///             .push((global_index, regex));
///     }
/// (the twin stores the regex STRING per event; upstream compiles
///  at build() through the trusted new_regex entry point, whose only
///  verified content is the Error::Regex mapping -- the twin's
///  build() cannot fail and that arm stays trusted-content)
pub struct RequiredExtensionStrategyBuilder {
    pub exts: FnvByteMap,
    pub regexes: Vec<Vec<char>>,
}

impl RequiredExtensionStrategyBuilder {
    /// Origin Rust (lib.rs:1092-1094): the empty builder.
    pub fn new() -> (r: RequiredExtensionStrategyBuilder)
        ensures
            r.exts.keys@ == Seq::empty(),
            r.exts.events@ == Seq::empty(),
            r.regexes@ == Seq::empty(),
    {
        RequiredExtensionStrategyBuilder {
            exts: FnvByteMap::new(),
            regexes: Vec::new(),
        }
    }

    /// Origin Rust (lib.rs:1096-1101): the entry push (the twin's
    /// aligned second column).
    pub fn add(&mut self, global_index: usize, ext: Vec<u8>, regex: Vec<char>)
        requires
            forall|e: int|
                0 <= e < self.exts.events@.len()
                    ==> (self.exts.events@.index(e).0 as int) < self.exts.keys@.len(),
        ensures
            final(self).exts.events@.len() == old(self).exts.events@.len() + 1,
            final(self).exts.events@.subrange(0, old(self).exts.events@.len() as int)
                == old(self).exts.events@,
            final(self).exts.events@.index(old(self).exts.events@.len() as int).0
                == (if spec_map_find(old(self).exts.keys@, ext@) is Some {
                    spec_map_find(old(self).exts.keys@, ext@).get_Some_0() as usize
                } else {
                    old(self).exts.keys@.len() as usize
                }),
            final(self).exts.events@.index(old(self).exts.events@.len() as int).1
                == global_index,
            final(self).regexes@.len() == old(self).regexes@.len() + 1,
            final(self).regexes@.subrange(0, old(self).regexes@.len() as int)
                == old(self).regexes@,
            final(self).regexes@.index(old(self).regexes@.len() as int)@ == regex@,
            final(self).exts.keys@.len()
                == old(self).exts.keys@.len()
                    + (if spec_map_has(old(self).exts.keys@, ext@) { 0int } else { 1int }),
            spec_map_has(old(self).exts.keys@, ext@) ==>
                final(self).exts.keys@ == old(self).exts.keys@,
            !spec_map_has(old(self).exts.keys@, ext@) ==> {
                &&& final(self).exts.keys@ == old(self).exts.keys@.push(ext)
                &&& final(self).exts.keys@.len() == old(self).exts.keys@.len() + 1
            },
            forall|e: int|
                0 <= e < final(self).exts.events@.len()
                    ==> (final(self).exts.events@.index(e).0 as int)
                        < final(self).exts.keys@.len(),
    {
        let regexes_len: usize = self.regexes.len();
        self.exts.add(ext, global_index);
        self.regexes.push(regex);
        proof {
            assert(self.regexes.len() == regexes_len + 1);
        }
    }

    /// Origin Rust (lib.rs:1103-1113): the build (compile-time
    /// trusted; the twin re-binds the store).
    pub fn build(self) -> (r: RequiredExtensionStrategy)
        ensures
            r.exts.keys@ == self.exts.keys@,
            r.exts.events@ == self.exts.events@,
            r.regexes@ == self.regexes@,
    {
        RequiredExtensionStrategy { exts: self.exts, regexes: self.regexes }
    }
}

// ---------------------------------------------------------------------------
// Part H2: the PR3613 guard theorems (RequiredExtensionStrategy::
// matches_all under the multi-bucket guard). Layering:
//   (a) guard-positive cases -- the patched spec's faces restated
//       as lemmas: multibucket false, empty-ext false, singleton
//       foreign-key false, and the single-bucket replay of the
//       keyed walk (the old body under the guard's own pass);
//   (b) unconditional soundness direction -- patched
//       matches_all == true forces the whole-map enumeration to
//       be true (the guard can never answer true while any regex
//       in the store misses; no premise beyond store
//       well-formedness);
//   (c) conditional equivalence -- under the extractor invariant
//       (every regex filed under key k only hits paths that end
//       with key k, the pigeonhole premise) plus the builder's
//       structural invariants, the guarded walk and the whole-map
//       enumeration agree in both directions. The invariant
//       premise is stated over the oracle face (the
//       uninterpreted spec_regex_hits predicate): its value side
//       belongs to the glob-to-regex compilation (an anchored
//       regex whose fixed escaped literal tail is the ext key),
//       carried here as a hypothesis; the runtime battery of the
//       PR3613 verification (f1-matches-all-pr3613-guard and the
//       invariant hunt probe) is its empirical leg.
// ---------------------------------------------------------------------------

/// Path suffix test, byte form (the fixed-tail reading of the
/// bucket regexes: any path a key-k regex accepts ends with k).
pub open spec fn spec_reqext_p_ends_with(p: Seq<u8>, k: Seq<u8>) -> bool {
    1 <= k.len()
        && k.len() <= p.len()
        && p.subrange(p.len() - k.len(), p.len() as int) == k
}

/// Store well-formedness: the res column aligns with the events
/// column, and every event's column position points into the keys
/// column (the builder add family's own invariant, restated here
/// for the theorems).
pub open spec fn spec_reqext_store_wf(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
) -> bool {
    res.len() == evs.len()
        && forall|e: int|
            0 <= e < evs.len()
                ==> 0 <= #[trigger] (evs.index(e).0 as int)
                    && (evs.index(e).0 as int) < keys.len()
}

/// The whole-map enumeration fix (the f1-matches-all-fixcheck
/// variant of the same defect fix): every regex of EVERY bucket
/// must hit, with the empty-ext gate kept.
pub open spec fn spec_reqext_matches_all_enum(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
) -> bool {
    ext.len() > 0
        && forall|e: int|
            0 <= e < evs.len() ==> spec_regex_hits(res.index(e)@, path)
}

/// The extractor key shape, byte form (the value column of
/// glob.rs's required_ext rev scan: every key is "." + a dotless,
/// slashless, nonempty run).
pub open spec fn spec_reqext_key_shape(k: Seq<u8>) -> bool {
    k.len() >= 1
        && k.index(0) == 0x2e
        && forall|q: int| 1 <= q < k.len() ==> {
            k.index(q) != 0x2e && k.index(q) != 0x2f
        }
}

/// Bucket populatedness: the builder add family pushes an event
/// for every key it creates, so every key of a built store has at
/// least one entry (no empty buckets).
pub open spec fn spec_reqext_bucket_populated(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    j: int,
) -> bool {
    exists|e: int| 0 <= e < evs.len() && (evs.index(e).0 as int) == j
}

/// The extractor invariant, oracle form (the pigeonhole premise):
/// any regex filed under key k only hits paths that end with key
/// k itself.
pub open spec fn spec_reqext_extractor_inv(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
) -> bool {
    forall|e: int, p: Seq<u8>|
        #[trigger] spec_regex_hits(res.index(e)@, p) && 0 <= e < evs.len()
            ==> spec_reqext_p_ends_with(
                p,
                keys.index(evs.index(e).0 as int)@,
            )
}

/// Seq extensionality for the byte seqs of this part (len plus
/// per-index equality).
proof fn lemma_reqext_seq_ext(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() == b.len(),
        forall|q: int| 0 <= q < a.len() ==> a.index(q) == b.index(q),
    ensures a == b,
{
}

/// The suffix test's index correspondence, per byte: byte q of the
/// key rides byte p.len()-k.len()+q of the path.
proof fn lemma_reqext_ends_with_index(p: Seq<u8>, k: Seq<u8>)
    requires
        spec_reqext_p_ends_with(p, k),
    ensures
        forall|q: int|
            0 <= q < k.len() ==> p.index(p.len() - k.len() + q) == k.index(q),
{
    let s = p.len() - k.len();
    vstd::seq::lemma_seq_subrange_len(p, s, p.len() as int);
    assert(p.subrange(s, p.len() as int).len() == p.len() - s);
    assert(p.subrange(s, p.len() as int) == k);
    assert(p.len() - s == k.len());
    assert(0 <= s && s <= p.len() && 1 <= k.len() && k.len() <= p.len());
    assert forall|q: int| 0 <= q < k.len() implies p.index(s + q) == k.index(q) by {
        assert(0 <= q && q < k.len());
        assert(s <= s + q && s + q < p.len());
        vstd::seq::lemma_seq_subrange_index(p, s, p.len() as int, q);
        assert(p.subrange(s, p.len() as int).index(q) == p.index(s + q));
    }
}

/// The pigeonhole: two extractor-shaped keys that both end the
/// same path are the same key (a single dot-led suffix can end
/// only one single-dot key -- distinct buckets therefore cannot
/// all hit one path).
proof fn lemma_reqext_two_suffixes_eq(p: Seq<u8>, x: Seq<u8>, y: Seq<u8>)
    requires
        spec_reqext_p_ends_with(p, x),
        spec_reqext_p_ends_with(p, y),
        spec_reqext_key_shape(x),
        spec_reqext_key_shape(y),
    ensures
        x == y,
{
    let lx = x.len() as int;
    let ly = y.len() as int;
    let lp = p.len() as int;
    if lx == ly {
        assert(x == p.subrange(lp - lx, lp));
        assert(y == p.subrange(lp - ly, lp));
        assert(x == y);
    } else if lx < ly {
        // y's suffix of length lx IS x, so y carries a '.' at
        // offset ly-lx >= 1: the shape forbids it
        let d = ly - lx;
        assert(d >= 1);
        assert(x == p.subrange(lp - lx, lp));
        assert(y == p.subrange(lp - ly, lp));
        vstd::seq::lemma_seq_subrange_index(p, lp - ly, lp, d);
        assert(p.subrange(lp - ly, lp).index(d) == p.index(lp - ly + d));
        assert(lp - ly + d == lp - lx);
        assert(y.index(d) == p.index(lp - lx));
        vstd::seq::lemma_seq_subrange_index(p, lp - lx, lp, 0);
        assert(p.subrange(lp - lx, lp).index(0) == p.index(lp - lx));
        assert(x.index(0) == p.index(lp - lx));
        assert(y.index(d) == x.index(0));
        assert(x.index(0) == 0x2e);
        // shape(y): no '.' at offsets >= 1
        assert(y.index(d) != 0x2e);
        assert(false);
    } else {
        // the mirror case, argument swapped
        let d = lx - ly;
        assert(d >= 1);
        assert(x == p.subrange(lp - lx, lp));
        assert(y == p.subrange(lp - ly, lp));
        vstd::seq::lemma_seq_subrange_index(p, lp - lx, lp, d);
        assert(p.subrange(lp - lx, lp).index(d) == p.index(lp - lx + d));
        assert(lp - lx + d == lp - ly);
        assert(x.index(d) == p.index(lp - ly));
        vstd::seq::lemma_seq_subrange_index(p, lp - ly, lp, 0);
        assert(p.subrange(lp - ly, lp).index(0) == p.index(lp - ly));
        assert(y.index(0) == p.index(lp - ly));
        assert(x.index(d) == y.index(0));
        assert(y.index(0) == 0x2e);
        assert(x.index(d) != 0x2e);
        assert(false);
    }
}

/// rfind face, forward direction: a nonnegative rfind result is
/// the byte itself.
proof fn lemma_reqext_rfind_is_byte(s: Seq<u8>, b: u8, n: int)
    requires
        0 <= n,
        n <= s.len(),
        rfind_pref(s, b, n) >= 0,
    ensures
        0 <= rfind_pref(s, b, n) < n,
        s.index(rfind_pref(s, b, n)) == b,
    decreases n,
{
    if n == 0 {
        // rfind over the empty prefix is -1: the premise closed
        // this branch by its own def
        assert(rfind_pref(s, b, 0) == -1);
        assert(false);
    } else {
        let top = rfind_pref(s, b, n);
        if s.index(n - 1) == b {
            assert(top == n - 1);
        } else {
            assert(rfind_pref(s, b, n) == rfind_pref(s, b, n - 1));
            lemma_reqext_rfind_is_byte(s, b, n - 1);
        }
    }
}

/// rfind face, the hit-at lemma over the full byte (the pathutil
/// discipline restated for this part): j carrying b with nothing
/// after it IS the rightmost occurrence.
proof fn lemma_reqext_rfind_hit_at(s: Seq<u8>, b: u8, n: int, j: int)
    requires
        0 <= j < n,
        n <= s.len(),
        s.index(j) == b,
        forall|t: int| j < t < n ==> s.index(t) != b,
    ensures
        rfind_pref(s, b, n) == j,
    decreases n,
{
    if n - 1 > j {
        assert(s.index(n - 1) != b);
        assert(rfind_pref(s, b, n) == rfind_pref(s, b, n - 1));
        lemma_reqext_rfind_hit_at(s, b, n - 1, j);
    } else {
        assert(n - 1 == j);
        assert(rfind_pref(s, b, n) == n - 1);
    }
}

/// The single-dot suffix of a path IS the candidate's ext: from
/// ends-with an extractor-shaped key comes ext == key (the ext
/// column of the pigeonhole premise; the basename premise is what
/// the nonempty-ext gate supplies at the call site).
proof fn lemma_reqext_dotted_suffix_is_ext(p: Seq<u8>, k: Seq<u8>)
    requires
        spec_reqext_p_ends_with(p, k),
        spec_reqext_key_shape(k),
        spec_cand_basename(p).len() > 0,
    ensures
        spec_cand_ext(p) == k,
{
    let lp = p.len() as int;
    let lk = k.len() as int;
    let b = spec_cand_basename(p);
    // the nonempty basename forces the final-component arm of the
    // basename def
    assert(b == spec_final_component(p)) by {
        // the nonempty premise excludes the empty-basename arms; the
        // remaining arm IS the final component
    }
    // the final component's slash anchor: the rfind value r
    // decides the component start s0
    let r = rfind_pref(p, 0x2f, lp);
    if r >= 0 {
        lemma_reqext_rfind_is_byte(p, 0x2f, lp);
        assert(0 <= r < lp);
        assert(p.index(r) == 0x2f);
        assert(spec_final_component(p) == p.subrange(r + 1, lp));
    } else {
        assert(spec_final_component(p) == p.subrange(0, lp));
    }
    let s0 = if r >= 0 { (r + 1) as int } else { 0int };
    assert(b == p.subrange(s0, lp));
    // the key rides the final component: if it straddled the
    // component start, the key would carry a '/'
    assert(s0 <= lp - lk) by {
        if s0 > lp - lk {
            // the slash at s0-1 lies inside the key's window
            assert(r == s0 - 1);
            assert(s0 - 1 >= lp - lk);
            vstd::seq::lemma_seq_subrange_index(
                p,
                lp - lk,
                lp,
                (s0 - 1) - (lp - lk),
            );
            assert(p.subrange(lp - lk, lp).index((s0 - 1) - (lp - lk))
                == p.index(lp - lk + ((s0 - 1) - (lp - lk))));
            assert(lp - lk + ((s0 - 1) - (lp - lk)) == s0 - 1);
            assert(p.subrange(lp - lk, lp) == k);
            assert(k.index((s0 - 1) - (lp - lk)) == p.index(s0 - 1));
            assert(k.index((s0 - 1) - (lp - lk)) == 0x2f);
            // the shape forbids '/' anywhere in the key
            assert(k.index(0) == 0x2e);
            assert(forall|q: int| 1 <= q < lk ==> k.index(q) != 0x2f);
            assert((s0 - 1) - (lp - lk) >= 0);
            assert(false);
        }
    }
    // b ends with k, per index
    let lb = b.len() as int;
    assert(lb == lp - s0);
    vstd::seq::lemma_seq_subrange_len(b, 0, lb);
    assert(b.subrange(0, lb) == b);
    assert(b.subrange(lb - lk, lb).len() == lk);
    assert forall|q: int| 0 <= q < lk implies b.index(lb - lk + q) == k.index(q) by {
        assert(0 <= q && q < lk);
        assert(s0 + (lb - lk) < lp);
        vstd::seq::lemma_seq_subrange_index(p, s0, lp, (lb - lk) + q);
        assert(p.subrange(s0, lp).index((lb - lk) + q)
            == p.index(s0 + (lb - lk) + q));
        vstd::seq::lemma_seq_subrange_index(p, lp - lk, lp, q);
        assert(p.subrange(lp - lk, lp).index(q) == p.index(lp - lk + q));
        assert(s0 + (lb - lk) == lp - lk);
        assert(s0 + (lb - lk) + q == lp - lk + q);
        assert(k.index(q) == p.subrange(lp - lk, lp).index(q));
        assert(b == p.subrange(s0, lp));
    }
    // the key's leading dot is the basename's rightmost dot
    let j = lb - lk;
    assert(b.index(j) == 0x2e);
    assert forall|t: int| j < t < lb implies b.index(t) != 0x2e by {
        assert(b.index(t) == k.index(t - j));
        assert(1 <= t - j < lk);
        assert(k.index(t - j) != 0x2e);
    }
    lemma_reqext_rfind_hit_at(b, 0x2e, lb, j);
    assert(rfind_pref(b, 0x2e, lb) == j);
    assert(spec_final_ext(b) == b.subrange(j, lb));
    lemma_reqext_seq_ext(b.subrange(j, lb), k);
    assert(b.len() > 0);
    assert(spec_cand_ext(p) == spec_final_ext(b));
    assert(spec_cand_ext(p) == k);
}

/// The all-hit scan's iff face: every entry's regex hits under
/// column j, exactly.
proof fn lemma_reqext_all_hit_upto_iff(
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    j: int,
    path: Seq<u8>,
    n: nat,
)
    requires
        (n as int) <= evs.len(),
        res.len() == evs.len(),
    ensures
        spec_reqext_all_hit_upto(evs, res, j, path, n as int)
            <==> forall|e: int| 0 <= e < (n as int)
                ==> ((evs.index(e).0 as int) != j
                    || spec_regex_hits(res.index(e)@, path)),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_reqext_all_hit_upto_iff(evs, res, j, path, (n - 1) as nat);
    }
}

/// Guard-positive case 1 (the gate): any store other than exactly
/// one bucket answers false.
proof fn th_reqext_guard_multibucket_false(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
)
    requires
        keys.len() != 1,
    ensures
        !spec_reqext_matches_all(keys, evs, res, ext, path),
{
}

/// Guard-positive case 2 (the ext gate): an empty candidate ext
/// answers false.
proof fn th_reqext_guard_empty_ext_false(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
)
    requires
        ext.len() == 0,
    ensures
        !spec_reqext_matches_all(keys, evs, res, ext, path),
{
    assert(!spec_reqext_matches_all_keyed(keys, evs, res, ext, path));
}

/// Guard-positive case 3 (the foreign key): a single bucket whose
/// key is not the candidate's ext answers false.
proof fn th_reqext_guard_foreign_key_false(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
)
    requires
        keys.len() == 1,
        ext.len() > 0,
        keys.index(0)@ != ext,
    ensures
        !spec_reqext_matches_all(keys, evs, res, ext, path),
{
    assert(spec_key_view(keys, 0) != ext);
    assert(keys.index(0)@ == spec_key_view(keys, 0));
    lemma_find_key_none(keys, ext, 1);
    assert(spec_map_find_key_upto(keys, ext, 1) is None);
    assert(spec_map_find(keys, ext) is None);
    assert(!spec_reqext_matches_all_keyed(keys, evs, res, ext, path));
}

/// Guard-positive case 4 (the single-bucket replay): with exactly
/// one bucket the patched spec is the keyed walk verbatim (the
/// PR3613 guard changes nothing for the len==1 store).
proof fn th_reqext_guard_single_old_logic(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
)
    requires
        keys.len() == 1,
    ensures
        spec_reqext_matches_all(keys, evs, res, ext, path)
            <==> spec_reqext_matches_all_keyed(keys, evs, res, ext, path),
{
}

/// (b) The unconditional soundness direction -- false-positive
/// impossibility: a patched matches_all == true forces the
/// whole-map enumeration to be true. Under the guard's own
/// keys.len()==1 face, the keyed column IS the whole map (every
/// event rides the single bucket), so the all-hit scan is the
/// full enumeration; no extractor premise is involved.
proof fn th_reqext_guard_true_sound(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
)
    requires
        spec_reqext_store_wf(keys, evs, res),
    ensures
        spec_reqext_matches_all(keys, evs, res, ext, path)
            ==> spec_reqext_matches_all_enum(keys, evs, res, ext, path),
{
    if spec_reqext_matches_all(keys, evs, res, ext, path) {
        assert(keys.len() == 1);
        let keyed = spec_reqext_matches_all_keyed(keys, evs, res, ext, path);
        assert(keyed);
        // collect the keyed walk's faces: the ext gate and the find
        let found = spec_map_find(keys, ext);
        assert(found is Some);
        let j = found.get_Some_0();
        // find over a 1-key column lands on position 0
        assert(j == 0) by {
            assert(spec_map_find(keys, ext)
                == spec_map_find_key_upto(keys, ext, (keys.len() as nat)));
            assert(keys.len() == 1);
            reveal_with_fuel(spec_map_find_key_upto, 2);
        }
        // the all-hit scan over column 0, per event
        lemma_reqext_all_hit_upto_iff(evs, res, 0, path, evs.len() as nat);
        assert(spec_reqext_all_hit(evs, res, 0, path));
        // every event rides the single column
        assert forall|e: int| 0 <= e < evs.len() implies spec_regex_hits(res.index(e)@, path) by {
            let col = evs.index(e).0 as int;
            assert(0 <= col < keys.len() == 1);
            assert(col == 0);
        }
        assert(ext.len() > 0);
        assert(spec_reqext_matches_all_enum(keys, evs, res, ext, path));
    }
}

/// (c) The conditional equivalence -- under the extractor
/// invariant (plus the builder's structural faces: populated
/// distinct extractor-shaped buckets), the guarded walk and the
/// whole-map enumeration agree in both directions. The layered
/// premises: distinct keys and nonempty buckets come from the
/// builder add family's own contracts; the key shape comes from
/// glob.rs's required_ext rev scan; the invariant premise is the
/// oracle-side hypothesis (empirical leg: the PR3613 battery).
proof fn th_reqext_guard_iff_enum(
    keys: Seq<Vec<u8>>,
    evs: Seq<(usize, usize)>,
    res: Seq<Vec<char>>,
    ext: Seq<u8>,
    path: Seq<u8>,
)
    requires
        spec_reqext_store_wf(keys, evs, res),
        keys.len() >= 1,
        forall|i: int, j: int| 0 <= i < j < keys.len() ==> keys.index(i)@ != keys.index(j)@,
        forall|j: int|
            0 <= j < keys.len() ==> spec_reqext_key_shape(keys.index(j)@),
        forall|j: int|
            0 <= j < keys.len() ==> spec_reqext_bucket_populated(keys, evs, j),
        spec_reqext_extractor_inv(keys, evs, res),
        spec_cand_ext(path).len() > 0,
        ext == spec_cand_ext(path),
    ensures
        spec_reqext_matches_all(keys, evs, res, ext, path)
            <==> spec_reqext_matches_all_enum(keys, evs, res, ext, path),
{
    // (==> direction) unconditional: the guard's true answers walk
    // through the soundness theorem
    th_reqext_guard_true_sound(keys, evs, res, ext, path);
    // (<== direction) from the enumeration split on the bucket count
    if !spec_reqext_matches_all_enum(keys, evs, res, ext, path) {
        assert(!spec_reqext_matches_all(keys, evs, res, ext, path));
        return;
    }
    assert(ext.len() > 0) by {
        assert(spec_reqext_matches_all_enum(keys, evs, res, ext, path));
    }
    // the pigeonhole: >= 2 distinct buckets cannot both carry a
    // rightmost-dot suffix of one path
    assert(keys.len() == 1) by {
        if keys.len() >= 2 {
            assert(spec_reqext_bucket_populated(keys, evs, 0));
            assert(spec_reqext_bucket_populated(keys, evs, 1));
            let ex0 = choose|e: int| 0 <= e < evs.len() && (evs.index(e).0 as int) == 0;
            let ex1 = choose|e: int| 0 <= e < evs.len() && (evs.index(e).0 as int) == 1;
            assert(spec_regex_hits(res.index(ex0)@, path));
            assert(spec_regex_hits(res.index(ex1)@, path));
            assert(spec_reqext_p_ends_with(path, keys.index(0)@));
            assert(spec_reqext_p_ends_with(path, keys.index(1)@));
            lemma_reqext_two_suffixes_eq(path, keys.index(0)@, keys.index(1)@);
            assert(keys.index(0)@ == keys.index(1)@);
            assert(false);
        }
    }
    // the single bucket's key is the path's own dot suffix, hence
    // the found key of the keyed walk
    assert(spec_reqext_bucket_populated(keys, evs, 0));
    let ec = choose|e: int| 0 <= e < evs.len() && (evs.index(e).0 as int) == 0;
    assert(spec_regex_hits(res.index(ec)@, path));
    assert(spec_reqext_p_ends_with(path, keys.index(0)@));
    let k0 = keys.index(0)@;
    assert(spec_cand_basename(path).len() > 0) by {
        // an ext-having path has a nonempty basename (the ext def
        // reads the basename's final-dot suffix)
        assert(spec_cand_ext(path).len() > 0);
    }
    lemma_reqext_dotted_suffix_is_ext(path, k0);
    assert(spec_cand_ext(path) == k0);
    assert(ext == k0);
    assert(spec_map_find(keys, ext) == Some(0)) by {
        assert(keys.index(0)@ == ext);
        lemma_find_key_hit_at(keys, ext, 1, 0);
        assert(spec_map_find_key_upto(keys, ext, 1) == Some(0));
    }
    // the single column's all-hit is the whole enumeration
    lemma_reqext_all_hit_upto_iff(evs, res, 0, path, evs.len() as nat);
    assert forall|e: int| 0 <= e < evs.len() implies spec_regex_hits(res.index(e)@, path) by {
        assert((evs.index(e).0 as int) != 0
            || spec_regex_hits(res.index(e)@, path));
        let col = evs.index(e).0 as int;
        assert(0 <= col < keys.len() == 1);
        assert(col == 0);
    }
    assert(spec_reqext_all_hit(evs, res, 0, path));
    assert(spec_reqext_matches_all_keyed(keys, evs, res, ext, path));
    assert(spec_reqext_matches_all(keys, evs, res, ext, path));
}

// ---------------------------------------------------------------------------
// Part I: RegexSetStrategy (lib.rs:970-1030) -- the meta-regex tier.
// Upstream compiles the patterns once (new_regex_set, trusted entry
// point) and asks which_overlapping_matches over a pooled PatternSet;
// the pool protocol (clear-before-use; the set_does_not_remember
// regression, lib.rs:1329-1347) is a ghost-state property: the twin
// derives the match set fresh per query (stateless), so the
// does-not-remember property holds by construction (the harness
// runs the two sequential queries as the ghost-state regression).
// ---------------------------------------------------------------------------

/// The haystack (upstream lib.rs:991-997):
///     fn haystack<'a>(&self, candidate) -> &'a [u8] {
///         if self.basename { candidate.basename_for_regex() } else { &candidate.path }
///     }
/// (the GL6 basename_for_regex twin returns a Vec; its spec face
///  carries the byte value)
pub open spec fn spec_rset_haystack(
    basename: bool,
    path: Seq<u8>,
) -> Seq<u8> {
    match spec_rset_hay_of(basename, path) {
        Some(h) => h,
        None => Seq::empty(),
    }
}

/// The bfr arm (the GL6 face's value column).
pub open spec fn spec_rset_hay_of(basename: bool, path: Seq<u8>) -> Option<Seq<u8>> {
    if basename {
        Some(spec_base_for_regex(path))
    } else {
        Some(path)
    }
}

/// The basename_for_regex spec (the GL6 face's ensures value,
/// restated over the path column).
pub open spec fn spec_base_for_regex(path: Seq<u8>) -> Seq<u8> {
    if spec_cand_base_for_regex_arm(path) {
        spec_dotdot()
    } else {
        spec_cand_basename(path)
    }
}

/// is_match (lib.rs:999-1001): the meta regex over the haystack.
pub open spec fn spec_rset_is_match(
    regexes: Seq<Vec<char>>,
    map: Seq<usize>,
    basename: bool,
    path: Seq<u8>,
) -> bool {
    let hay = spec_rset_haystack(basename, path);
    exists|q: int| 0 <= q < regexes.len() && spec_regex_hits(regexes.index(q)@, hay)
}

/// matches_all (lib.rs:1014-1017): patset.is_full() -- every
/// pattern's regex hits the haystack.
pub open spec fn spec_rset_matches_all(
    regexes: Seq<Vec<char>>,
    map: Seq<usize>,
    basename: bool,
    path: Seq<u8>,
) -> bool {
    let hay = spec_rset_haystack(basename, path);
    forall|q: int| 0 <= q < regexes.len() ==> spec_regex_hits(regexes.index(q)@, hay)
}

/// matches_into (lib.rs:1019-1029): the hitting patterns' map cells
/// in pattern order (PatternSet::iter's ascending id order).
pub open spec fn spec_rset_hits(
    regexes: Seq<Vec<char>>,
    map: Seq<usize>,
    basename: bool,
    path: Seq<u8>,
) -> Seq<usize> {
    let hay = spec_rset_haystack(basename, path);
    spec_rset_hits_upto(regexes, map, hay, regexes.len() as int)
}

pub open spec fn spec_rset_hits_upto(
    regexes: Seq<Vec<char>>,
    map: Seq<usize>,
    hay: Seq<u8>,
    n: int,
) -> Seq<usize>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        let base = spec_rset_hits_upto(regexes, map, hay, n - 1);
        if spec_regex_hits(regexes.index(n - 1)@, hay) {
            base.push(map.index(n - 1))
        } else {
            base
        }
    }
}

/// The strategy value (the twin of lib.rs:970-984's struct; the
/// pool aux columns are the stateless-ghost twin's note -- upstream's
/// Arc<Pool<PatternSet>> never leaks between queries, which is the
/// does-not-remember property the twin holds by construction).
pub struct RegexSetStrategy {
    pub regexes: Vec<Vec<char>>,
    pub map: Vec<usize>,
    pub basename: bool,
}

impl RegexSetStrategy {
    pub open spec fn is_match_of(&self, cand: &Candidate) -> bool {
        spec_rset_is_match(self.regexes@, self.map@, self.basename, cand.path.view())
    }

    pub open spec fn matches_all_of(&self, cand: &Candidate) -> bool {
        spec_rset_matches_all(self.regexes@, self.map@, self.basename, cand.path.view())
    }

    pub open spec fn matches_list_of(&self, cand: &Candidate) -> Seq<usize> {
        spec_rset_hits(self.regexes@, self.map@, self.basename, cand.path.view())
    }
}

// ---------------------------------------------------------------------------
// Part J: the set tier (lib.rs:674-740 dispatch, 442-565 the set
// query surface, 461-563 the fan-out, 574-601 the builder).
//
// Disposition architecture (the inventory's GL7 row): strategies
// whose whole query is computable over verified data (Literal,
// Extension, Prefix, Suffix; the hashed and scanned tiers) carry
// exec twins with full value contracts (Parts B/E and the GL6
// faces); the oracle-bound tiers (RequiredExtension, RegexSet)
// carry SPEC-composite query faces over the twin data (the
// predicates are oracle queries; the verified content is the
// container, the routing and this dispatch table). The GlobSet
// queries are therefore spec fns over the strats column; the
// matches_candidate_into VALUE (GM15's post-form) is the exec
// canonicalize walk over the collected stream, whose per-strategy
// collection spec matches the composite dispatch list below --
// the harness rows drive each vector's bag via the strategy
// contracts and the oracle axioms.
// ---------------------------------------------------------------------------

/// The char-slice copy (a to_vec twin for the char lanes; std's
/// to_vec lacks a spec).
pub fn chars_to_vec(src: &[char]) -> (r: Vec<char>)
    ensures
        r@ == src@,
{
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < src.len()
        invariant
            i <= src.len(),
            src@.len() == src.len(),
            out@.len() == i,
            forall|k: int|
                #![trigger out@.index(k)]
                0 <= k < out@.len() ==> out@.index(k) == src@.index(k),
        decreases src.len() - i,
    {
        out.push(src[i]);
        i += 1;
    }
    proof {
        assert forall|k: int|
            #![trigger out@.index(k)]
            0 <= k < src.len() as int implies out@.index(k) == src@.index(k) by {
        }
        ext_equal(out@, src@);
    }
    out
}

/// The routing tag (upstream's MatchStrategy, glob.rs:37-46; the
/// twin moves the payload to the columns where it is consumed).
pub enum MatchRoute {
    Lit,
    BaseLit,
    Ext,
    Pre,
    Suf,
    ReqExt,
    BaseRe,
    Re,
}

/// One prepared pattern row for the fan-out: the classification
/// decision already rendered (the GL4 spec_match_strategy tie rides
/// the harness assertion), plus the payload columns.
pub struct PreparedPattern {
    pub route: MatchRoute,
    /// The routed payload bytes (literal/ext/prefix/suffix bytes;
    /// the suffix-component strip consumes its [1..]).
    pub payload: Vec<char>,
    /// The full-regex string (RequiredExtension's and Regex' arm
    /// both consume p.regex(); BaseRe's payload IS its basename
    /// regex, so the regex column carries it there).
    pub re: Vec<char>,
}

/// The view of a prepared row (the char payloads arrive as their
/// byte encodings; the recorded classification).
pub open spec fn spec_route(r: &MatchRoute) -> int {
    match *r {
        MatchRoute::Lit => 0,
        MatchRoute::BaseLit => 1,
        MatchRoute::Ext => 2,
        MatchRoute::Pre => 3,
        MatchRoute::Suf => 4,
        MatchRoute::ReqExt => 5,
        MatchRoute::BaseRe => 6,
        MatchRoute::Re => 7,
    }
}

/// The set strategy column (upstream's GlobSetMatchStrategy
/// dispatch enum; each arm carries the tier twin's data).
pub enum GlobSetMatchStrategyS {
    Literal(LiteralStrategy),
    BasenameLiteral(LiteralStrategy),
    Extension(ExtensionStrategy),
    Prefix(PrefixStrategy),
    Suffix(SuffixStrategy),
    RequiredExtension(RequiredExtensionStrategy),
    Regex(RegexSetStrategy),
}

/// Origin Rust (lib.rs:685-700): the is_match dispatch, every arm
/// quoted; the BasenameLiteral arm carries the load-bearing guard
/// `!candidate.basename.is_empty()` (the GL6-deferred behavior
/// theorem: the guard makes a trailing-`..` path yield no
/// basename-literal hit although the literal itself could equal
/// the virtual `..` -- lib.rs:1421's own parent-component KAT rows
/// pin it).
pub open spec fn spec_gsm_is_match(s: &GlobSetMatchStrategyS, cand: &Candidate) -> bool {
    match s {
        GlobSetMatchStrategyS::Literal(l) => spec_lit_is_match(
            l.lengths,
            l.literals.keys@,
            l.literals.events@,
            cand.path.view(),
        ),
        GlobSetMatchStrategyS::BasenameLiteral(l) => cand.basename.view().len() > 0
            && spec_lit_is_match(
                l.lengths,
                l.literals.keys@,
                l.literals.events@,
                cand.basename.view(),
            ),
        GlobSetMatchStrategyS::Extension(e) => spec_ext_is_match(
            e.0.keys@,
            e.0.events@,
            cand.ext.view(),
        ),
        GlobSetMatchStrategyS::Prefix(p) => spec_pre_is_match(
            p.lits@,
            spec_window(cand.path.view(), p.longest as int, false),
        ),
        GlobSetMatchStrategyS::Suffix(x) => spec_suf_is_match(
            x.lits@,
            spec_window(cand.path.view(), x.longest as int, true),
        ),
        GlobSetMatchStrategyS::RequiredExtension(r) => r.is_match_of(cand),
        GlobSetMatchStrategyS::Regex(g) => g.is_match_of(cand),
    }
}

/// Origin Rust (lib.rs:725-739): the matches_all dispatch (GM16's
/// per-tier semantics: the hashed tiers' singleton gate, the AC
/// tiers' count-each, the oracle tiers' all-cells).
pub open spec fn spec_gsm_matches_all(s: &GlobSetMatchStrategyS, cand: &Candidate) -> bool {
    match s {
        GlobSetMatchStrategyS::Literal(l) => spec_lit_matches_all(
            l.lengths,
            l.literals.keys@,
            l.literals.events@,
            cand.path.view(),
        ),
        GlobSetMatchStrategyS::BasenameLiteral(l) => cand.basename.view().len() > 0
            && spec_lit_matches_all(
                l.lengths,
                l.literals.keys@,
                l.literals.events@,
                cand.basename.view(),
            ),
        GlobSetMatchStrategyS::Extension(e) => spec_ext_matches_all(
            e.0.keys@,
            e.0.events@,
            cand.ext.view(),
        ),
        GlobSetMatchStrategyS::Prefix(p) => spec_pre_count(
            p.lits@,
            spec_window(cand.path.view(), p.longest as int, false),
        ) == p.map@.len() as int,
        GlobSetMatchStrategyS::Suffix(x) => spec_suf_count(
            x.lits@,
            spec_window(cand.path.view(), x.longest as int, true),
        ) == x.map@.len() as int,
        GlobSetMatchStrategyS::RequiredExtension(r) => r.matches_all_of(cand),
        GlobSetMatchStrategyS::Regex(g) => g.matches_all_of(cand),
    }
}

/// Origin Rust (lib.rs:702-723): the matches_into dispatch, each
/// arm's contribution list (the collection spec of the GM15 walk).
pub open spec fn spec_gsm_matches_list(s: &GlobSetMatchStrategyS, cand: &Candidate) -> Seq<usize> {
    let l = match s {
        GlobSetMatchStrategyS::Literal(l) => spec_hit_list(
            l.literals.keys@,
            l.literals.events@,
            cand.path.view(),
        ),
        GlobSetMatchStrategyS::BasenameLiteral(l) => if cand.basename.view().len() > 0 {
            spec_hit_list(
                l.literals.keys@,
                l.literals.events@,
                cand.basename.view(),
            )
        } else {
            Seq::empty()
        },
        GlobSetMatchStrategyS::Extension(e) => spec_hit_list(
            e.0.keys@,
            e.0.events@,
            cand.ext.view(),
        ),
        GlobSetMatchStrategyS::Prefix(p) => spec_pre_hits(
            p.lits@,
            p.map@,
            spec_window(cand.path.view(), p.longest as int, false),
        ),
        GlobSetMatchStrategyS::Suffix(x) => spec_suf_hits(
            x.lits@,
            x.map@,
            spec_window(cand.path.view(), x.longest as int, true),
        ),
        GlobSetMatchStrategyS::RequiredExtension(r) => r.matches_list_of(cand),
        GlobSetMatchStrategyS::Regex(g) => g.matches_list_of(cand),
    };
    l
}

/// The nonempty-list iff (the is_match bridge over the dispatch
/// lists; each arm's carrier is a scan family with the
/// any-hit/list-link at its root -- the harness rows pin the
/// oracle-arm sides, the computable arms ride their proofs).
pub open spec fn spec_gsm_list_nonempty_iff(s: &GlobSetMatchStrategyS, cand: &Candidate) -> bool {
    spec_gsm_matches_list(s, cand).len() > 0 <==> spec_gsm_is_match(s, cand)
}


// ---------------------------------------------------------------------------
// The set composites (the query surface spec: upstream lib.rs:442-
// 740 driven over the strategy column; the matches_into collected
// stream is the GM15 walk's bag input).
// ---------------------------------------------------------------------------

/// The any-strategy scan (is_match_candidate, lib.rs:342-360).
pub open spec fn spec_set_is_match(strats: Seq<GlobSetMatchStrategyS>, cand: &Candidate) -> bool {
    exists|q: int| 0 <= q < strats.len() && spec_gsm_is_match(&strats.index(q), cand)
}

/// The all-strategy conjunction (matches_all_candidate, lib.rs:
/// 379-397; the empty set is vacuously true -- GM16).
pub open spec fn spec_set_matches_all(strats: Seq<GlobSetMatchStrategyS>, cand: &Candidate) -> bool {
    forall|q: int| 0 <= q < strats.len() ==> spec_gsm_matches_all(&strats.index(q), cand)
}

/// The collected stream (the pre-canonicalization bag, lib.rs:451-
/// 453's extend-per-strategy loop, spec form).
pub open spec fn spec_set_collect(strats: Seq<GlobSetMatchStrategyS>, cand: &Candidate) -> Seq<usize> {
    spec_set_collect_upto(strats, cand, strats.len() as int)
}

pub open spec fn spec_set_collect_upto(
    strats: Seq<GlobSetMatchStrategyS>,
    cand: &Candidate,
    n: int,
) -> Seq<usize>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        spec_set_collect_upto(strats, cand, n - 1).add(
            spec_gsm_matches_list(&strats.index(n - 1), cand),
        )
    }
}

/// The GlobSet value (lib.rs:275-339's struct; the twin carries the
/// strategy column plus the set length).
pub struct GlobSet {
    pub len: usize,
    pub strats: Vec<GlobSetMatchStrategyS>,
}

impl GlobSet {
    /// Origin Rust (lib.rs:341-360): the pub query surface, spec
    /// composites over the strategy column.
    pub open spec fn is_match_of(&self, cand: &Candidate) -> bool {
        spec_set_is_match(self.strats@, cand)
    }

    pub open spec fn matches_all_of(&self, cand: &Candidate) -> bool {
        spec_set_matches_all(self.strats@, cand)
    }

    pub open spec fn matches_of(&self, cand: &Candidate) -> Seq<usize> {
        canonicalize_of(spec_set_collect(self.strats@, cand), self.len as int)
    }
}

/// The GM15 post-value over the collected stream (the walk's value
/// form at the set level: the strictly-ascending enumeration).
pub open spec fn canonicalize_of(bag: Seq<usize>, bound: int) -> Seq<usize> {
    spec_walk_value(bag, 0, bound)
}

/// The walk value, spec form (the exec canonicalize_rec's twin
/// statement; the exec twin's ensures bind the same shape and the
/// harness locks the value rows per vector).
pub open spec fn spec_walk_value(bag: Seq<usize>, v: int, bound: int) -> Seq<usize>
    decreases bound - v
{
    if v >= bound {
        Seq::empty()
    } else {
        let rest = spec_walk_value(bag, v + 1, bound);
        if spec_bag_has(bag, v) {
            seq![v as usize].add(rest)
        } else {
            rest
        }
    }
}

// ---------------------------------------------------------------------------
// The fan-out (GlobSet::new, lib.rs:461-563, and the builder
// lib.rs:574-601). The exec assembly walks the classification table
// in upstream order, adds each routed payload to its tier builder
// (the builder's ensures carry the column contents), and pushes
// only populated strategies (the populated-only discipline,
// lib.rs:532-561).
// ---------------------------------------------------------------------------

/// The assembled set (the fan-out return; the classification of
/// each row is an input -- the GL4-extractor tie rides the harness
/// routers, where spec_match_strategy is asserted against each
/// prepared row).
pub struct GlobSetFromParts {
    pub set: GlobSet,
}

impl GlobSetFromParts {
    /// Origin Rust (lib.rs:461-563), the merge loop arms:
    ///   Literal(lit)            => lits.add(i, lit)
    ///   BasenameLiteral(lit)    => base_lits.add(i, lit)
    ///   Extension(ext)          => exts.add(i, ext)
    ///   Prefix(prefix)          => prefixes.add(i, prefix)
    ///   Suffix{suffix, comp}    => if comp { lits.add(i, suffix[1..]) }
    ///                              suffixes.add(i, suffix)
    ///   RequiredExtension(ext)  => required_exts.add(i, ext, p.regex())
    ///   BasenameRegex(re)       => base_regexes.add(i, re)
    ///   Regex                   => regexes.add(i, p.regex())
    /// followed by the populated-only strats pushes in upstream
    /// order (exts, base_lits, lits, suffixes, prefixes, reqexts,
    /// base_regexes w/ basename=true, regexes).
    ///
    /// The twin takes the classification as data (each row already
    /// rendered; the payload wire is the byte-encoding of the row's
    /// char column through the Part A bridge).
    pub fn new(rows: &[PreparedPattern]) -> (r: GlobSet)
        ensures
            r.len == rows@.len(),
            r.strats@.len() <= 8,
    {
        // Origin arms (lib.rs:480-518) -- the classification loop
        let mut lits: LiteralStrategy = LiteralStrategy::new();
        let mut base_lits: LiteralStrategy = LiteralStrategy::new();
        let mut exts: ExtensionStrategy = ExtensionStrategy::new();
        let mut prefixes: MultiStrategyBuilder = MultiStrategyBuilder::new();
        let mut suffixes: MultiStrategyBuilder = MultiStrategyBuilder::new();
        let mut required_exts: RequiredExtensionStrategyBuilder =
            RequiredExtensionStrategyBuilder::new();
        let mut base_regexes: CharStrategyBuilder = CharStrategyBuilder::new();
        let mut regexes: CharStrategyBuilder = CharStrategyBuilder::new();
        let mut i: usize = 0;
        while i < rows.len()
            invariant
                i <= rows.len(),
                lits.literals.events@.len() == lits.literals.events.len(),
                forall|e: int|
                    0 <= e < lits.literals.events@.len()
                        ==> (lits.literals.events@.index(e).0 as int) < lits.literals.keys@.len(),
                forall|e: int|
                    0 <= e < base_lits.literals.events@.len()
                        ==> (base_lits.literals.events@.index(e).0 as int)
                            < base_lits.literals.keys@.len(),
                forall|e: int|
                    0 <= e < exts.0.events@.len()
                        ==> (exts.0.events@.index(e).0 as int) < exts.0.keys@.len(),
                forall|e: int|
                    0 <= e < required_exts.exts.events@.len()
                        ==> (required_exts.exts.events@.index(e).0 as int)
                            < required_exts.exts.keys@.len(),
            decreases rows.len() - i,
        {
            let row = &rows[i];
            match row.route {
                MatchRoute::Lit => {
                    let lq: &[char] = row.payload.as_slice();
                    lits.add(i, utf8_encode_chars(lq));
                }
                MatchRoute::BaseLit => {
                    let lq: &[char] = row.payload.as_slice();
                    base_lits.add(i, utf8_encode_chars(lq));
                }
                MatchRoute::Ext => {
                    let lq: &[char] = row.payload.as_slice();
                    exts.add(i, utf8_encode_chars(lq));
                }
                MatchRoute::Pre => {
                    let lq: &[char] = row.payload.as_slice();
                    prefixes.add(i, utf8_encode_chars(lq));
                }
                MatchRoute::Suf => {
                    let lq: &[char] = row.payload.as_slice();
                    suffixes.add(i, utf8_encode_chars(lq));
                }
                MatchRoute::ReqExt => {
                    let lq: &[char] = row.payload.as_slice();
                    let recopy = chars_to_vec(row.re.as_slice());
                    required_exts.add(i, utf8_encode_chars(lq), recopy);
                }
                MatchRoute::BaseRe => {
                    let lq: &[char] = row.payload.as_slice();
                    base_regexes.add(i, chars_to_vec(lq));
                }
                MatchRoute::Re => {
                    let recopy = chars_to_vec(row.re.as_slice());
                    regexes.add(i, recopy);
                }
            }
            i += 1;
        }
        // populated-only pushes (the upstream order, lib.rs:532-561)
        let mut strats: Vec<GlobSetMatchStrategyS> = Vec::new();
        if exts.0.len() > 0 {
            strats.push(GlobSetMatchStrategyS::Extension(exts));
        }
        if base_lits.literals.len() > 0 {
            strats.push(GlobSetMatchStrategyS::BasenameLiteral(base_lits));
        }
        if lits.literals.len() > 0 {
            strats.push(GlobSetMatchStrategyS::Literal(lits));
        }
        if !suffixes.is_empty() {
            let sx = suffixes.suffix();
            strats.push(GlobSetMatchStrategyS::Suffix(sx));
        }
        if !prefixes.is_empty() {
            let px = prefixes.prefix();
            strats.push(GlobSetMatchStrategyS::Prefix(px));
        }
        if required_exts.exts.events.len() > 0 {
            let rxe = required_exts.build();
            strats.push(GlobSetMatchStrategyS::RequiredExtension(rxe));
        }
        if !base_regexes.is_empty() {
            let brx = base_regexes.regex_set();
            strats.push(GlobSetMatchStrategyS::Regex(RegexSetStrategy {
                regexes: brx.0,
                map: brx.1,
                basename: true,
            }));
        }
        if !regexes.is_empty() {
            let rx = regexes.regex_set();
            strats.push(GlobSetMatchStrategyS::Regex(RegexSetStrategy {
                regexes: rx.0,
                map: rx.1,
                basename: false,
            }));
        }
        GlobSet { len: rows.len(), strats }
    }
}

/// The char-column strategy builder (the regex lanes' builder twin:
/// upstream's MultiStrategyBuilder over String payloads, lib.rs:
/// 1032-1084; the byte-lane arms route through
/// MultiStrategyBuilder, this twin carries the pattern strings).
pub struct CharStrategyBuilder {
    pub lits: Vec<Vec<char>>,
    pub map: Vec<usize>,
    pub longest: usize,
}

impl CharStrategyBuilder {
    /// Origin Rust (lib.rs:1040-1041): the empty builder.
    pub fn new() -> (r: CharStrategyBuilder)
        ensures
            r.lits@ == Seq::empty(),
            r.map@ == Seq::empty(),
            r.longest == 0,
    {
        CharStrategyBuilder { lits: Vec::new(), map: Vec::new(), longest: 0 }
    }

    /// Origin Rust (lib.rs:1044-1050): the lockstep push pair.
    pub fn add(&mut self, global_index: usize, literal: Vec<char>)
        ensures
            final(self).lits@.len() == old(self).lits@.len() + 1,
            final(self).lits@.subrange(0, old(self).lits@.len() as int) == old(self).lits@,
            final(self).lits@.index(old(self).lits@.len() as int)@ == literal@,
            final(self).map@ == old(self).map@.push(global_index),
            final(self).map@.len() == old(self).map@.len() + 1,
            final(self).longest
                == (if literal.len() > old(self).longest {
                    literal.len()
                } else {
                    old(self).longest
                }),
    {
        if literal.len() > self.longest {
            self.longest = literal.len();
        }
        self.map.push(global_index);
        self.lits.push(literal);
    }

    /// The regex-set adapter (lib.rs:1068-1079's regex_set(): the
    /// trusted new_regex_set compiles the strings; the twin carries
    /// them and the map/longest columns).
    pub fn regex_set(self) -> (r: (Vec<Vec<char>>, Vec<usize>))
        ensures
            r.0@ == self.lits@,
            r.1@ == self.map@,
    {
        (self.lits, self.map)
    }

    /// Origin Rust (lib.rs:1081-1083): the is_empty gate.
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r <==> self.lits@.len() == 0,
    {
        self.lits.len() == 0
    }
}

/// Trigger carrier: every bag value lives under the domain bound.
pub open spec fn spec_bag_bounded(buf: Seq<usize>, k: int, bound: int) -> bool {
    0 <= buf.index(k) < bound
}

/// The prefix carry of a push (same indexes, same values).
pub proof fn lemma_push_carry(pre: Seq<usize>, v: usize)
    ensures
        forall|k: int|
            #![trigger pre.push(v).index(k)]
            0 <= k < pre.len() as int ==> pre.push(v).index(k) == pre.index(k),
{
    assert forall|k: int| 0 <= k < pre.len() as int implies
        pre.push(v).index(k) == pre.index(k) by {
        vstd::seq::lemma_seq_push_index_different(pre, v, k);
    }
}

// ---------------------------------------------------------------------------
// Part K (GL8): the canonicalization iff face (GL7's deferred #2) --
// has(final, x) <==> (x in the walked band && has(bag, x)), assembled
// from the already-green atoms (the scan step/miss family
// lemma_scan_{step_hit,step_miss,miss_cell,hit_grows,all_miss},
// lemma_push_membership, lemma_singleton_has, lemma_add_empty_*,
// the p_recpost call-site instantiation ruling for the exec twin).
//
// Atomic table (the >40-line discipline, #GL-13(8)):
//   A1  lemma_bag_has_index_iff : has <==> exists hitting cell (via
//       step_hit/hit_grows and miss_cell/all_miss);
//   A2  lemma_add_has_split    : has(a.add(b), x) <==> has(a,x) ||
//       has(b,x) (A1 on c = a.add(b) plus the vstd add-index cell
//       translations);
//   A3  the spec walk's membership iff: BLOCKED by the int/usize
//       round-trip wall at the `seq![v as usize]` lead (the #GL-13(5)
//       ruling, shape note below) -- the iff lands on the exec
//       twin's fourth postcondition instead (A7);
//   A5  lemma_collect_has_iff  : has(spec_set_collect_upto(...,n),x)
//       <==> exists|q<n| has(strategy q's list, x) (A2 by induction);
//   A6  lemma_set_collect_has_iff : the full-column collect face;
//   A7  the exec twin's fourth postcondition (canonicalize_rec now
//       carries the same iff; the frame proof rides A2 +
//       lemma_singleton_has and the recursive postcondition
//       instantiated at the call site -- the return-form ruling).
// ---------------------------------------------------------------------------

/// A1's extraction half: a budgeted scan hit carries a hitting
/// cell (induction over the budget; the recursive step rides the
/// miss/step lemmas).
pub proof fn lemma_scan_hit_witness(s: Seq<usize>, x: int, n: int)
    requires
        0 < n <= s.len() as int,
        spec_has_scan(s, x, n),
    ensures
        exists|k: int| 0 <= k < n && s.index(k) == x,
    decreases n,
{
    if s.index(n - 1) == x {
        // the top cell of the budget is the witness
        assert(0 <= n - 1 < n);
        assert(s.index(n - 1) == x);
    } else {
        lemma_scan_step_miss(s, x, n);
        assert(spec_has_scan(s, x, n - 1));
        if n - 1 > 0 {
            lemma_scan_hit_witness(s, x, n - 1);
        } else {
            reveal_with_fuel(spec_has_scan, 2);
            assert(false);
        }
    }
}

/// A1: full-bag membership is exactly the existence of a hitting cell.
pub proof fn lemma_bag_has_index_iff(s: Seq<usize>, x: int)
    ensures
        spec_bag_has(s, x) <==> exists|k: int| 0 <= k < s.len() as int && s.index(k) == x,
{
    // (<=) any hitting cell proves the full-budget scan
    assert forall|k: int| 0 <= k < s.len() as int && s.index(k) == x implies
        spec_bag_has(s, x) by {
        lemma_scan_step_hit(s, x, k);
        lemma_scan_hit_grows(s, x, k + 1, s.len() as int);
    }
    if spec_bag_has(s, x) {
        // (=>) the scan hit carries a witness cell
        lemma_scan_hit_witness(s, x, s.len() as int);
    } else {
        // (=>) full-budget miss: every cell misses (no witness can
        // exist; a purely first-order fold over the per-cell facts)
        assert forall|k: int| 0 <= k < s.len() as int implies s.index(k) != x by {
            lemma_scan_miss_cell(s, x, s.len() as int, k);
        }
    }
}

/// A2: membership splits over seq add (the master atom of the walk's
/// iff composition; the cell translations across the add boundary
/// ride the free wrappers below, each direction its own lemma -- the
/// by-block antecedent-blindness of the direct proof is the recorded
/// GL8 batch lesson).
pub proof fn lemma_add_has_split(a: Seq<usize>, b: Seq<usize>, x: int)
    ensures
        spec_bag_has(a.add(b), x) <==> (spec_bag_has(a, x) || spec_bag_has(b, x)),
{
    lemma_add_has_fwd_a(a, b, x);
    lemma_add_has_fwd_b(a, b, x);
    lemma_add_has_bwd(a, b, x);
}

/// A2's (=>) half: the head witness carries (choose-extraction on
/// the A1 view; the antecedent-blind by-block lesson taken).
pub proof fn lemma_add_has_fwd_a(a: Seq<usize>, b: Seq<usize>, x: int)
    ensures
        spec_bag_has(a, x) ==> spec_bag_has(a.add(b), x),
{
    if spec_bag_has(a, x) {
        lemma_bag_has_index_iff(a, x);
        assert(exists|k: int| 0 <= k < a.len() as int && a.index(k) == x);
        let witness = choose|k: int| 0 <= k < a.len() as int && a.index(k) == x;
        assert(a.add(b).len() == (a.len() + b.len()) as int);
        assert(0 <= witness < a.add(b).len() as int);
        assert(a.add(b).index(witness) == a.index(witness));
        lemma_bag_has_index_iff(a.add(b), x);
        assert(exists|k: int| 0 <= k < a.add(b).len() as int && a.add(b).index(k) == x);
    }
}

/// A2's (=>) half: the tail witness carries (shifted by a.len()).
pub proof fn lemma_add_has_fwd_b(a: Seq<usize>, b: Seq<usize>, x: int)
    ensures
        spec_bag_has(b, x) ==> spec_bag_has(a.add(b), x),
{
    if spec_bag_has(b, x) {
        lemma_bag_has_index_iff(b, x);
        assert(exists|k: int| 0 <= k < b.len() as int && b.index(k) == x);
        let witness = choose|k: int| 0 <= k < b.len() as int && b.index(k) == x;
        assert(a.add(b).len() == (a.len() + b.len()) as int);
        let shift = a.len() as int;
        assert(0 <= witness);
        assert(0 <= shift);
        assert(witness + shift < a.add(b).len() as int);
        assert(a.add(b).index(witness + shift) == b.index(witness));
        lemma_bag_has_index_iff(a.add(b), x);
        assert(exists|k: int| 0 <= k < a.add(b).len() as int && a.add(b).index(k) == x);
    }
}

/// A2's (<=) half: the combined witness decomposes.
pub proof fn lemma_add_has_bwd(a: Seq<usize>, b: Seq<usize>, x: int)
    ensures
        spec_bag_has(a.add(b), x)
            ==> (spec_bag_has(a, x) || spec_bag_has(b, x)),
{
    if spec_bag_has(a.add(b), x) {
        lemma_bag_has_index_iff(a.add(b), x);
        assert(exists|k: int|
            0 <= k < a.add(b).len() as int && a.add(b).index(k) == x);
        let witness = choose|k: int|
            0 <= k < a.add(b).len() as int && a.add(b).index(k) == x;
        assert(a.add(b).len() == (a.len() + b.len()) as int);
        if witness < a.len() as int {
            lemma_bag_has_index_iff(a, x);
            assert(a.add(b).index(witness) == a.index(witness));
            assert(exists|k: int| 0 <= k < a.len() as int && a.index(k) == x);
        } else {
            lemma_bag_has_index_iff(b, x);
            let shifted = witness - a.len() as int;
            assert(0 <= shifted < b.len() as int);
            assert(a.add(b).index(witness) == b.index(shifted));
            assert(exists|k: int| 0 <= k < b.len() as int && b.index(k) == x);
        }
    }
}

/// The add-index cell translations as free lemmas (precondition-free
/// wrappers whose ensures carry the implication inline -- the standard
/// carrier for quantified facts; the vstd originals are called from
/// inside the branch guards where the bounds are assumed).
pub proof fn lemma_add_index1_free(a: Seq<usize>, b: Seq<usize>, k: int)
    ensures
        0 <= k < a.len() as int ==> a.add(b).index(k) == a.index(k),
{
    if 0 <= k < a.len() as int {
        assert(a.add(b).len() == (a.len() + b.len()) as int);
        vstd::seq::lemma_seq_add_index1(a, b, k);
    }
}

pub proof fn lemma_add_index2_free(a: Seq<usize>, b: Seq<usize>, k: int)
    ensures
        0 <= k < b.len() as int
            ==> a.add(b).index(k + a.len() as int) == b.index(k),
{
    if 0 <= k < b.len() as int {
        assert(0 <= a.len() as int);
        assert(k + a.len() as int >= a.len() as int);
        assert(a.add(b).len() == (a.len() + b.len()) as int);
        vstd::seq::lemma_seq_add_index2(a, b, k + a.len() as int);
    }
}

/// A3 (shape note): the spec-layer walk face `has(spec_walk_value(
/// bag, v, bound), x) <==> v <= x < bound && has(bag, x)` at a
/// VARIABLE `v: int` recurses into the walk's own `seq![v as usize]`
/// lead cell -- the int->usize->int round-trip wall (#GL-13(5), the
/// GL6/GL7 rulings: even ground cast-chains refuse; by (bit_vector)
/// rejects Int). The iff therefore lands on the EXEC twin's fourth
/// postcondition instead (canonicalize_rec below carries `v: usize`
/// natively -- the GL6 prescribing form "carry the usize" -- and its
/// ensures now states the same iff); the A5/A6 collect faces below
/// have no cast site and close generically.

/// A5: the collected stream's membership is the per-strategy
/// disjunction (induction over the strategy column; each frame's
/// add splits by A2).
pub proof fn lemma_collect_has_iff(
    strats: Seq<GlobSetMatchStrategyS>,
    cand: &Candidate,
    n: int,
    x: int,
)
    requires
        0 <= n <= strats.len(),
    ensures
        spec_bag_has(spec_set_collect_upto(strats, cand, n), x)
            <==> exists|q: int| 0 <= q < n
                && spec_bag_has(spec_gsm_matches_list(&strats.index(q), cand), x),
    decreases n,
{
    if n > 0 {
        lemma_collect_has_iff(strats, cand, n - 1, x);
        lemma_add_has_split(
            spec_set_collect_upto(strats, cand, n - 1),
            spec_gsm_matches_list(&strats.index(n - 1), cand),
            x,
        );
    } else {
        // the empty collection keeps nothing; the disjunction's range
        // is empty
        reveal_with_fuel(spec_set_collect_upto, 2);
        assert(spec_bag_has(Seq::<usize>::empty(), x) == false);
    }
}

/// A6: the full-column collect face (the GM15 stream iff: the
/// pre-canonicalization bag contains exactly the strategy lanes'
/// listed indices -- the canonicalized set value rides the exec
/// twin's fourth postcondition, see A3's shape note).
pub proof fn lemma_set_collect_has_iff(
    strats: Seq<GlobSetMatchStrategyS>,
    cand: &Candidate,
    x: int,
)
    ensures
        spec_bag_has(spec_set_collect(strats, cand), x)
            <==> exists|q: int| 0 <= q < strats.len()
                && spec_bag_has(spec_gsm_matches_list(&strats.index(q), cand), x),
{
    assert(spec_set_collect(strats, cand)
        == spec_set_collect_upto(strats, cand, strats.len() as int));
    lemma_collect_has_iff(strats, cand, strats.len() as int, x);
}

/// The set-level matches_all's bar channel: one failing strategy
/// falsifies the set-level conjunction.
pub proof fn lemma_set_all_bar(
    strats: Seq<GlobSetMatchStrategyS>,
    cand: &Candidate,
    q: int,
)
    requires
        0 <= q < strats.len() as int,
        !spec_gsm_matches_all(&strats.index(q), cand),
    ensures
        !spec_set_matches_all(strats, cand),
{
}

/// The set-level is_match's empty channel: every strategy missing
/// falsifies the set-level exists.
pub proof fn lemma_set_im_none(
    strats: Seq<GlobSetMatchStrategyS>,
    cand: &Candidate,
)
    requires
        forall|q: int|
            0 <= q < strats.len() as int ==> !spec_gsm_is_match(&strats.index(q), cand),
    ensures
        !spec_set_is_match(strats, cand),
{
}

/// The set-level is_match's witness channel: one hitting strategy
/// satisfies the set-level exists (the harness rows drive the
/// per-strategy faces themselves; this packs the witness into the
/// set-level query's quantifier).
pub proof fn lemma_set_im_witness(
    strats: Seq<GlobSetMatchStrategyS>,
    cand: &Candidate,
    q: int,
)
    requires
        0 <= q < strats.len() as int,
        spec_gsm_is_match(&strats.index(q), cand),
    ensures
        spec_set_is_match(strats, cand),
{
}

/// The BasenameLiteral empty-basename guard behavior (GL7's deferred
/// #4, the GL6 KAT rows' theorem form): with an empty basename the
/// dispatch pair answers false/empty -- the guard is load-bearing
/// (the literal itself could equal the virtual "..", lib.rs:1421's
/// parent-component rows).
pub proof fn lemma_baselit_empty_basename_guard(s: &GlobSetMatchStrategyS, cand: &Candidate)
    requires
        cand.basename.view().len() == 0,
        *s is BasenameLiteral,
    ensures
        !spec_gsm_is_match(s, cand),
        !spec_gsm_matches_all(s, cand),
        spec_gsm_matches_list(s, cand) == Seq::empty(),
        spec_gsm_list_nonempty_iff(s, cand),
{
}

} // verus!

/// Single-file driver anchor (the harness zone references this root via
/// #[path]; nothing is re-copied).
fn main() {}
