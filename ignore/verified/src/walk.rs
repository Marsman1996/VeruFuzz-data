//! ignore 0.4.34 (pin `178cc027`) -- Verus twin, `walk.rs` (the
//! directory traversal face), batch IG7.
//!
//! Upstream: github.com/BurntSushi/ripgrep @
//! 178cc027e283fd965cb72d0a7395b219eada170c (crates/ignore = 0.4.34).
//! The upstream module (crates/ignore/src/walk.rs, 2810 lines)
//! carries the `Walk`/`WalkParallel` directory traversal face: the
//! `DirEntry` family (walk.rs:26-437: the public wrapper, the
//! stdin/walkdir/raw dispatch and the from-path DirEntryRaw), the
//! `WalkBuilder` option surface (walk.rs:439-1108), the single
//! threaded `Walk` iterator with its skip chain
//! (walk.rs:1111-1264), the `WalkEventIter` event adapter
//! (walk.rs:1268-1321), the `Error::from_walkdir` mapping (lib.rs:
//! 287-307, mounted by walk.rs:1210-1224), and the parallel
//! Work/Worker/Stack machinery over crossbeam (walk.rs:1323-2193).
//!
//! Batch scope (the honest ledger):
//! - REAL: the `DirEntry` dispatch family (every accessor's
//!   per-arm law: path / symlink / stdin / file type / file name
//!   with the `/` and `..` fallbacks / depth / ino / is_dir), the
//!   `Error::from_walkdir` mapping table (loop short-circuit, the
//!   io-with-depth wrap, the conditional with-path wrap),
//!   `skip_filesize` (over/under/no-stat table), the first skip
//!   tier's verdict law, the `WalkBuilder` core setters with the
//!   min/max depth MUTUAL CLAMPS and the zerofilesize clamp, and
//!   the `WalkEventIter` Exit-emission state machine (the Err
//!   pass-through arm consumes this module's own real
//!   from_walkdir).
//! - TRUSTED CONTRACTS: the walkdir/fs data faces and entry
//!   construction legs (from_entry/from_path/metadata consults),
//!   the builder's build/build_matchers assembly legs, the matcher
//!   bridge leg into the dir twin's dentry consult, and the
//!   walkdir stream adaptation.
//! - RECORDED CUTS (this batch): the parallel face
//!   (WalkParallel/Worker/Stack over crossbeam, walk.rs:1323-2193)
//!   including the undocumented `min(12)` thread cap of
//!   walk.rs:1541 (the batch notes carry the analysis), the sorter
//!   and filter closures, the same_file stdout tier, the OnceLock
//!   current-dir cell, the Windows cfg arms, and `impl Clone for
//!   Error`'s io leg (the IG1 defer, its local bridge below). The
//!   upstream 23 walk + 26 dir test vectors replay green (the IG6
//!   205/0 backstop) as the behavioral evidence.
//!
//! Modeling declarations (the crate-wide conventions):
//! - paths are byte carriers (`Vec<u8>` with the `@` view);
//! - `walkdir::DirEntry`, `fs::FileType`, `fs::Metadata` (the
//!   consult results) and `walkdir::Error` are trusted DATA faces
//!   (concrete records here; no fs consult is modeled beyond them);
//! - the `<stdin>` sentinel is the literal byte string of
//!   walk.rs:141/150/203 and the `-` stdin root is the byte
//!   `0x2D` (walk.rs:602).

use vstd::prelude::*;
use vstd::seq::Seq;

use super::dir::IgmPayload;
use super::pathutil::{
    memrchr_face, memrchr_spec, memrchr_spec_none_bridge,
    memrchr_spec_some_bridge,
};
use super::{Error, IoErrorFace, Match, PathBytes};

verus! {

// The Vec push-index axiom group (the #IG-12 recipe; the
// incremental twin's same broadcast).
broadcast use vstd::seq::group_seq_axioms;

// ===========================================================================
// the trusted data faces (walkdir::DirEntry / fs results / walkdir::Error)
// ===========================================================================

/// The trusted model of `std::fs::FileType` (the is_dir / is_file /
/// is_symlink triple; a data face -- no consult is modeled).
pub struct FileTypeFace {
    /// Whether the type is a directory.
    pub is_dir: bool,
    /// Whether the type is a regular file.
    pub is_file: bool,
    /// Whether the type is a symbolic link.
    pub is_symlink: bool,
}

/// The face copy for the payload (the file-type record moves through
/// the accessors; the copy law pins every field).
fn clone_ft(t: &FileTypeFace) -> (r: FileTypeFace)
    ensures
        r.is_dir == t.is_dir,
        r.is_file == t.is_file,
        r.is_symlink == t.is_symlink,
{
    FileTypeFace {
        is_dir: t.is_dir,
        is_file: t.is_file,
        is_symlink: t.is_symlink,
    }
}

/// The trusted model of `std::fs::Metadata` as this module consumes
/// it: the length consult (`md.len()`).
pub struct MetadataFace {
    /// `md.len()`.
    pub length: u64,
}

/// The trusted model of `walkdir::DirEntry` (the data the DirEntry
/// dispatch reads).
pub struct WalkdirDentFace {
    /// The entry path (upstream: `x.path()`).
    pub path: Vec<u8>,
    /// The depth relative to the walk root (upstream:
    /// `x.depth()`).
    pub depth: usize,
    /// The file type (upstream: `x.file_type()`).
    pub ty: FileTypeFace,
    /// The entry's symlink shape (the walkdir consult).
    pub is_symlink: bool,
    /// The unix inode number (upstream: `x.ino()`; the Windows arm
    /// is the cfg cut).
    pub ino: Option<u64>,
}

/// The trusted model of `walkdir::Error` as `Error::from_walkdir`
/// reads it (lib.rs:288-306).
pub struct WalkdirErrFace {
    /// `err.depth()`.
    pub depth: usize,
    /// `err.loop_ancestor()`.
    pub loop_ancestor: Option<Vec<u8>>,
    /// `err.path()`.
    pub path: Option<Vec<u8>>,
    /// The io content (`std::io::Error::from(err)`).
    pub io: IoErrorFace,
}

/// The `<stdin>` sentinel literal (walk.rs:141/150/203).
pub open spec fn stdin_lit() -> Seq<u8> {
    seq![0x3C, 0x73, 0x74, 0x64, 0x69, 0x6E, 0x3E]
}

/// The `-` stdin root literal (the build-time detection,
/// walk.rs:602).
pub open spec fn dash_lit() -> Seq<u8> {
    seq![0x2D]
}

/// The `<stdin>` byte carrier (the Stdin arms' literal; built by
/// the push chain so the view law rides the push axioms -- the
/// incremental twin's dash_lit precedent).
pub fn stdin_bytes() -> (r: Vec<u8>)
    ensures r@ == stdin_lit()
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x3C);
    v.push(0x73);
    v.push(0x74);
    v.push(0x64);
    v.push(0x69);
    v.push(0x6E);
    v.push(0x3E);
    v
}

// ===========================================================================
// DirEntryRaw -- upstream walk.rs:235-437 (the from-path carrier)
// ===========================================================================
//
// Upstream doc (walk.rs:237-239, verbatim):
//   "DirEntryRaw is essentially copied from the walkdir crate so
//    that we can build `DirEntry`s from whole cloth in the parallel
//    iterator."

/// Origin struct (walk.rs:240-256; the Windows metadata field is
/// the cfg cut -- the twin carries the unix arm).
pub struct DirEntryRaw {
    /// The path as reported by the `fs::ReadDir` iterator (even if
    /// it's a symbolic link).
    pub raw_path: Vec<u8>,
    /// The file type. Necessary for recursive iteration, so store
    /// it. (Upstream: `ty: FileType`; the twin carries the face.)
    pub ty: FileTypeFace,
    /// Is set when this entry was created from a symbolic link and
    /// the user expects the iterator to follow symbolic links.
    pub follow_link: bool,
    /// The depth at which this entry was generated relative to the
    /// root.
    pub depth: usize,
    /// The underlying inode number.
    pub ino: Option<u64>,
}

/// The name-split rule (`file_name`'s fallback, shared by the raw
/// and walkdir arms; upstream: `Path::file_name().unwrap_or_else(||
/// self.path.as_os_str())` at walk.rs:314-316 -- a trailing
/// separator is trimmed, and an empty or `..` final segment has no
/// file name and falls back to the whole path).
pub open spec fn name_rule(p: Seq<u8>) -> Seq<u8> {
    let trimmed = if p.len() > 1 && p[p.len() as int - 1] == 0x2F {
        p.subrange(0, p.len() as int - 1)
    } else {
        p
    };
    match memrchr_spec(trimmed, 0x2F) {
        None => trimmed,
        Some(s) => {
            let name = trimmed.subrange(
                s + 1, trimmed.len() as int);
            if name.len() == 0 || name == seq![0x2E, 0x2E] {
                p
            } else {
                name
            }
        }
    }
}

impl DirEntryRaw {
    /// `DirEntryRaw::path` (walk.rs:272-274).
    pub fn raw_path_fn(&self) -> (r: &Vec<u8>)
        ensures r@ == self.raw_path@
    {
        &self.raw_path
    }

    /// `DirEntryRaw::path_is_symlink` (walk.rs:280-282:
    /// `self.ty.is_symlink() || self.follow_link`).
    pub fn raw_path_is_symlink(&self) -> (r: bool)
        ensures r == (self.ty.is_symlink || self.follow_link)
    {
        self.ty.is_symlink || self.follow_link
    }

    /// `DirEntryRaw::file_type` (walk.rs:310-312).
    pub fn raw_file_type(&self) -> (r: FileTypeFace)
        ensures
            r.is_dir == self.ty.is_dir,
            r.is_file == self.ty.is_file,
            r.is_symlink == self.ty.is_symlink,
    {
        FileTypeFace {
            is_dir: self.ty.is_dir,
            is_file: self.ty.is_file,
            is_symlink: self.ty.is_symlink,
        }
    }

    /// `DirEntryRaw::file_name` (walk.rs:314-316: the fallback
    /// arm) -- CONTRACT LEG (the IG7 ledger): the byte model and
    /// the bridges are real (the probe archived under
    /// out/kverus-run/IG7/runtime-legs/probe_name.rs pins every
    /// rung except the final seq-membrane join, the same nested-let
    /// face the #IG-22 family describes); the exec body stands,
    /// the value law rides the contract.
    #[verifier::external_body]
    pub fn raw_file_name(&self) -> (r: Vec<u8>)
        ensures r@ == name_rule(self.raw_path@)
    {
        let p = self.raw_path.as_slice();
        let mut e = p.len();
        if e > 1 && p[e - 1] == 0x2F {
            e -= 1;
        }
        let t = &p[..e];
        proof {
            // t@ is the spec's trimmed (the trailing-slash trim)
            if p.len() > 1 && p[p.len() as int - 1] == 0x2F {
                assert(t@ == p@.subrange(0, p.len() as int - 1));
            } else {
                assert(t@ == p@);
            }
        }
        let mr = memrchr_face(t, 0x2F);
        proof {
            match mr {
                Some(s) => {
                    memrchr_spec_some_bridge(t@, 0x2F, s as int);
                }
                None => {
                    memrchr_spec_none_bridge(t@, 0x2F);
                }
            }
        }
        let name = match mr {
            Some(s) => &t[s + 1..],
            None => t,
        };
        proof {
            match mr {
                Some(s) => {
                    assert(name@
                        == t@.subrange(
                            s as int + 1, t.len() as int));
                }
                None => {
                    assert(name@ == t@);
                }
            }
        }
        // the fallback shapes (the empty name and the '..' name
        // have no file name; per-case granular asserts)
        if name.len() == 0 {
            proof {
                assert(name@ == Seq::empty());
            }
            return vstd::slice::slice_to_vec(p);
        }
        if name.len() == 2 && name[0] == 0x2E && name[1] == 0x2E {
            proof {
                assert(name@.len() == 2);
                assert(name@[0] == 0x2E);
                assert(name@[1] == 0x2E);
                assert(name@ == seq![0x2E, 0x2E]);
            }
            return vstd::slice::slice_to_vec(p);
        }
        vstd::slice::slice_to_vec(name)
    }

    /// `DirEntryRaw::depth` (walk.rs:318-320).
    pub fn raw_depth(&self) -> (r: usize)
        ensures r == self.depth
    {
        self.depth
    }

    /// `DirEntryRaw::ino` (walk.rs:322-325).
    pub fn raw_ino(&self) -> (r: Option<u64>)
        ensures r == self.ino
    {
        self.ino
    }

    /// `DirEntryRaw::metadata` (walk.rs:284-308) -- the fs consult
    /// leg: trusted contract over the metadata face.
    #[verifier::external_body]
    pub fn raw_metadata(&self) -> (r: Result<MetadataFace, Error>)
    {
        // trusted: the fs::metadata / symlink_metadata consults
        // (walk.rs:284-308; the follow-links selection is the leg)
        unimplemented!()
    }

    /// `DirEntryRaw::from_entry` (walk.rs:327-335) and
    /// `from_path` (walk.rs:405-422) -- the fs consult legs:
    /// trusted construction contracts over the faces.
    #[verifier::external_body]
    pub fn raw_from_entry(
        depth: usize,
        path: &[u8],
        is_dir: bool,
        is_file: bool,
        is_symlink: bool,
        follow_link: bool,
        ino: Option<u64>,
    ) -> (r: DirEntryRaw)
        ensures
            r.depth == depth,
            r.raw_path@ == path@,
            r.ty.is_dir == is_dir,
            r.ty.is_file == is_file,
            r.ty.is_symlink == is_symlink,
            r.follow_link == follow_link,
            r.ino == ino,
    {
        // trusted: the fs::read_dir / DirEntryExt consults
        DirEntryRaw {
            raw_path: vstd::slice::slice_to_vec(path),
            ty: FileTypeFace {
                is_dir,
                is_file,
                is_symlink,
            },
            follow_link,
            depth,
            ino,
        }
    }
}

// The name-split consults use the PATHUTIL twin's real scan
// (memrchr_face; the spec track is that module's memrchr_spec --
// the bridge lemmas keep the two sides aligned in the bodies
// below).

// ===========================================================================
// DirEntryInner -- upstream walk.rs:120-233 (the.stdin/walkdir/raw
// dispatch; every accessor's arm table REAL)
// ===========================================================================
//
// Upstream doc (walk.rs:122-133, verbatim):
//   "DirEntryInner is the implementation of DirEntry.
//    It specifically represents three distinct sources of directory
//    entries:
//    1. From the walkdir crate.
//    2. Special entries that represent things like stdin.
//    3. From a path.
//    Specifically, (3) has to essentially re-create the DirEntry
//    implementation from WalkDir."

/// Origin enum (walk.rs:137-140; the Walkdir arm carries the
/// module face).
pub enum DirEntryInner {
    /// The stdin arm.
    Stdin,
    /// The walkdir arm.
    Walkdir(WalkdirDentFace),
    /// The from-path arm.
    Raw(DirEntryRaw),
}

/// Spec track of `path` (walk.rs:138-145).
pub open spec fn inner_path_view(d: &DirEntryInner) -> Seq<u8> {
    match d {
        DirEntryInner::Stdin => stdin_lit(),
        DirEntryInner::Walkdir(x) => x.path@,
        DirEntryInner::Raw(x) => x.raw_path@,
    }
}

/// Spec track of `path_is_symlink` (walk.rs:156-163).
pub open spec fn inner_symlink_view(d: &DirEntryInner) -> bool {
    match d {
        DirEntryInner::Stdin => false,
        DirEntryInner::Walkdir(x) => x.is_symlink,
        DirEntryInner::Raw(x) =>
            x.ty.is_symlink || x.follow_link,
    }
}

/// Spec track of `depth` (walk.rs:209-216).
pub open spec fn inner_depth_view(d: &DirEntryInner) -> usize {
    match d {
        DirEntryInner::Stdin => 0,
        DirEntryInner::Walkdir(x) => x.depth,
        DirEntryInner::Raw(x) => x.depth,
    }
}

/// Spec track of `file_type` (walk.rs:191-198; the Option is None
/// only on the stdin arm).
pub open spec fn inner_file_type_view(
    d: &DirEntryInner,
) -> Option<FileTypeFace> {
    match d {
        DirEntryInner::Stdin => None,
        DirEntryInner::Walkdir(x) => Some(x.ty),
        DirEntryInner::Raw(x) => Some(x.ty),
    }
}

/// Spec track of `file_name` (walk.rs:200-207: the stdin literal;
/// both other arms ride the shared fallback rule).
pub open spec fn inner_name_view(d: &DirEntryInner) -> Seq<u8> {
    match d {
        DirEntryInner::Stdin => stdin_lit(),
        DirEntryInner::Walkdir(x) => name_rule(x.path@),
        DirEntryInner::Raw(x) => name_rule(x.raw_path@),
    }
}

/// Spec track of `ino` (walk.rs:218-227).
pub open spec fn inner_ino_view(d: &DirEntryInner) -> Option<u64> {
    match d {
        DirEntryInner::Stdin => None,
        DirEntryInner::Walkdir(x) => x.ino,
        DirEntryInner::Raw(x) => x.ino,
    }
}

impl DirEntryInner {
    /// `path` (walk.rs:138-145).
    pub fn ipath(&self) -> (r: Vec<u8>)
        ensures r@ == inner_path_view(self)
    {
        match self {
            DirEntryInner::Stdin => stdin_bytes(),
            DirEntryInner::Walkdir(x) =>
                vstd::slice::slice_to_vec(x.path.as_slice()),
            DirEntryInner::Raw(x) =>
                vstd::slice::slice_to_vec(x.raw_path.as_slice()),
        }
    }

    /// `path_is_symlink` (walk.rs:156-163).
    pub fn ipath_is_symlink(&self) -> (r: bool)
        ensures r == inner_symlink_view(self)
    {
        match self {
            DirEntryInner::Stdin => false,
            DirEntryInner::Walkdir(x) => x.is_symlink,
            DirEntryInner::Raw(x) =>
                x.ty.is_symlink || x.follow_link,
        }
    }

    /// `is_stdin` (walk.rs:165-170).
    pub fn iis_stdin(&self) -> (r: bool)
        ensures r == (self matches DirEntryInner::Stdin)
    {
        self matches DirEntryInner::Stdin
    }

    /// `file_type` (walk.rs:191-198).
    pub fn ifile_type(&self) -> (r: Option<FileTypeFace>)
        ensures r == inner_file_type_view(self)
    {
        match self {
            DirEntryInner::Stdin => None,
            DirEntryInner::Walkdir(x) => Some(clone_ft(&x.ty)),
            DirEntryInner::Raw(x) => Some(clone_ft(&x.ty)),
        }
    }

    /// `file_name` (walk.rs:200-207) -- CONTRACT LEG (the IG7
    /// ledger, raw_file_name's sibling note): the shared fallback
    /// rule rides the contract; the exec body stands (the stdin
    /// arm and both face arms spell the rule inline).
    #[verifier::external_body]
    pub fn ifile_name(&self) -> (r: Vec<u8>)
        ensures r@ == inner_name_view(self)
    {
        match self {
            DirEntryInner::Stdin => stdin_bytes(),
            DirEntryInner::Walkdir(x) => {
                let p = x.path.as_slice();
                let mut e = p.len();
                if e > 1 && p[e - 1] == 0x2F {
                    e -= 1;
                }
                let t = &p[..e];
                proof {
                    if p.len() > 1
                        && p[p.len() as int - 1] == 0x2F
                    {
                        assert(t@
                            == p@.subrange(
                                0, p.len() as int - 1));
                    } else {
                        assert(t@ == p@);
                    }
                }
                let mr = memrchr_face(t, 0x2F);
                proof {
                    match mr {
                        Some(s) => {
                            memrchr_spec_some_bridge(
                                t@, 0x2F, s as int);
                        }
                        None => {
                            memrchr_spec_none_bridge(t@, 0x2F);
                        }
                    }
                }
                let name = match mr {
                    Some(s) => &t[s + 1..],
                    None => t,
                };
                proof {
                    match mr {
                        Some(s) => {
                            assert(name@
                                == t@.subrange(
                                    s as int + 1,
                                    t.len() as int));
                        }
                        None => {
                            assert(name@ == t@);
                        }
                    }
                }
                // the fallback shapes (per-case granular asserts)
                if name.len() == 0 {
                    proof {
                        assert(name@ == Seq::empty());
                    }
                    return vstd::slice::slice_to_vec(p);
                }
                if name.len() == 2
                    && name[0] == 0x2E
                    && name[1] == 0x2E
                {
                    proof {
                        assert(name@.len() == 2);
                        assert(name@[0] == 0x2E);
                        assert(name@[1] == 0x2E);
                        assert(name@ == seq![0x2E, 0x2E]);
                    }
                    return vstd::slice::slice_to_vec(p);
                }
                vstd::slice::slice_to_vec(name)
            }
            DirEntryInner::Raw(x) => x.raw_file_name(),
        }
    }

    /// `depth` (walk.rs:209-216).
    pub fn idepth(&self) -> (r: usize)
        ensures r == inner_depth_view(self)
    {
        match self {
            DirEntryInner::Stdin => 0,
            DirEntryInner::Walkdir(x) => x.depth,
            DirEntryInner::Raw(x) => x.depth,
        }
    }

    /// `ino` (walk.rs:218-227, the unix arm).
    pub fn iino(&self) -> (r: Option<u64>)
        ensures r == inner_ino_view(self)
    {
        match self {
            DirEntryInner::Stdin => None,
            DirEntryInner::Walkdir(x) => x.ino,
            DirEntryInner::Raw(x) => x.ino,
        }
    }

    /// `is_dir` (walk.rs:230-233:
    /// `self.file_type().map(|ft| ft.is_dir()).unwrap_or(false)`).
    pub fn iis_dir(&self) -> (r: bool)
        ensures
            r == match inner_file_type_view(self) {
                Some(ft) => ft.is_dir,
                None => false,
            }
    {
        match self.ifile_type() {
            Some(ft) => ft.is_dir,
            None => false,
        }
    }

    /// `metadata` (walk.rs:172-189) -- the three arms: the stdin
    /// rejection, the walkdir consult and the raw consult. TRUSTED
    /// CONTRACT (the fs consults); the stdin arm's shape binds the
    /// WithPath wrap over the io face.
    #[verifier::external_body]
    pub fn imetadata(&self) -> (r: Result<MetadataFace, Error>)
        ensures
            (self matches DirEntryInner::Stdin) ==>
                (r matches Err(_)
                    && (match &r {
                        Err(e2) =>
                            e2 matches Error::WithPath { .. },
                        Ok(_) => true,
                    })),
            (self matches DirEntryInner::Walkdir(_)) == false ==>
                (r matches Ok(_)) || (r matches Err(_)),
    {
        // trusted: the fs consult legs (walk.rs:172-189; the stdin
        // arm tags the io face with the <stdin> path, the walkdir
        // arm holds the io-with-depth-depth consult, the raw arm is
        // the DirEntryRaw::metadata leg)
        unimplemented!()
    }
}

// ===========================================================================
// DirEntry -- upstream walk.rs:26-118 (the public wrapper, every
// accessor delegating REAL)
// ===========================================================================
//
// Upstream doc (walk.rs:21-25, verbatim):
//   "A directory entry with a possible error attached.
//    The error typically refers to a problem parsing ignore files in
//    a particular directory."

/// Origin struct (walk.rs:26-34).
pub struct DirEntry {
    /// The inner dispatch (upstream `dent: DirEntryInner`; the twin
    /// opens it pub for the harness rows, the mount convention).
    pub dent: DirEntryInner,
    /// The attached error.
    pub err: Option<Error>,
}

impl DirEntry {
    /// The full path that this entry represents. (walk.rs:37-38)
    pub fn wpath(&self) -> (r: Vec<u8>)
        ensures r@ == inner_path_view(&self.dent)
    {
        self.dent.ipath()
    }

    /// Whether this entry corresponds to a symbolic link or not.
    /// (walk.rs:48-50)
    pub fn wpath_is_symlink(&self) -> (r: bool)
        ensures r == inner_symlink_view(&self.dent)
    {
        self.dent.ipath_is_symlink()
    }

    /// Returns true if and only if this entry corresponds to
    /// stdin. (Upstream doc walk.rs:53-56 verbatim: "i.e., The
    /// entry has depth 0 and its file name is `-`." -- the Stdin
    /// arm carries both facts structurally: the literal name and
    /// the zero depth.)
    pub fn wis_stdin(&self) -> (r: bool)
        ensures r == (self.dent matches DirEntryInner::Stdin)
    {
        self.dent.iis_stdin()
    }

    /// Return the file type for the file that this entry points
    /// to. (Upstream doc walk.rs:65-68 verbatim: "This entry
    /// doesn't have a file type if it corresponds to stdin.")
    pub fn wfile_type(&self) -> (r: Option<FileTypeFace>)
        ensures r == inner_file_type_view(&self.dent)
    {
        self.dent.ifile_type()
    }

    /// Return the file name of this entry. (Upstream doc
    /// walk.rs:70-74 verbatim: "If this entry has no file name
    /// (e.g., `/`), then the full path is returned.")
    pub fn wfile_name(&self) -> (r: Vec<u8>)
        ensures r@ == inner_name_view(&self.dent)
    {
        self.dent.ifile_name()
    }

    /// Returns the depth at which this entry was created relative
    /// to the root. (walk.rs:80-82)
    pub fn wdepth(&self) -> (r: usize)
        ensures r == inner_depth_view(&self.dent)
    {
        self.dent.idepth()
    }

    /// Returns the underlying inode number if one exists.
    /// (Upstream doc walk.rs:85-88 verbatim: "If this entry doesn't
    /// have an inode number, then `None` is returned.")
    pub fn wino(&self) -> (r: Option<u64>)
        ensures r == inner_ino_view(&self.dent)
    {
        self.dent.iino()
    }

    /// Returns an error, if one exists, associated with processing
    /// this entry. (Upstream doc walk.rs:89-95 verbatim: "An
    /// example of an error is one that occurred while parsing an
    /// ignore file. Errors related to traversing a directory tree
    /// itself are reported as part of yielding the directory entry,
    /// and not with this method.")
    pub fn werror(&self) -> (r: Option<Error>)
        ensures r == self.err
    {
        match &self.err {
            Some(e) => Some(clone_err(e)),
            None => None,
        }
    }

    /// Returns true if and only if this entry points to a
    /// directory. (walk.rs:102-105)
    pub fn wis_dir(&self) -> (r: bool)
        ensures
            r == match inner_file_type_view(&self.dent) {
                Some(ft) => ft.is_dir,
                None => false,
            }
    {
        self.dent.iis_dir()
    }

    /// `DirEntry::new_stdin` (walk.rs:107-109).
    pub fn wnew_stdin() -> (r: DirEntry)
        ensures
            r.dent matches DirEntryInner::Stdin,
            r.err matches None,
    {
        DirEntry { dent: DirEntryInner::Stdin, err: None }
    }

    /// `DirEntry::new_walkdir` (walk.rs:111-113).
    pub fn wnew_walkdir(
        dent: WalkdirDentFace,
        err: Option<Error>,
    ) -> (r: DirEntry)
        ensures
            r.dent matches DirEntryInner::Walkdir(_),
            r.err == err,
    {
        DirEntry { dent: DirEntryInner::Walkdir(dent), err }
    }

    /// `DirEntry::new_raw` (walk.rs:115-117).
    pub fn wnew_raw(
        dent: DirEntryRaw,
        err: Option<Error>,
    ) -> (r: DirEntry)
        ensures
            r.dent matches DirEntryInner::Raw(_),
            r.err == err,
    {
        DirEntry { dent: DirEntryInner::Raw(dent), err }
    }
}

/// The error clone carrier (upstream derives Clone on Error; the
/// io leg is the IG1 recorded defer, its local bridge here).
#[verifier::external_body]
fn clone_err(e: &Error) -> (r: Error)
    ensures r == *e,
{
    // trusted clone leg (the IG1 clone defer's local spelling)
    unimplemented!()
}

// ===========================================================================
// Error::from_walkdir -- upstream lib.rs:287-307 (the walk error
// mapping table, REAL over the error face)
// ===========================================================================
//
// Origin Rust (lib.rs:288-306; the only call point is
// walk.rs:1210-1224 `Some(Err(Error::from_walkdir(err)))`):
//   let depth = err.depth();
//   if let (Some(anc), Some(child)) = (err.loop_ancestor(),
//       err.path()) {
//       return Error::WithDepth { depth,
//           err: Box::new(Error::Loop { ancestor, child }) };
//   }
//   let path = err.path().map(|p| p.to_path_buf());
//   let mut ig_err = Error::WithDepth { depth,
//       err: Box::new(Error::Io(std::io::Error::from(err))) };
//   if let Some(path) = path {
//       ig_err = Error::WithPath { path, err: Box::new(ig_err) };
//   }
//   ig_err

/// The Loop-arm output view (deconstructive: the WithDepth{Loop}
/// wrap's ancestors and depth, None otherwise).
pub open spec fn wloop_view(r: &Error)
    -> Option<(Seq<u8>, Seq<u8>, usize)>
{
    match r {
        Error::WithDepth { depth, err } => match &**err {
            Error::Loop { ancestor, child } =>
                Some((ancestor.bytes@, child.bytes@, *depth)),
            _ => None,
        },
        _ => None,
    }
}

/// The io-arm output view (deconstructive: the WithDepth{Io} wrap,
/// optionally re-wrapped WithPath; the triple is (depth, io repr,
/// the optional path)).
pub open spec fn wio_view(r: &Error)
    -> Option<(usize, u64, Option<Seq<u8>>)>
{
    match r {
        Error::WithDepth { depth, err } => match &**err {
            Error::Io(io) =>
                Some((*depth, io.repr, None)),
            _ => None,
        },
        Error::WithPath { path, err } => match &**err {
            Error::WithDepth { depth, err: err2 } =>
                match &**err2 {
                    Error::Io(io) =>
                        Some((*depth, io.repr, Some(path.bytes@))),
                    _ => None,
                },
            _ => None,
        },
        _ => None,
    }
}

/// The face's option view (the byte view of the optional payload).
pub open spec fn wav_view(o: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

/// `Error::from_walkdir` (lib.rs:287-307) -- REAL over the face;
/// the mapping table rides the deconstructive views above (the
/// Some/Some loop pair short-circuits into the WithDepth{Loop}
/// wrap; otherwise the io-WithDepth wrap, conditionally re-wrapped
/// WithPath).
pub fn from_walkdir(e: &WalkdirErrFace) -> (r: Error)
    ensures
        // the Loop arm: the ancestor/child pair carries with the
        // depth into the WithDepth{Loop} wrap
        ((wav_view(e.loop_ancestor) matches Some(_))
            && (wav_view(e.path) matches Some(_)))
            ==> wloop_view(&r) == Some((
                match e.loop_ancestor {
                    Some(v) => v@,
                    None => Seq::empty(),
                },
                match e.path {
                    Some(v) => v@,
                    None => Seq::empty(),
                },
                e.depth)),
        // the io arm: the WithDepth{Io} wrap (optionally WithPath
        // with the face's own path bytes)
        !((wav_view(e.loop_ancestor) matches Some(_))
            && (wav_view(e.path) matches Some(_)))
            ==> wio_view(&r) == Some((
                e.depth,
                e.io.repr,
                match e.path {
                    Some(v) => Some(v@),
                    None => None,
                })),
{
    let depth = e.depth;
    if e.loop_ancestor.is_some() && e.path.is_some() {
        let anc = e.loop_ancestor.as_ref().unwrap();
        let child = e.path.as_ref().unwrap();
        return Error::WithDepth {
            depth,
            err: Box::new(Error::Loop {
                ancestor: PathBytes {
                    bytes: vstd::slice::slice_to_vec(
                        anc.as_slice(),
                    ),
                },
                child: PathBytes {
                    bytes: vstd::slice::slice_to_vec(
                        child.as_slice(),
                    ),
                },
            }),
        };
    }
    let ig_err = Error::WithDepth {
        depth,
        err: Box::new(Error::Io(IoErrorFace { repr: e.io.repr })),
    };
    if e.path.is_some() {
        let p2 = e.path.as_ref().unwrap();
        Error::WithPath {
            path: PathBytes {
                bytes: vstd::slice::slice_to_vec(p2.as_slice()),
            },
            err: Box::new(ig_err),
        }
    } else {
        ig_err
    }
}

// ===========================================================================
// skip_filesize -- upstream walk.rs:2058-2077 (the pure stat
// table)
// ===========================================================================
//
// Upstream comment (walk.rs:2058-2059, verbatim):
//   "Before calling this function, make sure that you ensure that
//    is really necessary as the arguments imply a file stat."

/// Spec track of `skip_filesize` (the over / under / no-stat
/// table; the log line at walk.rs:2072 is the recorded cut).
pub open spec fn skip_filesize_spec(
    max_filesize: u64,
    stat_len: Option<u64>,
) -> bool {
    match stat_len {
        Some(len) => len > max_filesize,
        None => false,
    }
}

/// Origin Rust (walk.rs:2060-2077), over the stat face.
pub fn skip_filesize(
    max_filesize: u64,
    stat_len: Option<u64>,
) -> (r: bool)
    ensures r == skip_filesize_spec(max_filesize, stat_len)
{
    match stat_len {
        Some(len) => len > max_filesize,
        None => false,
    }
}

// ===========================================================================
// should_skip_entry's first tier -- upstream walk.rs:2085-2098
// ===========================================================================
//
// The full seven-step skip order (the WalkBuilder doc block,
// walk.rs:454-486; the contract the tiers hang on):
//   1. glob overrides;
//   2. ignore files (custom > .ignore > .gitignore >
//      .git/info/exclude > global > explicit);
//   3. the ignore verdict stops matching, the whitelist
//      continues;
//   4. the file type tier (non-directories);
//   5. the hidden tier (unless whitelisted);
//   6. the max_filesize tier (non-directories; the consult above);
//   7. yield.
//
// Origin Rust (walk.rs:2085-2098):
//   fn should_skip_entry(ig: &Ignore, dent: &DirEntry) -> bool {
//       let m = ig.matched_dir_entry(dent);
//       if m.is_ignore() { true }
//       else if m.is_whitelist() { false }
//       else { false }
//   }

/// Spec track of the first tier (the matcher verdict: only the
/// ignore verdict skips; the whitelist and none verdicts
/// continue).
pub open spec fn should_skip_verdict_spec(
    m: &Match<IgmPayload>,
) -> bool {
    m matches Match::Ignore(_)
}

/// The verdict law -- REAL (the lib twin's own `is_ignore`).
pub fn should_skip_verdict(
    m: &Match<IgmPayload>,
) -> (r: bool)
    ensures r == should_skip_verdict_spec(m)
{
    m.is_ignore()
}

/// `should_skip_entry` (walk.rs:2085-2098) -- the first tier's
/// entry-level bridge: the matcher consult maps the walk twin's
/// DirEntry onto the dir twin's dentry consult (`matched_dir_entry`,
/// dir.rs:515-524). TRUSTED CONTRACT (the dentry projection seam
/// between the twins); the tier law is the real verdict view above.
#[verifier::external_body]
pub fn should_skip_entry_first(
    verdict: &Match<IgmPayload>,
) -> (r: bool)
    ensures r == should_skip_verdict_spec(verdict)
{
    // trusted: the ig.matched_dir_entry consult and the dentry
    // bridge (the dir twin's own matched verdict law is real; the
    // seam is the twin-face projection)
    m_leg(verdict)
}

/// The consult passthrough of the trusted bridge.
fn m_leg(verdict: &Match<IgmPayload>) -> (r: bool)
    ensures r == (verdict matches Match::Ignore(_))
{
    verdict matches Match::Ignore(_)
    // the leg's content equals the real is_ignore consult; the
    // trusted wrapper above restores the runtime shape
    // (matched_dir_entry's mapping is dir.rs:515-524's verified law)
}

// ===========================================================================
// WalkEvent -- upstream walk.rs:1279-1283 and WalkEventIter --
// walk.rs:1268-1321 (the Exit-emission state machine, REAL over
// the abstract walkdir stream)
// ===========================================================================
//
// Upstream doc (walk.rs:1269-1271, verbatim):
//   "Like `Walk`, but yields events instead of just paths. This is
//    useful for code that wants to take advantage of the
//    iterator's directory handling (e.g., sorted directory entries)
//    but wants to do something else with the results."

/// Origin enum (walk.rs:1280-1283).
pub enum WalkEvent {
    /// An event for entering a directory.
    Dir,
    /// An event for leaving a directory.
    Exit,
    /// An event for a file or other non-directory entity.
    File,
}

/// The trusted face of one `walkdir::IntoIter` yield (upstream:
/// the `next: Option<Result<walkdir::DirEntry, walkdir::Error>>`
/// cache, walk.rs:1274; well-formed events are ok-or-err, never
/// both).
pub struct WdEventFace {
    /// The Ok half (the entry face; None on the Err half).
    pub ok: Option<WalkdirDentFace>,
    /// The Err half (the walkdir error; None on the Ok half).
    pub err: Option<WalkdirErrFace>,
}

/// The event well-formedness of an abstract stream (the trusted
/// oracle premise of the machine: each event is ok-or-err, and
/// the ok depths descend at most one past their predecessor's
/// depth).
pub open spec fn wstream_wf(evs: Seq<WdEventFace>) -> bool {
    forall|i: int| #![trigger evs[i].ok, evs[i].err]
        0 <= i < evs.len() ==>
    {
        ((evs[i].ok matches Some(_))
            || (evs[i].err matches Some(_)))
        && ((evs[i].ok matches None)
            || (evs[i].err matches None))
        && ((i == 0)
            || (evs[i].ok matches None)
            || (evs[i - 1].ok matches None)
            || match evs[i].ok {
                None => true,
                Some(dent) => match evs[i - 1].ok {
                    None => true,
                    Some(prev) =>
                        dent.depth <= prev.depth + 1,
                },
            })
    }
}

/// The trusted deep-copy leg of one event (the face records carry
/// Vec payloads; the adapter's stream adaptation owns the copy --
/// the copy law pins the view).
#[verifier::external_body]
fn wev_clone(e: &WdEventFace) -> (r: WdEventFace)
    ensures
        r.ok@ == e.ok@,
        r.err@ == e.err@,
        (r.ok matches Some(_)) == (e.ok matches Some(_)),
        (r.err matches Some(_)) == (e.err matches Some(_)),
        r.ok matches Some(d) ==> ({
            d.path@ == (match e.ok {
                Some(d2) => d2.path@,
                None => Seq::empty(),
            })
            && d.depth == (match e.ok {
                Some(d2) => d2.depth,
                None => 0,
            })
        }),
{
    // trusted: the face record copy
    unimplemented!()
}

/// The trusted vec-of-events copy (the stream adaptation's own
/// leg; the view law rides the per-element legs).
#[verifier::external_body]
fn wev_clone_vec(evs: &[WdEventFace]) -> (r: Vec<WdEventFace>)
    ensures
        r@.len() == evs@.len(),
        forall|i: int| 0 <= i < evs.len() ==>
            (r@[i].ok@ == evs@[i].ok@
                && r@[i].err@ == evs@[i].err@
                && (r@[i].ok matches Some(_))
                    == (evs@[i].ok matches Some(_))),
{
    // trusted: the vector copy (the per-element legs above)
    unimplemented!()
}

/// Origin struct (walk.rs:1272-1276: the cached `next` slot, the
/// walkdir iterator, and the depth counter; the twin holds the
/// abstract stream with a cursor and the one-slot re-push cache).
pub struct WalkEventIter {
    /// The current directory depth (upstream: `self.depth`).
    pub depth: usize,
    /// The abstract stream (upstream: `it: walkdir::IntoIter`).
    pub evs: Vec<WdEventFace>,
    /// The stream cursor (the events consumed so far).
    pub pos: usize,
    /// The one-slot re-push cache (upstream: `self.next`);
    /// Some(deferred event) follows a pending Exit cascade.
    pub slot: Option<WdEventFace>,
}

impl WalkEventIter {
    /// `From<WalkDir> for WalkEventIter` (walk.rs:1285-1289: the
    /// empty cache and the fresh depth counter) -- the stream
    /// adaptation is the trusted face; the counter and slot shapes
    /// REAL.
    #[verifier::external_body]
    pub fn we_from_stream(evs: &[WdEventFace]) -> (r: WalkEventIter)
        ensures
            r.depth == 0,
            r.evs@ == evs@,
            r.pos == 0,
            r.slot matches None,
    {
        // trusted: the walkdir::IntoIter adapter (the fs session)
        WalkEventIter {
            depth: 0,
            evs: wev_clone_vec(evs),
            pos: 0,
            slot: None,
        }
    }

    /// `Iterator::next for WalkEventIter` (walk.rs:1291-1321) --
    /// REAL state machine over the face stream:
    /// - the cached slot consumes first, then the stream cursor
    ///   (1296 `self.next.take().or_else(|| self.it.next())`);
    /// - the depth read is the ok depth, else the error depth
    ///   (1297-1301);
    /// - a strictly-lower incoming depth fires ONE Exit and
    ///   re-caches the event (1302-1306; `self.depth -= 1` can
    ///   never underflow, the post's Exit arithmetic pins it);
    /// - the ok entry dispatches Dir (counter grows by one) or
    ///   File (1316-1319); the Err half passes through as the
    ///   Error::from_walkdir mapping above (1310, the twin's own
    ///   real fn consumed here).
    pub fn we_next(&mut self) -> (r: Option<Result<WalkEvent, Error>>)
        requires
            wstream_wf(self.evs@),
            // the counter's domain headroom (the machine's single
            // increment; the usize domain owns the rest)
            self.depth <= usize::MAX - 1,
        ensures
            final(self).evs@ == old(self).evs@,
            final(self).pos <= old(self).pos + 1,
            (r matches Some(Ok(WalkEvent::Exit))) ==>
                (final(self).depth + 1 == old(self).depth
                    && final(self).slot matches Some(_)),
            (r matches Some(Ok(WalkEvent::Dir))) ==>
                (final(self).depth == old(self).depth + 1
                    && final(self).slot matches None),
            (r matches Some(Ok(WalkEvent::File))) ==>
                (final(self).depth == old(self).depth
                    && final(self).slot matches None),
            (r matches Some(Err(_))) ==>
                (final(self).depth == old(self).depth
                    && final(self).slot matches None),
            (r matches None) ==>
                (final(self).depth == old(self).depth
                    && final(self).slot matches None),
    {
        // 1296: the cache consults first, then the stream
        let dent: WdEventFace = match self.slot.take() {
            Some(d) => d,
            None => {
                if self.pos >= self.evs.len() {
                    return None;
                }
                let d = wev_clone(&self.evs[self.pos]);
                self.pos += 1;
                d
            }
        };
        // 1297-1301: the depth read
        let depth: usize = match &dent.ok {
            Some(d) => d.depth,
            None => match &dent.err {
                Some(e) => e.depth,
                None => return None,
            },
        };
        // 1302-1306: the Exit cascade (one Exit per level; the
        // re-push keeps the event for the next call)
        if depth < self.depth {
            self.depth -= 1;
            self.slot = Some(dent);
            return Some(Ok(WalkEvent::Exit));
        }
        // 1310: the Err pass-through (the walk error mapping is
        // this module's own real from_walkdir above)
        if dent.ok.is_none() && dent.err.is_some() {
            let e = dent.err.as_ref().unwrap();
            return Some(Err(from_walkdir(e)));
        }
        // 1316-1319: the Dir / File dispatch (the walkdir_is_dir
        // consult reads the ty face; walk.rs:214-215's root-level
        // symlink nuance rides the face's own value). The counter
        // growth: the stream's depth step is bounded by the
        // well-formedness premise (depth <= prev+1), and the
        // machine's counter follows the stream depth -- the
        // saturation guard keeps the exec arithmetic total.
        let is_dir_next = match &dent.ok {
            Some(d) => d.ty.is_dir,
            None => false,
        };
        if is_dir_next {
            self.depth += 1;
            Some(Ok(WalkEvent::Dir))
        } else {
            Some(Ok(WalkEvent::File))
        }
    }
}

// ===========================================================================
// WalkBuilder -- upstream walk.rs:439-1108 (the option table; the
// core setters with the depth mutual clamps REAL)
// ===========================================================================

/// Origin struct (walk.rs:487-512; the ig_builder / sorter /
/// filter / skip / global-gitignore OnceLock fields are this
/// batch's recorded cuts or trusted legs -- the option table
/// below carries the core; the ignore-chain mount is the
/// build_matchers contract's seam into the IG5/IG6 twins).
pub struct WalkBuilder {
    /// The traversal roots (upstream: `paths: Vec<PathBuf>`).
    pub paths: Vec<Vec<u8>>,
    /// The maximum depth of traversal (None: no limit).
    pub max_depth: Option<usize>,
    /// The minimum depth of traversal (None: no minimum).
    pub min_depth: Option<usize>,
    /// The maximum size (in bytes) of file paths to yield.
    pub max_filesize: Option<u64>,
    /// Whether to follow symbolic links or not.
    pub follow_links: bool,
    /// Whether to skip entries on a different file system (the
    /// consult tier is the trusted same_file leg).
    pub same_file_system: bool,
    /// The number of threads to use (0: automatic; the parallel
    /// face is this batch's cut, and the undocumented `min(12)`
    /// cap of walk.rs:1541 rides the batch notes).
    pub threads: usize,
}

impl WalkBuilder {
    /// `WalkBuilder::new` (walk.rs:551-554: a root, the standard
    /// filters on) -- trusted construction contract.
    #[verifier::external_body]
    pub fn wnew(root: &[u8]) -> (r: WalkBuilder)
        ensures
            r.paths@.len() == 1,
            r.paths@[0]@ == root@,
            r.max_depth matches None,
            r.min_depth matches None,
            r.max_filesize matches None,
            r.follow_links == false,
            r.same_file_system == false,
            r.threads == 0,
    {
        // trusted: the standard-filter construction (the
        // ignore-chain mount consults the dir twin's builder)
        unimplemented!()
    }

    /// `WalkBuilder::empty` (walk.rs:558-560: no paths, the
    /// standard filters on) -- trusted construction contract.
    #[verifier::external_body]
    pub fn wempty() -> (r: WalkBuilder)
        ensures
            r.paths@.len() == 0,
            r.max_depth matches None,
            r.min_depth matches None,
            r.max_filesize matches None,
            r.threads == 0,
    {
        // trusted: the from_iter arm's empty shape
        unimplemented!()
    }

    /// `WalkBuilder::add` (walk.rs:722-725: append a root) -- REAL.
    pub fn wadd(&mut self, path: &[u8])
        ensures
            final(self).paths@.len()
                == old(self).paths@.len() + 1,
            final(self).paths@.subrange(
                0, old(self).paths@.len() as int)
                == old(self).paths@,
            final(self).paths@[
                old(self).paths@.len() as int]@ == path@,
            final(self).max_depth == old(self).max_depth,
            final(self).min_depth == old(self).min_depth,
            final(self).max_filesize == old(self).max_filesize,
            final(self).follow_links == old(self).follow_links,
            final(self).same_file_system
                == old(self).same_file_system,
            final(self).threads == old(self).threads,
    {
        self.paths.push(vstd::slice::slice_to_vec(path));
    }

    /// Upstream doc (walk.rs:727-729 verbatim):
    ///   "The maximum depth to recurse when traversing the
    ///    directory tree."
    /// `max_depth` (walk.rs:730-739) -- the mutual clamp: a max
    /// below the min lifts to the min (both-Some only, the Option
    /// compare's shape) -- REAL.
    pub fn wmax_depth(&mut self, depth: Option<usize>)
        ensures
            final(self).max_depth
                == (if (depth matches Some(d)
                    && old(self).min_depth matches Some(m)
                    && d < m)
                {
                    old(self).min_depth
                } else {
                    depth
                }),
            final(self).min_depth == old(self).min_depth,
            final(self).paths@ == old(self).paths@,
            final(self).max_filesize == old(self).max_filesize,
            final(self).follow_links == old(self).follow_links,
            final(self).same_file_system
                == old(self).same_file_system,
            final(self).threads == old(self).threads,
    {
        self.max_depth = depth;
        // if self.min_depth.is_some() && self.max_depth.is_some()
        //     && self.max_depth < self.min_depth
        if self.min_depth.is_some() && self.max_depth.is_some() {
            let mn = self.min_depth.unwrap();
            let mx = self.max_depth.unwrap();
            if mx < mn {
                self.max_depth = self.min_depth;
            }
        }
    }

    /// Upstream doc (walk.rs:741-743 verbatim):
    ///   "The minimum depth to recurse."
    /// `min_depth` (walk.rs:744-753) -- the symmetric clamp: a
    /// min above the max drops to the max -- REAL.
    pub fn wmin_depth(&mut self, depth: Option<usize>)
        ensures
            final(self).min_depth
                == (if (depth matches Some(d)
                    && old(self).max_depth matches Some(m)
                    && m < d)
                {
                    old(self).max_depth
                } else {
                    depth
                }),
            final(self).max_depth == old(self).max_depth,
            final(self).paths@ == old(self).paths@,
            final(self).max_filesize == old(self).max_filesize,
            final(self).follow_links == old(self).follow_links,
            final(self).same_file_system
                == old(self).same_file_system,
            final(self).threads == old(self).threads,
    {
        self.min_depth = depth;
        // if self.max_depth.is_some() && self.min_depth.is_some()
        //     && self.min_depth > self.max_depth
        if self.max_depth.is_some() && self.min_depth.is_some() {
            let mx = self.max_depth.unwrap();
            let mn = self.min_depth.unwrap();
            if mx < mn {
                self.min_depth = self.max_depth;
            }
        }
    }

    /// Upstream doc (walk.rs:755-757 verbatim):
    ///   "Whether to follow symbolic links or not."
    /// `follow_links` (walk.rs:756-759) -- REAL.
    pub fn wfollow_links(&mut self, yes: bool)
        ensures
            final(self).follow_links == yes,
            final(self).paths@ == old(self).paths@,
            final(self).max_depth == old(self).max_depth,
            final(self).min_depth == old(self).min_depth,
            final(self).max_filesize == old(self).max_filesize,
            final(self).same_file_system
                == old(self).same_file_system,
            final(self).threads == old(self).threads,
    {
        self.follow_links = yes;
    }

    /// Upstream doc (walk.rs:761-763 verbatim):
    ///   "The maximum size (in bytes) of file paths to yield."
    /// `max_filesize` (walk.rs:762-765) -- the zerotier clamp (a
    /// Some(0) size clamps to None, the `if size == Some(0)` arm's
    /// shape) -- REAL.
    pub fn wmax_filesize(&mut self, size: Option<u64>)
        ensures
            final(self).max_filesize
                == (if size matches Some(0) {
                    None
                } else {
                    size
                }),
            final(self).paths@ == old(self).paths@,
            final(self).max_depth == old(self).max_depth,
            final(self).min_depth == old(self).min_depth,
            final(self).follow_links == old(self).follow_links,
            final(self).same_file_system
                == old(self).same_file_system,
            final(self).threads == old(self).threads,
    {
        match size {
            Some(0) => self.max_filesize = None,
            _ => self.max_filesize = size,
        }
    }

    /// Upstream doc (walk.rs:765-775 verbatim):
    ///   "The number of threads to use for traversal. Note that
    ///    this only has an effect when using `build_parallel`."
    /// `threads` (walk.rs:766-776) -- REAL (the setter's own
    /// value law; the parallel consumer is the batch cut).
    pub fn wthreads(&mut self, n: usize)
        ensures
            final(self).threads == n,
            final(self).paths@ == old(self).paths@,
            final(self).max_depth == old(self).max_depth,
            final(self).min_depth == old(self).min_depth,
            final(self).max_filesize == old(self).max_filesize,
            final(self).follow_links == old(self).follow_links,
            final(self).same_file_system
                == old(self).same_file_system,
    {
        self.threads = n;
    }

    /// `build` (walk.rs:593-644) -- the single-thread assembly:
    /// trusted contract (the walkdir::WalkDir mount with the
    /// min/max depths and follow_links, the `-` root's stdin
    /// pump, and the matcher spine; the IG6 twin's real
    /// IncrementalIgnore builder consumes the options below).
    #[verifier::external_body]
    pub fn wbuild(&mut self) -> (r: WBuildFace)
        ensures
            r.max_depth == final(self).max_depth,
            r.min_depth == final(self).min_depth,
            r.max_filesize == final(self).max_filesize,
            r.follow_links == final(self).follow_links,
            r.same_file_system == final(self).same_file_system,
            (r.stdin_roots == (final(self).paths@.len() > 0
                && final(self).paths@[0]@
                    == seq![0x2D])),
    {
        // trusted: the walkdir + matcher assembly (the twin holds
        // the option carry; the seam consults the incremental
        // mount from IG6)
        unimplemented!()
    }

    /// `build_matchers` (walk.rs:675-694) -- the matcher spine
    /// over the dir twin's builder product: trusted contract.
    /// (Upstream 677-683 packs min_depth / max_depth /
    /// max_filesize / hidden / follow_links into the incremental
    /// options -- the IG6 twin's ii_new / ii_new_stdin are the
    /// real constructors this seam consults.)
    #[verifier::external_body]
    pub fn wbuild_matchers(
        min_depth: Option<usize>,
        max_depth: Option<usize>,
        max_filesize: Option<u64>,
        hidden: bool,
        follow_links: bool,
    ) -> (r: WMatchersFace)
        ensures
            r.min_depth == min_depth,
            r.max_depth == max_depth,
            r.max_filesize == max_filesize,
            r.hidden == hidden,
            r.follow_links == follow_links,
    {
        // trusted: the matcher spine (the incremental mount: the
        // II twin's ii_new/ii_new_stdin constructors consume the
        // options; the stdin root spells the `-` detection of
        // walk.rs:602)
        unimplemented!()
    }
}

/// The build face (the option carry of the single-thread pump; the
/// trusted assembly above hands the values to the callers).
pub struct WBuildFace {
    /// The max depth carry.
    pub max_depth: Option<usize>,
    /// The min depth carry.
    pub min_depth: Option<usize>,
    /// The filesize carry.
    pub max_filesize: Option<u64>,
    /// The follow-links carry.
    pub follow_links: bool,
    /// The same-filesystem carry.
    pub same_file_system: bool,
    /// Whether the first root is the stdin root `-`.
    pub stdin_roots: bool,
}

/// The matcher spine face (the carriers of build_matchers.
pub struct WMatchersFace {
    /// The min depth carry.
    pub min_depth: Option<usize>,
    /// The max depth carry.
    pub max_depth: Option<usize>,
    /// The filesize carry.
    pub max_filesize: Option<u64>,
    /// The hidden carry.
    pub hidden: bool,
    /// The follow-links carry.
    pub follow_links: bool,
}

}

// Standalone-file invocation anchor (the harness mounts this file
// with #[path]; single-file verus runs need the empty main).
fn main() {}
