//! bitflags 2.13.2 x Verus -- src-zone module root
//!
//! Mirrors the module tree of upstream `code/src/` (SUBDIR is empty:
//! the code/ directory itself is the crate root):
//!   * `traits.rs` (`Flag` + `Flags` trait default bodies, monomorphized)
//!     -- mirrors code/src/traits.rs
//!   * `example_generated.rs` (an instance carrying the macro-expanded
//!     inherent API face) -- mirrors code/src/example_generated.rs plus
//!     the macro-expansion products of code/src/public.rs / internal.rs
//!   * `iter.rs` (the Iter/IterNames/IterDefinedNames/IterEqualNames state
//!     machines) -- mirrors code/src/iter.rs
//!
//! Items not mirrored, with reasons (nothing silently dropped; see
//! out/bug-finder-summary.md):
//!   * the `bitflags!` / `bitflags_match!` macro_rules definition bodies of
//!     `code/src/lib.rs` -- macro bodies are outside the transcription face
//!     (skill ruling); macro expansion products are carried as
//!     monomorphized instances;
//!   * `code/src/public.rs` / `code/src/internal.rs` are macro template
//!     files; their expansion bodies are carried by example_generated.rs;
//!   * `code/src/external.rs` (the serde/bytemuck/arbitrary external trait
//!     impl face) -- external-crate dependency domain (B3);
//!   * the `std::str` / `fmt::Write` layer of `code/src/parser.rs` -- the
//!     std str/fmt layers have no vstd specs yet; the parser UT face is
//!     blocked (B1/B2), see out/bug-finder-summary.md.
//!
//! This file has no standalone driver: the harness zone mounts the whole
//! src zone via `#[path = "../src/lib.rs"] mod ..;`; the src zone's own
//! self-verification panel is re-run by a dedicated dev driver.

pub mod example_generated;
pub mod traits;
pub mod iter;
