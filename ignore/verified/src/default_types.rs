//! ignore 0.4.34 (pin `178cc027`) -- Verus transcription of upstream
//! `crates/ignore/src/default_types.rs`, batch IG4.
//!
//! Upstream shape (default_types.rs:1-267): the module is ONE constant
//! `DEFAULT_TYPES: &[(&[&str], &[&str])]` -- roughly fifty rows of
//! (alias-name list, glob list) pairs that ripgrep ships with, guarded
//! by two `#[cfg(test)]` sortedness tests and consumed exclusively by
//! `TypesBuilder::add_defaults` (types.rs:486-497), whose `.expect`
//! ("adding a default type should never fail", types.rs:487) rides on
//! every row name passing `TypesBuilder::add`'s validation.
//!
//! Twin modeling declarations (Origin: every deviation recorded):
//! - **Table-as-parameter face.** The upstream constant is not
//!   duplicated into the twin (byte-duplicating ~260 string literals
//!   into the verified tree buys no leverage: the twin never executes,
//!   and the full-table properties are mechanical data facts). Instead
//!   `types::add_defaults` transcribes its triple loop over a table
//!   parameter of `DefaultTypeRow` entries, and THIS module supplies
//!   the row shape plus the per-row validity view that unstakes the
//!   upstream `.expect` (if every row name passes `add`'s check, the
//!   expect provably never fires -- the twin recovers the panic
//!   contract as a precondition).
//! - The two upstream sortedness tests (`default_types_are_sorted`,
//!   `default_types_aliases_are_sorted`, the #[cfg(test)] tail) are
//!   runtime evidence in the IG4 driver (the S12 sorted columns + the
//!   upstream `cargo test` rows re-run), not twin theorems: sortedness
//!   is a property of the literal data, which the twin deliberately
//!   does not carry.
//! - **Bounded name-validity face.** The twin's
//!   `default_row_names_valid` checks ASCII letters/digits only
//!   (via `types::ty_name_ok`, bytes 0x30..0x39, 0x41..0x5A,
//!   0x61..0x7A). Upstream validates with `char::is_alphanumeric`
//!   (Unicode): a name like `añ` is ACCEPTED upstream and REJECTED by
//!   the twin face. Non-ASCII names are reachable only through the
//!   user-facing `add`/`--type-add` seam, never through the default
//!   table itself (all ASCII; the driver S12 unicode probe row
//!   records the upstream value).

use vstd::prelude::*;

verus! {

// ===========================================================================
// One default-types row -- upstream `(&[&str], &[&str])`
// ===========================================================================

/// The twin row shape: the alias-name list and the glob list of one
/// DEFAULT_TYPES entry (upstream: a `(&[&str], &[&str])` pair per row;
/// bytes per the crate-wide carrier convention).
pub struct DefaultTypeRow {
    /// The alias names of this type (upstream `&[&str]`, the alias
    /// list; every alias gets the same globs when added).
    pub names: Vec<Vec<u8>>,
    /// The glob strings recognizing this type (upstream `&[&str]`).
    pub exts: Vec<Vec<u8>>,
}

/// Validity face of one row: every alias name is a valid type name
/// under `types::ty_name_ok` (bounded ASCII face; see the header
/// note). The preconditions this view feeds are what makes upstream's
/// `add_defaults` `.expect(MSG)` (`"adding a default type should
/// never fail"`, types.rs:487) provably dead.
pub open spec fn default_row_names_valid(r: DefaultTypeRow) -> bool {
    forall|k: int| #![trigger r.names@[k]]
        0 <= k < r.names@.len() ==> super::types::ty_name_ok(r.names@[k]@)
}

/// The whole-table validity view (the driver's S12 all-names column is
/// the runtime backing of every harness instantiation of this view).
pub open spec fn default_table_valid(tbl: &[DefaultTypeRow]) -> bool {
    forall|k: int| #![trigger tbl@[k]]
        0 <= k < tbl@.len() ==> default_row_names_valid(tbl@[k])
}

} // verus!

// Standalone-file invocation anchor (the harness mounts this file with
// #[path]; single-file verus runs need the empty main).
fn main() {}
