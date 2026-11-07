//! dev driver -- for iteration (superseded by the formal harness; kept to re-run the verified-tree compilation)
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod base64ct_v;

fn main() {
    println!("base64ct verified tree mounted");
}
