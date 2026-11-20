//! GL3 mounting driver -- the lib tree (escape + pathutil + fnv +
//! glob's GL2 parser + the GL3 lowering face) compiled and verified
//! as one unit; KAT vectors go in their own small ut_toregex* files.
#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod lib;

#[allow(unused_imports)]
use lib::CowBytes;
#[allow(unused_imports)]
use lib::pathutil;

fn main() {}
