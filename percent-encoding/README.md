# percent-encoding 2.3.2

- upstream: [servo/rust-url](https://github.com/servo/rust-url) @ [00a6ce5](https://github.com/servo/rust-url/commit/00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a) (`COMMIT` pin in `fetch.conf`; `../fetch.sh percent-encoding --latest` follows the tip)
- source: `../code/` — whole upstream tree at the pinned commit (byte-exact `git archive`, git-ignored); this crate lives in upstream subdir `percent_encoding/` (workspace carrier: build with `cargo build -p percent-encoding` from `../code/`, or `--manifest-path ../code/percent_encoding/Cargo.toml`)
