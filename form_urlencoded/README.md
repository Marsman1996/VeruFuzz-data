# form_urlencoded 1.2.2

- upstream: [servo/rust-url](https://github.com/servo/rust-url) @ [00a6ce5](https://github.com/servo/rust-url/commit/00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a) (`COMMIT` pin in `fetch.conf`; `../fetch.sh form_urlencoded --latest` follows the tip)
- source: `../code/` — whole upstream tree at the pinned commit (byte-exact `git archive`, git-ignored); this crate lives in upstream subdir `form_urlencoded/` (workspace carrier: build with `cargo build -p form_urlencoded` from `../code/`, or `--manifest-path ../code/form_urlencoded/Cargo.toml`)
