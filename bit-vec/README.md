# bit-vec 0.10.1

- upstream: [contain-rs/bit-vec](https://github.com/contain-rs/bit-vec) @ [cd5b439](https://github.com/contain-rs/bit-vec/commit/cd5b4392be151fb507f3bdbf71ce1e73885dbc28) (`COMMIT` pin in `fetch.conf`; `../fetch.sh bit-vec --latest` follows the tip)
- source: `../code/` — whole upstream tree at the pinned commit (byte-exact `git archive`, git-ignored); this crate lives in upstream subdir `vec/` (workspace carrier: build with `cargo build -p bit-vec` from `../code/`, or `--manifest-path ../code/vec/Cargo.toml`)
