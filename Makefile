# Build the Rust project
rust-build:
	cargo build --release

# Build the Rust documentation
rust-doc:
	cargo doc --no-deps --open

# Lint checks for Rust code
lint:
	cargo fmt --all -- --check
	cargo clippy -p era_revm -Zunstable-options -- -D warnings --allow clippy::unwrap_used

# Fix lint errors for Rust code
lint-fix:
	cargo clippy --fix
	cargo fmt

# Run unit tests for Rust code
test:
	cargo test

.PHONY: rust-build lint test
