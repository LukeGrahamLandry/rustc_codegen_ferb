set -e
cargo test
cargo build
cd target
# RUSTC_ICE=0 makes it not create rustc-ice-DATE.txt when i crash
# which happens a lot :(
RUSTC_ICE=0 rustc -Z codegen-backend=debug/librustc_codegen_ferb.dylib -C panic=abort ../tests/hello.rs -lc
./hello || echo "status = $?"
