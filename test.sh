set -e

case "$(uname -s)" in
    Darwin) suffix="dylib";;
    Linux) suffix="so";;
  *) echo "Unsupported target"; exit 1;;
esac
cg="codegen-backend=debug/librustc_codegen_ferb.$suffix"

cargo test
cargo build
cd target
# RUSTC_ICE=0 makes it not create rustc-ice-DATE.txt when i crash
# which happens a lot :(
RUSTC_ICE=0 rustc -Z "$cg" -C panic=abort ../tests/hello.rs -lc -Z dump-mir=" & PreCodegen"
./hello || echo "status = $?"
