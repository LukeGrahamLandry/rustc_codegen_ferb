set -e

case "$(uname -s)" in
    Darwin) suffix="dylib";;
    Linux) suffix="so";;
  *) echo "Unsupported target"; exit 1;;
esac
cg="codegen-backend=debug/librustc_codegen_ferb.$suffix"

export RUSTFLAGS="--remap-path-prefix $(pwd)=."
export RUSTFLAGS="--remap-path-prefix $HOME=~"
cargo build
cargo test --package ferb --tests
cd target
# RUSTC_ICE=0 makes it not create rustc-ice-DATE.txt when i crash
# which happens a lot :(
export RUSTC_ICE=0 
# opt-level=3 enables inlining (and presumably other stuff), gives me simpler ir to deal with. 
echo "=== YES mir optimisations ==="
rustc -Z "$cg" -C panic=abort ../tests/hello.rs -lc -Z dump-mir=" & PreCodegen" -C opt-level=3
./hello || echo "status = $?"
echo "=== NO mir optimisations ==="
rustc -Z "$cg" -C panic=abort ../tests/hello.rs -lc -Z dump-mir=" & PreCodegen" -C opt-level=0
./hello || echo "status = $?"
