# `script` phase: you usually build, test and generate docs in this phase

set -ex

. $(dirname $0)/utils.sh

run_test_suite() {
    cargo build --target $TARGET --verbose
    #cargo run --target $TARGET
    cargo test --target $TARGET

    # sanity check the file type
    file target/$TARGET/debug/ayzim-opt
}

main() {
    run_test_suite
}

main
