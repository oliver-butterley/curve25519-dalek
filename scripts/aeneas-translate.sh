#!/usr/bin/env bash
# Translate curve25519-dalek to Lean: apply curve25519-dalek/translation-patches/, run charon + aeneas,
# then revert the patches. Charon settings live in curve25519-dalek/Cargo.toml.
set -euo pipefail
cd "$(dirname "$0")/.."

TAG=$(awk -F'"' '/^\[/{name=""} /^name = /{name=$2} /^rev = / && name=="aeneas"{print $2}' lakefile.toml)
: "${TAG:?no aeneas rev in lakefile.toml}"
[[ "$(.aeneas/aeneas -version 2>/dev/null)" == "aeneas $TAG" ]] \
    || { echo "run ./scripts/aeneas-install.sh: .aeneas/ is not $TAG" >&2; exit 1; }

revert() {
    # Undo the applied patches in reverse order (patch contexts may overlap).
    local i
    for (( i = ${#applied[@]} - 1; i >= 0; i-- )); do
        git apply -R "${applied[i]}"
    done
}
applied=()
trap revert EXIT
shopt -s nullglob
for patch in curve25519-dalek/translation-patches/*.patch; do
    git apply "$patch"
    applied+=("$patch")
done

mkdir -p .llbc
# Four configurations, merged by charon's multi-target translation:
# {64-bit, 32-bit} x {with precomputed-tables, without precomputed-tables} 
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
rustc="$(.aeneas/charon toolchain-path)/bin/rustc"
serial='--cfg curve25519_dalek_backend="serial"'
targets=()
for arch in x86_64 i686; do
    triple=$arch-unknown-linux-gnu
    spec=$arch-no-tables
    "$rustc" -Z unstable-options --print target-spec-json --target "$triple" > ".llbc/$spec.json"
    targets+=(--targets "$triple" --targets "$PWD/.llbc/$spec.json")
    export "CARGO_TARGET_$(tr 'a-z-' 'A-Z_' <<< "$triple")_RUSTFLAGS=$serial --cfg feature=\"precomputed-tables\""
    export "CARGO_TARGET_$(tr 'a-z-' 'A-Z_' <<< "$spec")_RUSTFLAGS=$serial"
done
(cd curve25519-dalek && ../.aeneas/charon cargo --preset=aeneas "${targets[@]}" \
    --dest-file ../.llbc/curve25519_dalek.llbc \
    -- --locked --no-default-features --features alloc,zeroize \
    -Zjson-target-spec -Zbuild-std=core,alloc)
.aeneas/aeneas -backend lean -split-files -emit-json \
    -dest curve25519-dalek/lean -subdir Curve25519Dalek .llbc/curve25519_dalek.llbc
