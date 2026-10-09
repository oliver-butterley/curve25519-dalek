#!/usr/bin/env bash
# Translate curve25519-dalek to Lean: apply curve25519-dalek/translation-patches/, run charon + aeneas,
# then revert the patches. Charon settings live in curve25519-dalek/Cargo.toml
# [package.metadata.charon].
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
# The serial backend is forced for the charon build only; build.rs derives
# curve25519_dalek_bits (64 or 32) from each target.
(cd curve25519-dalek && CARGO_ENCODED_RUSTFLAGS='--cfg=curve25519_dalek_backend="serial"' \
    ../.aeneas/charon cargo --preset=aeneas \
    --targets x86_64-unknown-linux-gnu --targets i686-unknown-linux-gnu \
    --dest-file ../.llbc/curve25519_dalek.llbc \
    -- --locked)
.aeneas/aeneas -backend lean -split-files -emit-json \
    -dest curve25519-dalek/lean -subdir Curve25519Dalek .llbc/curve25519_dalek.llbc
