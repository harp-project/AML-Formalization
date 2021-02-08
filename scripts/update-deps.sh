#!/bin/bash
STDPP_REPO="https://gitlab.mpi-sws.org/iris/stdpp.git"
STDPP_REV_FILE="$(pwd)/deps/stdpp.rev"

STDPP_GIT_DIR=$(mktemp -d)

git clone --depth=1 --branch=master "$STDPP_REPO" "$STDPP_GIT_DIR"
pushd "$STDPP_GIT_DIR"
REV=$(git rev-parse master)
popd
echo "rev: $REV"
rm -rf "$STDPP_GIT_DIR"

echo "$REV" > "$STDPP_REV_FILE"
