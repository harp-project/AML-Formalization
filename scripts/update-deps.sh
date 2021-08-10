#!/bin/bash
STDPP_REPO="https://gitlab.mpi-sws.org/iris/stdpp.git"
STDPP_REV_FILE="$(pwd)/matching-logic/deps/stdpp.rev"

STDPP_GIT_DIR=$(mktemp -d)

git clone --depth=1 --branch=master "$STDPP_REPO" "$STDPP_GIT_DIR"
pushd "$STDPP_GIT_DIR"
REV=$(git rev-parse master)
popd
echo "rev: $REV"
rm -rf "$STDPP_GIT_DIR"

echo "$REV" > "$STDPP_REV_FILE"

git diff --exit-code
if [[ $? -eq 1 ]]; then
  BRANCH="auto-update-stdpp-$(date +'%Y-%m-%d--%H-%M-%S')"
  git checkout -b "$BRANCH"
  git commit -a -m 'Bump stdpp version'
  git push origin "$BRANCH"
  gh pr create --title 'Bump stdpp version' --body 'This PR was auto-generated.'
fi
