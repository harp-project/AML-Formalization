#!/usr/bin/env bash
nix build -L '.#koreimport' --out-link result-koreimport
./result-koreimport/bin/koreimport -o out.v --module IMP koreimport/korefiles/imp.kore
