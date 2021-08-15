#!/usr/bin/env bash

compare() {
  NAME="$1"
  GENERATED="$NAME.mm"
  REFERENCE="ref/$NAME.mm.ref"

  cat "$GENERATED" | grep the-proof | sed 's/the-proof $p |- \(.*\) $=.*/\1/' > $NAME.tmp
  diff -uZ "$NAME.tmp" "$REFERENCE"
}

mm_files = $(ls *.mm)
echo $mm_files"

compare proof_4
