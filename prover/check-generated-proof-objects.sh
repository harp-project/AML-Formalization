#!/usr/bin/env bash

compare() {
  NAME="$1"
  GENERATED="$NAME"
  REFERENCE="ref/$NAME.ref"

  cat "$GENERATED" | grep the-proof | sed 's/the-proof $p |- \(.*\) $=.*/\1/' > $NAME.tmp
  diff -uZ "$NAME.tmp" "$REFERENCE"
}

RESULT="0"
for hs_file in *_mm.hs
do
    echo "Patching $hs_file"
    patched_hs_file="$(basename "$hs_file" ".hs").p.hs"
    ./patch-extracted-hs.sh "$hs_file" "$patched_hs_file"
    runner_hs="$(basename $hs_file ".hs")_main.hs"
    str_name="$(basename "$hs_file" "_mm.hs")"
    printf "module Main where\n  import Proof\n  main = Prelude.putStrLn Proof.$str_name" > "$runner_hs"
    # https://github.com/coq/coq/issues/15180
    ghc -XNoPolyKinds "$patched_hs_file" "$runner_hs" -o runner
    mm_file="$(basename "$hs_file" "_mm.hs").mm"
    ./runner > "$mm_file"
    #continue
    echo "Checking $mm_file"
    compare "$mm_file"
    if [[ "$?" -gt 0 ]]
    then
	echo "ERROR"
	RESULT="1"
	continue
    fi
    
    echo "verify proof *" | metamath "$mm_file"
done

exit "$RESULT"
# compare proof_4.mm
