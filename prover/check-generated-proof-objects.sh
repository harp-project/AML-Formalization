#!/usr/bin/env bash

compare() {
  NAME="$1"
  GENERATED="$NAME"
  REFERENCE="ref/$NAME.ref"

  cat "$GENERATED" | grep the-proof | sed 's/the-proof $p |- \(.*\) $=.*/\1/' > $NAME.tmp
  diff -uZ "$NAME.tmp" "$REFERENCE"
}

RESULT="0"
mm_files=$(ls *.mm)
for mm_file in $mm_files
do
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
