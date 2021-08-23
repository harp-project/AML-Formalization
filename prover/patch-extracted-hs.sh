#!/usr/bin/env bash

cat "$1" | head -n 5 > "$2"
printf "import qualified Data.Bits\nimport qualified Data.Char\n" >> "$2"
cat "$1" | tail -n +5 >> "$2"
