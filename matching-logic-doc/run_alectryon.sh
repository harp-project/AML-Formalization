#!/usr/bin/env bash

path_to_compiled_library="$1"
source_filename="$2"

stripped_filename="${source_filename#${path_to_compiled_library}}"
out_dir="doc/alectryon/$(dirname "$stripped_filename")"
mkdir -p "$out_dir"

alectryon -R "$path_to_compiled_library" MatchingLogic \
        --traceback \
        --frontend coq \
        --backend webpage \
        --output-directory "$out_dir" \
        "$source_filename"

