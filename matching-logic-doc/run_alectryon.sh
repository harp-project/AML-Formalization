#!/usr/bin/env bash

path_to_compiled_library="$1"
source_filename="$2"

stripped_filename="${source_filename#${path_to_compiled_library}}"
base_out_dir="doc/alectryon/"
out_dir="$base_out_dir/$(dirname "$stripped_filename")"


set -x
mkdir -p "$out_dir"
alectryon -R "$path_to_compiled_library" MatchingLogic \
        --traceback \
        --frontend coq \
        --backend webpage \
        --output-directory "$base_out_dir" \
        --copy-assets none \
        --output "$base_out_dir/$stripped_filename.html" \
        "$source_filename"

