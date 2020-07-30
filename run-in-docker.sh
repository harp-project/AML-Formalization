#!/bin/bash
docker run --rm --mount src=$(pwd),target=/home/coq/AML-Formalization,type=bind --workdir=/home/coq/AML-Formalization ml-in-coq "$@"
