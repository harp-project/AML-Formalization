#!/bin/bash

docker build -t ml-in-coq .
# In Travis-CI, the user has different id than in the container.
./run-in-docker.sh sudo chown coq:coq .
./run-in-docker.sh coq_makefile -f _CoqProject -o Makefile
./run-in-docker.sh ls -laZ
./run-in-docker.sh ls -laZ ./ML
./run-in-docker.sh make
