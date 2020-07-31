#!/bin/bash

docker build -t ml-in-coq .
./run-in-docker.sh whoami
./run-in-docker.sh id -u
./run-in-docker.sh ls -l
./run-in-docker.sh coq_makefile -f _CoqProject -o Makefile
./run-in-docker.sh make
