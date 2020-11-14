#!/bin/bash

docker build -t ml-in-coq .
# In Travis-CI, the user has different id than in the container.
./run-in-docker.sh sudo chown -R coq:coq .
./run-in-docker.sh make
