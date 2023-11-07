#!/usr/bin/env bash

koreimport -o out.v --module IMP koreimport/korefiles/imp.kore
coqc out.v
