#! /bin/bash

set -e
set -x
lean --version
lake build -d=lib/ -- --test
lake build -d=lens/ -- --test
lake build -d=lean-tools/
lake build -d=cmd-line-args/
cd advent && lake build
lake build
set +x
echo Success!!
