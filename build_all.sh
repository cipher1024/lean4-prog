#! /bin/bash

set -e

lake build -d=lib/
lake build -d=lean-tools/
lake build -d=cmd-line-args/
lake build -d=advent/
lake build
set +x
echo Success!!
