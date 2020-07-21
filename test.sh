#!/bin/bash

set -x

mkdir -p _build
pushd _build
cmake ..
make
popd
clang-10 -S -emit-llvm -o test.bc test.c
opt-10 -instnamer -load _build/*/*SLVA* -slva test.bc > /dev/null
rm -rf _build test.bc
