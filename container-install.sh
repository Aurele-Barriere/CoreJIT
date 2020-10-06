#!/bin/bash

set -e

LLVM="clang+llvm-9.0.0-x86_64-pc-linux-gnu"
cd /home/opam

sudo chmod o+r /tmp/$LLVM.tar.xz
tar xf /tmp/$LLVM.tar.xz
sudo rm -f /tmp/$LLVM.tar.xz
PATH="$PATH:/home/opam/$LLVM/bin"

sudo apt-get update
sudo apt-get install -y pkg-config python2 m4 cmake libz3-4 libffi-dev libz-dev libncurses5-dev lua5.3 luajit cowsay
sudo ln -s /usr/lib/x86_64-linux-gnu/libz3.so.4 /usr/lib/x86_64-linux-gnu/libz3.so.4.8
sudo apt-get clean all

opam update

sudo chown -R opam:opam coqjit native_lib
cd coqjit
make install-deps
opam clean
eval $(opam env)

make -j coq
make -j extract
make -j ocaml

cd ..
sudo rm -rf $LLVM
sudo rm -rf opam-repository
