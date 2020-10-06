#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
JIT=$DIR/jit

function measure {
  TIMEFORMAT='%E';time ( $@ ) 2>&1 1>/dev/null
}

ITER=$1

$JIT -f -n $DIR/progs_lua/bubble_sort.lua > /dev/null

echo "benchmark, vm, run, time"
for i in $(seq 1 $ITER); do
  for t in gnome_sort fib2; do
    p=$DIR/progs_lua/$t.lua
    pn=$(mktemp /tmp/jit-test.XXXXXX)
    sed 's/__hint.*//' $p > $pn
    time=$(measure $JIT -f -n $p)
    echo "$t, jit,            $i, $time"
    time=$(measure $JIT -f -k -n $p)
    echo "$t, jit_static,     $i, $time"
    time=$(measure lua $pn)
    echo "$t, lua,            $i, $time"
    time=$(measure luajit $pn)
    echo "$t, luajit,         $i, $time"
    rm $pn
  done
done
