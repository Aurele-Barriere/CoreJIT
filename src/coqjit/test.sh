#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
JIT=$DIR/jit

for t in constprop native_test2 native_test; do
  echo "=== RUNNING $t"
  p=$DIR/progs_specIR/$t.specir
  $JIT $p
  $JIT -n $p
  $JIT -n -c $p
  $JIT -t $p
  $JIT -t -n $p
  $JIT -k $p
  $JIT -n -k $p
done


for t in example1 fib first if_then loop printing scopes spec_fail spec spec_pos table; do
  echo "=== RUNNING $t"
  p=$DIR/progs_lua/$t.lua
  $JIT -f $p
  $JIT -f -n $p
  $JIT -f -n -c $p
  $JIT -f -t $p
  $JIT -f -t -n $p
  $JIT -f -k $p
  $JIT -f -n -k $p
done

for t in bubble_sort fib2 gnome_sort; do
  echo "=== RUNNING $t"
  p=$DIR/progs_lua/$t.lua
  $JIT -f -n $p
  $JIT -f -t -n $p
  $JIT -f -n -k $p
done
