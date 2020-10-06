#!/bin/sh

set -e

cd /home/opam/coqjit

echo "Welcome to the coqjit artifact"

/usr/games/cowsay "Proving Theorems     \"make proofs\""
make -j proofs
echo "□"

/usr/games/cowsay "Running Tests        \"./test.sh\""
./test.sh > /dev/null
echo "□"

/usr/games/cowsay "Running Experiments  \"./experiments.sh\""
./experiments.sh 1
echo "□"

/usr/games/cowsay "All done, enjoy your well deserved cup of coffee!"
