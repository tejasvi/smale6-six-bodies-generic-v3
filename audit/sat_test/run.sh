#!/bin/bash
# The Singular test of `sat` with and without elim.lib (sat_test.out). Written for the supplement (the stored
# sat_test.out had no shipped driver); apart from the Singular version banner it reproduces sat_test.out byte for byte.
# Usage: bash audit/sat_test/run.sh > sat_test.out
cd "$(dirname "$0")"
for f in without_elim.sing with_elim.sing; do echo "== Singular -q $f"; Singular -q $f < /dev/null 2>&1; echo "exit $?"; done
echo "== Singular version"; Singular --version < /dev/null 2>&1 | head -2
