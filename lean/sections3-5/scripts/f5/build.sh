#!/bin/bash
# Builds the family F5 (Proposition 5.9) from the root of the Lake package, with wall-clock times.
# Prerequisite: `lake exe cache get` (Mathlib, for L6Sound.F5.Rank). The output contains the native_decide timings
# (profiler), the statements and axioms of the theorems (L6Check.F5.Axioms), and the census table, the open cells,
# the cells without a clique and the cells with a clique of four bodies (L6Check.F5.Print).
set -o pipefail
step () {
  echo "== lake build $*"
  local t0=$(date +%s.%N)
  lake build "$@" 2>&1 | grep -v '^⣿\|^trace:'
  local rc=$?
  local t1=$(date +%s.%N)
  echo "== exit $rc, wall $(awk "BEGIN {printf \"%.1f\", $t1 - $t0}") s"
}
step L6F5 L6Common.SHA256
step L6Sound.F5.Rank
step L6Check.F5.Data L6Check.F5.Sha L6Check.F5.Census
step L6Check.F5.Axioms L6Check.F5.Print
