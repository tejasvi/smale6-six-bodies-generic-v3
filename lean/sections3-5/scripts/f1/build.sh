#!/bin/bash
# Builds the family F1 (Proposition 3.1) from the root of the Lake package, step by step, with wall-clock times.
# Prerequisite: `lake exe cache get` (Mathlib). The output contains the native_decide timings (profiler) and the
# statements and axioms of the theorems (L6Check.F1.Axioms).
set -o pipefail
step () {
  echo "== lake build $*"
  local t0=$(date +%s.%N)
  lake build "$@" 2>&1 | grep -v '^⣿\|^trace:'
  local rc=$?
  local t1=$(date +%s.%N)
  echo "== exit $rc, wall $(awk "BEGIN {printf \"%.1f\", $t1 - $t0}") s"
}
step L6Common.SHA256 L6F1
step L6Sound.F1.Basic L6Sound.F1.Complete L6Sound.F1.Orbit L6Sound.F1.Component L6Sound.F1.Classes
step L6Check.F1.Sha L6Check.F1.N4 L6Check.F1.N5 L6Check.F1.N6
step L6Check.F1.Main L6Check.F1.ChangChen L6Check.F1.Axioms
