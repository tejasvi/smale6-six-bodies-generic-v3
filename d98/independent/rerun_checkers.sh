#!/bin/bash
# The re-run of the checkers of Lemma 6.13 recorded in rerun_checkers.log: the Arb certifier and the exact rational
# checker at (1,2,7 | B) for four mass triples B, then the independent mpmath check (rho_indep.py; the log names it by
# its original path tools/rho_indep.py). Written for the supplement (the driver of the stored log was not kept); apart
# from the date line and the four "time N s" lines it reproduces rerun_checkers.log byte for byte.
# Usage, from the root of the supplement: bash d98/independent/rerun_checkers.sh OUT_DIR > rerun_checkers.log 2>&1
# (PY: the Python interpreter, default python3; the Arb certificates are written to OUT_DIR)
OUT=${1:?usage: rerun_checkers.sh OUT_DIR}
PY=${PY:-python3}
mkdir -p "$OUT"
date
for B in "1 2 7" "1 2 8" "1 3 7" "2 3 11"; do
  echo "=== Arb 1 2 7 $B"; $PY -I -B d98/d98_certify_arb.py 1 2 7 $B "$OUT/arb_1_2_7_${B// /_}.json"; echo "exit $?"
  echo "=== rational 1 2 7 $B"; $PY -I -B d98/d98_check_rational.py 1 2 7 $B; echo "exit $?"
done
echo "=== independent mpmath (tools/rho_indep.py)"
$PY -I -B d98/independent/rho_indep.py 1 2 7
$PY -I -B d98/independent/rho_indep.py 1 2 8
