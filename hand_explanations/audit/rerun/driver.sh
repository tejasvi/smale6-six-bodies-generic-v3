#!/bin/bash
# Rerun of the mechanisms referee's independent checkers, from a fresh copy of its scripts.
# In this supplement: run it in a writable copy of the supplement; it writes its outputs next to the checkers
# (hand_explanations/independent/scripts/, sing/) and its log to hand_explanations/independent/driver.log.
# PY: a Python with numpy, highspy and python-flint; SPY: a Python with SymPy (the stored run used SymPy 1.14).
set -u
cd "$(dirname "$0")/../../independent/scripts"
PY=${PY:-python3}
SPY=${SPY:-python3}
export OPENBLAS_NUM_THREADS=1 RAYON_NUM_THREADS=1 OMP_NUM_THREADS=1
t0=$(date +%s)
step(){ echo "[$(($(date +%s)-t0))s] $*" >> ../driver.log; }
step run_ref;      nice -n 10 $PY -B run_ref.py ref_cover.jsonl 32 > run_ref.log 2>&1
step run_resid;    nice -n 10 $PY -B run_resid.py ref_resid_cover.jsonl 32 > run_resid.log 2>&1
for s in compare_cov cmp_resid cmp_global_resid cumul_ref final_partition misc_counts single_acct table21 clique_overlap families_check; do
  step $s; nice -n 10 $PY -B $s.py > $s.out 2>&1
done
step ref_lp;       nice -n 10 $PY -B ref_lp.py ref_cover.jsonl ref_lp.jsonl 32 > ref_lp.log 2>&1
step resid_certs;  nice -n 10 $PY -B resid_certs.py > resid_certs.out 2>&1
step exact_templates; ALL_TEMPLATES=1 nice -n 10 $PY -B exact_templates.py > exact_templates_all.out 2>&1
step p4_check;     ALL_TEMPLATES=1 nice -n 10 $PY -B p4_check.py > p4_check_all.out 2>&1
step resid_polys;  nice -n 10 $SPY -B resid_polys.py > resid_polys.out 2>&1
step L_identity;   nice -n 10 $SPY -B L_identity.py > L_identity.out 2>&1
cd ../sing
for f in *.sing; do step "Singular $f"; nice -n 10 Singular -q $f > ${f%.sing}.out 2>&1 < /dev/null; done
step done
