#!/bin/bash
export OPENBLAS_NUM_THREADS=1
# Alternative cores for the 600 first-pass uncertified cells of class 3 (results/unc_c3.json).
# Usage: bash engine/jobs/alt3_job.sh   (PY: the Python interpreter, default python3); output engine/runs/alt3_out.jsonl
cd "$(dirname "$0")/.."
PY=${PY:-python3}
mkdir -p runs
[ -f runs/alt3_out.jsonl.done ] || { $PY -I talt.py ../results/unc_c3.json ../results runs/alt3_out.jsonl --tries 8 --jobs 370 --qtime 900 > runs/alt3.log 2>&1 && touch runs/alt3_out.jsonl.done; }
echo alt3 done
