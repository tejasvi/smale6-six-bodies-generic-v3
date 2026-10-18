#!/bin/bash
export OPENBLAS_NUM_THREADS=1
# Alternative cores for the 433 first-pass uncertified cells outside class 3 (results/unc_alt.json).
# Usage: bash engine/jobs/alt_job.sh   (PY: the Python interpreter, default python3); output engine/runs/alt_out.jsonl
cd "$(dirname "$0")/.."
PY=${PY:-python3}
U=../results/unc_alt.json
mkdir -p runs
[ -f runs/alt_out.jsonl.done ] || { $PY -I talt.py $U ../results runs/alt_out.jsonl --tries 8 --jobs 370 --qtime 900 > runs/alt.log 2>&1 && touch runs/alt_out.jsonl.done; }
echo alt done
