#!/bin/bash
# EXACT pipeline per class in CLASSES (mode le, --base):
#  1. treplay.py in 384 parts (certified enumeration; output identical to texact.py);
#  2. tsec_exact.py on the cells (certified single-term exclusions, or systems of initial forms);
#  3. tcore.py (cores mod p, verified at the random masses);
#  4. tcert.py (each distinct core certified over Q(m)).
# Resumable per part. Results in runs/exact6/cCLS/ under the directory engine/ of the supplement.
# Usage: CLASSES="0 1 2" P=64 NP=384 bash engine/jobs/exact_job.sh   (PY: the Python interpreter, default python3)
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
# the cells of a class are numbered in the order of rep/p*.jsonl in the C locale (p0, p1, p10, p100, ...), as in the
# stored runs; the order of sec/p*.cores.jsonl fixes the field "example" of cert.jsonl
export LC_ALL=C
cd "$(dirname "$0")/.."
PY=${PY:-python3}
P=${P:-64}; NP=${NP:-384}   # parallel processes; parts of the cells (the stored runs: NP=384)
for c in $CLASSES; do
  O=runs/exact6/c$c; mkdir -p $O/rep $O/sec
  seq 0 383 | xargs -P $P -I{} bash -c 'f='$O'/rep/p{}.jsonl; [ -f $f.done ] && exit 0; '$PY' -I treplay.py 6 ../diagrams/n6.json '$c' $f --mode le --base --split 3 --part {} --nparts 384 > $f.log 2>&1 && touch $f.done'
  [ $(ls $O/rep/*.jsonl.done 2>/dev/null | wc -l) -eq 384 ] || { echo replay incomplete $c; continue; }
  [ -f $O/cells.jsonl.done ] || { cat $O/rep/p*.jsonl > $O/cells.jsonl && touch $O/cells.jsonl.done; }
  nc=$(wc -l < $O/cells.jsonl)
  if [ $nc -gt 0 ]; then
    np=$(( nc < NP ? nc : NP ))
    seq 0 $((np-1)) | xargs -P $P -I{} bash -c 'f='$O'/sec/p{}; [ -f $f.done ] && exit 0; '$PY' -I tsec_exact.py 6 ../diagrams/n6.json '$c' '$O'/cells.jsonl $f.sec.jsonl --part {} --nparts '$np' > /dev/null 2> $f.err && '$PY' -I tcore.py $f.sec.jsonl $f.cores.jsonl > /dev/null 2>> $f.err && touch $f.done'
    [ -f $O/cert.jsonl.done ] || { TCERT_JOBS=$P $PY -I tcert.py 6 x $O/cert.jsonl $O/sec/p*.cores.jsonl > $O/cert.log 2>&1 && touch $O/cert.jsonl.done; }
  fi
  echo class $c cells $nc
done
echo exact done
