#!/bin/bash
# Referee re-run of the exact pipeline for the classes in $CLASSES, from a copy of the engine code
# (CODE: a directory holding the engine programs and n6.json; the referee used a snapshot of 2026-10-16 18:56 UTC),
# at nice 10, single-threaded BLAS.
#  1. treplay.py in 384 parts (--split 3), each compared line by line (--ref) with the stored part;
#  2. tsec_exact.py on the cells (NP parts), 3. tcore.py, 4. tcert.py.
# Results in $OUT/cCLS/ (default rerun/exact6).
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
PY=${PY:-python3}
CODE=${CODE:?set CODE to a directory holding the engine programs and n6.json}
OUT=${OUT:-$PWD/rerun/exact6}
STORE=${STORE:?set STORE to the root of the supplement (its results/exact6/cN are the stored runs)}
P=${P:-64}; NP=${NP:-384}
cd $CODE
for c in $CLASSES; do
  O=$OUT/c$c; mkdir -p $O/rep $O/sec
  S=$(ls -d $STORE/*/exact6/c$c | head -1)
  t0=$(date +%s)
  seq 0 383 | xargs -P $P -I{} bash -c 'f='$O'/rep/p{}.jsonl; [ -f $f.done ] && exit 0; nice -n 10 '$PY' -I treplay.py 6 n6.json '$c' $f --mode le --base --split 3 --part {} --nparts 384 --ref '$S'/rep/p{}.jsonl > $f.log 2>&1 && touch $f.done'
  [ $(ls $O/rep/*.jsonl.done 2>/dev/null | wc -l) -eq 384 ] || { echo replay incomplete $c; continue; }
  [ -f $O/cells.jsonl.done ] || { cat $O/rep/p*.jsonl > $O/cells.jsonl && touch $O/cells.jsonl.done; }
  t1=$(date +%s)
  nc=$(wc -l < $O/cells.jsonl)
  if [ $nc -gt 0 ]; then
    np=$(( nc < NP ? nc : NP ))
    seq 0 $((np-1)) | xargs -P $P -I{} bash -c 'f='$O'/sec/p{}; [ -f $f.done ] && exit 0; nice -n 10 '$PY' -I tsec_exact.py 6 n6.json '$c' '$O'/cells.jsonl $f.sec.jsonl --part {} --nparts '$np' > /dev/null 2> $f.err && nice -n 10 '$PY' -I tcore.py $f.sec.jsonl $f.cores.jsonl > /dev/null 2>> $f.err && touch $f.done'
    t2=$(date +%s)
    [ -f $O/cert.jsonl.done ] || { TCERT_JOBS=$P nice -n 10 $PY -I tcert.py 6 x $O/cert.jsonl $O/sec/p*.cores.jsonl > $O/cert.log 2>&1 && touch $O/cert.jsonl.done; }
  else
    t2=$t1
  fi
  t3=$(date +%s)
  echo "class $c cells $nc replay $((t1-t0))s sec+core $((t2-t1))s cert $((t3-t2))s"
done
echo rerun done
