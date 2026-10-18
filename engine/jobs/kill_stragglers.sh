#!/bin/bash
# kill tcore.py runs older than LIMIT seconds; mark their parts done with a .timeout marker (cells stay unresolved)
LIMIT=${1:-1800}
for line in $(ps -u $(id -un) -o pid=,etimes=,args= | awk -v L=$LIMIT '$3 ~ /python/ && $5 == "tcore.py" && $2 > L {print $1"|"$7}'); do
  pid=${line%%|*}; out=${line#*|}; base=${out%.cores.jsonl}
  kill $pid && touch $base.timeout && sleep 1 && touch $base.done && echo "killed $pid $base"
done
