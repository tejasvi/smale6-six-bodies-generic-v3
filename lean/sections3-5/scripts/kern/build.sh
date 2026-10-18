#!/bin/bash
# Builds the kernel-only checks (`decide +kernel`, no `native_decide`) from the root of lean6, stage by stage.
#
#   scripts/kern/build.sh STAGE...      stages, in this order: libs f1 f4gen f4 f4link f34kexport f34kgen f34k
#
# libs        Lake: the libraries L6K, L6SoundK (and what they import) and the generators f1shardgen, f1repgen, f34kexport.
# f1          F1 (Proposition 3.1): the committed modules L6CheckK/F1 (written by kf1_modules.py from data/f1k), then
#             the axioms of L6CheckK.F1.F1_main_k.
# f4gen       F4 (Lemma 5.2): kf4_gen.py writes L6CheckK/F4 and data/f4k from lean6's certificate texts
#             (data/f4/certs_txt), then their hashes are compared with data/f4k/SHA256SUMS.
# f4          F4: the modules of L6CheckK/F4 (hashes compared again first), then the axioms of the 1,928 theorems
#             L6CheckK.F4.C<H>.cert.
# f4link      The links of lean6's certificate texts to the kernel certificates (committed modules L6CheckK/F4Link,
#             `native_decide`, not used by the kernel route); needs lean6's L6Check.Certs (scripts/build_all.sh).
# f34kexport  F2-F4 fused (Propositions 4.5 and 5.3): f34kexport writes the units, level nodes, claims and keep tables
#             of the classes of scripts/kern/f34k_classes.txt under data/f34k.
# f34kgen     kf34k_gen.py, kf34k_certs.py, kf34k_final.py write L6CheckF, then the hashes of L6CheckF and of the
#             exporter's output are compared with data/f34k/SHA256SUMS and data/f34k/EXPORT.sha256.
# f34k        The modules of L6CheckF (hashes compared again first), then the axioms of L6CheckF.fusedK.
#
# Every check module is compiled by `lean` directly (one process per module, nice 10) under a memory budget by the
# schedulers kf1_build.py (stages in order) and kf34k_build.py (dependency order); their .olean files go to out/.
# The estimate of each module (GB), which the schedulers add up against BUDGET_GB, is set below per family.
#
# Environment: BUDGET_GB (default 600), MAXJOBS (default 300), JOBS (exporter and F4 generator processes, default
# 300), LOGS (default logs/kern). Measured on machines with 384 cores and 708 GB: F1 26 CPU-hours, F4 24, F4Link 1
# (logs/kern); F2-F4 fused 927 (the kernel run of the track, on four machines).
set -u
export LC_ALL=C
cd "$(dirname "$0")/../.." || exit 1
BUDGET_GB=${BUDGET_GB:-600}
MAXJOBS=${MAXJOBS:-300}
JOBS=${JOBS:-300}
LOGS=${LOGS:-logs/kern}
S=scripts/kern
mkdir -p "$LOGS" out
ulimit -n 65536

lean_path() {
  export LEAN_PATH=$PWD/out:$(lake env printenv LEAN_PATH)
  export KF_OUT=out
}

# hashes of the generated files against a committed list (paths relative to the root), and no other files
verify() {  # verify SUMS DIR...
  local sums=$1; shift
  sha256sum --check --quiet --strict "$sums" || { echo "HASH MISMATCH ($sums)"; return 1; }
  diff <(awk '{print $2}' "$sums" | sed 's/^\*//' | LC_ALL=C sort) \
       <(find "$@" -type f ! -name SHA256SUMS | LC_ALL=C sort) > /dev/null || { echo "FILE SET DIFFERS ($sums)"; return 1; }
  echo "hashes ok: $sums ($(wc -l < "$sums") files)"
}

# the fused run: every generated file under L6CheckF and the lists classinfo.txt, certnames.txt against
# data/f34k/SHA256SUMS; the exporter's output per class (data/f34k/c<k>: the SHA-256 of the sorted list of the SHA-256
# of its files, their number and their bytes) against data/f34k/EXPORT.sha256
verify_f34k() {
  verify data/f34k/SHA256SUMS L6CheckF data/f34k/classinfo.txt data/f34k/certnames.txt || return 1
  local h d n b bad=0
  while read -r h d n b; do
    [ "$h $n $b" = "$(cd data/f34k/$d && find . -type f | sort | xargs sha256sum | sha256sum | cut -c1-64) $(find data/f34k/$d -type f | wc -l) $(find data/f34k/$d -type f -printf '%s\n' | awk '{s+=$1} END {print s}')" ] ||
      { echo "export data of $d differ"; bad=1; }
  done < data/f34k/EXPORT.sha256
  [ "$(ls -d data/f34k/c[0-9]* | wc -l)" = "$(wc -l < data/f34k/EXPORT.sha256)" ] || { echo "export classes differ"; bad=1; }
  [ $bad = 0 ] && echo "hashes ok: data/f34k/EXPORT.sha256 ($(wc -l < data/f34k/EXPORT.sha256) classes)"
  return $bad
}

stage_libs() {
  nice -n 10 lake build L6K L6SoundK f1shardgen f1repgen f34kexport 2>&1 | tail -n 3
  [ "${PIPESTATUS[0]}" = 0 ]
}

# F1 estimates: a shard or representative module, 2 GB + 16 MB per unit of cost of its heaviest declaration (a leaf, or
# a third of a labelled diagram found; kf1_estimates.py), representatives 5 GB; All 8, Global 60, Codes/C<t> 8,
# Codes/All 8, Main 10. Measured peaks: 6.95 GB (shards), 14.5 GB (Global).
stage_f1() {
  lean_path
  local log=$LOGS/f1_build.log
  python3 $S/kf1_build.py $log $BUDGET_GB $MAXJOBS $(python3 $S/kf1_estimates.py) || return 1
  python3 $S/kf1_build.py $log $BUDGET_GB 1 L6CheckK/F1/Reps/All.lean:8 L6CheckK/F1/All.lean:8 || return 1
  python3 $S/kf1_build.py $log $BUDGET_GB 64 L6CheckK/F1/Global.lean:60 $(ls L6CheckK/F1/Codes/C*.lean | sed 's/$/:8/') || return 1
  python3 $S/kf1_build.py $log $BUDGET_GB 1 L6CheckK/F1/Codes/All.lean:8 L6CheckK/F1/Main.lean:10 || return 1
  printf 'import L6CheckK.F1.Main\n#print axioms L6CheckK.F1.F1_main_k\n' > out/AxiomsF1.lean
  nice -n 10 lean out/AxiomsF1.lean > $LOGS/f1_axioms.txt 2>&1
  cat $LOGS/f1_axioms.txt
  grep -q "^'L6CheckK.F1.F1_main_k' depends on axioms: \[propext, Classical.choice, Quot.sound\]$" $LOGS/f1_axioms.txt
}

stage_f4gen() {
  rm -rf L6CheckK/F4 data/f4k/*.bin data/f4k/*.idx
  KF4_JOBS=$JOBS KF4_SPLIT=60000 python3 $S/kf4_gen.py . 12000 400000 data/f4/certs_txt/*.txt > $LOGS/f4_gen.log 2>&1 || return 1
  verify data/f4k/SHA256SUMS L6CheckK/F4 data/f4k
}

# F4 estimates, by the stages of L6CheckK/F4/modules.txt: data, packed and bucket modules 4 GB; certificate theorems
# and cover modules 12 GB. Measured peaks: 4.3 GB (bucket and packed modules), 11.1 GB (certificate theorems),
# 17.9 GB (a cover module).
stage_f4() {
  verify data/f4k/SHA256SUMS L6CheckK/F4 data/f4k || return 1
  lean_path
  local log=$LOGS/f4_build.log st mods
  for st in 1 2 3 4; do
    mods=$(awk -v s=$st '$1==s {m=$2; gsub(/\./, "/", m); est=(s>=3)?12:4; print m ".lean:" est}' L6CheckK/F4/modules.txt)
    [ -n "$mods" ] && { python3 $S/kf1_build.py $log $BUDGET_GB $MAXJOBS $mods || return 1; }
  done
  { awk '$1==4 {print "import " $2}' L6CheckK/F4/modules.txt
    for f in data/f4k/*.bin; do echo "#print axioms L6CheckK.F4.C$(basename $f .bin).cert"; done; } > out/AxiomsF4.lean
  nice -n 10 lean out/AxiomsF4.lean > $LOGS/f4_axioms.txt 2>&1
  local n=$(ls data/f4k/*.bin | wc -l)
  local ok=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" $LOGS/f4_axioms.txt)
  echo "F4: certificates $n, standard axioms only $ok"
  [ "$n" = "$ok" ]
}

# F4Link estimates: 12 GB per module (measured peak 7.8 GB).
stage_f4link() {
  lean_path
  # the committed modules are those that kf4_link_gen.py writes from the generated F4 sources
  local d=$(mktemp -d)
  mkdir -p $d/L6CheckK && ln -s "$PWD/L6CheckK/F4" $d/L6CheckK/F4
  python3 $S/kf4_link_gen.py $d > /dev/null && diff -r $d/L6CheckK/F4Link L6CheckK/F4Link > /dev/null ||
    { echo "F4Link: the generator does not reproduce the committed modules"; rm -rf $d; return 1; }
  rm -rf $d
  python3 $S/kf1_build.py $LOGS/f4link_build.log $BUDGET_GB 24 $(ls L6CheckK/F4Link/L*.lean | sed 's/$/:12/') || return 1
  { for f in L6CheckK/F4Link/L*.lean; do m=${f%.lean}; echo "import ${m//\//.}"; done
    for f in data/f4k/*.bin; do echo "#print axioms L6CheckK.F4Link.meaning_$(basename $f .bin)"; done; } > out/AxiomsF4Link.lean
  nice -n 10 lean out/AxiomsF4Link.lean > $LOGS/f4link_axioms.txt 2>&1
  # each meaning_<H>: the standard axioms and the auxiliary axiom of its own link_<H> (native_decide), nothing else
  python3 - $LOGS/f4link_axioms.txt $(ls data/f4k/*.bin | wc -l) <<'PY'
import re, sys
txt, n = open(sys.argv[1]).read(), int(sys.argv[2])
std = {'propext', 'Classical.choice', 'Quot.sound'}
ok = bad = 0
for m in re.finditer(r"'L6CheckK\.F4Link\.meaning_(\w+)' depends on axioms: \[(.*?)\]", txt, re.S):
    ax = {a.strip() for a in m.group(2).split(',')}
    aux = ax - std
    if std <= ax and len(aux) == 1 and re.fullmatch(rf'L6CheckK\.F4Link\.link_{m.group(1)}\._native\.native_decide\.ax_\d+(_\d+)?', aux.pop()):
        ok += 1
    else:
        bad += 1
print(f'F4Link: certificates {n}, meaning theorems with the standard axioms and their own link only {ok}, other {bad}')
sys.exit(0 if ok == n and bad == 0 and 'sorryAx' not in txt else 1)
PY
}

# The exporter's runs as in scripts/kern/f34k_classes.txt (lines `class depth programs`): a class with depth 0 in one
# run; a class split at depth d > 0 in its prefix and runs over its pairs (8 pairs per run for d = 4, otherwise 1).
# B: at most B weighted programs (tree programs counting 3) below the sibling nodes of a unit.
F34K_B=1000
stage_f34kexport() {
  local exe=.lake/build/bin/f34kexport out=data/f34k c d n i chunk max
  rm -rf $out/c[0-9]* $out/classinfo.txt $out/certnames.txt
  mkdir -p $out
  $exe info > $out/classinfo.txt || return 1
  ls data/f4/certs_txt | sed -n 's/\.txt$//p' | sort > $out/certnames.txt
  local tasks=$(mktemp)
  while read c d n; do
    if [ "$d" = 0 ]; then
      echo "$exe $c 0 0 1 $F34K_B . $out" >> $tasks
    else
      echo "$exe prefix $c $d . $out" >> $tasks
      if [ "$d" = 4 ]; then chunk=8; max=1300; else chunk=1; max=400; fi
      for ((i = 0; i < max; i += chunk)); do echo "$exe $c $d $i $((i + chunk)) $F34K_B . $out" >> $tasks; done
    fi
  done < $S/f34k_classes.txt
  echo "# start $(date -u +%FT%TZ) tasks $(wc -l < $tasks)" >> $LOGS/f34k_export.log
  xargs -P $JOBS -I{} sh -c 'nice -n 10 {} 2>&1 | tail -n 1' < $tasks >> $LOGS/f34k_export.log
  echo "# end $(date -u +%FT%TZ)" >> $LOGS/f34k_export.log
  rm -f $tasks
}

# kf34k_gen.py per class: groups of 20 units; the classes of f34k_levels_apart.txt with their level nodes grouped apart
# (a line `CLASS N depth`: at most N level nodes per group, grouped by depth; otherwise 200 per group, by id). The
# modules read the keep table of each node from data/f34k/c<k>/n<id>.tbl, relative to the root, when they are compiled.
stage_f34kgen() {
  local out=data/f34k c d n line apart gl bd
  rm -rf L6CheckF
  while read c d n; do
    apart=0; gl=200; bd=0
    line=$(grep -E "^$c( |\$)" $S/f34k_levels_apart.txt)
    if [ -n "$line" ]; then
      set -- $line; apart=1; [ -n "${2:-}" ] && gl=$2; [ "${3:-}" = depth ] && bd=1
    fi
    set -- $(grep "^$c " $out/classinfo.txt)
    KF34K_GROUP=20 KF34K_LEVELS_APART=$apart KF34K_LEVEL_GROUP=$gl KF34K_LEVELS_BY_DEPTH=$bd KF34K_TBL_DIR=$out/c$c \
      python3 $S/kf34k_gen.py $out/c$c $out/certnames.txt $c $2 $3 $4 $5 . . >> $LOGS/f34k_gen.log 2>&1 || return 1
  done < $S/f34k_classes.txt
  python3 $S/kf34k_certs.py $out/certnames.txt . . >> $LOGS/f34k_gen.log 2>&1 || return 1
  python3 $S/kf34k_final.py . >> $LOGS/f34k_gen.log 2>&1 || return 1
  verify_f34k
}

# F2-F4 estimates (kf34k_build.py, KF34K_EST): a group of kernel checks NG<g> max(2, 1 + 0.0045 * the weight of its
# largest unit) GB, a covering module VG<g> 3 GB, every other module 7 GB. The memory in use stayed near a third to
# 40 % of the sum of the estimates. Measured peaks: 20.6 GB (NG), 21.5 GB (VG), 26.7 GB (Final).
# On several machines: give each the deps files of a part of the classes (kf34k_split.py splits a class by export
# run), gather out/L6CheckF, then run this stage on one machine (built modules are skipped).
stage_f34k() {
  verify_f34k || return 1
  lean_path
  KF34K_EST=1,0.0045,2,3,7 python3 $S/kf34k_build.py . $LOGS/f34k_build.log $BUDGET_GB $MAXJOBS \
    L6CheckF/deps_certs.txt L6CheckF/C*/deps.txt L6CheckF/deps_final.txt || return 1
  printf 'import L6CheckF.Final\n#print axioms L6CheckF.fusedK\n' > out/AxiomsF34K.lean
  nice -n 10 lean out/AxiomsF34K.lean > $LOGS/f34k_axioms.txt 2>&1
  cat $LOGS/f34k_axioms.txt
  grep -q "^'L6CheckF.fusedK' depends on axioms: \[propext, Classical.choice, Quot.sound\]$" $LOGS/f34k_axioms.txt
}

[ $# -gt 0 ] || { sed -n '2,30p' "$0"; exit 2; }
for st in "$@"; do
  echo "== stage $st $(date -u +%FT%TZ)"
  "stage_$st" || { echo "== stage $st FAILED"; exit 1; }
  echo "== stage $st done $(date -u +%FT%TZ)"
done
