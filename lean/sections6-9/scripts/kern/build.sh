#!/bin/bash
# Builds the kernel-only versions (`decide +kernel`, no `native_decide`) of checks of lean6_special, from its root,
# stage by stage:
#
#   scripts/kern/build.sh STAGE...      stages, in this order: libs boxes d98 e4 c4gen c4 tropgen trop tropmem axioms
#
# libs      Lake: lean6_special (Lean6Special, Lean6SpecialComp) and the libraries L6KSpec, L6SoundKSpec.
# boxes     Lemma 6.19(c), (d) and the counts of Sec. 6.7: the committed modules L6CheckKSpec/N4, KC and the data
#           data/ksp (checked to be those that ksp_gen.py, kc_classes.lean and kspc_gen.py write from lean6_special's
#           box strings), then L6CheckKSpec/Final.
# d98       The D98 computations (Lemma 6.9 and the (1,2,7) check): L6CheckKSpec/D98.lean, written by hand.
# e4        The Macaulay checks of Sec. 7.2: the committed modules L6CheckKSpec/E4 (checked to be those that
#           ke4_gen.py writes), then L6CheckKSpec/E4Final.
# c4gen     Lemma 7.9 over F_32003: the certificates data/kern/cert/*.cert.xz (distributed separately) are compared
#           with data/kern/SHA256SUMS, the chart equations are printed by gen/c4/dump_eqs.lean, kc4_gen.py writes
#           L6CheckC4 and data/c4k, and their hashes are compared with data/c4k/SHA256SUMS.
# c4        The modules of L6CheckC4 (hashes compared again first).
# tropgen   Lemma 6.19(a)(iii)-(iv): ktrop_gen.py writes L6CheckTrop and data/tropk for KC (with the cofactor
#           certificate of its escape-ray system) and for N4 (with the traced Buchberger run of its escape-ray system,
#           checked as a chain of identities), and their hashes are compared with data/tropk/SHA256SUMS.
# trop      The modules of L6CheckTrop (hashes compared again first).
# tropmem   Lemma 6.19(a)(i), (ii): L6CheckKSpec/TropUnits, TropMem and TropSame (the statements are lean6_special's).
# axioms    The axioms of the final theorems (logs/kern/axioms.txt); each must be [propext, Classical.choice,
#           Quot.sound].
#
# Every check module is compiled by `lean` directly (one process per module, nice 10) under a memory budget by the
# scheduler kf1_build.py, stage by stage (by levels of the dependency order for the generated families,
# levels.py); the .olean files go to out/. The estimate of each module (GB), which the scheduler adds up against
# BUDGET_GB, is set below per family, from the largest peaks measured.
#
# Environment: BUDGET_GB (default 600), MAXJOBS (default 200), JOBS (generator processes, default 64), LOGS (default
# logs/kern).
set -u
export LC_ALL=C
cd "$(dirname "$0")/../.." || exit 1
BUDGET_GB=${BUDGET_GB:-600}
MAXJOBS=${MAXJOBS:-200}
JOBS=${JOBS:-64}
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
  diff <(awk '{print $2}' "$sums" | sed 's/^\*//' | sort) <(find "$@" -type f ! -name SHA256SUMS | sort) > /dev/null ||
    { echo "FILE SET DIFFERS ($sums)"; return 1; }
  echo "hashes ok: $sums ($(wc -l < "$sums") files)"
}

# the certificates (xz) against the digests of the uncompressed files in data/kern/SHA256SUMS
verify_certs() {
  local h f bad=0
  while read -r h f; do
    [ "$(xz -dc data/kern/cert/$f.xz | sha256sum | cut -c1-64)" = "$h" ] || { echo "certificate $f differs"; bad=1; }
  done < data/kern/SHA256SUMS
  [ $bad = 0 ] && echo "certificates ok: data/kern/SHA256SUMS ($(wc -l < data/kern/SHA256SUMS) files)"
  return $bad
}

# the committed modules (and data) of a family are those its generator writes now
same_as_generated() {  # same_as_generated TMPROOT PATH...
  local t=$1 p; shift
  for p in "$@"; do
    diff -r "$t/$p" "$p" > /dev/null || { echo "$p: the generator does not reproduce the committed files"; return 1; }
  done
  echo "reproduced by the generator: $*"
}

# kf1_build.py over the levels of the dependency order of DEPS files, estimates by KS_EST_RULES
build_levels() {  # build_levels LOG DEPS...
  local log=$1 line; shift
  python3 $S/levels.py "$@" > out/levels.txt || return 1
  while read -r line; do
    python3 $S/kf1_build.py $log $BUDGET_GB $MAXJOBS $line || return 1
  done < out/levels.txt
}

axioms_of() {  # axioms_of OUT IMPORT... -- THEOREM...
  local out=$1 m; shift
  { while [ "$1" != "--" ]; do echo "import $1"; shift; done; shift
    for m in "$@"; do echo "#print axioms $m"; done; } > out/Axioms.lean
  nice -n 10 lean out/Axioms.lean > $out 2>&1
  cat $out
  [ "$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" $out)" = "$#" ]
}

stage_libs() {
  nice -n 10 lake build Lean6Special Lean6SpecialComp L6KSpec L6SoundKSpec 2>&1 | tail -n 3
  [ "${PIPESTATUS[0]}" = 0 ]
}

# Box estimates: a box module 4 GB (measured at most 3.7), a count module Cnt<k> 10 (8.2), N4/All 20 (16.5), KC/All
# 8 (5.1), KC/Counts (after KC/All) 8, Final 12.
stage_boxes() {
  local t=$(mktemp -d) r=$PWD
  lean_path
  # the classes of the KC boxes (kc_classes.lean, from the sorted box strings), then the modules
  python3 $S/ksp_gen.py . $t N4 64 > /dev/null && python3 $S/ksp_gen.py . $t KC 64 > /dev/null &&
    (cd $t && nice -n 10 lean -R $r --run $r/$S/kc_classes.lean) &&
    python3 $S/kspc_gen.py $t $t/data/ksp/KC_classes.txt 64 > /dev/null || { rm -rf $t; return 1; }
  cmp -s $t/data/ksp/KC_classes.txt data/ksp/KC_classes.txt ||
    { echo "data/ksp/KC_classes.txt: kc_classes.lean does not reproduce the committed file"; rm -rf $t; return 1; }
  same_as_generated $t L6CheckKSpec/N4 L6CheckKSpec/KC || { rm -rf $t; return 1; }
  diff <(cd $t/data/ksp && ls *_M*.bin | xargs sha256sum) <(cd data/ksp && ls *_M*.bin | xargs sha256sum) > /dev/null ||
    { echo "data/ksp: the generator does not reproduce the committed box data"; rm -rf $t; return 1; }
  rm -rf $t
  lean_path
  local log=$LOGS/boxes_build.log
  python3 $S/kf1_build.py $log $BUDGET_GB $MAXJOBS $(ls L6CheckKSpec/N4/M*.lean L6CheckKSpec/KC/M*.lean | sed 's/$/:4/') || return 1
  python3 $S/kf1_build.py $log $BUDGET_GB $MAXJOBS $(ls L6CheckKSpec/KC/Cnt*.lean | sed 's/$/:10/') || return 1
  python3 $S/kf1_build.py $log $BUDGET_GB 2 L6CheckKSpec/N4/All.lean:20 L6CheckKSpec/KC/All.lean:8 || return 1
  python3 $S/kf1_build.py $log $BUDGET_GB 1 L6CheckKSpec/KC/Counts.lean:8 L6CheckKSpec/Final.lean:12 || return 1
  axioms_of $LOGS/boxes_axioms.txt L6CheckKSpec.Final -- Lean6.Special.D88.BoxesK.lemma_6_19_c \
    Lean6.Special.D88.BoxesK.lemma_6_19_d Lean6.Special.D88.BoxesK.sec_6_7_counts
}

# D98 estimate: 4 GB (measured 0.8).
stage_d98() {
  lean_path
  python3 $S/kf1_build.py $LOGS/d98_build.log $BUDGET_GB 1 L6CheckKSpec/D98.lean:4 || return 1
  axioms_of $LOGS/d98_axioms.txt L6CheckKSpec.D98 -- $(grep -oE '^theorem [A-Za-z0-9_]+' L6CheckKSpec/D98.lean |
    awk '{print "Lean6.Special.Comp.D98K." $2}')
}

# E4 estimates: a pattern module 7 GB (measured at most 5.4), All 20, E4Final 12 (9.8).
stage_e4() {
  local t=$(mktemp -d)
  python3 $S/ke4_gen.py $t 8 > /dev/null || { rm -rf $t; return 1; }
  same_as_generated $t L6CheckKSpec/E4 || { rm -rf $t; return 1; }
  rm -rf $t
  lean_path
  local log=$LOGS/e4_build.log
  python3 $S/kf1_build.py $log $BUDGET_GB $MAXJOBS $(ls L6CheckKSpec/E4/[FG]*.lean | sed 's/$/:7/') || return 1
  python3 $S/kf1_build.py $log $BUDGET_GB 1 L6CheckKSpec/E4/All.lean:20 L6CheckKSpec/E4Final.lean:12 || return 1
  axioms_of $LOGS/e4_axioms.txt L6CheckKSpec.E4Final -- Lean6.Special.K4.E4K.lemma_7_7 Lean6.Special.K4.E4K.check_3_5_7_11
}

# kc4_gen.py: patterns of at most 60,000 term products (split variables chosen greedily), packed into buckets of at
# most 12,000, modules of at most 400,000; codes compared in intervals of 16,000 (KC4_COVER).
C4_CHARTS="s_p12 s_p13 s_p14 s_p23 s_p24 s_p34 s_c t_p12 t_p13 t_p14 t_p23 t_p24 t_p34 t_c"
stage_c4gen() {
  verify_certs || return 1
  rm -rf L6CheckC4 data/c4k/*.bin data/c4k/*.idx data/c4k/lean_eqs.txt
  mkdir -p data/c4k
  nice -n 10 lake env lean gen/c4/dump_eqs.lean > data/c4k/lean_eqs.txt || return 1
  KC4_JOBS=$JOBS python3 $S/kc4_gen.py . data/c4k/lean_eqs.txt "[3, 5, 7, 11]" 32003 12000 60000 400000 \
    $(for c in $C4_CHARTS; do echo "$c=data/kern/cert/c4_3_5_7_11_$c.cert.xz"; done) > $LOGS/c4_gen.log 2>&1 || return 1
  verify data/c4k/SHA256SUMS L6CheckC4 data/c4k
}

# C4 estimates: an interval module Ivl<q> 34 GB (measured 24-33 for the large charts), a bucket module B<m> 17
# (at most 16.4, mean 3.1), Main, Bridge and Final 8 (at most 7.2), the others 2 (at most 1.7).
C4_EST='\.Ivl[0-9]+$=34 \.B[0-9]+$=17 \.(Main|Bridge|Final)$=8 .=2'
stage_c4() {
  verify data/c4k/SHA256SUMS L6CheckC4 data/c4k || return 1
  lean_path
  KS_EST_RULES=$C4_EST build_levels $LOGS/c4_build.log L6CheckC4/deps.txt L6CheckC4/deps_final.txt || return 1
  axioms_of $LOGS/c4_axioms.txt L6CheckC4.Final -- L6CheckC4.lemma_7_9_32003
}

stage_tropgen() {
  verify_certs || return 1
  rm -rf L6CheckTrop data/tropk/*.bin data/tropk/*.idx
  xz -dc data/kern/cert/trace_hypN4.txt.xz > out/trace_hypN4.txt || return 1
  { python3 $S/ktrop_gen.py . . KC data/kern/cert/esc_kc_0.cert.xz 60000 60000 400000 &&
    python3 $S/ktrop_gen.py . . N4 trace:out/trace_hypN4.txt 60000 60000 400000; } > $LOGS/trop_gen.log 2>&1 || return 1
  rm -f out/trace_hypN4.txt
  verify data/tropk/SHA256SUMS L6CheckTrop data/tropk
}

# Trop estimates: the covering check of N4 48 GB (measured 43), of KC 8 (6.4); N4's Small 20 (17); the chain of N4,
# a step module 8 (5.7), Ok 26 (21.7), Tab 4 (2.1); an interval module 15 (13.1), a bucket module 16 (14.1); Small,
# Main, Bridge, Final 8 (at most 7.4); the others 2 (at most 1.7).
TROP_EST='^L6CheckTrop\.N4\.Cover$=48 ^L6CheckTrop\.KC\.Cover$=8 ^L6CheckTrop\.N4\.Small$=20 \.Chain\.B[0-9]+$=8 \.Chain\.Ok$=26 \.Chain\.Tab$=4 \.Ivl[0-9]+$=15 \.B[0-9]+$=16 \.(Small|Main|Bridge|Final|Tree)$=8 .=2'
stage_trop() {
  verify data/tropk/SHA256SUMS L6CheckTrop data/tropk || return 1
  lean_path
  KS_EST_RULES=$TROP_EST build_levels $LOGS/trop_build.log L6CheckTrop/deps_KC.txt L6CheckTrop/deps_N4.txt || return 1
  axioms_of $LOGS/trop_axioms.txt L6CheckTrop.KC.Final L6CheckTrop.N4.Final -- Lean6.Special.D88.TropK.kc_torus_gamma \
    Lean6.Special.D88.TropK.n4_torus_gamma
}

# Estimates: TropUnits 4 GB, TropMem 20 (16), TropSame 8.
stage_tropmem() {
  lean_path
  python3 $S/kf1_build.py $LOGS/tropmem_build.log $BUDGET_GB 2 L6CheckKSpec/TropUnits.lean:4 L6CheckKSpec/TropMem.lean:20 || return 1
  python3 $S/kf1_build.py $LOGS/tropmem_build.log $BUDGET_GB 1 L6CheckKSpec/TropSame.lean:8 || return 1
  axioms_of $LOGS/tropmem_axioms.txt L6CheckKSpec.TropSame -- Lean6.Special.Comp.D88.TropK.n4_units_ok \
    Lean6.Special.Comp.D88.TropK.kc_units_ok Lean6.Special.D88.TropK.n4_G_mem Lean6.Special.D88.TropK.kc_G_mem
}

stage_axioms() {
  lean_path
  axioms_of $LOGS/axioms.txt L6CheckKSpec.Final L6CheckKSpec.D98 L6CheckKSpec.E4Final L6CheckC4.Final \
    L6CheckTrop.KC.Final L6CheckTrop.N4.Final L6CheckKSpec.TropSame -- \
    Lean6.Special.D88.BoxesK.lemma_6_19_c Lean6.Special.D88.BoxesK.lemma_6_19_d Lean6.Special.D88.BoxesK.sec_6_7_counts \
    $(grep -oE '^theorem [A-Za-z0-9_]+' L6CheckKSpec/D98.lean | awk '{print "Lean6.Special.Comp.D98K." $2}') \
    Lean6.Special.K4.E4K.lemma_7_7 Lean6.Special.K4.E4K.check_3_5_7_11 L6CheckC4.lemma_7_9_32003 \
    Lean6.Special.D88.TropK.kc_torus_gamma Lean6.Special.D88.TropK.n4_torus_gamma Lean6.Special.Comp.D88.TropK.n4_units_ok \
    Lean6.Special.Comp.D88.TropK.kc_units_ok Lean6.Special.D88.TropK.n4_G_mem Lean6.Special.D88.TropK.kc_G_mem
}

[ $# -gt 0 ] || { sed -n '2,36p' "$0"; exit 2; }
for st in "$@"; do
  echo "== stage $st $(date -u +%FT%TZ)"
  "stage_$st" || { echo "== stage $st FAILED"; exit 1; }
  echo "== stage $st done $(date -u +%FT%TZ)"
done
