#!/usr/bin/env bash
# Checks version 3 of the formalization of Theorem 1.1 (the kernel route; `./check.sh v3` runs this script).
#  1. Scans the sources for forbidden keywords as check.sh does; in addition the modules of the kernel route of the
#     composition (the *Core modules, ClassesLit, V3/ except Native.lean) must not use `native_decide`. lean6's tools
#     f2sexport, f2sprof, f34sstats and f34kexport (executables that write data or measurements; the kernel checks
#     read their output only as data that the drivers compare with committed hash lists) use `unsafe` and
#     `implemented_by` for speed: the scan skips them and fails if a module imports them. After step 2 the scan is
#     repeated, for the modules that the drivers generate.
#  2. Builds the kernel checks of the certificate projects with their drivers, under a memory budget:
#     ../sections3-5 and ../sections6-9, each `scripts/kern/build.sh`; their check
#     modules are compiled by lean directly into <project>/out.
#  3. Builds CC6Full and the composition with Lake, at most JOBS Lean processes at once, and prints the axioms of the
#     theorems listed in Check.lean (the main results of CC6Full), as check.sh does: only propext, Classical.choice and
#     Quot.sound are allowed.
#  4. Compiles the modules of the kernel route that import the kernel checks (V3/Kernel.lean, V3/Release.lean) with
#     lean directly, on LEAN_PATH = ../sections3-5/out : ../sections6-9/out : the composition's Lake path, and prints the
#     axioms of CC6Compose.V3.main_theorem_v3 (Compose/CheckV3.lean).
# Fails on a forbidden keyword, a build error, another axiom in Check.lean, or an axiom list of main_theorem_v3 other
# than exactly propext, Classical.choice, Quot.sound and the auxiliary axioms of the two F4 runs behind count_S12 and
# count_KC (Lemma 6.19(b)). Needs the
# certificate projects at ../sections3-5 and ../sections6-9, with the inputs that are
# distributed separately: lean6's certificate texts unpacked (data/f4/certs_txt, read by the generator of the kernel
# certificates) and lean6_special's certificates data/kern/cert/*.cert.xz (Lemma 7.9 on the fourteen charts, the
# escape-ray system of KC), each checked by the drivers against the projects' SHA-256 lists; and Mathlib (`lake exe
# cache get`). Environment: JOBS (Lean processes run by Lake at once, default 40: some modules of lean6_special take
# more than 10 GB), BUDGET_GB (memory budget of the drivers, default 600), L6_STAGES, SP_STAGES (the drivers' stages;
# set to the empty string, the kernel checks of that project are not built and its out/ is used as built before).
set -euo pipefail
cd "$(dirname "$0")"

JOBS=${JOBS:-40}
BUDGET_GB=${BUDGET_GB:-600}
L6_STAGES=${L6_STAGES-libs f1 f4gen f4 f34kexport f34kgen f34k}
SP_STAGES=${SP_STAGES-libs boxes d98 e4 c4gen c4 tropgen trop tropmem axioms}
L6=$(cd ../sections3-5 && pwd)
SP=$(cd ../sections6-9 && pwd)

KW='sorry|admit|axiom|implemented_by|extern|unsafe|ofReduceBool|ofReduceNat|reduceBool|reduceNat|skipKernelTC'
KW="$KW|addDeclWithoutChecking"
# grep's exit status: 0 lines found, 1 none, 2 an error (a missing file), which fails the check as well
scan() {  # scan PATTERN PATH...
  local rc=0
  /usr/bin/grep -rnwE "$1" "${@:2}" || rc=$?
  [ $rc != 0 ] || { echo "check_v3.sh: forbidden keyword in the sources" >&2; exit 1; }
  [ $rc = 1 ] || { echo "check_v3.sh: the keyword scan failed" >&2; exit 1; }
}
C=Compose/CC6Compose
scan "$KW|native_decide|native" CC6Full.lean CC6Full
scan "$KW|native_decide" $C/EnumCore.lean $C/CellsCore.lean $C/ClaimCore.lean $C/SpecialCore.lean $C/OpenCore.lean \
  $C/ClassesLit.lean $C/V3/Interface.lean $C/V3/Main.lean $C/V3/Special.lean $C/V3/Kernel.lean $C/V3/Release.lean
TOOLS=(L6K/F2S/Export L6K/F2S/Prof L6K/F34S/Stats L6K/F34K/Export)
scan_projects() {
  local hits t rc=0 ex=() im=()
  for t in "${TOOLS[@]}"; do ex+=(-e "$L6/$t.lean:"); im+=(-e "import ${t//\//.}"); done
  hits=$(/usr/bin/grep -rnwE "$KW" Compose/CC6Compose.lean $C "$SP/Lean6" "$SP"/L6*.lean "$SP"/L6*/ \
    "$L6"/L6*.lean "$L6"/L6*/) || rc=$?
  [ $rc -le 1 ] || { echo "check_v3.sh: the keyword scan failed" >&2; exit 1; }
  hits=$(printf '%s\n' "$hits" | /usr/bin/grep -vF "${ex[@]}" || true)
  [ -z "$hits" ] || { echo "$hits"; echo "check_v3.sh: forbidden keyword in the sources" >&2; exit 1; }
  rc=0
  /usr/bin/grep -rnwF "${im[@]}" CC6Full.lean CC6Full Compose/CC6Compose.lean $C "$SP/Lean6" "$SP"/L6*.lean \
    "$SP"/L6*/ "$L6"/L6*.lean "$L6"/L6*/ || rc=$?
  [ $rc != 0 ] || { echo "check_v3.sh: a module imports one of lean6's tools" >&2; exit 1; }
  [ $rc = 1 ] || { echo "check_v3.sh: the keyword scan failed" >&2; exit 1; }
}
scan_projects
echo "check_v3.sh: keyword scan OK"

ulimit -n "$(ulimit -Hn)" 2>/dev/null || true   # the soft limit on open files, raised to the hard limit
kern() {  # kern NAME DIR STAGES
  if [ -z "$3" ]; then
    echo "check_v3.sh: kernel checks of $1 not built here: $2/out as built before"
    return
  fi
  SECONDS=0
  (cd "$2" && BUDGET_GB=$BUDGET_GB nice -n 10 bash scripts/kern/build.sh $3)
  echo "check_v3.sh: kernel checks of $1 built in ${SECONDS} s"
}
kern lean6 "$L6" "$L6_STAGES"
kern lean6_special "$SP" "$SP_STAGES"
scan_projects
echo "check_v3.sh: keyword scan of the generated modules OK"

export LEAN_NUM_THREADS=$JOBS
SECONDS=0
nice -n 10 lake build
(cd Compose && nice -n 10 lake build)
echo "check_v3.sh: CC6Full and the composition built in ${SECONDS} s"
unset LEAN_NUM_THREADS

out=$(nice -n 10 lake env lean -j4 Check.lean) || { echo "$out"; echo "check_v3.sh: Check.lean failed" >&2; exit 1; }
echo "$out"
n=$(/usr/bin/grep -c "^#print axioms" Check.lean)
ok=$(echo "$out" | /usr/bin/grep -cE "depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$|does not depend on any axioms" || true)
if [ "$n" -eq 0 ] || [ "$ok" -ne "$n" ]; then
  echo "check_v3.sh: $ok of $n theorems of Check.lean use only propext, Classical.choice, Quot.sound" >&2
  exit 1
fi
echo "check_v3.sh: Check.lean OK ($n theorems, only propext, Classical.choice, Quot.sound)"

cd Compose
LP="$L6/out:$SP/out:$(lake env printenv LEAN_PATH)"
B=.lake/build/lib/lean/CC6Compose/V3
for m in Kernel Release; do
  LEAN_PATH=$LP nice -n 10 lean -j4 -o $B/$m.olean -i $B/$m.ilean CC6Compose/V3/$m.lean ||
    { echo "check_v3.sh: CC6Compose/V3/$m.lean failed" >&2; exit 1; }
done
out=$(LEAN_PATH=$LP nice -n 10 lean -j4 CheckV3.lean) ||
  { echo "$out"; echo "check_v3.sh: Compose/CheckV3.lean failed" >&2; exit 1; }
echo "$out"
ax=$(echo "$out" | tr -d '\n' | sed 's/.*depends on axioms: \[//; s/\].*//' | tr ',' '\n' |
  sed 's/^ *//; s/ *$//' | sort)
want=$(printf '%s\n' propext Classical.choice Quot.sound \
  Lean6.Special.Comp.Count.s12_f4_ok._native.native_decide.ax_1_1 \
  Lean6.Special.Comp.Count.kc_f4_ok._native.native_decide.ax_1_1 | sort)
if [ "$ax" != "$want" ]; then
  echo "check_v3.sh: the axioms of CC6Compose.V3.main_theorem_v3 are not exactly the expected five" >&2
  exit 1
fi
echo "check_v3.sh: CC6Compose.V3.main_theorem_v3 depends on propext, Classical.choice, Quot.sound and the auxiliary"
echo "check_v3.sh: axioms of the F4 runs behind count_S12 and count_KC, nothing else"
echo "check_v3.sh: OK"
