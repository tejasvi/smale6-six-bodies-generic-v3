#!/usr/bin/env bash
# Checks the formalization of Theorem 1.1.
#  1. Scans the sources for forbidden keywords: in CC6Full, everything that can add an assumption, replace compiled
#     code or bypass the kernel, `native_decide` included; in the composition (Compose) and in the certificate
#     projects ../sections6-9 and ../sections3-5, the same list without `native_decide`.
#  2. Builds CC6Full and the composition. The composition builds the modules of ../sections6-9 and ../sections3-5 that it
#     imports, and every `native_decide` in them is evaluated when its module is built.
#  3. Prints the axioms of the theorems listed in Check.lean (only propext, Classical.choice and Quot.sound allowed)
#     and of the main theorem CC6Compose.main_theorem in Compose/Check.lean (these three and the auxiliary axioms of
#     `native_decide`).
# Fails on a forbidden keyword, a build error or another axiom. Needs the certificate projects at ../sections6-9 and
# ../sections3-5, the latter with its certificates unpacked (scripts/poly/unpack_certs.sh there), and Mathlib
# (`lake exe cache get`). Runs Lean at low priority (nice -n 10). The libraries pass -j4 to Lean (at most four threads
# per Lean process); LEAN_NUM_THREADS is not set, since it also limits the number of jobs that Lake runs in parallel.
set -euo pipefail
cd "$(dirname "$0")"

# `./check.sh v3`: version 3, the kernel route (check_v3.sh)
if [ "${1:-}" = v3 ]; then exec ./check_v3.sh; fi

KW='sorry|admit|axiom|implemented_by|extern|unsafe|ofReduceBool|ofReduceNat|reduceBool|reduceNat|skipKernelTC|addDeclWithoutChecking'
scan() {
  if /usr/bin/grep -rnwE "$1" "${@:2}"; then
    echo "check.sh: forbidden keyword in the sources" >&2
    exit 1
  fi
}
scan "$KW|native_decide|native" CC6Full.lean CC6Full
scan "$KW" Compose/CC6Compose.lean Compose/CC6Compose ../sections6-9/Lean6 ../sections3-5/L6*.lean ../sections3-5/L6*/
echo "check.sh: keyword scan OK"

ulimit -n "$(ulimit -Hn)" 2>/dev/null || true   # the soft limit on open files, raised to the hard limit
SECONDS=0
nice -n 10 lake build
echo "check.sh: CC6Full built in ${SECONDS} s"
SECONDS=0
(cd Compose && nice -n 10 lake build)
echo "check.sh: composition built in ${SECONDS} s"

out=$(nice -n 10 lake env lean -j4 Check.lean) || { echo "$out"; echo "check.sh: Check.lean failed" >&2; exit 1; }
echo "$out"
n=$(/usr/bin/grep -c "^#print axioms" Check.lean)
ok=$(echo "$out" | /usr/bin/grep -cE "depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$|does not depend on any axioms" || true)
if [ "$ok" -ne "$n" ]; then
  echo "check.sh: $ok of $n theorems use only propext, Classical.choice, Quot.sound" >&2
  exit 1
fi
echo "check.sh: Check.lean OK ($n theorems)"

out=$(cd Compose && nice -n 10 lake env lean -j4 Check.lean) ||
  { echo "$out"; echo "check.sh: Compose/Check.lean failed" >&2; exit 1; }
if ! /usr/bin/grep -q "^'CC6Compose.main_theorem' depends on axioms: \[" <<< "$out"; then
  echo "$out"
  echo "check.sh: no axiom list for CC6Compose.main_theorem" >&2
  exit 1
fi
ax=$(echo "$out" | tr -d '\n' | sed 's/.*depends on axioms: \[//; s/\].*//' | tr ',' '\n' | sed 's/^ *//; s/ *$//')
std=$(echo "$ax" | /usr/bin/grep -cxE 'propext|Classical\.choice|Quot\.sound' || true)
nat=$(echo "$ax" | /usr/bin/grep -cE '\._native\.native_decide\.ax_[0-9]+_[0-9]+$' || true)
other=$(echo "$ax" | /usr/bin/grep -vxE 'propext|Classical\.choice|Quot\.sound' |
  /usr/bin/grep -vE '\._native\.native_decide\.ax_[0-9]+_[0-9]+$' || true)
if [ -n "$other" ]; then
  echo "$other"
  echo "check.sh: CC6Compose.main_theorem depends on the axioms above" >&2
  exit 1
fi
echo "check.sh: CC6Compose.main_theorem depends on $std of propext, Classical.choice, Quot.sound and on $nat auxiliary axioms of native_decide, nothing else"
echo "check.sh: OK"
