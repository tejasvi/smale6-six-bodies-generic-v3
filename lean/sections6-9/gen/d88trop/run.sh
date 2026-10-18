#!/bin/bash
# Regenerate the data of the Lean checks of Lemma 6.19(a) and build them. Run from the project root (the directory
# containing Lean6/), with D88 = the directory of the diagram-88 computations (containing certificates/ and scripts/),
# PY = a Python 3 with sympy, numpy and scipy, and Singular, msolve on the PATH. Set OPENBLAS_NUM_THREADS=1.
#   1. G, its reduction and the cofactors of (i) (sympy checks every identity), compared with the gfan inputs:
#        $PY -I gen/d88trop/mkdata.py n4 OUT $D88/certificates/n4_trop/work/n4_all.gfan
#        $PY -I gen/d88trop/mkdata.py kc OUT $D88/certificates/kc_trop/single_pass/kc_all.gfan
#   2. the covering (HiGHS proposes, every certificate is exact; torus certificates from Singular `lift`), then the
#      final torus certificates with the fallbacks of `torus_one` (about 20 and 25 minutes on 64 cores):
#        $PY -I gen/d88trop/dfs.py n4 OUT early ; $PY -I gen/d88trop/dfs.py n4 OUT resume
#        $PY -I gen/d88trop/dfs.py kc OUT early ; $PY -I gen/d88trop/dfs.py kc OUT resume
#      (`early` tests torus emptiness after every polynomial and stops at the first certificate; `resume` redoes the
#      final tests from the saved state OUT/<kind>_state.pkl.) HiGHS proposes the LP certificates, so a rerun can
#      produce a different tree; every tree that passes the checker proves the same theorem.
#   3. the Lean data modules: $PY -I gen/d88trop/emit.py n4 OUT . ; $PY -I gen/d88trop/emit.py kc OUT .
#   4. the systems assumed torus-empty (leaves `hyp`), with Singular and msolve: $PY -I gen/d88trop/hypcheck.py OUT
#   5. build and axioms:  lake build Lean6.Special.D88.Trop ; lake env lean gen/d88trop/axioms.lean
#      negative controls: lake env lean gen/d88trop/negctl.lean
set -euo pipefail
echo "see the comments of this file"
