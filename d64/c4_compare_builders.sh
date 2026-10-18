#!/bin/bash
# Check that the Singular checker (c4_cert_singular.sing) and the Python builder (c4_systems.py) build identical
# polynomials for the compact C4 model at mu0 = (3,5,7,11).  Usage: bash d64/c4_compare_builders.sh
set -e
D=$(cd "$(dirname "$0")" && pwd)
T=$(mktemp -d)
sed -e 's/^int CHAR = 32003;/int CHAR = 0;/' \
    -e 's/^"number of equations:", cnt;/"number of equations:", cnt; int ii; for (ii=1; ii<=cnt; ii++) { "EQ", ii; print(I[ii]); } quit;/' \
    "$D/c4_cert_singular.sing" > "$T/print.sing"
Singular -q "$T/print.sing" 2>/dev/null | grep -v redefining > "$T/sing_eqs.txt"
"${PY:-python3}" -I - "$T/sing_eqs.txt" "$D" <<'PY'
import sys, re
sys.path.insert(0, sys.argv[2])
import c4_systems as C
import sympy as sp
txt = open(sys.argv[1]).read()
blocks = re.split(r'EQ\s*\n?\s*(\d+)\s*\n', txt)
sing = {int(blocks[i]): blocks[i + 1].replace('\n', '').strip() for i in range(1, len(blocks), 2)}
syms = sp.symbols(C.VARS); loc = dict(zip(C.VARS, syms))
ok = True
for idx, (name, f) in enumerate(C.build([3, 5, 7, 11]), 1):
    a = sp.expand(sp.sympify(C.to_string(f, C.VARS).replace('^', '**'), locals=loc))
    b = sp.expand(sp.sympify(sing[idx].replace('^', '**'), locals=loc))
    same = sp.expand(a - b) == 0
    ok &= same
    print(idx, name, 'identical' if same else 'DIFFERENT')
print('ALL IDENTICAL' if ok else 'MISMATCH')
sys.exit(0 if ok else 1)
PY
rm -rf "$T"
