#!/usr/bin/env python3
"""Sanity tests of exactlp: the interior point satisfies all rows; the engine's single-term torques of the
residual single cells are re-certified exactly (single minimal term on the whole cell)."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
import exactlp as X
from fractions import Fraction as Fr

def interior_ok(P, rec):
    val = {}
    for (col, v), j in P.var.items():
        val[j] = Fr(str((rec['hz'] if col == 'z' else rec['hw'])[str(v)]))
    bad = 0
    for f, kind, lab in P.rows:
        x = sum(c * (val[j] if j != X.ONE else 1) for j, c in f.items())
        if kind == 'eq' and abs(x) > Fr(1, 10**4): bad += 1
        if kind == 'strict' and x <= 0: bad += 1
        if kind == 'weak' and x < -Fr(1, 10**4): bad += 1
    return bad

t0 = time.time()
n = ok = 0
for r in R.residual():
    if r['kind'] != 'single':
        continue
    c, i = r['class'], r['cell']
    rec = R.load_cell(c, i)
    D = X.Diag(R.classes()[c])
    P = X.Poly(rec, D)
    b = interior_ok(P, rec)
    idn, tm = r['engine_single']
    J = eval(idn)[1]; t = eval(tm)
    lab = ('zw', t[1], t[2]) if t[0] == 'T1' else ('zw', t[2], t[1])
    terms = P.torque_terms(J)
    res, certs = P.argmin_is(terms, [lab])
    n += 1; ok += res
    print(c, i, 'interior-bad', b, 'single-term', res, len(P.rows), round(time.time() - t0, 1), flush=True)
print(n, ok)
