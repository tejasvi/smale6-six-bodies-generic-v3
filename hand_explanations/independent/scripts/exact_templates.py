#!/usr/bin/env python3
"""Exact certificates (Lemma 4.4, referee's polyhedra) for the argmin sets of the secondary identities of the engine
cores of the 179 template-only cells: every non-minimal term strictly above the minimum on the open cell, and the
minimal terms equal on the cell (identical forms, or the difference in the span of the cell's equality rows)."""
import json, os, sys
from collections import Counter
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refkit as K
from ref_lp import CellLP
from ref_exact import certify_positive, solve_exact, to_fr
import verify_templates as V          # (re-runs its float checks; reuses its data and helpers)


def in_equality_span(L, d):
    """d (linear form, no s) is a combination of the equality rows of the cell (so d = const on the cell; the
    constant is then checked to be 0)"""
    eqrows = [(f, lo) for f, lo, hi in L.rows if lo == hi and L.s not in f]
    cols = []
    for f, lo in eqrows:
        col = {('a', j): to_fr(v) for j, v in f.items() if v != 0}
        col[('c',)] = to_fr(lo)
        cols.append(col)
    rhs = {('a', j): to_fr(v) for j, v in d.items() if v != 0}
    rhs[('c',)] = Fr(0)
    return solve_exact(cols, rhs) is not None


cnt = Counter()
for key in sorted(V.TARGET):
    c, i = key
    C = K.RCell(V.recs[key], c, i)
    L = CellLP(C, K.RDiag(V.CLS[c]))
    for nm, eq in zip(V.cores[key]['names'], V.cores[key]['core_sym']):
        t = eval(nm)
        if t[0] == 'S':
            terms = V.S_terms(L, t[1], t[2]); S = V.engine_terms_S(eq, t[2])
        elif t[0] == 'T':
            terms = V.T_terms(L, t[1]); S = V.engine_terms_T(eq, C)
        else:
            continue
        s0 = sorted(S)[0]
        for x in S:
            if x == s0:
                continue
            d = L.lin((1, terms[x]), (-1, terms[s0]))
            if all(abs(v) < 1e-12 for v in d.values()):
                cnt['eq identical'] += 1
            elif in_equality_span(L, d):
                cnt['eq span'] += 1
            else:
                cnt['eq FAIL'] += 1
                print('eq fail', key, nm, x, s0)
        for x, f in terms.items():
            if x in S:
                continue
            ok, info = certify_positive(L, L.lin((1, f), (-1, terms[s0])))
            cnt['gt ok' if ok else 'gt FAIL'] += 1
            if not ok:
                print('gt fail', key, nm, x, info)
print(dict(cnt))
