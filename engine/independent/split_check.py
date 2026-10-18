#!/usr/bin/env python3
"""Referee check of the --split 3 partition of treplay: the part of a depth-3 node is (running counter) mod 384, where
the counter runs over the option pairs met below the depth-2 nodes that the DFS keeps. All parts must therefore make
the same verdicts at depths 1 and 2. Pruned verdicts there are certified in every part (no failure anywhere); this
script certifies the KEPT verdicts at depths 1 and 2 exactly: a rational point (heights, s) with s > 0 satisfying every
row, obtained by rounding the HiGHS solution (limit_denominator) and checked in Fractions. It also reports the counter
value (number of depth-3 option pairs), the same in every part.
Usage: split_check.py CODE_DIR [CLASS ...]  (default: all 191 classes)"""
import json, sys
from fractions import Fraction
sys.path.insert(0, sys.argv[1])
import numpy as np
import tengine as T
import tsign
import treplay as R

n = 6
cls = json.load(open(sys.argv[1] + '/n6.json'))['classes']
which = [int(a) for a in sys.argv[2:]] or range(len(cls))


def exact_point(L):
    h = R.highs(L)
    if h.getModelStatus() != R.OPT:
        return None
    x = np.asarray(h.getSolution().col_value, dtype=float)
    for Dn in (10 ** 3, 10 ** 6, 10 ** 9):
        p = [Fraction(v).limit_denominator(Dn) for v in x]
        p[L.ns] = min(p[L.ns], Fraction(1))
        # shrink s a little to absorb rounding, keep s > 0
        p[L.ns] = p[L.ns] / 2
        if p[L.ns] <= 0:
            continue
        ok = True
        for coefs, lo, hi in L.rows:
            v = sum(Fraction(c) * p[j] for j, c in coefs.items())
            if lo is not None and v < Fraction(lo):
                ok = False
                break
            if hi is not None and v > Fraction(hi):
                ok = False
                break
        if ok:
            return p
    return None


tot = {'kept': 0, 'kept_exact': 0, 'pruned': 0, 'classes': 0}
bad = []
for ci in which:
    D = T.Diagram.from_json(n, cls[ci])
    zt0 = T.Tree(n).options(n)[0]
    wt0 = T.Tree(n).options(n)[0]
    order = T.order_bodies(D)
    counter = 0
    kept = kexact = pruned = 0

    def rec(i, zt, wt, pts):
        global counter, kept, kexact, pruned
        if i == 2:                       # depth-3 option pairs: count them as treplay's counter does
            p = order[i]
            counter += len(zt.options(p)) * len(wt.options(p))
            return
        p = order[i]
        npts = pts + [p]
        for zt2 in zt.options(p):
            for wt2 in wt.options(p):
                L = T.base_lp(D, zt2, wt2, npts)
                if L is None:
                    continue
                L.rows.append(tsign.threshold_row(D, zt2, wt2, L, npts, 'le'))
                if T.feasible(L)[0]:
                    kept += 1
                    if exact_point(L) is not None:
                        kexact += 1
                    else:
                        bad.append((ci, i + 1))
                    rec(i + 1, zt2, wt2, npts)
                else:
                    pruned += 1

    rec(0, zt0, wt0, [n])
    tot['kept'] += kept
    tot['kept_exact'] += kexact
    tot['pruned'] += pruned
    tot['classes'] += 1
    print(json.dumps({'class': ci, 'depth12_kept': kept, 'kept_exactly_feasible': kexact, 'depth12_pruned': pruned,
                      'depth3_counter': counter}), flush=True)
print('TOTAL', json.dumps(tot), 'unverified kept:', bad[:10])
