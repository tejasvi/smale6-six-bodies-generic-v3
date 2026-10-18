#!/usr/bin/env python3
"""Read-only use of the engine's LP builders (no bytecode is written into the engine directory).

base(D, zt, wt): trees + (O1) + (O2) + circles (+ bodies at O), as tengine.base_lp.
cell(D, zt, wt, argmin): base + the exact argmin sets of the cell's identities, as tsec.cell_lp.
strictly_least(L, forms, i): True if form i is strictly less than every other form on the open polyhedron L
(floating point LPs; for classification only)."""
import os, sys
sys.dont_write_bytecode = True
ENG = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'engine')
if ENG not in sys.path:
    sys.path.insert(0, ENG)
_cwd = os.getcwd()
os.chdir(ENG)            # tsec/texact insert '.' into sys.path at import time
import tengine as T
import texact as X
import tsec as S
os.chdir(_cwd)


def diagram(c):
    return T.Diagram.from_json(6, c)


def trees(rec):
    return S.tree_from_json(6, rec['ztree']), S.tree_from_json(6, rec['wtree'])


def base(D, zt, wt):
    return T.base_lp(D, zt, wt, list(range(7)))


def cell(D, zt, wt, argmin):
    return S.cell_lp(D, zt, wt, argmin)


def strictly_least(L, forms, i):
    """forms: list of dicts var -> coef (exponent linear forms in the LP variables)."""
    for j, f in enumerate(forms):
        if j == i:
            continue
        d = S.add(f, S.scale(forms[i], -1.0))     # f_j - f_i
        if T.feasible(X.sub(L, [(d, None, 0.0)]))[0]:
            return False
    return True
