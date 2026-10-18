#!/usr/bin/env python3
"""Exact Farkas certificates (Lemma 4.4 of the paper) for 'f > 0 on the whole open cell', on the referee's own cell
polyhedra (ref_lp.CellLP). A float LP proposes multipliers; the support is re-solved exactly over Q and the
conditions of Lemma 4.4 are checked in rational arithmetic."""
import itertools, os, sys
from fractions import Fraction as Fr
import numpy as np
import highspy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ref_lp import CellLP, INF


def to_fr(x):
    return Fr(x).limit_denominator(10 ** 6)


def exact_rows(L, extra):
    """rows as (a: dict var->Fr (without s), c: Fr (coefficient of s), lo, hi) with lo/hi Fr or None"""
    out = []
    for f, lo, hi in list(L.rows[:-1]) + list(extra):      # drop the auxiliary row s <= 1
        a = {k: to_fr(v) for k, v in f.items() if k != L.s and v != 0}
        c = to_fr(f.get(L.s, 0.0))
        out.append((a, c, None if lo == -INF else to_fr(lo), None if hi == INF else to_fr(hi)))
    return out


def solve_exact(cols, rhs):
    """solve sum_j y_j cols[j] = rhs exactly (cols: list of dict row->Fr); returns list or None (inconsistent);
    free variables set to 0."""
    rows = sorted(set(r for col in cols for r in col) | set(rhs))
    n = len(cols)
    M = [[col.get(r, Fr(0)) for col in cols] + [rhs.get(r, Fr(0))] for r in rows]
    piv = []
    ri = 0
    for cj in range(n):
        p = next((i for i in range(ri, len(M)) if M[i][cj] != 0), None)
        if p is None:
            continue
        M[ri], M[p] = M[p], M[ri]
        inv = 1 / M[ri][cj]
        M[ri] = [e * inv for e in M[ri]]
        for i in range(len(M)):
            if i != ri and M[i][cj] != 0:
                fct = M[i][cj]
                M[i] = [a - fct * b for a, b in zip(M[i], M[ri])]
        piv.append(cj)
        ri += 1
    for i in range(ri, len(M)):
        if M[i][n] != 0:
            return None
    y = [Fr(0)] * n
    for i, cj in enumerate(piv):
        y[cj] = M[i][n]
    return y


def _multiplier_lp(R, nvar, mode):
    """mode 'norm': sum y_i a_i = 0, sum y_i c_i = 1, minimise beta;
    mode 'ray': sum y_i a_i = 0, sum y_i c_i = 0, beta = -1 (feasibility). Returns y (floats) or None."""
    m = len(R)
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    lower, upper, cost = [], [], []
    for a, c, lo, hi in R:
        if lo is not None and hi is not None and lo == hi:
            lower.append(-INF); upper.append(INF); cost.append(float(lo))
        elif hi is not None and lo is None:
            lower.append(0.0); upper.append(INF); cost.append(float(hi))
        elif lo is not None and hi is None:
            lower.append(-INF); upper.append(0.0); cost.append(float(lo))
        else:
            raise ValueError('two-sided row')
    h.addVars(m, np.array(lower), np.array(upper))
    if mode == 'norm':
        h.changeColsCost(m, np.arange(m, dtype=np.int32), np.array(cost))
    for j in range(nvar):
        idx = [i for i, (a, c, lo, hi) in enumerate(R) if j in a]
        if idx:
            h.addRow(0.0, 0.0, len(idx), np.array(idx, dtype=np.int32), np.array([float(R[i][0][j]) for i in idx]))
    idx = [i for i, (a, c, lo, hi) in enumerate(R) if c != 0]
    g = 1.0 if mode == 'norm' else 0.0
    h.addRow(g, g, len(idx), np.array(idx, dtype=np.int32), np.array([float(R[i][1]) for i in idx]))
    if mode == 'ray':
        h.addRow(-1.0, -1.0, m, np.arange(m, dtype=np.int32), np.array(cost))
    h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None, str(h.getModelStatus())
    if mode == 'norm' and h.getInfo().objective_function_value > 1e-9:
        return None, 'optimum %g > 0' % h.getInfo().objective_function_value
    return list(h.getSolution().col_value), 'ok'


def certify_positive(L, f):
    """certificate that f > 0 at every point of the open cell (rows of L with s > 0). Returns (ok, info)."""
    extra = [(f, -INF, 0.0)]                                # f <= 0
    R = exact_rows(L, extra)
    m = len(R)
    nvar = L.s
    for mode in ('ray', 'norm'):
        y, msg = _multiplier_lp(R, nvar, mode)
        if y is None:
            continue
        supp = [i for i in range(m) if abs(y[i]) > 1e-9]
        cols = []
        for i in supp:
            a, c, lo, hi = R[i]
            col = {('a', j): v for j, v in a.items()}
            if c != 0:
                col[('c',)] = c
            if mode == 'ray':
                b = lo if (lo is not None and (hi is None or y[i] < 0)) else hi
                col[('b',)] = b
            cols.append(col)
        rhs = {('c',): Fr(1)} if mode == 'norm' else {('b',): Fr(-1)}
        ye = solve_exact(cols, rhs)
        if ye is None:
            continue
        beta, g, bad = Fr(0), Fr(0), False
        for yi, i in zip(ye, supp):
            a, c, lo, hi = R[i]
            if yi > 0:
                if hi is None:
                    bad = True
                    break
                beta += yi * hi
            elif yi < 0:
                if lo is None:
                    bad = True
                    break
                beta += yi * lo
            g += yi * c
        if bad:
            continue
        tot = {}
        for yi, i in zip(ye, supp):
            for j, v in R[i][0].items():
                tot[j] = tot.get(j, Fr(0)) + yi * v
        if any(v != 0 for v in tot.values()):
            continue
        gm = max(Fr(0), -g)
        if beta + gm <= 0 and (g + gm > 0 or beta + gm < 0):
            return True, {'mode': mode, 'support': len(supp), 'beta': str(beta), 'g': str(g)}
    return False, 'no certificate found'
