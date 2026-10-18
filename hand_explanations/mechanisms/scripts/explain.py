#!/usr/bin/env python3
"""Labelled LP of a cell (same semantics as tengine.base_lp + texact.forced_rows) and explanations of strict
inequalities between exponent forms: the support of an LP dual certificate, as a list of labelled constraints.
Floating point; for finding the hand arguments only."""
import itertools, json, sys, os
import numpy as np
import highspy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import Cell, Diag, O, N

INF = float('inf')


class LLP:
    def __init__(self, C):
        self.C = C
        self.var = {}
        for col, T in (('z', C.zt), ('w', C.wt)):
            for v in T.children:
                self.var[(col, v)] = len(self.var)
        self.s = len(self.var)
        self.nv = self.s + 1
        self.rows = []      # (coefs, lo, hi, label)

    def add(self, coefs, lo, hi, label):
        self.rows.append((coefs, lo, hi, label))

    def h(self, col, node):
        return {self.var[(col, node)]: 1.0}


def lin(*pairs):
    d = {}
    for f, c in pairs:
        for j, x in f.items():
            d[j] = d.get(j, 0.0) + c * x
    return {j: x for j, x in d.items() if x != 0}


def exp_forms(L, rec):
    """Exponent forms of all terms of the base identities, keyed like texact labels: returns dict name -> list of
    (label, form)."""
    C = L.C
    zt, wt = C.zt, C.wt
    out = {}
    zeta = lambda k, l: L.h('z', zt.meet(k, l))
    omega = lambda k, l: L.h('w', wt.meet(k, l))
    for col in 'zw':
        T = zt if col == 'z' else wt
        for i in range(N):
            terms = []
            m = T.meet(i, O)
            if m is not None:
                terms.append((('pos', i), L.h(col, m)))
            for j in range(N):
                if j == i:
                    continue
                if col == 'z':
                    f = lin((zeta(i, j), -0.5), (omega(i, j), -1.5))
                else:
                    f = lin((zeta(i, j), -1.5), (omega(i, j), -0.5))
                terms.append((('cross', i, j), f))
            out[(col, 'S', (i,))] = terms
    pairs = list(itertools.combinations(range(N), 2))
    out[('U',)] = [(('E',), {})] + [(('delta', k, l), lin((zeta(k, l), -0.5), (omega(k, l), -0.5))) for k, l in pairs]
    out[('I',)] = [(('E',), {})] + [(('zw', k, l), lin((zeta(k, l), 1.0), (omega(k, l), 1.0))) for k, l in pairs]
    ip = [(('E',), {})]
    for k in range(N):
        u, v = zt.meet(k, O), wt.meet(k, O)
        if u is not None and v is not None:
            ip.append((('zkwk', k), lin((L.h('z', u), 1.0), (L.h('w', v), 1.0))))
    out[('Ip',)] = ip
    return out


def build(rec, D, with_argmin=True):
    C = Cell(rec)
    L = LLP(C)
    s = L.s
    for col, T in (('z', C.zt), ('w', C.wt)):
        L.add(L.h(col, T.root), -2.0, None, ('root>=-2', col))
        for v, ch in T.children.items():
            for c in ch:
                if c in T.children:
                    L.add(lin((L.h(col, c), 1.0), (L.h(col, v), -1.0), ({s: 1.0}, -1.0)), 0.0, None, ('edge', col, v, c))
    for k, l in itertools.combinations(range(N), 2):
        Z = L.h('z', C.zt.meet(k, l))
        W = L.h('w', C.wt.meet(k, l))
        if D.zstroke(k, l):
            L.add(lin((Z, 1.0), (W, 3.0)), 4.0, 4.0, ('zstroke', k, l))
        else:
            L.add(lin((Z, 1.0), (W, 3.0), ({s: 1.0}, 1.0)), None, 4.0, ('O1:z+3w<4', k, l))
        if D.wstroke(k, l):
            L.add(lin((Z, 3.0), (W, 1.0)), 4.0, 4.0, ('wstroke', k, l))
        else:
            L.add(lin((Z, 3.0), (W, 1.0), ({s: 1.0}, 1.0)), None, 4.0, ('O1:3z+w<4', k, l))
    for k in range(N):
        for col, T, circ in (('z', C.zt, D.zc), ('w', C.wt, D.wc)):
            m = T.meet(k, O)
            if m is None:
                continue
            if k in circ:
                L.add(L.h(col, m), -2.0, -2.0, ('circle', col, k))
            else:
                L.add(lin((L.h(col, m), 1.0), ({s: 1.0}, -1.0)), -2.0, None, ('nocircle', col, k))
    if with_argmin:
        forms = exp_forms(L, rec)
        for nm, labs in rec['argmin']:
            key = (nm[0], nm[1], tuple(nm[2])) if nm[0] in ('z', 'w') else tuple(nm)
            terms = forms[key]
            labset = [tuple(x) for x in labs]
            idx = [i for i, (lab, f) in enumerate(terms) if lab in labset]
            f0 = idx[0]
            for t, (lab, f) in enumerate(terms):
                if t == f0:
                    continue
                d = lin((f, 1.0), (terms[f0][1], -1.0))
                if t in idx:
                    L.add(d, 0.0, 0.0, ('argmin=', key, lab, terms[f0][0]))
                else:
                    L.add(lin((d, 1.0), ({s: 1.0}, -1.0)), 0.0, None, ('argmin>', key, lab, terms[f0][0]))
    return L


def solve(L, extra=()):
    rows = L.rows + list(extra)
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('threads', 1)
    lp = highspy.HighsLp()
    lp.num_col_ = L.nv
    lp.num_row_ = len(rows)
    cost = np.zeros(L.nv)
    cost[L.s] = 1.0
    lp.col_cost_ = cost
    lo = np.full(L.nv, -highspy.kHighsInf)
    hi = np.full(L.nv, highspy.kHighsInf)
    lo[L.s] = 0.0
    hi[L.s] = 1.0
    lp.col_lower_ = lo
    lp.col_upper_ = hi
    lp.sense_ = highspy.ObjSense.kMaximize
    starts, idx, vals, rlo, rhi = [0], [], [], [], []
    for coefs, a, b, lab in rows:
        for j, c in coefs.items():
            idx.append(j)
            vals.append(float(c))
        starts.append(len(idx))
        rlo.append(-highspy.kHighsInf if a is None else float(a))
        rhi.append(highspy.kHighsInf if b is None else float(b))
    lp.row_lower_ = np.array(rlo)
    lp.row_upper_ = np.array(rhi)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_ = np.array(starts, dtype=np.int32)
    lp.a_matrix_.index_ = np.array(idx, dtype=np.int32)
    lp.a_matrix_.value_ = np.array(vals)
    lp.a_matrix_.num_col_ = L.nv
    lp.a_matrix_.num_row_ = len(rows)
    h.passModel(lp)
    h.run()
    st = h.getModelStatus()
    if st == highspy.HighsModelStatus.kOptimal:
        val = h.getInfo().objective_function_value
        duals = np.array(h.getSolution().row_dual)
        return val, duals, rows
    if st == highspy.HighsModelStatus.kInfeasible:
        _, has, ray = h.getDualRay()
        if not has:
            h.setOptionValue("presolve", "off")
            h.run()
            if h.getModelStatus() == highspy.HighsModelStatus.kInfeasible:
                _, has, ray = h.getDualRay()
        if has:
            return -1.0, np.array(ray), rows
    return None, None, rows


def explain(L, f_small, f_big):
    """Is f_small < f_big on the open polyhedron? Returns (True, support labels with dual weights) or (False, None)."""
    d = lin((f_big, 1.0), (f_small, -1.0))
    extra = [(d, None, 0.0, ('claim-negation',))]
    val, duals, rows = solve(L, extra)
    if val is None:
        return None, None
    if val > 1e-9:
        return False, None
    sup = [(round(float(duals[i]), 6), rows[i][3]) for i in range(len(rows)) if abs(duals[i]) > 1e-9]
    return True, sup
