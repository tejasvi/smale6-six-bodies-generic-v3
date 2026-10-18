#!/usr/bin/env python3
"""Referee's own cell polyhedra (Definition 4.3 of the paper; engine conventions) and LP checks of the conclusions of
Lemmas T, P, C, B on the cells where the referee's checkers found witnesses.

Variables: the heights of the internal nodes of both trees and a common slack s (strict f > 0 is written f - s >= 0).
Rows: root >= -2; h(child) - h(parent) - s >= 0; for each pair zeta + 3 omega = 4 (z-stroke) or + s <= 4, and
3 zeta + omega = 4 (w-stroke) or + s <= 4; circled body: a_k = -2, else a_k - s >= -2 (a body at O must not be
circled); for each base identity: the terms of the argmin set have equal exponents, the others are larger by >= s.
Usage: ref_lp.py REF_COVER.jsonl OUT.jsonl [NPROC]"""
import json, os, sys, itertools
from multiprocessing import Pool
import numpy as np
import highspy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refkit as K
from refkit import O, BODIES

INF = highspy.kHighsInf


class CellLP:
    def __init__(self, C, D):
        self.C, self.D = C, D
        self.var = {}
        for col, tr in (('z', C.zt), ('w', C.wt)):
            for n in tr.internal:
                self.var[(col, n)] = len(self.var)
        self.s = len(self.var)
        self.nv = self.s + 1
        self.rows = []
        self._build()

    # exponent forms: dict var-index -> coef, plus constant
    def h(self, col, n):
        return {self.var[(col, n)]: 1.0}

    def zeta(self, k, l):
        return self.h('z', self.C.zt.meet(k, l))

    def omega(self, k, l):
        return self.h('w', self.C.wt.meet(k, l))

    @staticmethod
    def lin(*parts):
        out = {}
        for c, f in parts:
            for k, v in f.items():
                out[k] = out.get(k, 0.0) + c * v
        return out

    def pos(self, col, k):
        tr = self.C.tree(col)
        if tr.at_origin(k):
            return None
        return self.h(col, tr.meet(k, O))

    def force(self, col, k, l):   # exponent of delta^3 z_kl (col z) or delta^3 w_kl (col w)
        if col == 'z':
            return self.lin((-0.5, self.zeta(k, l)), (-1.5, self.omega(k, l)))
        return self.lin((-1.5, self.zeta(k, l)), (-0.5, self.omega(k, l)))

    def xkl(self, k, l):
        return self.lin((0.5, self.zeta(k, l)), (0.5, self.omega(k, l)))

    def add(self, f, lo, hi, strict_lo=False, strict_hi=False):
        f = dict(f)
        if strict_lo:
            f[self.s] = f.get(self.s, 0.0) - 1.0
        if strict_hi:
            f[self.s] = f.get(self.s, 0.0) + 1.0
        self.rows.append((f, lo, hi))

    def terms(self, ident):
        """terms (label -> exponent form, constant) of a base identity"""
        out = {}
        if ident[0] in ('z', 'w'):
            col, k = ident
            p = self.pos(col, k)
            if p is not None:
                out[('pos', k)] = (p, 0.0)
            for l in BODIES:
                if l != k:
                    out[('cross', k, l)] = (self.force(col, k, l), 0.0)
        elif ident == 'U':
            out[('E',)] = ({}, 0.0)
            for k, l in itertools.combinations(BODIES, 2):
                out[('delta', k, l)] = (self.lin((-1.0, self.xkl(k, l))), 0.0)
        elif ident == 'I':
            out[('E',)] = ({}, 0.0)
            for k, l in itertools.combinations(BODIES, 2):
                out[('zw', k, l)] = (self.lin((2.0, self.xkl(k, l))), 0.0)
        return out

    def _build(self):
        C, D = self.C, self.D
        for col, tr in (('z', C.zt), ('w', C.wt)):
            self.add(self.h(col, tr.root), -2.0, INF)
            for v in tr.internal:
                for c in tr.ch[v]:
                    if c in tr.ch:
                        self.add(self.lin((1, self.h(col, c)), (-1, self.h(col, v))), 0.0, INF, strict_lo=True)
        for k, l in itertools.combinations(BODIES, 2):
            f1 = self.lin((1, self.zeta(k, l)), (3, self.omega(k, l)))
            f2 = self.lin((3, self.zeta(k, l)), (1, self.omega(k, l)))
            if (k, l) in D.z:
                self.add(f1, 4.0, 4.0)
            else:
                self.add(f1, -INF, 4.0, strict_hi=True)
            if (k, l) in D.w:
                self.add(f2, 4.0, 4.0)
            else:
                self.add(f2, -INF, 4.0, strict_hi=True)
        for col in 'zw':
            circ = D.circles(col)
            for k in BODIES:
                p = self.pos(col, k)
                if p is None:
                    assert k not in circ
                    continue
                if k in circ:
                    self.add(p, -2.0, -2.0)
                else:
                    self.add(p, -2.0, INF, strict_lo=True)
        for ident, S in C.A.items():
            T = self.terms(ident)
            assert set(S) <= set(T), (ident, S)
            S = sorted(S)
            f0, c0 = T[S[0]]
            for lab, (f, c) in T.items():
                if lab == S[0]:
                    continue
                d = self.lin((1, f), (-1, f0))
                if lab in S:
                    self.add(d, c0 - c, c0 - c)
                else:
                    self.add(d, c0 - c, INF, strict_lo=True)
        self.add({self.s: 1.0}, -INF, 1.0)

    def check_point(self, tol=1e-5):
        """the stored interior point (heights hz, hw) satisfies every row with s = min slack; returns that s."""
        x = np.zeros(self.nv)
        for (col, n), i in self.var.items():
            x[i] = (self.C.hz if col == 'z' else self.C.hw)[n]
        # largest s for which all rows hold
        smax = 1.0
        for f, lo, hi in self.rows:
            cs = f.get(self.s, 0.0)
            val = sum(v * x[k] for k, v in f.items() if k != self.s)
            if cs == 0.0:
                if lo > -INF and val < lo - tol:
                    return -1.0
                if hi < INF and val > hi + tol:
                    return -1.0
            elif cs < 0:     # val - s >= lo  ->  s <= val - lo
                smax = min(smax, val - lo)
            else:            # val + s <= hi  ->  s <= hi - val
                smax = min(smax, hi - val)
        return smax

    def maxs(self, extra=()):
        h = highspy.Highs()
        h.setOptionValue('output_flag', False)
        nv = self.nv
        lower = np.full(nv, -INF)
        upper = np.full(nv, INF)
        cost = np.zeros(nv)
        cost[self.s] = 1.0
        h.addVars(nv, lower, upper)
        h.changeColsCost(nv, np.arange(nv, dtype=np.int32), cost)
        h.changeObjectiveSense(highspy.ObjSense.kMaximize)
        for f, lo, hi in list(self.rows) + list(extra):
            idx = np.array(list(f.keys()), dtype=np.int32)
            val = np.array(list(f.values()), dtype=np.float64)
            h.addRow(lo, hi, len(idx), idx, val)
        h.run()
        st = h.getModelStatus()
        if st == highspy.HighsModelStatus.kInfeasible:
            return None
        if st != highspy.HighsModelStatus.kOptimal:
            raise RuntimeError(str(st))
        return h.getInfo().objective_function_value


def below_everywhere(L, f_small, f_big):
    """f_big - f_small > 0 on the whole open cell: max s subject to f_big - f_small <= 0 is <= 1e-9 (or infeasible)."""
    d = L.lin((1, f_big), (-1, f_small))
    r = L.maxs([(d, -INF, 0.0)])
    return r is None or r <= 1e-9, r


def equal_everywhere(L, f1, f2):
    """f1 = f2 on the whole open cell: d = f1 - f2 is identically zero, or neither d >= s nor -d >= s is possible
    with s > 0."""
    d = L.lin((1, f1), (-1, f2))
    if all(abs(v) < 1e-12 for v in d.values()):
        return True
    dp = dict(d); dp[L.s] = dp.get(L.s, 0.0) - 1.0
    dm = {k: -v for k, v in d.items()}; dm[L.s] = dm.get(L.s, 0.0) - 1.0
    r1 = L.maxs([(dp, 0.0, INF)])
    r2 = L.maxs([(dm, 0.0, INF)])
    return (r1 is None or r1 <= 1e-9) and (r2 is None or r2 <= 1e-9)


CLS = K.classes()


def check_cell(args):
    c, i, rec, mine = args
    C = K.RCell(rec, c, i)
    D = K.RDiag(CLS[c])
    L = CellLP(C, D)
    res = {'class': c, 'cell': i}
    res['point_s'] = L.check_point()
    res['maxs'] = L.maxs()
    fails = []
    # T
    if mine['Tlit']:
        J, (p, q) = mine['Tlit'][0]
        Jc = [j for j in BODIES if j not in J]
        def tex(a, b):
            return L.lin((1, L.pos('z', a)), (1, L.pos('w', b)), (-3, L.xkl(a, b)))
        f0 = tex(p, q)
        for k in J:
            for l in Jc:
                for a, b in ((k, l), (l, k)):
                    if (a, b) == (p, q) or L.pos('z', a) is None or L.pos('w', b) is None:
                        continue
                    ok, r = below_everywhere(L, f0, tex(a, b))
                    if not ok:
                        fails.append(('T', J, (p, q), (a, b), r))
        res['T'] = True
    # P
    if mine['P'] is not None:
        for k in BODIES:
            pa, pb = L.pos('z', k), L.pos('w', k)
            if pa is None or pb is None:
                continue
            ok, r = below_everywhere(L, {}, L.lin((1, pa), (1, pb)))
            if not ok:
                fails.append(('P', k, r))
        res['P'] = True
    # C
    if mine['C']:
        col, J, kind, X = mine['C'][0]
        Js = set(J)
        terms = {}
        for k in J:
            p = L.pos(col, k)
            if p is not None:
                terms[('pos', k)] = p
            for j in BODIES:
                if j not in Js:
                    terms[('cross', k, j)] = L.force(col, k, j)
        if kind == 'single':
            Xs = [tuple(X)]
        else:
            Xs = [('pos', k) for k in X]
        x0 = Xs[0]
        for t in Xs[1:]:
            if not equal_everywhere(L, terms[x0], terms[t]):
                fails.append(('C-eq', x0, t))
        for t, f in terms.items():
            if t in Xs:
                continue
            ok, r = below_everywhere(L, terms[x0], f)
            if not ok:
                fails.append(('C', J, col, x0, t, r))
        res['C'] = True
    # B
    if mine['B']:
        col, k, l = mine['B'][0]
        f0 = L.force(col, k, l)
        others = [L.lin((1, L.zeta(k, l))) if col == 'z' else L.lin((1, L.omega(k, l)))]
        for j in BODIES:
            if j not in (k, l):
                others.append(L.force(col, k, j))
                others.append(L.force(col, l, j))
        for f in others:
            ok, r = below_everywhere(L, f0, f)
            if not ok:
                fails.append(('B', col, k, l, r))
        res['B'] = True
    res['fails'] = fails
    return res


def gen(path):
    mine = {}
    for l in open(path):
        r = json.loads(l)
        mine[(r['class'], r['cell'])] = r
    for c, i, rec in K.iter_cells():
        yield (c, i, rec, mine[(c, i)])


def main():
    nproc = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    with Pool(nproc) as pool, open(sys.argv[2], 'w') as f:
        n = 0
        for r in pool.imap_unordered(check_cell, gen(sys.argv[1]), chunksize=64):
            f.write(json.dumps(r) + '\n')
            n += 1
            if n % 10000 == 0:
                print(n, flush=True)


if __name__ == '__main__':
    main()
