#!/usr/bin/env python3
"""Krawczyk certification (Arb ball arithmetic, python-flint) of solutions of the stretched four-body system S11 of
diagram 88, and the interval T-test.

S11: unknowns v = (X2, X3, Y1, Y2, Y3, p12, p13, p14, p23, p24, p34); X1 = X2 + 1; X4 = -(m1 X1 + m2 X2 + m3 X3)/m4,
Y4 = -(m1 Y1 + m2 Y2 + m3 Y3)/m4; equations: X-equations of bodies 1, 2, 3, Y-equations of bodies 1, 2, the six
distance equations  p_kl^2 (X_k - X_l)(Y_k - Y_l) = 1  (the Y-equation of body 3 follows from the torque identity
since X_34 != 0).  Masses are exact integers.

Krawczyk: for a box B around a point c and any matrix Y, if K(B) = c - Y F(c) + (I - Y J(B))(B - c) lies in the
interior of B, then B contains exactly one zero of F, and J is invertible on B.

T-test (DERIVATION.md, Lemma 4): with beta_l = m_l |X_l|^(-1/2), some k has beta_k > sum_{l != k} beta_l.
Checked with rigorous lower/upper bounds from the certified box.

Usage: k4_krawczyk.py SOLS.txt m1 m2 m3 m4 OUT.jsonl NPROC [PREC]   (SOLS.txt: see arrayio.py)
Output: one JSON line per solution: midpoint (decimal strings), radius, Krawczyk verdict, T-test verdict and margin.
"""
import json
import os
import sys
from multiprocessing import Pool

import numpy as np
from flint import acb, arb, acb_mat, ctx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arrayio

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
PIDX = {pr: 5 + i for i, pr in enumerate(PAIRS)}


def pidx(k, l):
    return PIDX[(min(k, l), max(k, l))]


class Sys:
    def __init__(self, mi):
        self.mi = [int(x) for x in mi]
        self.m = [acb(x) for x in self.mi]
        m1, m2, m3, m4 = self.mi
        from fractions import Fraction as Fr
        # affine maps X = AX v + bX, Y = AY v + bY with rational coefficients
        AX = [[Fr(0)] * 11 for _ in range(4)]
        AY = [[Fr(0)] * 11 for _ in range(4)]
        bX = [Fr(0)] * 4
        AX[0][0] = Fr(1); bX[0] = Fr(1)
        AX[1][0] = Fr(1)
        AX[2][1] = Fr(1)
        for j in range(11):
            AX[3][j] = -(m1 * AX[0][j] + m2 * AX[1][j] + m3 * AX[2][j]) / m4
        bX[3] = Fr(-m1, m4)
        AY[0][2] = Fr(1); AY[1][3] = Fr(1); AY[2][4] = Fr(1)
        for j in range(11):
            AY[3][j] = -(m1 * AY[0][j] + m2 * AY[1][j] + m3 * AY[2][j]) / m4
        self.AX = [[acb(arb(c.numerator) / c.denominator) for c in row] for row in AX]
        self.AY = [[acb(arb(c.numerator) / c.denominator) for c in row] for row in AY]
        self.bX = [acb(arb(c.numerator) / c.denominator) for c in bX]
        self.AXq, self.AYq, self.bXq = AX, AY, bX

    def pos(self, v):
        X = []
        Y = []
        for k in range(4):
            sx = self.bX[k]
            sy = acb(0)
            for j in range(5):
                if self.AXq[k][j] != 0:
                    sx += self.AX[k][j] * v[j]
                if self.AYq[k][j] != 0:
                    sy += self.AY[k][j] * v[j]
            X.append(sx)
            Y.append(sy)
        return X, Y

    def F(self, v, full=False):
        X, Y = self.pos(v)
        m = self.m
        out = []

        def ceq(Z, k):
            s = Z[k]
            for l in range(4):
                if l != k:
                    p = v[pidx(k, l)]
                    s = s - m[l] * (p * p * p) * (Z[k] - Z[l])
            return s
        for k in range(3):
            out.append(ceq(X, k))
        for k in range(2):
            out.append(ceq(Y, k))
        for (a, b) in PAIRS:
            p = v[pidx(a, b)]
            out.append(p * p * (X[a] - X[b]) * (Y[a] - Y[b]) - 1)
        if full:
            out.append(ceq(Y, 2))
        return out

    def J(self, v):
        X, Y = self.pos(v)
        m = self.m
        rows = []
        for (Z, A, ks) in ((X, self.AX, range(3)), (Y, self.AY, range(2))):
            for k in ks:
                g = [A[k][j] for j in range(11)]
                for l in range(4):
                    if l != k:
                        j0 = pidx(k, l)
                        p = v[j0]
                        p2 = p * p
                        p3 = p2 * p
                        d = Z[k] - Z[l]
                        for j in range(11):
                            c = A[k][j] - A[l][j]
                            if c != 0:
                                g[j] = g[j] - m[l] * p3 * c
                        g[j0] = g[j0] - m[l] * 3 * p2 * d
                rows.append(g)
        for (a, b) in PAIRS:
            j0 = pidx(a, b)
            p = v[j0]
            dx = X[a] - X[b]
            dy = Y[a] - Y[b]
            p2 = p * p
            g = [acb(0)] * 11
            for j in range(11):
                cx = self.AX[a][j] - self.AX[b][j]
                cy = self.AY[a][j] - self.AY[b][j]
                g[j] = p2 * (dy * cx + dx * cy)
            g[j0] = g[j0] + 2 * p * dx * dy
            rows.append(g)
        return acb_mat(rows)


def _mid(z):
    return acb(z.real.mid(), z.imag.mid())


def certify_one(args):
    v0, mi, prec = args
    ctx.prec = prec
    S = Sys(mi)
    v = [acb(complex(z).real, complex(z).imag) for z in v0]
    # Newton refinement (midpoints only)
    for _ in range(8):
        f = S.F(v)
        Jm = S.J(v)
        try:
            dv = Jm.solve(acb_mat([[x] for x in f]))
        except Exception:
            return {'ok': False, 'why': 'singular in Newton'}
        v = [_mid(v[i] - dv[i, 0]) for i in range(11)]
    # the certificate's centre: decimal strings with DIG significant digits, read back as Arb balls
    DIG = 60
    cstr = [[z.real.mid().str(DIG, radius=False), z.imag.mid().str(DIG, radius=False)] for z in v]
    v = [acb(arb(a), arb(b)) for a, b in cstr]
    Jm = S.J(v)
    try:
        Yi = Jm.inv()
    except Exception:
        return {'ok': False, 'why': 'singular J'}
    Y = acb_mat([[_mid(Yi[i, j]) for j in range(11)] for i in range(11)])
    f = S.F(v)
    yf = Y * acb_mat([[x] for x in f])
    nyf = max(float(abs(yf[i, 0]).upper()) for i in range(11))
    vmax = max(float(abs(z).upper()) for z in v)
    r = max(nyf * 1e4, 1e-50 * (1 + vmax))
    I11 = acb_mat([[acb(1) if i == j else acb(0) for j in range(11)] for i in range(11)])
    ok = False
    for attempt in range(8):
        rr = arb(0, r)
        B = [acb(z.real + rr, z.imag + rr) for z in v]
        JB = S.J(B)
        Dm = acb_mat([[B[i] - v[i]] for i in range(11)])
        K = acb_mat([[v[i] - yf[i, 0]] for i in range(11)]) + (I11 - Y * JB) * Dm
        ok = all(B[i].contains_interior(K[i, 0]) for i in range(11))
        if ok:
            break
        r *= 100
    if not ok:
        return {'ok': False, 'why': 'krawczyk failed', 'r': r}
    # quantities on the certified box B
    X, Yp = S.pos(B)
    Ffull = S.F(B, full=True)
    x34 = X[2] - X[3]
    res = {'ok': True, 'r': r, 'mid': cstr,
           'x34_nonzero': not x34.contains(0)}
    # T-test: beta_l = m_l |X_l|^(-1/2)
    lo, hi = [], []
    for l in range(4):
        ab = abs(X[l])          # arb ball for |X_l|
        up = ab.upper()
        lw = ab.lower()
        bl = arb(mi[l]) / up.sqrt() if up > 0 else None          # lower bound of beta_l
        bu = (arb(mi[l]) / lw.sqrt()) if lw > 0 else None         # upper bound (None = unbounded)
        lo.append(bl)
        hi.append(bu)
    best = None
    passk = None
    for k in range(4):
        if lo[k] is None or any(hi[l] is None for l in range(4) if l != k):
            continue
        s = sum((hi[l] for l in range(4) if l != k), arb(0))
        marg = lo[k] - s
        if marg > 0:
            passk = k
            rel = (marg / (lo[k] + s))
            best = float(rel.lower())
            break
    res['T_pass_body'] = passk
    res['T_margin_rel_lower'] = best
    res['X_abs_lower'] = [float(abs(X[l]).lower()) for l in range(4)]
    return res


def main():
    sols = arrayio.load_array(sys.argv[1])
    mi = [int(x) for x in sys.argv[2:6]]
    out = sys.argv[6]
    nproc = int(sys.argv[7])
    prec = int(sys.argv[8]) if len(sys.argv) > 8 else 256
    args = [(list(s), mi, prec) for s in sols]
    with Pool(nproc) as pool:
        res = pool.map(certify_one, args, chunksize=16)
    with open(out, 'w') as fo:
        for i, r in enumerate(res):
            r['index'] = i
            fo.write(json.dumps(r) + '\n')
    nok = sum(1 for r in res if r['ok'])
    ntt = sum(1 for r in res if r.get('T_pass_body') is not None)
    print(json.dumps({'n': len(res), 'krawczyk_ok': nok, 'T_pass': ntt,
                      'min_T_margin': min((r['T_margin_rel_lower'] for r in res if r.get('T_margin_rel_lower') is not None), default=None)}))


if __name__ == '__main__':
    main()
