#!/usr/bin/env python3
"""Independent checker for the Krawczyk certificates of k4_krawczyk.py (diagram 88, stretched four-body system).

Shares no code with k4_krawczyk.py: interval arithmetic is mpmath.iv (outward rounding; complex boxes as pairs of
real intervals), and the Jacobian enclosure comes from forward-mode automatic differentiation of the equations
(written out again below), not from hand-coded derivatives.  Only the certificate data are read: the midpoint c
(decimal strings) and the radius r of each box B = c + [-r, r] + i[-r, r] (componentwise, 11 unknowns).

Checks, for every certificate:
 (K) Krawczyk: K(B) = c - Y F(c) + (I - Y J(B))(B - c) lies in the interior of B (Y: any matrix; here a floating
     inverse of J(c)); hence B contains exactly one zero of S11 and J is invertible on B;
 (D) X_34 = X_3 - X_4 does not vanish on B (so the omitted Y-equation of body 3 holds at that zero);
 (T) T-test: some k has m_k |X_k|^(-1/2) > sum_{l != k} m_l |X_l|^(-1/2) on B;
and globally
 (S) the boxes are pairwise disjoint (so they contain distinct zeros).
Usage: k4_check_iv.py CERT.jsonl m1 m2 m3 m4 NPROC [PREC]
"""
import json
import sys
from multiprocessing import Pool

import mpmath
from mpmath import iv, mp

PREC = 256


# ---------------- complex intervals ----------------
class CI:
    __slots__ = ('re', 'im')

    def __init__(self, re, im=None):
        self.re = re if isinstance(re, iv.mpf) else iv.mpf(re)
        self.im = (im if isinstance(im, iv.mpf) else iv.mpf(im)) if im is not None else iv.mpf(0)

    def __add__(self, o):
        o = _c(o)
        return CI(self.re + o.re, self.im + o.im)
    __radd__ = __add__

    def __sub__(self, o):
        o = _c(o)
        return CI(self.re - o.re, self.im - o.im)

    def __rsub__(self, o):
        return _c(o) - self

    def __neg__(self):
        return CI(-self.re, -self.im)

    def __mul__(self, o):
        o = _c(o)
        return CI(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    __rmul__ = __mul__

    def abs2(self):
        return self.re * self.re + self.im * self.im   # interval enclosing |z|^2 (may be loose but valid)


def _c(x):
    if isinstance(x, CI):
        return x
    return CI(iv.mpf(x), iv.mpf(0))


# ---------------- forward-mode AD over CI ----------------
class AD:
    __slots__ = ('v', 'g')

    def __init__(self, v, g):
        self.v, self.g = v, g

    def __add__(self, o):
        if isinstance(o, AD):
            return AD(self.v + o.v, [a + b for a, b in zip(self.g, o.g)])
        return AD(self.v + o, self.g)
    __radd__ = __add__

    def __sub__(self, o):
        if isinstance(o, AD):
            return AD(self.v - o.v, [a - b for a, b in zip(self.g, o.g)])
        return AD(self.v - o, self.g)

    def __rsub__(self, o):
        return AD(_c(o) - self.v, [-a for a in self.g])

    def __mul__(self, o):
        if isinstance(o, AD):
            return AD(self.v * o.v, [self.v * b + o.v * a for a, b in zip(self.g, o.g)])
        o = _c(o)
        return AD(self.v * o, [a * o for a in self.g])
    __rmul__ = __mul__


def equations(v, m):
    """v: 11 quantities (CI or AD) = X2, X3, Y1, Y2, Y3, p12, p13, p14, p23, p24, p34; m: 4 integers.
    Returns (S11 list, X positions, Y positions)."""
    X2, X3, Y1, Y2, Y3 = v[0:5]
    p = {(1, 2): v[5], (1, 3): v[6], (1, 4): v[7], (2, 3): v[8], (2, 4): v[9], (3, 4): v[10]}
    m1, m2, m3, m4 = m
    q = iv.mpf(1) / m4
    X1 = X2 + 1
    X4 = (X1 * (-m1) + X2 * (-m2) + X3 * (-m3)) * CI(q)
    Y4 = (Y1 * (-m1) + Y2 * (-m2) + Y3 * (-m3)) * CI(q)
    X = {1: X1, 2: X2, 3: X3, 4: X4}
    Y = {1: Y1, 2: Y2, 3: Y3, 4: Y4}
    mm = {1: m1, 2: m2, 3: m3, 4: m4}

    def P(k, l):
        return p[(min(k, l), max(k, l))]

    eqs = []
    for k in (1, 2, 3):        # X-equations of bodies 1, 2, 3
        s = X[k]
        for l in (1, 2, 3, 4):
            if l != k:
                pk = P(k, l)
                s = s - (pk * pk * pk) * (X[k] - X[l]) * mm[l]
        eqs.append(s)
    for k in (1, 2):           # Y-equations of bodies 1, 2
        s = Y[k]
        for l in (1, 2, 3, 4):
            if l != k:
                pk = P(k, l)
                s = s - (pk * pk * pk) * (Y[k] - Y[l]) * mm[l]
        eqs.append(s)
    for (k, l) in [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]:
        pk = P(k, l)
        eqs.append(pk * pk * (X[k] - X[l]) * (Y[k] - Y[l]) - 1)
    return eqs, X, Y


def check_one(args):
    cert, m, prec = args
    iv.prec = prec
    mp.prec = prec
    if not cert.get('ok'):
        return {'index': cert['index'], 'K': False, 'why': 'no certificate'}
    r = iv.mpf(cert['r'])
    cmid = [CI(iv.mpf(a), iv.mpf(b)) for a, b in cert['mid']]
    # F(c) with thin-ish intervals
    Fc, _, _ = equations(cmid, m)
    # floating Jacobian at c via AD with point values, then floating inverse Y
    cpt = [mpmath.mpc(mpmath.mpf(a), mpmath.mpf(b)) for a, b in cert['mid']]
    vad = [AD(CI(iv.mpf(a), iv.mpf(b)), [CI(1) if j == i else CI(0) for j in range(11)])
           for i, (a, b) in enumerate(cert['mid'])]
    eqad, _, _ = equations(vad, m)
    Jc = mpmath.matrix(11, 11)
    for i in range(11):
        for j in range(11):
            g = eqad[i].g[j]
            Jc[i, j] = mpmath.mpc(g.re.mid, g.im.mid)
    Yf = Jc ** -1
    Y = [[CI(iv.mpf(mpmath.re(Yf[i, j])), iv.mpf(mpmath.im(Yf[i, j]))) for j in range(11)] for i in range(11)]
    # box B and J(B) via AD
    B = [CI(c.re + iv.mpf([-r, r]), c.im + iv.mpf([-r, r])) for c in cmid]
    bad = [AD(B[i], [CI(1) if j == i else CI(0) for j in range(11)]) for i in range(11)]
    eqB, XB, YB = equations(bad, m)
    JB = [[eqB[i].g[j] for j in range(11)] for i in range(11)]
    # K(B)
    D = [B[i] - cmid[i] for i in range(11)]
    okK = True
    for i in range(11):
        yf = CI(0)
        for j in range(11):
            yf = yf + Y[i][j] * Fc[j]
        acc = cmid[i] - yf
        for k in range(11):
            # (I - Y J(B))_{ik}
            s = CI(1) if i == k else CI(0)
            for j in range(11):
                s = s - Y[i][j] * JB[j][k]
            acc = acc + s * D[k]
        # strict interior containment for real and imaginary parts
        for part, bpart in ((acc.re, B[i].re), (acc.im, B[i].im)):
            if not (part.a > bpart.a and part.b < bpart.b):
                okK = False
    # (D) X_34 nonzero on B
    x34 = XB[3].v - XB[4].v
    a2 = x34.abs2()
    okD = a2.a > 0
    # (T) T-test with |X_l| enclosures on B
    lo, hi = [], []
    for l in (1, 2, 3, 4):
        a2 = XB[l].v.abs2()
        up = a2.b
        lw = a2.a
        lo.append(iv.mpf(m[l - 1]) / iv.sqrt(iv.sqrt(iv.mpf(up))) if up > 0 else None)
        hi.append(iv.mpf(m[l - 1]) / iv.sqrt(iv.sqrt(iv.mpf(lw))) if lw > 0 else None)
    okT = False
    for k in range(4):
        if lo[k] is None or any(hi[l] is None for l in range(4) if l != k):
            continue
        s = iv.mpf(0)
        for l in range(4):
            if l != k:
                s = s + hi[l]
        if (lo[k] - s).a > 0:
            okT = True
            break
    box = [(float(c.re.mid), float(c.im.mid)) for c in cmid]
    return {'index': cert['index'], 'K': okK, 'D': okD, 'T': okT, 'r': float(cert['r']), 'box': box}


def main():
    certs = [json.loads(l) for l in open(sys.argv[1])]
    m = [int(x) for x in sys.argv[2:6]]
    nproc = int(sys.argv[6])
    prec = int(sys.argv[7]) if len(sys.argv) > 7 else PREC
    with Pool(nproc) as pool:
        res = pool.map(check_one, [(c, m, prec) for c in certs], chunksize=8)
    nK = sum(r['K'] for r in res)
    nD = sum(r.get('D', False) for r in res)
    nT = sum(r.get('T', False) for r in res)
    # (S) disjointness: boxes are tiny (radius r) around float midpoints; two boxes can meet only if all 22 real
    # coordinates of the midpoints differ by <= 2 r_max (plus the float rounding of the midpoints, < 1e-15 relative).
    rmax = max(r['r'] for r in res)
    pts = sorted((r['box'], r['index']) for r in res)
    tol = 2 * rmax
    worst = float('inf')
    nclose = 0
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            a, b = pts[i][0], pts[j][0]
            if b[0][0] - a[0][0] > 1e-6:
                break
            d = max(max(abs(x[0] - y[0]), abs(x[1] - y[1])) for x, y in zip(a, b))
            worst = min(worst, d)
            if d <= tol + 1e-12 * (1 + max(abs(t) for x in a for t in x)):
                nclose += 1
    print(json.dumps({'n': len(res), 'krawczyk_ok': nK, 'x34_nonzero': nD, 'T_test_ok': nT, 'r_max': rmax,
                      'pairs_not_separated': nclose, 'min_sup_distance_of_midpoints_among_near_pairs': worst}))


if __name__ == '__main__':
    main()
