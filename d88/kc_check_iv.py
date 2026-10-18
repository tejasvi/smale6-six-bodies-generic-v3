#!/usr/bin/env python3
"""Independent checker for kc_krawczyk.py certificates (diagram 94, 'K4 with centre' system KC12).

Shares no code with kc_krawczyk.py: mpmath.iv intervals (complex boxes as pairs of real intervals), Jacobian by
forward-mode automatic differentiation of the equations (written out again here).  Reads only the centres (decimal
strings) and radii.  Checks: (K) Krawczyk on each box; (D) X_3 != 0 on the box; (Q) the torque test at binary masses
(m5, m6): for every eps in {1} x {+-1}^2, s in {+-1}^3, |sum_l eps_l beta_l (1 + i s_l rho)| > 0 with
beta_l = mu_l / sqrt(X_l) (a fixed square root on the box), rho = (m6/m5)^(3/2); (S) pairwise disjointness.
Usage: kc_check_iv.py CERT.jsonl mu1 mu2 mu3 mu4 m5 m6 NPROC [PREC]
"""
import itertools
import json
import sys
from multiprocessing import Pool

import mpmath
from mpmath import iv, mp


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
        return self.re * self.re + self.im * self.im


def _c(x):
    return x if isinstance(x, CI) else CI(iv.mpf(x), iv.mpf(0))


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


def equations(v, mu, ad_zero):
    """v: 12 entries (CI or AD) = X2, X3, Y1, Y2, Y3, Y4, p12, p13, p14, p23, p24, p34."""
    one = CI(1)
    zero = ad_zero
    X = {1: one if not isinstance(v[0], AD) else AD(one, [CI(0)] * 12), 2: v[0], 3: v[1], 4: zero}
    Y = {1: v[2], 2: v[3], 3: v[4], 4: v[5]}
    p = {(1, 2): v[6], (1, 3): v[7], (1, 4): v[8], (2, 3): v[9], (2, 4): v[10], (3, 4): v[11]}
    m = {1: mu[0], 2: mu[1], 3: mu[2], 4: mu[3]}

    def P(k, l):
        return p[(min(k, l), max(k, l))]
    eqs = []
    for k in (1, 2, 3, 4):
        s = X[k] if k < 4 else zero
        for l in (1, 2, 3, 4):
            if l != k:
                pk = P(k, l)
                s = s - (pk * pk * pk) * (X[k] - X[l]) * m[l]
        eqs.append(s)
    for k in (1, 2):
        s = Y[k]
        for l in (1, 2, 3, 4):
            if l != k:
                pk = P(k, l)
                s = s - (pk * pk * pk) * (Y[k] - Y[l]) * m[l]
        eqs.append(s)
    for (k, l) in [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]:
        pk = P(k, l)
        eqs.append(pk * pk * (X[k] - X[l]) * (Y[k] - Y[l]) - 1)
    return eqs, X, Y


def isqrt_c(z):
    """An interval enclosure of one square root of the complex box z (z away from 0 and small)."""
    # use mpmath on the midpoint to pick the branch, then enclose by a Newton-type interval refinement
    zm = mpmath.mpc(z.re.mid, z.im.mid)
    s0 = mpmath.sqrt(zm) if mpmath.re(zm) >= 0 else 1j * mpmath.sqrt(-zm)
    # enclosure: |sqrt(z) - s0| <= |z - s0^2| / (|s0| - ...) ; use |sqrt(z) - s0| <= |z - z0| / |s0| * 1.01 + tiny
    rad = iv.mpf(mpmath.mpf(max(abs(z.re.delta), abs(z.im.delta)))) if False else None
    zr = mpmath.mpf(max(z.re.b - z.re.a, z.im.b - z.im.a))
    e = (zr + abs(s0 * s0 - zm)) / abs(s0) * mpmath.mpf('1.1') + mpmath.mpf(10) ** (-(mp.dps - 5))
    return CI(iv.mpf([mpmath.re(s0) - e, mpmath.re(s0) + e]), iv.mpf([mpmath.im(s0) - e, mpmath.im(s0) + e]))


def check_one(args):
    cert, mu, m5, m6, prec = args
    iv.prec = prec
    mp.prec = prec
    if not cert.get('ok'):
        return {'index': cert['index'], 'K': False}
    r = iv.mpf(cert['r'])
    c = [CI(iv.mpf(a), iv.mpf(b)) for a, b in cert['mid']]
    Fc, _, _ = equations(c, mu, CI(0))
    vad = [AD(c[i], [CI(1) if j == i else CI(0) for j in range(12)]) for i in range(12)]
    eqad, _, _ = equations(vad, mu, AD(CI(0), [CI(0)] * 12))
    Jc = mpmath.matrix(12, 12)
    for i in range(12):
        for j in range(12):
            g = eqad[i].g[j]
            Jc[i, j] = mpmath.mpc(g.re.mid, g.im.mid)
    Yf = Jc ** -1
    Y = [[CI(iv.mpf(mpmath.re(Yf[i, j])), iv.mpf(mpmath.im(Yf[i, j]))) for j in range(12)] for i in range(12)]
    B = [CI(z.re + iv.mpf([-r, r]), z.im + iv.mpf([-r, r])) for z in c]
    bad = [AD(B[i], [CI(1) if j == i else CI(0) for j in range(12)]) for i in range(12)]
    eqB, XB, YB = equations(bad, mu, AD(CI(0), [CI(0)] * 12))
    JB = [[eqB[i].g[j] for j in range(12)] for i in range(12)]
    D = [B[i] - c[i] for i in range(12)]
    okK = True
    for i in range(12):
        yf = CI(0)
        for j in range(12):
            yf = yf + Y[i][j] * Fc[j]
        acc = c[i] - yf
        for k in range(12):
            s = CI(1) if i == k else CI(0)
            for j in range(12):
                s = s - Y[i][j] * JB[j][k]
            acc = acc + s * D[k]
        for part, bp in ((acc.re, B[i].re), (acc.im, B[i].im)):
            if not (part.a > bp.a and part.b < bp.b):
                okK = False
    x3 = XB[3].v
    okD = x3.abs2().a > 0
    # torque test
    Xl = [XB[1].v if isinstance(XB[1], AD) else XB[1], XB[2].v, XB[3].v]
    beta = []
    for l in range(3):
        s = isqrt_c(Xl[l])
        # beta = mu_l / s  : enclose 1/s via conj(s)/|s|^2
        den = s.abs2()
        inv = CI(s.re / den, -s.im / den)
        beta.append(inv * mu[l])
    rho = (iv.mpf(m6) / iv.mpf(m5)) ** iv.mpf(1.5)
    okQ = True
    for e in itertools.product([1, -1], repeat=2):
        eps = (1,) + e
        for sg in itertools.product([1, -1], repeat=3):
            val = CI(0)
            for l in range(3):
                val = val + beta[l] * CI(iv.mpf(eps[l]), iv.mpf(eps[l] * sg[l]) * rho)
            if not (val.abs2().a > 0):
                okQ = False
    return {'index': cert['index'], 'K': okK, 'D': okD, 'Q': okQ, 'r': float(cert['r']),
            'box': [(float(z.re.mid), float(z.im.mid)) for z in c]}


def main():
    certs = [json.loads(l) for l in open(sys.argv[1])]
    mu = [int(x) for x in sys.argv[2:6]]
    m5, m6 = int(sys.argv[6]), int(sys.argv[7])
    nproc = int(sys.argv[8])
    prec = int(sys.argv[9]) if len(sys.argv) > 9 else 320
    with Pool(nproc) as pool:
        res = pool.map(check_one, [(c, mu, m5, m6, prec) for c in certs], chunksize=4)
    rmax = max(r['r'] for r in res if 'r' in r)
    pts = sorted((r['box'], r['index']) for r in res if 'box' in r)
    nclose = 0
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            a, b = pts[i][0], pts[j][0]
            if b[0][0] - a[0][0] > 1e-6:
                break
            d = max(max(abs(x[0] - y[0]), abs(x[1] - y[1])) for x, y in zip(a, b))
            if d <= 2 * rmax + 1e-10 * (1 + max(abs(t) for x in a for t in x)):
                nclose += 1
    print(json.dumps({'n': len(res), 'krawczyk_ok': sum(r['K'] for r in res), 'x3_nonzero': sum(r.get('D', False) for r in res),
                      'torque_ok': sum(r.get('Q', False) for r in res), 'r_max': rmax, 'pairs_not_separated': nclose}))


if __name__ == '__main__':
    main()
