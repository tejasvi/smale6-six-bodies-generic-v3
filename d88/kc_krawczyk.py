#!/usr/bin/env python3
"""Krawczyk certification (Arb, python-flint) of the solutions of the 'K4 with centre' system KC12 (diagram 94), and
the interval torque test (★94) at fixed binary masses.

KC12: unknowns v = (X2, X3, Y1, Y2, Y3, Y4, p12, p13, p14, p23, p24, p34); X1 = 1, X4 = 0; equations: X-equations of
bodies 1, 2, 3 (X_k = sum_l mu_l p_kl^3 (X_k - X_l)), of body 4 (0 = sum_l mu_l p_4l^3 (X_4 - X_l)), Y-equations of
bodies 1, 2, the six distance equations.  The Y-equation of body 3 follows from the torque identity
sum_{k<=3} mu_k (Y_k Xeq_k - X_k Yeq_k) + mu_4 Y_4 Xeq_4 = 0 when X_3 != 0 (checked on the box).

Torque test (DERIVATION B.4): with beta_l = mu_l / sqrt(X_l) (l = 1, 2, 3; any branch), rho = (m6/m5)^(3/2), for all
eps in {1} x {+-1}^2 and s in {+-1}^3:  sum_l eps_l beta_l (1 + i s_l rho) != 0.  Checked by a rigorous lower bound
of the modulus on the certified box.
Usage: kc_krawczyk.py SOLS.txt mu1 mu2 mu3 mu4 m5 m6 OUT.jsonl NPROC [PREC]   (SOLS.txt: see arrayio.py)
"""
import itertools
import json
import os
import sys
from multiprocessing import Pool

import numpy as np
from flint import acb, arb, acb_mat, ctx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arrayio

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
PIDX = {pr: 6 + i for i, pr in enumerate(PAIRS)}


def pidx(k, l):
    return PIDX[(min(k, l), max(k, l))]


def pos(v):
    X = [acb(1), v[0], v[1], acb(0)]
    Y = [v[2], v[3], v[4], v[5]]
    return X, Y


def F(v, mu, full=False):
    X, Y = pos(v)
    m = [acb(x) for x in mu]
    out = []

    def ceq(Z, k, lhs=True):
        s = Z[k] if lhs else acb(0)
        for l in range(4):
            if l != k:
                p = v[pidx(k, l)]
                s = s - m[l] * (p * p * p) * (Z[k] - Z[l])
        return s
    for k in range(3):
        out.append(ceq(X, k))
    out.append(ceq(X, 3, lhs=False))
    for k in range(2):
        out.append(ceq(Y, k))
    for (a, b) in PAIRS:
        p = v[pidx(a, b)]
        out.append(p * p * (X[a] - X[b]) * (Y[a] - Y[b]) - 1)
    if full:
        out.append(ceq(Y, 2))
    return out


# derivative selectors: X depends on v0 (X2), v1 (X3); Y_k on v[2+k]
DX = [[0] * 12 for _ in range(4)]
DX[1][0] = 1
DX[2][1] = 1
DY = [[0] * 12 for _ in range(4)]
for _k in range(4):
    DY[_k][2 + _k] = 1


def J(v, mu):
    X, Y = pos(v)
    m = [acb(x) for x in mu]
    rows = []
    for (Z, D, ks) in ((X, DX, [(0, True), (1, True), (2, True), (3, False)]), (Y, DY, [(0, True), (1, True)])):
        for (k, lhs) in ks:
            g = [acb(D[k][j]) if lhs else acb(0) for j in range(12)]
            for l in range(4):
                if l != k:
                    j0 = pidx(k, l)
                    p = v[j0]
                    p2 = p * p
                    p3 = p2 * p
                    d = Z[k] - Z[l]
                    for j in range(12):
                        c = D[k][j] - D[l][j]
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
        g = [acb(0)] * 12
        for j in range(12):
            cx = DX[a][j] - DX[b][j]
            cy = DY[a][j] - DY[b][j]
            if cx != 0 or cy != 0:
                g[j] = p2 * (dy * cx + dx * cy)
        g[j0] = g[j0] + 2 * p * dx * dy
        rows.append(g)
    return acb_mat(rows)


def _mid(z):
    return acb(z.real.mid(), z.imag.mid())


def certify_one(args):
    v0, mu, m5, m6, prec = args
    ctx.prec = prec
    v = [acb(complex(z).real, complex(z).imag) for z in v0]
    for _ in range(10):
        f = F(v, mu)
        try:
            dv = J(v, mu).solve(acb_mat([[x] for x in f]))
        except Exception:
            return {'ok': False, 'why': 'singular in Newton'}
        v = [_mid(v[i] - dv[i, 0]) for i in range(12)]
    DIG = 70
    cstr = [[z.real.mid().str(DIG, radius=False), z.imag.mid().str(DIG, radius=False)] for z in v]
    v = [acb(arb(a), arb(b)) for a, b in cstr]
    try:
        Yi = J(v, mu).inv()
    except Exception:
        return {'ok': False, 'why': 'singular J'}
    Ym = acb_mat([[_mid(Yi[i, j]) for j in range(12)] for i in range(12)])
    f = F(v, mu)
    yf = Ym * acb_mat([[x] for x in f])
    nyf = max(float(abs(yf[i, 0]).upper()) for i in range(12))
    vmax = max(float(abs(z).upper()) for z in v)
    r = max(nyf * 1e4, 1e-58 * (1 + vmax))
    I12 = acb_mat([[acb(1) if i == j else acb(0) for j in range(12)] for i in range(12)])
    ok = False
    for attempt in range(8):
        rr = arb(0, r)
        B = [acb(z.real + rr, z.imag + rr) for z in v]
        JB = J(B, mu)
        Dm = acb_mat([[B[i] - v[i]] for i in range(12)])
        K = acb_mat([[v[i] - yf[i, 0]] for i in range(12)]) + (I12 - Ym * JB) * Dm
        ok = all(B[i].contains_interior(K[i, 0]) for i in range(12))
        if ok:
            break
        r *= 100
    if not ok:
        return {'ok': False, 'why': 'krawczyk failed', 'r': r}
    X, Y = pos(B)
    res = {'ok': True, 'r': r, 'mid': cstr, 'x3_nonzero': not X[2].contains(0)}
    # torque test at (m5, m6)
    rho = (arb(m6) / arb(m5)) ** 1.5
    beta = []
    for l in range(3):
        xl = X[l]
        if float(xl.real.mid()) < 0:
            sq = acb(0, 1) * (-xl).sqrt()
        else:
            sq = xl.sqrt()
        beta.append(acb(mu[l]) / sq)
    tot = sum((abs(b) for b in beta), arb(0))
    worst = None
    for e in itertools.product([1, -1], repeat=2):
        eps = (1,) + e
        for s in itertools.product([1, -1], repeat=3):
            val = sum((eps[l] * beta[l] * (1 + acb(0, s[l]) * rho) for l in range(3)), acb(0))
            lo = abs(val).lower()
            rel = float((lo / (tot * (1 + rho * rho).sqrt())).lower())
            if worst is None or rel < worst:
                worst = rel
    res['torque_min_rel_lower'] = worst
    res['torque_ok'] = worst is not None and worst > 0
    return res


def main():
    sols = arrayio.load_array(sys.argv[1])
    mu = [int(x) for x in sys.argv[2:6]]
    m5, m6 = int(sys.argv[6]), int(sys.argv[7])
    out = sys.argv[8]
    nproc = int(sys.argv[9])
    prec = int(sys.argv[10]) if len(sys.argv) > 10 else 320
    with Pool(nproc) as pool:
        res = pool.map(certify_one, [(list(s), mu, m5, m6, prec) for s in sols], chunksize=8)
    with open(out, 'w') as fo:
        for i, r in enumerate(res):
            r['index'] = i
            fo.write(json.dumps(r) + '\n')
    print(json.dumps({'n': len(res), 'krawczyk_ok': sum(r['ok'] for r in res),
                      'x3_nonzero': sum(r.get('x3_nonzero', False) for r in res),
                      'torque_ok': sum(r.get('torque_ok', False) for r in res),
                      'min_torque_rel': min((r['torque_min_rel_lower'] for r in res if r.get('ok')), default=None)}))


if __name__ == '__main__':
    main()
