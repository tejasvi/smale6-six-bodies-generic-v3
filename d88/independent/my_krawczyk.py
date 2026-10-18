#!/usr/bin/env python3
"""Referee's third, independent Krawczyk check of the d88 certificates (shares no code with d88/scripts).

Reads only the certificate centres (decimal strings) and radii.  The equations are the referee's own polynomials
(tools/mysys.py), evaluated as sparse polynomials in Arb complex balls; the Jacobian is the exact formal derivative of
those polynomials.
  n4: variables = certificate variables (X2 X3 Y1 Y2 Y3 p..); box B = c + [-r,r] + i[-r,r].
  kc: certificate variables are (X2 X3 Y1 Y2 Y3 Y4 p..); the referee's variables are (X2 X3 U1 U2 U3 p..) with
      U_k = Y_k - Y4.  The box used is the Arb image of the certificate box (radius about 2r in U), centre = image of c.
Checks per box:
  (K) Krawczyk for the square subsystem "all equations except the Y-equation of body 3";
  (R) the omitted equation's enclosure on B contains 0 (consistency; implied by the ideal equality);
  (T) n4: T-test (some k with beta_k > sum_{l != k} beta_l), rigorous; reports the best relative margin;
      kc: the 32 sums of (*94) at binary masses (m5, m6), rigorous lower bound of |sum| / (sum|beta| sqrt(1+rho^2)).
Global: (S) disjointness of the boxes in the referee's variables, exact on near pairs.
Usage: my_krawczyk.py n4|kc CERT.jsonl NPROC [m5 m6]
"""
import itertools
import json
import os
import sys
from fractions import Fraction as Fr
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mysys
from flint import acb, arb, acb_mat, ctx

MU = [1, 2, 3, 30]
KIND = None
SYS = None


def setup(kind):
    global KIND, SYS
    KIND = kind
    names, eqs = (mysys.n4_system if kind == 'n4' else mysys.kc_system)(MU)
    omit = 5   # n4: eqs = Xeq1..3, Yeq1..3, dist(6) -> index 5 = Yeq3;  kc: Xeq1..4, Yeq2, Yeq3, dist -> index 5 = Yeq3
    sq = [e for i, e in enumerate(eqs) if i != omit]
    jac = [[e.deriv(j) for j in range(len(names))] for e in sq]
    maxe = max(max(k) for e in eqs for k in e.t)
    assert maxe <= 4, maxe
    SYS = (names, sq, jac, eqs[omit])


def cst(c):
    return acb(c.numerator) if c.denominator == 1 else acb(arb(c.numerator) / c.denominator)


def ev(poly, pw):
    s = acb(0)
    for k, c in poly.t.items():
        t = cst(c)
        for i, e in enumerate(k):
            if e:
                t = t * pw[i][e]
        s += t
    return s


def powers(v):
    return [[acb(1), z, z * z, z * z * z, z * z * z * z] for z in v]


def to_vars(raw):
    if KIND == 'n4':
        return list(raw)
    X2, X3, Y1, Y2, Y3, Y4 = raw[:6]
    return [X2, X3, Y1 - Y4, Y2 - Y4, Y3 - Y4] + list(raw[6:])


def check(args):
    cert, prec, m5, m6 = args
    ctx.prec = prec
    names, sq, jac, omitted = SYS
    n = len(names)
    c_raw = [acb(arb(a), arb(b)) for a, b in cert['mid']]
    rr = arb(0, cert['r'])
    B_raw = [acb(z.real + rr, z.imag + rr) for z in c_raw]
    c = to_vars(c_raw)
    B = to_vars(B_raw)
    pc, pB = powers(c), powers(B)
    Fc = [ev(e, pc) for e in sq]
    Jc = acb_mat([[ev(d, pc) for d in row] for row in jac])
    JB = acb_mat([[ev(d, pB) for d in row] for row in jac])
    Jinv = Jc.inv()
    Yi = acb_mat([[acb(Jinv[i, j].real.mid(), Jinv[i, j].imag.mid()) for j in range(n)] for i in range(n)])
    yf = Yi * acb_mat([[x] for x in Fc])
    Imat = acb_mat([[acb(1) if i == j else acb(0) for j in range(n)] for i in range(n)])
    D = acb_mat([[B[i] - c[i]] for i in range(n)])
    K = acb_mat([[c[i] - yf[i, 0]] for i in range(n)]) + (Imat - Yi * JB) * D
    okK = all(B[i].contains_interior(K[i, 0]) for i in range(n))
    okR = ev(omitted, pB).contains(0)
    out = {'index': cert['index'], 'K': okK, 'R': okR}
    if KIND == 'n4':
        X2, X3 = B_raw[0], B_raw[1]
        X1 = X2 + 1
        X4 = -(MU[0] * X1 + MU[1] * X2 + MU[2] * X3) / MU[3]
        Xs = [X1, X2, X3, X4]
        lo, hi = [], []
        for l in range(4):
            a = abs(Xs[l])
            lo.append(arb(MU[l]) / a.upper().sqrt())
            hi.append(arb(MU[l]) / a.lower().sqrt() if a.lower() > 0 else None)
        best = None
        bestk = None
        for k in range(4):
            if any(hi[l] is None for l in range(4) if l != k):
                continue
            s = sum((hi[l] for l in range(4) if l != k), arb(0))
            mg = lo[k] - s
            if mg > 0:
                rel = float((mg / (lo[k] + s)).lower())
                if best is None or rel > best:
                    best, bestk = rel, k
        out['T'] = best
        out['Tk'] = bestk
    else:
        Xs = [acb(1), B_raw[0], B_raw[1]]
        rho = (arb(m6) / arb(m5)).sqrt() ** 3
        beta = []
        for l in range(3):
            xl = Xs[l]
            s_ = acb(0, 1) * (-xl).sqrt() if xl.real.mid() < 0 else xl.sqrt()
            beta.append(acb(MU[l]) / s_)
        tot = sum((abs(b) for b in beta), arb(0)) * (1 + rho * rho).sqrt()
        worst = worst_u = None
        for eps in itertools.product([1, -1], repeat=3):
            if eps[0] != 1:
                continue
            for s in itertools.product([1, -1], repeat=3):
                val = sum((eps[l] * beta[l] * (1 + acb(0, s[l]) * rho) for l in range(3)), acb(0))
                lb = abs(val).lower()
                q = float((lb / tot).lower()) if lb > 0 else 0.0
                worst = q if worst is None else min(worst, q)
                if s[0] == s[1] == s[2]:
                    worst_u = q if worst_u is None else min(worst_u, q)
        out['Q'] = worst
        out['Qu'] = worst_u
        # |Y4| (escape indicator): Y4 = force(U,1) - U1 in referee variables, report the raw value
        out['absY4'] = float(abs(c_raw[5]).upper())
    out['c'] = [(float(z.real.mid()), float(z.imag.mid())) for z in c]
    out['rad'] = max(float(z.rad()) for z in B)
    out['cm'] = [[z.real.mid().str(80, radius=False), z.imag.mid().str(80, radius=False)] for z in c]
    return out


def main():
    kind, path, nproc = sys.argv[1], sys.argv[2], int(sys.argv[3])
    m5, m6 = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (1, 2)
    setup(kind)
    certs = [json.loads(l) for l in open(path)]
    with Pool(nproc, initializer=setup, initargs=(kind,)) as pool:
        res = pool.map(check, [(ct, 400, m5, m6) for ct in certs], chunksize=8)
    summ = {'kind': kind, 'n': len(res), 'krawczyk_ok': sum(r['K'] for r in res),
            'omitted_eq_contains_0': sum(r['R'] for r in res)}
    if kind == 'n4':
        summ['T_pass'] = sum(r['T'] is not None for r in res)
        summ['min_T_rel_margin'] = min((r['T'] for r in res if r['T'] is not None), default=None)
        summ['T_body_counts'] = {k: sum(1 for r in res if r['Tk'] == k) for k in range(4)}
    else:
        summ['torque_pass'] = sum((r['Q'] or 0) > 0 for r in res)
        summ['min_torque_rel'] = min(r['Q'] for r in res)
        summ['min_torque_rel_uniform_patterns'] = min(r['Qu'] for r in res)
        summ['n_below_1e-4'] = sum(r['Q'] < 1e-4 for r in res)
        summ['n_below_1e-5'] = sum(r['Q'] < 1e-5 for r in res)
        summ['max_absY4'] = max(r['absY4'] for r in res)
    # (S) disjointness: boxes have componentwise radius <= rad (in both real and imaginary parts)
    radmax = max(r['rad'] for r in res)
    order = sorted(range(len(res)), key=lambda i: res[i]['c'][0][0])
    nnear = 0
    nbad = 0
    mind = None
    for a in range(len(order)):
        for b in range(a + 1, len(order)):
            i, j = order[a], order[b]
            if res[j]['c'][0][0] - res[i]['c'][0][0] > 1e-9:
                break
            d = max(max(abs(x[0] - y[0]), abs(x[1] - y[1])) for x, y in zip(res[i]['c'], res[j]['c']))
            mind = d if mind is None else min(mind, d)
            if d < 1e-6:
                nnear += 1
                sep = any(abs(Fr(x) - Fr(y)) > 2 * Fr(radmax) * 2 for u, w in zip(res[i]['cm'], res[j]['cm'])
                          for x, y in zip(u, w))
                if not sep:
                    nbad += 1
    summ['near_pairs_float_lt_1e-6'] = nnear
    summ['not_separated'] = nbad
    summ['min_supdist_pairs_with_first_coord_within_1e-9'] = mind
    summ['max_box_radius_used'] = radmax
    print(json.dumps(summ))


if __name__ == '__main__':
    main()
