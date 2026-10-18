#!/usr/bin/env python3
"""Mechanical cross-check of the integrality lemma for the four-body system N_4 at masses m0 (DERIVATION A.6), and the
same test for the 'K4 with centre' system KC of diagram 94.  Uses tropcheck.py (initial forms over F_p on the
cones of the tropical prevariety of a generating set enlarged by identities).

N_4 torus variables: all pairwise differences X_kl, Y_kl (k < l) and p_kl, with the slice X_12 = 1; positions by the
centre of mass.  KC torus variables: X_k = X_k4 (X_4 = 0), X_kl (k < l <= 3), U_k = Y_k - Y_4, U_kl, p_kl, slice
X_1 = 1; Y_4 eliminated by the Y-equation of body 1.
Usage: n4_trop.py n4|kc m1 m2 m3 m4 p WORKDIR [identities: none|basic|all]
"""
import itertools
import json
import os
import sys

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tropcheck

PAIRS = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]


def n4_system(m, ident):
    m = {i + 1: (sp.Integer(x) if not isinstance(x, sp.Basic) else x) for i, x in enumerate(m)}
    M = sum(m.values())
    Xs = {pr: sp.Symbol('X%d%d' % pr) for pr in PAIRS}
    Ys = {pr: sp.Symbol('Y%d%d' % pr) for pr in PAIRS}
    Ps = {pr: sp.Symbol('p%d%d' % pr) for pr in PAIRS}
    Xs[(1, 2)] = sp.Integer(1)
    gens = [Xs[pr] for pr in PAIRS if pr != (1, 2)] + [Ys[pr] for pr in PAIRS] + [Ps[pr] for pr in PAIRS]

    def D(S, k, l):
        return S[(k, l)] if k < l else -S[(l, k)]

    def P(k, l):
        return Ps[(min(k, l), max(k, l))]
    polys = []
    # cycle relations
    for S in (Xs, Ys):
        polys += [D(S, 1, 3) - D(S, 1, 2) - D(S, 2, 3), D(S, 1, 4) - D(S, 1, 2) - D(S, 2, 4),
                  D(S, 3, 4) - D(S, 1, 4) + D(S, 1, 3)]
    pos = {}
    for name, S in (('X', Xs), ('Y', Ys)):
        pos[name] = {k: sum(m[l] * D(S, k, l) for l in m if l != k) / M for k in m}
    for name, S in (('X', Xs), ('Y', Ys)):
        for k in m:
            polys.append(sp.expand(M * (pos[name][k] - sum(m[l] * P(k, l) ** 3 * D(S, k, l) for l in m if l != k))))
    for pr in PAIRS:
        polys.append(Ps[pr] ** 2 * Xs[pr] * Ys[pr] - 1)
    if ident in ('basic', 'all'):
        X, Y = pos['X'], pos['Y']
        for J in [(1, 2), (1, 3), (1, 4)]:
            T = sum(m[k] * m[l] * P(k, l) ** 3 * (X[k] * Y[l] - X[l] * Y[k]) for k in J for l in m if l not in J)
            polys.append(sp.expand(M * M * T))
    if ident == 'all':
        X, Y = pos['X'], pos['Y']
        for J in [(1, 2), (1, 3), (1, 4)]:
            for name, S in (('X', Xs), ('Y', Ys)):
                Z = pos[name]
                SJ = sum(m[k] * Z[k] for k in J) - sum(m[k] * m[l] * P(k, l) ** 3 * D(S, k, l) for k in J for l in m if l not in J)
                polys.append(sp.expand(M * SJ))
        U = sum(m[k] * m[l] * P(k, l) for (k, l) in PAIRS)
        V = sum(m[k] * X[k] * Y[k] for k in m)
        polys.append(sp.expand(M * M * (V - U)))
    # integer coefficients
    if any(isinstance(v, sp.Symbol) for v in m.values()):
        return [sp.expand(f) for f in polys if sp.expand(f) != 0], gens
    out = []
    for f in polys:
        f = sp.expand(f)
        if f == 0:
            continue
        Pp = sp.Poly(f, *gens)
        den = sp.ilcm(*[sp.fraction(sp.Rational(c))[1] for c in Pp.coeffs()])
        Pp = sp.Poly(sp.expand(Pp.as_expr() * den), *gens)
        g = sp.igcd(*[int(c) for c in Pp.coeffs()])
        out.append(sp.expand(Pp.as_expr() / g))
    return out, gens


def kc_system(m, ident, variants=3):
    m = {i + 1: (sp.Integer(x) if not isinstance(x, sp.Basic) else x) for i, x in enumerate(m)}
    X = {1: sp.Integer(1), 2: sp.Symbol('X2'), 3: sp.Symbol('X3'), 4: sp.Integer(0)}
    U = {1: sp.Symbol('U1'), 2: sp.Symbol('U2'), 3: sp.Symbol('U3'), 4: sp.Integer(0)}
    Xd = {(1, 2): sp.Symbol('X12'), (1, 3): sp.Symbol('X13'), (2, 3): sp.Symbol('X23')}
    Ud = {(1, 2): sp.Symbol('U12'), (1, 3): sp.Symbol('U13'), (2, 3): sp.Symbol('U23')}
    Ps = {pr: sp.Symbol('p%d%d' % pr) for pr in PAIRS}
    gens = [X[2], X[3], Xd[(1, 2)], Xd[(1, 3)], Xd[(2, 3)], U[1], U[2], U[3], Ud[(1, 2)], Ud[(1, 3)], Ud[(2, 3)]] + \
        [Ps[pr] for pr in PAIRS]

    def DX(k, l):
        if l == 4:
            return X[k]
        if k == 4:
            return -X[l]
        return Xd[(k, l)] if k < l else -Xd[(l, k)]

    def DU(k, l):
        if l == 4:
            return U[k]
        if k == 4:
            return -U[l]
        return Ud[(k, l)] if k < l else -Ud[(l, k)]

    def P(k, l):
        return Ps[(min(k, l), max(k, l))]
    polys = []
    for (k, l) in [(1, 2), (1, 3), (2, 3)]:
        polys.append(Xd[(k, l)] - X[k] + X[l])
        polys.append(Ud[(k, l)] - U[k] + U[l])
    for k in (1, 2, 3, 4):
        polys.append(X[k] - sum(m[l] * P(k, l) ** 3 * DX(k, l) for l in m if l != k))
    # Y-equations: Y_k = Y4 + U_k ; Yeq_k: Y4 + U_k - sum m p^3 DU(k,l) ; eliminate Y4 by differences
    R = {k: U[k] - sum(m[l] * P(k, l) ** 3 * DU(k, l) for l in m if l != k) for k in (1, 2, 3)}
    polys.append(sp.expand(R[2] - R[1]))
    polys.append(sp.expand(R[3] - R[1]))
    # the same differences written with the difference variables U_kl (U_k - U_l -> U_kl): same ideal, sharper supports
    for (k, l) in [(1, 2), (1, 3), (2, 3)]:
        Rk = -sum(m[j] * P(k, j) ** 3 * DU(k, j) for j in m if j != k)
        Rl = -sum(m[j] * P(l, j) ** 3 * DU(l, j) for j in m if j != l)
        polys.append(sp.expand(Ud[(k, l)] + Rk - Rl))
    for (k, l) in PAIRS:
        polys.append(P(k, l) ** 2 * DX(k, l) * DU(k, l) - 1)
    if ident in ('basic', 'all'):
        # torques T_J = sum_{k in J, l not in J} m_k m_l p^3 (X_k Y_l - X_l Y_k); with Y = Y4 + U the Y4-terms cancel
        # only for... we use T_J with Y4 eliminated: Y4 = -R[1] (from Yeq_1: Y4 + R[1] = 0)
        # Y4 can be eliminated with the Y-equation of any of bodies 1, 2, 3 (Y4 = -R[k]); all versions are in the
        # ideal, and different versions expose different leading terms (no spurious cancellations)
        for kk in ((1, 2, 3) if variants == 3 else (1,)):
            Y4 = -R[kk]
            Yp = {k: Y4 + U[k] for k in (1, 2, 3)}
            Yp[4] = Y4
            for J in [(1,), (2,), (3,), (1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (3, 4)]:
                T = sum(m[k] * m[l] * P(k, l) ** 3 * (X[k] * Yp[l] - X[l] * Yp[k]) for k in J for l in m if l not in J)
                polys.append(sp.expand(T))
    if ident == 'all':
        for J in [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (3, 4)]:
            SJ = sum(m[k] * X[k] for k in J) - sum(m[k] * m[l] * P(k, l) ** 3 * DX(k, l) for k in J for l in m if l not in J)
            polys.append(sp.expand(SJ))
        # X-centre of mass (sum of all X-equations) and the 3-element X-subset sums
        polys.append(sp.expand(sum(m[k] * X[k] for k in (1, 2, 3))))
        for J in [(1, 2, 3), (1, 2, 4), (1, 3, 4), (2, 3, 4)]:
            SJ = sum(m[k] * X[k] for k in J) - sum(m[k] * m[l] * P(k, l) ** 3 * DX(k, l) for k in J for l in m if l not in J)
            polys.append(sp.expand(SJ))
        # Y-subset sums over J in {1,2,3} with Y_k = Y4 + U_k; combinations of two of them with Y4 eliminated
        SY = {}
        for kk in ((1, 2, 3) if variants == 3 else (1,)):
            Y4e = -R[kk]
            for J in [(1,), (2,), (3,), (1, 2), (1, 3), (2, 3), (1, 2, 3)]:
                SY[J] = sum(m[k] * (Y4e + U[k]) for k in J) - sum(m[k] * m[l] * P(k, l) ** 3 * DU(k, l) for k in J for l in m if l not in J)
                polys.append(sp.expand(SY[J]))
        # virial with the other eliminations of Y4
        Uu = sum(m[k] * m[l] * P(k, l) for (k, l) in PAIRS)
        for kk in ((2, 3) if variants == 3 else ()):
            V = sum(m[k] * X[k] * (-R[kk] + U[k]) for k in (1, 2, 3))
            polys.append(sp.expand(V - Uu))
        Js = list(SY)
        for a in range(len(Js)):
            for b in range(a + 1, len(Js)):
                A, B = Js[a], Js[b]
                ma, mb = sum(m[k] for k in A), sum(m[k] for k in B)
                # Y4-free: mb*S_A - ma*S_B with S written using U only
                SA = sum(m[k] * U[k] for k in A) - sum(m[k] * m[l] * P(k, l) ** 3 * DU(k, l) for k in A for l in m if l not in A)
                SB = sum(m[k] * U[k] for k in B) - sum(m[k] * m[l] * P(k, l) ** 3 * DU(k, l) for k in B for l in m if l not in B)
                polys.append(sp.expand(mb * SA - ma * SB))
        Uu = sum(m[k] * m[l] * P(k, l) for (k, l) in PAIRS)
        Y4 = -R[1]
        V = sum(m[k] * X[k] * (Y4 + U[k]) for k in (1, 2, 3))
        polys.append(sp.expand(V - Uu))
    if any(isinstance(v, sp.Symbol) for v in m.values()):
        return [sp.expand(f) for f in polys if sp.expand(f) != 0], gens
    out = []
    for f in polys:
        f = sp.expand(f)
        if f == 0:
            continue
        Pp = sp.Poly(f, *gens)
        den = sp.ilcm(*[sp.fraction(sp.Rational(c))[1] for c in Pp.coeffs()])
        Pp = sp.Poly(sp.expand(Pp.as_expr() * den), *gens)
        g = sp.igcd(*[int(c) for c in Pp.coeffs()])
        out.append(sp.expand(Pp.as_expr() / g))
    return out, gens


def support_check(kind, m0, p, ident):
    """The coefficients of G are polynomials in the masses; check that none of them vanishes at m0 mod p, so the
    supports at m0 are the generic supports and every coefficient is a unit at any valuation dominating (p, m - m0)."""
    mu = sp.symbols('mu1 mu2 mu3 mu4')
    polys, gens = (n4_system if kind == 'n4' else kc_system)(list(mu), ident)
    sub = dict(zip(mu, [sp.Integer(x) for x in m0]))
    bad = 0
    nterm = 0
    for f in polys:
        num, den = sp.fraction(sp.together(f))
        P = sp.Poly(sp.expand(num), *gens)
        dval = sp.Rational(den.subs(sub))
        assert dval != 0 and sp.fraction(dval)[0] % p != 0
        for mon, c in P.terms():
            nterm += 1
            cv = sp.Rational(sp.expand(c).subs(sub))
            if cv == 0 or sp.fraction(cv)[0] % p == 0:
                bad += 1
    return {'terms': nterm, 'coefficients_vanishing_at_m0_mod_p': bad}


def main():
    kind = sys.argv[1]
    m = [int(x) for x in sys.argv[2:6]]
    p = int(sys.argv[6])
    wd = sys.argv[7]
    ident = sys.argv[8] if len(sys.argv) > 8 else 'all'
    sc = support_check(kind, m, p, ident)
    print('support check', sc, flush=True)
    assert sc['coefficients_vanishing_at_m0_mod_p'] == 0
    polys, gens = (n4_system if kind == 'n4' else kc_system)(m, ident)
    print(kind, 'polys', len(polys), 'vars', len(gens), flush=True)
    res = tropcheck.run(polys, gens, p, wd, '%s_%s' % (kind, ident))
    print(json.dumps({k: v for k, v in res.items() if k != 'failures'}))
    for f in res['failures'][:20]:
        print('FAIL', f)
    json.dump(res, open(os.path.join(wd, '%s_%s_result.json' % (kind, ident)), 'w'))


if __name__ == '__main__':
    main()
