#!/usr/bin/env python3
"""The 'K4 with centre' leading system KC of diagram 94, in torus variables, for msolve (mod p) and gfan (mixed volume).

Diagram 94 (Chang-Chen labels): z-triangle {4,5,6} with z-circles 5, 6; w-K4 {1,2,3,4} with w-circles 1, 2, 3.
KC(mu), mu = (m1, m2, m3, m4) the K4 masses, body 4 the centre.  X = [w]_{-2} (stretched), Y = [z]_{+2}:
  X_4 = 0;  X-equations of bodies 1..4:  X_k = sum_{l != k} mu_l p_kl^3 (X_k - X_l)   (for k = 4 the left side is 0);
  Y-equations of bodies 1..3:  Y_k = sum_{l != k} mu_l p_kl^3 (Y_k - Y_l)   (body 4's is not part of the system);
  distances  p_kl^2 (X_k - X_l)(Y_k - Y_l) = 1  for the six pairs.
Rotation slice: X_1 = 1 (X_1 = X_14 != 0).  Torus variables: X2, X3 (= X_24, X_34), U1, U2, U3 (U_k = Y_k - Y_4), p12..p34.
Y_4 is eliminated with the Y-equation of body 1.  Equations: X-equations of bodies 1..4, Y-equations of bodies 2, 3
(after the substitution), six distance equations: 12 equations in 11 unknowns ('full', for msolve), or the square
subsystem without the Y-equation of body 3 ('square', for gfan; that equation follows from the torque identity,
since X_3 != 0).
Usage: kc_sys.py full|square m1 m2 m3 m4 CHAR OUT
"""
import os
import sys
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def kc_system(mu):
    mu = [sp.Integer(v) for v in mu]
    X2, X3, U1, U2, U3 = sp.symbols('X2 X3 U1 U2 U3')
    ps = sp.symbols('p12 p13 p14 p23 p24 p34')
    P = dict(zip(PAIRS, ps))

    def p(a, b):
        return P[(min(a, b), max(a, b))]
    X = [sp.Integer(1), X2, X3, sp.Integer(0)]
    U = [U1, U2, U3, sp.Integer(0)]
    # Y_k = Y4 + U_k ; Y-equation of body 1 gives Y4
    def yeq(k, Y4):
        Yk = Y4 + U[k]
        return Yk - sum(mu[l] * p(k, l) ** 3 * (U[k] - U[l]) for l in range(4) if l != k)
    Y4s = sp.Symbol('Y4s')
    Y4 = sp.solve(yeq(0, Y4s), Y4s)[0]
    eqs = []
    for k in range(4):
        lhs = X[k] if k < 3 else sp.Integer(0)
        eqs.append(lhs - sum(mu[l] * p(k, l) ** 3 * (X[k] - X[l]) for l in range(4) if l != k))
    eqs.append(sp.expand(yeq(1, Y4)))
    eqs.append(sp.expand(yeq(2, Y4)))
    for (a, b) in PAIRS:
        eqs.append(p(a, b) ** 2 * (X[a] - X[b]) * (U[a] - U[b]) - 1)
    gens = [X2, X3, U1, U2, U3] + list(ps)
    return gens, eqs, Y4


if __name__ == '__main__':
    import msio
    kind = sys.argv[1]
    mu = [int(v) for v in sys.argv[2:6]]
    char = int(sys.argv[6])
    out = sys.argv[7]
    gens, eqs, Y4 = kc_system(mu)
    if kind == 'full':
        msio.write_input(out, gens, eqs, char)
        print(out, len(gens), 'vars', len(eqs), 'eqs')
    elif kind == 'square':
        sq = eqs[:5] + eqs[6:]           # drop the Y-equation of body 3
        polys = []
        for e in sq:
            Pp = sp.Poly(sp.expand(e), *gens)
            den = sp.ilcm(*[sp.fraction(sp.Rational(c))[1] for c in Pp.coeffs()])
            Pp = sp.Poly(sp.expand(Pp.as_expr() * den), *gens)
            polys.append(str(Pp.as_expr()).replace('**', '^'))
        with open(out, 'w') as f:
            f.write('Q[' + ','.join(str(g) for g in gens) + ']\n{' + ',\n'.join(polys) + '}\n')
        print(out, len(gens), 'vars', len(polys), 'polys')
