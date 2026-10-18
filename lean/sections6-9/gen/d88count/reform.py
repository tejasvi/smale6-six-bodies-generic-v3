#!/usr/bin/env python3
"""Reformulations of S12 (Lemma 6.19(b)) for size experiments with msolve (not part of any proof).
Variant 'yelim': Y eliminated through the distance equations, Y_kl = 1/(p_kl^2 X_kl): unknowns X2, X3, p12..p34 and a
saturation variable t with t * prod(p_kl) * prod(X_k - X_l) = 1.
Usage: reform.py VARIANT OUT.ms"""
import sys
import sympy as sp

mu = [1, 2, 3, 30]
M = sum(mu)
X2, X3, t = sp.symbols('X2 X3 t')
P = {}
names = []
for k in range(4):
    for l in range(k + 1, 4):
        P[(k, l)] = sp.Symbol('p%d%d' % (k + 1, l + 1))
        names.append('p%d%d' % (k + 1, l + 1))
def p(k, l):
    return P[(min(k, l), max(k, l))]
X = [X2 + 1, X2, X3, -(mu[0] * (X2 + 1) + mu[1] * X2 + mu[2] * X3) / sp.Integer(mu[3])]
def a(k, l):
    return p(k, l) ** 2 * (X[k] - X[l])
eqs = []
for k in range(3):
    e = X[k] - sum(mu[l] * p(k, l) ** 3 * (X[k] - X[l]) for l in range(4) if l != k)
    eqs.append(sp.expand(e * mu[3]))
for (k, l, m) in [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]:
    e = a(l, m) * a(m, k) + a(k, l) * a(m, k) + a(k, l) * a(l, m)
    eqs.append(sp.expand(e * mu[3] ** 2))
for k in range(4):
    others = [l for l in range(4) if l != k]
    e = 0
    for l in others:
        prod = 1
        for l2 in others:
            if l2 != l:
                prod *= a(k, l2)
        e += mu[l] * (1 - M * p(k, l) ** 3) * prod
    eqs.append(sp.expand(e * mu[3] ** 2))
sat = t
for v in P.values():
    sat *= v
for k in range(4):
    for l in range(k + 1, 4):
        sat *= (X[k] - X[l])
eqs.append(sp.expand(sat * mu[3] ** 3 - mu[3] ** 3))
vars_ = [X2, X3] + [P[k] for k in sorted(P)] + [t]
lines = []
for e in eqs:
    poly = sp.Poly(e, *vars_)
    terms = []
    for mon, c in poly.terms():
        c = sp.Integer(c)
        assert c.q == 1, c
        mon_s = '*'.join(('%s^%d' % (v, d) if d > 1 else str(v)) for v, d in zip(vars_, mon) if d)
        terms.append('%d%s' % (int(c), ('*' + mon_s) if mon_s else ''))
    lines.append('+'.join(terms).replace('+-', '-'))
open(sys.argv[2], 'w').write(','.join(str(v) for v in vars_) + '\n65521\n' + ',\n'.join(lines) + '\n')
print(len(eqs), 'equations,', sum(len(l.split('+')) for l in lines), 'terms (approx)')
