#!/usr/bin/env python3
"""For Lemma 6.19(b): compare the msolve inputs with the systems of Section 6.7 written from the paper, and print the
cofactors e_j with  msolve_j - u_j * paper_j = e_j * (30*i4 - 1)  (S12; i4 stands for 1/mu_4) as Lean expressions in
v 0, ..., v 10 and i4, and check  msolve_j = u_j * paper_j  for KC'.  Usage: br_syscoef.py S12.ms KC.ms"""
import sys
import sympy as sp
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from br_mkinputs import parse_ms

mu = [1, 2, 3, 30]
v = sp.symbols('v0:11')
i4 = sp.Symbol('i4')
Pd = {(0, 1): v[5], (0, 2): v[6], (0, 3): v[7], (1, 2): v[8], (1, 3): v[9], (2, 3): v[10]}
def P(a, b):
    return Pd[(min(a, b), max(a, b))]
def body(Z, k):
    return Z[k] - sum(mu[l] * P(k, l) ** 3 * (Z[k] - Z[l]) for l in range(4) if l != k)
pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def topoly(names, poly):
    e = 0
    for c, ex in poly:
        t = sp.Integer(c)
        for k, d in enumerate(ex):
            t *= v[k] ** d
        e += t
    return sp.expand(e)

def lean(e):
    s = str(sp.expand(e))
    for k in range(10, -1, -1):
        s = s.replace('v%d' % k, '(v %d)' % k)
    return s.replace('**', '^')

names, s12 = parse_ms(sys.argv[1])
X = [v[0] + 1, v[0], v[1], -i4 * (mu[0] * (v[0] + 1) + mu[1] * v[0] + mu[2] * v[1])]
Y = [v[2], v[3], v[4], -i4 * (mu[0] * v[2] + mu[1] * v[3] + mu[2] * v[4])]
rows = [body(X, 0), body(X, 1), body(X, 2), body(Y, 0), body(Y, 1), body(Y, 2)] + \
       [P(a, b) ** 2 * (X[a] - X[b]) * (Y[a] - Y[b]) - 1 for (a, b) in pairs]
u = [1] * 6 + [1, 1, 900, 1, 900, 900]
print('-- S12 cofactors')
for j in range(12):
    D = sp.expand(topoly(names, s12[j]) - u[j] * rows[j])
    q, r = sp.div(sp.Poly(D, i4), sp.Poly(30 * i4 - 1, i4))
    assert r.is_zero, (j, r)
    print(j, lean(q.as_expr()))
names, kc = parse_ms(sys.argv[2])
Xk = [1, v[0], v[1], 0]
U = [v[2], v[3], v[4], 0]
Y4 = -U[0] + sum(mu[l] * P(0, l) ** 3 * (U[0] - U[l]) for l in range(4) if l != 0)
def yeq(k):
    return (U[k] + Y4) - sum(mu[l] * P(k, l) ** 3 * (U[k] - U[l]) for l in range(4) if l != k)
centre = sum(mu[l] * P(3, l) ** 3 * (Xk[3] - Xk[l]) for l in range(4) if l != 3)
rowsk = [body(Xk, 0), body(Xk, 1), body(Xk, 2), centre, yeq(1), yeq(2)] + \
        [P(a, b) ** 2 * (Xk[a] - Xk[b]) * (U[a] - U[b]) - 1 for (a, b) in pairs]
uk = [1, 1, 1, -1, 1, 1] + [1] * 6
print('-- KC check')
for j in range(12):
    D = sp.expand(topoly(names, kc[j]) - uk[j] * rowsk[j])
    assert D == 0, (j, D)
print('KC rows equal (u = 1 except the centre equation, u = -1)')
