#!/usr/bin/env python3
"""Polynomial systems for the stretched four-body leading system of diagram 88 (and variants).

N_4(mu): normalized complex four-body system in AK form, for masses mu = (mu1..mu4):
    X_k = sum_l mu_l p_kl^3 (X_k - X_l),  Y_k = sum_l mu_l p_kl^3 (Y_k - Y_l),  p_kl^2 (X_k - X_l)(Y_k - Y_l) = 1.
For diagram 88, X = [w]_{-2} (the stretched colour of the w-K4) and Y = [z]_{+2}.
Slice (rotation (X,Y) -> (sX, Y/s)):  X_1 - X_2 = 1.  Centre of mass Sum mu X = Sum mu Y = 0 is implied by the
equations; we use it to eliminate X_4, Y_4 and then drop the 4th X- and Y-equation (implied: Sum_k mu_k (X-eq)_k is
Sum mu X identically).

Usage: k4sys.py full mu1 mu2 mu3 mu4 CHAR OUT.ms
"""
import os
import sys
import sympy as sp

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
PNAMES = ['p12', 'p13', 'p14', 'p23', 'p24', 'p34']


def full_system(mu):
    mu = [sp.Integer(v) for v in mu]
    X2, X3, Y1, Y2, Y3 = sp.symbols('X2 X3 Y1 Y2 Y3')
    ps = sp.symbols(' '.join(PNAMES))
    P = dict(zip(PAIRS, ps))

    def p(a, b):
        return P[(min(a, b), max(a, b))]
    X1 = X2 + 1
    X4 = -(mu[0] * X1 + mu[1] * X2 + mu[2] * X3) / mu[3]
    Y4 = -(mu[0] * Y1 + mu[1] * Y2 + mu[2] * Y3) / mu[3]
    X = [X1, X2, X3, X4]
    Y = [Y1, Y2, Y3, Y4]
    gens = [X2, X3, Y1, Y2, Y3] + list(ps)
    eqs = []
    for k in range(3):
        eqs.append(X[k] - sum(mu[l] * p(k, l) ** 3 * (X[k] - X[l]) for l in range(4) if l != k))
    for k in range(3):
        eqs.append(Y[k] - sum(mu[l] * p(k, l) ** 3 * (Y[k] - Y[l]) for l in range(4) if l != k))
    for (a, b) in PAIRS:
        eqs.append(p(a, b) ** 2 * (X[a] - X[b]) * (Y[a] - Y[b]) - 1)
    return gens, eqs, {'X': X, 'Y': Y, 'p': P}


if __name__ == '__main__':
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import msio
    kind = sys.argv[1]
    mu = [int(v) for v in sys.argv[2:6]]
    char = int(sys.argv[6])
    out = sys.argv[7]
    if kind == 'full':
        gens, eqs, _ = full_system(mu)
    else:
        raise SystemExit('unknown kind')
    msio.write_input(out, gens, eqs, char)
    print(out, len(gens), 'vars', len(eqs), 'eqs')
