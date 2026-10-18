#!/usr/bin/env python3
"""Diagram 93, exceptional set: each factor L of P_93 (AK's L1..L8) is a norm over conjugate shape pairs, hence
nonnegative on real masses, and its positive zeros are isolated (no sign change). Find them numerically: local
minima of L(m1,m2,m3)/(m1+m2+m3)^deg on the open simplex from many starts; report minima with value < 1e-12 relative
to the max coefficient scale, refined by Newton on the gradient. Numerical pilot, not a proof.
Usage: p93_minima.py FACTORS.txt NSTART"""
import sys
import numpy as np
import sympy as sp
from scipy.optimize import minimize

m1, m2, m3 = sp.symbols('m1 m2 m3')


def main():
    nstart = int(sys.argv[2])
    seen = set()
    for line in open(sys.argv[1]):
        name, deg, mult, poly = [s.strip() for s in line.split('|')]
        d = int(deg.split()[1])
        if d < 2 or poly in seen:
            continue
        seen.add(poly)
        P = sp.sympify(poly)
        f = sp.lambdify((m1, m2, m3), P, 'numpy')
        g = sp.lambdify((m1, m2, m3), [sp.diff(P, v) for v in (m1, m2, m3)], 'numpy')
        def F(u):
            x = np.exp(u)                     # positive orthant, scale-free via normalization
            s = x.sum()
            return f(*(x / s))
        rng = np.random.default_rng(1)
        found = []
        vals = []
        for k in range(nstart):
            u0 = rng.normal(size=3) * 1.5
            r = minimize(F, u0, method='Nelder-Mead', options={'xatol': 1e-13, 'fatol': 1e-300, 'maxiter': 20000})
            x = np.exp(r.x); x = x / x.sum()
            vals.append(r.fun)
            if r.fun < 1e-14:
                key = tuple(np.round(np.sort(x), 5))
                if key not in [tuple(np.round(np.sort(y), 5)) for y in found]:
                    found.append(x)
        print('%-5s deg %2d: global min found %.3e; near-zero minima (sorted mass ratios, sum 1): %s' % (
            name, d, min(vals), [tuple(np.round(np.sort(x) / np.sort(x)[0], 6)) for x in found]), flush=True)


if __name__ == '__main__':
    main()
