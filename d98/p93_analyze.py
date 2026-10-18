#!/usr/bin/env python3
"""Diagram 93: the generic mass condition P_93(m_B) (masses of the fully circled triangle) factors as
M^k * L1 L2 L3 L4 (L5 L5')^2 L6 L7 L8 (Albouy-Kaloshin 2012, Sec. 8.2.1). This script reads the factors computed by
p93_resultants.sing (certificates/p93_factors.txt), checks (exactly, in integers) that none vanishes at a given
mass triple, and maps the positive zero set of each factor on the mass simplex (sign changes on a grid; numerical).
Usage: p93_analyze.py FACTORS.txt [m1 m2 m3] [GRID]"""
import sys, re
import numpy as np
import sympy as sp

m1, m2, m3 = sp.symbols('m1 m2 m3')


def load(path):
    out = []
    for line in open(path):
        name, deg, mult, poly = [s.strip() for s in line.split('|')]
        out.append((name, int(deg.split()[1]), int(mult.split()[1]), sp.Poly(sp.sympify(poly), m1, m2, m3)))
    return out


def main():
    F = load(sys.argv[1])
    pt = [int(v) for v in sys.argv[2:5]] if len(sys.argv) > 4 else [1, 2, 7]
    grid = int(sys.argv[5]) if len(sys.argv) > 5 else 600
    print('exact values at m =', pt)
    allnz = True
    for name, d, mult, P in F:
        v = P.eval({m1: pt[0], m2: pt[1], m3: pt[2]})
        allnz &= (v != 0)
        sgn_terms = sum(1 for c in P.coeffs() if c < 0)
        print('  %-5s deg %2d mult %d  terms %3d  negative coeffs %3d  value %s' % (
            name, d, mult, len(P.coeffs()), sgn_terms, ('%.6e' % float(v)) if v != 0 else '0'))
    print('P_93 nonzero at', pt, ':', allnz)
    # positive zero sets on the simplex m1 + m2 + m3 = 1 (numerical sign scan)
    s = np.linspace(0, 1, grid + 1)[1:-1]
    A, B = np.meshgrid(s, s, indexing='ij')
    C = 1 - A - B
    mask = C > 1e-9
    print('positive zero sets (sign changes on a %d-grid of the simplex):' % grid)
    seen = set()
    for name, d, mult, P in F:
        key = str(P.as_expr())
        if key in seen or d < 2:
            continue
        seen.add(key)
        f = sp.lambdify((m1, m2, m3), P.as_expr(), 'numpy')
        V = np.where(mask, f(A, B, np.where(mask, C, 0.5)), np.nan)
        sg = np.sign(V)
        ch = 0
        ch += np.nansum((sg[1:, :] * sg[:-1, :]) < 0)
        ch += np.nansum((sg[:, 1:] * sg[:, :-1]) < 0)
        npos = np.nansum(sg > 0); nneg = np.nansum(sg < 0)
        print('  %-5s deg %2d: grid points +%d / -%d, sign changes %d %s' % (
            name, d, npos, nneg, ch, '-> positive zeros' if ch > 0 else ('(L5 vanishes only at equal masses)' if d == 2 else '-> none found')))


if __name__ == '__main__':
    main()
