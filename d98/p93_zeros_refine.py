#!/usr/bin/env python3
"""Refine the isolated positive zeros of the P_93 factors (nonnegative forms) at high precision: Newton on the
gradient system dL/dm1 = dL/dm2 = 0 at m3 = 1 (mpmath, 80 digits), then report L at the critical point relative to
the size of L nearby. A genuine zero has L ~ 1e-70; a positive minimum stays O(1) relative. Numerical, not a proof.
Usage: p93_zeros_refine.py FACTORS.txt"""
import sys
import mpmath as mp
import sympy as sp

mp.mp.dps = 80
m1, m2, m3 = sp.symbols('m1 m2 m3')
START = {'L01': [(1.211156, 1.470853), (1.470853, 1.211156)], 'Cppp': [(1.104245, 1.128841), (1.128841, 1.104245)]}


def main():
    seen = {}
    for line in open(sys.argv[1]):
        name, deg, mult, poly = [s.strip() for s in line.split('|')]
        if int(deg.split()[1]) < 13 or poly in seen.values():
            continue
        seen[name] = poly
    for name, poly in seen.items():
        P = sp.sympify(poly).subs(m3, 1)
        gx, gy = sp.diff(P, m1), sp.diff(P, m2)
        f = sp.lambdify((m1, m2), P, 'mpmath')
        G = sp.lambdify((m1, m2), [gx, gy], 'mpmath')
        H = sp.lambdify((m1, m2), [[sp.diff(gx, m1), sp.diff(gx, m2)], [sp.diff(gy, m1), sp.diff(gy, m2)]], 'mpmath')
        # try all permutations of the candidate ratios, normalized to m3 = 1
        base = [(1.211156, 1.470853), (1.104245, 1.128841)]
        cands = set()
        for a, b in base:
            trip = [1.0, a, b]
            import itertools
            for p in itertools.permutations(trip):
                cands.add((p[0] / p[2], p[1] / p[2]))
        out = []
        for x0, y0 in sorted(cands):
            x, y = mp.mpf(x0), mp.mpf(y0)
            ok = True
            for it in range(60):
                g = G(x, y)
                h = H(x, y)
                try:
                    d = mp.lu_solve(mp.matrix(h), -mp.matrix(g))
                except ZeroDivisionError:
                    ok = False
                    break
                x, y = x + d[0], y + d[1]
                if mp.norm(d) < mp.mpf(10) ** -70:
                    break
            if not ok or x <= 0 or y <= 0:
                continue
            val = f(x, y)
            scale = f(x * 1.01, y * 0.99)
            if abs(val) < mp.mpf(10) ** -40 * abs(scale):
                out.append((mp.nstr(x, 15), mp.nstr(y, 15), mp.nstr(val, 3), mp.nstr(scale, 3)))
        print('%-5s: genuine positive zeros (m1, m2) at m3 = 1, with L and L nearby:' % name)
        for o in sorted(set(out)):
            print('      ', o)


if __name__ == '__main__':
    main()
