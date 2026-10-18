# Independent recomputation of the diagram-98 dominant-term bound (non-rigorous floating check, mpmath 60 digits).
# Shape polynomials re-derived here:  collinear: x^2(1+x)^2 [x(F1-F2) - (F2-F3)], x = t-1, z = (0,-1,-1-x) up to translation;
# Lagrange: t^2 - (1 + w^b - w^c) t + w^b for (b,c) in (Z/3)^2 (all nine classes, no pairing into quartics).
import sys, itertools, mpmath as mp
mp.mp.dps = 60
def shapes(mu):
    m1, m2, m3 = [mp.mpf(v) for v in mu]
    w = mp.exp(2j * mp.pi / 3)
    roots = []
    for b in range(3):
        for c in range(3):
            B = 1 + w**b - w**c; C = w**b
            d = mp.sqrt(B * B - 4 * C)
            roots += [('L%d%d' % (b, c), (B + d) / 2), ('L%d%d' % (b, c), (B - d) / 2)]
    for s in [(1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)]:
        s12, s13, s23 = s
        # polynomial in x via sampling + exact-ish interpolation: build coefficients symbolically
        # A = x^2(1+x)^2(F1-F2), B = x^2(1+x)^2(F2-F3)
        def poly_mul(p, q):
            r = [0] * (len(p) + len(q) - 1)
            for i, a in enumerate(p):
                for j, bb in enumerate(q): r[i + j] += a * bb
            return r
        X2 = [0, 0, 1]; Q2 = [1, 2, 1]; XQ = poly_mul(X2, Q2)
        def comb(terms):
            n = max(len(t) for _, t in terms); r = [mp.mpf(0)] * n
            for k, t in terms:
                for i, v in enumerate(t): r[i] += k * v
            return r
        A = comb([((m1 + m2) * s12, XQ), (m3 * s13, X2), (-m3 * s23, Q2)])
        Bp = comb([(-m1 * s12, XQ), (m1 * s13, X2), ((m2 + m3) * s23, Q2)])
        xA = [mp.mpf(0)] + A
        P = [xA[i] - (Bp[i] if i < len(Bp) else 0) for i in range(len(xA))]
        # check against direct evaluation of the definition at a test point
        x0 = mp.mpf('0.37') + mp.mpf('0.21') * 1j
        z = [0, -1, -1 - x0]
        S = {(0, 1): s12, (0, 2): s13, (1, 2): s23}
        sg = lambda k, l: S[(k, l)] if k < l else -S[(l, k)]
        M = [m1, m2, m3]
        F = [sum(M[l] * sg(k, l) / (z[k] - z[l])**2 for l in range(3) if l != k) for k in range(3)]
        direct = x0**2 * (1 + x0)**2 * (x0 * (F[0] - F[1]) - (F[1] - F[2]))
        val = sum(c * x0**i for i, c in enumerate(P))
        assert abs(val - direct) < mp.mpf(10)**-40, 'collinear poly mismatch'
        for r in mp.polyroots(list(reversed(P)), maxsteps=500, extraprec=200):
            roots.append(('C%+d%+d%+d' % s, r + 1))
    return roots
def rho(mu, t):
    m1, m2, m3 = [mp.mpf(v) for v in mu]; M = m1 + m2 + m3
    l1 = m2 + m3 * t; l = [l1, l1 - M, l1 - M * t]
    al = [mp.mpf(mu[j]) / mp.sqrt(abs(l[j])) for j in range(3)]
    return al[2] / sum(al), l
mu = [int(v) for v in sys.argv[1:4]]
R = shapes(mu)
print('number of roots (Lagrange counted per class, 18; collinear 20):', len(R))
vals = sorted(((rho(mu, t)[0], nm, t) for nm, t in R), key=lambda v: v[0])
for v, nm, t in vals[:4]:
    print('  rho = %s  at %s  t = %s' % (mp.nstr(v, 12), nm, mp.nstr(t, 10)))
print('min |l_j| over roots:', mp.nstr(min(min(abs(x) for x in rho(mu, t)[1]) for _, t in R), 6))
