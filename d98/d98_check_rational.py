#!/usr/bin/env python3
"""Independent checker for the diagram-98 certificate, in exact rational arithmetic (Python standard library only).

It does not read the Arb certificate's enclosures. From the masses alone it
  1. rebuilds the shape polynomials of Lemma B by independent code:
       - the collinear quintics Q_s(t - 1) by exact evaluation of x^2 (1+x)^2 [x (F_1 - F_2) - (F_2 - F_3)] at six
         points and interpolation, checked at a seventh point (F_k = sum_l mu_l s_kl z_kl^-2 with z = (0, -1, -1-x));
       - the Lagrange quartics in Q(sqrt(-3)) (om = (-1 + sqrt(-3))/2), and t^2 - t + 1;
  2. encloses every root: approximate roots (Durand-Kerner in floats), refined by exact Newton steps on a dyadic grid,
     then a disk D(t~, r) is certified to contain exactly one root by Rouche's theorem:
         |c_0| + sum_{k>=2} |c_k| r^k < |c_1| r,   c_k = p^(k)(t~)/k!   (p(t~ + h) = sum c_k h^k),
     comparing p(t~ + h) with c_1 h on |h| = r; the disks of one polynomial are pairwise disjoint and their number equals
     the degree, so they contain all its roots;
  3. bounds |l_j| on each disk (l_1 = mu_2 + mu_3 t, l_2 = l_1 - M, l_3 = l_1 - M t, linear in t), checks l_j != 0, and
     bounds alpha_j = mu_j |l_j|^(-1/2) and rho = alpha_3 / (alpha_1 + alpha_2 + alpha_3) by rationals;
  4. checks min rho_A * min rho_B > 1/2 exactly (the dominant-term criterion of DERIVATION.md, Theorem 1 step 4).
Square roots of rationals are bounded by integer square roots at scale 2^-SCALE. Exit code 0 iff all checks pass.
Usage: d98_check_rational.py muA1 muA2 muA3 muB1 muB2 muB3
"""
import sys, cmath
from fractions import Fraction as Fr
from math import isqrt

SCALE = 160            # bits for the square-root bounds
GRID = 2 ** 220        # dyadic grid for the refined roots
RAD = Fr(1, 2 ** 120)  # Rouche radius


# ---------- exact complex rationals as pairs (re, im) ------------------------------------------------------------
def cadd(a, b): return (a[0] + b[0], a[1] + b[1])
def csub(a, b): return (a[0] - b[0], a[1] - b[1])
def cmul(a, b): return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def cabs2(a): return a[0] * a[0] + a[1] * a[1]
def cdiv(a, b):
    d = cabs2(b)
    n = cmul(a, (b[0], -b[1]))
    return (n[0] / d, n[1] / d)


def sqrt_up(x):
    """Rational upper bound of sqrt(x), x >= 0 rational."""
    x = Fr(x)
    if x == 0:
        return Fr(0)
    N = x.numerator * (2 ** (2 * SCALE))
    D = x.denominator
    s = isqrt(N // D)            # floor(sqrt(floor(N/D)))
    v = Fr(s + 1, 2 ** SCALE)
    assert v * v >= x
    return v


def sqrt_low(x):
    x = Fr(x)
    if x <= 0:
        return Fr(0)
    N = x.numerator * (2 ** (2 * SCALE))
    D = x.denominator
    s = isqrt(N // D)
    v = Fr(s, 2 ** SCALE)
    assert v * v <= x
    return v


def cabs_up(a): return sqrt_up(cabs2(a))
def cabs_low(a): return sqrt_low(cabs2(a))


# ---------- polynomials with rational / complex-rational coefficients, lowest degree first -----------------------
def peval_c(p, t):
    """p real-rational coefficients, t complex rational."""
    r = (Fr(0), Fr(0))
    for c in reversed(p):
        r = cadd(cmul(r, t), (Fr(c), Fr(0)))
    return r


def taylor_c(p, t):
    """Coefficients c_k of p(t + h) = sum c_k h^k (exact), by repeated synthetic division."""
    q = [(Fr(c), Fr(0)) for c in p]
    out = []
    while q:
        # divide q by (h - t): remainder q(t)
        n = len(q)
        b = [None] * n
        b[n - 1] = q[n - 1]
        for i in range(n - 2, -1, -1):
            b[i] = cadd(q[i], cmul(b[i + 1], t))
        out.append(b[0])
        q = b[1:]
    return out


def interpolate(xs, ys):
    """Lagrange interpolation over Q, returns coefficients lowest-first."""
    n = len(xs)
    coef = [Fr(0)] * n
    for i in range(n):
        basis = [Fr(1)]
        den = Fr(1)
        for j in range(n):
            if j == i:
                continue
            basis = [Fr(0)] + basis
            for k in range(len(basis) - 1):
                basis[k] -= xs[j] * basis[k + 1]
            den *= xs[i] - xs[j]
        for k in range(n):
            coef[k] += ys[i] * basis[k] / den
    return coef


# ---------- the shape polynomials (independent construction) ------------------------------------------------------
def collinear_value(mu, s, x):
    m = [Fr(v) for v in mu]
    z = [Fr(0), Fr(-1), Fr(-1) - x]            # z_12 = 1, z_23 = x, z_13 = 1 + x
    S = {(0, 1): s[0], (0, 2): s[1], (1, 2): s[2]}
    def sg(k, l):
        return S[(k, l)] if k < l else -S[(l, k)]
    F = [sum(m[l] * sg(k, l) / (z[k] - z[l]) ** 2 for l in range(3) if l != k) for k in range(3)]
    return x * x * (1 + x) ** 2 * (x * (F[0] - F[1]) - (F[1] - F[2]))


def collinear_poly_t(mu, s):
    xs = [Fr(k) for k in range(1, 7)]
    ys = [collinear_value(mu, s, x) for x in xs]
    px = interpolate(xs, ys)                 # degree <= 5 in x
    assert collinear_value(mu, s, Fr(11, 3)) == sum(c * Fr(11, 3) ** i for i, c in enumerate(px)), 'interpolation'
    # substitute x = t - 1
    pt = [Fr(0)] * len(px)
    for i, c in enumerate(px):
        # c (t - 1)^i
        binom = [Fr(1)]
        for _ in range(i):
            nb = [Fr(0)] * (len(binom) + 1)
            for k, v in enumerate(binom):
                nb[k + 1] += v
                nb[k] -= v
            binom = nb
        for k, v in enumerate(binom):
            pt[k] += c * v
    while pt and pt[-1] == 0:
        pt.pop()
    return pt


# Q(sqrt(-3)) as pairs (a, b) = a + b sqrt(-3)
def qmul(x, y): return (x[0] * y[0] - 3 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])
def qadd(x, y): return (x[0] + y[0], x[1] + y[1])
def qneg(x): return (-x[0], -x[1])
def qconj(x): return (x[0], -x[1])
OMEGA = (Fr(-1, 2), Fr(1, 2))
def qom(k):
    r = (Fr(1), Fr(0))
    for _ in range(k % 3):
        r = qmul(r, OMEGA)
    return r


def lagrange_quartic(b, c):
    B = qadd(qadd((Fr(1), Fr(0)), qom(b)), qneg(qom(c)))
    C = qom(b)
    p1 = [C, qneg(B), (Fr(1), Fr(0))]
    p2 = [qconj(C), qneg(qconj(B)), (Fr(1), Fr(0))]
    r = [(Fr(0), Fr(0))] * 5
    for i, u in enumerate(p1):
        for j, v in enumerate(p2):
            r[i + j] = qadd(r[i + j], qmul(u, v))
    assert all(v[1] == 0 for v in r)
    return [v[0] for v in r]


def shape_polys(mu):
    out = [('L_eq', [Fr(1), Fr(-1), Fr(1)])]
    for b, c in [(0, 1), (1, 0), (1, 1)]:
        out.append(('L%d%d' % (b, c), lagrange_quartic(b, c)))
    for s in [(1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)]:
        out.append(('C%+d%+d%+d' % s, collinear_poly_t(mu, s)))
    return out


# ---------- root enclosure ----------------------------------------------------------------------------------------
def approx_roots(p):
    """Durand-Kerner in floating point (only to get starting points)."""
    n = len(p) - 1
    a = [float(c) / float(p[-1]) for c in p]
    z = [complex(0.4, 0.9) ** k for k in range(n)]
    for _ in range(2000):
        nz = []
        for i in range(n):
            num = sum(a[k] * z[i] ** k for k in range(n + 1))
            den = 1
            for j in range(n):
                if j != i:
                    den *= z[i] - z[j]
            nz.append(z[i] - num / den)
        if max(abs(nz[i] - z[i]) for i in range(n)) < 1e-15:
            z = nz
            break
        z = nz
    return z


def to_grid(x):
    return Fr(round(x * GRID), GRID)


def refine(p, t0, steps=8):
    dp = [i * c for i, c in enumerate(p)][1:]
    t = (Fr(t0.real).limit_denominator(10 ** 18), Fr(t0.imag).limit_denominator(10 ** 18))
    for _ in range(steps):
        t = csub(t, cdiv(peval_c(p, t), peval_c(dp, t)))
        t = (to_grid(t[0]), to_grid(t[1]))
    return t


def rouche_one_root(p, t, r):
    c = taylor_c(p, t)
    lhs = cabs_up(c[0]) + sum(cabs_up(c[k]) * r ** k for k in range(2, len(c)))
    rhs = cabs_low(c[1]) * r
    return lhs < rhs


def enclose(p):
    n = len(p) - 1
    disks = [refine(p, t0) for t0 in approx_roots(p)]
    for t in disks:
        assert rouche_one_root(p, t, RAD), 'Rouche test failed'
    for i in range(n):
        for j in range(i + 1, n):
            assert cabs2(csub(disks[i], disks[j])) > (2 * RAD) ** 2, 'disks overlap'
    return disks


# ---------- the dominant-term bound -------------------------------------------------------------------------------
def rho_low(mu, t, r):
    m = [Fr(v) for v in mu]
    M = sum(m)
    l1 = cadd((m[1], Fr(0)), cmul((m[2], Fr(0)), t))
    ls = [l1, csub(l1, (M, Fr(0))), csub(l1, cmul((M, Fr(0)), t))]
    coef = [m[2], m[2], m[0] + m[1]]                 # |d l_j / d t|
    lo = [cabs_low(ls[j]) - coef[j] * r for j in range(3)]
    up = [cabs_up(ls[j]) + coef[j] * r for j in range(3)]
    assert all(v > 0 for v in lo), 'l_j may vanish'
    # alpha_j = m_j / sqrt|l_j|
    a_up = [m[j] / sqrt_low(lo[j]) for j in range(3)]
    a_lo = [m[j] / sqrt_up(up[j]) for j in range(3)]
    return a_lo[2] / (a_up[0] + a_up[1] + a_lo[2])


def triangle(mu):
    recs = []
    total = 0
    for name, p in shape_polys(mu):
        disks = enclose(p)
        total += len(disks)
        for t in disks:
            recs.append((name, t, rho_low(mu, t, RAD)))
    return recs, total


def main():
    muA = [Fr(v) for v in sys.argv[1:4]]
    muB = [Fr(v) for v in sys.argv[4:7]]
    RA, nA = triangle(muA)
    RB, nB = triangle(muB)
    rA = min(r for _, _, r in RA)
    rB = min(r for _, _, r in RB)
    ok = rA * rB > Fr(1, 2)
    print('masses A %s B %s' % ([str(v) for v in muA], [str(v) for v in muB]))
    print('roots certified (Rouche, radius 2^-120): A %d, B %d' % (nA, nB))
    print('min rho_A >= %.10f, min rho_B >= %.10f (exact rationals); rho_A rho_B > 1/2: %s' % (
        float(rA), float(rB), ok))
    worst = min(RA, key=lambda x: x[2])
    print('worst A root: %s  t ~ %.6f %+.6fi' % (worst[0], float(worst[1][0]), float(worst[1][1])))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
