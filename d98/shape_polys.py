#!/usr/bin/env python3
"""Exact shape polynomials of the normalized complex three-body CC system (Lemma B of DERIVATION.md).

For masses mu = (mu_1, mu_2, mu_3) (rationals) and the slice z_12 = 1, the z-shape tau = z_13 of every solution is a
root of one of the following integer polynomials in t:
  Lagrange (mass independent):  t^2 - t + 1  and the three quartics N_bc(t) = (t^2 - B t + C)(t^2 - conj(B) t + conj(C)),
                                B = 1 + om^b - om^c, C = om^b, for (b, c) in {(0,1), (1,0), (1,1)} (their conjugate
                                classes (0,2), (2,0), (2,2) give the same quartics; (0,0), (1,2), (2,1) give t^2 - t + 1);
  collinear: Q_s(t - 1) for the four sign classes s = (s12, s13, s23), (1,-1,1) being the cyclic one, where
             Q_s(x) = x^2 (1+x)^2 [ x (F_1 - F_2) - (F_2 - F_3) ],  F_k = sum_{l != k} mu_l s_kl z_kl^{-2},
             z_12 = 1, z_23 = x, z_13 = 1 + x  (denominators cleared to make the coefficients integers).
Arithmetic in Z[om] is done by hand (om^2 = -1 - om), so the module needs only the standard library.
Usage: shape_polys.py mu1 mu2 mu3      (prints the polynomials, highest degree first)
"""
import sys
from fractions import Fraction
from math import lcm


# ---- Z[om] arithmetic: a + b om, om^2 = -1 - om -------------------------------------------------------------
def zo_mul(x, y):
    a, b = x
    c, d = y
    # (a + b om)(c + d om) = ac + (ad + bc) om + bd om^2 = (ac - bd) + (ad + bc - bd) om
    return (a * c - b * d, a * d + b * c - b * d)


def zo_add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def zo_neg(x):
    return (-x[0], -x[1])


def zo_conj(x):
    # conj(om) = om^2 = -1 - om:  a + b om -> a + b(-1 - om) = (a - b) - b om
    a, b = x
    return (a - b, -b)


def zo_pow_om(k):
    k %= 3
    return [(1, 0), (0, 1), (-1, -1)][k]


def poly_mul(p, q, mul, add, zero):
    """Polynomials as lists, lowest degree first."""
    r = [zero] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] = add(r[i + j], mul(a, b))
    return r


def lagrange_quartic(b, c):
    B = zo_add(zo_add((1, 0), zo_pow_om(b)), zo_neg(zo_pow_om(c)))
    C = zo_pow_om(b)
    q1 = [C, zo_neg(B), (1, 0)]
    q2 = [zo_conj(C), zo_neg(zo_conj(B)), (1, 0)]
    prod = poly_mul(q1, q2, zo_mul, zo_add, (0, 0))
    assert all(v[1] == 0 for v in prod), 'quartic not rational'
    return [v[0] for v in prod]          # lowest degree first, integers


def lagrange_polys():
    """[(name, coeffs lowest-first)]: t^2 - t + 1 and the three Lagrange quartics."""
    out = [('L_eq', [1, -1, 1])]
    for b, c in [(0, 1), (1, 0), (1, 1)]:
        out.append(('L%d%d' % (b, c), lagrange_quartic(b, c)))
    # sanity: the conjugate classes give the same quartic, (0,0),(1,2),(2,1) give t^2 - t + 1 (as quadratics over Z[om])
    for (b, c), (b2, c2) in [((0, 1), (0, 2)), ((1, 0), (2, 0)), ((1, 1), (2, 2))]:
        assert lagrange_quartic(b, c) == lagrange_quartic(b2, c2)
    return out


def collinear_poly_x(mu, s):
    """Q_s(x) as a list lowest-first with Fraction coefficients (exact)."""
    m1, m2, m3 = [Fraction(v) for v in mu]
    s12, s13, s23 = s
    X2 = [0, 0, 1]
    Q2 = [1, 2, 1]
    XQ = poly_mul(X2, Q2, lambda a, b: a * b, lambda a, b: a + b, 0)
    def comb(*terms):
        n = max(len(t) for _, t in terms)
        r = [Fraction(0)] * n
        for k, t in terms:
            for i, v in enumerate(t):
                r[i] += k * v
        return r
    A = comb(((m1 + m2) * s12, XQ), (m3 * s13, X2), (-m3 * s23, Q2))        # x^2(1+x)^2 (F_1 - F_2)
    B = comb((-m1 * s12, XQ), (m1 * s13, X2), ((m2 + m3) * s23, Q2))        # x^2(1+x)^2 (F_2 - F_3)
    xA = [Fraction(0)] + A
    n = max(len(xA), len(B))
    P = [(xA[i] if i < len(xA) else 0) - (B[i] if i < len(B) else 0) for i in range(n)]
    while P and P[-1] == 0:
        P.pop()
    return P


def shift(p, a):
    """p(t + a) for p lowest-first (Taylor shift), exact."""
    n = len(p)
    out = [Fraction(0)] * n
    # Horner: p(t + a) = (...((c_n)(t + a) + c_{n-1})(t + a) + ...)
    for c in reversed(p):
        # out = out * (t + a) + c
        new = [Fraction(0)] * n
        for i in range(n):
            if out[i] != 0:
                if i + 1 < n:
                    new[i + 1] += out[i]
                new[i] += a * out[i]
        new[0] += c
        out = new
    return out


def to_int(p):
    p = [Fraction(v) for v in p]
    L = 1
    for v in p:
        L = lcm(L, v.denominator)
    q = [int(v * L) for v in p]
    from math import gcd
    g = 0
    for v in q:
        g = gcd(g, abs(v))
    q = [v // g for v in q]
    if q[-1] < 0:
        q = [-v for v in q]
    return q


SIGMAS = [(1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)]


def all_shape_polys(mu):
    """[(name, integer coeffs lowest-first)] whose roots (in t = tau) contain every z-shape at masses mu."""
    out = list(lagrange_polys())
    for s in SIGMAS:
        Px = collinear_poly_x(mu, s)
        Pt = shift(Px, Fraction(-1))      # Q_s(t - 1)
        out.append(('C%+d%+d%+d' % s, to_int(Pt)))
    return out


def fmt(p):
    terms = []
    for i in range(len(p) - 1, -1, -1):
        if p[i] != 0:
            terms.append('%+d*t^%d' % (p[i], i))
    return ' '.join(terms)


if __name__ == '__main__':
    mu = [Fraction(v) for v in sys.argv[1:4]]
    for name, p in all_shape_polys(mu):
        print(name, 'deg', len(p) - 1, ':', fmt(p))
