"""Lemma 6.9 check: the eliminants stored for (1,2,7), (1,2,8), (2,3,11) have the square-free part of S_mu.

Usage: python3 -I lemma69_sqfree.py <elim_1_2_7.txt> <elim_1_2_8.txt> <elim_2_3_11.txt>

S_mu is built here from the definitions of Section 6.4 of the paper (not from the programs that produced the
eliminants): S_mu(t) = (t^2 - t + 1) N01 N10 N11 prod_sigma Q_sigma(t - 1). Each input file holds the line
g=<eliminant in t>, written by Singular. The script prints, for each mass vector, the degrees of S_mu, of its
square-free part and of g, and whether the square-free parts agree up to a nonzero constant.
"""
import re, sys
import sympy as sp

t, x = sp.symbols('t x')
N01 = t**4 - 5*t**3 + 9*t**2 - 5*t + 1
N10 = t**4 + t**3 - 2*t + 1
N11 = t**4 - 2*t**3 + t + 1


def S(mu):
    m1, m2, m3 = [sp.Integer(v) for v in mu]
    Q = sp.Integer(1)
    for s12, s13, s23 in ((1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)):
        F1 = m2*s12 + m3*s13/(1 + x)**2
        F2 = -m1*s12 + m3*s23/x**2
        F3 = -m1*s13/(1 + x)**2 - m2*s23/x**2
        q = sp.cancel(x**2*(1 + x)**2*(x*(F1 - F2) - (F2 - F3)))
        Q *= q.subs(x, t - 1)
    return sp.Poly(sp.expand((t**2 - t + 1)*N01*N10*N11*Q), t)


def sqfree(p):
    return sp.Poly(sp.sqf_part(p.as_expr()), t)


for path in sys.argv[1:]:
    mu = tuple(int(v) for v in re.findall(r'elim_(\d+)_(\d+)_(\d+)', path)[0])
    g = sp.Poly(sp.sympify(re.search(r'^g=(.*)$', open(path).read(), re.M).group(1)), t)
    s = S(mu)
    a, b = sqfree(s), sqfree(g)
    q, r = sp.div(a.monic(), b.monic())
    print(f'mu={mu}: deg S_mu {s.degree()}, lead {s.LC()}, deg sqfree(S_mu) {a.degree()}, deg g {g.degree()}, '
          f'deg sqfree(g) {b.degree()}, sqfree parts equal up to a constant: {r.is_zero and q.degree() == 0}')
