"""Exact data for the hand-proof computations of Lemmas 6.9 and 6.13 (printed, then pasted into Lean sources).

Usage: python3 -I gen_hand.py
1. The Lagrange quadratics q_bc = t^2 - (1 + w^b - w^c) t + w^b: the cofactors e with LHS - RHS = e (w^2 + w + 1).
2. Taylor coefficient lists (constant term first) at c in {0, 1} of t^2 - t + 1, N01, N10, N11, and at
   c in {0, -1} of C_sigma, D_sigma (mu = (1, 2, 40)), with the bounds sum_{k>=1} |a_k| 10^-k, resp. sum_k.
"""
import sympy as sp

t, w, h, x = sp.symbols('t w h x')
lag = t**2 - t + 1
N01 = t**4 - 5*t**3 + 9*t**2 - 5*t + 1
N10 = t**4 + t**3 - 2*t + 1
N11 = t**4 - 2*t**3 + t + 1
E = w**2 + w + 1


def q(b, c):
    return t**2 - (1 + w**b - w**c)*t + w**b


def cof(lhs, rhs):
    d = sp.expand(lhs - rhs)
    qq, r = sp.div(sp.Poly(d, w), sp.Poly(E, w))
    assert r.is_zero, r
    return sp.factor(qq.as_expr())


print('1. cofactors')
print('q12 - (t-(1+w))^2 :', cof(q(1, 2), (t - (1 + w))**2))
print('lag(1+w) :', cof(lag.subs(t, 1 + w), 0))
print('q21 - (t+w)^2 :', cof(q(2, 1), (t + w)**2))
print('lag(-w) :', cof(lag.subs(t, -w), 0))
print('q01 q02 - N01 :', cof(q(0, 1)*q(0, 2), N01))
print('q10 q20 - N10 :', cof(q(1, 0)*q(2, 0), N10))
print('q11 q22 - N11 :', cof(q(1, 1)*q(2, 2), N11))


def taylor(p, var, c):
    pp = sp.Poly(sp.expand(p.subs(var, c + h)), h)
    return [int(pp.coeff_monomial(h**k)) for k in range(pp.degree() + 1)]


r = sp.Rational(1, 10)
print('2. Taylor lists')
for name, p in [('lag', lag), ('N01', N01), ('N10', N10), ('N11', N11)]:
    for c in (0, 1):
        T = taylor(p, t, c)
        print(name, c, T, 'tail bound', sum(abs(a)*r**k for k, a in enumerate(T) if k > 0))
for s12, s13, s23 in ((1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)):
    C = s13*x**3 - s23*(1 + x)**3
    D = 3*s12*x**3*(1 + x)**2 + s12*x**2*(1 + x)**2 - s13*x**2 - 2*s23*(1 + x)**2
    for c in (0, -1):
        TC = taylor(C, x, c)
        TD = taylor(D, x, c)
        print((s12, s13, s23), c, 'C', TC, 'tail', sum(abs(a)*r**k for k, a in enumerate(TC) if k > 0),
              'D', TD, 'all', sum(abs(a)*r**k for k, a in enumerate(TD)))
