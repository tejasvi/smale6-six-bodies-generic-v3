"""Checks of the hand proof of Lemma 6.13 at mu = (1, 2, 40) (Section 6.5).

Usage: python3 -I p98_heavy_mass.py        (needs sympy and mpmath)

1. Exact bounds. For each Lagrange factor p in {t^2-t+1, N01, N10, N11} and c in {0, 1}: p(c) = 1 and the sum of
   |coefficient| (1/10)^k over the nonconstant terms of p(c+h) is < 1. For each sign pattern sigma, with
   Q_sigma(x) = 40 C_sigma(x) + D_sigma(x) (identity checked), on |x - c| <= 1/10, c in {0, -1}: the bound
   |C_sigma - C_sigma(c)| <= B_C and |D_sigma| <= B_D obtained from the triangle inequality on the coefficients of
   the expansion at c, and 40 (1 - B_C) > B_D.
2. Numerical sanity: all 34 roots of S_mu, min |t|, min |t - 1|, and min over the roots of
   rho = A_3 / (A_1 + A_2 + A_3), A_j = mu_j |Lambda_j(t)|^(1/2).
"""
import sympy as sp
import mpmath as mp

t, x, h = sp.symbols('t x h')
mu1, mu2, N = 1, 2, 40
lag = {'t^2-t+1': t**2 - t + 1, 'N01': t**4 - 5*t**3 + 9*t**2 - 5*t + 1,
       'N10': t**4 + t**3 - 2*t + 1, 'N11': t**4 - 2*t**3 + t + 1}
r = sp.Rational(1, 10)
ok = True
for name, p in lag.items():
    for c in (0, 1):
        q = sp.Poly(sp.expand(p.subs(t, c + h)), h)
        coeffs = dict(zip([m[0] for m in q.monoms()], q.coeffs()))
        const = coeffs.get(0, 0)
        bound = sum(abs(a) * r**k for k, a in coeffs.items() if k > 0)
        ok &= (const == 1 and bound < 1)
        print(f'{name} at {c}: value {const}, tail bound {bound} = {float(bound):.4f}')


def F(m1, m2, m3, s12, s13, s23):
    F1 = m2*s12 + m3*s13/(1 + x)**2
    F2 = -m1*s12 + m3*s23/x**2
    F3 = -m1*s13/(1 + x)**2 - m2*s23/x**2
    return sp.cancel(x**2*(1 + x)**2*(x*(F1 - F2) - (F2 - F3)))


worst = None
for sig in ((1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)):
    s12, s13, s23 = sig
    Q = sp.expand(F(mu1, mu2, N, *sig))
    C = s13*x**3 - s23*(1 + x)**3
    D = (mu1 + mu2)*s12*x**3*(1 + x)**2 + mu1*s12*x**2*(1 + x)**2 - mu1*s13*x**2 - mu2*s23*(1 + x)**2
    ok &= sp.expand(Q - (N*C + D)) == 0
    for c in (0, -1):
        def tail(f, const_too):
            q = sp.Poly(sp.expand(f.subs(x, c + h)), h)
            return sum(abs(a) * r**m[0] for m, a in zip(q.monoms(), q.coeffs()) if const_too or m[0] > 0)
        Cc = C.subs(x, c)
        BC, BD = tail(C, False), tail(D, True)
        margin = N*(abs(Cc) - BC) - BD
        ok &= abs(Cc) == 1 and margin > 0
        worst = margin if worst is None or margin < worst else worst
        print(f'sigma {sig} at x={c}: |C(c)|={abs(Cc)}, B_C={float(BC):.4f}, B_D={float(BD):.4f}, 40(1-B_C)-B_D={float(margin):.3f}')
print('exact bounds hold:', ok)

S = (t**2 - t + 1)*lag['N01']*lag['N10']*lag['N11']
for sig in ((1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)):
    S *= F(mu1, mu2, N, *sig).subs(x, t - 1)
S = sp.Poly(sp.expand(S), t)
print('deg S_mu', S.degree(), 'leading coefficient', S.LC())
mp.mp.dps = 40
roots = sp.Poly(S, t).nroots(n=30, maxsteps=200)
M = mu1 + mu2 + N
rho_min, tmin, t1min = 2, 10, 10
for z in roots:
    z = complex(z)
    l1 = mu2 + N*z
    l2 = l1 - M
    l3 = l1 - M*z
    A = [mu1*abs(l2*l3)**0.5, mu2*abs(l1*l3)**0.5, N*abs(l1*l2)**0.5]
    rho_min = min(rho_min, A[2]/sum(A))
    tmin, t1min = min(tmin, abs(z)), min(t1min, abs(z - 1))
print(f'{len(roots)} roots; min |t| = {tmin:.4f}; min |t-1| = {t1min:.4f}; min rho = {rho_min:.4f}')
