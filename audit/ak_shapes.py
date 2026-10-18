"""Check of the sentence after Lemma 6.9: the factors of S_mu are those of the complex three-body shapes S1-S8 of
[AK12, appendix], written in the w-coordinates of the bodies.

Usage: python3 -I ak_shapes.py        (needs sympy)

The polynomials S1-S8 are transcribed from the appendix of [AK12] (A. Albouy and V. Kaloshin, Ann. of Math. 176 (2012)
535-588; AK's bodies 3, 4, 5 are the bodies 1, 2, 3 here). Each S_i is evaluated at (w3, w4, w5) = (l1, l2, l3)(t), the positions of the
bodies as functions of the shape t (Section 6.4), and compared with the factors t^2 - t + 1, N01, N10, N11 and
Q_sigma(t - 1) of S_mu: a match up to a factor depending on the masses only is printed.
"""
import sympy as sp
w3, w4, w5, t, x = sp.symbols('w3 w4 w5 t x')
m1, m2, m3 = sp.symbols('mu1 mu2 mu3', positive=True)
S = {}
S[1] = (w4**5 + w5**2*w4**3 - 2*w4**4*w3 + 4*w5**3*w3*w4 - 2*w4**4*w5 + w3**2*w4**3 + 4*w5*w3*w4**3 + w3**2*w5*w4**2
        - 2*w5**4*w4 + w5**3*w4**2 - 5*w3*w5**2*w4**2 - w3**3*w4**2 + w5**5 + 2*w3**4*w4 + w3**2*w5**3 + w3**2*w5**2*w4
        - 2*w3*w5**4 + 2*w3**4*w5 - w3**3*w5**2 - w3**5 - 4*w3**3*w5*w4)
S[2] = (w4**5 + w5**2*w4**3 - 2*w4**4*w3 - 4*w5**3*w3*w4 - 2*w4**4*w5 + w3**2*w4**3 + 4*w5*w3*w4**3 - w3**2*w5*w4**2
        + 2*w5**4*w4 - w5**3*w4**2 - w3*w5**2*w4**2 - w3**3*w4**2 - w5**5 + 2*w3**4*w4 - w3**2*w5**3 + 5*w3**2*w5**2*w4
        + 2*w3*w5**4 + 2*w3**4*w5 - w3**3*w5**2 - w3**5 - 4*w3**3*w5*w4)
S[3] = (w3**5 - 2*w3**4*w4 - 2*w3**4*w5 + w3**3*w4**2 + w3**3*w5**2 + 4*w3**3*w5*w4 - 5*w3**2*w5*w4**2 + w3**2*w5**2*w4
        - w3**2*w5**3 + w3**2*w4**3 + 4*w5*w3*w4**3 + w3*w5**2*w4**2 - 4*w5**3*w3*w4 - 2*w4**4*w3 + 2*w3*w5**4
        - w5**3*w4**2 - 2*w4**4*w5 + w5**2*w4**3 + w4**5 - w5**5 + 2*w5**4*w4)
S[4] = (w3**3 - w3**2*w4 - w3*w4**2 + w4**3 + 3*w3*w5*w4 - w3**2*w5 - w5*w4**2 - w5**2*w4 - w3*w5**2 + w5**3)
S[5] = w3**2 - w3*w4 + w4**2 - w5*w3 - w5*w4 + w5**2
S[6] = (w3**4 - 2*w3**3*w4 + w3*w4**3 + w4**4 - 2*w3**3*w5 + 6*w3**2*w5*w4 - 3*w5*w3*w4**2 - 5*w5*w4**3
        - 3*w3*w5**2*w4 + 9*w5**2*w4**2 + w5**3*w3 - 5*w5**3*w4 + w5**4)
S[7] = (w3**4 + w3**3*w4 - 2*w3*w4**3 + w4**4 - 3*w3**2*w5*w4 - 5*w3**3*w5 + 6*w5*w3*w4**2 - 2*w5*w4**3
        + 9*w3**2*w5**2 - 3*w3*w5**2*w4 - 5*w5**3*w3 + w5**3*w4 + w5**4)
S[8] = (w3**4 - 5*w3**3*w4 + 9*w3**2*w4**2 - 5*w3*w4**3 + w4**4 + w3**3*w5 - 3*w3**2*w5*w4 - 3*w5*w3*w4**2
        + w5*w4**3 + 6*w3*w5**2*w4 - 2*w5**3*w3 - 2*w5**3*w4 + w5**4)
M = m1 + m2 + m3
l1 = m2 + m3*t
l2 = l1 - M
l3 = l1 - M*t
N01 = t**4 - 5*t**3 + 9*t**2 - 5*t + 1
N10 = t**4 + t**3 - 2*t + 1
N11 = t**4 - 2*t**3 + t + 1
def Q(sig):
    s12, s13, s23 = sig
    sg = {(1,2): s12, (1,3): s13, (2,3): s23, (2,1): -s12, (3,1): -s13, (3,2): -s23}
    z = {(1,2): 1, (2,3): x, (1,3): 1 + x}
    zz = lambda k, l: z[(k, l)] if (k, l) in z else -z[(l, k)]
    mu = {1: m1, 2: m2, 3: m3}
    F = {k: sum(mu[l]*sg[(k, l)]/zz(k, l)**2 for l in (1, 2, 3) if l != k) for k in (1, 2, 3)}
    return sp.factor(sp.together(x**2*(1 + x)**2*(x*(F[1] - F[2]) - (F[2] - F[3]))))
targets = {'t2-t+1': t**2 - t + 1, 'N01': N01, 'N10': N10, 'N11': N11}
for sig in [(1,1,1), (1,1,-1), (1,-1,-1), (1,-1,1)]:
    targets['Q%s' % (sig,)] = sp.expand(Q(sig).subs(x, t - 1))
for sig in [(1,-1,1)]:
    q = sp.factor(targets['Q%s' % (sig,)])
    print('Q(1,-1,1)(t-1) factored:', q)
for i in range(1, 9):
    s = sp.expand(S[i].subs({w3: l1, w4: l2, w5: l3}, simultaneous=True))
    fs = sp.factor_list(s, t)
    matches = []
    for name, tg in targets.items():
        r = sp.cancel(s / tg)
        if r.free_symbols <= {m1, m2, m3}:
            matches.append((name, sp.factor(r)))
    print('S%d' % i, 'deg_t', sp.degree(s, t), 'matches:', matches if matches else None)
    if not matches:
        print('   factors:', [(sp.factor(f), e) for f, e in fs[1]][:6], 'const', fs[0])
