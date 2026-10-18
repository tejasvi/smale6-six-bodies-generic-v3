"""Lemma L (Lagrange triangle), step-by-step verification of the hand derivation with exact polynomial identities,
and the final condition: its norm over the cube roots of unity, its factors, the engine's label of class 16 cells
4/6/8/10 (L21), and the absence of positive zeros (hand argument + check)."""
import sympy as sp
ma, mb, ms = sp.symbols('ma mb ms', positive=True)
Xa, Xb, Xs, Ya, Yb, Pab, Pas, Pbs = sp.symbols('Xa Xb Xs Ya Yb Pab Pas Pbs')
M = ma + mb + ms
zeq_a = Xa - mb*Pab**3*(Xa-Xb) - ms*Pas**3*(Xa-Xs)
zeq_b = Xb - ma*Pab**3*(Xb-Xa) - ms*Pbs**3*(Xb-Xs)
zeq_s = Xs - ma*Pas**3*(Xs-Xa) - mb*Pbs**3*(Xs-Xb)
weq_a = Ya - mb*Pab**3*(Ya-Yb) - ms*Pas**3*Ya
weq_b = Yb - ma*Pab**3*(Yb-Ya) - ms*Pbs**3*Yb
bal_s = ma*Pas**3*(0-Ya) + mb*Pbs**3*(0-Yb)
# (1) w-centre of the pair: ma Ya + mb Yb = ma weq_a + mb weq_b - ms bal_s
print('(1)', sp.expand(ma*weq_a + mb*weq_b - ms*bal_s - (ma*Ya + mb*Yb)) == 0)
# (2) balance at s with (1): ma Ya (Pbs^3 - Pas^3) = bal_s + Pbs^3 (ma Ya + mb Yb)
rel1 = ma*Ya + mb*Yb
print('(2)', sp.expand(ma*Ya*(Pbs**3 - Pas**3) - (bal_s + Pbs**3*rel1)) == 0)
# (3) z-centre of the triangle: ma Xa + mb Xb + ms Xs = ma zeq_a + mb zeq_b + ms zeq_s
print('(3)', sp.expand(ma*zeq_a + mb*zeq_b + ms*zeq_s - (ma*Xa + mb*Xb + ms*Xs)) == 0)
# (4) with Pas^3 = Pbs^3 = Q: zeq_s = Xs (1 - M Q) - Q (ma Xa + mb Xb + ms Xs)
Q = sp.symbols('Q')
z4 = zeq_s.subs({Pas: Q**sp.Rational(1, 3), Pbs: Q**sp.Rational(1, 3)})
# precisely: zeq_s = Xs - Q((ma+mb) Xs - ma Xa - mb Xb) = Xs (1 - M Q) + Q (ma Xa + mb Xb + ms Xs)
print('(4b)', sp.simplify(z4 - (Xs*(1 - M*Q) + Q*(ma*Xa + mb*Xb + ms*Xs))) == 0)
# (5) weq_a with Yb = -(ma/mb) Ya and Pas^3 = 1/M: Ya (1 - ms/M) - mb Pab^3 Ya (ma+mb)/mb = Ya (ma+mb)(1/M - Pab^3)
R3 = sp.symbols('R3')
w5 = weq_a.subs({Yb: -ma/mb*Ya}).subs({Pab: R3**sp.Rational(1, 3), Pas: (1/M)**sp.Rational(1, 3)})
print('(5)', sp.simplify(w5 - Ya*(ma+mb)*(1/M - R3)) == 0)
# (6) closure of the z-separations: xi_kl = 1/(P_kl^2 eta_kl), eta_ab = Ya (ma+mb)/mb, eta_bs = -(ma/mb) Ya, eta_sa = -Ya
eab, ebs, esa = Ya*(ma+mb)/mb, -(ma/mb)*Ya, -Ya
# (7) with P_kl = c_kl M^(-1/3), c^3 = 1, P^-2 = c M^(2/3) (c^-2 = c): closure*Ya*M^(-2/3) =
#     c_ab mb/(ma+mb) - c_bs mb/ma - c_sa ; times ma (ma+mb):  ma mb c_ab - mb (ma+mb) c_bs - ma (ma+mb) c_sa
w = sp.exp(2*sp.pi*sp.I/3)
cands = []
for e1 in range(3):
    for e2 in range(3):
        for e3 in range(3):
            cands.append(ma*mb*w**e1 - mb*(ma+mb)*w**e2 - ma*(ma+mb)*w**e3)
# norm over e2, e3 with e1 = 0 (the condition is homogeneous under a common cube root): 9 factors
x, y = sp.symbols('x y')
A, B, C = ma*mb, -mb*(ma+mb), -ma*(ma+mb)
H = sp.expand((A**3 + B**3 + C**3)**3 - 27*A**3*B**3*C**3)
W = sp.symbols('W')
prod9 = sp.expand(sp.prod([A + B*W**i + C*W**j for i in range(3) for j in range(3)]))
print('(7) norm identity (mod W^2+W+1)', sp.rem(sp.Poly(prod9 - H, W), sp.Poly(W**2 + W + 1, W)).is_zero)
fl = sp.factor_list(H)
print('factors of the norm H:', [(sp.factor(f), e) for f, e in fl[1]])
lab = sp.sympify('m3^14+7*m3^13*m4+19*m3^12*m4^2+23*m3^11*m4^3+17*m3^10*m4^4+41*m3^9*m4^5+105*m3^8*m4^6+141*m3^7*m4^7+105*m3^6*m4^8+41*m3^5*m4^9+17*m3^4*m4^10+23*m3^3*m4^11+19*m3^2*m4^12+7*m3*m4^13+m4^14'.replace('^', '**'))
m3, m4 = sp.symbols('m3 m4')
Hl = sp.expand(H.subs({ma: m3, mb: m4}))
q, r = sp.div(sp.Poly(Hl, m3, m4), sp.Poly(lab, m3, m4))
print('engine label (class 16 cell 4) divides H(a=3,b=4):', r.is_zero, ' quotient:', sp.factor(q.as_expr()))
# (8) no positive zero: |B w^i + C w^j| > A for all i, j at positive masses (hand: B^2 + C^2 - BC >= BC > A^2)
print('(8) B^2+C^2-|B||C| - A^2 =', sp.factor(sp.expand(B**2 + C**2 - B*C - A**2)))
print('    (B+C)^2 - A^2 =', sp.factor(sp.expand((B + C)**2 - A**2)))
