import sympy as sp
ma, mb, t = sp.symbols('ma mb t', positive=True)
A = ma*mb; B = mb*(ma+mb); C = ma*(ma+mb)
w = sp.exp(2*sp.pi*sp.I/3)
# norm over eps2, eps3 (eps1 = 1) of A - B*e2 - C*e3
prod = 1
for i in range(3):
    for j in range(3):
        prod *= (A - B*w**i - C*w**j)
prod = sp.expand(sp.simplify(sp.expand(prod)))
lhs = sp.expand((A**3 - B**3 - C**3)**3 - 27*A**3*B**3*C**3)
print('norm == (A^3-B^3-C^3)^3 - 27 A^3B^3C^3:', sp.simplify(prod - lhs) == 0)
HL = (ma**2+ma*mb+mb**2)**3*(ma**4-ma**3*mb+2*ma*mb**3+mb**4)*(ma**4+2*ma**3*mb-ma*mb**3+mb**4)*(ma**4+5*ma**3*mb+9*ma**2*mb**2+5*ma*mb**3+mb**4)
print('(A^3-B^3-C^3)^3 - 27A^3B^3C^3 == -H_L:', sp.expand(lhs + HL) == 0)
q = t**4 - t**3 + 2*t + 1
print('t^4 - t^3 + 2t + 1 minimum on t>0:', [sp.N(q.subs(t, r)) for r in sp.real_roots(sp.diff(q, t)) if r > 0], 'real roots of q:', sp.real_roots(q))
q2 = t**4 + 2*t**3 - t + 1
print('reverse quartic real positive roots:', [r for r in sp.real_roots(q2) if r > 0])
