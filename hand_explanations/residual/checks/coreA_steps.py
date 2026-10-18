"""No-label family A (core level): the core relations (both centres, D on three sides, x[a] with position, x[s]
balanced, y[a] with position) imply (sigma^3 - 1)(N^2 sigma^2 - m_b^2) = 0 with
sigma^2 = m_a m_b w^2 / (N (m_a w^2 + m_b)), w^3 = 1, N = m_a + m_b; i.e. m_a^6 = m_b^6, or a factor without positive
zeros. Exact identity checks of the steps."""
import sympy as sp
ma, mb, ms, s, Pas, W = sp.symbols('ma mb ms sigma Pas W')
N = ma + mb
M = ma + mb + ms
# (i) and (ii) after normalising Ya = 1, Pab = sigma*Pas, Pbs = w*Pas:
#   (ii)  Pas^3 (ms + N sigma^3) = 1
#   (i)   Pas^3 * M * (ms + mb^2 sigma/N) = ms + mb^2/(N sigma^2)
# eliminating Pas^3:  M (ms + mb^2 sigma/N) = (ms + mb^2/(N sigma^2)) (ms + N sigma^3)
G = sp.expand((M*(ms + mb**2*s/N) - (ms + mb**2/(N*s**2))*(ms + N*s**3)) * N * s**2)
print('G factorises as -ms (sigma^3 - 1)(N^2 sigma^2 - mb^2):', sp.simplify(G + ms*(s**3 - 1)*(N**2*s**2 - mb**2)) == 0)
# the closure relation defining sigma^2 (from D and the y-closure, with Pbs = w Pas, w^3 = 1, w^-2 = w):
#   1/Pas^2 + mb/(ma Pbs^2) = mb/(N Pab^2)   <=>  sigma^2 = ma mb w^2 / (N (ma w^2 + mb))
w = sp.symbols('w')
sig2 = ma*mb*w**2/(N*(ma*w**2 + mb))
lhs = 1 + mb/(ma*w**2)
rhs = mb/(N*sig2)
print('closure gives sigma^2:', sp.simplify(lhs - rhs) == 0)
# case N^2 sigma^2 = mb^2:  ma^2 w^2 = mb^2  ->  (ma/mb)^6 = 1
c1 = sp.numer(sp.together(N**2*sig2 - mb**2))
print('case 2 numerator:', sp.factor(c1))
# case sigma^3 = 1  <=>  (sigma^2)^3 = 1 (sigma = 1/sigma^2):  ma^3 mb^3 w^6 = N^3 (ma w^2 + mb)^3
c2 = sp.expand((ma*mb*W**2)**3 - N**3*(ma*W**2 + mb)**3)
norm = sp.expand(sp.prod([c2.subs(W, sp.exp(2*sp.pi*sp.I*j/3)) for j in range(3)]))
norm = sp.nsimplify(sp.expand(sp.simplify(norm)))
print('case 1 norm over w, factored:', sp.factor(norm))
# positivity of case 1: |ma mb| < N |ma w^2 + mb| for positive masses (w = 1: N^2 > ma mb; w != 1: N sqrt(ma mb))

# The branch N^2 sigma^2 = mb^2 is excluded: X_s (the y-position of s, nonzero) equals
#   X_s = sigma (mb^2 - N^2 sigma^2) / (N (ms + N sigma^3) Pas^2)   (normalisation Ya = 1)
Xa = Pas*(ms + mb**2*s/N)                 # from y[a]
Xs = Xa - 1/Pas**2                        # X_a - X_s = 1/(Pas^2 Ya)
Pas3 = 1/(ms + N*s**3)                    # from x[a]
expr = sp.simplify((Xs*Pas**2).subs(Pas**3, Pas3) if False else ((Pas**3*(ms + mb**2*s/N) - 1)).subs(Pas**3, Pas3))
print('X_s * Pas^2 = sigma (mb^2 - N^2 sigma^2)/(N (ms + N sigma^3)):',
      sp.simplify(expr - s*(mb**2 - N**2*s**2)/(N*(ms + N*s**3))) == 0)
# Hence sigma^3 = 1, i.e. (sigma^2)^3 = 1: ma^3 mb^3 = N^3 (ma w^2 + mb)^3; its norm over w is -H_L:
Wv = sp.symbols('Wv')
Rn = sp.resultant(Wv**3 - 1, ma**3*mb**3 - N**3*(ma*Wv**2 + mb)**3, Wv)
HL = sp.expand((ma**2+ma*mb+mb**2)**3*(ma**4-ma**3*mb+2*ma*mb**3+mb**4)*(ma**4+2*ma**3*mb-ma*mb**3+mb**4)
               *(ma**4+5*ma**3*mb+9*ma**2*mb**2+5*ma*mb**3+mb**4))
print('norm of the branch sigma^3 = 1 equals -H_L (Lemma L):', sp.expand(Rn + HL) == 0)
