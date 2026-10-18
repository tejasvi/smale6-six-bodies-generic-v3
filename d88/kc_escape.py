#!/usr/bin/env python3
"""The 'escape' leading system of KC (diagram 94): valuation direction v(U_k) = -2t, v(p_k4) = t (k = 1, 2, 3), all
other torus coordinates of valuation 0 (the only cone of the tropical prevariety whose initial system is not empty,
DERIVATION B.6).  On such a place: bodies 1..3 satisfy the complete three-body system N_3(mu1, mu2, mu3) at order 0
(positions X_k, Y_k = [Y_k]_0, distances q_kl), and body 4 (X_4 = 0, Y_4 of order -2t) satisfies
P_k4^2 X_k (-Y4) = 1 and the leading term of its X-equation, sum_l mu_l P_l4^3 X_l = 0.
Writes a Singular file testing that this system generates the unit ideal over F_p and over Q.
Usage: kc_escape.py mu1 mu2 mu3 mu4 p OUT.sing
"""
import sys
mu = [int(x) for x in sys.argv[1:5]]
p = int(sys.argv[5])
out = sys.argv[6]
m1, m2, m3, m4 = mu
eqs = []
X = {1: '1', 2: 'X2', 3: 'X3'}
Y = {1: 'Y1', 2: 'Y2', 3: 'Y3'}
q = {(1, 2): 'q12', (1, 3): 'q13', (2, 3): 'q23'}
m = {1: m1, 2: m2, 3: m3}
def Q(k, l):
    return q[(min(k, l), max(k, l))]
for Z in (X, Y):
    for k in (1, 2, 3):
        terms = ['%d*%s^3*((%s)-(%s))' % (m[l], Q(k, l), Z[k], Z[l]) for l in (1, 2, 3) if l != k]
        eqs.append('(%s) - (%s)' % (Z[k], '+'.join(terms)))
for (k, l), nm in q.items():
    eqs.append('%s^2*((%s)-(%s))*((%s)-(%s)) - 1' % (nm, X[k], X[l], Y[k], Y[l]))
for k in (1, 2, 3):
    eqs.append('P%d4^2*(%s)*(-Y4) - 1' % (k, X[k]))
eqs.append('+'.join('%d*P%d4^3*(%s)' % (m[l], l, X[l]) for l in (1, 2, 3)))
s = ''
for ch in (p, 0):
    s += 'ring r = %d,(X2,X3,Y1,Y2,Y3,q12,q13,q23,P14,P24,P34,Y4),dp;\n' % ch
    s += 'ideal I = ' + ',\n'.join(eqs) + ';\n'
    s += 'ideal G = std(I);\nprint("char %d escape system unit ideal: " + string(G[1]==1) + " dim " + string(dim(G)));\nkill r;\n' % ch
s += 'quit;\n'
open(out, 'w').write(s)
