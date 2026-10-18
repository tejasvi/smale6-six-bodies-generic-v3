# Compare the P93 factors (d98 certificates/p93_factors.txt) with AK 2012 p. 574's printed terms (read-only).
import sys, sympy as sp
m1, m2, m3 = sp.symbols('m1 m2 m3')
F = []
for line in open(sys.argv[1]):
    name, deg, mult, poly = [s.strip() for s in line.split('|')]
    F.append((name, int(deg.split()[1]), int(mult.split()[1]), sp.Poly(sp.sympify(poly), m1, m2, m3)))
# AK labels m3,m4,m5 -> our m1,m2,m3
def mono(e3, e4, e5): return (e3, e4, e5)
AK = {
 'L1': [(6522, mono(15,12,9)), (3528, mono(17,17,2))], 'L2': [(2414, mono(15,12,9)), (3528, mono(17,17,2))],
 'L3': [(495, mono(0,24,12)), (-452, mono(17,17,2))],
 'L4': [(-110, mono(7,7,8)), (-30, mono(7,10,5))],
 'L5p': [(2, mono(0,10,2)), (1, mono(12,0,0))],
 'L6': [(866, mono(0,11,17)), (-1456, mono(6,15,7))], 'L7': [(-208, mono(0,11,17)), (-25528, mono(6,15,7))],
 'L8': [(-184, mono(0,11,17)), (9440, mono(6,15,7))],
}
perms = {'id': (m1,m2,m3)}
def sym_pairs(P):
    out = []
    for (a, b, nm) in [(m1, m2, '12'), (m1, m3, '13'), (m2, m3, '23')]:
        Q = sp.Poly(P.as_expr().subs({a: b, b: a}, simultaneous=True), m1, m2, m3)
        if Q == P or Q == -P: out.append(nm)
    return out
seen = []
for name, d, mult, P in F:
    if d <= 1: continue
    key = (name, d)
    c = P.as_dict()
    info = {k: [(coef, c.get(m, 0)) for coef, m in v] for k, v in AK.items()}
    match = [k for k, v in info.items() if all(a == b or a == -b for a, b in v)]
    print('%-5s deg %2d mult %d terms %3d symmetric-in %s | AK match: %s' % (name, d, mult, len(c), sym_pairs(P), match))
    for k in match: print('     ', k, info[k])
