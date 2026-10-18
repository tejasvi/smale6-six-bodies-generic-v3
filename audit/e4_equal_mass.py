"""Checks of the hand proof of Lemma 7.7 (E_4 at mu = (1,1,1,1)), Section 7.2.

Usage: python3 -I e4_equal_mass.py        (needs sympy)

Non-collinear branch.
1. The 729 symmetric patterns e_kl in Z/3 (epsilon_kl = j^e_kl) form 9 orbits of size 81 under e_kl -> e_kl + c_k + c_l,
   and (e12+e34, e13+e24, e14+e23) modulo (1,1,1) separates the orbits.
2. Relabellings (S_4) and e -> -e (complex conjugation) reduce the 9 orbits to the 3 types of the classes
   (0,0,0), (0,0,1), (0,1,2).
3. For one pattern of each type, with E = (j^e_kl) (zero diagonal): ker E and the system E p = p o p, sum p^3 = 0
   has no solution with p != 0 (Groebner bases over Q(j), one for each coordinate p_k != 0).
Collinear branch.
4. The 64 antisymmetric sign patterns have the score sequences (3,2,1,0), (3,1,1,1), (2,2,2,0), (2,2,1,1); under
   relabelling and sigma -> -sigma there are 3 classes T, S, C.
5. For the representatives of T, S, C, with xi = (0, 1, t, s): e_k = numerator of sum_l sigma_kl/(xi_k - xi_l)^2,
   R1 = Res_s(e_1, e_2), R2 = Res_s(e_1, e_3), R1(0), and the integer Res_t(R1, R2/t^4), factored.
"""
import itertools
import sympy as sp

pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def inv(e):
    E = dict(zip(pairs, e))
    P = [(E[(0, 1)] + E[(2, 3)]) % 3, (E[(0, 2)] + E[(1, 3)]) % 3, (E[(0, 3)] + E[(1, 2)]) % 3]
    return tuple((v - P[0]) % 3 for v in P)


pats = list(itertools.product(range(3), repeat=6))
orbits = {}
for e in pats:
    key = min(tuple((e[i] + c[a] + c[b]) % 3 for i, (a, b) in enumerate(pairs))
              for c in itertools.product(range(3), repeat=4))
    orbits.setdefault(key, []).append(e)
sizes = sorted(len(v) for v in orbits.values())
separates = len({inv(k) for k in orbits}) == len(orbits) and all(len({inv(e) for e in v}) == 1 for v in orbits.values())
print(f'(1) {len(orbits)} orbits, sizes {set(sizes)}; the invariant separates them: {separates}')


def relabel(e, g):
    E = dict(zip(pairs, e))
    out = []
    for a, b in pairs:
        ga, gb = g[a], g[b]
        out.append(E[(min(ga, gb), max(ga, gb))])
    return tuple(out)


classes = {inv(k) for k in orbits}
types = []
seen = set()
for P in sorted(classes):
    if P in seen:
        continue
    rep = next(k for k in orbits if inv(k) == P)
    orb = set()
    for g in itertools.permutations(range(4)):
        for sgn in (1, -1):
            orb.add(inv(tuple((sgn * v) % 3 for v in relabel(rep, g))))
    seen |= orb
    types.append((P, sorted(orb)))
print(f'(2) {len(types)} types: ' + '; '.join(f'{P}: {len(o)} classes' for P, o in types))

w = sp.Symbol('w')
K = sp.QQ.algebraic_field(sp.Rational(-1, 2) + sp.sqrt(-3) / 2)
j = sp.Rational(-1, 2) + sp.sqrt(-3) / 2
p = sp.symbols('p1:5')
z = sp.Symbol('z')
reps = {'I': (0, 0, 0, 0, 0, 0), 'II': (0, 0, 1, 0, 0, 0), 'III': (0, 2, 1, 1, 2, 0)}
for name, e in reps.items():
    E = sp.zeros(4, 4)
    for (a, b), v in zip(pairs, e):
        E[a, b] = E[b, a] = j**v
    E = sp.simplify(E)
    ker = E.nullspace()
    eqs = [sp.expand(sum(E[k, l] * p[l] for l in range(4)) - p[k]**2) for k in range(4)] + [sum(v**3 for v in p)]
    nosol = True
    for k in range(4):
        G = sp.groebner(eqs + [1 - z * p[k]], *p, z, domain=K, order='grevlex')
        nosol &= (list(G.exprs) == [1])
    kerdim = len(ker)
    kertxt = 'E invertible' if kerdim == 0 else f'ker E = span{[sp.nsimplify(sp.simplify(c)) for c in ker[0]]}'
    print(f'(3) type {name}, e = {e} (invariant {inv(e)}): {kertxt}; no solution with p != 0: {nosol}')

scores = {}
sig_all = list(itertools.product((1, -1), repeat=6))
for s in sig_all:
    S = dict(zip(pairs, s))
    sc = [0] * 4
    for (a, b), v in S.items():
        sc[a if v == 1 else b] += 1
    scores.setdefault(tuple(sorted(sc, reverse=True)), 0)
    scores[tuple(sorted(sc, reverse=True))] += 1
print(f'(4) score sequences: {scores}')

t, s = sp.symbols('t s')
xi = [sp.Integer(0), sp.Integer(1), t, s]
REP = {'T': {(0, 1): 1, (0, 2): 1, (0, 3): 1, (1, 2): 1, (1, 3): 1, (2, 3): 1},
       'S': {(0, 1): 1, (0, 2): 1, (0, 3): 1, (1, 2): 1, (1, 3): -1, (2, 3): 1},
       'C': {(0, 1): 1, (0, 2): 1, (0, 3): -1, (1, 2): 1, (1, 3): 1, (2, 3): 1}}
for name, S in REP.items():
    sg = lambda a, b: S[(a, b)] if a < b else -S[(b, a)]
    sc = sorted([sum(1 for b in range(4) if b != a and sg(a, b) == 1) for a in range(4)], reverse=True)
    e = [sp.numer(sp.together(sum(sp.Integer(sg(k, l)) / (xi[k] - xi[l])**2 for l in range(4) if l != k))) for k in range(3)]
    e = [sp.expand(v) for v in e]
    R1 = sp.Poly(sp.resultant(e[0], e[1], s), t)
    R2 = sp.Poly(sp.resultant(e[0], e[2], s), t)
    q, rem = sp.div(R2, sp.Poly(t**4, t))
    res = sp.resultant(R1.as_expr(), q.as_expr(), t)
    print(f'(5) {name} scores {tuple(sc)}: e1 = {e[0]}; R1 = {R1.as_expr()}; R1(0) = {R1.eval(0)}; '
          f'R2 = t^4 ({q.as_expr()}), remainder {rem.as_expr()}; Res_t(R1, R2/t^4) = {res} = {sp.factorint(res)}')
