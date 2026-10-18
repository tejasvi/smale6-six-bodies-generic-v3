#!/usr/bin/env python3
"""Instantiate the generic polynomials of the residual lemmas on the referee's own witnesses (residual cells whose
first lemma in RESIDUAL is generic: R1*, W3, EQ2, TQ) and check that they are nonzero polynomials in the masses."""
import json, os, sys
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refkit as K
import ref_resid as RR

m = sp.symbols('m0:6', positive=True)
k = sp.Symbol('k')
mech = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'coverage.jsonl')):
    r = json.loads(l); mech[(r['class'], r['cell'])] = r
theirs = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'residual', 'data', 'resid_cover.jsonl')):
    r = json.loads(l); theirs[(r['class'], r['cell'])] = r
mine = {}
for l in open('ref_resid_cover.jsonl'):
    r = json.loads(l)
    if (r['class'], r['cell']) in theirs:
        mine[(r['class'], r['cell'])] = r
recs = {}
for c, i, rec in K.iter_cells({c for c, _ in theirs}):
    if (c, i) in theirs:
        recs[(c, i)] = rec


def N(ma, mb, ms, MA, MB):
    r = sp.resultant(MA * mb * k**3 - MB * ma, ms**2 * (MA + MB) * (ma + mb * k)**3 - ma**3 * mb**2 * MB, k)
    return sp.cancel(r / (ma**3 * mb**3))


def W3poly(C, y, T, v):
    tr = C.tree(y)
    co = RR.ochild(tr, v)
    kids = [u for u in tr.ch[v] if u != co]
    rels = RR.centre_relations(C, y, v)
    M = sp.Matrix([[sum(m[j] * rel[1].get(u, (0,) * 6)[j] for j in range(6)) for u in kids] for rel in rels])
    ns = M.nullspace()
    idx = [kids.index(tr.child_to(v, t)) for t in T]
    proj = [sp.Matrix([vec[i] for i in idx]) for vec in ns]
    P = sp.Matrix.hstack(*proj)
    assert P.rank() == 1
    e = [sp.simplify(x) for x in next(p for p in proj if any(sp.simplify(z) != 0 for z in p))]
    a, b, c = T
    u1 = m[c]**2 * (e[0] - e[1]); u2 = m[a]**2 * (e[1] - e[2]); u3 = m[b]**2 * (e[2] - e[0])
    H = sp.together((u1*u2 + u2*u3 + u3*u1)**3 - 27*(u1*u2*u3)**2)
    return sp.factor(sp.numer(H)), e


out = []
for key in sorted(theirs):
    first = theirs[key]['first']
    if first not in ('R1*', 'W3', 'EQ2', 'TQ'):
        continue
    C = K.RCell(recs[key], *key)
    M = mine[key]
    if first == 'R1*':
        ws = [w for w in M['R1s'] if w[2] in ('alpha', 'beta')]
        if ws:
            y, (a, b, s), how, bA, bB = ws[0]
            MA, MB = sum(m[j] for j in bA), sum(m[j] for j in bB)
        else:     # gamma, J = T (certified in resid_certs.py)
            y, (a, b, s), how, bA, bB = [w for w in M['R1s'] if w[2] == 'gamma?'][0]
            MA, MB = m[a], m[b]
            how = 'gamma(J=T)'
        P = N(m[a], m[b], m[s], MA, MB)
        P = sp.expand(sp.numer(sp.together(P)))
        out.append((key, 'R1*', how, (a, b, s), str(MA), str(MB), P != 0, sp.Poly(P, *m).total_degree()))
    elif first == 'W3':
        y, T, v, rels, bal = M['W3'][0]
        H, e = W3poly(C, y, tuple(T), v)
        out.append((key, 'W3', str(rels), tuple(T), [str(x) for x in e], H != 0, sp.Poly(sp.expand(H), *m).total_degree()))
    elif first == 'EQ2':
        y, (s, a, b) = M['EQ2'][0]
        tr = C.tree(y)
        v = tr.meet(a, b)
        co = RR.ochild(tr, v)
        kids = [u for u in tr.ch[v] if u != co]
        rels = RR.centre_relations(C, y, v)
        Mx = sp.Matrix([[sum(m[j] * rel[1].get(u, (0,) * 6)[j] for j in range(6)) for u in kids] for rel in rels])
        ns = Mx.nullspace()
        ia, ib = kids.index(tr.child_to(v, a)), kids.index(tr.child_to(v, b))
        vec = [vv for vv in ns if sp.simplify(vv[ia]) != 0][0]
        # relation MA*X_a + MB*X_b = 0 with X_b/X_a = vec[ib]/vec[ia]  ->  MA/MB = -vec[ib]/vec[ia]
        ratio = sp.simplify(-vec[ib] / vec[ia])
        MA, MB = sp.fraction(sp.together(ratio))
        P = sp.expand(m[a]**2 * MA**4 - m[b]**2 * MB**4)
        out.append((key, 'EQ2', (s, a, b), str(MA), str(MB), P != 0, sp.factor(P)))
    elif first == 'TQ':
        y, (l1, l2), (k1, k2) = M['TQ'][0]
        n1, n2, M1, M2 = m[k1], m[k2], m[l1], m[l2]
        A, B, Cc, D = n1**3, n2**3, M1**3, M2**3
        S = sp.expand((A + B)**2 * (Cc + D)**2 - 16 * A * B * Cc * D)
        P = sp.expand((n1**2 - n1*n2 + n2**2) * (M1**2 - M1*M2 + M2**2) * S)
        out.append((key, 'TQ', (l1, l2), (k1, k2), P != 0, sp.factor(S)))
for o in out:
    print(o)
print('all nonzero:', all(o[6] if o[1] in ('R1*', 'W3') else (o[5] if o[1] in ('EQ2',) else o[4]) for o in out), len(out))
