"""Lemmas W3 and EQ2 where they are needed: their polynomials are nonzero in every cell whose only cell-level lemmas
are among W3 and EQ2 (the two lemmas whose polynomial depends on the linear relations of the cell).

Usage: python3 -I -B cell_polys.py REF_SCRIPTS REF_RESID_COVER REF_CLASS

REF_SCRIPTS      the directory of the independent re-implementation (refkit.py, ref_resid.py; read-only);
REF_RESID_COVER  its ref_resid_cover.jsonl (per cell, the W3 and EQ2 witnesses);
REF_CLASS        its final_classification.jsonl.
For each cell whose only cell-level lemma is W3, the shape vector e is computed in SymPy from the linear relations of
the witness (the centre of mass at the root and the relations of Lemma 9.1 at the node), as in the referee's
resid_polys.py, scaled to polynomial entries, and H_W = (u1u2+u2u3+u3u1)^3 - 27(u1u2u3)^2 with u1 = m_c^2(e_a-e_b),
u2 = m_a^2(e_b-e_c), u3 = m_b^2(e_c-e_a) is expanded; the program prints the shape, whether H_W is nonzero, its
degree, and its value at m = (1, 2, 3, 4, 5, 6) (masses of the bodies 0..5 of the supplement, 1..6 of the paper). For EQ2 the ratio
-M_A/M_B = X(c(b))/X(c(a)) is read off the same solution space, and m_a^2 M_A^4 - m_b^2 M_B^4 is expanded and
evaluated at the same point.
"""
import json, sys
import sympy as sp

sys.path.insert(0, sys.argv[1])
import refkit as K
import ref_resid as RR

m = sp.symbols('m0:6', positive=True)
need = []
for line in open(sys.argv[3]):
    r = json.loads(line)
    g = set(r['cell_level_generic'])
    if g and g <= {'W3', 'EQ2'} and not r['cell_level_allmass']:
        need.append((r['class'], r['cell']))
wit = {}
for line in open(sys.argv[2]):
    r = json.loads(line)
    if (r['class'], r['cell']) in need:
        wit[(r['class'], r['cell'])] = (r.get('W3') or [], r.get('EQ2') or [])
recs = {}
for c, i, rec in K.iter_cells({c for c, _ in need}):
    if (c, i) in wit:
        recs[(c, i)] = rec


def w3poly(C, y, T, v):
    tr = C.tree(y)
    co = RR.ochild(tr, v)
    kids = [u for u in tr.ch[v] if u != co]
    rels = RR.centre_relations(C, y, v)
    M = sp.Matrix([[sum(m[j] * rel[1].get(u, (0,) * 6)[j] for j in range(6)) for u in kids] for rel in rels])
    ns = M.nullspace()
    idx = [kids.index(tr.child_to(v, t)) for t in T]
    proj = [sp.Matrix([vec[i] for i in idx]) for vec in ns]
    assert sp.Matrix.hstack(*proj).rank() == 1
    e = [sp.simplify(x) for x in next(p for p in proj if any(sp.simplify(z) != 0 for z in p))]
    den = sp.lcm([sp.fraction(sp.together(x))[1] for x in e])
    e = [sp.expand(sp.cancel(x * den)) for x in e]          # e in Z[m], as in the lemma
    a, b, c = T
    u1 = m[c] ** 2 * (e[0] - e[1]); u2 = m[a] ** 2 * (e[1] - e[2]); u3 = m[b] ** 2 * (e[2] - e[0])
    H = sp.expand((u1 * u2 + u2 * u3 + u3 * u1) ** 3 - 27 * (u1 * u2 * u3) ** 2)
    return H, e


def eq2poly(C, y, s, a, b):
    tr = C.tree(y)
    v = tr.meet(a, b)
    co = RR.ochild(tr, v)
    kids = [u for u in tr.ch[v] if u != co]
    rels = RR.centre_relations(C, y, v)
    M = sp.Matrix([[sum(m[j] * rel[1].get(u, (0,) * 6)[j] for j in range(6)) for u in kids] for rel in rels])
    ns = M.nullspace()
    ia, ib = kids.index(tr.child_to(v, a)), kids.index(tr.child_to(v, b))
    assert sp.Matrix([[vec[ia], vec[ib]] for vec in ns]).rank() == 1
    vec = [vv for vv in ns if sp.simplify(vv[ia]) != 0][0]
    MA, MB = sp.fraction(sp.together(sp.simplify(-vec[ib] / vec[ia])))
    return sp.expand(m[a] ** 2 * MA ** 4 - m[b] ** 2 * MB ** 4), MA, MB


ok = True
print('cells whose only cell-level lemmas are among W3 and EQ2:', len(need))
for key in sorted(need):
    C = K.RCell(recs[key], *key)
    res = []
    w3, eq2 = wit[key]
    for w in w3:
        y, T, v, rels, bal = w
        H, e = w3poly(C, y, tuple(T), v)
        val = H.subs({m[j]: j + 1 for j in range(6)})
        res.append(('W3', y, tuple(T), [str(x) for x in e], H != 0, sp.Poly(H, *m).total_degree() if H != 0 else None, val))
    for w in eq2:
        y, (s_, a, b) = w
        H, MA, MB = eq2poly(C, y, s_, a, b)
        val = H.subs({m[j]: j + 1 for j in range(6)})
        res.append(('EQ2', y, (s_, a, b), [str(MA), str(MB)], H != 0, sp.Poly(H, *m).total_degree() if H != 0 else None, val))
    good = any(r[4] for r in res)
    ok &= good
    print(key, 'witnesses', len(res), 'first:', res[0], 'some polynomial nonzero:', good)
print('all cells have a witness with a nonzero polynomial:', ok)
