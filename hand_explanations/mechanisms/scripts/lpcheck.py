"""Independent floating-point LP cross-check of the single-monomial lemmas on random samples of the cells where they
apply: on the cell polyhedron (base + argmin rows, explain.build), the claimed minimal monomial is strictly below
every other term of the identity (for C and B: the merged minimal terms against all others)."""
import json, sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from explain import build, lin, explain
from lemmas import argmins
import glob
cls = load_classes()
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
rng = random.Random(7)
NS = int(sys.argv[1]) if len(sys.argv) > 1 else 300
if NS <= 0: NS = 10**9
cov = {}
for l in open('../data/coverage.jsonl'):
    r = json.loads(l)
    cov[(r['class'], r['cell'])] = r
want = {}
for lem in ('T', 'P', 'C', 'B'):
    keys = [k for k, r in cov.items() if r['lemmas'][lem]]
    rng.shuffle(keys)
    for k in keys[:NS]:
        want.setdefault(k, []).append(lem)
cellrec = {}
for d in sorted(glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*'))):
    c = int(d.rsplit('/c', 1)[1])
    need = {k[1] for k in want if k[0] == c}
    if not need: continue
    for i, line in enumerate(open(os.path.join(d, 'cells.jsonl'))):
        if i in need:
            r = json.loads(line); r['class'] = c; cellrec[(c, i)] = r
from collections import Counter
res = Counter(); bad = []
for key, lems in want.items():
    rec = cellrec[key]; D = Diag(cls[key[0]])
    L = build(rec, D); C = L.C
    def zpos(k): m = C.zt.meet(k, 6); return None if m is None else L.h('z', m)
    def wpos(k): m = C.wt.meet(k, 6); return None if m is None else L.h('w', m)
    def zeta(k, l): return L.h('z', C.zt.meet(k, l))
    def omega(k, l): return L.h('w', C.wt.meet(k, l))
    def force(k, l, col):
        return lin((zeta(k, l), -0.5), (omega(k, l), -1.5)) if col == 'z' else lin((zeta(k, l), -1.5), (omega(k, l), -0.5))
    wit = cov[key]['witness']
    for lem in lems:
        w = wit[lem]
        terms = []  # (label, form)
        claim = []
        if lem == 'T':
            J, (p, q) = w[0], w[1]
            J = eval(J) if isinstance(J, str) else J
            if isinstance(w, str): w = eval(w)
            J, (p, q) = w
            Jc = [j for j in range(6) if j not in J]
            for k in J:
                for l2 in Jc:
                    for a, b in ((k, l2), (l2, k)):
                        if zpos(a) is None or wpos(b) is None: continue
                        f = lin((zpos(a), 1), (wpos(b), 1), (zeta(a, b), -1.5), (omega(a, b), -1.5))
                        terms.append(((a, b), f))
            claim = [(p, q)]
        elif lem == 'P':
            terms = [(('E',), {})]
            for k in range(6):
                if zpos(k) is None or wpos(k) is None: continue
                terms.append((('zw', k), lin((zpos(k), 1), (wpos(k), 1))))
            claim = [('E',)]
        elif lem == 'C':
            if isinstance(w, str): w = eval(w)
            col, J, (typ, x) = w
            Jc = [j for j in range(6) if j not in J]
            pos = zpos if col == 'z' else wpos
            for i in J:
                if pos(i) is not None: terms.append((('pos', i), pos(i)))
            for i in J:
                for j in Jc: terms.append((('cross', i, j), force(i, j, col)))
            if typ == 'single': claim = [tuple(x)]
            else: claim = [('pos', i) for i in x]
        elif lem == 'B':
            if isinstance(w, str): w = eval(w)
            col, k, l2 = w
            pos = zpos if col == 'z' else wpos
            sep = zeta(k, l2) if col == 'z' else omega(k, l2)
            terms.append((('sep',), sep))
            terms.append((('merged',), force(k, l2, col)))
            for j in range(6):
                if j in (k, l2): continue
                terms.append((('cross', k, j), force(k, j, col)))
                terms.append((('cross', l2, j), force(l2, j, col)))
            claim = [('merged',)]
        cl = [f for lab, f in terms if lab in claim]
        others = [(lab, f) for lab, f in terms if lab not in claim]
        ok = True
        # claimed terms equal to each other identically, strictly below the others
        f0 = cl[0]
        for f in cl[1:]:
            okz, _ = explain(L, f0, f); okz2, _ = explain(L, f, f0)
            if okz or okz2: ok = False
        for lab, f in others:
            s, _ = explain(L, f0, f)
            if not s: ok = False; bad.append((key, lem, lab)); break
        res[(lem, ok)] += 1
print(res)
print(bad[:10])
