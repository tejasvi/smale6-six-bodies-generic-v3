"""Tree-only torque criterion (TT): some torque T_J has a term (p,q) (z_p w_q delta^3) that tree-dominates all other
terms: A(k;l)-A(p;q) >= 0 in the z-tree and B(l;k)-B(q;p) >= 0 in the w-tree for all increasing heights, one > 0."""
import json, sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from treeform import *
from collections import Counter
from fractions import Fraction as F
H = F(3, 2)
def zf(C, k, l):
    u = C.zt.meet(k, O)
    if u is None: return None
    return add({u: 1}, {C.zt.meet(k, l): -H})
def wf(C, l, k):
    u = C.wt.meet(l, O)
    if u is None: return None
    return add({u: 1}, {C.wt.meet(k, l): -H})
def tt_torque(C, J):
    Jc = [j for j in range(6) if j not in J]
    terms = []
    for k in J:
        for l in Jc:
            for p, q in ((k, l), (l, k)):
                a = zf(C, p, q); b = wf(C, q, p)
                if a is None or b is None: continue
                terms.append(((p, q), a, b))
    for i, (pq, a, b) in enumerate(terms):
        ok = True
        for j, (pq2, a2, b2) in enumerate(terms):
            if i == j: continue
            sz = sign_tree(C.zt, add(a2, scale(a, -1)))
            if sz is None: ok = False; break
            sw = sign_tree(C.wt, add(b2, scale(b, -1)))
            if sw is None: ok = False; break
            if sz != 'pos' and sw != 'pos': ok = False; break
        if ok:
            return pq
    return None
tor_sets = [J for r in range(1, 6) for J in itertools.combinations(range(6), r) if 0 in J]
res = Counter(); byc = Counter(); tot = Counter()
out = open('../data/tt_torque.jsonl', 'w')
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    C = Cell(r)
    hit = None
    for J in sorted(tor_sets, key=lambda J: min(len(J), 6 - len(J))):
        pq = tt_torque(C, J)
        if pq is not None:
            hit = (J, pq); break
    tot[r['class']] += 1
    if hit: byc[r['class']] += 1
    res[hit is not None] += 1
    out.write(json.dumps({'class': r['class'], 'cell': r['cell'], 'tt': hit}) + '\n')
print(res)
for c in sorted(tot, key=lambda c: -tot[c]): print(c, tot[c], byc[c])
