"""Shapes of the TT witnesses: J relative to the trees and the diagram; (p,q) shapes."""
import json, sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from collections import Counter
cls = load_classes()
def zshape(T, p, q):
    t = T.meet(p, q)
    u = T.meet(p, O)
    if u is None: return 'p-at-O'
    below_t = t in T.anc(T.leaf[O])
    if not below_t: return 'farclu'
    if u == t: return 'outer'
    return 'inner'
def is_clade(T, J):
    """J (as a set of bodies) equals the set of bodies below some node (ignoring O), or its complement does."""
    Js = set(J)
    for v in list(T.children) + list(set(T.leaf.values())):
        pts = set(p for p in T.below(v) if p != O) if v in T.children else set(p for p, lf in T.leaf.items() if lf == v and p != O)
        if pts == Js: return True
    return False
tt = {}
for l in open('../data/tt_torque.jsonl'):
    r = json.loads(l); tt[(r['class'], r['cell'])] = r['tt']
shapes = Counter(); jkind = Counter()
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    h = tt[(r['class'], r['cell'])]
    if h is None: continue
    C = Cell(r)
    J, (p, q) = h
    sz = zshape(C.zt, p, q); sw = zshape(C.wt, q, p)
    shapes[tuple(sorted((sz, sw)))] += 1
    Jc = tuple(j for j in range(6) if j not in J)
    D = Diag(cls[r['class']])
    def tri(S):
        S = set(S)
        if len(S) != 3: return None
        pairs = [(a, b) for a, b in itertools.combinations(sorted(S), 2)]
        if all(e in D.zs for e in pairs): return 'ztri'
        if all(e in D.ws for e in pairs): return 'wtri'
        return None
    kz = 'zclade' if (is_clade(C.zt, J) or is_clade(C.zt, Jc)) else ''
    kw = 'wclade' if (is_clade(C.wt, J) or is_clade(C.wt, Jc)) else ''
    kt = tri(J) or tri(Jc) or ''
    jkind[(min(len(J), 6 - len(J)), kz, kw, kt)] += 1
for k, v in shapes.most_common(): print(v, k)
print()
for k, v in jkind.most_common(): print(v, k)
