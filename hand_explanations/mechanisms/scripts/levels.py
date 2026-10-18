"""For the cells not covered by Lemma T: identities (torques, subset sums, Ip) with a unique minimal term at the
interior point, and whether that term is strictly least on the base polyhedron (L1: trees, (O1), (O2), circles) and on
the cell (L2). Output data/levels.jsonl."""
import json, sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
import lpkit as LK
from lemmas import lemma_T
TOL = 1e-4
INF = float('inf')
cls = load_classes()
subsets = [J for r in range(1, 6) for J in itertools.combinations(range(6), r)]
tor_sets = [J for J in subsets if 0 in J]

def forms_torque(L, zt, wt, J):
    """exponent forms (LP variables) of the torque terms, with labels."""
    Jc = [j for j in range(6) if j not in J]
    out = []
    for k in J:
        for l in Jc:
            for p, q in ((k, l), (l, k)):
                up, uq = zt.meet(p, 6), wt.meet(q, 6)
                if up is None or uq is None: continue
                f = {}
                for v, c in ((L.zv[up], 1.0), (L.wv[uq], 1.0), (L.zv[zt.meet(p, q)], -1.5), (L.wv[wt.meet(p, q)], -1.5)):
                    f[v] = f.get(v, 0.0) + c
                out.append((f, ('z', p, 'w', q)))
    return out

def forms_subset(L, zt, wt, J, col):
    Jc = [j for j in range(6) if j not in J]
    out = []
    T1, V1, T2, V2 = (zt, L.zv, wt, L.wv) if col == 'z' else (wt, L.wv, zt, L.zv)
    for i in J:
        u = T1.meet(i, 6)
        if u is not None:
            out.append(({V1[u]: 1.0}, ('pos', i)))
    for i in J:
        for j in Jc:
            f = {}
            for v, c in ((V1[T1.meet(i, j)], -0.5), (V2[T2.meet(i, j)], -1.5)):
                f[v] = f.get(v, 0.0) + c
            out.append((f, ('cross', i, j)))
    return out

def forms_ip(L, zt, wt):
    out = [({}, ('E',))]
    for k in range(6):
        u, v = zt.meet(k, 6), wt.meet(k, 6)
        if u is None or v is None: continue
        f = {}
        for var, c in ((L.zv[u], 1.0), (L.wv[v], 1.0)):
            f[var] = f.get(var, 0.0) + c
        out.append((f, ('zw', k)))
    return out

def value(f, C, zt, wt, L):
    # evaluate at the interior point using heights hz/hw
    inv = {}
    for v, i in L.zv.items(): inv[i] = C.zt.h[v]
    for v, i in L.wv.items(): inv[i] = C.wt.h[v]
    return sum(c * inv[j] for j, c in f.items())

out = open('../data/levels.jsonl', 'w')
n = 0
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    C = Cell(r)
    if lemma_T(C) is not None: continue
    D = LK.diagram(cls[r['class']])
    zt, wt = LK.trees(r)
    Lb = LK.base(D, zt, wt)
    Lc = LK.cell(D, zt, wt, r['argmin'])
    cands = []
    for J in tor_sets:
        cands.append((('T', J), forms_torque(Lb, zt, wt, J)))
    for col in 'zw':
        for J in subsets:
            cands.append((('S', col, J), forms_subset(Lb, zt, wt, J, col)))
    cands.append((('Ip',), forms_ip(Lb, zt, wt)))
    res = []
    for name, fl in cands:
        if len(fl) < 2: continue
        vals = sorted((value(f, C, zt, wt, Lb), i) for i, (f, lab) in enumerate(fl))
        if vals[1][0] - vals[0][0] <= TOL: continue
        i = vals[0][1]
        forms = [f for f, lab in fl]
        l1 = LK.strictly_least(Lb, forms, i)
        l2 = True if l1 else LK.strictly_least(Lc, forms, i)
        res.append([repr(name), repr(fl[i][1]), l1, l2])
    out.write(json.dumps({'class': r['class'], 'cell': r['cell'], 'res': res}) + '\n')
    out.flush()
    n += 1
    if n % 500 == 0: print(n, flush=True)
print('done', n)
