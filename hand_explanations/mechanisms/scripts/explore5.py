"""Torque exclusions: does the minimal term minimize its z-part and its w-part separately (over all terms)?"""
import json, sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from collections import Counter
TOL = 1e-4
INF = float('inf')
def parts(C, J):
    Jc = [j for j in range(6) if j not in J]
    out = []
    for k in J:
        for l in Jc:
            z1 = C.a(k) - 1.5 * C.zeta(k, l); w1 = C.b(l) - 1.5 * C.omega(k, l)
            z2 = C.a(l) - 1.5 * C.zeta(k, l); w2 = C.b(k) - 1.5 * C.omega(k, l)
            out.append((z1 + w1, z1, w1, ('T1', k, l)))
            out.append((z2 + w2, z2, w2, ('T2', k, l)))
    return [t for t in out if t[0] < INF]
cnt = Counter(); bycls = Counter()
for l in open('../data/uniq_interior.jsonl'):
    r = json.loads(l)
    tor = [x for x in r['uniq'] if x[0] == 'T']
    if not tor: continue
    rec = None
    for l2 in []: pass
    cnt['cells_with_torque'] += 1
for line in open('../data/single.jsonl'):
    pass
# second pass: join
uniq = {}
for l in open('../data/uniq_interior.jsonl'):
    r = json.loads(l)
    uniq[(r['class'], r['cell'])] = r['uniq']
res = Counter()
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    u = uniq[(r['class'], r['cell'])]
    tor = [x for x in u if x[0] == 'T']
    if not tor: continue
    C = Cell(r)
    best = None
    for x in tor:
        pp = sorted(parts(C, x[1]))
        m = pp[0]
        zmin = min(p[1] for p in pp); wmin = min(p[2] for p in pp)
        zok = m[1] <= zmin + TOL; wok = m[2] <= wmin + TOL
        # strict simultaneous: every other term strictly larger in z or in w part
        strict = zok and wok and all((p[1] > m[1] + TOL or p[2] > m[2] + TOL) for p in pp[1:])
        tag = 'both' if strict else ('z' if zok else ('w' if wok else 'none'))
        if best is None or ['none', 'w', 'z', 'both'].index(tag) > ['none', 'w', 'z', 'both'].index(best):
            best = tag
    res[best] += 1
print(res)
