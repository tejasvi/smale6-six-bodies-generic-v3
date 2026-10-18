"""For each single-excluded cell: which identities (torques T_J, subset sums S_J both colours, Ip) have a unique
minimal term at the stored interior point. Output counts and a per-cell list (data/uniq_interior.jsonl)."""
import json, itertools, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from collections import Counter
TOL = 1e-4
subsets = [J for r in range(1, 6) for J in itertools.combinations(range(6), r)]
tor_sets = [J for J in subsets if 0 in J]
out = open('../data/uniq_interior.jsonl', 'w')
cnt = Counter(); cover = Counter(); n = 0
for l in open('../data/single.jsonl'):
    r = json.loads(l)
    C = Cell(r)
    res = []
    for J in tor_sets:
        tt = torque_terms(C, J)
        tt = [t for t in tt if t[0] < float('inf')]
        if len(tt) >= 2 and tt[1][0] - tt[0][0] > TOL:
            res.append(('T', J, tt[0][1]))
    for col in 'zw':
        for J in subsets:
            tt = subset_terms(C, J, col)
            tt = [t for t in tt if t[0] < float('inf')]
            if len(tt) >= 2 and tt[1][0] - tt[0][0] > TOL:
                res.append(('S', col, J, tt[0][1]))
    ip = sorted([C.a(k) + C.b(k) for k in range(6)])
    if ip[0] > TOL:
        res.append(('Ip',))
    kinds = set()
    for x in res:
        if x[0] == 'T':
            kinds.add('T%d' % min(len(x[1]), 6 - len(x[1])))
        elif x[0] == 'S':
            kinds.add('S%d' % len(x[2]))
        else:
            kinds.add('Ip')
    for k in kinds: cover[k] += 1
    cnt[tuple(sorted(kinds))] += 1
    out.write(json.dumps({'class': r['class'], 'cell': r['cell'], 'uniq': res}) + '\n')
    n += 1
print(n)
print('cells having a unique-min identity of kind:', dict(cover))
for k, v in cnt.most_common(40): print(v, k)
