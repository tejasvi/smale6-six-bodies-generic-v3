import json
from collections import Counter
best = Counter(); kinds = Counter(); bycls = Counter(); nothing = []
for l in open('../data/levels.jsonl'):
    r = json.loads(l)
    res = r['res']
    l1 = [x for x in res if x[2]]
    l2 = [x for x in res if x[3]]
    def kind(x):
        nm = eval(x[0])
        if nm[0] == 'T': return 'T%d' % min(len(nm[1]), 6 - len(nm[1]))
        if nm[0] == 'S': return 'S%d' % len(nm[2])
        return 'Ip'
    k1 = tuple(sorted(set(kind(x) for x in l1)))
    k2 = tuple(sorted(set(kind(x) for x in l2)))
    lev = 'L1' if l1 else ('L2' if l2 else 'none')
    best[lev] += 1
    kinds[(lev, k1 if l1 else k2)] += 1
    bycls[(r['class'], lev)] += 1
    if not l2: nothing.append((r['class'], r['cell']))
print(best)
for k, v in kinds.most_common(30): print(v, k)
print(sorted(bycls.items()))
print(len(nothing), nothing[:20])
