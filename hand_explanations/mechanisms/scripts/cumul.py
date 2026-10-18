import json
from collections import Counter
ECLS = {3, 148, 149, 40, 150, 183}
cov = [json.loads(l) for l in open('../data/coverage.jsonl')]
def has(r, k):
    if k == 'E': return r['class'] in ECLS
    if k in ('E1', 'R1', 'R5', 'R6', 'Q', 'T', 'P', 'C', 'B'): return r['lemmas'][k]
    if k == 'templ': return r['first'] in ('coreLIN-generic', 'coreLIN-all', 'coreP4', 'coreB')
    if k == 'dfold': return r['first'] in ('d64', 'd88', 'd98')
for order in (['E', 'E1', 'R1', 'R5', 'R6', 'Q', 'T', 'P', 'C', 'B', 'templ', 'dfold'],
              ['T', 'P', 'C', 'B', 'templ', 'E', 'E1', 'R1', 'R5', 'R6', 'Q', 'dfold']):
    seen = set(); line = []
    for k in order:
        new = sum(1 for i, r in enumerate(cov) if i not in seen and has(r, k))
        for i, r in enumerate(cov):
            if has(r, k): seen.add(i)
        line.append((k, new, len(seen)))
    print(order)
    for x in line: print('   ', x)
    print('   residue', len(cov) - len(seen))
