#!/usr/bin/env python3
"""Classes with a triangle of strokes of one colour that has exactly one circled vertex in that colour (excluded by
[AK12, Rule 2e]: the three separations of that colour have the same order). Usage: tri1.py N N_JSON [CC_MEMBERSHIP]"""
import itertools, json, sys
n = int(sys.argv[1])
cls = json.load(open(sys.argv[2]))['classes']
hits = []
for idx, c in enumerate(cls):
    E = {(int(k[0]), int(k[1])): v for k, v in c['edges'].items()}
    def has(a, b, bit):
        return (E.get((min(a, b), max(a, b)), 0) & bit) != 0
    why = []
    for bit, circ, col in ((1, set(c['zcircles']), 'z'), (2, set(c['wcircles']), 'w')):
        for t in itertools.combinations(range(n), 3):
            if all(has(a, b, bit) for a, b in itertools.combinations(t, 2)) and len(circ & set(t)) == 1:
                why.append(col + ''.join(map(str, t)))
    if why:
        hits.append((idx, why))
print(f'n={n}: {len(hits)} classes with a one-colour triangle with exactly one circle:', hits)
