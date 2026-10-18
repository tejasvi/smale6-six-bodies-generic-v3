import json, os
from collections import Counter
theirs = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'residual', 'data', 'global_cover.jsonl')):
    r = json.loads(l); theirs[(r['class'], r['cell'])] = set(r['resid_lemmas'])
resid_keys = set()
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'residual', 'data', 'resid_cover.jsonl')):
    r = json.loads(l); resid_keys.add((r['class'], r['cell']))
mine = {}
for l in open('ref_resid_cover.jsonl'):
    r = json.loads(l)
    f = set()
    for n in ('B0', 'K', 'L', 'W3', 'EQ2'):
        if r[n]: f.add(n)
    if any(w[2] in ('alpha', 'beta') for w in r['R1s']): f.add('R1*')
    mine[(r['class'], r['cell'])] = f
for n in ('B0', 'K', 'L', 'R1*', 'W3', 'EQ2'):
    cnt = Counter(); ex = []
    for k in mine:
        if k in resid_keys:
            continue      # residual cells: theirs merges LP-based witnesses
        a, b = n in mine[k], n in theirs[k]
        cnt[(a, b)] += 1
        if a != b and len(ex) < 4: ex.append(k)
    print(n, 'mine/theirs (non-residual cells):', dict(cnt), ex)
