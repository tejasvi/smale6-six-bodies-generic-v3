"""Remaining cells after Lemmas T, P, S; categorized by the L2 identity kinds available."""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import lemma_T, lemma_P, lemma_S
from collections import Counter
cls = load_classes()
lev = {}
for l in open('../data/levels.jsonl'):
    r = json.loads(l); lev[(r['class'], r['cell'])] = r['res']
out = open('../data/remaining1.jsonl', 'w')
cnt = Counter()
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    key = (r['class'], r['cell'])
    if key not in lev: continue
    C = Cell(r); D = Diag(cls[r['class']])
    if lemma_P(C, D) or lemma_S(r): continue
    res = lev[key]
    kinds = set()
    for x in res:
        if not x[3]: continue
        nm = eval(x[0])
        kinds.add(nm[0] if nm[0] != 'T' else 'T%d' % min(len(nm[1]), 6 - len(nm[1])))
    cnt[(r['class'], tuple(sorted(kinds)))] += 1
    out.write(json.dumps({'class': r['class'], 'cell': r['cell'], 'kinds': sorted(kinds)}) + '\n')
tot = sum(cnt.values())
print(tot)
for k, v in cnt.most_common(): print(v, k)
