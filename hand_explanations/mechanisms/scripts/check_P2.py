import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import lemma_P2
from collections import Counter
cls = load_classes()
rem = {}
for l in open('../data/remaining1.jsonl'):
    r = json.loads(l); rem[(r['class'], r['cell'])] = r['kinds']
cnt = Counter(); allc = Counter()
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    key = (r['class'], r['cell'])
    C = Cell(r); D = Diag(cls[r['class']])
    w = lemma_P2(C, D, r)
    allc[w is not None] += 1
    if key in rem:
        cnt[(r['class'], tuple(rem[key]), w is not None)] += 1
print(allc)
for k, v in sorted(cnt.items()): print(k, v)
