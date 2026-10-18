import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import lemma_T
from collections import Counter
tt = {}
for l in open('../data/tt_torque.jsonl'):
    r = json.loads(l); tt[(r['class'], r['cell'])] = r['tt']
cnt = Counter()
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    C = Cell(r)
    w = lemma_T(C)
    a = w is not None; b = tt[(r['class'], r['cell'])] is not None
    cnt[(a, b)] += 1
print(cnt)
