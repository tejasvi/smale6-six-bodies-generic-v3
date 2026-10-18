import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import lemma_T, lemma_P
from collections import Counter
cls = load_classes()
lev = {}
for l in open('../data/levels.jsonl'):
    r = json.loads(l); lev[(r['class'], r['cell'])] = r['res']
cnt = Counter(); allP = Counter()
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    key = (r['class'], r['cell'])
    C = Cell(r); D = Diag(cls[r['class']])
    w = lemma_P(C, D)
    allP[w is not None] += 1
    if key not in lev: continue
    res = lev[key]
    ipl1 = any(x[0] == "('Ip',)" and x[2] for x in res)
    ipl2 = any(x[0] == "('Ip',)" and x[3] for x in res)
    cnt[(w is not None, ipl1, ipl2)] += 1
print('Lemma P on all single cells:', allP)
print('remaining cells (P?, Ip-L1, Ip-L2):', cnt)
