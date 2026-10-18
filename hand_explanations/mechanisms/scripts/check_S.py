import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import lemma_T, lemma_S
from collections import Counter
lev = {}
for l in open('../data/levels.jsonl'):
    r = json.loads(l); lev[(r['class'], r['cell'])] = r['res']
cnt = Counter(); kinds = Counter(); ex = []
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    key = (r['class'], r['cell'])
    if key not in lev: continue
    w = lemma_S(r)
    res = lev[key]
    hasS = any(eval(x[0])[0] == 'S' and x[3] for x in res)
    cnt[(w is not None, hasS)] += 1
    if w is not None:
        kinds[(r['class'], w[0], len(w[1]))] += 1
    elif hasS and len(ex) < 5:
        ex.append(key)
print(cnt)
print(sorted(kinds.items(), key=lambda t: -t[1])[:20])
print(ex)
