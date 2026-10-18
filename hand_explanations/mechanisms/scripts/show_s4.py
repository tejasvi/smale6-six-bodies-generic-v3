import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import argmins
from collections import Counter
cov = {}
for l in open('../data/coverage.jsonl'):
    r = json.loads(l)
    if r['kind'] == 'single' and r['engine_single'][0].startswith("('S'") and "SP" in r['engine_single'][1]:
        cov[(r['class'], r['cell'])] = r
print(Counter(k[0] for k in cov), Counter(r['first'] for r in cov.values()))
n = 0
for l in open('../data/single.jsonl'):
    r = json.loads(l)
    if (r['class'], r['cell']) not in cov: continue
    n += 1
    if n % 60 != 1: continue
    C = Cell(r)
    print(r['class'], r['cell'], r['identity'], r['term'])
    print('  z:', tree_str(C.zt)); print('  w:', tree_str(C.wt))
    idn = eval(r['identity'])
    print('  terms:', [(round(e, 3), t) for e, t in subset_terms(C, idn[2], idn[1])[:6]])
    A = argmins(r)
    print('  ', {str(k): sorted(v) for k, v in A.items() if k[0] == idn[1]})
