import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import argmins
want = [tuple(map(int, a.split(':'))) for a in sys.argv[1:]]
lev = {}
for l in open('../data/levels.jsonl'):
    r = json.loads(l); lev[(r['class'], r['cell'])] = r['res']
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    key = (r['class'], r['cell'])
    if key not in want: continue
    C = Cell(r)
    print('class', key, 'engine', r['identity'], r['term'], 'sumx', r['sumx'])
    print('  z:', tree_str(C.zt)); print('  w:', tree_str(C.wt))
    print('  levels:', lev.get(key))
    A = argmins(r)
    for k in sorted(A, key=str): print('   ', k, sorted(A[k]))
