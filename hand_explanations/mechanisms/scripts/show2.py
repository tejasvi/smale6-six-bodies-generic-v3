import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import argmins
cl = int(sys.argv[1]); kind = sys.argv[2]; step = int(sys.argv[3]); lim = int(sys.argv[4])
rem = {}
for l in open('../data/remaining1.jsonl'):
    r = json.loads(l)
    if r['class'] == cl and kind in r['kinds']: rem[r['cell']] = r
lev = {}
for l in open('../data/levels.jsonl'):
    r = json.loads(l)
    if r['class'] == cl: lev[r['cell']] = r['res']
n = shown = 0
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    if r['class'] != cl or r['cell'] not in rem: continue
    n += 1
    if n % step != 1: continue
    C = Cell(r)
    print('cell', r['cell'], 'engine', r['identity'], r['term'], 'sumx', r['sumx'])
    print('  z:', tree_str(C.zt)); print('  w:', tree_str(C.wt))
    print('  a+b:', [round(C.a(k) + C.b(k), 3) for k in range(6)], ' x:', {k: v for k, v in r['x'].items()})
    print('  L2:', [x[:2] for x in lev[r['cell']] if x[3]])
    A = argmins(r)
    print('  ', {str(k): sorted(v) for k, v in A.items() if k[0] in ('U', 'I')})
    print('  ', {str(k): sorted(v) for k, v in A.items() if k[0] in ('z', 'w')})
    shown += 1
    if shown >= lim: break
