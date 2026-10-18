import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import argmins
from explain import *
cls = load_classes()
cl = int(sys.argv[1]); key = sys.argv[2]; step = int(sys.argv[3]); lim = int(sys.argv[4])
rem = set()
for l in open('../data/remaining2.jsonl'):
    r = json.loads(l)
    if r['class'] == cl: rem.add(r['cell'])
n = shown = 0
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    if r['class'] != cl or r['cell'] not in rem or key not in r['identity']: continue
    n += 1
    if n % step != 1: continue
    C = Cell(r)
    print('cell', r['cell'], 'engine', r['identity'], r['term'], 'sumx', r['sumx'])
    print('  z:', tree_str(C.zt)); print('  w:', tree_str(C.wt))
    idn = eval(r['identity'])
    if idn[0] == 'T': tt = torque_terms(C, idn[1])
    else: tt = subset_terms(C, idn[2], idn[1])
    print('  terms:', [(round(e, 3), t) for e, t in tt[:6]])
    A = argmins(r)
    print('   bodyeq argmins:', {str(k): sorted(v) for k, v in A.items() if k[0] in ('z', 'w') and k[1] in (0, 1, 2)})
    print('   U/I:', {str(k): sorted(v) for k, v in A.items() if k[0] in ('U', 'I')})
    shown += 1
    if shown >= lim: break
