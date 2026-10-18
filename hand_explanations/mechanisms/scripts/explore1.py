import json, itertools, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
cls = load_classes()
want_cls = int(sys.argv[1]); key = sys.argv[2]; step = int(sys.argv[3]); lim = int(sys.argv[4])
n = 0; shown = 0
for l in open('../data/single.jsonl'):
    r = json.loads(l)
    if r['class'] != want_cls or key not in r['identity']: continue
    n += 1
    if n % step != 1: continue
    C = Cell(r)
    print('cell', r['cell'], r['identity'], r['term'], 'sumx', r['sumx'])
    print('  z:', tree_str(C.zt)); print('  w:', tree_str(C.wt))
    print('  a:', [C.a(k) for k in range(6)], ' b:', [C.b(k) for k in range(6)])
    idn = eval(r['identity'])
    if idn[0] == 'T':
        tt = torque_terms(C, idn[1])
    elif idn[0] == 'S':
        tt = subset_terms(C, idn[2], idn[1])
    else:
        tt = []
    print('  terms:', [(round(e, 3), t) for e, t in tt[:6]])
    shown += 1
    if shown >= lim: break
