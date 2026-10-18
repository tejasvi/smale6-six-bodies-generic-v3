import json, sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
want_cls = int(sys.argv[1]); kind = sys.argv[2]; arg = eval(sys.argv[3]); step = int(sys.argv[4]); lim = int(sys.argv[5])
cells = {}
for l in open('../data/uniq_interior.jsonl'):
    r = json.loads(l)
    if r['class'] != want_cls: continue
    for x in r['uniq']:
        if kind == 'T' and x[0] == 'T' and (tuple(x[1]) == arg or tuple(j for j in range(6) if j not in x[1]) == arg):
            cells[r['cell']] = x
        if kind == 'S' and x[0] == 'S' and x[1] == arg[0] and tuple(x[2]) == arg[1]:
            cells[r['cell']] = x
        if kind == 'Ip' and x[0] == 'Ip':
            cells[r['cell']] = x
n = 0; shown = 0
for l in open('../data/single.jsonl'):
    r = json.loads(l)
    if r['class'] != want_cls or r['cell'] not in cells: continue
    n += 1
    if n % step != 1: continue
    C = Cell(r)
    x = cells[r['cell']]
    print('cell', r['cell'], x, 'sumx', r['sumx'], ' engine:', r['identity'], r['term'])
    print('  z:', tree_str(C.zt)); print('  w:', tree_str(C.wt))
    if x[0] == 'T':
        tt = torque_terms(C, x[1])
    elif x[0] == 'S':
        tt = subset_terms(C, x[2], x[1])
    else:
        tt = sorted([(C.a(k) + C.b(k), ('V0', k)) for k in range(6)])
    print('  terms:', [(round(e, 3), t) for e, t in tt[:6]])
    shown += 1
    if shown >= lim: break
