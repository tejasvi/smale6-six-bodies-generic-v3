import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
cls = load_classes()
tt = {}
for l in open('../data/tt_torque.jsonl'):
    r = json.loads(l); tt[(r['class'], r['cell'])] = r['tt']
uq = {}
for l in open('../data/uniq_interior.jsonl'):
    r = json.loads(l); uq[(r['class'], r['cell'])] = r['uniq']
want = int(sys.argv[1]); step = int(sys.argv[2]); lim = int(sys.argv[3])
n = shown = 0
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    if r['class'] != want or tt[(r['class'], r['cell'])] is not None: continue
    n += 1
    if n % step != 1: continue
    C = Cell(r)
    kinds = sorted(set((x[0], tuple(x[1]) if x[0]=='T' else (x[1], tuple(x[2])) if x[0]=='S' else ()) for x in uq[(r['class'], r['cell'])]))
    print('cell', r['cell'], 'engine:', r['identity'], r['term'], 'sumx', r['sumx'])
    print('   uniq-interior:', kinds[:8])
    print('  z:', tree_str(C.zt)); print('  w:', tree_str(C.wt))
    print('  a+b:', [round(C.a(k) + C.b(k), 3) for k in range(6)])
    am = [(tuple(nm), [tuple(x) for x in labs]) for nm, labs in r['argmin'] if nm[0] in ('U', 'I')]
    print('  U/I argmin:', am)
    shown += 1
    if shown >= lim: break
