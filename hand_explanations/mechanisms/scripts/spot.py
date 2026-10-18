import json, sys, os, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import argmins
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
want = sys.argv[1]
picked = None
for l in open('../data/coverage.jsonl'):
    r = json.loads(l)
    if r['first'] == want:
        picked = r; break
c, i = picked['class'], picked['cell']
d = glob.glob(os.path.join(ROOT, '*', 'exact6', 'c%d' % c))[0]
rec = json.loads(open(os.path.join(d, 'cells.jsonl')).readlines()[i])
C = Cell(rec)
print('class', c, 'cell', i, 'witness', picked['witness'][want])
print('  z:', tree_str(C.zt)); print('  w:', tree_str(C.wt))
A = argmins(rec)
for k in sorted(A, key=str): print('   ', k, sorted(A[k]))
