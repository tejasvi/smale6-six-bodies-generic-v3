import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from explain import *
cls = load_classes()
want = (int(sys.argv[1]), int(sys.argv[2]))
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    if (r['class'], r['cell']) == want: break
D = Diag(cls[r['class']])
L = build(r, D)
C = L.C
print('z:', tree_str(C.zt)); print('w:', tree_str(C.wt))
val, du, rows = solve(L)
print('cell feasible, max s =', val)
# S_z(W) term forms
def ez(k, l): return lin((L.h('z', C.zt.meet(k, l)), -0.5), (L.h('w', C.wt.meet(k, l)), -1.5))
def ew(k, l): return lin((L.h('z', C.zt.meet(k, l)), -1.5), (L.h('w', C.wt.meet(k, l)), -0.5))
def a(k): m = C.zt.meet(k, 6); return None if m is None else L.h('z', m)
def b(k): m = C.wt.meet(k, 6); return None if m is None else L.h('w', m)
exec(sys.argv[3])
