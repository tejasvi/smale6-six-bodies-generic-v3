"""Shape of the minimal torque term (p carries z, q carries w) relative to O in each tree."""
import json, sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from collections import Counter
TOL = 1e-4
INF = float('inf')
def zshape(T, p, q):
    t = T.meet(p, q)
    if t is None: return 'same-leaf'
    if T.leaf[p] == T.leaf[O]: return 'p-at-O'
    u = T.meet(p, O)
    below_t = t in T.anc(T.leaf[O])
    if not below_t: return 'farclu'
    if u == t: return 'outer'
    return 'inner'
uniq = {}
for l in open('../data/uniq_interior.jsonl'):
    r = json.loads(l)
    uniq[(r['class'], r['cell'])] = r['uniq']
res = Counter(); res_cls = Counter()
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    u = uniq[(r['class'], r['cell'])]
    tor = [x for x in u if x[0] == 'T']
    if not tor: continue
    C = Cell(r)
    # take the torque with smallest |J| (canonical) as representative
    x = min(tor, key=lambda x: min(len(x[1]), 6 - len(x[1])))
    typ, k, l = x[2]
    p, q = (k, l) if typ == 'T1' else (l, k)   # p carries z, q carries w
    sz = zshape(C.zt, p, q); sw = zshape(C.wt, q, p)
    key = (sz, sw)
    key = tuple(sorted(key))  # colour symmetry
    res[key] += 1
for k, v in res.most_common(): print(v, k)
