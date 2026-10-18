import json, sys, os, glob, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from collections import Counter
cls = load_classes()
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
ncells = {}
for d in glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*')):
    c = int(d.rsplit('/c', 1)[1])
    p = os.path.join(d, 'cells.jsonl')
    n = sum(1 for _ in open(p)) if os.path.exists(p) else 0
    if n: ncells[c] = n
single = Counter()
for l in open('../data/single.jsonl'):
    single[json.loads(l)['class']] += 1
cc = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'diagrams', 'cc_compare.json')))
print(type(cc), list(cc.keys())[:5] if isinstance(cc, dict) else cc[:2])
def zwtri_ok(D):
    """zw-triangles with no circle at the vertices and no other stroke at the vertices."""
    out = []
    for T in itertools.combinations(range(6), 3):
        pairs = list(itertools.combinations(T, 2))
        if not all(p in D.zw for p in pairs): continue
        ok = True
        for v in T:
            if v in D.zc or v in D.wc: ok = False
            for e in D.zs | D.ws:
                if v in e and e not in pairs: ok = False
        out.append((T, ok))
    return out
for c in sorted(ncells, key=lambda c: -ncells[c]):
    D = Diag(cls[c])
    print(c, ncells[c], 'single', single[c], cls[c]['edges'], 'zc', cls[c]['zcircles'], 'wc', cls[c]['wcircles'], 'zwtri', zwtri_ok(D))
