import json, sys, os, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from explain import build, lin, explain
cls = load_classes()
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
want_cls = int(sys.argv[1]); nmax = int(sys.argv[2])
cov = [json.loads(l) for l in open('../data/coverage.jsonl')]
cells = [r for r in cov if r['class'] == want_cls and r['first'] == 'comp' and r['kind'] == 'single'][:nmax]
d = glob.glob(os.path.join(ROOT, '*', 'exact6', 'c%d' % want_cls))[0]
lines = open(os.path.join(d, 'cells.jsonl')).readlines()
for r in cells:
    rec = json.loads(lines[r['cell']]); rec['class'] = want_cls
    D = Diag(cls[want_cls]); L = build(rec, D); C = L.C
    print('cell', r['cell'], r['engine_single'])
    print('  z:', tree_str(C.zt)); print('  w:', tree_str(C.wt))
    idn = eval(r['engine_single'][0]); tm = eval(r['engine_single'][1])
    J = idn[1]; Jc = [j for j in range(6) if j not in J]
    def zpos(k): m = C.zt.meet(k, 6); return None if m is None else L.h('z', m)
    def wpos(k): m = C.wt.meet(k, 6); return None if m is None else L.h('w', m)
    terms = []
    for k in J:
        for l in Jc:
            for a, b in ((k, l), (l, k)):
                if zpos(a) is None or wpos(b) is None: continue
                f = lin((zpos(a), 1), (wpos(b), 1), (L.h('z', C.zt.meet(a, b)), -1.5), (L.h('w', C.wt.meet(a, b)), -1.5))
                terms.append(((a, b), f))
    pq = (tm[1], tm[2]) if tm[0] == 'T1' else (tm[2], tm[1])
    f0 = [f for lab, f in terms if lab == pq][0]
    for lab, f in terms:
        if lab == pq: continue
        ok, sup = explain(L, f0, f)
        print('   vs', lab, ok, [ (round(w,3), s) for w, s in sup if s[0] != 'claim-negation'] if sup else None)
