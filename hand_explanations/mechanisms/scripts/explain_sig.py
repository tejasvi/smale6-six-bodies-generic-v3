"""For remaining cells: the engine's single-term exclusion, and for each competitor term, the support of an LP
certificate of 'minimal term < competitor' (labels only). Prints the distinct support signatures."""
import json, sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from explain import *
from collections import Counter
cls = load_classes()
want_cls = int(sys.argv[1]); lim = int(sys.argv[2])
rem = set()
for l in open('../data/remaining2.jsonl'):
    r = json.loads(l)
    if r['class'] == want_cls: rem.add(r['cell'])
sigs = Counter(); n = 0
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    if r['class'] != want_cls or r['cell'] not in rem: continue
    D = Diag(cls[r['class']])
    L = build(r, D)
    C = L.C
    idn = eval(r['identity']); tm = eval(r['term'])
    def zf(k, l, col):
        if col == 'z': return lin((L.h('z', C.zt.meet(k, l)), -0.5), (L.h('w', C.wt.meet(k, l)), -1.5))
        return lin((L.h('z', C.zt.meet(k, l)), -1.5), (L.h('w', C.wt.meet(k, l)), -0.5))
    def pos(k, col):
        T = C.zt if col == 'z' else C.wt
        m = T.meet(k, 6); return None if m is None else L.h(col, m)
    terms = []
    if idn[0] == 'S':
        col, J = idn[1], idn[2]
        Jc = [j for j in range(6) if j not in J]
        for i in J:
            p = pos(i, col)
            if p is not None: terms.append((('SP', col, i), p))
        for i in J:
            for j in Jc: terms.append((('SC', col, i, j), zf(i, j, col)))
    elif idn[0] == 'T':
        J = idn[1]; Jc = [j for j in range(6) if j not in J]
        for k in J:
            for l in Jc:
                x3 = lin((L.h('z', C.zt.meet(k, l)), -1.5), (L.h('w', C.wt.meet(k, l)), -1.5))
                if pos(k, 'z') is not None and pos(l, 'w') is not None:
                    terms.append((('T1', k, l), lin((x3, 1), (pos(k, 'z'), 1), (pos(l, 'w'), 1))))
                if pos(k, 'w') is not None and pos(l, 'z') is not None:
                    terms.append((('T2', k, l), lin((x3, 1), (pos(k, 'w'), 1), (pos(l, 'z'), 1))))
    else:
        continue
    tmin = [f for lab, f in terms if lab == tm][0]
    allsup = set()
    for lab, f in terms:
        if lab == tm: continue
        ok, sup = explain(L, tmin, f)
        if not ok:
            print('NOT STRICT?', r['cell'], lab); continue
        kinds = tuple(sorted(set(x[1][0] + (':' + str(x[1][1][0]) + str(len(x[1][1])) if x[1][0].startswith('argmin') else '') for x in sup if x[1][0] not in ('claim-negation',))))
        allsup.add(kinds)
    sig = tuple(sorted(set(k for s in allsup for k in s)))
    sigs[sig] += 1
    n += 1
    if n >= lim: break
for k, v in sigs.most_common(): print(v, k)
