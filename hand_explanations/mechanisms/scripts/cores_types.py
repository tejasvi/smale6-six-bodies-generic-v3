"""Join certified cores with labels/positivity; canonical label type per core (as tlabtypes: non-monomial irreducible
factors of the generators, masses renamed); per type: count of cores/cells, example names and equations."""
import json, sys, os, itertools
from collections import Counter, defaultdict
import sympy as sp
R = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'inputs') + '/'
M = sp.symbols('m0:6'); X = sp.symbols('x0:6'); LOC = {str(v): v for v in M}
lab = {json.loads(l)['hash']: json.loads(l) for l in open(R + 'labels_all.jsonl')}
pos = {json.loads(l)['hash']: json.loads(l) for l in open(R + 'pos_all.jsonl')}
cert = {json.loads(l)['hash']: json.loads(l) for l in open(R + 'certified_cores.jsonl')}
def ltype(L):
    gens = [sp.sympify(g.replace('^', '**'), locals=LOC) for g in L['gens']]
    gfac = []
    for g in gens:
        fl = sp.factor_list(g)[1]
        fs = sorted(set(sp.expand(f) for f, e in fl if not sp.Poly(f, *M).is_monomial and not f.is_number), key=str)
        gfac.append(fs)
    involved = sorted({str(s) for fs in gfac for f in fs for s in f.free_symbols})
    best = None; bestperm = None
    for perm in itertools.permutations(range(len(involved))):
        sub = {LOC[involved[i]]: X[perm[i]] for i in range(len(involved))}
        rep = sorted(sorted(str(sp.expand(f.subs(sub, simultaneous=True))) for f in fs) for fs in gfac)
        key = json.dumps(rep)
        if best is None or key < best:
            best = key; bestperm = {involved[i]: 'x%d' % perm[i] for i in range(len(involved))}
    return best, bestperm
out = open('../data/core_types.jsonl', 'w')
types = defaultdict(lambda: {'cores': 0, 'cells': 0, 'status': Counter(), 'ex': []})
for h, c in cert.items():
    L = lab[h]; st = pos[h]['status']
    if L.get('timeout') or not L.get('gens'):
        t, perm = 'NOLABEL', {}
    else:
        t, perm = ltype(L)
    d = types[t]; d['cores'] += 1; d['cells'] += c['count']; d['status'][st] += 1
    if len(d['ex']) < 2: d['ex'].append((h, perm, c['eqs'], L['gens']))
    out.write(json.dumps({'hash': h, 'type': t, 'perm': perm, 'status': st, 'count': c['count'], 'classes': c.get('classes')}) + '\n')
json.dump({k: {'cores': v['cores'], 'cells': v['cells'], 'status': dict(v['status']), 'ex': v['ex']} for k, v in types.items()},
          open('../data/core_types_summary.json', 'w'), indent=1)
for k, v in sorted(types.items(), key=lambda t: -t[1]['cells']):
    print(v['cells'], v['cores'], dict(v['status']), k[:150])
