import json
from collections import Counter, defaultdict
ECLS = {3, 148, 149, 40, 150, 183}
tot = 0; Eany = 0; allmass = 0; union = 0; comp = Counter(); E1only = 0
genE = 0; genE_R = 0
kind = Counter()
for l in open('../data/coverage.jsonl'):
    r = json.loads(l); tot += 1
    L = r['lemmas']
    e = r['class'] in ECLS or L['E1']
    if e: Eany += 1
    if e or L['R1']: genE_R += 1
    am = L['T'] or L['P'] or L['C'] or L['B'] or (r['first'] in ('coreB', 'coreLIN-all', 'coreP4'))
    if am: allmass += 1
    if r['first'] == 'comp': comp[(r['class'], r['kind'], r['label'])] += 1
    kind[(r['kind'], am, e)] += 1
print('cells', tot)
print('E-class or E1 (generic E(T)):', Eany)
print('E/E1 or R1:', genE_R)
print('all-mass lemmas (T,P,C,B,coreB,coreLIN-all,coreP4):', allmass)
print('kind x allmass x E:', sorted(kind.items()))
print('comp', sum(comp.values()))
byc = Counter()
for (c, k, lab), v in comp.items(): byc[c] += v
print(sorted(byc.items(), key=lambda t: -t[1]))
for k, v in sorted(comp.items(), key=lambda t: -t[1])[:40]: print(v, k)
