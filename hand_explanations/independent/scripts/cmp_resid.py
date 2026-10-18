import json, os
from collections import Counter
mech = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'coverage.jsonl')):
    r = json.loads(l); mech[(r['class'], r['cell'])] = r
theirs = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'residual', 'data', 'resid_cover.jsonl')):
    r = json.loads(l); theirs[(r['class'], r['cell'])] = r
mine = {}
for l in open('ref_resid_cover.jsonl'):
    r = json.loads(l); mine[(r['class'], r['cell'])] = r
resid = sorted(k for k, r in mech.items() if r['first'] == 'comp')
print('residual cells', len(resid), 'same as theirs:', set(resid) == set(theirs))
tab = Counter()
for k in resid:
    m = mine[k]
    mm = []
    for lem in ('B0', 'K', 'L', 'W3', 'EQ2', 'TQ'):
        if m[lem]: mm.append(lem)
    r1 = [w for w in m['R1s'] if w[2] in ('alpha', 'beta')]
    r1g = [w for w in m['R1s'] if w[2] == 'gamma?']
    if r1: mm.append('R1*ab')
    if r1g and not r1: mm.append('R1*gamma?')
    th = theirs[k]['applies']
    tab[(k[0], mech[k]['kind'], tuple(mm), tuple(th))] += 1
for k, v in sorted(tab.items()): print(k, v)
