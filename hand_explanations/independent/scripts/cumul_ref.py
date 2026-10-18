#!/usr/bin/env python3
"""Cumulative coverage from the referee's own flags (ref_cover.jsonl, ref_resid_cover.jsonl), with the authors'
template classification (coverage.jsonl 'first' in coreB/coreLIN-*/coreP4) and the d-folder classes."""
import json, os
from collections import Counter
mech = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'coverage.jsonl')):
    r = json.loads(l); mech[(r['class'], r['cell'])] = r
mine = {}
for l in open('ref_cover.jsonl'):
    r = json.loads(l); mine[(r['class'], r['cell'])] = r
res = {}
for l in open('ref_resid_cover.jsonl'):
    r = json.loads(l); res[(r['class'], r['cell'])] = r
DCLASS = {124: 'd64', 143: 'd64', 127: 'd88', 147: 'd88', 133: 'd98', 131: 'd98', 31: 'd98', 132: 'd98'}
single = {k for k, r in mech.items() if r['kind'] == 'single'}
def flags(k):
    m = mine[k]; f = set()
    if m['Eclass']: f.add('E')
    for n in ('E1', 'R1', 'R5', 'R6', 'Q', 'P', 'C', 'B'):
        if m[n]: f.add(n)
    if m['Tlit']: f.add('T')
    t = mech[k]['first']
    if t.startswith('core'): f.add('tmpl'); f.add(t)
    if k[0] in DCLASS: f.add('dfold')
    r = res[k]
    for n in ('B0', 'K', 'L'):
        if r[n]: f.add(n)
    if any(w[2] in ('alpha', 'beta') for w in r['R1s']): f.add('R1s')
    if r['W3']: f.add('W3')
    if r['EQ2']: f.add('EQ2')
    return f
F = {k: flags(k) for k in mine}
def cumul(order, keys):
    cov = set(); out = []
    for name, test in order:
        new = {k for k in keys if k not in cov and test(F[k], k)}
        cov |= new
        out.append((name, len(new), len(cov)))
    return out
has = lambda *names: (lambda f, k: bool(f & set(names)))
keys = set(F)
gen = [('E', has('E')), ('E1', has('E1')), ('R1', has('R1')), ('R6', has('R6')), ('Q', has('Q')), ('T', has('T')),
       ('C', has('C')), ('P,B,R5', has('P', 'B', 'R5')), ('templates', has('tmpl')), ('d-folders', has('dfold'))]
print('generic-first (MECHANISMS lemmas):')
for x in cumul(gen, keys): print('  ', x)
rest = {k for k in keys if not any(t(F[k], k) for _, t in gen)}
print('residue after MECHANISMS:', len(rest), Counter((k[0], mech[k]['kind']) for k in rest))
resid_gen = [('B0', has('B0')), ('K', has('K')), ('L', has('L')), ('R1*(alpha/beta)', has('R1s')), ('W3', has('W3')), ('EQ2', has('EQ2'))]
print('residual lemmas on the residue:')
for x in cumul(resid_gen, rest): print('  ', x)
allm = [('T', has('T')), ('P', has('P')), ('C', has('C')), ('B', has('B')),
        ('tmpl all-mass', has('coreB', 'coreLIN-all', 'coreP4')), ('B0', has('B0')), ('K', has('K')), ('L', has('L'))]
print('every positive mass (cell-level and template):')
for x in cumul(allm, keys): print('  ', x)
print('every positive mass, single-term cells:')
for x in cumul(allm, single): print('  ', x)
# without templates (pure cell-level hand lemmas)
allm2 = [x for x in allm if x[0] != 'tmpl all-mass']
print('every positive mass, cell-level only (no engine cores):')
for x in cumul(allm2, keys): print('  ', x)
# template cells covered by any cell-level lemma (MECHANISMS or residual)?
tm = {k for k in keys if mech[k]['first'].startswith('core')}
cl = {k for k in tm if F[k] & {'B0', 'K', 'L', 'R1s', 'W3', 'EQ2'}}
print('template-first cells:', len(tm), Counter(mech[k]['first'] for k in tm))
print('  of which covered by a residual cell-level lemma:', len(cl), Counter(mech[k]['first'] for k in cl))
print('  by lemma:', Counter(x for k in cl for x in F[k] & {'B0', 'K', 'L', 'R1s', 'W3', 'EQ2'}))
left = tm - cl
print('  template cells with no cell-level lemma:', len(left), Counter(k[0] for k in left))
dc = {k for k in keys if mech[k]['first'] in ('d64', 'd88', 'd98')}
cd = {k for k in dc if F[k] & {'B0', 'K', 'L', 'R1s', 'W3', 'EQ2'}}
print('d-folder-first cells:', len(dc), 'covered by a residual cell-level lemma:', len(cd), Counter(k[0] for k in cd))
print('  d-folder cells with no cell-level lemma:', Counter((k[0], mech[k]['first']) for k in dc - cd))
print('==== partition of all cells by the weakest input needed ====')
cell_level = {'E', 'E1', 'R1', 'R5', 'R6', 'Q', 'T', 'P', 'C', 'B', 'B0', 'K', 'L', 'R1s', 'W3', 'EQ2'}
P1 = {k for k in keys if F[k] & cell_level}
sec = {(4, 58), (28, 0), (53, 1), (0, 0)}         # R1*(gamma), TQ: one secondary identity, exact certificate
P2 = {k for k in keys - P1 if k in sec}
P3 = {k for k in keys - P1 - P2 if k[0] in DCLASS}
P4 = {k for k in keys - P1 - P2 - P3 if 'tmpl' in F[k]}
P5 = keys - P1 - P2 - P3 - P4
print('cell-level hand lemma:', len(P1))
print('secondary identity with exact certificate (R1* gamma, TQ):', len(P2), sorted(P2))
print('d-folder whole-class theorems only:', len(P3), Counter((k[0], mech[k]['first']) for k in P3))
print('engine core template only (LIN/P4):', len(P4), Counter(mech[k]['first'] for k in P4))
print('   by class:', sorted(Counter(k[0] for k in P4).items()))
print('nothing:', len(P5))
json.dump({'P2': sorted(P2), 'P3': sorted(P3), 'P4': sorted(P4)}, open('partition.json', 'w'))
# generic vs every-mass among P1
allmass_cl = {'T', 'P', 'C', 'B', 'B0', 'K', 'L'}
print('P1 at every positive mass:', len({k for k in P1 if F[k] & allmass_cl}), '; P1 generic only:', len({k for k in P1 if not F[k] & allmass_cl}))
