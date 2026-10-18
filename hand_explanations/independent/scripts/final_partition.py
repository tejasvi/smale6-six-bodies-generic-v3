#!/usr/bin/env python3
"""Final per-cell classification by the weakest input needed (referee's flags), written to ../final_classification.jsonl"""
import json, os
from collections import Counter
exec(open('cumul_ref.py').read().split("F = {k: flags(k) for k in mine}")[0])
F = {k: flags(k) for k in mine}
cell_level_all = {'T', 'P', 'C', 'B', 'B0', 'K', 'L'}
cell_level_gen = {'E', 'E1', 'R1', 'R5', 'R6', 'Q', 'R1s', 'W3', 'EQ2'}
sec = {(4, 58): 'R1*gamma', (28, 0): 'R1*gamma', (53, 1): 'R1*gamma', (0, 0): 'TQ'}
out = open('../final_classification.jsonl', 'w')
cnt = Counter()
for k in sorted(F):
    f = F[k]
    t = mech[k]['first']
    rec = {'class': k[0], 'cell': k[1], 'kind': mech[k]['kind']}
    allmass_cl = sorted(f & cell_level_all)
    gen_cl = sorted(f & cell_level_gen)
    tmpl = t if t.startswith('core') else None
    if allmass_cl:
        tier = 'A1 every-mass cell-level'
    elif tmpl in ('coreP4', 'coreLIN-all', 'coreB'):
        tier = 'A2 every-mass template (secondary identities)'
    elif k == (15, 0):
        tier = 'A3 every-mass exact torque certificate (TD)'
    elif gen_cl:
        tier = 'G1 generic cell-level'
    elif k in sec:
        tier = 'G2 generic, one secondary identity (exact cert)'
    elif tmpl:
        tier = 'G3 generic template LIN (secondary identities)'
    elif k[0] in DCLASS:
        tier = 'D paper sections 6-7 only'
    else:
        tier = 'NONE'
    rec.update({'tier': tier, 'cell_level_allmass': allmass_cl, 'cell_level_generic': gen_cl, 'template': tmpl,
                'secondary': sec.get(k), 'dclass': DCLASS.get(k[0])})
    out.write(json.dumps(rec) + '\n')
    cnt[tier] += 1
for k, v in sorted(cnt.items()):
    print('%-50s %d' % (k, v))
print('every positive mass total:', sum(v for k, v in cnt.items() if k.startswith('A')))
print('total:', sum(cnt.values()))
D = Counter((r['class']) for r in map(json.loads, open('../final_classification.jsonl')) if r['tier'].startswith('D'))
print('D by class:', dict(D))
# P needed for every-mass? cells whose only every-mass cell-level lemma is P
print('cells whose only every-mass cell-level lemma is P:', sum(1 for k in F if (F[k] & cell_level_all) == {'P'}))
print('cells whose only every-mass cell-level lemmas are within {B}:', sum(1 for k in F if (F[k] & cell_level_all) == {'B'}))
