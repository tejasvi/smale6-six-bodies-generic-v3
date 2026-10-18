#!/usr/bin/env python3
"""Compare the referee's flags (ref_cover.jsonl) with concept/mechanisms/data/coverage.jsonl cell by cell."""
import json, os, sys
from collections import Counter
THEIRS = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'coverage.jsonl')
mine = {}
for l in open('ref_cover.jsonl'):
    r = json.loads(l)
    mine[(r['class'], r['cell'])] = r
theirs = {}
for l in open(THEIRS):
    r = json.loads(l)
    theirs[(r['class'], r['cell'])] = r
print('cells mine', len(mine), 'theirs', len(theirs), 'same keys', set(mine) == set(theirs))
cmp = {
    'T': lambda m: bool(m['Tlit']),
    'P': lambda m: m['P'] is not None,
    'C': lambda m: bool(m['C']),
    'B': lambda m: bool(m['B']),
    'E1': lambda m: bool(m['E1'] or m['E1u']),
    'R1': lambda m: bool(m['R1'] or m['R1v']),
    'R5': lambda m: bool(m['R5']),
    'R6': lambda m: bool(m['R6']),
    'Q': lambda m: bool(m['Q']),
}
for k, f in cmp.items():
    cnt = Counter()
    ex = []
    for key in mine:
        a, b = f(mine[key]), theirs[key]['lemmas'][k]
        cnt[(a, b)] += 1
        if a != b and len(ex) < 5:
            ex.append(key)
    print(k, 'mine/theirs', dict(cnt), 'disagree examples', ex)
# extra statistics
c = Counter()
for key, m in mine.items():
    c['Tlit'] += bool(m['Tlit'])
    c['Tdom'] += bool(m['Tdom'])
    c['Tlit_not_dom'] += bool(m['Tlit']) and not m['Tdom']
    c['Tdom_not_lit'] += bool(m['Tdom']) and not m['Tlit']
    c['E1main'] += bool(m['E1'])
    c['E1u_only'] += (not m['E1']) and bool(m['E1u'])
    c['R1main'] += bool(m['R1'])
    c['R1v_only'] += (not m['R1']) and bool(m['R1v'])
    c['Eclass'] += bool(m['Eclass'])
    c['Eclass_and_E1main'] += bool(m['Eclass']) and bool(m['E1'])
print(dict(c))
# witness consistency for T: every literal witness is also a domination witness?
bad = 0
for key, m in mine.items():
    dom = {(tuple(J), tuple(t)) for J, t in m['Tdom']}
    for J, t in m['Tlit']:
        if (tuple(J), tuple(t)) not in dom:
            bad += 1
print('literal-T witnesses not confirmed by domination:', bad)
print('E classes (mine):', sorted({k[0] for k, m in mine.items() if m['Eclass']}))
