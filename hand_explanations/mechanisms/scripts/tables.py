#!/usr/bin/env python3
"""Tables for MECHANISMS.md from data/coverage.jsonl (coverage.py), data/cores_h.jsonl, data/core_types.jsonl.
Writes data/tables.md."""
import json, os, sys, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter, defaultdict
from cellkit import Cell, Diag, load_classes, O

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')
ECLS = {3, 148, 149, 40, 150, 183}
out = []
P = out.append

cov = [json.loads(l) for l in open(os.path.join(DATA, 'coverage.jsonl'))]
N = len(cov)
P(f'cells: {N}')

# ---- T4: coverage by lemma
first = Counter(r['first'] for r in cov)
appl = Counter()
for r in cov:
    for k, v in r['lemmas'].items():
        if v:
            appl[k] += 1
    if r['class'] in ECLS:
        appl['E'] += 1
P('\n## first applicable (fixed order E, T, P, C, B, E1, R1, R5, R6, core templates, d-folders, comp)')
for k, v in sorted(first.items(), key=lambda t: -t[1]):
    P(f'| {k} | {v} |')
P('\n## cells where the lemma applies')
for k, v in sorted(appl.items(), key=lambda t: -t[1]):
    P(f'| {k} | {v} |')
allmass = sum(1 for r in cov if r['lemmas']['T'] or r['lemmas']['P'] or r['lemmas']['C'] or r['lemmas']['B']
              or r['first'] in ('coreB', 'coreLIN-all', 'coreP4'))
gen = sum(1 for r in cov if r['class'] in ECLS or r['lemmas']['E1'])
genR = sum(1 for r in cov if r['class'] in ECLS or any(r['lemmas'][k] for k in ('E1', 'R1', 'R5', 'R6', 'Q')))
P(f'\nall-positive-mass lemmas (T, P, C, B, coreB, coreLIN-all, coreP4): {allmass}')
P(f'E or E1 (generic E(T)): {gen}; E, E1, R1, R5 or R6: {genR}')
uni = sum(1 for r in cov if r['first'] != 'comp')
P(f'covered (any): {uni}; computational residue: {N - uni}')
E1inE = sum(1 for r in cov if r['class'] in ECLS and r['lemmas']['E1'])
P(f'E1 holds on {E1inE} of the {sum(1 for r in cov if r["class"] in ECLS)} cells of the E-classes')

# ---- T1: engine single-term exclusions
P('\n## engine single-term exclusions: identity type x term type -> lemmas')
tab = defaultdict(Counter)
for r in cov:
    if r['kind'] != 'single':
        continue
    idn = eval(r['engine_single'][0])
    tm = eval(r['engine_single'][1])
    it = idn[0]
    if it == 'T':
        it = 'T|J|=%d' % min(len(idn[1]), 6 - len(idn[1]))
    elif it == 'S':
        it = 'S|J|=%d' % len(idn[2])
    key = (it, tm[0])
    tab[key]['cells'] += 1
    L = r['lemmas']
    tab[key]['T'] += L['T']
    tab[key]['P'] += L['P']
    tab[key]['C'] += L['C']
    tab[key]['B'] += L['B']
    tab[key]['allmass'] += (L['T'] or L['P'] or L['C'] or L['B'])
    tab[key]['E/E1/R'] += (r['class'] in ECLS or L['E1'] or L['R1'] or L['R5'] or L['R6'] or L['Q'])
    tab[key]['comp'] += (r['first'] == 'comp')
P('| identity | minimal term | cells | T | P | C | B | T,P,C or B | E/E1/R1/R5/R6 | residue |')
for k, v in sorted(tab.items(), key=lambda t: -t[1]['cells']):
    P(f"| {k[0]} | {k[1]} | {v['cells']} | {v['T']} | {v['P']} | {v['C']} | {v['B']} | {v['allmass']} | {v['E/E1/R']} | {v['comp']} |")

# ---- T2: Lemma T witness shapes
P('\n## Lemma T witnesses: shape of (p, q) and of J')
cls = load_classes()
shapes = Counter()
jk = Counter()
single = {}
for l in open(os.path.join(DATA, 'single.jsonl')):
    rr = json.loads(l)
    single[(rr['class'], rr['cell'])] = rr
for r in cov:
    w = r['witness'].get('T')
    if not w:
        continue
    if isinstance(w, str):
        w = eval(w)
    J, (p, q) = w
    rec = single[(r['class'], r['cell'])]
    C = Cell(rec)
    D = Diag(cls[r['class']])
    def sh(T, a, b):
        t = T.meet(a, b)
        u = T.meet(a, O)
        if t not in T.anc(T.leaf[O]):
            return 'far-cluster'
        return 'outer' if u == t else 'inner'
    s1, s2 = sh(C.zt, p, q), sh(C.wt, q, p)
    shapes[tuple(sorted((s1, s2)))] += 1
    Js = set(J)
    Jc = set(range(6)) - Js
    small = min((Js, Jc), key=len)
    if len(small) == 3:
        prs = list(itertools.combinations(sorted(small), 2))
        if all(e in D.zs for e in prs):
            kind = 'z-triangle of the diagram'
        elif all(e in D.ws for e in prs):
            kind = 'w-triangle of the diagram'
        else:
            kind = 'other 3-set'
    else:
        kind = f'{len(small)}-set'
    jk[kind] += 1
for k, v in shapes.most_common():
    P(f'| {k} | {v} |')
for k, v in jk.most_common():
    P(f'| J: {k} | {v} |')

# ---- T3: cores by label type
P('\n## cores by label type (label_types.json numbering for the positive types)')
lt = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'inputs', 'label_types.json')))
S = json.load(open(os.path.join(DATA, 'core_types_summary.json')))
mine = {}
for i, (k, v) in enumerate(sorted(S.items(), key=lambda t: -t[1]['cells'])):
    mine['L%d' % i] = k
lt_index = {t['type']: i for i, t in enumerate(lt)}
lab_tab = defaultdict(Counter)
for r in cov:
    if r['kind'] != 'core':
        continue
    lab = r['label'] or 'nocore'
    lab_tab[lab]['cells'] += 1
    lab_tab[lab][r['first']] += 1
    lab_tab[lab]['E1any'] += (r['class'] in ECLS or r['lemmas']['E1'])
P('| my label id | label_types.json index | status | cells | first-applicable lemmas |')
for lab, v in sorted(lab_tab.items(), key=lambda t: -t[1]['cells']):
    lid = lab.split(':')[0]
    key = mine.get(lid)
    idx = lt_index.get(key, '-') if key else '-'
    rest = {k: c for k, c in v.items() if k not in ('cells', 'E1any')}
    P(f"| {lab} | {idx} | | {v['cells']} | {dict(sorted(rest.items(), key=lambda t: -t[1]))} ; E/E1 holds on {v['E1any']} |")

# ---- T5: per class
P('\n## per class: cells and first-applicable lemma')
pc = defaultdict(Counter)
for r in cov:
    pc[r['class']][r['first']] += 1
for c, v in sorted(pc.items(), key=lambda t: -sum(t[1].values())):
    P(f'| {c} | {sum(v.values())} | {dict(sorted(v.items(), key=lambda t: -t[1]))} |')

# ---- T6: residue
P('\n## computational residue')
res = Counter()
for r in cov:
    if r['first'] == 'comp':
        res[(r['class'], r['kind'], r['label'] or (r['engine_single'][0] if r['engine_single'] else None))] += 1
for k, v in sorted(res.items()):
    P(f'| {k[0]} | {k[1]} | {k[2]} | {v} |')
open(os.path.join(DATA, 'tables.md'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out[:60]))
