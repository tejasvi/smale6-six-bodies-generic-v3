#!/usr/bin/env python3
"""The 43 certified cores without a label (Singular timeouts) and the cells that carry them; which satisfy
Lemma N1 of LABELS.md (as recorded by its coverage run is not stored, so we re-test N1 here: a centre-of-mass
relation whose positions are all equal by the tree), and which of the residual lemmas apply to their cells.
Output ../data/nolabel_cells.jsonl"""
import json, os, sys, ast
from collections import Counter, defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
import exactlp as X
import lemmas_resid as LR

CT = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'inputs', 'core_types.json')))
nol = {h for h, r in CT.items() if r.get('status') == 'nolabel'}
print('nolabel cores in core_types.json:', len(nol), 'cells', sum(CT[h]['count'] for h in nol))
cells = defaultdict(list)
for l in open(os.path.join(R.MECH, 'data', 'cores_h.jsonl')):
    r = json.loads(l)
    if r['certified'] is False:
        continue
    h = r.get('hash_old') or r.get('hash')
    if h in nol:
        cells[h].append((r['class'], r['cell'], r))
cov = {}
for l in open(os.path.join(R.MECH, 'data', 'coverage.jsonl')):
    if '"label": "L16:nolabel"' in l:
        r = json.loads(l)
        cov[(r['class'], r['cell'])] = r
print('cells with L16:nolabel in mechanisms coverage:', len(cov))
seen = set()
out = open(os.path.join(R.DATA, 'nolabel_cells.jsonl'), 'w')
stat = Counter()
for h in sorted(nol, key=lambda x: -CT[x]['count']):
    for c, i, rr in cells[h]:
        if (c, i) in seen:
            continue
        seen.add((c, i))
        rec = R.load_cell(c, i)
        D = X.Diag(R.classes()[c])
        C = LR.Ctx(rec, D)
        app = []
        for nm, fn in (('B0', LR.lemma_B0), ('K', LR.lemma_K), ('L', LR.lemma_L), ('R1*', LR.lemma_R1star),
                       ('W3', LR.lemma_W3), ('EQ2', LR.lemma_EQ2), ('TQ', LR.lemma_TQ)):
            w = fn(C)
            if w:
                app.append(nm)
        first = cov.get((c, i), {}).get('first')
        names = rr['names']
        out.write(json.dumps({'hash': h, 'class': c, 'cell': i, 'mech_first': first, 'resid_lemmas': app,
                              'names': names}) + '\n')
        stat[(tuple(app) if app else ('none',), first)] += 1
print(len(seen), 'cells')
for k, v in sorted(stat.items(), key=lambda t: -t[1]):
    print(v, k)
