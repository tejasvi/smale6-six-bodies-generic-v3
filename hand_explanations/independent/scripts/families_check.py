"""Cell-level lemmas on the no-label cells of RESIDUAL 10 (families A, C by core hash; others = N1 and family B)."""
import json, os
from collections import Counter
A = {'96674494358ac0b5','7c60897cf0a47385','6fd2e5810bbf2a5f','9a753c1a541ced1d','ba6b8555b3facbb0','1e2248294818e876'}
Cc = {'9c5d5a0eb5274caf','c1343e65a5f12f68','9d52073c7df67ada','a7135526b888cf20','f88fb651a732d579','854f9cb97f452836','a942ebc464768f1a','9dc44c4284b43aee','2e39da8594e724c4','78d53510b38736e3','de05f2d8fe3db5f1','9861d60ca184c3e3','01c96ebcb817106e'}
mine, cov = {}, {}
for l in open('ref_resid_cover.jsonl'):
    r = json.loads(l); mine[(r['class'], r['cell'])] = r
for l in open('ref_cover.jsonl'):
    r = json.loads(l); cov[(r['class'], r['cell'])] = r
fam = Counter()
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'residual', 'data', 'nolabel_cells.jsonl')):
    r = json.loads(l); k = (r['class'], r['cell'])
    f = 'A' if r['hash'] in A else ('C' if r['hash'] in Cc else 'other (N1, B)')
    m = mine[k]; fl = []
    if m['L']: fl.append('L')
    if m['W3']: fl.append('W3')
    if any(w[2] in ('alpha', 'beta') for w in m['R1s']): fl.append('R1*')
    if cov[k]['E1']: fl.append('E1')
    if cov[k]['C']: fl.append('C')
    if cov[k]['Eclass']: fl.append('E')
    fam[(f, tuple(fl))] += 1
for k, v in sorted(fam.items()): print(k, v)
print('family A cells with L:', sum(v for k, v in fam.items() if k[0] == 'A' and 'L' in k[1]), 'of', sum(v for k, v in fam.items() if k[0] == 'A'))
print('family C cells with R1*:', sum(v for k, v in fam.items() if k[0] == 'C' and 'R1*' in k[1]), 'of', sum(v for k, v in fam.items() if k[0] == 'C'))
