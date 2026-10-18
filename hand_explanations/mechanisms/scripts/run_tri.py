import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import lemma_E1, lemma_R1
from collections import Counter
cls = load_classes()
ECLS = {3, 148, 149, 40, 150, 183}
fam = {}
for l in open('../data/corefam.jsonl'):
    r = json.loads(l); fam[(r['class'], r['cell'])] = r['fam']
pl = {}
for l in open('../data/core_pat_ids.jsonl'):
    r = json.loads(l); pl[(r['class'], r['cell'])] = r['label']
idx = {}
for l in open('../data/systems_index.jsonl'):
    r = json.loads(l); idx[(r['class'], r['cell'])] = r
# load cells for system cells (non-E classes only) by streaming cells.jsonl per class
import glob
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
cnt = Counter(); out = open('../data/tri_status.jsonl', 'w')
for d in sorted(glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*'))):
    c = int(d.rsplit('/c', 1)[1])
    if c in ECLS: continue
    p = os.path.join(d, 'cells.jsonl')
    if not os.path.exists(p): continue
    D = Diag(cls[c])
    for i, line in enumerate(open(p)):
        key = (c, i)
        if key not in idx: continue
        rec = json.loads(line); rec['class'] = c
        C = Cell(rec)
        e = lemma_E1(C, D, rec); rr = lemma_R1(C, D, rec)
        st = 'E1' if e else ('R1' if rr else None)
        cnt[(fam.get(key), pl.get(key, 'nocore'), st)] += 1
        out.write(json.dumps({'class': c, 'cell': i, 'E1': e, 'R1': rr}) + '\n')
for k, v in sorted(cnt.items(), key=lambda t: -t[1])[:50]: print(v, k)
