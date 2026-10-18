import json, sys, os, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from corefam import tri_template, classify
from cellkit import Cell
from lemmas import common_meet
from collections import Counter, defaultdict
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
cores = {}
for l in open('../data/cores_h.jsonl'):
    r = json.loads(l)
    if r['certified'] is False: continue
    k = (r['class'], r['cell'])
    if k not in cores or r['certified'] is True: cores[k] = r
lab = {}
for l in open('../data/coverage.jsonl'):
    r = json.loads(l)
    if r['kind'] == 'core': lab[(r['class'], r['cell'])] = r['label']
tab = defaultdict(Counter)
out = open('../data/corefam2.jsonl', 'w')
for d in sorted(glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*'))):
    c = int(d.rsplit('/c', 1)[1])
    need = {k[1] for k in cores if k[0] == c}
    if not need: continue
    for i, line in enumerate(open(os.path.join(d, 'cells.jsonl'))):
        if i not in need: continue
        rec = json.loads(line); C = Cell(rec)
        cr = cores[(c, i)]
        f, x = classify(cr['names'], cr['core_sym'])
        t = None
        if f is None:
            t = tri_template(cr['names'], cr['core_sym'], lambda T: common_meet(C.zt, T) is not None and common_meet(C.wt, T) is not None)
        fam = f if f else (t[0] if t else None)
        tab[lab[(c, i)]][fam] += 1
        out.write(json.dumps({'class': c, 'cell': i, 'fam': fam, 'lab': str(x) if f else str(t)}) + '\n')
for k, v in sorted(tab.items(), key=lambda x: -sum(x[1].values())): print(k, dict(v))
