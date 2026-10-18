import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from corefam import classify
from collections import Counter, defaultdict
ECLS = {3, 148, 149, 40, 150, 183}
pl = {}
for l in open('../data/core_pat_ids.jsonl'):
    r = json.loads(l); pl[(r['class'], r['cell'])] = r['label']
cnt = Counter(); labs = defaultdict(Counter)
out = open('../data/corefam.jsonl', 'w')
for l in open('../data/cores_h.jsonl'):
    r = json.loads(l)
    if r['certified'] is False: continue
    fam, lab = classify(r['names'], r['core_sym'])
    key = (r['class'], r['cell'])
    cnt[(r['class'] in ECLS, fam)] += 1
    if fam: labs[fam][(pl.get(key), str(lab)[:80])] += 1
    out.write(json.dumps({'class': r['class'], 'cell': r['cell'], 'fam': fam, 'lab': str(lab)}) + '\n')
print(sorted(cnt.items(), key=str))
for f in labs:
    print(f)
    for k, v in labs[f].most_common(25): print('   ', v, k)
