import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from corefam import classify
from collections import Counter
cov = {}
for l in open('../data/coverage.jsonl'):
    r = json.loads(l)
    cov[(r['class'], r['cell'])] = r
c = Counter()
for l in open('../data/cores_h.jsonl'):
    r = json.loads(l)
    if r['certified'] is False: continue
    k = (r['class'], r['cell'])
    lab = cov[k]['label']
    if lab and 'L8' in lab:
        f, x = classify(r['names'], r['core_sym'])
        c[(cov[k]['first'], f)] += 1
print(c)
