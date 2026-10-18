import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core_sigs import sig
from collections import Counter, defaultdict
ECLS = {3, 148, 149, 40, 150, 183}
fam = {}
for l in open('../data/corefam.jsonl'):
    r = json.loads(l); fam[(r['class'], r['cell'])] = r['fam']
pat = {}
for l in open('../data/core_pat_ids.jsonl'):
    r = json.loads(l); pat[(r['class'], r['cell'])] = (r['pattern'], r['label'])
c = Counter(); bycls = Counter()
for k, f in fam.items():
    if k[0] in ECLS or f is not None: continue
    p, lab = pat[k]
    c[(lab, sig(p))] += 1; bycls[(k[0], lab)] += 1
tot = sum(c.values()); print(tot)
for k, v in c.most_common(45): print(v, k)
print(sorted(bycls.items(), key=lambda t: -t[1])[:40])
