import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter, defaultdict
from cellkit import *
cls = load_classes()
per = defaultdict(Counter); tot = Counter()
for l in open('../data/uniq_interior.jsonl'):
    r = json.loads(l)
    c = r['class']; tot[c] += 1
    seen = set()
    for x in r['uniq']:
        if x[0] == 'T':
            J = tuple(x[1]); Jc = tuple(j for j in range(6) if j not in J)
            key = ('T', min(J, Jc, key=lambda s: (len(s), s)))
        elif x[0] == 'S':
            key = ('S', x[1], tuple(x[2]))
        else:
            key = ('Ip',)
        if key not in seen:
            per[c][key] += 1; seen.add(key)
for c in sorted(tot, key=lambda c: -tot[c]):
    print('class', c, cls[c]['edges'], 'zc', cls[c]['zcircles'], 'wc', cls[c]['wcircles'], 'cells', tot[c])
    print('   ', [(k, v) for k, v in per[c].most_common(12)])
