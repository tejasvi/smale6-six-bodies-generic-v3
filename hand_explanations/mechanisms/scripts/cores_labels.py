import json, sys, os
from collections import Counter, defaultdict
R = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'inputs') + '/'
lab = {json.loads(l)['hash']: json.loads(l) for l in open(R + 'labels_all.jsonl')}
pos = {json.loads(l)['hash']: json.loads(l) for l in open(R + 'pos_all.jsonl')}
cert = {json.loads(l)['hash']: json.loads(l) for l in open(R + 'certified_cores.jsonl')}
print(len(lab), len(pos), len(cert))
st = Counter(); stcells = Counter()
for h, c in cert.items():
    s = pos.get(h, {}).get('status')
    st[s] += 1; stcells[s] += c['count']
print(st, stcells)
# the 'none' labels: what generators?
g = Counter()
for h, c in cert.items():
    if pos.get(h, {}).get('status') == 'none':
        L = lab[h]
        key = tuple(sorted(f.split(' ', 1)[1].rsplit(' ', 1)[0] for f in L['factors'] if not f.split(' ', 1)[1].startswith('1 ') and f.split(' ',1)[1].rsplit(' ',1)[0] not in ('1', '-1')))
        g[key] += c['count']
for k, v in g.most_common(30): print(v, k)
