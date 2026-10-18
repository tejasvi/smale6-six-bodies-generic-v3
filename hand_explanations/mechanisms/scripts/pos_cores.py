import json, sys, os
from collections import Counter, defaultdict
ECLS = {3, 148, 149, 40, 150, 183}
want = sys.argv[1] if len(sys.argv) > 1 else None
ctype = {}
for l in open('../data/core_types.jsonl'):
    r = json.loads(l); ctype[r['hash']] = r
S = json.load(open('../data/core_types_summary.json'))
tnames = {}
for i, (k, v) in enumerate(sorted(S.items(), key=lambda t: -t[1]['cells'])): tnames[k] = 'L%d' % i
def abstract(nm):
    t = eval(nm)
    if t[0] == 'D' and len(t) == 3: return 'dist'
    if t[0] in ('z', 'w') and t[1] == 'S': return 'B' + t[0]
    if t[0] == 'S': return 'S%s%d' % (t[1], len(t[2]))
    if t[0] == 'T': return 'T%d' % min(len(t[1]), 6 - len(t[1]))
    if t[0] == 'V': return 'V%d' % len(t[1])
    if t[0] == 'D': return 'Diff' + t[1]
    return t[0]
pat = defaultdict(Counter); ex = {}; tc = Counter()
for l in open('../data/cores_h.jsonl'):
    r = json.loads(l)
    if r['class'] in ECLS or r['certified'] is not True: continue
    if want and str(r['class']) != want: continue
    h = r.get('hash_old') or r['hash']
    t = ctype.get(h)
    if t is None or t['status'] == 'none': continue
    a = tuple(sorted(abstract(x) for x in r['names'] if abstract(x) != 'dist'))
    a2 = tuple(sorted(x.replace('z', '#').replace('w', 'z').replace('#', 'w') for x in a))
    key = (tnames.get(t['type'], '?'), min(a, a2))
    pat[key][r['class']] += 1; tc[tnames.get(t['type'], '?')] += 1
    if key not in ex: ex[key] = r
print(sorted(tc.items(), key=lambda t: -t[1]))
for k, v in sorted(pat.items(), key=lambda t: -sum(t[1].values()))[:40]:
    print(sum(v.values()), k, dict(v))
