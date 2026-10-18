import json, sys
from collections import Counter
want = eval(sys.argv[1]); lim = int(sys.argv[2])
def abstract(nm):
    t = eval(nm)
    if t[0] == 'D' and len(t) == 3: return 'dist'
    if t[0] in ('z', 'w') and t[1] == 'S': return 'B' + t[0]
    if t[0] == 'S': return 'S%s%d' % (t[1], len(t[2]))
    if t[0] == 'T': return 'T%d' % min(len(t[1]), 6 - len(t[1]))
    if t[0] == 'V': return 'V%d' % len(t[1])
    if t[0] == 'D': return 'Diff' + t[1]
    return t[0]
n = 0; byc = Counter()
for l in open('../data/cores_h.jsonl'):
    r = json.loads(l)
    a = tuple(sorted(abstract(x) for x in r['names']))
    a2 = tuple(sorted(x.replace('z', '#').replace('w', 'z').replace('#', 'w') for x in a))
    if min(a, a2) != want: continue
    byc[r['class']] += 1
    if n < lim:
        print(r['class'], r['cell'], r['names'])
        for e in r['core_sym']: print('     ', e)
    n += 1
print(n, sorted(byc.items(), key=lambda t: -t[1])[:15])
