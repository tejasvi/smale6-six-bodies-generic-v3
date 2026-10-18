import json, sys, os
from collections import Counter, defaultdict
P = json.load(open('../data/core_patterns.json'))
def sig(pattern):
    rels = [eval(x) for x in eval(pattern)]
    out = []
    for r in rels:
        k = r[0]
        if k == 'dist': continue
        if k == 'bal': out.append('bal%s%s%d' % (r[1], '+p' if r[3] else '', len(r[4])))
        elif k == 'sum': out.append('sum%s|J%d|p%d|L%d|f%d' % (r[1], len(r[2]), len(r[3]), r[4], len(r[5])))
        elif k == 'U': out.append('U%d%s' % (len(r[1]), '+E' if r[2] else ''))
        elif k == 'V': out.append('V|p%d|zw%d|t%d' % (len(r[2]), len(r[3]), r[4]))
        elif k == 'Diff': out.append('Diff%s%s|f%d' % (r[1], '+sep' if r[3] else '', len(r[4])))
        elif k in ('Ip', 'I'): out.append('%s%d%s' % (k, len(r[1]), '+E' if r[2] else ''))
        elif k == 'T': out.append('T%d' % len(r[2]))
        else: out.append(str(r))
    # colour canonical
    a = tuple(sorted(out)); b = tuple(sorted(x.replace('z', '#').replace('w', 'z').replace('#', 'w') for x in out))
    return min(a, b)
if __name__ == "__main__":
  S = defaultdict(Counter)
  for p in P:
      S[sig(p['pattern'])].update(p['labels'])
  rows = sorted(S.items(), key=lambda t: -sum(t[1].values()))
  print(len(rows))
  for k, v in rows[:80]:
      print(sum(v.values()), dict(v), k)
