"""Per cell status for all 91,273 cells: E-class, single (T/P2/S/rest), core (label status/type), alt, uncovered."""
import json, sys, os, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter, defaultdict
ECLS = {3, 148, 149, 40, 150, 183}
rem2 = set()
for l in open('../data/remaining2.jsonl'):
    r = json.loads(l); rem2.add((r['class'], r['cell']))
single = set()
for l in open('../data/single.jsonl'):
    r = json.loads(l); single.add((r['class'], r['cell']))
ctype = {}
for l in open('../data/core_types.jsonl'):
    r = json.loads(l); ctype[r['hash']] = r
cores = {}
for l in open('../data/cores_h.jsonl'):
    r = json.loads(l)
    key = (r['class'], r['cell'])
    if r['certified'] is True:
        h = r.get('hash_old') or r['hash']
        cores.setdefault(key, []).append(('first', h))
    elif r['certified'] == 'alt':
        cores.setdefault(key, []).append(('alt', None))
cnt = Counter(); bycls = defaultdict(Counter)
for l in open('../data/systems_index.jsonl'):
    r = json.loads(l)
    key = (r['class'], r['cell'])
    E = r['class'] in ECLS
    cs = cores.get(key, [])
    first = [h for s, h in cs if s == 'first']
    if first:
        t = ctype.get(first[0])
        st = 'core-' + (t['status'] if t else 'unknownhash')
    elif cs:
        st = 'core-alt'
    else:
        st = 'nocore'
    cnt[(E, st)] += 1
    if not E: bycls[r['class']][st] += 1
for key in single:
    E = key[0] in ECLS
    st = 'single-rest' if key in rem2 else 'single-TPS'
    cnt[(E, st)] += 1
    if not E: bycls[key[0]][st] += 1
for k, v in sorted(cnt.items()): print(k, v)
print(sum(cnt.values()))
for c in sorted(bycls, key=lambda c: -sum(bycls[c].values())):
    print(c, dict(bycls[c]))
