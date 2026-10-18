#!/usr/bin/env python3
"""Account for our classes beyond Chang-Chen's list: the rules of ccrules.py plus Rule T (a one-colour triangle of
strokes has 0, 2 or 3 circled vertices of that colour: (O2) with (O5), or [AK12, Rule 2e]).
Usage: extra_account.py N_JSON CCRULES_JSON TRI1_CLASSES CC_COMPARE_JSON OUT_JSON"""
import json, sys
from collections import Counter
ours = json.load(open(sys.argv[1]))['classes']
rules = json.load(open(sys.argv[2]))
tri1 = set(json.loads(sys.argv[3]))
cmp_ = json.load(open(sys.argv[4]))
in_cc = {r['ours'] for r in cmp_['per_cc']}
fails = {}
for r in rules:
    f = set(x.rstrip('zw') if not x.startswith('T3.3d*') else 'T3.3d*' for x in r['fails'])
    f = {x[:-1] if x.endswith(('z', 'w')) else x for x in f}
    if r['class'] in tri1:
        f.add('RuleT')
    fails[r['class']] = f
bad_cc = [i for i in in_cc if fails[i]]
print('Chang-Chen classes failing some rule:', bad_cc)
extra = [i for i in range(len(ours)) if i not in in_cc]
unexpl = [i for i in extra if not fails[i]]
print(f'{len(extra)} extra classes; unexplained: {unexpl}')
sole = Counter(next(iter(fails[i])) for i in extra if len(fails[i]) == 1)
print('extra classes with a single failing rule, by rule:', dict(sole))
order = ['RuleT', 'T3.4b', 'T3.5a', 'T3.6', 'T3.8', 'T3.3c', 'T3.3e', 'T3.3d*']
first = Counter(next(x for x in order if x in fails[i]) for i in extra)
print('first failing rule in the order', order, ':', dict(first))
# a smallest set of rules that covers all extra classes (exhaustive over subsets of the rules that occur)
import itertools
occ = sorted({x for i in extra for x in fails[i]})
best = None
for r in range(1, len(occ) + 1):
    for S in itertools.combinations(occ, r):
        if all(fails[i] & set(S) for i in extra):
            best = S
            break
    if best:
        break
print('a smallest covering set of rules:', best)
json.dump({str(i): sorted(fails[i]) for i in extra}, open(sys.argv[5], 'w'), indent=1)
