import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coreparse import *
n = 0
for l in open('../data/cores_h.jsonl'):
    r = json.loads(l)
    n += 1
    if n % 4000 != 7: continue
    print(r['class'], r['cell'])
    for nm, e in zip(r['names'], r['core_sym']):
        rel = relation(nm, e)
        print('   ', nm, '->', rel)
        if any(x[0] == '?' for x in parse_eq(e)): print('      PARSE?', e)
