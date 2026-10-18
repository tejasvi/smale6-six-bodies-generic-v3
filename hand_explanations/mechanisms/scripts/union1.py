import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import lemma_T, lemma_P2, lemma_S
from collections import Counter
cls = load_classes()
cnt = Counter(); first = Counter(); byc = Counter(); rem = Counter()
out = open('../data/remaining2.jsonl', 'w')
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    C = Cell(r); D = Diag(cls[r['class']])
    t = lemma_T(C) is not None
    p = lemma_P2(C, D, r) is not None
    s = lemma_S(r) is not None
    cnt[(t, p, s)] += 1
    if t: first['T'] += 1
    elif p: first['P'] += 1
    elif s: first['S'] += 1
    else:
        first['none'] += 1; rem[r['class']] += 1
        out.write(json.dumps({'class': r['class'], 'cell': r['cell']}) + '\n')
print(sorted(cnt.items()))
print(first)
print(sorted(rem.items(), key=lambda t: -t[1]))
