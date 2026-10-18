import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellkit import *
from lemmas import lemma_T, lemma_P2, lemma_C, lemma_B
from collections import Counter
cls = load_classes()
ECLS = {3, 148, 149, 40, 150, 183}
first = Counter(); byc = Counter()
out = open('../data/single_status.jsonl', 'w')
for line in open('../data/single.jsonl'):
    r = json.loads(line)
    C = Cell(r); D = Diag(cls[r['class']])
    st = None
    if lemma_T(C): st = 'T'
    elif lemma_P2(C, D, r): st = 'P'
    elif lemma_C(C, r): st = 'C'
    elif lemma_B(C, D, r): st = 'B'
    else: st = 'none'
    first[(r['class'] in ECLS, st)] += 1
    out.write(json.dumps({'class': r['class'], 'cell': r['cell'], 'st': st}) + '\n')
print(sorted(first.items()))
