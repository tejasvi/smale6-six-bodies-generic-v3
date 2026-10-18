#!/usr/bin/env python3
"""Summary of ../data/coreC_sub.txt (class-29 I-core branches restricted to one triangle) -> ../data/coreC_sub_table.md"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coreC_table import classify
DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')
txt = open(os.path.join(DATA, 'coreC_sub.txt')).read()
out = ['| core | branch (centre relation) | triangle | relations kept | condition |', '|---|---|---|---|---|']
cnt = {}
for block in txt.split('=== core ')[1:]:
    h = block.split()[0]
    for br in block.split('--- branch ')[1:]:
        first = br.split('\n')[0]
        phi = first.split(' = 0')[0]
        tri = re.search(r'triangle (\[[^\]]*\])', first).group(1)
        kept = first.split('kept: ')[1]
        gens = br.split('\n', 1)[1].split('[1]:')[1:]
        conds = []
        for g in gens:
            facs = re.findall(r'_\[\d+\]=(.*)', g)
            conds.append(classify(facs))
        c = ' / '.join(sorted(set(conds))) if 'TIMEOUT' not in br else 'TIMEOUT'
        cnt[c.split(':')[0]] = cnt.get(c.split(':')[0], 0) + 1
        out.append(f'| {h} | {phi} | {tri} | {kept} | {c} |')
open(os.path.join(DATA, 'coreC_sub_table.md'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
print(cnt)
