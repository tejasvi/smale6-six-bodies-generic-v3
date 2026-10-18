#!/usr/bin/env python3
"""Writes L6Check/F5/Data.lean: the stored cell lists data/cells/c<N>.jsonl of the 191 classes, the class file
data/f1/n6.json, the list data/cells/open43.tsv and data/cells/SHA256SUMS, embedded with include_str.
Usage: gen_data.py LEAN6_DIR"""
import os, sys
root = sys.argv[1]
out = os.path.join(root, 'L6Check', 'F5', 'Data.lean')
lines = ['/-!',
         '# The embedded data of the family F5',
         '',
         'The stored cells of the 191 classes (`data/cells/c<N>.jsonl`, one cell per line, the cell `k` on the line `k`,',
         'counted from `0`), the classes (`data/f1/n6.json`), the 43 open cells of Proposition 5.3',
         '(`data/cells/open43.tsv`) and the published digests of the cell files (`data/cells/SHA256SUMS`), embedded as',
         'strings. Written by `scripts/f5/gen_data.py`; the digests are checked in `L6Check.F5.Sha`.',
         '-/',
         '',
         'namespace L6F5.Data',
         '']
for c in range(191):
    lines.append(f'/-- `data/cells/c{c}.jsonl`. -/')
    lines.append(f'def c{c} : String := include_str "../../data/cells/c{c}.jsonl"')
    lines.append('')
lines.append('/-- The stored cells of the classes `0, …, 190`. -/')
names = [f'c{c}' for c in range(191)]
body = []
cur = '  ['
for i, nm in enumerate(names):
    tok = nm + (', ' if i < len(names) - 1 else ']')
    if len(cur) + len(tok) > 118:
        body.append(cur.rstrip())
        cur = '   '
    cur += tok
body.append(cur)
lines.append('def files : List String :=')
lines.extend(body)
lines.append('')
lines.append('/-- The classes of labelled diagrams on six bodies (`data/f1/n6.json`). -/')
lines.append('def n6 : String := include_str "../../data/f1/n6.json"')
lines.append('')
lines.append('/-- The 43 open cells of Proposition 5.3 (`data/cells/open43.tsv`). -/')
lines.append('def open43 : String := include_str "../../data/cells/open43.tsv"')
lines.append('')
lines.append('/-- The digests of the cell files (`data/cells/SHA256SUMS`). -/')
lines.append('def sums : String := include_str "../../data/cells/SHA256SUMS"')
lines.append('')
lines.append('end L6F5.Data')
open(out, 'w').write('\n'.join(lines) + '\n')
print('wrote', out)
