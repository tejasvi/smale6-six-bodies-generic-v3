#!/usr/bin/env python3
"""Copies the stored cell lists of the 191 classes (results/exact6/c<N>/cells.jsonl of the supplement) byte for byte to
data/cells/c<N>.jsonl, and writes data/cells/parts.tsv (class, part, number of lines of rep/p<part>.jsonl, the
replay counters lp and pruned of that part) and data/cells/SHA256SUMS. Untrusted helper: Lean re-checks everything.
Usage: copy_cells.py SUPPLEMENT_ROOT OUT_DIR"""
import glob, hashlib, json, os, shutil, sys
src, out = sys.argv[1], sys.argv[2]
rows, sums = [], []
for c in range(191):
    ds = glob.glob(os.path.join(src, '*', 'exact6', f'c{c}'))
    assert len(ds) == 1, (c, ds)
    d = ds[0]
    cells = open(os.path.join(d, 'cells.jsonl'), 'rb').read()
    lex = sorted(range(384), key=lambda k: f'p{k}.jsonl')
    cat = b''.join(open(os.path.join(d, 'rep', f'p{k}.jsonl'), 'rb').read() for k in lex)
    assert cat == cells, c
    dst = os.path.join(out, f'c{c}.jsonl')
    shutil.copyfile(os.path.join(d, 'cells.jsonl'), dst)
    sums.append((hashlib.sha256(cells).hexdigest(), f'c{c}.jsonl'))
    for k in range(384):
        lines = open(os.path.join(d, 'rep', f'p{k}.jsonl'), 'rb').read().count(b'\n')
        r = json.load(open(os.path.join(d, 'rep', f'p{k}.jsonl.replay.json')))
        rows.append((c, k, lines, r['cert']['lp'], r['cert']['pruned'], r['cert']['fail']))
with open(os.path.join(out, 'parts.tsv'), 'w') as f:
    f.write('class\tpart\tlines\tlp\tpruned\tfail\n')
    for r in rows:
        f.write('\t'.join(map(str, r)) + '\n')
with open(os.path.join(out, 'SHA256SUMS'), 'w') as f:
    for h, n in sums:
        f.write(f'{h}  {n}\n')
print('classes', len(sums), 'parts', len(rows), 'lines', sum(r[2] for r in rows), 'lp', sum(r[3] for r in rows),
      'pruned', sum(r[4] for r in rows), 'fail', sum(r[5] for r in rows))
