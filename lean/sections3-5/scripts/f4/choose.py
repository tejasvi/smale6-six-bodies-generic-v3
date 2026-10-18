#!/usr/bin/env python3
"""Choose replacement cores for the cells whose stored core has no certificate: among the cores found for the cell
by altcore.py (logs/f4/altcore.jsonl, one record per try with the cell's own names and core polynomials), each with
F = -1 and with F = the least mass index occurring in it, those whose generator block has a verified certificate in
data/f4/certs/ or in RUN_DIR/extra_certs/ (where prune.py moves unused files); the one with the smallest file is
taken (ties: F = -1 first, then fewer variables, then the try).
Writes data/f4/replacements.jsonl for collect.py --replace.
Usage: choose.py RUN_DIR HARDCELLS.txt
HARDCELLS.txt: lines "class cell certid F" of the cells and their stored cores (from the links of collect.py)."""
import json
import os
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import collect as C  # noqa: E402


def main():
    run, hard = sys.argv[1], sys.argv[2]
    certs = {}
    for d in (os.path.join(run, 'data', 'f4', 'certs'), os.path.join(run, 'extra_certs')):
        if not os.path.isdir(d):
            continue
        for f in os.listdir(d):
            cid = f.split('.')[0]
            s = os.path.getsize(os.path.join(d, f))
            certs[cid] = min(s, certs.get(cid, 1 << 62))
    cells = {}
    for ln in open(hard):
        c, cell, cid, F = ln.split()
        cells[(int(c), int(cell))] = cid
    tries = defaultdict(list)
    for ln in open(os.path.join(run, 'logs', 'f4', 'altcore.jsonl')):
        r = json.loads(ln)
        if r['status'] == 'core':
            tries[(r['class'], r['cell'])].append(r)
    out = []
    stats = Counter()
    for key in sorted(cells):
        if cells[key] in certs:
            continue
        opts = []
        for r in tries[key]:
            for F in sorted({C.fixed_mass(r['core_sym']), -1}):
                cid, block, ren = C.build_core(r['core_sym'], F, stats)
                if cid in certs:
                    opts.append((certs[cid], F >= 0, len(ren), r['try'], cid, F, r))
        if not opts:
            print('no certified candidate for', key, file=sys.stderr)
            continue
        size, _, _, t, cid, F, r = min(opts, key=lambda o: o[:4])
        out.append({'class': key[0], 'cell': key[1], 'names': r['names'], 'core_sym': r['core_sym'], 'fixed': F,
                    'source': f'altcore-try{t}', 'certid': cid, 'cert_file_bytes': size})
    with open(os.path.join(run, 'data', 'f4', 'replacements.jsonl'), 'w') as fh:
        for r in out:
            fh.write(json.dumps(r) + '\n')
    print(len(out), 'replacements')


if __name__ == '__main__':
    main()
