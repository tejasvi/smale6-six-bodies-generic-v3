#!/usr/bin/env python3
"""List the cells of the exact pipeline that are not certified, with the reason, from collected exact6 directories.
Writes engine/runs/UNCERTIFIED.txt and engine/runs/uncertified.json.
Usage: uncertified.py DIR [DIR ...]"""
import glob, json, os, re, sys, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tcorehash
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
CCMAP = {}
try:
    for r in json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'diagrams', 'cc_compare.json')))['per_cc']:
        CCMAP[r['ours']] = r['cc']
except Exception:
    pass


def canon_hash(eqs):
    order = []
    for e in eqs:
        for v in VAR.findall(e):
            if v not in order:
                order.append(v)
    ren = {v: f'v{i}' for i, v in enumerate(order)}
    ceqs = [VAR.sub(lambda mm: ren[mm.group(0)], e) for e in eqs]
    return hashlib.sha1('\n'.join(ceqs).encode()).hexdigest()[:16]


rows = []
for top in sys.argv[1:]:
    for d in sorted(glob.glob(os.path.join(top, 'exact6', 'c*'))):
        c = int(os.path.basename(d)[1:])
        cert = {}
        if os.path.exists(d + '/cert.jsonl'):
            for l in open(d + '/cert.jsonl'):
                r = json.loads(l)
                cert[r['hash']] = r['dim_Qm']
        resolved = set()
        sumx = {}
        for f in glob.glob(d + '/sec/p*.sec.jsonl'):
            for l in open(f):
                r = json.loads(l)
                sumx[r['cell']] = r['sumx']
                if 'excluded_by' in r:
                    resolved.add(r['cell'])
        corestat = {}
        for f in glob.glob(d + '/sec/p*.cores.jsonl'):
            for l in open(f):
                r = json.loads(l)
                if not r.get('verified_modp'):
                    corestat[r['cell']] = 'core not verified mod p'
                    continue
                ho, hn = tcorehash.hashes(r['core_sym'])
                h = hn if hn in cert else ho
                if cert.get(h) == -1:
                    resolved.add(r['cell'])
                else:
                    corestat[r['cell']] = f'core {h} not certified over Q(m) (dim {cert.get(h)})'
        for cell in sorted(sumx):
            if cell not in resolved:
                rows.append({'class': c, 'cc': CCMAP.get(c), 'cell': cell, 'sumx': sumx[cell],
                             'reason': corestat.get(cell, 'core search timed out (no core)')})
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs')
os.makedirs(out, exist_ok=True)
json.dump(rows, open(out + '/uncertified.json', 'w'), indent=0)
with open(out + '/UNCERTIFIED.txt', 'w') as f:
    f.write('# Cells of the exact generic pipeline (mode le, --base) that are not certified.\n')
    f.write('# Columns: engine class, Chang-Chen number, cell index (line of runs/exact6/cCLS/cells.jsonl on the box), '
            'sum x, reason.\n')
    for r in rows:
        f.write(f"{r['class']}\t{r['cc']}\t{r['cell']}\t{r['sumx']}\t{r['reason']}\n")
from collections import Counter
print(len(rows), 'uncertified cells;', Counter(r['reason'].split(' ')[0] + ' ' + r['reason'].split(' ')[1] for r in rows))
print(Counter(r['class'] for r in rows))
