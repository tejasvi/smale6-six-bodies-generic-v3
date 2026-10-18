"""Collect the first-pass cores (sec/p*.cores.jsonl) of all classes and the alternative cores (alt_out, alt3_out).
Output data/cores.jsonl: class, cell, names, core_sym, size, source."""
import glob, json, os
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')   # the supplement
out = open('../data/cores.jsonl', 'w')
n = 0
for d in sorted(glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*'))):
    c = int(d.rsplit('/c', 1)[1])
    for f in glob.glob(os.path.join(d, 'sec', 'p*.cores.jsonl')):
        for line in open(f):
            if not line.strip(): continue
            r = json.loads(line)
            if 'core_sym' not in r: continue
            out.write(json.dumps({'class': c, 'cell': r['cell'], 'names': r['names'], 'core_sym': r['core_sym'],
                                  'size': r['core_size'], 'verified_modp': r.get('verified_modp'), 'source': 'first'}) + '\n')
            n += 1
na = 0
for fn in ('alt_out.jsonl', 'alt3_out.jsonl'):
    for line in open(os.path.join(ROOT, 'results', fn)):
        r = json.loads(line)
        if r.get('certified'):
            out.write(json.dumps({'class': r['class'], 'cell': r['cell'], 'names': r['names'], 'core_sym': r['core_sym'],
                                  'size': len(r['core_sym']), 'source': fn}) + '\n')
            na += 1
print(n, na)
