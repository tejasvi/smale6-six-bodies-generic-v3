#!/usr/bin/env python3
"""Corroboration (not a proof) for alternative cores with no second-system certificate: Macaulay2 over QQ at random
rational mass points (all six masses specialized), Rabinowitsch variable for the same saturating factors.
A unit ideal over Q(m) must specialize to the unit ideal at random points (with probability 1).
Usage: m2_spec.py LIFT_ALT.jsonl OUT.jsonl ALT.jsonl [ALT.jsonl ...]"""
import json, os, random, re, subprocess, sys, tempfile
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
src, outp, alts = sys.argv[1], sys.argv[2], sys.argv[3:]
todo = {(json.loads(l)['class'], json.loads(l)['cell']) for l in open(src) if json.loads(l)['lift'] != 'ok'}
todo.add((30, 122))
items = [json.loads(l) for f in alts for l in open(f) if (json.loads(l)['class'], json.loads(l)['cell']) in todo]
work = os.path.join(os.path.dirname(os.path.abspath(outp)), 'spec_tmp')
def sats_of(vs):
    sats = list(vs); bynode = {}
    for v in vs:
        if v[0] in 'XY': bynode.setdefault(v.split('_')[0], []).append(v)
    for node, lst in bynode.items():
        for i in range(len(lst)):
            for j in range(i + 1, len(lst)): sats.append(f'({lst[i]}-{lst[j]})')
    return sats
rng = random.Random(17)
with open(outp, 'w') as f:
    for it in items:
        res = []
        for trial in range(2):
            ms = [f'{rng.randint(1, 97)}/{rng.randint(1, 97)}' for _ in range(6)]
            eqs = [re.sub(r'\bm(\d)\b', lambda mm: '(' + ms[int(mm.group(1))] + ')', e) for e in it['core_sym']]
            vs = sorted(set(VAR.findall(' '.join(eqs))))
            s = [f'R = QQ[{",".join(vs + ["tRab"])}];', f'I = ideal({",".join(eqs)});',
                 f'J = I + ideal(tRab*{"*".join(sats_of(vs))}-1);', 'G = gb J;',
                 'print(if (1_R % J) == 0 then "UNIT" else "NOTUNIT");', 'exit 0;']
            fd, path = tempfile.mkstemp(suffix='.m2', dir=work)
            with os.fdopen(fd, 'w') as fh: fh.write('\n'.join(s) + '\n')
            try:
                o = subprocess.run(['nice', '-n', '10', 'M2', '--script', path], capture_output=True, text=True, timeout=1800).stdout
            except subprocess.TimeoutExpired:
                o = 'TIMEOUT'
            os.unlink(path)
            res.append('notunit' if 'NOTUNIT' in o else 'unit' if 'UNIT' in o else 'timeout' if o == 'TIMEOUT' else 'error')
        f.write(json.dumps({'class': it['class'], 'cell': it['cell'], 'm2_random_points': res}) + '\n'); f.flush()
print('done')
