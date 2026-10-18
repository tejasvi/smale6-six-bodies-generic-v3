#!/usr/bin/env python3
"""Macaulay2 re-check, with the first mass symbol of the core fixed to 1 (homogeneity), of the alternative cores whose
all-six-parameter M2 run timed out in recert_alt.py. Same saturating factors (Rabinowitsch variable).
Usage: m2_fix1.py RECERT_ALT.jsonl OUT.jsonl ALT.jsonl [ALT.jsonl ...] [--timeout S] [--jobs J]"""
import json, os, re, subprocess, sys, tempfile
import multiprocessing as mp

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
args = sys.argv[1:]
tmo = int(args[args.index('--timeout') + 1]) if '--timeout' in args else 3600
jobs = int(args[args.index('--jobs') + 1]) if '--jobs' in args else 18
pos = [a for i, a in enumerate(args) if not a.startswith('--') and (i == 0 or not args[i - 1].startswith('--'))]
rec, outp, alts = pos[0], pos[1], pos[2:]
work = os.path.join(os.path.dirname(os.path.abspath(outp)), 'm2fix1_tmp')
os.makedirs(work, exist_ok=True)


def sats_of(vs):
    sats = list(vs)
    bynode = {}
    for v in vs:
        if v[0] in 'XY':
            bynode.setdefault(v.split('_')[0], []).append(v)
    for node, lst in bynode.items():
        for i in range(len(lst)):
            for j in range(i + 1, len(lst)):
                sats.append(f'({lst[i]}-{lst[j]})')
    return sats


def m2_fix1(item):
    eqs = item['core_sym']
    ms = sorted(set(re.findall(r'\bm\d\b', ' '.join(eqs))))
    fix = ms[0]
    eqs1 = [re.sub(r'\b%s\b' % fix, '1', e) for e in eqs]
    par = [m for m in ms if m != fix]
    vs = sorted(set(VAR.findall(' '.join(eqs1))))
    prod = '*'.join(sats_of(vs))
    K = f'K = frac(QQ[{",".join(par)}]);' if par else 'K = QQ;'
    s = [K, f'R = K[{",".join(vs + ["tRab"])}];', f'I = ideal({",".join(eqs1)});', f'J = I + ideal(tRab*{prod}-1);',
         'G = gb J;', 'print(if (1_R % J) == 0 then "UNIT" else "NOTUNIT");', 'exit 0;']
    fd, path = tempfile.mkstemp(suffix='.m2', dir=work)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    try:
        out = subprocess.run(['nice', '-n', '10', 'M2', '--script', path], capture_output=True, text=True, timeout=tmo)
        out = out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    os.unlink(path)
    res = 'notunit' if 'NOTUNIT' in out else 'unit' if 'UNIT' in out else ('timeout' if out == 'TIMEOUT' else 'error')
    return {'class': item['class'], 'cell': item['cell'], 'm2_fix1': res}


if __name__ == '__main__':
    mp.set_start_method('fork', force=True)
    todo = set()
    for l in open(rec):
        r = json.loads(l)
        if r['m2_all6'] != 'unit':
            todo.add((r['class'], r['cell']))
    items = []
    for f in alts:
        for l in open(f):
            r = json.loads(l)
            if (r['class'], r['cell']) in todo:
                items.append(r)
    print(len(items), 'cores to re-check', flush=True)
    with open(outp, 'w') as f, mp.Pool(min(jobs, max(1, len(items)))) as pool:
        for x in pool.imap_unordered(m2_fix1, items):
            f.write(json.dumps(x) + '\n')
            f.flush()
    print('done', flush=True)
