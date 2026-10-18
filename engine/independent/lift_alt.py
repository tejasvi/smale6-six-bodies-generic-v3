#!/usr/bin/env python3
"""Explicit certificates for the alternative cores that Macaulay2 could not re-certify within the time limits:
Singular lift (talt's normalization: first mass symbol fixed to 1, the others parameters; Rabinowitsch variable for the
product of the saturating factors) gives cofactors with sum C_i g_i = 1; Macaulay2 checks the identity by polynomial
arithmetic only (no Groebner basis), which is independent of Singular's Groebner computation.
Usage: lift_alt.py M2FIX1.jsonl[,M2FIX1b.jsonl] OUT.jsonl ALT.jsonl [ALT.jsonl ...] [--timeout S] [--jobs J]"""
import json, os, re, subprocess, sys, tempfile, time
import multiprocessing as mp

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
args = sys.argv[1:]
tmo = int(args[args.index('--timeout') + 1]) if '--timeout' in args else 1800
jobs = int(args[args.index('--jobs') + 1]) if '--jobs' in args else 14
pos = [a for i, a in enumerate(args) if not a.startswith('--') and (i == 0 or not args[i - 1].startswith('--'))]
srcs, outp, alts = pos[0].split(','), pos[1], pos[2:]
work = os.path.join(os.path.dirname(os.path.abspath(outp)), 'lift_alt_tmp')
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


def run(cmd, text, suffix):
    fd, path = tempfile.mkstemp(suffix=suffix, dir=work)
    with os.fdopen(fd, 'w') as fh:
        fh.write(text)
    t = time.time()
    try:
        out = subprocess.run(['nice', '-n', '10'] + cmd + [path], capture_output=True, text=True, timeout=tmo)
        out = out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    os.unlink(path)
    return out, time.time() - t


def one(item):
    eqs = item['core_sym']
    ms = sorted(set(re.findall(r'\bm\d\b', ' '.join(eqs))))
    fix = ms[0]
    eqs1 = [re.sub(r'\b%s\b' % fix, '1', e) for e in eqs]
    par = [m for m in ms if m != fix]
    vs = sorted(set(VAR.findall(' '.join(eqs1))))
    prod = '*'.join(sats_of(vs))
    gens = eqs1 + [f'tRab*{prod}-1']
    allv = vs + ['tRab']
    ring = f'ring R = (0,{",".join(par)}), ({",".join(allv)}), dp;' if par else f'ring R = 0, ({",".join(allv)}), dp;'
    s = [ring, f'ideal J = {",".join(gens)};', 'matrix T = lift(J, ideal(1));', 'int i;',
         'for (i = 1; i <= ncols(J); i++) { print("C" + string(i) + " = " + string(T[i,1]) + ";"); }', 'quit;']
    out, ts = run(['Singular', '-q'], '\n'.join(s) + '\n', '.sing')
    res = {'class': item['class'], 'cell': item['cell'], 'lift_s': round(ts, 1)}
    if out == 'TIMEOUT' or 'C1 =' not in out:
        res['lift'] = 'lift_timeout' if out == 'TIMEOUT' else 'lift_error'
        return res
    res['cert_bytes'] = len(out)
    K = f'K = frac(QQ[{",".join(par)}]);' if par else 'K = QQ;'
    m2 = [K, f'R = K[{",".join(allv)}];', 'J = {' + ','.join(gens) + '};', out,
          'S = ' + ' + '.join(f'C{i + 1}*J#{i}' for i in range(len(gens))) + ';',
          'print(if S == 1_R then "LIFT_IDENTITY_OK" else "LIFT_IDENTITY_FAIL");', 'exit 0;']
    o2, t2 = run(['M2', '--script'], '\n'.join(m2) + '\n', '.m2')
    res['verify_s'] = round(t2, 1)
    res['lift'] = 'ok' if 'LIFT_IDENTITY_OK' in o2 else ('FAIL' if 'LIFT_IDENTITY_FAIL' in o2 else
                                                         ('verify_timeout' if o2 == 'TIMEOUT' else 'verify_error'))
    return res


if __name__ == '__main__':
    mp.set_start_method('fork', force=True)
    todo = set()
    for src in srcs:
        for l in open(src):
            r = json.loads(l)
            if r.get('m2_fix1') != 'unit':
                todo.add((r['class'], r['cell']))
    items = []
    for f in alts:
        for l in open(f):
            r = json.loads(l)
            if (r['class'], r['cell']) in todo:
                items.append(r)
    print(len(items), 'cores', flush=True)
    with open(outp, 'w') as f, mp.Pool(min(jobs, max(1, len(items)))) as pool:
        for x in pool.imap_unordered(one, items):
            f.write(json.dumps(x) + '\n')
            f.flush()
    print('done', flush=True)
