#!/usr/bin/env python3
"""Referee check of the alternative cores (types/runs/alt_out.jsonl, alt3_out.jsonl):
 (a) every equation of the core (core_sym) is an equation of the cell's stored initial system (eqs_sym of the stored
     tsec_exact record of that class and cell), with the same name;
 (b) re-certification by two systems: (S) Singular exactly as talt.certify (first mass symbol fixed to 1, iterated sat
     by every variable and every same-node difference, std, dim = -1); (M) Macaulay2 over frac(QQ[m0..m5]) with ALL six
     masses as parameters (no homogeneity argument), Rabinowitsch variable for the product of the same factors.
Usage: recert_alt.py EXACT_COLLECT_DIR OUT.jsonl ALT.jsonl [ALT.jsonl ...] [--jobs J] [--timeout S]"""
import glob, json, os, re, subprocess, sys, tempfile
import multiprocessing as mp

VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
args = [a for a in sys.argv[1:]]
jobs = int(args[args.index('--jobs') + 1]) if '--jobs' in args else 32
tmo = int(args[args.index('--timeout') + 1]) if '--timeout' in args else 900
pos = [a for i, a in enumerate(args) if not a.startswith('--') and (i == 0 or not args[i - 1].startswith('--'))]
root, outp, alts = pos[0], pos[1], pos[2:]
work = os.path.join(os.path.dirname(os.path.abspath(outp)), 'recert_alt_tmp')
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


def run(cmd, path):
    try:
        out = subprocess.run(cmd + [path], capture_output=True, text=True, timeout=tmo)
        return out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        return 'TIMEOUT'


def singular_fix1(eqs_sym):
    ms = sorted(set(re.findall(r'\bm\d\b', ' '.join(eqs_sym))))
    fix = ms[0] if ms else None
    eqs1 = [re.sub(r'\b%s\b' % fix, '1', e) for e in eqs_sym] if fix else eqs_sym
    vs = sorted(set(VAR.findall(' '.join(eqs1))))
    par = [m for m in ms if m != fix]
    ring = f'ring R = (0,{",".join(par)}), ({",".join(vs)}), dp;' if par else f'ring R = 0, ({",".join(vs)}), dp;'
    s = [ring, f'ideal I = {",".join(eqs1)};'] + [f'I = sat(I, ideal({v}));' for v in sats_of(vs)]
    s += ['ideal G = std(I);', 'print("DIM " + string(dim(G)));', 'quit;']
    fd, path = tempfile.mkstemp(suffix='.sing', dir=work)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    out = run(['nice', '-n', '10', 'Singular', '-q'], path)
    os.unlink(path)
    m = re.search(r'DIM (-?\d+)', out)
    return int(m.group(1)) if m else ('timeout' if out == 'TIMEOUT' else 'error')


def m2_all(eqs_sym):
    vs = sorted(set(VAR.findall(' '.join(eqs_sym))))
    prod = '*'.join(sats_of(vs))
    s = ['K = frac(QQ[m0,m1,m2,m3,m4,m5]);', f'R = K[{",".join(vs + ["tRab"])}];',
         f'I = ideal({",".join(eqs_sym)});', f'J = I + ideal(tRab*{prod}-1);', 'G = gb J;',
         'print(if (1_R % J) == 0 then "UNIT" else "NOTUNIT");', 'exit 0;']
    fd, path = tempfile.mkstemp(suffix='.m2', dir=work)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    out = run(['nice', '-n', '10', 'M2', '--script'], path)
    os.unlink(path)
    if 'NOTUNIT' in out:
        return 'notunit'
    if 'UNIT' in out:
        return 'unit'
    return 'timeout' if out == 'TIMEOUT' else 'error: ' + out[-300:]


def work_item(r):
    return {'class': r['class'], 'cell': r['cell'], 'subset': r['subset'], 'size': len(r['core_sym']),
            'singular_fix1': singular_fix1(r['core_sym']), 'm2_all6': m2_all(r['core_sym'])}


if __name__ == '__main__':
    mp.set_start_method('fork', force=True)
    recs = []
    for f in alts:
        for l in open(f):
            r = json.loads(l)
            if r.get('certified'):
                recs.append(r)
    want = {(r['class'], r['cell']) for r in recs}
    systems = {}
    for f in glob.glob(os.path.join(root, '*', 'exact6', 'c*', 'sec', 'p*.sec.jsonl')):
        c = int(f.split('/exact6/c')[1].split('/')[0])
        for l in open(f):
            r = json.loads(l)
            if (c, r['cell']) in want and 'system' in r:
                systems[(c, r['cell'])] = r['system']
    for r in recs:
        S = systems.get((r['class'], r['cell']))
        ok = S is not None
        if ok:
            for e, nm in zip(r['core_sym'], r['names']):
                idx = [i for i, x in enumerate(S['eqs_sym']) if x == e]
                if not idx or nm not in [S['names'][i] for i in idx]:
                    ok = False
        r['subset'] = ok
    print(len(recs), 'certified alternative cores;', sum(r['subset'] for r in recs), 'are subsets of their stored cell systems',
          flush=True)
    with open(outp, 'w') as f, mp.Pool(jobs) as pool:
        for x in pool.imap_unordered(work_item, recs):
            f.write(json.dumps(x) + '\n')
            f.flush()
    print('done', flush=True)
