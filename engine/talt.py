#!/usr/bin/env python3
"""Alternative cores for uncertified cells: QuickXplain (tcore.quickxplain) with randomized equation orders, each core
verified mod p and then certified over Q(m) (tcert's method, one mass fixed to 1); stops at the first certified core.
Usage: talt.py UNCERT.json SEC_ROOT OUT.jsonl [--tries K] [--jobs J] [--qtime S]
SEC_ROOT: a directory containing exact6/cCLS/sec/p*.sec.jsonl for the classes of the list."""
import glob, json, os, random, re, subprocess, sys, tempfile, hashlib
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tinit as I
import tcore as Q

unc = json.load(open(sys.argv[1]))
root, outp = sys.argv[2], sys.argv[3]
tries = int(sys.argv[sys.argv.index('--tries') + 1]) if '--tries' in sys.argv else 8
jobs = int(sys.argv[sys.argv.index('--jobs') + 1]) if '--jobs' in sys.argv else 100
qtime = int(sys.argv[sys.argv.index('--qtime') + 1]) if '--qtime' in sys.argv else 600
workdir = os.path.dirname(os.path.abspath(outp))
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
PRIME = 32003


def systems():
    want = {(u['class'], u['cell']) for u in unc}
    out = {}
    for f in glob.glob(os.path.join(root, '**', 'exact6', 'c*', 'sec', 'p*.sec.jsonl'), recursive=True):
        c = int(f.split('/exact6/c')[1].split('/')[0])
        for l in open(f):
            r = json.loads(l)
            if (c, r['cell']) in want and 'system' in r:
                out[(c, r['cell'])] = r['system']
    return out


def certify(eqs_sym):
    ms = sorted(set(re.findall(r'\bm\d\b', ' '.join(eqs_sym))))
    fix = ms[0] if ms else None
    eqs1 = [re.sub(r'\b%s\b' % fix, '1', e) for e in eqs_sym] if fix else eqs_sym
    vs = sorted(set(VAR.findall(' '.join(eqs1))))
    par = [m for m in ms if m != fix]
    ring = f'ring R = (0,{",".join(par)}), ({",".join(vs)}), dp;' if par else f'ring R = 0, ({",".join(vs)}), dp;'
    sats = list(vs)
    bynode = {}
    for v in vs:
        if v[0] in 'XY':
            bynode.setdefault(v.split('_')[0], []).append(v)
    for node, lst in bynode.items():
        for i in range(len(lst)):
            for j in range(i + 1, len(lst)):
                sats.append(f'({lst[i]}-{lst[j]})')
    s = [ring, f'ideal I = {",".join(eqs1)};'] + [f'I = sat(I, ideal({v}));' for v in sats]
    s += ['ideal G = std(I);', 'print("DIM " + string(dim(G)));', 'quit;']
    fd, path = tempfile.mkstemp(suffix='.sing', dir=workdir)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    try:
        out = subprocess.run(['Singular', '-q', path], capture_output=True, text=True, timeout=qtime).stdout
    except subprocess.TimeoutExpired:
        out = ''
    os.unlink(path)
    for line in out.splitlines():
        if line.startswith('DIM '):
            return int(line.split()[1])
    return None


def work(item):
    (c, cell), S = item
    rng = random.Random(1000 * c + cell)
    n = len(S['eqs'])
    tried = []
    for t in range(tries):
        idx = list(range(n))
        rng.shuffle(idx)
        stats = {'calls': 0}
        core = Q.quickxplain(S['vars'], [], [S['eqs'][i] for i in idx], S['sats'], PRIME, workdir, stats)
        if not core or not Q.inconsistent(S['vars'], core, S['sats'], PRIME, workdir):
            tried.append({'try': t, 'core': None})
            continue
        cidx = [S['eqs'].index(e) for e in core]
        csym = [S['eqs_sym'][i] for i in cidx]
        dim = certify(csym)
        tried.append({'try': t, 'size': len(core), 'dim': dim, 'names': [S['names'][i] for i in cidx]})
        if dim == -1:
            return {'class': c, 'cell': cell, 'certified': True, 'core_sym': csym, 'names': [S['names'][i] for i in cidx],
                    'tries': tried}
    return {'class': c, 'cell': cell, 'certified': False, 'tries': tried}


if __name__ == '__main__':
    sy = systems()
    print(len(sy), 'systems found for', len(unc), 'uncertified cells', flush=True)
    items = sorted(sy.items())
    with open(outp, 'w') as f, Pool(min(jobs, max(1, len(items)))) as pool:
        for r in pool.imap_unordered(work, items):
            f.write(json.dumps(r) + '\n')
            f.flush()
