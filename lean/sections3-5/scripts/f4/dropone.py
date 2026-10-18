#!/usr/bin/env python3
"""Irredundancy test of cores: for each core (a generator block of cores.jsonl), modulo the prime 32003 at random
masses (m_F = 1 already substituted when F >= 0), whether the core generates the unit ideal, and whether the core
with one generator dropped does, for each generator.  A core none of whose one-dropped subsets is the unit ideal at
these masses has no proper subset that generates the unit ideal over Q(m) (such a subset would do so at almost all
masses and primes).
Usage: dropone.py RUN_DIR IDS.txt [--seed N] [--jobs J] [--timeout S] [--cores CORES.jsonl]
                  [--systems SYSTEMS.jsonl --links LINKDIR]
(prints one JSON record per core; a subset whose test exceeds S seconds gets dimension null; with --systems the ring
variables are listed in the order of the cell's stored variable list, as in the engine's tests)"""
import json
import os
import random
import subprocess
import sys
import tempfile
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import certfmt as CF  # noqa: E402

RUN, IDS = sys.argv[1], sys.argv[2]
SEED = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
JOBS = int(sys.argv[sys.argv.index('--jobs') + 1]) if '--jobs' in sys.argv else 64
TMO = int(sys.argv[sys.argv.index('--timeout') + 1]) if '--timeout' in sys.argv else 600
PRIME = 32003


def parse_block(block):
    lines = block.strip('\n').split('\n')
    t = lines[1].split()
    nvar, fixed = int(t[3]), int(t[5])
    ng = int(lines[2].split()[1])
    gens, p = [], 3
    for i in range(ng):
        T = int(lines[p].split()[2])
        p += 1
        d = {}
        for _ in range(T):
            a = list(map(int, lines[p].split()))
            p += 1
            k = [0] * (6 + nvar)
            k[:6] = a[1:7]
            for q in range(a[7]):
                k[6 + a[8 + 2 * q]] = a[9 + 2 * q]
            d[tuple(k)] = a[0]
        gens.append(d)
    return nvar, fixed, gens


def poly_str(d, names):
    out = []
    for k, c in d.items():
        mon = [f'{names[j]}^{e}' for j, e in enumerate(k) if e]
        out.append(f'({c})' + ''.join('*' + m for m in mon))
    return '+'.join(out) if out else '0'


def dims(nvar, gens, masses, subsets):
    names = [f'm{k}' for k in range(6)] + [f'x{j}' for j in range(nvar)]
    s = [f'ring R = {PRIME}, ({",".join(names[6:])}), dp;']
    s += [f'poly m{k} = {v};' for k, v in enumerate(masses)]
    for si, sub in enumerate(subsets):
        s += [f'ideal I{si} = ' + ','.join(poly_str(gens[i], names) for i in sub) + ';',
              f'print("D {si} " + string(dim(std(I{si}))));']
    s.append('quit;')
    fd, path = tempfile.mkstemp(suffix='.sing', dir=os.path.join(RUN, 'work'))
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    try:
        out = subprocess.run(['Singular', '-q', '--no-rc', path], capture_output=True, text=True, timeout=TMO).stdout
    except subprocess.TimeoutExpired:
        out = ''
    os.unlink(path)
    res = {}
    for ln in out.splitlines():
        if ln.startswith('D '):
            _, i, d = ln.split()
            res[int(i)] = int(d)
    return [res.get(i) for i in range(len(subsets))]


VARPOS = {}   # certid -> ring position of each canonical variable (option --systems)


def work(c):
    nvar, fixed, gens = parse_block(c['block'])
    if c['certid'] in VARPOS:
        # list the ring variables in the order of the cell's stored variable list (the engine's test order)
        perm = VARPOS[c['certid']]
        gens = [{k[:6] + tuple(k[6 + j] for j in perm): v for k, v in g.items()} for g in gens]
    rng = random.Random(SEED * 7919 + int(c['certid'], 16) % 100003)
    masses = [rng.randrange(2, PRIME - 1) for _ in range(6)]
    if fixed >= 0:
        masses[fixed] = 1
    G = len(gens)
    subsets = [list(range(G))] + [[j for j in range(G) if j != i] for i in range(G)]
    # one Singular run per subset, so that one slow subset does not hide the others
    d = [dims(nvar, gens, masses, [sub])[0] for sub in subsets]
    return {'certid': c['certid'], 'fixed': fixed, 'ngens': G, 'full_dim': d[0], 'drop_dims': d[1:],
            'irredundant': d[0] == -1 and all(x is not None and x != -1 for x in d[1:])}


def main():
    ids = set(open(IDS).read().split())
    cores_file = sys.argv[sys.argv.index('--cores') + 1] if '--cores' in sys.argv else os.path.join(
        RUN, 'data', 'f4', 'cores.jsonl')
    cores = [json.loads(ln) for ln in open(cores_file)]
    cores = [c for c in cores if c['certid'] in ids]
    if '--systems' in sys.argv:
        # --systems SYSTEMS.jsonl --links LINKDIR: ring variable order = order in the cell's stored variable list
        svars = {}
        for ln in open(sys.argv[sys.argv.index('--systems') + 1]):
            r = json.loads(ln)
            svars[(r['class'], r['cell'])] = r['system']['vars']
        import glob
        for f in glob.glob(os.path.join(sys.argv[sys.argv.index('--links') + 1], 'c*.txt')):
            for ln in open(f):
                left, right = ln.split(' | ')
                t = left.split()
                key, cid = (int(t[0]), int(t[1])), t[2]
                if cid in ids and key in svars:
                    ren = right.split()
                    order = sorted(range(len(ren)), key=lambda j: svars[key].index(ren[j]))
                    VARPOS[cid] = order
    with Pool(min(JOBS, max(1, len(cores)))) as pool:
        for r in pool.imap_unordered(work, cores):
            print(json.dumps(r), flush=True)


if __name__ == '__main__':
    main()
