#!/usr/bin/env python3
"""Other cores for the cells whose stored core has no cofactor certificate: QuickXplain (as in the engine's search)
over the cell's full initial system with several equation orders, testing modulo the prime 32003 at random masses
whether a subset generates the unit ideal (no saturation).  The search only proposes candidates; each candidate is
then certified by lift.py like any core.

Usage: altcore.py SYSTEMS.jsonl RUN_DIR [--tries K] [--t0 T] [--jobs J] [--qtime S] [--seed N] [--bias B]
Tries T..T+K-1; try 0 orders the equations by their number of variables, the others are random orders, or, with
--bias B > 0, orders by the number of variables plus B times a uniform random number.
SYSTEMS.jsonl: one record per cell {"class", "cell", "system": {"vars", "eqs_sym", "names", ...}} (the initial
system as stored by the engine in exact6/c<N>/sec/p*.sec.jsonl).
Appends to RUN_DIR/data/f4/cand_cores.jsonl (or --out NAME; cores in the format of cores.jsonl, refs
"class:cell:try:F", plus names, core_sym, renaming) and to
RUN_DIR/logs/f4/altcore.jsonl (one record per try)."""
import json
import os
import random
import re
import subprocess
import sys
import tempfile
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import collect as C  # noqa: E402

PRIME = 32003


def opt(name, default, conv=str):
    return conv(sys.argv[sys.argv.index(name) + 1]) if name in sys.argv else default


SYS, RUN = sys.argv[1], sys.argv[2]
TRIES = opt('--tries', 8, int)
JOBS = opt('--jobs', 100, int)
QTIME = opt('--qtime', 20, int)
SEED = opt('--seed', 1, int)
BIAS = opt('--bias', 0.0, float)
T0 = opt('--t0', 0, int)
WORK = os.path.join(RUN, 'work')


def unit_modp(vars_, eqs, masses):
    """True if eqs (strings in the masses m0..m5 and vars_) generate the unit ideal mod PRIME at the given masses;
    a timeout counts as not unit."""
    if not eqs:
        return False
    s = [f'ring R = {PRIME}, ({",".join(vars_)}), dp;']
    s += [f'poly m{k} = {v};' for k, v in enumerate(masses)]
    s += [f'ideal I = {",".join(eqs)};', 'ideal G = std(I);', 'print("DIM " + string(dim(G)));', 'quit;']
    fd, path = tempfile.mkstemp(suffix='.sing', dir=WORK)
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    try:
        out = subprocess.run(['Singular', '-q', '--no-rc', path], capture_output=True, text=True,
                             timeout=QTIME).stdout
    except subprocess.TimeoutExpired:
        out = ''
    os.unlink(path)
    for ln in out.splitlines():
        if ln.startswith('DIM '):
            return int(ln.split()[1]) == -1
    return False


def quickxplain(vars_, cand, masses, stats):
    def qx(B, delta_added, Cs):
        if delta_added and B:
            stats['calls'] += 1
            if unit_modp(vars_, B, masses):
                return []
        if len(Cs) == 1:
            return Cs
        k = len(Cs) // 2
        C1, C2 = Cs[:k], Cs[k:]
        D2 = qx(B + C1, True, C2)
        D1 = qx(B + D2, bool(D2), C1)
        return D1 + D2
    return qx([], False, cand)


def work(item):
    rec, t = item
    S = rec['system']
    c, cell = rec['class'], rec['cell']
    rng = random.Random(SEED * 1000003 + 1000 * c + cell * 17 + t)
    masses = [rng.randrange(2, PRIME - 1) for _ in range(6)]
    n = len(S['eqs_sym'])
    nv = [len(set(C.VAR.findall(e))) for e in S['eqs_sym']]
    if t == 0:
        idx = sorted(range(n), key=lambda i: nv[i])
    elif BIAS > 0:
        # local equations first, with random tie-breaking and noise: QuickXplain prefers early equations
        idx = sorted(range(n), key=lambda i: nv[i] + BIAS * rng.random())
    else:
        idx = list(range(n))
        rng.shuffle(idx)
    eqs = [S['eqs_sym'][i] for i in idx]
    out = {'class': c, 'cell': cell, 'try': t, 'masses': masses}
    if not unit_modp(S['vars'], eqs, masses):
        out['status'] = 'system_not_unit_modp'
        return out
    stats = {'calls': 0}
    core = quickxplain(S['vars'], eqs, masses, stats)
    out['calls'] = stats['calls']
    if not core or not unit_modp(S['vars'], core, masses):
        out['status'] = 'no_core'
        return out
    cidx = [S['eqs_sym'].index(e) for e in core]
    out.update({'status': 'core', 'idx': cidx, 'names': [S['names'][i] for i in cidx],
                'core_sym': [S['eqs_sym'][i] for i in cidx]})
    return out


def main():
    os.makedirs(WORK, exist_ok=True)
    recs = [json.loads(ln) for ln in open(SYS)]
    items = [(r, t) for r in recs for t in range(T0, T0 + TRIES)]
    res = []
    with Pool(min(JOBS, len(items))) as pool, open(os.path.join(RUN, 'logs', 'f4', 'altcore.jsonl'), 'a') as lf:
        for out in pool.imap_unordered(work, items):
            lf.write(json.dumps(out) + '\n')
            lf.flush()
            res.append(out)
            print(out['class'], out['cell'], out['try'], out['status'], len(out.get('names', [])), flush=True)
    from collections import Counter
    stats = Counter()
    cores = {}
    for out in sorted(res, key=lambda o: (o['class'], o['cell'], o['try'])):
        if out['status'] != 'core':
            continue
        F0 = C.fixed_mass(out['core_sym'])
        for F in sorted({F0, -1}):
            cid, block, ren = C.build_core(out['core_sym'], F, stats)
            ref = f'{out["class"]}:{out["cell"]}:{out["try"]}:{F}'
            if cid not in cores:
                cores[cid] = {'certid': cid, 'fixed': F, 'nvar': len(ren), 'ngens': len(out['core_sym']),
                              'nterms': sum(1 for ln in block.split('\n') if ln and ln[0] in '-0123456789'),
                              'block': block, 'cells': 0, 'refs': [], 'kind': 'b' if F >= 0 else 'a',
                              'names': out['names'], 'core_sym': out['core_sym'], 'renaming': ren}
            cores[cid]['cells'] += 1
            cores[cid]['refs'].append(ref)
    with open(os.path.join(RUN, 'data', 'f4', opt('--out', 'cand_cores.jsonl')), 'a') as fh:
        for cid in sorted(cores):
            fh.write(json.dumps(cores[cid]) + '\n')
    print(len(cores), 'candidate cores', dict(stats), flush=True)


if __name__ == '__main__':
    main()
