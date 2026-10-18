#!/usr/bin/env python3
"""For each distinct face vector found by run_myprev.py, form the initial system of G at the cell's exact interior
point w (MIN convention, coefficients = the integer coefficients at m0) and decide with msolve (not Singular) whether
it has a zero in the torus over F_p-bar: msolve -g 2 on  {in_w(g)} + {T * prod(vars) - 1}; empty iff the reduced GB
is [1].  Inputs are written in msolve's strict grammar and linted (ms_lint + own strict re-parse).
Also compares with the author's gfan fan: for each cell, -w must lie in some gfan cone (max convention) whose
relative-interior initial forms equal ours.
Usage: check_cells_msolve.py GFAN_INPUT PREV.json AUTHOR_FAN WORKDIR p NPROC
"""
import json
import os
import re
import subprocess
import sys
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'tools'))
import myprev
from ms_lint import lint_text

NAMES = None
POLYS = None
P = None
WD = None


def init(gf, p, wd):
    global NAMES, POLYS, P, WD
    NAMES, POLYS = myprev.parse_gfan(gf)
    P, WD = p, wd


def initial(poly, w, maximize=False):
    vals = {k: sum(a * b for a, b in zip(k, w)) for k in poly}
    ext = max(vals.values()) if maximize else min(vals.values())
    return {k: c for k, c in poly.items() if vals[k] == ext}


def to_ms(polys, names, p):
    vars_ = list(names) + ['TT']
    lines = []
    for poly in polys:
        terms = []
        for k in sorted(poly, reverse=True):
            c = poly[k] % p
            if c == 0:
                continue
            mon = '*'.join(('%s^%d' % (nm, e) if e > 1 else nm) for nm, e in zip(names, k) if e > 0)
            terms.append('%d%s' % (c, ('*' + mon) if mon else ''))
        if terms:
            lines.append('+'.join(terms))
    lines.append('1*' + '*'.join(names) + '*TT-1')
    return ','.join(vars_) + '\n' + str(p) + '\n' + ',\n'.join(lines) + '\n'


def check(args):
    idx, w = args
    ini = [initial(g, w) for g in POLYS]
    txt = to_ms(ini, NAMES, P)
    probs = lint_text(txt)
    if probs:
        return (idx, 'LINT', probs[:3])
    fin = os.path.join(WD, 'cell%d.ms' % idx)
    fout = os.path.join(WD, 'cell%d.out' % idx)
    open(fin, 'w').write(txt)
    subprocess.run(['msolve', '-g', '2', '-t', '1', '-f', fin, '-o', fout], capture_output=True, timeout=3600)
    out = open(fout).read()
    body = out[out.index('['):].strip() if '[' in out else ''
    empty = body.replace(' ', '').replace('\n', '') in ('[1]:', '[1]')
    return (idx, 'EMPTY' if empty else 'NONEMPTY', body[:200])


def parse_fan(path):
    txt = open(path).read().split('\n')

    def sec(name):
        out, on = [], False
        for l in txt:
            if l.strip() == name:
                on = True
                continue
            if on:
                if re.fullmatch(r'[A-Z_]+', l.strip()):
                    break
                if l.strip():
                    out.append(l.split('#')[0].strip())
        return out
    rays = [[int(x) for x in l.split()] for l in sec('RAYS') if l]
    cones = []
    for l in sec('CONES'):
        if l.startswith('{'):
            b = l.strip('{}').strip()
            cones.append([int(x) for x in b.split()] if b else [])
    return rays, cones


def main():
    gf, prevf, fanf, wd, p, nproc = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]), int(sys.argv[6])
    os.makedirs(wd, exist_ok=True)
    init(gf, p, wd)
    prev = json.load(open(prevf))
    fvs = prev['face_vectors']
    jobs = [(i, fv['w']) for i, fv in enumerate(fvs) if any(x != 0 for x in fv['w'])]
    nzero = len(fvs) - len(jobs)
    with Pool(nproc, initializer=init, initargs=(gf, p, wd)) as pool:
        res = pool.map(check, jobs, chunksize=1)
    verdicts = {}
    for idx, v, body in res:
        verdicts[v] = verdicts.get(v, 0) + 1
    bad = [(idx, v, body) for idx, v, body in res if v != 'EMPTY']
    # comparison with the author's gfan fan: initial-form signatures
    rays, cones = parse_fan(fanf)
    sig_gfan = set()
    for cone in cones:
        rs = [rays[i] for i in cone]
        r = [sum(col) for col in zip(*rs)] if rs else [0] * len(NAMES)
        sig = tuple(tuple(sorted(initial(g, r, maximize=True).keys())) for g in POLYS)
        sig_gfan.add(sig)
    sig_mine = set()
    for fv in fvs:
        sig = tuple(tuple(sorted(initial(g, fv['w']).keys())) for g in POLYS)
        sig_mine.add(sig)
    out = {'n_face_vectors': len(fvs), 'zero_cells': nzero, 'tested': len(jobs), 'verdicts': verdicts,
           'not_empty': bad[:20], 'gfan_cones': len(cones), 'gfan_distinct_initial_signatures': len(sig_gfan),
           'my_distinct_initial_signatures': len(sig_mine),
           'mine_minus_gfan': len(sig_mine - sig_gfan), 'gfan_minus_mine': len(sig_gfan - sig_mine)}
    print(json.dumps(out))
    json.dump(out, open(os.path.join(wd, 'summary.json'), 'w'))


if __name__ == '__main__':
    main()
