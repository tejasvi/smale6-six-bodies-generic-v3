#!/usr/bin/env python3
"""Certificate (checker 2) for Lemma C of DERIVATION.md: the compact model Z(mu0) of C4 is empty, by msolve over a
prime field on each of the 14 affine charts of X (output [-1] = no solution over the algebraic closure of F_p).

Why mod p suffices (DERIVATION.md, C.4): X is a projective toric variety; if Z has no F_p-bar point, the toric
Nullstellensatz gives B^N in I mod p (B the irrelevant ideal), so the Macaulay matrix of the generators in some
bidegree (a, b) has full rank mod p, hence over Q, hence Z(mu0) has no complex point.

msolve 0.9.4 input hygiene (known silent misparses): variable names are pure letters (no digits), every polynomial
is fully expanded with integer coefficients, no parentheses, no '**', no '/', no floats; the files are linted.
Usage: c4_cert_msolve.py [m1 m2 m3 m4] [p] [workdir]
"""
import json
import os
import re
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c4_systems as C  # noqa: E402

LETTER = {'s': 'sa', 't': 'ta', 'p12': 'pab', 'p13': 'pac', 'p14': 'pad', 'p23': 'pbc', 'p24': 'pbd', 'p34': 'pcd',
          'c': 'ca'}


def lint(line, names):
    assert re.fullmatch(r'[a-z0-9\^\*\+\-]+', line), line[:80]
    for tok in re.findall(r'[a-z]+', line):
        assert tok in names, tok
    assert '**' not in line and '^^' not in line


def main():
    a = sys.argv[1:]
    mu = [int(x) for x in a[:4]] if len(a) >= 4 else [3, 5, 7, 11]
    p = int(a[4]) if len(a) >= 5 else 1073741789
    work = a[5] if len(a) >= 6 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'certificates',
                                                   'c4_msolve_work')
    os.makedirs(work, exist_ok=True)
    eqs = C.build(mu)
    degs = C.degree_check(eqs)
    res = {'mu0': mu, 'p': p, 'degrees': degs, 'charts': []}
    ok = True
    t0 = time.time()
    for ch in C.charts():
        keep = [i for i in range(C.NV) if i not in ch]
        names = [LETTER[C.VARS[i]] for i in keep]
        allnames = [LETTER[v] for v in C.VARS]
        lines = []
        for _, f in eqs:
            g = C.dehomogenize(f, ch)
            sline = C.to_string(g, allnames)
            lint(sline, set(names) | set())
            lines.append(sline)
        tag = '%s_%s' % (C.VARS[ch[0]], C.VARS[ch[1]])
        fin = os.path.join(work, 'c4_%s.ms' % tag)
        fout = os.path.join(work, 'c4_%s.out' % tag)
        with open(fin, 'w') as fo:
            fo.write(','.join(names) + '\n' + str(p) + '\n' + ',\n'.join(lines) + '\n')
        r = subprocess.run(['msolve', '-f', fin, '-o', fout, '-t', '1'], capture_output=True, text=True, timeout=3600)
        txt = open(fout).read().strip() if os.path.exists(fout) else ''
        empty = (txt.replace(' ', '').rstrip(':') == '[-1]')
        ok = ok and empty and r.returncode == 0
        res['charts'].append({'chart': tag, 'msolve_output': txt[:40], 'empty': empty, 'rc': r.returncode})
    res['seconds'] = round(time.time() - t0, 1)
    res['verdict'] = 'PASS' if ok else 'FAIL'
    print(json.dumps(res, indent=1))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
