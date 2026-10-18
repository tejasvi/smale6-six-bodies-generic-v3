#!/usr/bin/env python3
"""The systems that the covering assumes torus-empty (leaves `hyp`): check with Singular (std) and msolve (F4) that
each generates the unit ideal over F_p (so it has no zero at all, in particular none in the torus).
Usage: hypcheck.py OUTDIR (reads n4_hyps.json, kc_hyps.json; writes the inputs next to them)"""
import json
import os
import re
import subprocess
import sys
import time

P = 65521
NV = 17


def sing_poly(f):
    out = []
    for c, e in f:
        mon = '*'.join(('x(%d)^%d' % (i, k) if k > 1 else 'x(%d)' % i) for i, k in enumerate(e) if k)
        out.append('%d%s' % (c, ('*' + mon) if mon else ''))
    return '+'.join(out) if out else '0'


def ms_poly(f):
    """msolve's strict grammar: integer coefficient first, each variable at most once per term (with ^), distinct
    monomials, no parentheses (msolve 0.9.4 misreads repeated variables, '**', parentheses and factors after variables)."""
    out = []
    mons = set()
    for c, e in f:
        assert tuple(e) not in mons
        mons.add(tuple(e))
        mon = '*'.join(('x%d^%d' % (i, k) if k > 1 else 'x%d' % i) for i, k in enumerate(e) if k)
        out.append('%d%s' % (c, ('*' + mon) if mon else ''))
    s = '+'.join(out) if out else '0'
    assert not re.search(r'[()]|\*\*', s)
    return s


def main():
    outdir = sys.argv[1]
    for kind in ('n4', 'kc'):
        path = os.path.join(outdir, '%s_hyps.json' % kind)
        if not os.path.exists(path):
            continue
        for k, sysm in enumerate(json.load(open(path))):
            base = os.path.join(outdir, '%s_hyp%d' % (kind, k))
            s = 'ring r = %d,(%s),dp;\noption(redSB);\nideal J = %s;\nint t0 = rtimer;\nideal G = std(J);\n' % (
                P, ','.join('x(%d)' % i for i in range(NV)), ',\n'.join(sing_poly(f) for f in sysm))
            s += 'print("SINGULAR unit " + string(deg(G[1]) == 0) + " size " + string(size(G)) + " seconds " + string(rtimer - t0));\nquit;\n'
            open(base + '.sing', 'w').write(s)
            t0 = time.time()
            r = subprocess.run(['nice', '-n', '10', 'Singular', '-q', base + '.sing'], capture_output=True, text=True, timeout=7200)
            print(kind, k, len(sysm), 'polynomials:', r.stdout.strip(), '(%.1fs)' % (time.time() - t0), flush=True)
            ms = ','.join('x%d' % i for i in range(NV)) + '\n%d\n' % P + ',\n'.join(ms_poly(f) for f in sysm) + '\n'
            open(base + '.ms', 'w').write(ms)
            t0 = time.time()
            subprocess.run(['nice', '-n', '10', 'msolve', '-t', '4', '-g', '2', '-f', base + '.ms', '-o', base + '.ms.out'],
                           capture_output=True, text=True, timeout=7200)
            out = open(base + '.ms.out').read()
            gb = out[out.index('['):].replace('\n', '').strip()
            print(kind, k, 'msolve reduced basis:', gb[:40], '(%.1fs)' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
