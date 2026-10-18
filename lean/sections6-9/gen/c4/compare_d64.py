#!/usr/bin/env python3
"""Compare the chart equations built in Lean (`gen/c4/dump_eqs.lean`, file LEAN) with
(1) the system builder of the d64 programs (D64/scripts/c4_systems.py),
(2) the msolve inputs of the d64 certificate (D64/certificates/c4_msolve_work/c4_<chart>.ms, masses (3,5,7,11)),
(3) the separate builder gen/c4/c4sys.py.
Usage: compare_d64.py LEAN D64. Prints one line per check and a final verdict."""
import os
import re
import sys

lean_file, d64 = sys.argv[1], sys.argv[2]
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
import c4sys  # noqa: E402
sys.path.insert(0, os.path.join(d64, 'scripts'))
import c4_systems  # noqa: E402

NAMES = ['s', 't', 'p12', 'p13', 'p14', 'p23', 'p24', 'p34', 'c']
MS = {'sa': 0, 'ta': 1, 'pab': 2, 'pac': 3, 'pad': 4, 'pbc': 5, 'pbd': 6, 'pcd': 7, 'ca': 8}

lean = {}
for line in open(lean_file):
    line = line.strip()
    if not line or '|' not in line:
        continue
    mu, ch, body = line.split('|')
    mu = tuple(int(x) for x in mu.strip('[]').split(','))
    poly = {}
    for t in body.split(';'):
        c, e = t.split(':')
        poly[tuple(int(x) for x in e.split(','))] = int(c)
    lean.setdefault((mu, ch), []).append(poly)


def parse_ms(path):
    lines = open(path).read().split('\n')
    names = lines[0].strip().split(',')
    body = ''.join(lines[2:]).replace(' ', '')
    polys = []
    for ptxt in body.split(','):
        if not ptxt:
            continue
        poly = {}
        for t in re.findall(r'[+-]?[^+-]+', ptxt):
            sg = -1 if t[0] == '-' else 1
            t = t.lstrip('+-')
            c, e = 1, [0] * 9
            for f in t.split('*'):
                if re.fullmatch(r'\d+', f):
                    c *= int(f)
                else:
                    m = re.fullmatch(r'([a-z]+)(\^(\d+))?', f)
                    e[MS[m.group(1)]] += int(m.group(3) or 1)
            k = tuple(e)
            poly[k] = poly.get(k, 0) + sg * c
        polys.append({k: v for k, v in poly.items() if v})
    return names, polys


bad = 0
n = 0
for mu in [(3, 5, 7, 11), (1, 1, 1, 1)]:
    d64eqs = [f for _, f in c4_systems.build(list(mu))]
    mine = c4sys.equations(mu)
    for (a, b) in c4sys.CHARTS:
        ch = '%s_%s' % (NAMES[a], NAMES[b])
        L = lean[(mu, ch)]
        D = [c4_systems.dehomogenize(f, (a, b)) for f in d64eqs]
        M = [c4sys.dehom(f, (a, b)) for f in mine]
        ok1 = L == D
        ok3 = L == M
        ok2 = True
        if mu == (3, 5, 7, 11):
            names, P = parse_ms(os.path.join(d64, 'certificates', 'c4_msolve_work', 'c4_%s.ms' % ch))
            ok2 = L == P
        n += 1
        if not (ok1 and ok2 and ok3):
            bad += 1
        print('mu=%s chart=%s: d64 builder %s, d64 msolve input %s, gen/c4/c4sys.py %s'
              % (mu, ch, ok1, ok2 if mu == (3, 5, 7, 11) else 'n/a', ok3))
print('VERDICT: %s (%d chart systems compared, %d mismatches)' % ('AGREE' if bad == 0 else 'DISAGREE', n, bad))
