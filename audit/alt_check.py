#!/usr/bin/env python3
"""Check the alternative-core certifications against the first-pass uncertified list and the open list.
Usage: alt_check.py ALT_OUT ALT3_OUT UNCERTIFIED_JSON GENERIC_OPEN_TXT"""
import json, sys
from collections import Counter
alt, alt3, unc, gopen = sys.argv[1:5]
recs = [json.loads(l) for l in open(alt)] + [json.loads(l) for l in open(alt3)]
ok = lambda r: r['certified'] and any(t.get('dim') == -1 for t in r['tries'])
cert = {(r['class'], r['cell']) for r in recs if ok(r)}
U = {(x['class'], x['cell']) for x in json.load(open(unc))}
op = set()
for l in open(gopen):
    if l.startswith('#') or not l.strip():
        continue
    f = l.split('\t')
    op.add((int(f[0]), int(f[2])))
print('records', len(recs), 'certified (a try with dim -1)', sum(ok(r) for r in recs))
print('first-pass uncertified', len(U), 'certified by alternative cores', len(cert), 'subset', cert <= U)
print('remaining', len(U - cert), 'equal to the open list', (U - cert) == op)
print('remaining by engine class', sorted(Counter(c for c, _ in U - cert).items()))
