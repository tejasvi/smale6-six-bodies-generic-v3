#!/usr/bin/env python3
"""Hashes of canonical cores, as tcert.py computes them: 'new' = equations and saturation set (since the engine
referee's fix 2), 'old' = equations only (the stored first-pass runs)."""
import hashlib, re
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')


def sats_of(eqs):
    vs = sorted(set(v for e in eqs for v in VAR.findall(e)))
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


def canon(eqs, sats):
    order = []
    for e in eqs:
        for v in VAR.findall(e):
            if v not in order:
                order.append(v)
    ren = {v: f'v{i}' for i, v in enumerate(order)}
    f = lambda e: VAR.sub(lambda mm: ren[mm.group(0)], e)
    ceqs = [f(e) for e in eqs]
    csats = sorted(set(f(s) for s in sats if VAR.findall(s) and all(v in ren for v in VAR.findall(s))))
    return ceqs, csats


def hashes(eqs):
    ceqs, csats = canon(eqs, sats_of(eqs))
    old = hashlib.sha1('\n'.join(ceqs).encode()).hexdigest()[:16]
    new = hashlib.sha1(('\n'.join(ceqs) + '\n#sat\n' + '\n'.join(csats)).encode()).hexdigest()[:16]
    return old, new
