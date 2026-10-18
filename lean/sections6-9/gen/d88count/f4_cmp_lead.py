"""Compare the leading monomials of the active basis elements of the F4 engine (one exponent list per line, as written
by the development driver Lean6.Special.Comp.D88.Count.RunDev) with an msolve .lead file: the minimal elements of both
sets, and the number of standard monomials of each (a breadth-first count, as in Comp.Count.dimCheck).

Usage: python3 -I f4_cmp_lead.py OURS.lead MSOLVE.lead
"""
import re, sys
ours = [tuple(int(x) for x in re.findall(r'\d+', l)) for l in open(sys.argv[1]) if l.strip()]
txt = open(sys.argv[2]).read()
hdr = re.search(r'#variable order:\s*(.*)', txt).group(1)
names = [v.strip() for v in hdr.split(',')]
body = txt[txt.index('[') + 1: txt.index(']')]
ms = []
for m in body.split(','):
    m = m.strip()
    e = [0] * len(names)
    for f in m.split('*'):
        v, k = f.split('^')
        e[names.index(v)] += int(k)
    ms.append(tuple(e))
def divides(a, b): return all(x <= y for x, y in zip(a, b))
def minimal(S):
    S = sorted(set(S), key=sum)
    out = []
    for s in S:
        if not any(divides(t, s) for t in out):
            out.append(s)
    return out
mo = minimal(ours)
print('ours active', len(ours), 'minimal', len(mo), 'msolve', len(ms), 'msolve minimal', len(minimal(ms)))
print('same minimal set:', set(mo) == set(ms))
def std(gens):
    from collections import deque
    z = tuple([0] * len(names))
    seen = {z}
    q = deque([z])
    while q:
        s = q.popleft()
        for i in range(len(names)):
            t = list(s); t[i] += 1; t = tuple(t)
            if t in seen: continue
            if any(divides(g, t) for g in gens): continue
            seen.add(t); q.append(t)
    return len(seen)
print('std ours', std(mo), 'std msolve', std(ms))
