#!/usr/bin/env python3
"""Summarizes the `#print axioms` output of a lake build log: for every theorem, its axioms; checks that each is one
of propext, Classical.choice, Quot.sound, or an auxiliary axiom `<theorem>._native.native_decide.ax_<i>_<j>` of a
native_decide theorem; writes one line per theorem and a verdict. Usage: axioms_summary.py LOG OUT"""
import re, sys
txt = open(sys.argv[1]).read()
std = {'propext', 'Classical.choice', 'Quot.sound'}
res, bad = [], []
for m in re.finditer(r"'([^']+)' depends on axioms: \[(.*?)\]", txt, re.S):
    name, ax = m.group(1), [a.strip() for a in m.group(2).replace('\n', ' ').split(',') if a.strip()]
    nstd = sorted(a for a in ax if a in std)
    aux = [a for a in ax if a not in std]
    ok = all(re.fullmatch(r'[\w.]+\._native\.native_decide\.ax_\d+_\d+', a) for a in aux)
    res.append((name, nstd, len(aux), ok))
    if not ok:
        bad.append((name, [a for a in aux if not re.fullmatch(r'[\w.]+\._native\.native_decide\.ax_\d+_\d+', a)]))
for m in re.finditer(r"'([^']+)' does not depend on any axioms", txt):
    res.append((m.group(1), [], 0, True))
with open(sys.argv[2], 'w') as f:
    f.write('# theorem | standard axioms | number of native_decide auxiliary axioms | only allowed axioms\n')
    for name, nstd, naux, ok in sorted(set((r[0], tuple(r[1]), r[2], r[3]) for r in res)):
        f.write(f'{name} | {",".join(nstd) or "-"} | {naux} | {ok}\n')
    f.write(f'# theorems: {len(set(r[0] for r in res))}; with a disallowed axiom: {len(bad)}; sorryAx anywhere in the log: {"sorryAx" in txt}\n')
print(len(set(r[0] for r in res)), 'theorems;', len(bad), 'with a disallowed axiom;', 'sorryAx' in txt and 'SORRY FOUND' or 'no sorryAx')
for b in bad[:10]:
    print('BAD', b)
