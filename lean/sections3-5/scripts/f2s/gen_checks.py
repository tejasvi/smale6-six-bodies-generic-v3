#!/usr/bin/env python3
"""Writes the native_decide checks of the specification search (L6F2S): every cell of the specification search of a
class has the key of a stored line of that class.

  L6Check/F2S/C<k>.lean        classes split at depth 3 (one theorem for all pairs after three insertions), or at
                               depth 4 for the classes HEAVY (one module per group of GROUP pairs, L6Check/F2S/C<k>/M<j>.lean)
  L6Check/F2S/Index.lean       imports everything

Input: PREFIX_COUNTS (lines "class d count", the lengths of prefixPairs keepLP (diagOf k) d, which the theorems
`f2s_len_c<k>` check). Run from the package root. Usage: gen_checks.py PREFIX_COUNTS"""
import os, sys
HEAVY = {3, 128, 148}
GROUP = 8
counts = {}
for line in open(sys.argv[1]):
    k, d, n = map(int, line.split())
    counts[(k, d)] = n
D = 'L6Check/F2S'
os.makedirs(D, exist_ok=True)
mods = []


def write(p, txt):
    if not os.path.exists(p) or open(p).read() != txt:
        open(p, 'w').write(txt)


HDR = 'import L6F2S.Stored\nimport L6F2.Check\nimport L6Check.F2.Data.C{k}\n\nnamespace L6.F2S.Checks\n\nopen L6.F2S\n\n'
for k in range(191):
    d = 4 if k in HEAVY else 3
    n = counts[(k, d)]
    pre = f'(prefixPairs keepLP (L6.F2.diagOf {k}) {d})'
    if k not in HEAVY:
        txt = HDR.format(k=k) + (
            f'/-- The number of pairs of trees of class {k} after {d} insertions. -/\n'
            f'theorem f2s_len_c{k} : {pre}.length = {n} := by native_decide\n\n'
            f'set_option maxHeartbeats 0 in\n'
            f'/-- Every cell of the specification search of class {k} has the key of a stored line. -/\n'
            f'theorem f2s_c{k} : checkBelow keepLP (L6.F2.diagOf {k}) {d} L6.F2.Data.cells_c{k} {pre} = true := by\n'
            f'  native_decide\n\nend L6.F2S.Checks\n')
        write(f'{D}/C{k}.lean', txt)
        mods.append(f'L6Check.F2S.C{k}')
    else:
        os.makedirs(f'{D}/C{k}', exist_ok=True)
        groups = [(lo, min(GROUP, n - lo)) for lo in range(0, n, GROUP)]
        sub = []
        for j, (lo, m) in enumerate(groups):
            txt = HDR.format(k=k) + (
                f'set_option maxHeartbeats 0 in\n'
                f'/-- Class {k}, the pairs {lo} ≤ i < {lo + m} after {d} insertions. -/\n'
                f'theorem f2s_c{k}_m{j} : checkBelow keepLP (L6.F2.diagOf {k}) {d} L6.F2.Data.cells_c{k}\n'
                f'    (({pre}.drop {lo}).take {m}) = true := by\n  native_decide\n\nend L6.F2S.Checks\n')
            write(f'{D}/C{k}/M{j}.lean', txt)
            sub.append(f'L6Check.F2S.C{k}.M{j}')
        txt = '\n'.join(f'import {s}' for s in sub) + '\n\n' + (
            'namespace L6.F2S.Checks\n\nopen L6.F2S\n\n'
            f'/-- The number of pairs of trees of class {k} after {d} insertions. -/\n'
            f'theorem f2s_len_c{k} : {pre}.length = {n} := by native_decide\n\nend L6.F2S.Checks\n')
        txt = 'import L6F2S.Stored\nimport L6F2.Check\n' + txt
        write(f'{D}/C{k}.lean', txt)
        mods.append(f'L6Check.F2S.C{k}')
write(f'{D}/Index.lean', '\n'.join(f'import {m}' for m in mods) + '\n')
print(len(mods), 'class modules;', sum(1 for k in HEAVY for _ in range(0, counts[(k, 4)], GROUP)), 'heavy group modules')
