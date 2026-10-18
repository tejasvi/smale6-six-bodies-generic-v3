#!/usr/bin/env python3
"""Writes the count modules of the KC boxes (Sec. 6.7, last paragraph): L6CheckKSpec/KC/Cnt<k>.lean with
`kcCountsB M<k>.boxes = some (f, p, m)` (decide +kernel) and L6CheckKSpec/KC/Counts.lean with the total. The counts of
each module come from a native classification of the sorted box strings (one line `t sm` or `none` per box, in the
order of data/ksp/KC_sorted.txt); untrusted, the kernel checks them. Usage: kspc_gen.py ROOT CLASSES.txt PER_MODULE"""
import os, sys

root, classes, per_mod = sys.argv[1], sys.argv[2], int(sys.argv[3])
cls = [l.split() for l in open(classes)]
assert all(len(c) == 2 for c in cls), 'undecided box'
mods = []
outdir = os.path.join(root, 'L6CheckKSpec', 'KC')
tot = [0, 0, 0]
for k in range(0, len(cls), per_mod):
    chunk = cls[k:k + per_mod]
    f = sum(1 for t, sm in chunk if t == 'false')
    p = sum(1 for t, sm in chunk if t == 'true')
    m = sum(1 for t, sm in chunk if sm == 'true')
    tot = [tot[0] + f, tot[1] + p, tot[2] + m]
    name = f'Cnt{k // per_mod}'
    ns = f'L6CheckKSpec.KC.{name}'
    L = [f'import L6CheckKSpec.KC.M{k // per_mod}', 'import L6KSpec.Counts', '', 'set_option maxRecDepth 1000000',
         'set_option maxHeartbeats 0', '', f'/-! The classes of the boxes of `KC.M{k // per_mod}`. -/', '', f'namespace {ns}', '',
         f'theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M{k // per_mod}.boxes = some ({f}, {p}, {m}) := by decide +kernel',
         '', f'end {ns}']
    open(os.path.join(outdir, f'{name}.lean'), 'w').write('\n'.join(L) + '\n')
    mods.append((ns, k // per_mod))
# the total by rewriting along the concatenation (allBoxes is M0.boxes ++ (M1.boxes ++ (… ++ Mn.boxes))): every step
# rewrites with the count of one module, so that the kernel never evaluates kcCountsB on the concatenation
nested = ' ++ ('.join(f'L6CheckKSpec.KC.M{j}.boxes' for _, j in mods) + ')' * (len(mods) - 1)
steps = []
for i, (m, _) in enumerate(mods):
    if i + 1 < len(mods):
        steps.append('kcCountsB_append')
    steps.append(f'{m}.cnt')
L = ['import L6CheckKSpec.KC.All', 'import L6SoundKSpec.Counts'] + [f'import {m}' for m, _ in mods] + ['',
     'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '',
     '/-! The counts of all KC boxes. -/', '', 'namespace L6CheckKSpec.KC', '', 'open L6KSpec', '',
     f'theorem counts_ok : kcCountsB allBoxes = some ({tot[0]}, {tot[1]}, {tot[2]}) := by',
     f'  rw [show allBoxes = {nested} from rfl]',
     '  rw [' + ', '.join(steps) + ']',
     '  rfl', '', 'end L6CheckKSpec.KC']
open(os.path.join(outdir, 'Counts.lean'), 'w').write('\n'.join(L) + '\n')
with open(os.path.join(outdir, 'modules_cnt.txt'), 'w') as f:
    for m, _ in mods:
        f.write(f'1 {m}\n')
    f.write('2 L6CheckKSpec.KC.Counts\n')
print('totals', tot, 'modules', len(mods))
