#!/usr/bin/env python3
"""Writes the kernel Macaulay checks of §7.2 (lean6_special `Comp.K4.E4.Run`) under ROOT/L6CheckKSpec/E4/:
modules <fam><mu>_<k>.lean with PER patterns each (`e4_data` computes the selection and the inverse at elaboration,
`decide +kernel` checks `macCheckK`), for the forms F (729 patterns, `formsF`, n = 4, D = 7) and G (64 patterns,
`formsGK`, n = 3, D = 8) at mu = (1,1,1,1) and (3,5,7,11); and All.lean with the four statements
`all<fam><mu> : ∀ i, i < N → ∃ sel B, macCheckK … = true` by cases on i.
Usage: ke4_gen.py ROOT PER"""
import os, sys

root, per = sys.argv[1], int(sys.argv[2])
out = os.path.join(root, 'L6CheckKSpec', 'E4')
os.makedirs(out, exist_ok=True)
fams = [('F', 729, 'formsF', 4, 7, 'patsF'), ('G', 64, 'formsGK', 3, 8, 'patsG')]
mus = [('1111', '[1, 1, 1, 1]', '(1, 1, 1, 1)'), ('3_5_7_11', '[3, 5, 7, 11]', '(3, 5, 7, 11)')]
mods, alls = [], []
for fam, npat, forms, n, D, pats in fams:
    for mtag, mu, mut in mus:
        ns = f'{fam}{mtag}'
        for k in range(0, npat, per):
            name = f'{ns}_{k // per}'
            L = ['import L6KSpec.E4Data', '', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '',
                 f'/-! Macaulay checks of the forms `{fam}` at `μ = {mut}`, '
                 f'patterns {k}–{min(k + per, npat) - 1}. -/', '',
                 f'namespace L6CheckKSpec.E4.{ns}', '', 'open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4', '']
            for i in range(k, min(k + per, npat)):
                L.append(f'e4_data P{i} {fam} {mu} {i}')
                L.append(f'theorem ok{i} : macCheckK {n} {D} pE sE ({forms} {mu} ({pats}.getD {i} [])) P{i}.sel '
                         f'P{i}.B = true := by\n  decide +kernel')
                L.append('')
            L.append(f'end L6CheckKSpec.E4.{ns}')
            open(os.path.join(out, name + '.lean'), 'w').write('\n'.join(L) + '\n')
            mods.append(f'L6CheckKSpec.E4.{name}')
        A = [f'theorem all{ns} : ∀ i, i < {npat} → ∃ sel B,\n'
             f'    macCheckK {n} {D} pE sE ({forms} {mu} ({pats}.getD i [])) sel B = true']
        A += [f'  | {i}, _ => ⟨_, _, {ns}.ok{i}⟩' for i in range(npat)]
        A += [f'  | _ + {npat}, h => absurd h (by omega)', '']
        alls.append('\n'.join(A))
L = [f'import {m}' for m in mods] + ['', '-- the matches over 729 patterns', 'set_option maxRecDepth 100000', '',
                                    '/-! The Macaulay checks of all patterns, by cases on the pattern. -/', '',
     'namespace L6CheckKSpec.E4', '', 'open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4', ''] + alls + \
    ['end L6CheckKSpec.E4']
open(os.path.join(out, 'All.lean'), 'w').write('\n'.join(L) + '\n')
print('modules', len(mods))
