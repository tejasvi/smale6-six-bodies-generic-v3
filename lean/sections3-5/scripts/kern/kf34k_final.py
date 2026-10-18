#!/usr/bin/env python3
"""Writes ROOT/L6CheckF/Final.lean: the exclusion of Propositions 4.5 and 5.3 for all classes (`fusedK`), from the class
theorems of the kernel run (`L6CheckF.C<k>.classOK`) and the open classes, with the diagram of class `k` taken from the
literal class list of the kernel F1 (`L6CheckK.F1.classes6L`) and the certificates of the cores from the list
`L6CheckF.csAll`; and ROOT/L6CheckF/deps_final.txt for the build scheduler.
Usage: kf34k_final.py ROOT"""
import os, sys

root = sys.argv[1]
openc = [31, 124, 127, 132, 133, 143, 147]
classes = [k for k in range(191) if k not in openc]
out = os.path.join(root, 'L6CheckF')
L = [f'import L6CheckF.C{k}.All' for k in classes] + ['import L6CheckK.F1.Reps.All', 'import L6Sound.F34S.Defs', '',
     '/-! # The exclusion of Propositions 4.5 and 5.3, by the kernel',
     '',
     'For every class `k < 191` and every pair of complete trees with heights satisfying `Cond` for the diagram of the',
     'class, the class is one of the open classes or the claim of the cell of the pair holds with the certificate of a',
     'core from the list `csAll` (`ClaimMeaningFinK csAll`): the conclusion of lean6\'s `f34s_excluded` with the',
     'certificates from a finite list and argmin sets without repetition, with the diagram of class `k` read from the',
     'literal class list of the kernel F1 (`L6CheckK.F1.classes6L`), checked by the kernel run of the search with the',
     'claims at every cell (`L6CheckF.C<k>.classOK`). -/', '',
     'namespace L6CheckF', '', 'open L6 L6.F2S L6.F34S L6K.F34K', '',
     '/-- The diagram of class `k`, from the literal class list. -/',
     'def diagOfL (k : Nat) : L6.F2.Diag := L6.F2.Diag.ofF1 (L6CheckK.F1.classes6L.getD k default).1', '',
     '/-- **Propositions 4.5 and 5.3 for every pair satisfying `Cond`, by the kernel.** -/',
     'theorem fusedK : ∀ k < 191, ∀ Xz Xw : ExpTree, Cond (diagOfL k) Xz Xw →',
     '    k ∈ openClasses ∨ ClaimMeaningFinK csAll Xz Xw := by',
     '  intro k hk',
     '  match k, hk with']
for k in range(191):
    if k in openc:
        L.append(f'  | {k}, _ => exact fun _ _ _ => Or.inl (by decide)')
    else:
        L.append(f'  | {k}, _ => exact fun Xz Xw hX => Or.inr (C{k}.classOK Xz Xw hX)')
L += ['  | _ + 191, h => exact absurd h (by omega)', '', 'end L6CheckF']
open(os.path.join(out, 'Final.lean'), 'w').write('\n'.join(L) + '\n')
open(os.path.join(out, 'deps_final.txt'), 'w').write(
    'L6CheckF.Final: ' + ' '.join(f'L6CheckF.C{k}.All' for k in classes) + '\n')
print('final', len(classes), 'classes')
