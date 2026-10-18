#!/usr/bin/env python3
"""Human-readable exact certificates for the secondary identities used by the residual lemmas:
the subset sums of R1* (classes 4/58, 28/0, 53/1), the torque of TQ (class 0 cell 0) and the torque single term of
class 15 cell 0 (TD). Each line: competitor term : sum of multipliers * cell constraints (+ constant) proving that
it is strictly larger than the claimed minimal terms on the whole cell. Output ../data/certificates.txt"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
import exactlp as X
import lemmas_resid as LR

LEGEND = """Constraint labels (all on the relatively open cell; h = node heights):
  ('edge', col, v, c)        h(c) - h(v) > 0 (child deeper than parent)
  ('root>=-2', col)          h(root) + 2 >= 0
  ('O1:z+3w<4', k, l)        4 - zeta_kl - 3 omega_kl > 0      ('zstroke', k, l): zeta + 3 omega - 4 = 0
  ('O1:3z+w<4', k, l)        4 - 3 zeta_kl - omega_kl > 0      ('wstroke', k, l): 3 zeta + omega - 4 = 0
  ('circle', col, k)         a_k + 2 = 0 (resp. b_k)           ('nocircle', col, k): a_k + 2 > 0
  ('argmin', id, t)          e(t) - e(t0) = 0 or > 0 for the first listed minimal term t0 of the base identity id
A certificate d = sum y_i g_i + c (y_i >= 0 on inequalities, free on equalities) proves d > 0.
"""


def show(f, title, C, terms, S):
    ok, certs = C.P.argmin_is(terms, S)
    f.write(f'=== {title}: claimed minimal terms {S}: {"CERTIFIED" if ok else "FAILED"}\n')
    if ok:
        for lab, (y, c) in certs:
            f.write(f'  {lab} : ' + ' + '.join(f'{v}*{l}' for v, l in sorted(y, key=lambda t: str(t[1])))
                    + (f' + {c}' if c else '') + '\n')
    f.write('\n')
    return ok


def main():
    f = open(os.path.join(R.DATA, 'certificates.txt'), 'w')
    f.write(LEGEND + '\n')
    allok = True
    for c, i, col, J, S in ((4, 58, 'w', (3, 4, 5), [('pos', 3), ('pos', 4)]),
                            (28, 0, 'w', (2, 3, 4), [('pos', 2), ('pos', 3)]),
                            (53, 1, 'z', (1, 4, 5), [('pos', 1), ('pos', 4)])):
        rec = R.load_cell(c, i)
        C = LR.Ctx(rec, X.Diag(R.classes()[c]))
        allok &= show(f, f'class {c} cell {i}: subset sum S_{col}{J}', C, C.P.subset_terms(col, J), S)
    rec = R.load_cell(0, 0)
    C = LR.Ctx(rec, X.Diag(R.classes()[0]))
    allok &= show(f, 'class 0 cell 0: torque T_{3,4} (terms zw(p,q) = delta_pq^3 z_p w_q)', C, C.P.torque_terms((3, 4)),
                  [('zw', l, k) for l in (3, 4) for k in (0, 1)])
    rec = R.load_cell(15, 0)
    C = LR.Ctx(rec, X.Diag(R.classes()[15]))
    allok &= show(f, 'class 15 cell 0: torque T_{0,3,4}', C, C.P.torque_terms((0, 3, 4)), [('zw', 2, 0)])
    f.write('ALL CERTIFIED\n' if allok else 'FAILURES\n')
    print('all certified' if allok else 'FAILURES')


if __name__ == '__main__':
    main()
