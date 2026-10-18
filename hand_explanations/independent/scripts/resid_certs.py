#!/usr/bin/env python3
"""Exact certificates for the secondary-identity hypotheses of RESIDUAL.md: (gamma) of R1* in class 4 cell 58,
class 28 cell 0, class 53 cell 1; (T3) of TQ in class 0 cell 0; TD in class 15 cell 0. Also float LP for comparison."""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refkit as K
from refkit import O, BODIES
from ref_lp import CellLP, below_everywhere
from ref_exact import certify_positive

CLS = K.classes()
cells = {}
want = {(4, 58), (28, 0), (53, 1), (0, 0), (15, 0)}
for c, i, rec in K.iter_cells({4, 28, 53, 0, 15}):
    if (c, i) in want:
        cells[(c, i)] = rec


def lp(c, i):
    C = K.RCell(cells[(c, i)], c, i)
    return C, CellLP(C, K.RDiag(CLS[c]))


def check(L, small, terms, label):
    """small: list of claimed minimal forms (must be identical); terms: dict label -> form (others)"""
    f0 = small[0][1]
    for lab, f in small[1:]:
        d = L.lin((1, f), (-1, f0))
        assert all(abs(v) < 1e-12 for v in d.values()), ('claimed minimal terms differ', lab)
    allok = True
    for lab, f in terms.items():
        fl, r = below_everywhere(L, f0, f)
        ok, info = certify_positive(L, L.lin((1, f), (-1, f0)))
        allok &= ok and fl
        print('   ', label, lab, 'float:', fl, 'exact:', ok, info if not ok else '')
    return allok


def subset_terms(L, C, col, J):
    t = {}
    for k in J:
        p = L.pos(col, k)
        if p is not None:
            t[('pos', k)] = p
        for j in BODIES:
            if j not in J:
                t[('cross', k, j)] = L.force(col, k, j)
    return t


def torque_terms(L, J):
    t = {}
    Jc = [j for j in BODIES if j not in J]
    for k in J:
        for l in Jc:
            for p, q in ((k, l), (l, k)):
                if L.pos('z', p) is None or L.pos('w', q) is None:
                    continue
                t[('z', p, 'w', q)] = L.lin((1, L.pos('z', p)), (1, L.pos('w', q)), (-3, L.xkl(p, q)))
    return t


res = {}
for (c, i, col, a, b, s) in [(4, 58, 'w', 3, 4, 5), (28, 0, 'w', 2, 3, 4), (53, 1, 'z', 1, 4, 5)]:
    C, L = lp(c, i)
    t = subset_terms(L, C, col, [a, b, s])
    small = [(('pos', a), t.pop(('pos', a))), (('pos', b), t.pop(('pos', b)))]
    print('class', c, 'cell', i, 'S_%s%s: minimal terms exactly pos %d, pos %d' % (col, (a, b, s), a, b))
    res[(c, i)] = check(L, small, t, 'gamma')
C, L = lp(0, 0)
t = torque_terms(L, [3, 4])
small = [(k, t.pop(k)) for k in [('z', 3, 'w', 0), ('z', 3, 'w', 1), ('z', 4, 'w', 0), ('z', 4, 'w', 1)]]
print('class 0 cell 0: T_{3,4} minimal terms exactly z_l w_k, l in {3,4}, k in {0,1}')
res[(0, 0)] = check(L, small, t, 'T3')
C, L = lp(15, 0)
t = torque_terms(L, [0, 3, 4])
small = [(('z', 2, 'w', 0), t.pop(('z', 2, 'w', 0)))]
print('class 15 cell 0: T_{0,3,4} single minimal term z_2 w_0 delta_02^3')
res[(15, 0)] = check(L, small, t, 'TD')
print({str(k): v for k, v in res.items()})
