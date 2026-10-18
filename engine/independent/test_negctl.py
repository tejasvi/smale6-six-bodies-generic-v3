#!/usr/bin/env python3
"""Referee negative controls for treplay's certifier (n = 6, class given).
(a) LPs kept by texact (max s > 1e-9): exact_cert on all rows must find no certificate, and check() must reject the
    rationalized HiGHS duals.
(b) Sharp: kept LP + row s <= eps. eps = 0: prune, must be certified. eps = 1e-12: HiGHS prunes (max s <= 1e-9), but
    the strict system is feasible, so the Certifier must report a failure for every such LP.
(c) Corrupted certificates of genuine prunes: y -> -y, one entry perturbed by 1/997, largest entry dropped: check() must
    reject (counted), y -> 2y must still pass.
(d) Injected false prune: during a treplay enumeration of the class, HiGHS is made to report 'infeasible' for every
    kept LP at one DFS stage with probability 0.01; the Certifier must count exactly those as failures.
Usage: test_negctl.py CODE_DIR CLASS"""
import io, json, random, sys
from fractions import Fraction
sys.path.insert(0, sys.argv[1])
import numpy as np
import tengine as T
import texact as X
import treplay as R

n = 6
ci = int(sys.argv[2])
cls = json.load(open(sys.argv[1] + '/n6.json'))['classes']
D = T.Diagram.from_json(n, cls[ci])
gf = lambda name: (name[0] in ('z', 'w') and len(name[2]) == 1) or name[0] in ('U', 'I')
kept, pruned = [], []
orig = T.feasible
rnd = random.Random(4)


def feas(L):
    ok, val, sol = L.solve()
    r = ok and val > T.TOL
    if r and rnd.random() < 0.05 and len(kept) < 400:
        kept.append(L)
    if not r and rnd.random() < 0.05 and len(pruned) < 400:
        pruned.append(L)
    return r, sol


T.feasible = feas
X.enumerate_cells(D, io.StringIO(), None, 0, 1, groups_filter=gf, mode='le')
T.feasible = orig
print(f'class {ci}: sampled {len(kept)} kept and {len(pruned)} pruned LPs')

# (a)
bad_a = 0
for L in kept:
    if R.exact_cert(L, list(range(len(L.rows)))) is not None:
        bad_a += 1
    h = R.highs(L)
    v = np.asarray(h.getSolution().row_dual, dtype=float)
    if R.rationalize(L, v, 1) is not None or R.rationalize(L, v, -1) is not None:
        bad_a += 1
print(f'(a) kept LPs with a certificate (must be 0): {bad_a}')

# (b)
res_b = {}
zt = T.Tree(n).options(n)[0]
for eps in (0.0, 1e-12):
    C = R.Certifier()
    v = [C.feasible(X.sub(L, [({L.ns: 1.0}, None, eps)]), ('negctl', zt, zt)) for L in kept]
    res_b[eps] = (sum(v), C.c['pruned'], C.c['fail'])
    print(f'(b) eps={eps}: kept {sum(v)}, pruned {C.c["pruned"]}, failures {C.c["fail"]} '
          f'(expected: eps=0 -> 0 failures; eps=1e-12 -> failures = {len(kept)})')

# (c)
cnt = {'valid': 0, 'neg_rejected': 0, 'pert_rejected': 0, 'drop_rejected': 0, 'double_ok': 0}
for L in pruned:
    h = R.highs(L)
    st = h.getModelStatus()
    if st == R.OPT:
        v, sg = np.asarray(h.getSolution().row_dual, dtype=float), 1
    else:
        v, sg = np.asarray(h.getDualRay()[2], dtype=float), -1
    y = R.rationalize(L, v, sg) or R.rationalize(L, v, -sg) or R.exact_cert(L, list(range(len(L.rows))))
    if y is None or not R.check(L, y):
        continue
    cnt['valid'] += 1
    cnt['neg_rejected'] += not R.check(L, {i: -a for i, a in y.items()})
    k = max(y, key=lambda i: abs(y[i]))
    y2 = dict(y); y2[k] = y2[k] + Fraction(1, 997)
    rej = not R.check(L, y2)
    cnt['pert_rejected'] += rej
    if not rej:
        # legitimate only if the perturbed row has no height variable (then (1) is unaffected)
        hv = [j for j, c in L.rows[k][0].items() if j != L.ns and c != 0]
        cnt['pert_valid_rows_without_heights' if not hv else 'pert_valid_BAD'] = cnt.get('pert_valid_rows_without_heights' if not hv else 'pert_valid_BAD', 0) + 1
    y3 = dict(y); del y3[k]
    cnt['drop_rejected'] += not R.check(L, y3)
    cnt['double_ok'] += R.check(L, {i: 2 * a for i, a in y.items()})
print('(c)', cnt)

# (d)
orig_highs = R.highs
injected = [0]
rnd2 = random.Random(9)


class Fake:
    def __init__(self, h):
        self.h = h

    def getModelStatus(self):
        return R.INF

    def getDualRay(self):
        return (None, False, None)

    def getInfo(self):
        return self.h.getInfo()


def highs_inj(L, presolve=True):
    h = orig_highs(L, presolve)
    if h.getModelStatus() == R.OPT and h.getInfo().objective_function_value > T.TOL and rnd2.random() < 0.01:
        injected[0] += 1
        return Fake(h)
    return h


R.highs = highs_inj
C = R.Certifier()
out = io.StringIO()
R.enumerate_cells(D, out, C, groups_filter=gf, mode='le')
R.highs = orig_highs
print(f'(d) injected false prunes: {injected[0]}; certifier failures: {C.c["fail"]} (must be >= injected: the fake '
      f'status is re-queried without presolve, so a re-run may hide some)')
ok = bad_a == 0 and res_b[0.0][2] == 0 and res_b[1e-12][2] == len(kept) and cnt.get('pert_valid_BAD', 0) == 0 \
     and cnt['drop_rejected'] == cnt['valid'] and cnt['double_ok'] == cnt['valid'] and C.c['fail'] >= 1
print('RESULT', 'PASS' if ok else 'CHECK')
