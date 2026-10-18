#!/usr/bin/env python3
"""Order calculus as a mixed-integer LP (independent of the engine's tree search).

Unknowns per colour: an ultrametric u on V = {0..n-1} u {O} (O = n), values in [-2, CAP]; u(k, O) = exponent of the
position (CAP stands for 'CAP or more', including +inf = body at O); u(k, l) = zeta_kl (resp. omega_kl).
Constraint groups (names as in the engine's docstring, tengine.py):
  T   ultrametric: in every triple of V the minimum is attained at least twice; all values >= -2 (root >= -2)
  O   (O1), (O2): zeta + 3 omega <= 4 (= 4 iff z-stroke), 3 zeta + omega <= 4 (= 4 iff w-stroke)
  C   k z-circled iff u_z(k, O) = -2 (else >= -2 + s); same in w
  M   centre of mass: the root has at least three children (three points of V pairwise at the global minimum)
  B   body equations: min over {a_k} u {-(zeta_kl + 3 omega_kl)/2} attained twice (bodies without a stroke of that
      colour); same in w
  U   min over {0} u {-x_kl} attained twice (only if fewer than two zw-edges)
  I   min over {0} u {2 x_kl} attained twice
  Ip  min over {0} u {a_k + b_k} attained twice
Strict inequalities carry the slack s (maximized); feasible iff max s > EPS.
A linear threshold 'phi(x) + s <= 0' (phi = weighted sum of x) can be added.
"""
import itertools, json, os, sys
import numpy as np
import highspy

CAP = 5.0
BIGM = 16.0
EPS = 1e-3
E = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'diagrams') + '/'


class Model:
    def __init__(self):
        self.lb, self.ub, self.integ, self.names = [], [], [], []
        self.rows = []          # (dict, lo, hi)

    def var(self, lb, ub, integ=False, name=''):
        self.lb.append(lb); self.ub.append(ub); self.integ.append(integ); self.names.append(name)
        return len(self.lb) - 1

    def add(self, coefs, lo=None, hi=None):
        self.rows.append((coefs, lo, hi))

    def solve(self, obj, time_limit=None):
        h = highspy.Highs()
        h.setOptionValue('output_flag', False)
        h.setOptionValue('threads', 1)
        h.setOptionValue('mip_rel_gap', 0.0)
        if time_limit:
            h.setOptionValue('time_limit', float(time_limit))
        nv = len(self.lb)
        lp = highspy.HighsLp()
        lp.num_col_ = nv
        lp.num_row_ = len(self.rows)
        cost = np.zeros(nv)
        for j, c in obj.items():
            cost[j] = c
        lp.col_cost_ = cost
        lp.col_lower_ = np.array(self.lb, dtype=float)
        lp.col_upper_ = np.array(self.ub, dtype=float)
        lp.sense_ = highspy.ObjSense.kMaximize
        starts, idx, vals, rlo, rhi = [0], [], [], [], []
        for coefs, a, b in self.rows:
            for j, c in coefs.items():
                if c != 0:
                    idx.append(j); vals.append(float(c))
            starts.append(len(idx))
            rlo.append(-highspy.kHighsInf if a is None else float(a))
            rhi.append(highspy.kHighsInf if b is None else float(b))
        lp.row_lower_ = np.array(rlo)
        lp.row_upper_ = np.array(rhi)
        lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
        lp.a_matrix_.start_ = np.array(starts, dtype=np.int32)
        lp.a_matrix_.index_ = np.array(idx, dtype=np.int32)
        lp.a_matrix_.value_ = np.array(vals)
        lp.a_matrix_.num_col_ = nv
        lp.a_matrix_.num_row_ = len(self.rows)
        lp.integrality_ = [highspy.HighsVarType.kInteger if t else highspy.HighsVarType.kContinuous
                           for t in self.integ]
        h.passModel(lp)
        h.run()
        st = h.getModelStatus()
        if st != highspy.HighsModelStatus.kOptimal:
            # time limit: keep an incumbent if there is one (a feasible point is a valid witness)
            try:
                info = h.getInfo()
                if info.primal_solution_status >= 2:
                    sol = np.array(h.getSolution().col_value)
                    return info.objective_function_value, sol, 'incumbent:' + str(st)
            except Exception:
                pass
            return None, None, str(st)
        sol = np.array(h.getSolution().col_value)
        return h.getInfo().objective_function_value, sol, 'ok'


def lin(*pairs):
    d = {}
    for c, j in pairs:
        d[j] = d.get(j, 0.0) + c
    return d


def min_twice(Mo, terms, lo=-2.0):
    """terms: list of (coef dict, const). Adds: the minimum of the terms is attained at least twice."""
    mu = Mo.var(-BIGM, BIGM, name='mu')
    es = []
    for coefs, k in terms:
        # term - mu >= 0
        d = dict(coefs); d[mu] = d.get(mu, 0.0) - 1.0
        Mo.add(d, -k, None)
        e = Mo.var(0, 1, True, name='e')
        es.append(e)
        # e = 1 => term - mu <= 0 :  term - mu + BIGM e <= BIGM
        d = dict(coefs); d[mu] = d.get(mu, 0.0) - 1.0; d[e] = BIGM
        Mo.add(d, None, BIGM - k)
    Mo.add({e: 1.0 for e in es}, 2, None)


def build(n, cls, groups, phi_weights=None):
    """Returns (model, handles). cls: a class dict of n6.json."""
    zs = {(int(k[0]), int(k[1])) for k, v in cls['edges'].items() if v & 1}
    ws = {(int(k[0]), int(k[1])) for k, v in cls['edges'].items() if v & 2}
    zc, wc = set(cls['zcircles']), set(cls['wcircles'])
    O = n
    V = list(range(n + 1))
    vp = list(itertools.combinations(V, 2))
    Mo = Model()
    s = Mo.var(0.0, 1.0, name='s')
    U = {}
    for col in 'zw':
        for p, q in vp:
            U[col, p, q] = U[col, q, p] = Mo.var(-2.0, CAP, name=f'{col}{p}{q}')
    # T: ultrametric
    for col in 'zw':
        for a, b, c in itertools.combinations(V, 3):
            A, B, C = U[col, a, b], U[col, a, c], U[col, b, c]
            ts = []
            for big, x, y in ((C, A, B), (B, A, C), (A, B, C)):
                t = Mo.var(0, 1, True, name='t')
                ts.append(t)
                # t = 1 => x = y <= big
                Mo.add({x: 1, y: -1, t: BIGM}, None, BIGM)
                Mo.add({y: 1, x: -1, t: BIGM}, None, BIGM)
                Mo.add({x: 1, big: -1, t: BIGM}, None, BIGM)
            Mo.add({t: 1 for t in ts}, 1, 1)
    bp = list(itertools.combinations(range(n), 2))
    if 'O' in groups:
        for k, l in bp:
            Z, W = U['z', k, l], U['w', k, l]
            if (k, l) in zs:
                Mo.add({Z: 1, W: 3}, 4, 4)
            else:
                Mo.add({Z: 1, W: 3, s: 1}, None, 4)
            if (k, l) in ws:
                Mo.add({Z: 3, W: 1}, 4, 4)
            else:
                Mo.add({Z: 3, W: 1, s: 1}, None, 4)
    if 'C' in groups:
        for k in range(n):
            for col, circ in (('z', zc), ('w', wc)):
                a = U[col, k, O]
                if k in circ:
                    Mo.add({a: 1}, -2, -2)
                else:
                    Mo.add({a: 1, s: -1}, -2, None)
    if 'M' in groups:
        for col in 'zw':
            h = Mo.var(-2.0, CAP, name='h')
            for p, q in vp:
                Mo.add({U[col, p, q]: 1, h: -1}, 0, None)
            vs = []
            for a, b, c in itertools.combinations(V, 3):
                v = Mo.var(0, 1, True, name='v')
                vs.append(v)
                for p, q in ((a, b), (a, c), (b, c)):
                    Mo.add({U[col, p, q]: 1, h: -1, v: BIGM}, None, BIGM)
            Mo.add({v: 1 for v in vs}, 1, None)
    if 'B' in groups:
        for col, strokes in (('z', zs), ('w', ws)):
            for k in range(n):
                if any(k in e for e in strokes):
                    continue
                terms = [({U[col, k, O]: 1.0}, 0.0)]
                for l in range(n):
                    if l == k:
                        continue
                    Z, W = U['z', k, l], U['w', k, l]
                    terms.append(({Z: -0.5, W: -1.5} if col == 'z' else {Z: -1.5, W: -0.5}, 0.0))
                min_twice(Mo, terms)
    zw = [e for e in bp if e in zs and e in ws]
    if 'U' in groups and len(zw) < 2:
        terms = [({}, 0.0)] + [({U['z', k, l]: -0.5, U['w', k, l]: -0.5}, 0.0) for k, l in bp]
        min_twice(Mo, terms)
    if 'I' in groups:
        terms = [({}, 0.0)] + [({U['z', k, l]: 1.0, U['w', k, l]: 1.0}, 0.0) for k, l in bp]
        min_twice(Mo, terms)
    if 'Ip' in groups:
        terms = [({}, 0.0)] + [({U['z', k, O]: 1.0, U['w', k, O]: 1.0}, 0.0) for k in range(n)]
        min_twice(Mo, terms)
    if phi_weights is not None:
        d = {s: 1.0}
        for (k, l), wgt in zip(bp, phi_weights):
            if wgt:
                d[U['z', k, l]] = d.get(U['z', k, l], 0.0) + 0.5 * wgt
                d[U['w', k, l]] = d.get(U['w', k, l], 0.0) + 0.5 * wgt
        Mo.add(d, None, 0.0)
    return Mo, {'s': s, 'U': U, 'n': n}


def seven_weights(n, a, b):
    return [1.0 if (k, l) == (a, b) or not ({k, l} & {a, b}) else 0.0 for k, l in itertools.combinations(range(n), 2)]


def witness(Mo, H, sol):
    n = H['n']
    U = H['U']
    out = {}
    for col in 'zw':
        out[col] = {f'{p}{q}': round(sol[U[col, p, q]], 9) for p, q in itertools.combinations(range(n + 1), 2)}
    out['x'] = {f'{k}{l}': round(0.5 * (sol[U['z', k, l]] + sol[U['w', k, l]]), 9)
                for k, l in itertools.combinations(range(n), 2)}
    return out


def test(n, cls, groups, phi=None, time_limit=None):
    Mo, H = build(n, cls, groups, phi)
    val, sol, st = Mo.solve({H['s']: 1.0}, time_limit)
    if val is None:
        return None, None, st
    if val > EPS:
        return True, witness(Mo, H, sol), round(val, 6)
    if st != 'ok':
        return None, None, st
    return False, None, round(val, 9)


if __name__ == '__main__':
    n = 6
    cls = json.load(open(E + 'n6.json'))['classes']
    ci = int(sys.argv[1])
    groups = sys.argv[2].split(',')
    pair = sys.argv[3] if len(sys.argv) > 3 else None
    phi = seven_weights(n, int(pair[0]), int(pair[1])) if pair else None
    import time
    t = time.time()
    ok, w, info = test(n, cls[ci], groups, phi)
    print(json.dumps({'class': ci, 'groups': groups, 'pair': pair, 'feasible': ok, 'info': info,
                      'time': round(time.time() - t, 2), 'witness': w}))
