#!/usr/bin/env python3
"""Exact replay of texact.py: the same enumeration (copied DFS, same HiGHS model and verdict rule, same output lines),
with every LP prune certified in exact rational arithmetic. All other cuts of the DFS are combinatorial, so OUT is
complete when every prune is certified; if OUT equals texact.py's output, that output is complete too.

An LP (tengine.LP) has rows lo_i <= a_i . v + c_i s <= hi_i (v = tree heights, free; s = slack, 0 <= s <= 1;
lo_i, hi_i may be absent). The data are binary floats (small dyadic rationals), read exactly. A prune
(tengine.feasible False) claims: no point of the LP has s > 0. Certificate: rationals y_i, one per row, with y_i > 0
only if hi_i exists and y_i < 0 only if lo_i exists (any sign on equality and ranged rows), such that, with
b_i = hi_i if y_i > 0 else lo_i,
  (1) sum_i y_i a_ij = 0 for every height variable j;
  (2) with g = sum_i y_i c_i, B = sum_i y_i b_i, nu = max(0, -g), gamma = g + nu, beta = B + nu:
      beta <= 0 and (gamma > 0 or beta < 0);
  (3) if nu > 0: every row is monotone in s (c_i > 0 only on rows without lo_i, c_i < 0 only on rows without hi_i).
Validity: summing y_i times row i gives g s <= B at every point; with nu s <= nu (s <= 1), gamma s <= beta. A point
with 0 < s <= 1 gives 0 <= gamma s <= beta <= 0, so gamma = beta = 0, against (2). By (3) a point with s > 1 yields
one with s = 1 (lower s), so no point has s > 0. Conversely such y exists iff the prune is correct (Motzkin).
Paths: (rat) HiGHS row duals (optimal, max s <= 1e-9) or dual ray (infeasible), rounded by limit_denominator (bound
10^6, then 1, 2, 12, 144, 10^4); (supp) exact phase-1 simplex (fmpq, Bland's rule) for the certificate LP on the rows
in the support of the float multipliers; (full) the same on all rows; a prune with none is a failure. Every
certificate is checked by check() in Fractions. Feasible verdicts with max s < 1e-6 are listed as borderline (kept,
as in texact).
Usage: treplay.py N CLASSES_JSON IDX OUT.jsonl [--mode le|ge] [--base] [--split DEPTH --part K --nparts P]
       [--ref TEXACT_OUT.jsonl]
Output: OUT.jsonl (as texact.py) and OUT.replay.json (counts, borderline and failed nodes, comparison with --ref)."""
import json, os, sys, time
from fractions import Fraction
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')      # numpy's BLAS threads only burn CPU here
import numpy as np
import highspy
from flint import fmpq
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tengine as T
import texact as X
import tsign

BORDER = 1e-6
DENOMS = (10 ** 6, 1, 2, 12, 144, 10 ** 4)
OPT, INF = highspy.HighsModelStatus.kOptimal, highspy.HighsModelStatus.kInfeasible
MAXLIST = 2000


def highs(L, presolve=True):
    """The model of tengine.LP.solve (maximize s, 0 <= s <= 1), built and run the same way; returns the Highs object."""
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    if not presolve:
        h.setOptionValue('presolve', 'off')
    nv = L.nv
    lp = highspy.HighsLp()
    lp.num_col_ = nv
    lp.num_row_ = len(L.rows)
    cost = np.zeros(nv)
    cost[L.ns] = 1.0
    lp.col_cost_ = cost
    lo = np.full(nv, -highspy.kHighsInf)
    hi = np.full(nv, highspy.kHighsInf)
    lo[L.ns] = 0.0
    hi[L.ns] = 1.0
    lp.col_lower_ = lo
    lp.col_upper_ = hi
    lp.sense_ = highspy.ObjSense.kMaximize
    starts, idx, vals, rlo, rhi = [0], [], [], [], []
    for coefs, a, b in L.rows:
        for j, c in coefs.items():
            if c != 0:
                idx.append(j)
                vals.append(float(c))
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
    lp.a_matrix_.num_row_ = len(L.rows)
    h.passModel(lp)
    h.run()
    return h


def monotone(L):
    """Every row is kept when s decreases."""
    for coefs, lo, hi in L.rows:
        c = coefs.get(L.ns, 0)
        if (c > 0 and lo is not None) or (c < 0 and hi is not None):
            return False
    return True


def fr(x, cache={}):
    """The exact rational value of a float or int (cached)."""
    r = cache.get(x)
    if r is None:
        r = cache[x] = Fraction(x)
    return r


def check(L, y):
    """Exact check of the certificate y (row index -> Fraction): conditions (1)-(3) of the module docstring."""
    ns = L.ns
    comb, g, B = {}, Fraction(0), Fraction(0)
    for i, yi in y.items():
        if yi == 0:
            continue
        coefs, lo, hi = L.rows[i]
        bd = hi if yi > 0 else lo
        if bd is None:
            return False
        B += yi * fr(bd)
        for j, c in coefs.items():
            if j == ns:
                g += yi * fr(c)
            else:
                comb[j] = comb.get(j, 0) + yi * fr(c)
    if any(v != 0 for v in comb.values()):
        return False
    nu = max(Fraction(0), -g)
    if nu > 0 and not monotone(L):
        return False
    gam, beta = g + nu, B + nu
    return beta <= 0 and (gam > 0 or beta < 0)


def rationalize(L, v, sign):
    """Round the float multipliers v (times sign) by limit_denominator, first with the bound 10^6 (exact when the float
    error is small), then with growing bounds; the first vector that checks, or None."""
    a = np.abs(v)
    m = a.max() if len(a) else 0.0
    if not m > 0:
        return None
    nz = [(int(i), sign * float(v[i])) for i in np.nonzero(a > 1e-9 * m)[0]]
    tried = []
    for D in DENOMS:
        y = {i: Fraction(x).limit_denominator(D) for i, x in nz}
        if y not in tried:
            if check(L, y):
                return y
            tried.append(y)
    return None


def q(x):
    return fmpq(*x.as_integer_ratio())


def phase1(cols, m, rhs):
    """Exact phase 1 (Bland's rule): x >= 0 with sum_k x_k cols[k] = rhs (rhs >= 0; cols sparse {row: fmpq}).
    Returns {k: x_k > 0} or None if there is no such x."""
    N = len(cols)
    W = N + m
    Z = fmpq(0)
    A = [[Z] * (W + 1) for _ in range(m)]
    for k, col in enumerate(cols):
        for r, v in col.items():
            A[r][k] = v
    for r in range(m):
        A[r][N + r] = fmpq(1)
        A[r][W] = fmpq(rhs[r])
    basis = [N + r for r in range(m)]
    d = [-sum((A[r][k] for r in range(m)), Z) for k in range(N)] + [Z] * m + [-sum((A[r][W] for r in range(m)), Z)]
    while True:                                  # objective (sum of artificials) = -d[W]; reduced costs d[:W]
        k = next((k for k in range(W) if d[k] < 0), None)
        if k is None:
            break
        best = None
        for r in range(m):
            if A[r][k] > 0:
                ratio = A[r][W] / A[r][k]
                if best is None or ratio < best[0] or (ratio == best[0] and basis[r] < basis[best[1]]):
                    best = (ratio, r)
        r = best[1]                              # always exists: the objective is bounded below by 0
        piv = A[r][k]
        Ar = [a / piv for a in A[r]]
        A[r] = Ar
        for r2 in range(m):
            f = A[r2][k]
            if r2 != r and f != 0:
                A[r2] = [a - f * b for a, b in zip(A[r2], Ar)]
        f = d[k]
        d = [a - f * b for a, b in zip(d, Ar)]
        basis[r] = k
    if d[W] != 0:
        return None
    return {basis[r]: A[r][W] for r in range(m) if basis[r] < N and A[r][W] != 0}


def exact_cert(L, R):
    """Certificate supported on the rows R by phase1 on the certificate LP: u_i, w_i >= 0 (multipliers of the upper and
    lower sides), nu >= 0 (if monotone), p, q >= 0; sum (u_i - w_i) a_ij = 0 (heights j), g + nu - p = 0,
    B + nu + q = 0, p + q = 1 (so gamma = p >= 0, beta = -q <= 0, not both 0). Returns y or None (none on R)."""
    ns = L.ns
    hv = sorted({j for i in R for j, c in L.rows[i][0].items() if j != ns and c != 0})
    hrow = {j: k for k, j in enumerate(hv)}
    rg, rb, rn = len(hv), len(hv) + 1, len(hv) + 2
    cols, lab = [], []
    for i in R:
        coefs, lo, hi = L.rows[i]
        for sg, bd in ((1, hi), (-1, lo)):
            if bd is None:
                continue
            col = {}
            for j, c in coefs.items():
                if c != 0:
                    r = rg if j == ns else hrow[j]
                    col[r] = col.get(r, fmpq(0)) + sg * q(c)
            if bd != 0:
                col[rb] = sg * q(bd)
            cols.append(col)
            lab.append((i, sg))
    if monotone(L):
        cols.append({rg: fmpq(1), rb: fmpq(1)})
        lab.append((None, 0))
    cols.append({rg: fmpq(-1), rn: fmpq(1)})
    cols.append({rb: fmpq(1), rn: fmpq(1)})
    lab += [(None, 0), (None, 0)]
    x = phase1(cols, len(hv) + 3, [0] * (len(hv) + 2) + [1])
    if x is None:
        return None
    y = {}
    for k, val in x.items():
        i, sg = lab[k]
        if i is not None:
            y[i] = y.get(i, Fraction(0)) + sg * Fraction(int(val.p), int(val.q))
    return y


def one_thread():
    """Start the HiGHS task scheduler with one thread (by default it starts a pool of half the cores; the serial dual
    simplex used for these LPs does not depend on it)."""
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('threads', 1)
    h.addVar(0.0, 1.0)
    h.run()


def ctx_json(ctx):
    """A node of the DFS: (stage, ztree, wtree, details...)."""
    return {'stage': ctx[0], 'ztree': X.tree_json(ctx[1]), 'wtree': X.tree_json(ctx[2]), 'extra': list(ctx[3:])}


class Certifier:
    """tengine.feasible with exact certificates for the prunes."""

    def __init__(self):
        self.c = {k: 0 for k in ('lp', 'kept', 'pruned', 'st_opt', 'st_inf', 'st_other', 'resolve', 'rat_dual',
                                 'rat_ray', 'supp', 'full', 'fail', 'border')}
        self.border, self.fails = [], []
        self.tmax = 0.0
        self.min_kept = float('inf')           # least max s over the kept LPs
        self.max_pruned = float('-inf')        # largest max s over the prunes with an optimal status

    def feasible(self, L, ctx):
        c = self.c
        c['lp'] += 1
        h = highs(L)
        st = h.getModelStatus()
        if st == OPT:
            val = h.getInfo().objective_function_value
            if val > T.TOL:
                c['kept'] += 1
                self.min_kept = min(self.min_kept, val)
                if val < BORDER:
                    c['border'] += 1
                    if len(self.border) < MAXLIST:
                        self.border.append(dict(ctx_json(ctx), slack=val))
                return True
            self.max_pruned = max(self.max_pruned, val)
        t = time.time()
        c['pruned'] += 1
        c['st_opt' if st == OPT else 'st_inf' if st == INF else 'st_other'] += 1
        v, sign, kind = None, 1, None
        if st != OPT and st != INF:
            c['resolve'] += 1
            h = highs(L, presolve=False)
            st = h.getModelStatus()
        if st == OPT:
            v, sign, kind = np.asarray(h.getSolution().row_dual, dtype=float), 1, 'rat_dual'
        elif st == INF:
            _, has, ray = h.getDualRay()
            if not has:
                c['resolve'] += 1
                h = highs(L, presolve=False)
                if h.getModelStatus() == INF:
                    _, has, ray = h.getDualRay()
            if has:
                v, sign, kind = np.asarray(ray, dtype=float), -1, 'rat_ray'
        ok = False
        if v is not None:
            y = rationalize(L, v, sign)
            if y is None:
                y = rationalize(L, v, -sign)
            if y is not None:
                c[kind] += 1
                ok = True
            else:
                a = np.abs(v)
                R = [int(i) for i in np.nonzero(a > 1e-9 * a.max())[0]] if len(a) and a.max() > 0 else []
                y = exact_cert(L, R) if R else None
                if y is not None and check(L, y):
                    c['supp'] += 1
                    ok = True
        if not ok:
            y = exact_cert(L, list(range(len(L.rows))))
            if y is not None and check(L, y):
                c['full'] += 1
                ok = True
        self.tmax = max(self.tmax, time.time() - t)
        if not ok:
            # no certificate: the verdict is not used as a prune (the branch is kept, which is always safe); counted
            c['fail'] += 1
            if len(self.fails) < MAXLIST:
                self.fails.append(dict(ctx_json(ctx), status=str(st), rows=[[{str(j): a for j, a in co.items()}, lo, hi]
                                                                            for co, lo, hi in L.rows]))
            return True
        return False


def exact_argmins(L0, extra, terms, stats, C, ctx):
    """texact.exact_argmins with certified verdicts."""
    s = L0.ns
    N = len(terms)
    res = []

    def diff(a, b):
        return T.lin_sub(terms[a], terms[b])

    def rec(j, first, ins, outs, rows):
        if j == N:
            if first is not None and len(ins) >= 2:
                res.append((tuple(ins), list(rows)))
            return
        if first is None:
            new = []
            for o in outs:
                d, k = diff(o, j)
                dd = dict(d)
                dd[s] = dd.get(s, 0.0) - 1.0
                new.append((dd, -k, None))
            nrows = rows + new
            stats['lp'] += 1
            if C.feasible(X.sub(L0, extra + nrows), ctx + ([j, 'in', ins, outs],)):
                rec(j + 1, j, ins + [j], outs, nrows)
        else:
            d, k = diff(j, first)
            nrows = rows + [(d, -k, -k)]
            stats['lp'] += 1
            if C.feasible(X.sub(L0, extra + nrows), ctx + ([j, 'in', ins, outs],)):
                rec(j + 1, first, ins + [j], outs, nrows)
        if first is None:
            if N - j - 1 >= 2:
                rec(j + 1, None, ins, outs + [j], rows)
        else:
            d, k = diff(j, first)
            dd = dict(d)
            dd[s] = dd.get(s, 0.0) - 1.0
            nrows = rows + [(dd, -k, None)]
            if len(ins) >= 2 or N - j - 1 >= 2 - len(ins):
                stats['lp'] += 1
                if C.feasible(X.sub(L0, extra + nrows), ctx + ([j, 'out', ins, outs],)):
                    rec(j + 1, first, ins, outs + [j], nrows)

    rec(0, None, [], [], [])
    return res


def cells_below(D, zt, wt, stats, C, groups_filter=None, mode=None):
    """texact.cells_below with certified verdicts."""
    n = D.n
    if not (T.com_ok(zt) and T.com_ok(wt)):
        return []
    L0 = T.base_lp(D, zt, wt, list(range(n + 1)))
    if L0 is None:
        return []
    if mode is not None:
        L0.rows.append(tsign.threshold_row(D, zt, wt, L0, list(range(n + 1)), mode))
    stats['lp'] += 1
    if not C.feasible(L0, ('L0', zt, wt, None)):
        return []
    ids = X.identities(D, zt, wt, L0)
    if groups_filter is not None:
        ids = [x for x in ids if groups_filter(x[0])]
    base_extra = []
    fixed = []
    branch = []
    for name, labels, terms, forced in ids:
        if forced is not None:
            if len(forced) < 2:
                return []
            base_extra += X.forced_rows(L0, terms, forced)
            fixed.append((name, [labels[t] for t in forced]))
        else:
            branch.append((name, labels, terms))
    stats['lp'] += 1
    if not C.feasible(X.sub(L0, base_extra), ('forced', zt, wt, None)):
        return []
    out = []

    def rec(gi, extra, chosen):
        if gi == len(branch):
            out.append((fixed + chosen, extra))
            return
        name, labels, terms = branch[gi]
        for S, rows in exact_argmins(L0, extra, terms, stats, C, ('argmin', zt, wt, [list(name), chosen])):
            rec(gi + 1, extra + rows, chosen + [(name, [labels[t] for t in S])])

    rec(0, base_extra, [])
    return [(zt, wt, L0, c, ex) for c, ex in out]


def enumerate_cells(D, out, C, split=None, part=0, nparts=1, groups_filter=None, mode=None):
    """texact.enumerate_cells with certified verdicts."""
    n = D.n
    stats = {'lp': 0, 'pairs': 0, 'cells': 0}
    zt0 = T.Tree(n).options(n)[0]
    wt0 = T.Tree(n).options(n)[0]
    order = T.order_bodies(D)
    counter = [0]

    def rec(i, zt, wt, pts):
        if i == n:
            stats['pairs'] += 1
            for zt2, wt2, L0, c, ex in cells_below(D, zt, wt, stats, C, groups_filter, mode):
                xs, hz, hw, sl = X.interior(D, zt2, wt2, L0, ex)
                stats['cells'] += 1
                out.write(json.dumps({'ztree': X.tree_json(zt2), 'wtree': X.tree_json(wt2), 'argmin': c, 'x': xs,
                                      'hz': hz, 'hw': hw, 'slack': round(sl, 9),
                                      'sumx': round(sum(xs.values()), 6)}) + '\n')
            return
        p = order[i]
        npts = pts + [p]
        for zt2 in zt.options(p):
            for wt2 in wt.options(p):
                if split is not None and i + 1 == split:
                    c = counter[0]
                    counter[0] += 1
                    if c % nparts != part:
                        continue
                L = T.base_lp(D, zt2, wt2, npts)
                if L is None:
                    continue
                if mode is not None:
                    L.rows.append(tsign.threshold_row(D, zt2, wt2, L, npts, mode))
                stats['lp'] += 1
                if C.feasible(L, ('tree', zt2, wt2, i + 1)):
                    rec(i + 1, zt2, wt2, npts)

    rec(0, zt0, wt0, [n])
    return stats


def compare(a, b):
    """Line-by-line comparison of two files: (identical, number of lines of a, of b, first differing line)."""
    la, lb = open(a).read().splitlines(), open(b).read().splitlines()
    diff = next((i for i, (x, y) in enumerate(zip(la, lb)) if x != y), None)
    if diff is None and len(la) != len(lb):
        diff = min(len(la), len(lb))
    return diff is None, len(la), len(lb), diff


if __name__ == '__main__':
    n = int(sys.argv[1])
    cls = json.load(open(sys.argv[2]))['classes']
    ci = int(sys.argv[3])
    outp = sys.argv[4]
    split, part, nparts = None, 0, 1
    mode = sys.argv[sys.argv.index('--mode') + 1] if '--mode' in sys.argv else None
    if '--split' in sys.argv:
        split = int(sys.argv[sys.argv.index('--split') + 1])
        part = int(sys.argv[sys.argv.index('--part') + 1])
        nparts = int(sys.argv[sys.argv.index('--nparts') + 1])
    D = T.Diagram.from_json(n, cls[ci])
    one_thread()
    C = Certifier()
    t = time.time()
    with open(outp, 'w') as f:
        gf = None
        if '--base' in sys.argv:
            gf = lambda name: (name[0] in ('z', 'w') and len(name[2]) == 1) or name[0] in ('U', 'I')
        st = enumerate_cells(D, f, C, split, part, nparts, groups_filter=gf, mode=mode)
    res = {'class': ci, 'part': part, 'nparts': nparts, 'mode': mode, 'base': '--base' in sys.argv, 'stats': st,
           'cert': C.c, 'min_kept_slack': C.min_kept, 'max_pruned_opt': C.max_pruned, 'max_cert_time': round(C.tmax, 3),
           'time': round(time.time() - t, 1)}
    if '--ref' in sys.argv:
        same, na, nb, dl = compare(outp, sys.argv[sys.argv.index('--ref') + 1])
        res['ref'] = {'identical': same, 'lines': na, 'ref_lines': nb, 'first_diff': dl}
    print(json.dumps(res), flush=True)
    res['borderline'] = C.border
    res['failures'] = C.fails
    json.dump(res, open(outp + '.replay.json', 'w'))
