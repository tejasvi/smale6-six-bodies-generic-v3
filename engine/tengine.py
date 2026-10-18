#!/usr/bin/env python3
"""Types engine: the exponents at a singular place with a given zw-diagram, as a finite union of polyhedra.

Exponents as in the paper (rung 2, §3.1): e = (2/d)(nu + gamma) for z-type functions, (2/d)(nu - gamma) for w-type,
(2/d) nu for neutral ones. Unknowns per colour: the exponents of the positions (a_k = e(z_k), b_k = e(w_k)) and of the
separations (zeta_kl, omega_kl); x_kl = (zeta_kl + omega_kl)/2. Constraints, each a necessary condition at a singular
place of a curve with U a nonzero constant:
 (T)  for each colour an ultrametric on the bodies and the origin O (z_kl = z_k - z_l, z_k = z_k - 0): a rooted tree
      whose internal nodes carry heights increasing towards the leaves; zeta_kl = height of the meet of k and l;
      a body may sit at O identically (a_k = +inf; it then shares the leaf of O);
 (O1) every exponent >= -2; zeta + 3 omega <= 4 and 3 zeta + omega <= 4;
 (O2) z-stroke kl iff zeta + 3 omega = 4; w-stroke iff 3 zeta + omega = 4;
 (C)  k z-circled iff a_k = -2;
 (M)  centre of mass, sum m_k z_k = 0 with positive masses: the root of the z-tree has at least three children (the
      bodies of least exponent are not all in one cluster, whose leading coefficients would be equal); also for w;
 (B)  body equations z_k = sum_l m_l Z_lk: the minimum over {a_k} and {e(Z_kl) = -(zeta_kl + 3 omega_kl)/2} is
      attained at least twice; also for w;
 (U)  sum m_k m_l / r_kl = U, a nonzero constant: the minimum over {0} and {-x_kl} is attained at least twice;
 (I)  sum m_k m_l r_kl^2 = M U: the minimum over {0} and {2 x_kl} is attained at least twice;
 (I') sum m_k z_k w_k = U: the minimum over {0} and {a_k + b_k} is attained at least twice.
Strict inequalities carry a common slack s; a system is feasible iff max s > 0 (floating point LPs, HiGHS).
"""
import itertools, json, sys, time
import numpy as np
import highspy

TOL = 1e-9
INF = float('inf')


class Tree:
    """Rooted tree on the points 0..n (n = O). Internal nodes are numbered from n + 1."""
    __slots__ = ('n', 'parent', 'children', 'root', 'leaf', 'next_id')

    def __init__(self, n):
        self.n = n
        self.parent = {}
        self.children = {}
        self.root = None
        self.leaf = {}            # point -> leaf node (a body at O shares the leaf n)
        self.next_id = n + 1

    def copy(self):
        t = Tree.__new__(Tree)
        t.n = self.n
        t.parent = dict(self.parent)
        t.children = {k: list(v) for k, v in self.children.items()}
        t.root = self.root
        t.leaf = dict(self.leaf)
        t.next_id = self.next_id
        return t

    def internal(self):
        return list(self.children.keys())

    def ancestors(self, v):
        out = [v]
        while v in self.parent:
            v = self.parent[v]
            out.append(v)
        return out

    def meet(self, p, q):
        """The meet of the leaves of p and q, or None if they share a leaf (exponent +inf)."""
        u, v = self.leaf[p], self.leaf[q]
        if u == v:
            return None
        au = self.ancestors(u)
        sv = set(self.ancestors(v))
        for w in au:
            if w in sv:
                return w
        raise RuntimeError('no meet')

    def options(self, p):
        """All trees obtained by inserting point p (each topology once)."""
        out = []
        if self.root is None:
            t = self.copy()
            t.root = p
            t.leaf[p] = p
            return [t]
        # p at O (bodies only; O is inserted first)
        if p != self.n and self.n in self.leaf and not any(self.leaf[q] == self.n for q in self.leaf if q != self.n):
            t = self.copy()
            t.leaf[p] = self.n
            out.append(t)
        # attach to an internal node
        for v in self.internal():
            t = self.copy()
            t.children[v].append(p)
            t.parent[p] = v
            t.leaf[p] = p
            out.append(t)
        # subdivide an edge parent(c) -> c
        for c, u in self.parent.items():
            t = self.copy()
            w = t.next_id
            t.next_id += 1
            t.children[u] = [w if x == c else x for x in t.children[u]]
            t.parent[w] = u
            t.children[w] = [c, p]
            t.parent[c] = w
            t.parent[p] = w
            t.leaf[p] = p
            out.append(t)
        # a new root
        t = self.copy()
        w = t.next_id
        t.next_id += 1
        t.children[w] = [t.root, p]
        t.parent[t.root] = w
        t.parent[p] = w
        t.root = w
        t.leaf[p] = p
        out.append(t)
        return out


class LP:
    """Rows sum c_j v_j in [lo, hi] over the variables of the two trees and the slack s (last variable)."""

    def __init__(self, zt, wt):
        self.zv = {v: i for i, v in enumerate(zt.internal())}
        off = len(self.zv)
        self.wv = {v: off + i for i, v in enumerate(wt.internal())}
        self.ns = off + len(self.wv)          # index of s
        self.nv = self.ns + 1
        self.rows = []

    def add(self, coefs, lo, hi):
        self.rows.append((coefs, lo, hi))

    def solve(self, obj=None, sense_max=True, smin=None):
        """Maximize s (default) or obj; returns (status_ok, value, x)."""
        h = highspy.Highs()
        h.setOptionValue('output_flag', False)
        nv = self.nv
        lp = highspy.HighsLp()
        lp.num_col_ = nv
        lp.num_row_ = len(self.rows)
        cost = np.zeros(nv)
        if obj is None:
            cost[self.ns] = 1.0
        else:
            for j, c in obj.items():
                cost[j] = c
        lp.col_cost_ = cost
        lo = np.full(nv, -highspy.kHighsInf)
        hi = np.full(nv, highspy.kHighsInf)
        lo[self.ns] = 0.0 if smin is None else smin
        hi[self.ns] = 1.0
        lp.col_lower_ = lo
        lp.col_upper_ = hi
        lp.sense_ = highspy.ObjSense.kMaximize if sense_max else highspy.ObjSense.kMinimize
        starts, idx, vals, rlo, rhi = [0], [], [], [], []
        for coefs, a, b in self.rows:
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
        lp.a_matrix_.num_row_ = len(self.rows)
        h.passModel(lp)
        h.run()
        st = h.getModelStatus()
        if st != highspy.HighsModelStatus.kOptimal:
            return False, None, None
        sol = np.array(h.getSolution().col_value)
        return True, h.getInfo().objective_function_value, sol


class Diagram:
    def __init__(self, n, edges, zc, wc):
        self.n = n
        self.zs = {(a, b) for (a, b), v in edges.items() if v & 1}
        self.ws = {(a, b) for (a, b), v in edges.items() if v & 2}
        self.zc, self.wc = set(zc), set(wc)

    @staticmethod
    def from_json(n, c):
        edges = {}
        for k, v in c['edges'].items():
            a, b = int(k[0]), int(k[1])
            edges[(min(a, b), max(a, b))] = v
        return Diagram(n, edges, c['zcircles'], c['wcircles'])

    def zstroke(self, k, l):
        return (min(k, l), max(k, l)) in self.zs

    def wstroke(self, k, l):
        return (min(k, l), max(k, l)) in self.ws


def base_lp(D, zt, wt, pts):
    """The LP of the constraints (T), (O1), (O2), (C) on the inserted points pts (O = n among them)."""
    n = D.n
    L = LP(zt, wt)
    s = L.ns
    for T, V in ((zt, L.zv), (wt, L.wv)):
        if T.root is not None and T.root in V:
            L.add({V[T.root]: 1}, -2, None)
        for v in T.internal():
            for c in T.children[v]:
                if c in V:
                    L.add({V[c]: 1, V[v]: -1, s: -1}, 0, None)
    bodies = [p for p in pts if p != n]
    for k, l in itertools.combinations(sorted(bodies), 2):
        mz, mw = zt.meet(k, l), wt.meet(k, l)
        Z, W = L.zv[mz], L.wv[mw]
        if D.zstroke(k, l):
            L.add({Z: 1, W: 3}, 4, 4)
        else:
            L.add({Z: 1, W: 3, s: 1}, None, 4)
        if D.wstroke(k, l):
            L.add({Z: 3, W: 1}, 4, 4)
        else:
            L.add({Z: 3, W: 1, s: 1}, None, 4)
    if n in pts:
        for k in bodies:
            for T, V, circ in ((zt, L.zv, D.zc), (wt, L.wv, D.wc)):
                m = T.meet(k, n)
                if m is None:
                    if k in circ:
                        return None
                    continue
                if k in circ:
                    L.add({V[m]: 1}, -2, -2)
                else:
                    L.add({V[m]: 1, s: -1}, -2, None)
    return L


def feasible(L):
    ok, val, sol = L.solve()
    return ok and val > TOL, sol


def com_ok(T):
    """(M): the root has at least three children."""
    return len(T.children[T.root]) >= 3


def terms_body(D, zt, wt, L, k, colour):
    """The terms of the equation of body k in a colour, as (coef dict, const); None if the term is absent."""
    n = D.n
    T, V = (zt, L.zv) if colour == 'z' else (wt, L.wv)
    out = []
    m = T.meet(k, n)
    if m is not None:
        out.append(({V[m]: 1.0}, 0.0))
    for l in range(n):
        if l == k:
            continue
        Z, W = L.zv[zt.meet(k, l)], L.wv[wt.meet(k, l)]
        if colour == 'z':
            out.append(({Z: -0.5, W: -1.5}, 0.0))
        else:
            out.append(({Z: -1.5, W: -0.5}, 0.0))
    return out


def xform(D, zt, wt, L, k, l, scale=1.0):
    Z, W = L.zv[zt.meet(k, l)], L.wv[wt.meet(k, l)]
    return {Z: 0.5 * scale, W: 0.5 * scale}


def lin_sub(a, b):
    (ca, ka), (cb, kb) = a, b
    d = dict(ca)
    for j, c in cb.items():
        d[j] = d.get(j, 0.0) - c
    return d, ka - kb


def min_twice_branches(L, terms):
    """Disjoint branching for 'the minimum of the terms is attained at least twice': yields lists of rows."""
    N = len(terms)
    s = L.ns
    for i in range(N):
        rows_i = []
        for j in range(N):
            if j == i:
                continue
            d, k = lin_sub(terms[j], terms[i])         # t_j - t_i (+ const k)
            if j < i:
                dd = dict(d)
                dd[s] = dd.get(s, 0.0) - 1.0
                rows_i.append((dd, -k, None))           # t_j - t_i - s >= 0
            else:
                rows_i.append((d, -k, None))            # t_j - t_i >= 0
        for j in range(i + 1, N):
            d, k = lin_sub(terms[j], terms[i])
            yield i, j, rows_i, (d, -k, -k)


def completions(D, zt, wt, stats):
    """The leaves below complete trees: rows for (B), (U), (I), (I')."""
    n = D.n
    if not (com_ok(zt) and com_ok(wt)):
        return []
    L0 = base_lp(D, zt, wt, list(range(n + 1)))
    if L0 is None:
        return []
    groups = []
    for colour, strokes, circ in (('z', D.zs, D.zc), ('w', D.ws, D.wc)):
        for k in range(n):
            has = any(k in e for e in strokes)
            if has:
                continue                                  # Rule 1a and (O2): the minimum -2 is attained twice
            groups.append(terms_body(D, zt, wt, L0, k, colour))
    pairs = list(itertools.combinations(range(n), 2))
    zw = [e for e in pairs if e in D.zs and e in D.ws]
    if len(zw) < 2:
        groups.append([({}, 0.0)] + [({j: -c for j, c in xform(D, zt, wt, L0, k, l).items()}, 0.0) for k, l in pairs])
    groups.append([({}, 0.0)] + [(xform(D, zt, wt, L0, k, l, 2.0), 0.0) for k, l in pairs])
    ip = [({}, 0.0)]
    for k in range(n):
        mz, mw = zt.meet(k, n), wt.meet(k, n)
        if mz is None or mw is None:
            continue
        ip.append(({L0.zv[mz]: 1.0, L0.wv[mw]: 1.0}, 0.0))
    groups.append(ip)
    leaves = []

    def rec(gi, extra):
        if gi == len(groups):
            leaves.append(list(extra))
            return
        seen_first = {}
        for i, j, rows_i, eqrow in min_twice_branches(L0, groups[gi]):
            if i not in seen_first:
                L = LP.__new__(LP)
                L.__dict__.update(L0.__dict__)
                L.rows = L0.rows + extra + rows_i
                stats['lp'] += 1
                seen_first[i] = feasible(L)[0]
            if not seen_first[i]:
                continue
            L = LP.__new__(LP)
            L.__dict__.update(L0.__dict__)
            L.rows = L0.rows + extra + rows_i + [eqrow]
            stats['lp'] += 1
            if feasible(L)[0]:
                rec(gi + 1, extra + rows_i + [eqrow])

    rec(0, [])
    return [(L0, ex) for ex in leaves]


def order_bodies(D):
    n = D.n
    deg = [sum(1 for e in D.zs | D.ws if k in e) for k in range(n)]
    order = [max(range(n), key=lambda k: (deg[k], -k))]
    while len(order) < n:
        rest = [k for k in range(n) if k not in order]
        order.append(max(rest, key=lambda k: (sum(1 for e in D.zs | D.ws if k in e and (e[0] in order or e[1] in order)),
                                              deg[k], -k)))
    return order


def run(D, verbose=False):
    n = D.n
    stats = {'lp': 0, 'nodes': 0, 'complete': 0}
    zt0, wt0 = Tree(n), Tree(n)
    zt0 = zt0.options(n)[0]
    wt0 = wt0.options(n)[0]
    order = order_bodies(D)
    leaves = []

    def rec(i, zt, wt, pts):
        if i == n:
            stats['complete'] += 1
            leaves.extend((zt, wt, L0, ex) for L0, ex in completions(D, zt, wt, stats))
            return
        p = order[i]
        npts = pts + [p]
        for zt2 in zt.options(p):
            for wt2 in wt.options(p):
                stats['nodes'] += 1
                L = base_lp(D, zt2, wt2, npts)
                if L is None:
                    continue
                stats['lp'] += 1
                if feasible(L)[0]:
                    rec(i + 1, zt2, wt2, npts)

    rec(0, zt0, wt0, [n])
    return leaves, stats


def leaf_summary(D, zt, wt, L0, ex):
    """An interior point (x vector), and the range of sum x over the closure of the leaf."""
    n = D.n
    L = LP.__new__(LP)
    L.__dict__.update(L0.__dict__)
    L.rows = L0.rows + ex
    ok, val, sol = L.solve()
    pairs = list(itertools.combinations(range(n), 2))
    xs = [0.5 * (sol[L.zv[zt.meet(k, l)]] + sol[L.wv[wt.meet(k, l)]]) for k, l in pairs]
    obj = {}
    for k, l in pairs:
        for j, c in xform(D, zt, wt, L, k, l).items():
            obj[j] = obj.get(j, 0.0) + c
    ok1, lo, _ = L.solve(obj=obj, sense_max=False, smin=0.0)
    ok2, hi, _ = L.solve(obj=obj, sense_max=True, smin=0.0)
    return xs, (lo if ok1 else -INF), (hi if ok2 else INF)


if __name__ == '__main__':
    n = int(sys.argv[1])
    cls = json.load(open(sys.argv[2]))['classes']
    which = [int(a) for a in sys.argv[3].split(',')] if len(sys.argv) > 3 else range(len(cls))
    for ci in which:
        D = Diagram.from_json(n, cls[ci])
        t = time.time()
        leaves, st = run(D)
        sums = [leaf_summary(D, *lf) for lf in leaves]
        lo = min((s[1] for s in sums), default=None)
        hi = max((s[2] for s in sums), default=None)
        print(f'class {ci}: {len(leaves)} leaves, nodes {st["nodes"]}, complete {st["complete"]}, LPs {st["lp"]}, '
              f'{time.time() - t:.1f} s; sum x in [{lo}, {hi}]', flush=True)
