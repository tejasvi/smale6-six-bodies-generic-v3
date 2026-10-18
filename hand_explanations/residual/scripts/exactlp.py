#!/usr/bin/env python3
"""Exact (rational) cell polyhedra and Farkas certificates for strict/non-strict inequalities between exponents.

The cell polyhedron of a stored cell is rebuilt exactly as tengine.base_lp + texact.forced_rows (the engine's
definition of a cell): variables are the heights of the internal nodes of the z- and w-trees; rows
  - root >= -2 (weak), child - parent > 0 (strict),
  - for every pair: z-stroke  zeta + 3 omega = 4  else  zeta + 3 omega < 4;  w-stroke 3 zeta + omega = 4 else < 4,
  - circles: a_k = -2 (eq); no circle: a_k > -2 (strict)  (bodies at O: no row),
  - for every argmin entry of the cell: the listed terms have equal exponents, every other term is strictly larger.
A claim d(h) > 0 (resp. >= 0) on the relatively open cell is certified by d = sum_i y_i g_i + c with y_i >= 0 on
inequality rows (free on equality rows), c >= 0, and c > 0 or y_i > 0 on some strict row (for '>').
Certificates are found by an exact simplex over Fractions (Bland's rule); nothing is floating point.
"""
import itertools
from fractions import Fraction as Fr

N, O = 6, 6


class Tree:
    def __init__(self, tj):
        self.children = {int(a): list(b) for a, b in tj['children'].items()}
        self.parent = {c: a for a, ch in self.children.items() for c in ch}
        self.root = tj['root']
        self.leaf = {int(a): b for a, b in tj['leaf'].items()}

    def anc(self, v):
        out = [v]
        while v in self.parent:
            v = self.parent[v]
            out.append(v)
        return out

    def meet(self, p, q):
        u, v = self.leaf[p], self.leaf[q]
        if u == v:
            return None
        sv = set(self.anc(v))
        for w in self.anc(u):
            if w in sv:
                return w

    def child_of(self, v, p):
        """the child of v containing point p (None if p is not strictly below v)."""
        u = self.leaf[p]
        if u == v:
            return None
        while u in self.parent and self.parent[u] != v:
            u = self.parent[u]
        return u if self.parent.get(u) == v else None

    def below(self, v):
        return sorted(p for p, lf in self.leaf.items() if v in self.anc(lf))

    def at_O(self, k):
        return self.leaf[k] == self.leaf[O]


class Diag:
    def __init__(self, c):
        self.zs, self.ws = set(), set()
        for k, v in c['edges'].items():
            a, b = int(k[0]), int(k[1])
            e = (min(a, b), max(a, b))
            if v & 1:
                self.zs.add(e)
            if v & 2:
                self.ws.add(e)
        self.zc, self.wc = set(c['zcircles']), set(c['wcircles'])

    def stroke(self, col, k, l):
        return (min(k, l), max(k, l)) in (self.zs if col == 'z' else self.ws)

    def circ(self, col):
        return self.zc if col == 'z' else self.wc


def lin(*pairs):
    """sum of c * form; a form is a dict var -> Fraction with key 1 for the constant."""
    d = {}
    for f, c in pairs:
        for j, x in f.items():
            d[j] = d.get(j, 0) + Fr(c) * x
    return {j: x for j, x in d.items() if x != 0}


ONE = 1  # key of the constant term


class Poly:
    """Exact cell polyhedron with labelled rows (form, kind) meaning form > 0 / >= 0 / = 0."""

    def __init__(self, rec, D, with_argmin=True):
        self.rec = rec
        self.D = D
        self.zt, self.wt = Tree(rec['ztree']), Tree(rec['wtree'])
        self.var = {}
        for col, T in (('z', self.zt), ('w', self.wt)):
            for v in sorted(T.children):
                self.var[(col, v)] = len(self.var) + 2      # 0, 1 reserved (1 = constant)
        self.rows = []
        for col, T in (('z', self.zt), ('w', self.wt)):
            self.add(lin((self.h(col, T.root), 1), ({ONE: Fr(2)}, 1)), 'weak', ('root>=-2', col))
            for v, ch in T.children.items():
                for c in ch:
                    if c in T.children:
                        self.add(lin((self.h(col, c), 1), (self.h(col, v), -1)), 'strict', ('edge', col, v, c))
        for k, l in itertools.combinations(range(N), 2):
            Z, W = self.zeta(k, l), self.omega(k, l)
            f1 = lin((Z, 1), (W, 3), ({ONE: Fr(-4)}, 1))     # zeta + 3 omega - 4
            f2 = lin((Z, 3), (W, 1), ({ONE: Fr(-4)}, 1))
            if D.stroke('z', k, l):
                self.add(f1, 'eq', ('zstroke', k, l))
            else:
                self.add(lin((f1, -1)), 'strict', ('O1:z+3w<4', k, l))
            if D.stroke('w', k, l):
                self.add(f2, 'eq', ('wstroke', k, l))
            else:
                self.add(lin((f2, -1)), 'strict', ('O1:3z+w<4', k, l))
        for k in range(N):
            for col in 'zw':
                p = self.pos(col, k)
                if p is None:
                    continue
                if k in D.circ(col):
                    self.add(lin((p, 1), ({ONE: Fr(2)}, 1)), 'eq', ('circle', col, k))
                else:
                    self.add(lin((p, 1), ({ONE: Fr(2)}, 1)), 'strict', ('nocircle', col, k))
        if with_argmin:
            for nm, labs in rec['argmin']:
                key = (nm[0], nm[1], tuple(nm[2])) if nm[0] in ('z', 'w') else tuple(nm)
                terms = self.identity_terms(key)
                labset = [tuple(x) for x in labs]
                idx = [i for i, (lab, f) in enumerate(terms) if lab in labset]
                assert len(idx) == len(labset), (key, labset)
                f0 = terms[idx[0]][1]
                for t, (lab, f) in enumerate(terms):
                    if t == idx[0]:
                        continue
                    d = lin((f, 1), (f0, -1))
                    self.add(d, 'eq' if t in idx else 'strict', ('argmin', key, lab))

    # ---- forms
    def add(self, form, kind, label):
        self.rows.append((form, kind, label))

    def h(self, col, v):
        return {self.var[(col, v)]: Fr(1)}

    def tree(self, col):
        return self.zt if col == 'z' else self.wt

    def sep(self, col, k, l):
        m = self.tree(col).meet(k, l)
        return None if m is None else self.h(col, m)

    def zeta(self, k, l):
        return self.sep('z', k, l)

    def omega(self, k, l):
        return self.sep('w', k, l)

    def pos(self, col, k):
        m = self.tree(col).meet(k, O)
        return None if m is None else self.h(col, m)

    def delta(self, k, l):          # exponent of delta_kl = -x_kl
        return lin((self.zeta(k, l), Fr(-1, 2)), (self.omega(k, l), Fr(-1, 2)))

    def force(self, col, k, l):     # exponent of delta^3 z_kl (col z) or delta^3 w_kl (col w)
        if col == 'z':
            return lin((self.zeta(k, l), Fr(-1, 2)), (self.omega(k, l), Fr(-3, 2)))
        return lin((self.zeta(k, l), Fr(-3, 2)), (self.omega(k, l), Fr(-1, 2)))

    def identity_terms(self, key):
        """terms (label, form) of a base identity, labels as in the engine's argmin data."""
        if key[0] in ('z', 'w'):
            col, _, J = key
            terms = []
            for i in J:
                p = self.pos(col, i)
                if p is not None:
                    terms.append((('pos', i), p))
            for i in J:
                for j in range(N):
                    if j not in J:
                        terms.append((('cross', i, j), self.force(col, i, j)))
            return terms
        if key == ('U',):
            return [(('E',), {})] + [(('delta', k, l), self.delta(k, l)) for k, l in itertools.combinations(range(N), 2)]
        if key == ('I',):
            return [(('E',), {})] + [(('zw', k, l), lin((self.zeta(k, l), 1), (self.omega(k, l), 1)))
                                     for k, l in itertools.combinations(range(N), 2)]
        if key == ('Ip',):
            out = [(('E',), {})]
            for k in range(N):
                a, b = self.pos('z', k), self.pos('w', k)
                if a is not None and b is not None:
                    out.append((('zkwk', k), lin((a, 1), (b, 1))))
            return out
        raise KeyError(key)

    def torque_terms(self, J):
        """terms of T_J = sum_{k in J, l not in J} m_k m_l delta^3 (z_k w_l - w_k z_l): labels ('zw', p, q) for
        delta_pq^3 z_p w_q over ordered cross pairs (p, q)."""
        Jc = [j for j in range(N) if j not in J]
        out = []
        for k in J:
            for l in Jc:
                for p, q in ((k, l), (l, k)):
                    a, b = self.pos('z', p), self.pos('w', q)
                    if a is None or b is None:
                        continue
                    out.append((('zw', p, q), lin((self.delta(p, q), 3), (a, 1), (b, 1))))
        return out

    def subset_terms(self, col, J):
        return self.identity_terms((col, 'S', tuple(J)))

    # ---- certificates
    def certify(self, d, strict=True):
        """certificate that d > 0 (strict) or d >= 0 on the open cell: list of (multiplier, row label), constant c;
        None if there is none."""
        return farkas(self.rows, d, strict)

    def less(self, f, g, strict=True):
        """certificate that f < g (or f <= g) on the cell."""
        return self.certify(lin((g, 1), (f, -1)), strict)

    def equal(self, f, g):
        return self.less(f, g, False) is not None and self.less(g, f, False) is not None

    def argmin_is(self, terms, S):
        """True if the terms with labels in S have equal exponents on the whole cell and all others are strictly
        larger; returns (ok, certificates)."""
        lab = [t[0] for t in terms]
        Sidx = [i for i, l in enumerate(lab) if l in S]
        if len(Sidx) != len(S):
            return False, ('labels missing', S, lab)
        f0 = terms[Sidx[0]][1]
        certs = []
        for i, (l, f) in enumerate(terms):
            if i == Sidx[0]:
                continue
            if i in Sidx:
                if not self.equal(f, f0):
                    return False, ('not equal', l)
            else:
                c = self.less(f0, f, True)
                if c is None:
                    return False, ('not larger', l)
                certs.append((l, c))
        return True, certs


# ------------------------------------------------------------------ exact Farkas search (simplex over Fractions)

def farkas(rows, d, strict):
    """Find y (y_i >= 0 on 'strict'/'weak' rows, free on 'eq'), c >= 0 with d = sum y_i g_i + c, maximizing
    t = c + sum_{strict} y_i capped at 1. Return (certificate list, c) if t > 0 (strict) / feasible (non-strict)."""
    keys = sorted({j for f, _, _ in rows for j in f} | set(d.keys()) | {ONE})
    # columns: for each row: y+ (and y- if eq); then c; then slack u for t + u = 1
    cols = []          # (row index, sign)
    for i, (f, kind, lab) in enumerate(rows):
        cols.append((i, 1))
        if kind == 'eq':
            cols.append((i, -1))
    nc = len(cols)
    ic, iu = nc, nc + 1
    nvar = nc + 2
    A, b = [], []
    for j in keys:
        row = [Fr(0)] * nvar
        for ci, (i, sg) in enumerate(cols):
            x = rows[i][0].get(j, 0)
            if x:
                row[ci] = sg * x
        if j == ONE:
            row[ic] = Fr(1)
        A.append(row)
        b.append(Fr(d.get(j, 0)))
    obj = [Fr(0)] * nvar
    trow = [Fr(0)] * nvar
    for ci, (i, sg) in enumerate(cols):
        if rows[i][1] == 'strict':
            obj[ci] = Fr(1)
            trow[ci] = Fr(1)
    obj[ic] = Fr(1)
    trow[ic] = Fr(1)
    trow[iu] = Fr(1)
    A.append(trow)
    b.append(Fr(1))
    x = simplex_max(A, b, obj)
    if x is None:
        return None
    val = sum(o * v for o, v in zip(obj, x))
    if strict and val <= 0:
        return None
    cert = []
    for ci, (i, sg) in enumerate(cols):
        if x[ci]:
            cert.append((sg * x[ci], rows[i][2]))
    # merge eq +/- parts
    m = {}
    for y, l in cert:
        m[l] = m.get(l, 0) + y
    cert = [(y, l) for l, y in m.items() if y != 0]
    # exact re-verification
    tot = {}
    lab2row = {r[2]: r for r in rows}
    for y, l in cert:
        f, kind, _ = lab2row[l]
        assert kind == 'eq' or y > 0
        for j, v in f.items():
            tot[j] = tot.get(j, 0) + y * v
    c = x[ic]
    tot[ONE] = tot.get(ONE, 0) + c
    for j in set(tot) | set(d):
        assert tot.get(j, 0) == d.get(j, 0), ('certificate mismatch', j)
    assert c >= 0
    if strict:
        assert c > 0 or any(lab2row[l][1] == 'strict' and y > 0 for y, l in cert)
    return cert, c


def simplex_max(A, b, c):
    """max c.x s.t. A x = b, x >= 0 (exact). Returns an optimal x or None if infeasible. Bland's rule."""
    m, n = len(A), len(A[0])
    A = [row[:] for row in A]
    b = b[:]
    for i in range(m):
        if b[i] < 0:
            A[i] = [-v for v in A[i]]
            b[i] = -b[i]
    # phase I: artificials n..n+m-1
    T = [A[i] + [Fr(1) if k == i else Fr(0) for k in range(m)] + [b[i]] for i in range(m)]
    basis = [n + i for i in range(m)]
    N2 = n + m

    def pivot(r, s):
        pv = T[r][s]
        T[r] = [v / pv for v in T[r]]
        for i in range(m):
            if i != r and T[i][s] != 0:
                f = T[i][s]
                Ti, Tr = T[i], T[r]
                T[i] = [vi - f * vr for vi, vr in zip(Ti, Tr)]
        basis[r] = s

    def run(cost, allowed):
        # maximize cost.x over current tableau; allowed: columns that may enter
        while True:
            # reduced costs: cost_j - sum_i cost_basis_i T[i][j]
            cb = [cost[basis[i]] for i in range(m)]
            enter = None
            for j in range(N2):
                if j not in allowed or j in basis:
                    continue
                rc = cost[j] - sum(cb[i] * T[i][j] for i in range(m) if T[i][j] != 0)
                if rc > 0:
                    enter = j
                    break
            if enter is None:
                return True
            # ratio test (Bland: smallest basis index among ties)
            best, r = None, None
            for i in range(m):
                if T[i][enter] > 0:
                    q = T[i][-1] / T[i][enter]
                    if best is None or q < best or (q == best and basis[i] < basis[r]):
                        best, r = q, i
            if r is None:
                return False        # unbounded
            pivot(r, enter)

    cost1 = [Fr(0)] * n + [Fr(-1)] * m
    run(cost1, set(range(N2)))
    if any(T[i][-1] != 0 for i in range(m) if basis[i] >= n):
        return None                  # infeasible
    # drive artificials out of the basis where possible
    for i in range(m):
        if basis[i] >= n:
            for j in range(n):
                if T[i][j] != 0:
                    pivot(i, j)
                    break
    cost2 = list(c) + [Fr(0)] * m
    ok = run(cost2, set(range(n)))
    x = [Fr(0)] * n
    for i in range(m):
        if basis[i] < n:
            x[basis[i]] = T[i][-1]
    if not ok:
        # unbounded objective: the current basic solution is feasible; t is capped, so this cannot happen
        raise RuntimeError('unbounded')
    return x


def fmt_cert(cert):
    y, c = cert
    parts = [f'{v}*{l}' for v, l in sorted(y, key=lambda t: str(t[1]))]
    return ' + '.join(parts) + (f' + {c}' if c else '')
