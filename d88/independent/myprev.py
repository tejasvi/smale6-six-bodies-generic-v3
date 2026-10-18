#!/usr/bin/env python3
"""Referee's independent tropical-prevariety computation (no gfan, no code from d88/scripts).

Input: a gfan-format polynomial file (as written by the author: 'Q[a,b,...]' then '{p1, p2, ...}'); only the
supports matter here.  Output: a partition of Prev(G) \\ {0} (min convention) into relatively open cells on which the
argmin face of every polynomial is constant, each with an exact relative-interior point (integer vector).

Method: depth-first refinement over the polynomials.  A cell is {w : E w = 0, S w > 0} (integer rows).  For the next
polynomial g, the cell is split along hyperplanes <a - b, w> = 0 (a, b in supp g) until the argmin face of g is
constant on each piece; pieces whose face has a single exponent are discarded (not in trop g).
Every emptiness/nonemptiness decision is certified exactly: nonempty by an exact rational point satisfying all
constraints, empty by an exact Motzkin certificate (y >= 0, y != 0, z >= 0 with A^T y + B^T z = 0 on the span).
Floating LPs (scipy HiGHS) only propose points / certificates; an exact rational simplex is the fallback.
Usage (module): cells(polys_supports, n, order) -> list of dicts.
"""
import itertools
import math
import re
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

STATS = {'lp': 0, 'cert_point': 0, 'cert_motzkin': 0, 'exact_fallback': 0}


# ---------------------------------------------------------------- parsing
def parse_gfan(path):
    txt = open(path).read()
    head, body = txt.split('\n', 1)
    names = head[head.index('[') + 1:head.index(']')].split(',')
    body = body.strip()
    assert body[0] == '{' and body[-1] == '}'
    polys = [p.strip() for p in body[1:-1].split(',')]
    out = []
    for p in polys:
        p = p.replace(' ', '').replace('\n', '')
        toks = re.findall(r'[+-]?[^+-]+', p)
        terms = {}
        for t in toks:
            sg = -1 if t[0] == '-' else 1
            t = t.lstrip('+-')
            c = 1
            e = [0] * len(names)
            for i, f in enumerate(t.split('*')):
                if re.fullmatch(r'\d+', f):
                    c *= int(f)
                else:
                    m = re.fullmatch(r'([a-z])(\^(\d+))?', f)
                    assert m, (f, p[:60])
                    e[names.index(m.group(1))] += int(m.group(3) or 1)
            k = tuple(e)
            terms[k] = terms.get(k, 0) + sg * c
        terms = {k: v for k, v in terms.items() if v != 0}
        out.append(terms)
    return names, out


# ---------------------------------------------------------------- exact linear algebra
def nullspace(E, n):
    """basis (list of integer vectors) of {w in Q^n : E w = 0}."""
    rows = [[Fr(x) for x in r] for r in E]
    piv_cols = []
    R = []
    for r in rows:
        r = r[:]
        for (pc, pr) in zip(piv_cols, R):
            if r[pc] != 0:
                f = r[pc]
                r = [a - f * b for a, b in zip(r, pr)]
        nz = [i for i, x in enumerate(r) if x != 0]
        if not nz:
            continue
        pc = nz[0]
        f = r[pc]
        r = [x / f for x in r]
        # eliminate pc from previous rows
        R = [[a - pr_[pc] * b for a, b in zip(pr_, r)] for pr_ in R]
        R.append(r)
        piv_cols.append(pc)
    free = [i for i in range(n) if i not in piv_cols]
    basis = []
    for fcol in free:
        v = [Fr(0)] * n
        v[fcol] = Fr(1)
        for pc, pr in zip(piv_cols, R):
            v[pc] = -pr[fcol]
        den = 1
        for x in v:
            den = den * x.denominator // math.gcd(den, x.denominator)
        iv = [int(x * den) for x in v]
        g = 0
        for x in iv:
            g = math.gcd(g, abs(x))
        basis.append([x // g for x in iv])
    return basis


def proj(vec, basis):
    return [sum(a * b for a, b in zip(vec, bv)) for bv in basis]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


# ---------------------------------------------------------------- exact simplex (fallback)
def exact_motzkin_or_point(A, B, d):
    """Decide feasibility of {t in Q^d : A t > 0, B t >= 0} exactly.
    Returns ('point', t) or ('cert', (y, z)).  Phase-I simplex on: find y >= 0, z >= 0 with
    A^T y + B^T z = 0, sum y = 1 (d+1 rows).  If infeasible, the final duals give t."""
    STATS['exact_fallback'] += 1
    m1, m2 = len(A), len(B)
    ncol = m1 + m2
    rows = d + 1
    # columns: y_j -> (A_j, 1), z_j -> (B_j, 0)
    cols = [list(map(Fr, A[j])) + [Fr(1)] for j in range(m1)] + [list(map(Fr, B[j])) + [Fr(0)] for j in range(m2)]
    b = [Fr(0)] * d + [Fr(1)]
    # make b >= 0 (it is) ; artificials a_i for each row
    # tableau rows: [coeffs of ncol vars | artificials | rhs]
    T = []
    for i in range(rows):
        T.append([cols[j][i] for j in range(ncol)] + [Fr(1) if k == i else Fr(0) for k in range(rows)] + [b[i]])
    basis = [ncol + i for i in range(rows)]
    nv = ncol + rows
    # phase I objective: minimize sum of artificials -> reduced costs
    def objrow():
        z = [Fr(0)] * (nv + 1)
        for i in range(rows):
            if basis[i] >= ncol:
                for j in range(nv + 1):
                    z[j] += T[i][j]
        return z   # maximize "sum of artificial-row entries" over nonbasic vars to reduce
    it = 0
    while True:
        it += 1
        assert it < 10000
        z = objrow()
        # entering: smallest index j (Bland) among non-artificial nonbasic with z[j] > 0
        enter = None
        for j in range(nv):
            if j in basis:
                continue
            if j >= ncol:
                continue
            if z[j] > 0:
                enter = j
                break
        if enter is None:
            break
        # ratio test
        best = None
        for i in range(rows):
            if T[i][enter] > 0:
                ratio = T[i][-1] / T[i][enter]
                if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]):
                    best = (ratio, i)
        if best is None:
            break   # unbounded direction (cannot happen in phase I with bounded objective)
        _, r = best
        pv = T[r][enter]
        T[r] = [x / pv for x in T[r]]
        for i in range(rows):
            if i != r and T[i][enter] != 0:
                f = T[i][enter]
                T[i] = [a - f * c for a, c in zip(T[i], T[r])]
        basis[r] = enter
    phase1 = sum(T[i][-1] for i in range(rows) if basis[i] >= ncol)
    if phase1 == 0:
        x = [Fr(0)] * ncol
        for i in range(rows):
            if basis[i] < ncol:
                x[basis[i]] = T[i][-1]
        return ('cert', (x[:m1], x[m1:]))
    # infeasible: duals pi with pi^T col_j <= 0 for all j? recover by solving pi^T B_basis = c_B (c = 1 on artificials)
    # simpler: the reduced costs z_j = sum_{art rows} T[i][j] equal (pi^T col_j) for the phase-I duals
    # Here we compute pi directly from artificial columns: z[ncol + k] - 1 = pi_k  (reduced cost of artificial k)
    z = objrow()
    pi = [z[ncol + k] - (0 if (ncol + k) in basis else 0) for k in range(rows)]
    # For basic artificials the reduced cost is 0 and pi_k = 1 ... handle generally by solving:
    # pi^T a_j = c_j for basic columns j, with c_j = 1 for artificials, 0 otherwise.
    Bm = [[(cols[j][i] if j < ncol else (Fr(1) if j - ncol == i else Fr(0))) for i in range(rows)] for j in basis]
    cB = [Fr(1) if j >= ncol else Fr(0) for j in basis]
    pi = solve_square_T(Bm, cB, rows)
    u, u0 = pi[:d], pi[d]
    # dual feasibility: pi^T col_j <= 0 for all original columns; objective pi^T b = u0 = phase1 > 0
    t = [-x for x in u]
    return ('point', t)


def solve_square_T(Brows, c, n):
    """solve for pi in Q^n: for each k, sum_i Brows[k][i] * pi_i = c[k]."""
    M = [list(Brows[k]) + [c[k]] for k in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]


# ---------------------------------------------------------------- certified feasibility
def verify_point(A, B, t):
    return all(dot(a, t) > 0 for a in A) and all(dot(bb, t) >= 0 for bb in B)


def verify_cert(A, B, y, z, d):
    if any(v < 0 for v in y) or any(v < 0 for v in z) or not any(v > 0 for v in y):
        return False
    for i in range(d):
        s = sum(y[j] * A[j][i] for j in range(len(A))) + sum(z[j] * B[j][i] for j in range(len(B)))
        if s != 0:
            return False
    return True


def rationalize(v, den):
    return [Fr(x).limit_denominator(den) for x in v]


def feasible(A, B, d):
    """Exact decision of {t : A t > 0, B t >= 0} (rows already projected to the d-dim span).
    Returns (True, t) or (False, None)."""
    if d == 0:
        return (len(A) == 0, [] if len(A) == 0 else None)
    if not A:
        return (True, [Fr(0)] * d)
    STATS['lp'] += 1
    An = np.array(A, dtype=float)
    Bn = np.array(B, dtype=float) if B else np.zeros((0, d))
    sc = max(1.0, np.abs(An).max())
    # variables t (d), tau ; maximize tau  s.t. -A t + tau <= 0 ; -B t <= 0 ; -1 <= t <= 1 ; tau <= 1
    c = np.zeros(d + 1)
    c[-1] = -1.0
    Aub = np.vstack([np.hstack([-An / sc, np.ones((len(A), 1))]), np.hstack([-Bn / sc, np.zeros((len(B), 1))])])
    bub = np.zeros(len(A) + len(B))
    res = linprog(c, A_ub=Aub, b_ub=bub, bounds=[(-1, 1)] * d + [(None, 1)], method='highs')
    if res.status == 0 and -res.fun > 1e-9:
        t0 = res.x[:d]
        for den in (10 ** 6, 10 ** 9, 10 ** 12):
            t = rationalize(t0, den)
            if verify_point(A, B, t):
                STATS['cert_point'] += 1
                return (True, t)
    else:
        # Motzkin certificate: y >= 0 (sum 1), z >= 0, A^T y + B^T z = 0
        m1, m2 = len(A), len(B)
        Aeq = np.vstack([np.hstack([An.T, Bn.T]) if m2 else An.T, np.hstack([np.ones(m1), np.zeros(m2)])])
        beq = np.zeros(d + 1)
        beq[-1] = 1.0
        r2 = linprog(np.zeros(m1 + m2), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * (m1 + m2), method='highs')
        if r2.status == 0:
            x = r2.x
            supp = [j for j in range(m1 + m2) if x[j] > 1e-12]
            sol = exact_on_support(A, B, supp, d)
            if sol is not None:
                y, z = sol
                if verify_cert(A, B, y, z, d):
                    STATS['cert_motzkin'] += 1
                    return (False, None)
    kind, val = exact_motzkin_or_point(A, B, d)
    if kind == 'point':
        assert verify_point(A, B, val), 'exact simplex point failed verification'
        return (True, val)
    y, z = val
    assert verify_cert(A, B, y, z, d), 'exact simplex certificate failed verification'
    return (False, None)


def exact_on_support(A, B, supp, d):
    m1 = len(A)
    cols = []
    for j in supp:
        if j < m1:
            cols.append([Fr(x) for x in A[j]] + [Fr(1)])
        else:
            cols.append([Fr(x) for x in B[j - m1]] + [Fr(0)])
    k = len(cols)
    rows = d + 1
    M = [[cols[j][i] for j in range(k)] + [Fr(1) if i == d else Fr(0)] for i in range(rows)]
    # gaussian elimination
    piv = []
    r = 0
    for col in range(k):
        pr = next((i for i in range(r, rows) if M[i][col] != 0), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        pv = M[r][col]
        M[r] = [x / pv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(col)
        r += 1
    for i in range(r, rows):
        if M[i][k] != 0:
            return None
    x = [Fr(0)] * k
    for i, col in enumerate(piv):
        x[col] = M[i][k]
    y = [Fr(0)] * m1
    z = [Fr(0)] * len(B)
    for idx, j in enumerate(supp):
        if j < m1:
            y[j] = x[idx]
        else:
            z[j - m1] = x[idx]
    return y, z


# ---------------------------------------------------------------- refinement
class Cell:
    __slots__ = ('E', 'S', 'basis', 'w', 'faces')

    def __init__(self, E, S, basis, w, faces):
        self.E, self.S, self.basis, self.w, self.faces = E, S, basis, w, faces


def make_cell(E, S, n, faces):
    basis = nullspace(E, n) if E else [[1 if i == j else 0 for i in range(n)] for j in range(n)]
    d = len(basis)
    A = [proj(s, basis) for s in S]
    ok, t = feasible(A, [], d)
    if not ok:
        return None
    w = [sum(Fr(t[j]) * basis[j][i] for j in range(d)) for i in range(n)] if d else [Fr(0)] * n
    den = 1
    for x in w:
        den = den * x.denominator // math.gcd(den, x.denominator)
    w = [int(x * den) for x in w]
    return Cell(E, S, basis, w, faces)


def refine(cell, supp, n):
    """split `cell` by the argmin face of the exponent list supp; return pieces in trop(g) with constant face."""
    out = []
    stack = [cell]
    while stack:
        c = stack.pop()
        d = len(c.basis)
        vals = [dot(a, c.w) for a in supp]
        mn = min(vals)
        F = [i for i, v in enumerate(vals) if v == mn]
        a0 = supp[F[0]]
        split = None
        for i in F[1:]:
            h = [x - y for x, y in zip(supp[i], a0)]
            if any(v != 0 for v in proj(h, c.basis)):
                split = h
                break
        if split is None:
            Aproj = [proj(s, c.basis) for s in c.S]
            for i in range(len(supp)):
                if i in F:
                    continue
                h = [x - y for x, y in zip(supp[i], a0)]
                hp = proj(h, c.basis)
                if not any(v != 0 for v in hp):
                    # h constant on the span and positive at w: positive on the whole cell
                    continue
                # is there a point of the cell with h <= 0 ?
                ok, _ = feasible(Aproj, [[-v for v in hp]], d)
                if ok:
                    split = h
                    break
        if split is None:
            if len(F) >= 2:
                out.append((c, tuple(F)))
            continue
        h = split
        for (E2, S2) in ((c.E, c.S + [h]), (c.E, c.S + [[-x for x in h]]), (c.E + [h], c.S)):
            nc = make_cell(E2, S2, n, c.faces)
            if nc is not None:
                stack.append(nc)
    return out


def prevariety(supports, n, order, log=None):
    root = make_cell([], [], n, ())
    cells = [root]
    for step, gi in enumerate(order):
        supp = supports[gi]
        new = []
        for c in cells:
            for (piece, F) in refine(c, supp, n):
                piece.faces = c.faces + ((gi, F),)
                new.append(piece)
        cells = new
        if log:
            log('step %d poly %d terms %d -> %d cells; %s' % (step, gi, len(supp), len(cells), STATS))
    return cells
