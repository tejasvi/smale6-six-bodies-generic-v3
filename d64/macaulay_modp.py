#!/usr/bin/env python3
"""Macaulay-matrix rank certificates mod p (checker 1; python-flint nmod_mat).

A homogeneous ideal J = (f_1..f_r) in K[x_0..x_n] has no common zero in P^n(Kbar) iff J contains every monomial of
some degree D.  That holds iff the Macaulay matrix M_D (rows: coefficient vectors of x^a f_i, |a| = D - deg f_i;
columns: the monomials of degree D) has rank equal to the number of monomials of degree D.

Reduction: the f_i have coefficients in Z[w] (w a primitive cube root of unity) or in Z.  Let p = 1 mod 3 and r a root
of t^2 + t + 1 mod p; w -> r is a ring map Z[w] -> F_p.  A nonzero maximal minor of M_D mod p lifts to a nonzero minor
over Z[w].  Hence rank_{F_p} M_D(mod p) = #monomials implies rank_{Q(w)} M_D = #monomials, i.e. the forms have no
common zero over C.

Polynomials are dicts {exponent tuple: (a, b)} meaning a + b*w with integers a, b.
"""
import itertools
import flint


def monomials(nvars, deg):
    """All exponent tuples of total degree deg in nvars variables (fixed order)."""
    if nvars == 1:
        return [(deg,)]
    out = []
    for i in range(deg, -1, -1):
        for rest in monomials(nvars - 1, deg - i):
            out.append((i,) + rest)
    return out


def cube_root_of_unity(p):
    assert p % 3 == 1
    for t in range(2, p):
        if (t * t + t + 1) % p == 0:
            return t
    raise ValueError


def to_modp(poly, p, r):
    out = {}
    for e, (a, b) in poly.items():
        v = (a + b * r) % p
        if v:
            out[e] = v
    return out


def degree(poly):
    degs = {sum(e) for e in poly}
    assert len(degs) == 1, 'not homogeneous'
    return degs.pop()


def macaulay_rank(polys_modp, nvars, D, p):
    cols = monomials(nvars, D)
    cidx = {m: i for i, m in enumerate(cols)}
    rows = []
    for f in polys_modp:
        d = degree(f)
        if d > D:
            continue
        for a in monomials(nvars, D - d):
            row = [0] * len(cols)
            for e, c in f.items():
                row[cidx[tuple(x + y for x, y in zip(a, e))]] = c
            rows.append(row)
    if not rows:
        return 0, len(cols), 0
    M = flint.nmod_mat(rows, p)
    return M.rank(), len(cols), len(rows)


def first_full_degree(polys_modp, nvars, p, Dmax):
    for D in range(max(degree(f) for f in polys_modp), Dmax + 1):
        rk, nc, nr = macaulay_rank(polys_modp, nvars, D, p)
        if rk == nc:
            return D, rk, nc, nr
    return None
