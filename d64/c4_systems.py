#!/usr/bin/env python3
"""The compact model of the 'K4 with centre and uniform w-force' system C4 (DERIVATION.md, Lemma C).

Bodies 1..4 (indices 0..3), body 4 = the centre.  Masses mu = (mu1, mu2, mu3, mu4) (integers).
xi = (mu3*s, mu3*t, -(mu1*s + mu2*t), 0)  [body 4 at xi = 0 and at the xi-centre of mass of the K4]
Unknowns: (s, t) and (p12, p13, p14, p23, p24, p34, c); grading deg(s) = deg(t) = (1,0), deg(p) = (0,1),
deg(c) = (-1,1).  The compact space X is the quotient of (C^2 - 0) x (C^7 - 0) by this (C*)^2 action, a P^6-bundle
over P^1 (projective).
Equations (all homogeneous for the grading):
 (I)   E_k   = sum_{l != k} mu_l p_kl^3 xi_kl                                            k = 1..4
 (II)  H_k   = sum_{l != k} mu_l p_kl prod_{j != k,l} xi_kj  -  c prod_{l != k} xi_kl      k = 1..3
 (III) T_kln = a_ln a_nk + a_kl a_nk + a_kl a_ln,  a_kl = p_kl^2 xi_kl,                  all 4 triangles
Charts: s = 1 or t = 1, and one of p12, ..., p34, c equal to 1 (14 affine charts covering X).

Self-contained polynomial arithmetic (dicts {exponent tuple: int}); no sympy, so this module is independent of the
exploration scripts and of the Singular checker.
"""
VARS = ['s', 't', 'p12', 'p13', 'p14', 'p23', 'p24', 'p34', 'c']
NV = len(VARS)
PIDX = {(0, 1): 2, (0, 2): 3, (0, 3): 4, (1, 2): 5, (1, 3): 6, (2, 3): 7}
CIDX = 8


def const(a):
    return {(0,) * NV: a} if a else {}


def var(i):
    e = [0] * NV
    e[i] = 1
    return {tuple(e): 1}


def add(f, g, sign=1):
    h = dict(f)
    for e, c in g.items():
        v = h.get(e, 0) + sign * c
        if v:
            h[e] = v
        else:
            h.pop(e, None)
    return h


def mul(f, g):
    h = {}
    for e1, c1 in f.items():
        for e2, c2 in g.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            v = h.get(e, 0) + c1 * c2
            if v:
                h[e] = v
            else:
                h.pop(e, None)
    return h


def scal(f, a):
    return {e: a * c for e, c in f.items()} if a else {}


def power(f, n):
    r = const(1)
    for _ in range(n):
        r = mul(r, f)
    return r


def P(k, l):
    return var(PIDX[(min(k, l), max(k, l))])


def build(mu):
    s, t, c = var(0), var(1), var(CIDX)
    xi = [scal(s, mu[2]), scal(t, mu[2]), add(scal(s, -mu[0]), scal(t, -mu[1])), {}]

    def d(k, l):
        return add(xi[k], xi[l], -1)
    eqs = []
    for k in range(4):                                   # (I)
        f = {}
        for l in range(4):
            if l != k:
                f = add(f, scal(mul(power(P(k, l), 3), d(k, l)), mu[l]))
        eqs.append(('I%d' % (k + 1), f))
    for k in range(3):                                   # (II)
        f = {}
        for l in range(4):
            if l == k:
                continue
            term = scal(P(k, l), mu[l])
            for j in range(4):
                if j not in (k, l):
                    term = mul(term, d(k, j))
            f = add(f, term)
        prod = const(1)
        for l in range(4):
            if l != k:
                prod = mul(prod, d(k, l))
        f = add(f, mul(c, prod), -1)
        eqs.append(('II%d' % (k + 1), f))

    def a(k, l):
        return mul(power(P(k, l), 2), d(k, l))
    for (k, l, n) in [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]:   # (III)
        f = add(add(mul(a(l, n), a(n, k)), mul(a(k, l), a(n, k))), mul(a(k, l), a(l, n)))
        eqs.append(('III%d%d%d' % (k + 1, l + 1, n + 1), f))
    return eqs


def degree_check(eqs):
    """Every equation homogeneous for the grading deg s = deg t = (1,0), deg p = (0,1), deg c = (-1,1)."""
    out = []
    for name, f in eqs:
        degs = set()
        for e in f:
            d1 = e[0] + e[1] - e[CIDX]
            d2 = sum(e[2:8]) + e[CIDX]
            degs.add((d1, d2))
        assert len(degs) == 1, (name, degs)
        out.append((name, degs.pop()))
    return out


def charts():
    return [(xv, pv) for xv in (0, 1) for pv in list(range(2, 8)) + [CIDX]]


def dehomogenize(f, chart):
    xv, pv = chart
    h = {}
    for e, c in f.items():
        e2 = tuple(0 if i in (xv, pv) else x for i, x in enumerate(e))
        v = h.get(e2, 0) + c
        if v:
            h[e2] = v
        else:
            h.pop(e2, None)
    return h


def to_string(f, names):
    """Expanded polynomial as a string: integer coefficients, '*' and '^' only, no parentheses."""
    terms = []
    for e, c in sorted(f.items(), reverse=True):
        mon = '*'.join(n if k == 1 else '%s^%d' % (n, k) for n, k in zip(names, e) if k)
        if not mon:
            terms.append('%d' % c)
        elif c == 1:
            terms.append(mon)
        elif c == -1:
            terms.append('-' + mon)
        else:
            terms.append('%d*%s' % (c, mon))
    sgn = '+'.join(terms).replace('+-', '-')
    return sgn if sgn else '0'
