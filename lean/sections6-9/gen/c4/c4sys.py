#!/usr/bin/env python3
"""The equations of the compact model Z(mu) of C_4 (Section 7.3 of the paper), chart by chart.

Variables, in this order: s, t, p12, p13, p14, p23, p24, p34, c (indices 0..8). Bodies 1..4 (indices 0..3), body 4
the centre, xi = (mu3 s, mu3 t, -(mu1 s + mu2 t), 0).
  (I)   sum_{l != k} mu_l p_kl^3 (xi_k - xi_l),                                         k = 1..4
  (II)  sum_{l != k} mu_l p_kl prod_{j != k,l} (xi_k - xi_j) - c prod_{l != k} (xi_k - xi_l),   k = 1..3
  (III) a_ln a_nk + a_kl a_nk + a_kl a_ln with a_kl = p_kl^2 (xi_k - xi_l), the triangles 123, 124, 134, 234.
A chart sets one of s, t and one of p12, ..., p34, c equal to 1. Polynomials are dicts {exponent tuple: int}.
"""
import sys

VARS = ['s', 't', 'p12', 'p13', 'p14', 'p23', 'p24', 'p34', 'c']
NV = 9
PIDX = {(0, 1): 2, (0, 2): 3, (0, 3): 4, (1, 2): 5, (1, 3): 6, (2, 3): 7}
CHARTS = [(x, p) for x in (0, 1) for p in (2, 3, 4, 5, 6, 7, 8)]


def padd(f, g, sg=1):
    h = dict(f)
    for e, c in g.items():
        v = h.get(e, 0) + sg * c
        if v:
            h[e] = v
        else:
            h.pop(e, None)
    return h


def pmul(f, g):
    h = {}
    for e1, c1 in f.items():
        for e2, c2 in g.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            v = h.get(e, 0) + c1 * c2
            if v:
                h[e] = v
            else:
                h.pop(e, None)
    return h


def pscal(f, a):
    return {e: a * c for e, c in f.items()} if a else {}


def pvar(i):
    e = [0] * NV
    e[i] = 1
    return {tuple(e): 1}


def pconst(a):
    return {(0,) * NV: a} if a else {}


def ppow(f, n):
    r = pconst(1)
    for _ in range(n):
        r = pmul(r, f)
    return r


def equations(mu):
    s, t, c = pvar(0), pvar(1), pvar(8)
    xi = [pscal(s, mu[2]), pscal(t, mu[2]), padd(pscal(s, -mu[0]), pscal(t, -mu[1])), {}]

    def d(k, l):
        return padd(xi[k], xi[l], -1)

    def P(k, l):
        return pvar(PIDX[(min(k, l), max(k, l))])
    eqs = []
    for k in range(4):
        f = {}
        for l in range(4):
            if l != k:
                f = padd(f, pscal(pmul(ppow(P(k, l), 3), d(k, l)), mu[l]))
        eqs.append(f)
    for k in range(3):
        f = {}
        for l in range(4):
            if l == k:
                continue
            term = pscal(P(k, l), mu[l])
            for j in range(4):
                if j not in (k, l):
                    term = pmul(term, d(k, j))
            f = padd(f, term)
        pr = pconst(1)
        for l in range(4):
            if l != k:
                pr = pmul(pr, d(k, l))
        f = padd(f, pmul(c, pr), -1)
        eqs.append(f)

    def a(k, l):
        return pmul(ppow(P(k, l), 2), d(k, l))
    for (k, l, n) in [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]:
        eqs.append(padd(padd(pmul(a(l, n), a(n, k)), pmul(a(k, l), a(n, k))), pmul(a(k, l), a(l, n))))
    return eqs


def dehom(f, chart):
    h = {}
    for e, c in f.items():
        e2 = tuple(0 if i in chart else x for i, x in enumerate(e))
        v = h.get(e2, 0) + c
        if v:
            h[e2] = v
        else:
            h.pop(e2, None)
    return h


def chart_vars(chart):
    return [i for i in range(NV) if i not in chart]


def to_str(f, names_all, keep):
    terms = []
    for e, c in sorted(f.items(), reverse=True):
        mon = '*'.join(names_all[i] if e[i] == 1 else '%s^%d' % (names_all[i], e[i]) for i in keep if e[i])
        if not mon:
            terms.append('%d' % c)
        else:
            terms.append('%d*%s' % (c, mon))
    s = '+'.join(terms).replace('+-', '-')
    return s if s else '0'


def chart_name(chart):
    return '%s_%s' % (VARS[chart[0]], VARS[chart[1]])


if __name__ == '__main__':
    mu = tuple(int(x) for x in sys.argv[1].split(','))
    for ch in CHARTS:
        eqs = [dehom(f, ch) for f in equations(mu)]
        print(chart_name(ch), [len(f) for f in eqs])
