#!/usr/bin/env python3
"""Referee's independent construction of the two polynomial systems of d88 (no code shared with d88/scripts).

Polynomials are dicts {exponent tuple: Fraction}.  Written from the definitions in DERIVATION.md A.5 and B.4 only.

N4 (diagram 88), slice X1 - X2 = 1, centre of mass used to eliminate X4, Y4:
  vars  X2 X3 Y1 Y2 Y3 p12 p13 p14 p23 p24 p34
  S12 = X-equations of bodies 1,2,3; Y-equations of bodies 1,2,3; six distance equations.
KC (diagram 94), slice X1 = 1, X4 = 0, U_k = Y_k - Y4, Y4 eliminated by the Y-equation of body 1:
  vars  X2 X3 U1 U2 U3 p12 p13 p14 p23 p24 p34
  KC = X-equations of bodies 1..4 (body 4: 0 = sum_l mu_l p_4l^3 (X4 - X_l)); Y-equations of bodies 2,3; six distances.
"""
from fractions import Fraction as Fr
import itertools

PAIRS = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]


class P:
    __slots__ = ('t', 'n')

    def __init__(self, n, t=None):
        self.n = n
        self.t = {k: v for k, v in (t or {}).items() if v != 0}

    @staticmethod
    def const(n, c):
        return P(n, {(0,) * n: Fr(c)})

    @staticmethod
    def var(n, i):
        e = [0] * n
        e[i] = 1
        return P(n, {tuple(e): Fr(1)})

    def __add__(self, o):
        if not isinstance(o, P):
            o = P.const(self.n, o)
        t = dict(self.t)
        for k, v in o.t.items():
            t[k] = t.get(k, 0) + v
        return P(self.n, t)
    __radd__ = __add__

    def __neg__(self):
        return P(self.n, {k: -v for k, v in self.t.items()})

    def __sub__(self, o):
        return self + (-o if isinstance(o, P) else P.const(self.n, -o))

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if not isinstance(o, P):
            o = Fr(o)
            return P(self.n, {k: v * o for k, v in self.t.items()})
        t = {}
        for k1, v1 in self.t.items():
            for k2, v2 in o.t.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                t[k] = t.get(k, 0) + v1 * v2
        return P(self.n, t)
    __rmul__ = __mul__

    def __pow__(self, e):
        r = P.const(self.n, 1)
        for _ in range(e):
            r = r * self
        return r

    def is_zero(self):
        return not self.t

    def cleared(self):
        """integer primitive multiple (positive leading content), as a new P with Fraction entries."""
        from math import gcd
        den = 1
        for v in self.t.values():
            den = den * v.denominator // gcd(den, v.denominator)
        ints = {k: int(v * den) for k, v in self.t.items()}
        g = 0
        for v in ints.values():
            g = gcd(g, abs(v))
        return P(self.n, {k: Fr(v // g) for k, v in ints.items()})

    def deriv(self, i):
        t = {}
        for k, v in self.t.items():
            if k[i] > 0:
                kk = list(k)
                kk[i] -= 1
                t[tuple(kk)] = t.get(tuple(kk), 0) + v * k[i]
        return P(self.n, t)


def n4_system(mu):
    m = {k + 1: Fr(mu[k]) for k in range(4)}
    names = ['X2', 'X3', 'Y1', 'Y2', 'Y3', 'p12', 'p13', 'p14', 'p23', 'p24', 'p34']
    n = len(names)
    V = {nm: P.var(n, i) for i, nm in enumerate(names)}
    X = {2: V['X2'], 3: V['X3']}
    X[1] = X[2] + 1
    X[4] = (m[1] * X[1] + m[2] * X[2] + m[3] * X[3]) * Fr(-1) * (1 / m[4])
    Y = {1: V['Y1'], 2: V['Y2'], 3: V['Y3']}
    Y[4] = (m[1] * Y[1] + m[2] * Y[2] + m[3] * Y[3]) * Fr(-1) * (1 / m[4])
    p = {}
    for (a, b) in PAIRS:
        p[(a, b)] = p[(b, a)] = V['p%d%d' % (a, b)]
    eqs = []
    for Z in (X, Y):
        for k in (1, 2, 3):
            e = Z[k]
            for l in (1, 2, 3, 4):
                if l != k:
                    e = e - m[l] * p[(k, l)] ** 3 * (Z[k] - Z[l])
            eqs.append(e)
    for (a, b) in PAIRS:
        eqs.append(p[(a, b)] ** 2 * (X[a] - X[b]) * (Y[a] - Y[b]) - 1)
    return names, eqs


def kc_system(mu):
    m = {k + 1: Fr(mu[k]) for k in range(4)}
    names = ['X2', 'X3', 'U1', 'U2', 'U3', 'p12', 'p13', 'p14', 'p23', 'p24', 'p34']
    n = len(names)
    V = {nm: P.var(n, i) for i, nm in enumerate(names)}
    X = {1: P.const(n, 1), 2: V['X2'], 3: V['X3'], 4: P.const(n, 0)}
    U = {1: V['U1'], 2: V['U2'], 3: V['U3'], 4: P.const(n, 0)}
    p = {}
    for (a, b) in PAIRS:
        p[(a, b)] = p[(b, a)] = V['p%d%d' % (a, b)]

    def force(Z, k):
        s = P.const(n, 0)
        for l in (1, 2, 3, 4):
            if l != k:
                s = s + m[l] * p[(k, l)] ** 3 * (Z[k] - Z[l])
        return s
    # Y-equation of body k:  Y4 + U_k - force(U, k) = 0 ; body 1 gives Y4 = force(U,1) - U1
    Y4 = force(U, 1) - U[1]
    eqs = []
    for k in (1, 2, 3):
        eqs.append(X[k] - force(X, k))
    eqs.append(P.const(n, 0) - force(X, 4))
    for k in (2, 3):
        eqs.append(Y4 + U[k] - force(U, k))
    for (a, b) in PAIRS:
        eqs.append(p[(a, b)] ** 2 * (X[a] - X[b]) * (U[a] - U[b]) - 1)
    return names, eqs


def to_msolve(names, eqs, char):
    lines = [','.join(names), str(char)]
    body = []
    for e in eqs:
        c = e.cleared()
        terms = []
        for k in sorted(c.t, reverse=True):
            v = int(c.t[k])
            mon = '*'.join(('%s^%d' % (nm, d) if d > 1 else nm) for nm, d in zip(names, k) if d > 0)
            s = str(abs(v)) + ('*' + mon if mon else '')
            terms.append(('-' if v < 0 else '+') + s)
        t = ''.join(terms)
        if t.startswith('+'):
            t = t[1:]
        body.append(t)
    return '\n'.join(lines) + '\n' + ',\n'.join(body) + '\n'


def parse_msolve(text):
    """strict re-parse of an msolve file into (names, char, list of P)."""
    import re
    ls = text.strip().split('\n')
    names = [s.strip() for s in ls[0].split(',')]
    char = int(ls[1])
    body = ''.join(ls[2:]).replace(' ', '')
    polys = []
    n = len(names)
    for ps in body.split(','):
        if not ps:
            continue
        assert '(' not in ps and '**' not in ps and '.' not in ps and '/' not in ps
        toks = re.findall(r'[+-]?[^+-]+', ps)
        t = {}
        for tok in toks:
            sg = -1 if tok[0] == '-' else 1
            tok = tok.lstrip('+-')
            fs = tok.split('*')
            c = 1
            e = [0] * n
            seen = set()
            for i, f in enumerate(fs):
                if re.fullmatch(r'\d+', f):
                    assert i == 0
                    c = int(f)
                else:
                    mm = re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*)(\^(\d+))?', f)
                    assert mm, f
                    v = mm.group(1)
                    assert v not in seen
                    seen.add(v)
                    e[names.index(v)] += int(mm.group(3) or 1)
            k = tuple(e)
            assert k not in t, 'duplicate monomial'
            t[k] = Fr(sg * c)
        polys.append(P(n, t))
    return names, char, polys


if __name__ == '__main__':
    import sys
    kind, mu, char, out = sys.argv[1], [int(x) for x in sys.argv[2:6]], int(sys.argv[6]), sys.argv[7]
    names, eqs = (n4_system if kind == 'n4' else kc_system)(mu)
    open(out, 'w').write(to_msolve(names, eqs, char))
    print(out, len(names), 'vars', len(eqs), 'eqs')
