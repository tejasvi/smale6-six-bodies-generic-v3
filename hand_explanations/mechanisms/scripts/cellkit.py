#!/usr/bin/env python3
"""Small toolkit for exact cells (read-only use of the engine's data formats).

A cell record has ztree/wtree (children, leaf, root), heights hz/hw of the internal nodes at an interior point, and
argmin data. Here: exponents at the interior point, tree navigation, and the terms of the identities."""
import itertools, json, os
from fractions import Fraction

N = 6
O = 6  # the origin's index in the trees


class Tr:
    def __init__(self, tj, h=None):
        self.children = {int(a): list(b) for a, b in tj['children'].items()}
        self.parent = {}
        for a, ch in self.children.items():
            for c in ch:
                self.parent[c] = a
        self.root = tj['root']
        self.leaf = {int(a): b for a, b in tj['leaf'].items()}
        self.h = {int(a): float(b) for a, b in h.items()} if h is not None else None

    def anc(self, v):
        out = [v]
        while v in self.parent:
            v = self.parent[v]
            out.append(v)
        return out

    def meet_nodes(self, u, v):
        if u == v:
            return None
        au = self.anc(u)
        sv = set(self.anc(v))
        for w in au:
            if w in sv:
                return w

    def meet(self, p, q):
        """meet of points p, q (bodies 0..5 or O = 6); None if they share a leaf."""
        return self.meet_nodes(self.leaf[p], self.leaf[q])

    def child_of(self, v, p):
        """the child of internal node v whose subtree contains point p (None if p is not below v)."""
        u = self.leaf[p]
        while u in self.parent and self.parent[u] != v:
            u = self.parent[u]
        return u if self.parent.get(u) == v else None

    def below(self, v):
        """the points (bodies and O) below node v."""
        pts = []
        for p, lf in self.leaf.items():
            if v in self.anc(lf):
                pts.append(p)
        return sorted(pts)

    def height(self, v):
        return self.h[v]

    def depth(self, v):
        return len(self.anc(v)) - 1


class Cell:
    def __init__(self, rec):
        self.rec = rec
        self.zt = Tr(rec['ztree'], rec.get('hz'))
        self.wt = Tr(rec['wtree'], rec.get('hw'))
        self.cls = rec.get('class')

    # exponents at the interior point
    def zeta(self, k, l):
        return self.zt.h[self.zt.meet(k, l)]

    def omega(self, k, l):
        return self.wt.h[self.wt.meet(k, l)]

    def x(self, k, l):
        return 0.5 * (self.zeta(k, l) + self.omega(k, l))

    def a(self, k):
        m = self.zt.meet(k, O)
        return float('inf') if m is None else self.zt.h[m]

    def b(self, k):
        m = self.wt.meet(k, O)
        return float('inf') if m is None else self.wt.h[m]

    def eZ(self, k, l):  # exponent of delta^3 z_kl
        return -0.5 * (self.zeta(k, l) + 3 * self.omega(k, l))

    def eW(self, k, l):
        return -0.5 * (3 * self.zeta(k, l) + self.omega(k, l))


def load_classes():
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'diagrams', 'n6.json')
    return json.load(open(p))['classes']


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
        self.zw = self.zs & self.ws

    def zstroke(self, k, l):
        return (min(k, l), max(k, l)) in self.zs

    def wstroke(self, k, l):
        return (min(k, l), max(k, l)) in self.ws


def torque_terms(C, J):
    """terms of T_J with exponents at the interior point: (exp, label)."""
    out = []
    Jc = [j for j in range(N) if j not in J]
    for k in J:
        for l in Jc:
            e3 = -3 * C.x(k, l)
            out.append((e3 + C.a(k) + C.b(l), ('T1', k, l)))
            out.append((e3 + C.b(k) + C.a(l), ('T2', k, l)))
    return sorted(out)


def subset_terms(C, J, colour):
    out = []
    Jc = [j for j in range(N) if j not in J]
    for i in J:
        out.append(((C.a(i) if colour == 'z' else C.b(i)), ('SP', colour, i)))
    for i in J:
        for j in Jc:
            out.append(((C.eZ(i, j) if colour == 'z' else C.eW(i, j)), ('SC', colour, i, j)))
    return sorted(out)


def tree_str(t):
    """nested string of a tree with heights."""
    def rec(v):
        if v not in t.children:
            pts = [p for p, lf in t.leaf.items() if lf == v]
            return '/'.join('O' if p == O else str(p) for p in sorted(pts))
        h = t.h[v] if t.h else None
        return '(' + ' '.join(rec(c) for c in t.children[v]) + (f')@{h:g}' if h is not None else ')')
    return rec(t.root)
