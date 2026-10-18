#!/usr/bin/env python3
"""Referee's own reader for the engine's exact cells (independent of concept/mechanisms/scripts).

Points: bodies 0..5, origin O = 6. A tree record has 'children' (internal node -> list of child node ids, where
leaf ids are point ids 0..6), 'leaf' (point -> leaf id; a body sitting at the origin has leaf 6) and 'root'."""
import glob, json, os, itertools

O = 6
BODIES = tuple(range(6))
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
ENUM = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'diagrams', 'n6.json')


class RTree:
    def __init__(self, tj):
        self.ch = {int(v): [int(c) for c in cs] for v, cs in tj['children'].items()}
        self.root = int(tj['root'])
        self.lf = {int(p): int(l) for p, l in tj['leaf'].items()}
        self.par = {}
        for v, cs in self.ch.items():
            for c in cs:
                assert c not in self.par
                self.par[c] = v
        # path to the root for every node
        self.up = {}
        nodes = set(self.ch) | set(self.par)
        for n in nodes:
            path = [n]
            while path[-1] in self.par:
                path.append(self.par[path[-1]])
            assert path[-1] == self.root
            self.up[n] = path
        # points below each node
        self.pts = {n: frozenset(p for p, l in self.lf.items() if n in self.up[l]) for n in nodes}
        self.internal = sorted(self.ch)

    def is_anc(self, a, b):
        """node a is an ancestor of node b or equal to it"""
        return a in self.up[b]

    def meet(self, p, q):
        """meet node of points p, q; None if they share a leaf."""
        lp, lq = self.lf[p], self.lf[q]
        if lp == lq:
            return None
        s = set(self.up[lq])
        for n in self.up[lp]:
            if n in s:
                return n
        raise ValueError

    def child_to(self, v, p):
        """child of internal node v on the path to point p, or None if p is not below v."""
        path = self.up[self.lf[p]]
        if v not in path:
            return None
        i = path.index(v)
        if i == 0:
            return None
        return path[i - 1]

    def at_origin(self, k):
        return self.lf[k] == self.lf[O]

    def depth(self, n):
        return len(self.up[n]) - 1


class RCell:
    def __init__(self, rec, cls, idx):
        self.cls, self.idx = cls, idx
        self.zt = RTree(rec['ztree'])
        self.wt = RTree(rec['wtree'])
        self.A = {}
        for name, labs in rec['argmin']:
            s = frozenset(tuple(x) for x in labs)
            if name[0] in ('z', 'w'):
                assert name[1] == 'S' and len(name[2]) == 1
                self.A[(name[0], name[2][0])] = s
            else:
                assert name[0] in ('U', 'I') and len(name) == 1
                self.A[name[0]] = s
        self.hz = {int(k): v for k, v in rec['hz'].items()}
        self.hw = {int(k): v for k, v in rec['hw'].items()}
        self.rec = rec

    def tree(self, col):
        return self.zt if col == 'z' else self.wt

    def other(self, col):
        return 'w' if col == 'z' else 'z'


class RDiag:
    def __init__(self, c):
        self.z, self.w = set(), set()
        for k, v in c['edges'].items():
            e = tuple(sorted((int(k[0]), int(k[1]))))
            if v & 1:
                self.z.add(e)
            if v & 2:
                self.w.add(e)
        self.zc = set(c['zcircles'])
        self.wc = set(c['wcircles'])
        self.zw = self.z & self.w

    def strokes(self, col):
        return self.z if col == 'z' else self.w

    def circles(self, col):
        return self.zc if col == 'z' else self.wc


def classes():
    return json.load(open(ENUM))['classes']


def cell_files():
    out = {}
    for d in glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*')):
        c = int(d.rsplit('/c', 1)[1])
        p = os.path.join(d, 'cells.jsonl')
        if os.path.exists(p) and os.path.getsize(p) > 0:
            assert c not in out
            out[c] = p
    return out


def iter_cells(cls_filter=None):
    files = cell_files()
    for c in sorted(files):
        if cls_filter is not None and c not in cls_filter:
            continue
        with open(files[c]) as fh:
            for i, line in enumerate(fh):
                yield c, i, json.loads(line)
