#!/usr/bin/env python3
"""Find the exact cell(s) containing a given exponent point: trees given as nested lists of points (n = O; a body at
O written as the pair [k, n] at leaf level), heights per internal node in the same nesting (pre-order).
Usage: find_cell.py N CLASSES_JSON IDX CELLS.jsonl SPEC.json"""
import itertools, json, sys
sys.path.insert(0, '.')
import tengine as T
import texact as X
import tsec as S


def canon(tr, v):
    if v not in tr['children']:
        pts = sorted(int(p) for p, l in tr['leaf'].items() if l == v)
        return ('L',) + tuple(pts)
    return ('N', frozenset(canon(tr, c) for c in tr['children'][v]))


def canon_tree(tj):
    tr = {'children': {int(a): b for a, b in tj['children'].items()}, 'leaf': tj['leaf']}
    return canon(tr, tj['root'])


def heights_of(tj, spec_h):
    """Map the cell's internal node ids to the heights of the spec (matching by the leaf sets below each node)."""
    tr = {int(a): b for a, b in tj['children'].items()}
    leafsets = {}

    def below(v):
        if v not in tr:
            return frozenset(int(p) for p, l in tj['leaf'].items() if l == v)
        s = frozenset()
        for c in tr[v]:
            s |= below(c)
        leafsets[v] = s
        return s

    below(tj['root'])
    return {v: spec_h[frozenset(ls)] for v, ls in leafsets.items()}


n = int(sys.argv[1])
cls = json.load(open(sys.argv[2]))['classes']
ci = int(sys.argv[3])
cells = [json.loads(l) for l in open(sys.argv[4])]
spec = json.load(open(sys.argv[5]))
D = T.Diagram.from_json(n, cls[ci])
want_z = canon_tree(spec['ztree'])
want_w = canon_tree(spec['wtree'])
hz = {frozenset(k): v for k, v in spec['hz']}
hw = {frozenset(k): v for k, v in spec['hw']}
found = []
for idx, c in enumerate(cells):
    if canon_tree(c['ztree']) != want_z or canon_tree(c['wtree']) != want_w:
        continue
    zt, wt = S.tree_from_json(n, c['ztree']), S.tree_from_json(n, c['wtree'])
    L = S.cell_lp(D, zt, wt, c['argmin'])
    Hz, Hw = heights_of(c['ztree'], hz), heights_of(c['wtree'], hw)
    rows = [({L.zv[v]: 1.0}, h, h) for v, h in Hz.items()] + [({L.wv[v]: 1.0}, h, h) for v, h in Hw.items()]
    ok, val, sol = X.sub(L, rows).solve()
    if ok and val > 1e-9:
        found.append(idx)
    elif ok:
        found.append((idx, 'closure only', val))
print('trees match and point inside:', found)
