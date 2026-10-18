#!/usr/bin/env python3
"""Sign test of the types engine (full system of tengine.py): is there a cell containing a type with
sum_kl x_kl >= 0 (mode ge) or <= 0 (mode le)? Depth-first search with the threshold in every LP; stops at the
first witness. Partial trees use the bounds x <= 1 (x < 1 off zw-edges) and x >= -2 (x >= 0 on strokes, = 1 on
zw-edges) for the pairs not yet placed.
Usage: tsign.py N CLASSES_JSON IDX MODE [--split DEPTH --part K --nparts P]
Output: one JSON line {class, mode, part, found, witness (x vector, trees), stats}."""
import itertools, json, sys, time
sys.path.insert(0, '.')
import tengine as T

TOL = 1e-9


def threshold_row(D, zt, wt, L, pts, mode):
    n = D.n
    bodies = sorted(p for p in pts if p != n)
    placed = set(itertools.combinations(bodies, 2))
    coefs = {}
    const = 0.0
    for k, l in itertools.combinations(range(n), 2):
        if (k, l) in placed:
            for j, c in T.xform(D, zt, wt, L, k, l).items():
                coefs[j] = coefs.get(j, 0.0) + c
        else:
            zwe = D.zstroke(k, l) and D.wstroke(k, l)
            st = D.zstroke(k, l) or D.wstroke(k, l)
            if mode == 'ge':
                const += 1.0
            else:
                const += 1.0 if zwe else (0.0 if st else -2.0)
    if mode == 'ge':
        return (coefs, -const, None)                   # sum_placed x + const >= 0
    return (coefs, None, -const)                       # sum_placed x + const <= 0


def first_argmin_branches(L, terms):
    """Two-level branching for 'min attained at least twice': first argmin i (t_j > t_i for j < i, t_j >= t_i for
    j > i), then a second index j > i with t_j = t_i."""
    s = L.ns
    N = len(terms)
    for i in range(N):
        rows_i = []
        for j in range(N):
            if j == i:
                continue
            d, k = T.lin_sub(terms[j], terms[i])
            if j < i:
                dd = dict(d)
                dd[s] = dd.get(s, 0.0) - 1.0
                rows_i.append((dd, -k, None))
            else:
                rows_i.append((d, -k, None))
        seconds = []
        for j in range(i + 1, N):
            d, k = T.lin_sub(terms[j], terms[i])
            seconds.append((d, -k, -k))
        yield rows_i, seconds


def sub(L0, rows):
    L = T.LP.__new__(T.LP)
    L.__dict__.update(L0.__dict__)
    L.rows = L0.rows + rows
    return L


def groups_full(D, zt, wt, L0):
    """(U) and (I) first, then (B) and (I')."""
    n = D.n
    pairs = list(itertools.combinations(range(n), 2))
    zw = [e for e in pairs if e in D.zs and e in D.ws]
    gs = []
    gs.append([({}, 0.0)] + [(T.xform(D, zt, wt, L0, k, l, 2.0), 0.0) for k, l in pairs])
    if len(zw) < 2:
        gs.append([({}, 0.0)] + [({j: -c for j, c in T.xform(D, zt, wt, L0, k, l).items()}, 0.0) for k, l in pairs])
    for colour, strokes in (('z', D.zs), ('w', D.ws)):
        for k in range(n):
            if not any(k in e for e in strokes):
                gs.append(T.terms_body(D, zt, wt, L0, k, colour))
    ip = [({}, 0.0)]
    for k in range(n):
        mz, mw = zt.meet(k, n), wt.meet(k, n)
        if mz is not None and mw is not None:
            ip.append(({L0.zv[mz]: 1.0, L0.wv[mw]: 1.0}, 0.0))
    gs.append(ip)
    return gs


def search_completion(D, zt, wt, mode, stats):
    n = D.n
    if not (T.com_ok(zt) and T.com_ok(wt)):
        return None
    L0 = T.base_lp(D, zt, wt, list(range(n + 1)))
    if L0 is None:
        return None
    L0.rows.append(threshold_row(D, zt, wt, L0, list(range(n + 1)), mode))
    stats['lp'] += 1
    if not T.feasible(L0)[0]:
        return None
    groups = groups_full(D, zt, wt, L0)

    def rec(gi, extra):
        if gi == len(groups):
            return extra
        for rows_i, seconds in first_argmin_branches(L0, groups[gi]):
            stats['lp'] += 1
            if not T.feasible(sub(L0, extra + rows_i))[0]:
                continue
            for r2 in seconds:
                stats['lp'] += 1
                if T.feasible(sub(L0, extra + rows_i + [r2]))[0]:
                    res = rec(gi + 1, extra + rows_i + [r2])
                    if res is not None:
                        return res
        return None

    ex = rec(0, [])
    if ex is None:
        return None
    L = sub(L0, ex)
    ok, val, sol = L.solve()
    xs = {f'{k}{l}': round(0.5 * (sol[L.zv[zt.meet(k, l)]] + sol[L.wv[wt.meet(k, l)]]), 6)
          for k, l in itertools.combinations(range(n), 2)}
    pos = {}
    for k in range(n):
        for tag, Tr, V in (('a', zt, L.zv), ('b', wt, L.wv)):
            m = Tr.meet(k, n)
            pos[f'{tag}{k}'] = None if m is None else round(sol[V[m]], 6)
    return {'x': xs, 'pos': pos, 'sumx': round(sum(xs.values()), 6), 'slack': round(val, 9),
            'ztree': {str(a): b for a, b in zt.children.items()}, 'wtree': {str(a): b for a, b in wt.children.items()},
            'zleaf': {str(a): b for a, b in zt.leaf.items()}, 'wleaf': {str(a): b for a, b in wt.leaf.items()}}


def search(D, mode, split=None, part=0, nparts=1):
    n = D.n
    stats = {'lp': 0, 'nodes': 0, 'pairs': 0}
    zt0 = T.Tree(n).options(n)[0]
    wt0 = T.Tree(n).options(n)[0]
    order = T.order_bodies(D)
    counter = [0]

    def rec(i, zt, wt, pts):
        if i == n:
            stats['pairs'] += 1
            return search_completion(D, zt, wt, mode, stats)
        p = order[i]
        npts = pts + [p]
        for zt2 in zt.options(p):
            for wt2 in wt.options(p):
                if split is not None and i + 1 == split:
                    c = counter[0]
                    counter[0] += 1
                    if c % nparts != part:
                        continue
                stats['nodes'] += 1
                L = T.base_lp(D, zt2, wt2, npts)
                if L is None:
                    continue
                L.rows.append(threshold_row(D, zt2, wt2, L, npts, mode))
                stats['lp'] += 1
                if T.feasible(L)[0]:
                    r = rec(i + 1, zt2, wt2, npts)
                    if r is not None:
                        return r
        return None

    return rec(0, zt0, wt0, [n]), stats


if __name__ == '__main__':
    n = int(sys.argv[1])
    cls = json.load(open(sys.argv[2]))['classes']
    ci = int(sys.argv[3])
    mode = sys.argv[4]
    split, part, nparts = None, 0, 1
    if '--split' in sys.argv:
        split = int(sys.argv[sys.argv.index('--split') + 1])
        part = int(sys.argv[sys.argv.index('--part') + 1])
        nparts = int(sys.argv[sys.argv.index('--nparts') + 1])
    D = T.Diagram.from_json(n, cls[ci])
    t = time.time()
    w, st = search(D, mode, split, part, nparts)
    print(json.dumps({'class': ci, 'mode': mode, 'part': part, 'nparts': nparts, 'found': w is not None,
                      'witness': w, 'stats': st, 'time': round(time.time() - t, 1)}), flush=True)
