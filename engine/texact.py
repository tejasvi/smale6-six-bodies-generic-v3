#!/usr/bin/env python3
"""Exact cells of the types engine and their initial systems.

A cell: a pair of complete trees (tengine.py) and, for every identity below whose minimum is not forced by the diagram,
the exact set of its terms of least exponent (all other terms strictly larger). On the relative interior of a cell
the initial forms of these identities are fixed. The identities (all hold on Y_m, U = I = E on the curve):
  (S_J) for every nonempty proper subset J of the bodies:
        sum_{i in J} m_i z_i - sum_{i in J, j not in J} m_i m_j delta_ij^3 z_ij = 0   (J = {k}: the equation of k),
        and the same in w;
  (U)   sum m_k m_l delta_kl - E = 0;   (I) sum m_k m_l z_kl w_kl / M - E = 0;   (I') sum m_k z_k w_k - E = 0;
  (D)   delta_kl^2 z_kl w_kl = 1 (both terms always);
  the separations: the leading coefficients are differences of node coordinates of the trees (exact).
A term's exponent: e(z_i) = a_i, e(delta_ij^3 z_ij) = e(Z_ij) = -(zeta + 3 omega)/2, e(delta_kl) = -x_kl,
e(z_kl w_kl) = 2 x_kl, e(z_k w_k) = a_k + b_k, e(E) = 0.
Usage (enumeration): texact.py N CLASSES_JSON IDX OUT.jsonl [--split DEPTH --part K --nparts P]"""
import itertools, json, sys, time
sys.path.insert(0, '.')
import tengine as T


def sub(L0, rows):
    L = T.LP.__new__(T.LP)
    L.__dict__.update(L0.__dict__)
    L.rows = L0.rows + rows
    return L


def zterm(D, zt, wt, L, i, j, colour):
    """Exponent form of delta_ij^3 z_ij (colour z) or delta_ij^3 w_ij (colour w)."""
    Z, W = L.zv[zt.meet(i, j)], L.wv[wt.meet(i, j)]
    return ({Z: -0.5, W: -1.5}, 0.0) if colour == 'z' else ({Z: -1.5, W: -0.5}, 0.0)


def identities(D, zt, wt, L):
    """All identities as (name, [(term_label, exponent_form)]), with forced minima marked: returns
    (name, terms, forced) where forced is the exact argmin (indices) if the diagram forces it, else None."""
    n = D.n
    out = []
    for colour, strokes, circ in (('z', D.zs, D.zc), ('w', D.ws, D.wc)):
        Tr, V = (zt, L.zv) if colour == 'z' else (wt, L.wv)
        for r in range(1, n):
            for J in itertools.combinations(range(n), r):
                Jc = [j for j in range(n) if j not in J]
                terms, labels = [], []
                for i in J:
                    m = Tr.meet(i, n)
                    if m is not None:
                        terms.append(({V[m]: 1.0}, 0.0))
                        labels.append(('pos', i))
                for i in J:
                    for j in Jc:
                        terms.append(zterm(D, zt, wt, L, i, j, colour))
                        labels.append(('cross', i, j))
                forced = []
                for t, lab in enumerate(labels):
                    if lab[0] == 'pos' and lab[1] in circ:
                        forced.append(t)
                    if lab[0] == 'cross' and (min(lab[1], lab[2]), max(lab[1], lab[2])) in strokes:
                        forced.append(t)
                out.append(((colour, 'S', J), labels, terms, forced if forced else None))
    pairs = list(itertools.combinations(range(n), 2))
    zw = [e for e in pairs if e in D.zs and e in D.ws]
    # (U): terms E and m m delta_kl (exponent -x_kl); forced if zw-edges exist (x = 1 exactly there)
    terms = [({}, 0.0)] + [({j: -c for j, c in T.xform(D, zt, wt, L, k, l).items()}, 0.0) for k, l in pairs]
    labels = [('E',)] + [('delta', k, l) for k, l in pairs]
    forced = [1 + pairs.index(e) for e in zw] if zw else None
    out.append((('U',), labels, terms, forced))
    terms = [({}, 0.0)] + [(T.xform(D, zt, wt, L, k, l, 2.0), 0.0) for k, l in pairs]
    labels = [('E',)] + [('zw', k, l) for k, l in pairs]
    out.append((('I',), labels, terms, None))
    terms, labels = [({}, 0.0)], [('E',)]
    for k in range(n):
        mz, mw = zt.meet(k, n), wt.meet(k, n)
        if mz is not None and mw is not None:
            terms.append(({L.zv[mz]: 1.0, L.wv[mw]: 1.0}, 0.0))
            labels.append(('zkwk', k))
    out.append((('Ip',), labels, terms, None))
    return out


def exact_argmins(L0, extra, terms, stats):
    """All exact argmin sets S (|S| >= 2) realizable within L0 + extra; yields (S, rows)."""
    s = L0.ns
    N = len(terms)
    res = []

    def diff(a, b):           # t_a - t_b as (coefs, const)
        return T.lin_sub(terms[a], terms[b])

    def rec(j, first, ins, outs, rows):
        if j == N:
            if first is not None and len(ins) >= 2:
                res.append((tuple(ins), list(rows)))
            return
        # option IN
        if first is None:
            new = []
            for o in outs:
                d, k = diff(o, j)
                dd = dict(d)
                dd[s] = dd.get(s, 0.0) - 1.0
                new.append((dd, -k, None))
            nrows = rows + new
            stats['lp'] += 1
            if T.feasible(sub(L0, extra + nrows))[0]:
                rec(j + 1, j, ins + [j], outs, nrows)
        else:
            d, k = diff(j, first)
            nrows = rows + [(d, -k, -k)]
            stats['lp'] += 1
            if T.feasible(sub(L0, extra + nrows))[0]:
                rec(j + 1, first, ins + [j], outs, nrows)
        # option OUT
        if first is None:
            # the remaining terms must supply at least two IN terms
            if N - j - 1 >= 2:
                rec(j + 1, None, ins, outs + [j], rows)
        else:
            d, k = diff(j, first)
            dd = dict(d)
            dd[s] = dd.get(s, 0.0) - 1.0
            nrows = rows + [(dd, -k, None)]
            if len(ins) >= 2 or N - j - 1 >= 2 - len(ins):
                stats['lp'] += 1
                if T.feasible(sub(L0, extra + nrows))[0]:
                    rec(j + 1, first, ins, outs + [j], nrows)

    rec(0, None, [], [], [])
    return res


def forced_rows(L0, terms, forced):
    """Rows saying that exactly the forced terms attain the minimum (they equal -2 by the diagram)."""
    s = L0.ns
    rows = []
    f0 = forced[0]
    for t in range(len(terms)):
        if t == f0:
            continue
        d, k = T.lin_sub(terms[t], terms[f0])
        if t in forced:
            rows.append((d, -k, -k))
        else:
            dd = dict(d)
            dd[s] = dd.get(s, 0.0) - 1.0
            rows.append((dd, -k, None))
    return rows


def cells_below(D, zt, wt, stats, groups_filter=None, mode=None):
    """Exact cells below a complete tree pair: lists of (identity name, argmin labels)."""
    n = D.n
    if not (T.com_ok(zt) and T.com_ok(wt)):
        return []
    L0 = T.base_lp(D, zt, wt, list(range(n + 1)))
    if L0 is None:
        return []
    if mode is not None:
        import tsign
        L0.rows.append(tsign.threshold_row(D, zt, wt, L0, list(range(n + 1)), mode))
    stats['lp'] += 1
    if not T.feasible(L0)[0]:
        return []
    ids = identities(D, zt, wt, L0)
    if groups_filter is not None:
        ids = [x for x in ids if groups_filter(x[0])]
    base_extra = []
    fixed = []
    branch = []
    for name, labels, terms, forced in ids:
        if forced is not None:
            if len(forced) < 2:
                return []                     # a single forced minimal term: impossible
            base_extra += forced_rows(L0, terms, forced)
            fixed.append((name, [labels[t] for t in forced]))
        else:
            branch.append((name, labels, terms))
    stats['lp'] += 1
    if not T.feasible(sub(L0, base_extra))[0]:
        return []
    return _stream(zt, wt, L0, branch, fixed, base_extra, stats)


def _stream(zt, wt, L0, branch, fixed, base_extra, stats):
    """The cells below a tree pair, yielded in the order of the former list (memory: one path of the recursion)."""

    def rec(gi, extra, chosen):
        if gi == len(branch):
            yield (zt, wt, L0, fixed + chosen, extra)
            return
        name, labels, terms = branch[gi]
        for S, rows in exact_argmins(L0, extra, terms, stats):
            yield from rec(gi + 1, extra + rows, chosen + [(name, [labels[t] for t in S])])

    yield from rec(0, base_extra, [])


def tree_json(Tr):
    return {'children': {str(a): b for a, b in Tr.children.items()}, 'leaf': {str(a): b for a, b in Tr.leaf.items()},
            'root': Tr.root}


def interior(D, zt, wt, L0, ex):
    L = sub(L0, ex)
    ok, val, sol = L.solve()
    n = D.n
    xs = {f'{k}{l}': round(0.5 * (sol[L.zv[zt.meet(k, l)]] + sol[L.wv[wt.meet(k, l)]]), 6)
          for k, l in itertools.combinations(range(n), 2)}
    hz = {str(v): round(sol[i], 6) for v, i in L.zv.items()}
    hw = {str(v): round(sol[i], 6) for v, i in L.wv.items()}
    return xs, hz, hw, val


def enumerate_cells(D, out, split=None, part=0, nparts=1, groups_filter=None, mode=None):
    import tsign
    n = D.n
    stats = {'lp': 0, 'pairs': 0, 'cells': 0}
    zt0 = T.Tree(n).options(n)[0]
    wt0 = T.Tree(n).options(n)[0]
    order = T.order_bodies(D)
    counter = [0]

    def rec(i, zt, wt, pts):
        if i == n:
            stats['pairs'] += 1
            for zt2, wt2, L0, c, ex in cells_below(D, zt, wt, stats, groups_filter, mode):
                xs, hz, hw, sl = interior(D, zt2, wt2, L0, ex)
                stats['cells'] += 1
                out.write(json.dumps({'ztree': tree_json(zt2), 'wtree': tree_json(wt2), 'argmin': c, 'x': xs,
                                      'hz': hz, 'hw': hw, 'slack': round(sl, 9),
                                      'sumx': round(sum(xs.values()), 6)}) + '\n')
            return
        p = order[i]
        npts = pts + [p]
        for zt2 in zt.options(p):
            for wt2 in wt.options(p):
                if split is not None and i + 1 == split:
                    c = counter[0]
                    counter[0] += 1
                    if c % nparts != part:
                        continue
                L = T.base_lp(D, zt2, wt2, npts)
                if L is None:
                    continue
                if mode is not None:
                    L.rows.append(tsign.threshold_row(D, zt2, wt2, L, npts, mode))
                stats['lp'] += 1
                if T.feasible(L)[0]:
                    rec(i + 1, zt2, wt2, npts)

    rec(0, zt0, wt0, [n])
    return stats


if __name__ == '__main__':
    n = int(sys.argv[1])
    cls = json.load(open(sys.argv[2]))['classes']
    ci = int(sys.argv[3])
    outp = sys.argv[4]
    split, part, nparts = None, 0, 1
    mode = sys.argv[sys.argv.index('--mode') + 1] if '--mode' in sys.argv else None
    if '--split' in sys.argv:
        split = int(sys.argv[sys.argv.index('--split') + 1])
        part = int(sys.argv[sys.argv.index('--part') + 1])
        nparts = int(sys.argv[sys.argv.index('--nparts') + 1])
    D = T.Diagram.from_json(n, cls[ci])
    t = time.time()
    with open(outp, 'w') as f:
        gf = None
        if '--base' in sys.argv:
            gf = lambda name: (name[0] in ('z', 'w') and len(name[2]) == 1) or name[0] in ('U', 'I')
        st = enumerate_cells(D, f, split, part, nparts, groups_filter=gf, mode=mode)
    print(json.dumps({'class': ci, 'part': part, 'nparts': nparts, 'stats': st, 'time': round(time.time() - t, 1)}))
