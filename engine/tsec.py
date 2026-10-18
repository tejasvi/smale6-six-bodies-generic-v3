#!/usr/bin/env python3
"""Secondary identities on a cell: initial forms that are constant on the cell, added to its initial system.

Secondary identities (all in the ideal of the equations; z_kl = z_k - z_l, delta^2 z_kl w_kl = 1):
  (S_J)  subset sums (texact.py), when not already in the cell's argmin data;
  (T_J)  torques: sum_{k in J, l not in J} m_k m_l delta_kl^3 (z_k w_l - w_k z_l) = 0;
  (V_J)  sub-virials: sum_{k in J} m_k z_k w_k - sum_{k<l in J} m_k m_l delta_kl
                      - (1/2) sum_{k in J, l not in J} m_k m_l delta_kl^3 (w_k z_kl + z_k w_kl) = 0;
  (Dkl)  differences of two body equations, with z_kl as one term:
         z_kl - sum_{j != k} m_j delta_kj^3 z_kj + sum_{j != l} m_j delta_lj^3 z_lj = 0 (and in w);
  (UI)   U - I: sum m_k m_l delta_kl - sum m_k z_k w_k = 0.
A term's exponent is the sum of the exponents of its factors; its leading coefficient the product of theirs.
The initial form of an identity is used only if its argmin set is the same at every point of the cell (checked by LPs).
Usage: tsec.py N CLASSES_JSON IDX CELLS.jsonl OUT.jsonl [--prime P] [--seed S] [--only i,j,...]"""
import itertools, json, random, sys, os
sys.path.insert(0, '.')
import tengine as T
import texact as X
import tinit as I


def tree_from_json(n, tj):
    t = T.Tree(n)
    t.children = {int(a): list(b) for a, b in tj['children'].items()}
    t.parent = {}
    for a, ch in t.children.items():
        for c in ch:
            t.parent[c] = a
    t.root = tj['root']
    t.leaf = {int(a): b for a, b in tj['leaf'].items()}
    t.next_id = max([n + 1] + [a + 1 for a in t.children])
    return t


def cell_lp(D, zt, wt, argmin):
    """The LP of the relatively open cell: base constraints and, for each identity in argmin, the exact argmin."""
    n = D.n
    L0 = T.base_lp(D, zt, wt, list(range(n + 1)))
    ids = {repr(tuple(x[0]) if isinstance(x[0], (list, tuple)) else x[0]): x for x in X.identities(D, zt, wt, L0)}
    rows = []
    for name, labs in argmin:
        key = repr(tuple(tuple(a) if isinstance(a, list) else a for a in name))
        nm, labels, terms, forced = ids[key]
        labs_t = [tuple(l) for l in labs]
        S = [labels.index(l) for l in labs_t]
        rows += X.forced_rows(L0, terms, S)
    return X.sub(L0, rows)


# ---- secondary identities: terms as (exponent form, coefficient-expression builder) ----

def pos_e(L, Tr, V, k, n):
    m = Tr.meet(k, n)
    return None if m is None else {V[m]: 1.0}


def sep_e(L, Tr, V, k, l):
    return {V[Tr.meet(k, l)]: 1.0}


def add(*forms):
    d = {}
    for f in forms:
        for j, c in f.items():
            d[j] = d.get(j, 0.0) + c
    return d


def scale(f, c):
    return {j: c * v for j, v in f.items()}


def secondary(D, zt, wt, L):
    """List of (name, [(exponent form, symbolic term)]) where a symbolic term is a tuple describing the monomial."""
    n = D.n
    out = []
    xe = lambda k, l: {L.zv[zt.meet(k, l)]: 0.5, L.wv[wt.meet(k, l)]: 0.5}
    dl = lambda k, l: scale(xe(k, l), -1.0)                        # exponent of delta_kl
    za = lambda k: pos_e(L, zt, L.zv, k, n)
    wb = lambda k: pos_e(L, wt, L.wv, k, n)
    zs = lambda k, l: sep_e(L, zt, L.zv, k, l)
    ws = lambda k, l: sep_e(L, wt, L.wv, k, l)
    for r in range(1, n):
        for J in itertools.combinations(range(n), r):
            Jc = [j for j in range(n) if j not in J]
            terms = []
            for k in J:
                for l in Jc:
                    if za(k) is not None and wb(l) is not None:
                        terms.append((add(scale(dl(k, l), 3), za(k), wb(l)), ('T1', k, l)))
                    if wb(k) is not None and za(l) is not None:
                        terms.append((add(scale(dl(k, l), 3), wb(k), za(l)), ('T2', k, l)))
            if J[0] == 0 and len(terms) >= 2:
                out.append((('T', J), terms))
            terms = []
            for k in J:
                if za(k) is not None and wb(k) is not None:
                    terms.append((add(za(k), wb(k)), ('V0', k)))
            for k, l in itertools.combinations(J, 2):
                terms.append((dl(k, l), ('V1', k, l)))
            for k in J:
                for l in Jc:
                    if wb(k) is not None:
                        terms.append((add(scale(dl(k, l), 3), wb(k), zs(k, l)), ('V2', k, l)))
                    if za(k) is not None:
                        terms.append((add(scale(dl(k, l), 3), za(k), ws(k, l)), ('V3', k, l)))
            if len(terms) >= 2:
                out.append((('V', J), terms))
    for k, l in itertools.combinations(range(n), 2):
        for colour in 'zw':
            sp = zs if colour == 'z' else ws
            other = ws if colour == 'z' else zs
            Ze = lambda a, b: add(scale(dl(a, b), 3), sp(a, b))     # delta^3 z_ab
            terms = [(sp(k, l), ('D0', colour, k, l))]
            for j in range(n):
                if j != k:
                    terms.append((Ze(k, j), ('D1', colour, k, j)))
                if j != l:
                    terms.append((Ze(l, j), ('D2', colour, l, j)))
            out.append((('D', colour, k, l), terms))
    for colour in 'zw':
        Tr, V = (zt, L.zv) if colour == 'z' else (wt, L.wv)
        pe = za if colour == 'z' else wb
        sp = zs if colour == 'z' else ws
        for r in range(2, n - 1):
            for J in itertools.combinations(range(n), r):
                Jc = [j for j in range(n) if j not in J]
                terms = []
                for i in J:
                    if pe(i) is not None:
                        terms.append((pe(i), ('SP', colour, i)))
                for i in J:
                    for j in Jc:
                        terms.append((add(scale(dl(i, j), 3), sp(i, j)), ('SC', colour, i, j)))
                out.append((('S', colour, J), terms))
    terms = [({}, ('E0',))]
    for k in range(n):
        if za(k) is not None and wb(k) is not None:
            terms.append((add(za(k), wb(k)), ('V0', k)))
    out.append((('Ip',), terms))
    terms = [(dl(k, l), ('U', k, l)) for k, l in itertools.combinations(range(n), 2)]
    for k in range(n):
        if za(k) is not None and wb(k) is not None:
            terms.append((add(za(k), wb(k)), ('Ip', k)))
    out.append((('UI',), terms))
    return out


def term_expr(n, zt_j, wt_j, sym, m):
    """Singular expression of the leading coefficient (with mass factors and signs) of a symbolic term."""
    L = lambda tr, tag, p, q: I.lead(tr, tag, p, q)
    Dv = lambda a, b: f'D{min(a, b)}_{max(a, b)}'
    t = sym[0]
    if t == 'T1':
        k, l = sym[1], sym[2]
        return f'{m[k]}*{m[l]}*{Dv(k, l)}^3*{L(zt_j, "X", k, n)}*{L(wt_j, "Y", l, n)}'
    if t == 'T2':
        k, l = sym[1], sym[2]
        return f'-{m[k]}*{m[l]}*{Dv(k, l)}^3*{L(wt_j, "Y", k, n)}*{L(zt_j, "X", l, n)}'
    if t == 'V0':
        k = sym[1]
        return f'{m[k]}*{L(zt_j, "X", k, n)}*{L(wt_j, "Y", k, n)}'
    if t == 'V1':
        k, l = sym[1], sym[2]
        return f'-{m[k]}*{m[l]}*{Dv(k, l)}'
    if t == 'V2':
        k, l = sym[1], sym[2]
        return f'-(1/2)*{m[k]}*{m[l]}*{Dv(k, l)}^3*{L(wt_j, "Y", k, n)}*{L(zt_j, "X", k, l)}'
    if t == 'V3':
        k, l = sym[1], sym[2]
        return f'-(1/2)*{m[k]}*{m[l]}*{Dv(k, l)}^3*{L(zt_j, "X", k, n)}*{L(wt_j, "Y", k, l)}'
    if t in ('D0', 'D1', 'D2'):
        colour = sym[1]
        tr, tag = (zt_j, 'X') if colour == 'z' else (wt_j, 'Y')
        a, b = sym[2], sym[3]
        if t == 'D0':
            return f'{L(tr, tag, a, b)}'
        sg = '-' if t == 'D1' else ''
        return f'{sg}{m[b]}*{Dv(a, b)}^3*{L(tr, tag, a, b)}'
    if t == 'SP':
        colour, i = sym[1], sym[2]
        tr, tag = (zt_j, 'X') if colour == 'z' else (wt_j, 'Y')
        return f'{m[i]}*{L(tr, tag, i, n)}'
    if t == 'SC':
        colour, i, j = sym[1], sym[2], sym[3]
        tr, tag = (zt_j, 'X') if colour == 'z' else (wt_j, 'Y')
        return f'-{m[i]}*{m[j]}*{Dv(i, j)}^3*{L(tr, tag, i, j)}'
    if t == 'E0':
        return '-E'
    if t == 'U':
        k, l = sym[1], sym[2]
        return f'{m[k]}*{m[l]}*{Dv(k, l)}'
    if t == 'Ip':
        k = sym[1]
        return f'-{m[k]}*{L(zt_j, "X", k, n)}*{L(wt_j, "Y", k, n)}'
    raise ValueError(sym)


def constant_argmin(L, terms, tol=1e-7):
    """The argmin set if it is the same on the whole (relatively open) cell, else None."""
    ok, val, sol = L.solve()
    if not ok or val <= T.TOL:
        return None
    vals = []
    for f, _ in terms:
        vals.append(sum(c * sol[j] for j, c in f.items()))
    mn = min(vals)
    S = [i for i, v in enumerate(vals) if abs(v - mn) < tol]
    if len(S) < 2:
        return 'single'
    i0 = S[0]
    s = L.ns
    for k in range(len(terms)):
        if k == i0:
            continue
        d = add(terms[k][0], scale(terms[i0][0], -1.0))       # t_k - t_i0
        if k in S:
            # must be identically zero on the cell: no point with d >= s or d <= -s
            for sg in (1.0, -1.0):
                dd = dict(scale(d, sg))
                dd[s] = dd.get(s, 0.0) - 1.0
                if T.feasible(X.sub(L, [(dd, 0.0, None)]))[0]:
                    return None
        else:
            # must be positive on the whole open cell: no point with d <= 0
            if T.feasible(X.sub(L, [(d, None, 0.0)]))[0]:
                return None
    return S


if __name__ == '__main__':
    n = int(sys.argv[1])
    cls = json.load(open(sys.argv[2]))['classes']
    ci = int(sys.argv[3])
    cells = [json.loads(l) for l in open(sys.argv[4])]
    outp = sys.argv[5]
    prime = int(sys.argv[sys.argv.index('--prime') + 1]) if '--prime' in sys.argv else 32003
    seed = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
    only = [int(a) for a in sys.argv[sys.argv.index('--only') + 1].split(',')] if '--only' in sys.argv else None
    if '--part' in sys.argv:
        pk = int(sys.argv[sys.argv.index('--part') + 1])
        pn = int(sys.argv[sys.argv.index('--nparts') + 1])
        only = [i for i in range(len(cells)) if i % pn == pk]
    rng = random.Random(seed)
    masses = [rng.randrange(2, prime - 1) for _ in range(n)]
    if '--masses' in sys.argv:
        masses = sys.argv[sys.argv.index('--masses') + 1].split(',')
    m = {k: f'({masses[k]})' for k in range(n)}
    D = T.Diagram.from_json(n, cls[ci])
    workdir = os.path.dirname(os.path.abspath(outp))
    res = []
    for ci_, cell in enumerate(cells):
        if only is not None and ci_ not in only:
            continue
        zt, wt = tree_from_json(n, cell['ztree']), tree_from_json(n, cell['wtree'])
        L = cell_lp(D, zt, wt, cell['argmin'])
        v, eqs, sats = I.system(n, cell, masses)
        names = [('D', k, l) for k, l in itertools.combinations(range(n), 2)] + [tuple(map(lambda a: tuple(a) if isinstance(a, list) else a, nm)) for nm, _ in cell['argmin']]
        nsec = nsing = nvar = 0
        for name, terms in secondary(D, zt, wt, L):
            S = constant_argmin(L, terms)
            if S is None:
                nvar += 1
                continue
            if S == 'single':
                nsing += 1
                break
            nsec += 1
            eqs.append('+'.join(term_expr(n, cell['ztree'], cell['wtree'], terms[i][1], m) for i in S).replace('+-', '-'))
            names.append(name)
        if nsing:
            res.append({'cell': ci_, 'dim': -1, 'why': 'single minimal term', 'sumx': cell['sumx']})
            continue
        blk = I.singular_block(ci_, v, eqs, sats, prime)
        tl = os.environ.get('TSEC_TIMEOUT')
        r = {ci_: -1} if '--nosolve' in sys.argv else I.run_batch([blk], workdir, timeout=float(tl) if tl else None)
        res.append({'cell': ci_, 'dim': r.get(ci_), 'nsec': nsec, 'nvar': nvar, 'sumx': cell['sumx'], 'x': cell['x']})
        if '--dump' in sys.argv:
            res[-1]['system'] = {'vars': v, 'eqs': eqs, 'names': [repr(x) for x in names], 'sats': sats}
        print(json.dumps(res[-1]), flush=True)
    with open(outp, 'w') as f:
        for r in res:
            f.write(json.dumps(r) + '\n')
