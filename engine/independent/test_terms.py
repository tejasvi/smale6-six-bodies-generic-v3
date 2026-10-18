#!/usr/bin/env python3
"""Referee test of the engine's own term generators (tsec.secondary + tsec.term_expr, tinit.system), n = 6.
(1) Value test: complex solutions of the normalized equations (Newton), star trees (every point a child of the root,
    O = child 0), so that every 'leading coefficient' expression of the engine equals the exact value of its term
    (X_root_{k+1} = z_k, Y_root_{k+1} = w_k, D = delta, E = U). Then the sum of ALL terms of every identity must vanish.
    tinit.system is tested the same way with a fake cell whose argmin sets are all terms.
(2) Exponent test: on random trees, the exponent form attached by the engine to each term must equal the sum of the
    exponents of the factors of its coefficient expression (m: 0, E: 0, D_kl: -x_kl, a lead (A-B) of node v: height v).
Usage: test_terms.py CODE_DIR"""
import itertools, json, random, re, sys
import numpy as np
sys.path.insert(0, sys.argv[1])
import tengine as T
import texact as X
import tinit as I
import tsec as S

n = 6
P = list(itertools.combinations(range(n), 2))
rng = np.random.default_rng(11)


def solve(m, tries=400):
    N = 2 * n + len(P)
    idx = {p: i for i, p in enumerate(P)}

    def F(u):
        z, w, d = u[:n], u[n:2 * n], u[2 * n:]
        out = []
        for k in range(n):
            out.append(z[k] - sum(m[l] * d[idx[(min(k, l), max(k, l))]] ** 3 * (z[k] - z[l]) for l in range(n) if l != k))
        for k in range(n):
            out.append(w[k] - sum(m[l] * d[idx[(min(k, l), max(k, l))]] ** 3 * (w[k] - w[l]) for l in range(n) if l != k))
        for i, (k, l) in enumerate(P):
            out.append(d[i] ** 2 * (z[k] - z[l]) * (w[k] - w[l]) - 1)
        return np.array(out)

    def J(u, h=1e-7):
        f0 = F(u)
        Jm = np.zeros((N, N), dtype=complex)
        for i in range(N):
            e = np.zeros(N, dtype=complex)
            e[i] = h
            Jm[:, i] = (F(u + e) - f0) / h
        return Jm
    sols = []
    for _ in range(tries):
        u = rng.normal(size=N) + 1j * rng.normal(size=N)
        for it in range(100):
            f = F(u)
            if np.linalg.norm(f) < 1e-13:
                break
            u = u + np.linalg.lstsq(J(u), -f, rcond=None)[0]
        if np.linalg.norm(F(u)) < 1e-11:
            sols.append(u)
        if len(sols) >= 3:
            break
    return sols


def star():
    t = T.Tree(n)
    root = n + 1
    t.children = {root: [n] + list(range(n))}
    t.parent = {c: root for c in t.children[root]}
    t.root = root
    t.leaf = {p: p for p in range(n + 1)}
    t.next_id = root + 1
    return t


def evaluate(expr, env):
    e = expr.replace('^', '**')
    return eval(e, {}, env)


def value_test():
    m = [float(x) for x in rng.uniform(0.5, 3.0, size=n)]
    sols = solve(m)
    print(f'value test: {len(sols)} complex solutions at masses {np.round(m, 3).tolist()}')
    zt, wt = star(), star()
    cls = json.load(open(sys.argv[1] + '/n6.json'))['classes']
    D = T.Diagram.from_json(n, cls[0])
    L = T.base_lp(D, zt, wt, list(range(n + 1)))
    worst = {}
    zj, wj = X.tree_json(zt), X.tree_json(wt)
    root = n + 1
    msym = {k: f'({m[k]!r})' for k in range(n)}
    for u in sols:
        z, w, d = u[:n], u[n:2 * n], u[2 * n:]
        env = {}
        for k in range(n):
            env[f'X{root}_{k + 1}'] = z[k]
            env[f'Y{root}_{k + 1}'] = w[k]
        for i, (k, l) in enumerate(P):
            env[f'D{k}_{l}'] = d[i]
        env['E'] = sum(m[k] * m[l] * d[i] for i, (k, l) in enumerate(P))
        # secondary identities: sum of all terms
        for name, terms in S.secondary(D, zt, wt, L):
            v = sum(evaluate(S.term_expr(n, zj, wj, sym, msym), env) for _, sym in terms)
            key = name[0] if name[0] != 'S' else 'S2'
            worst[key] = max(worst.get(key, 0.0), abs(v))
        # primary identities of tinit.system with argmin = all terms
        ids = X.identities(D, zt, wt, L)
        cell = {'ztree': zj, 'wtree': wj, 'argmin': [[list(nm), [list(lb) for lb in labels]] for nm, labels, _, _ in ids]}
        vars_, eqs, sats = I.system(n, cell, [repr(x) for x in m])
        names = ['Dkl'] * len(P) + [('S1' if nm[0] in 'zw' and len(nm[2]) == 1 else 'S' + nm[0] if nm[0] in 'zw' else nm[0])
                                    for nm, _, _, _ in ids]
        for nm, e in zip(names, eqs):
            v = evaluate(e, env)
            worst['tinit_' + nm] = max(worst.get('tinit_' + nm, 0.0), abs(v))
    print('  largest |sum of all terms| by identity type:', {k: f'{v:.1e}' for k, v in sorted(worst.items())})
    return max(worst.values())


FACT = re.compile(r'\(m\d\)|\(-?[0-9.e+-]+\)|D(\d)_(\d)(?:\^(\d))?|\((0|[XY]\d+_\d+)-(0|[XY]\d+_\d+)\)|E|\(1/2\)')


def exp_of_expr(expr, zt, wt, L):
    """Exponent form of a coefficient expression from its factors."""
    form = {}
    s = expr.lstrip('-')
    pos = 0
    for mm in FACT.finditer(s):
        tok = mm.group(0)
        if tok.startswith('D'):
            k, l, p = int(mm.group(1)), int(mm.group(2)), int(mm.group(3) or 1)
            for j, c in T.xform(None, zt, wt, L, k, l).items():
                form[j] = form.get(j, 0.0) - p * c
        elif tok.startswith('(') and ('X' in tok or 'Y' in tok):
            a, b = mm.group(4), mm.group(5)
            v = a if a != '0' else b
            tag, node = v[0], int(v[1:].split('_')[0])
            j = L.zv[node] if tag == 'X' else L.wv[node]
            form[j] = form.get(j, 0.0) + 1.0
    return {j: c for j, c in form.items() if abs(c) > 1e-12}


def random_tree(r):
    t = T.Tree(n).options(n)[0]
    for p in range(n):
        t = r.choice(t.options(p))
    return t


def exponent_test(trials=300):
    r = random.Random(5)
    cls = json.load(open(sys.argv[1] + '/n6.json'))['classes']
    D = T.Diagram.from_json(n, cls[0])
    bad = 0
    nterms = 0
    m = {k: f'(m{k})' for k in range(n)}
    for _ in range(trials):
        zt, wt = random_tree(r), random_tree(r)
        L = T.base_lp(D, zt, wt, list(range(n + 1)))
        if L is None:
            continue
        zj, wj = X.tree_json(zt), X.tree_json(wt)
        for name, terms in S.secondary(D, zt, wt, L):
            for f, sym in terms:
                e = S.term_expr(n, zj, wj, sym, m)
                g = exp_of_expr(e, zt, wt, L)
                ff = {j: c for j, c in f.items() if abs(c) > 1e-12}
                nterms += 1
                if set(g) != set(ff) or any(abs(g[j] - ff[j]) > 1e-12 for j in g):
                    bad += 1
                    if bad < 5:
                        print('MISMATCH', name, sym, e, ff, g)
    print(f'exponent test: {nterms} terms on {trials} random tree pairs, mismatches {bad}')
    return bad


if __name__ == '__main__':
    w = value_test()
    b = exponent_test()
    print('RESULT', 'PASS' if w < 1e-9 and b == 0 else 'FAIL')
