#!/usr/bin/env python3
"""Referee tests of the enumeration logic of the engine (tengine/texact/treplay), n = 6.
(1) Trees: sequential insertion (tengine.Tree.options) over the 6 bodies, without pruning, must give every rooted tree
    on {0..5, O} with >= 2 children per internal node exactly once (39208 = total partitions of 7 labelled leaves), plus
    the trees with one body at O (6 * 2752), i.e. 55720 distinct trees, with no duplicates. Canonical form: the set of
    clusters (leaf sets of the internal nodes), a body at O being merged with O.
(2) Exact argmin sets: on random complete tree pairs of a class, for every identity of texact.identities with at most
    11 terms, the list produced by texact.exact_argmins must equal the brute-force list of all subsets S (|S| >= 2) for
    which {cell LP, t_i = t_j (i, j in S), t_k > t_i (k not in S)} is feasible.
Usage: test_enum.py CODE_DIR"""
import itertools, json, random, sys
sys.path.insert(0, sys.argv[1])
import tengine as T
import texact as X

n = 6


def canon(t):
    """Clusters of a tree: for each internal node the frozenset of points below it (body at O merged with O)."""
    cl = set()

    def below(v):
        if v not in t.children:
            pts = {p for p, lf in t.leaf.items() if lf == v}
            return frozenset(pts)
        s = frozenset()
        for c in t.children[v]:
            s = s | below(c)
        cl.add(s)
        return s
    below(t.root)
    atO = frozenset(p for p, lf in t.leaf.items() if lf == n and p != n)
    return (frozenset(cl), atO)


def test_trees():
    layer = [T.Tree(n).options(n)[0]]
    for p in range(n):
        layer = [t2 for t in layer for t2 in t.options(p)]
    keys = [canon(t) for t in layer]
    nd = len(set(keys))
    atO = sum(1 for k in set(keys) if k[1])
    print(f'trees: generated {len(layer)}, distinct {nd}, with a body at O {atO}, expected 55720 = 39208 + 6*2752')
    return len(layer) == nd == 55720 and atO == 6 * 2752


def feasible_rows(L0, rows):
    return T.feasible(X.sub(L0, rows))[0]


def brute(L0, extra, terms):
    s = L0.ns
    N = len(terms)
    out = []
    for r in range(2, N + 1):
        for S in itertools.combinations(range(N), r):
            rows = []
            f = S[0]
            for j in range(N):
                if j == f:
                    continue
                d, k = T.lin_sub(terms[j], terms[f])
                if j in S:
                    rows.append((d, -k, -k))
                else:
                    dd = dict(d)
                    dd[s] = dd.get(s, 0.0) - 1.0
                    rows.append((dd, -k, None))
            if feasible_rows(L0, extra + rows):
                out.append(S)
    return sorted(out)


def test_argmins(classes, per_class, seed, maxterms=16):
    """Tree pairs of stored cells (known feasible), base LP plus the forced rows; every branch identity with at most
    maxterms terms: exact_argmins (no extra rows) vs brute force."""
    import glob, os
    import tsec as Sx
    cls = json.load(open(sys.argv[1] + '/n6.json'))['classes']
    r = random.Random(seed)
    tested = mism = 0
    store = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
    for ci in classes:
        D = T.Diagram.from_json(n, cls[ci])
        cl = glob.glob(f'{store}/*/exact6/c{ci}/cells.jsonl')[0]
        cells = [json.loads(l) for l in open(cl)]
        pairs = {}
        for c in cells:
            pairs[json.dumps([c['ztree'], c['wtree']], sort_keys=True)] = c
        keys = sorted(pairs)
        r.shuffle(keys)
        for kk in keys[:per_class]:
            c = pairs[kk]
            zt, wt = Sx.tree_from_json(n, c['ztree']), Sx.tree_from_json(n, c['wtree'])
            L0 = T.base_lp(D, zt, wt, list(range(n + 1)))
            base_extra = []
            branch = []
            for name, labels, terms, forced in X.identities(D, zt, wt, L0):
                if not ((name[0] in ('z', 'w') and len(name[2]) == 1) or name[0] in ('U', 'I')):
                    continue
                if forced is not None:
                    base_extra += X.forced_rows(L0, terms, forced)
                else:
                    branch.append((name, terms))
            for name, terms in branch:
                if len(terms) > maxterms:
                    continue
                st = {'lp': 0}
                a = sorted(S for S, rows in X.exact_argmins(L0, base_extra, terms, st))
                b = brute(L0, base_extra, terms)
                tested += 1
                if a != b:
                    mism += 1
                    print('MISMATCH', ci, name, a, b)
        print(f'class {ci}: {min(per_class, len(keys))} stored tree pairs examined, cumulative instances {tested}', flush=True)
    print(f'exact argmins vs brute force: {tested} identity instances, mismatches {mism}')
    return mism == 0 and tested > 0


if __name__ == '__main__':
    ok1 = test_trees()
    ok2 = test_argmins([63, 124, 171, 30, 128, 131], 4, 1)
    print('RESULT', 'PASS' if ok1 and ok2 else 'FAIL')
