#!/usr/bin/env python3
"""zw-diagram enumeration for n bodies with the rule set of the n = 5 Lean development
(CC5Full/Theory/Types/Enum.lean, `okR`): edge rules E1-E6 and circle rules C1, C2, C4, C5 in both colours.

A labelled diagram: an edge value per pair (0 none, 1 z-stroke, 2 w-stroke, 3 zw-edge) and the circle masks cz, cw.
The triangle and 4-cycle rules are the tables triTab, quadTab of Enum.lean (both are symmetric, so the orientation of a
triangle or a 4-cycle does not matter). Classes are orbits under relabelling (S_n) and the exchange of the colours.

Usage: zwenum.py N [--out FILE.json]
"""
import itertools, json, sys, time

TRI = 9301926778534592511
QUAD = 65640695185967659268242446690056340963675207442853364191111911264718159871999


def tri_ok(x, y, z):
    return (TRI >> (x + 4 * y + 16 * z)) & 1


def quad_ok(a, b, c, d):
    return (QUAD >> (a + 4 * b + 16 * c + 64 * d)) & 1


def setup(n):
    pairs = [(a, b) for b in range(n) for a in range(b)]           # (0,1),(0,2),(1,2),(0,3),... : triangles close early
    pos = {}
    for i, (a, b) in enumerate(pairs):
        pos[(a, b)] = pos[(b, a)] = i
    tris = []
    for a, b, c in itertools.combinations(range(n), 3):
        t = (pos[(a, b)], pos[(a, c)], pos[(b, c)])
        tris.append(t)
    quads = []
    for s in itertools.combinations(range(n), 4):
        a, b, c, d = s
        for cyc in [(a, b, c, d), (a, b, d, c), (a, c, b, d)]:      # the three 4-cycles on four vertices
            p, q, r, t = cyc
            quads.append((pos[(p, q)], pos[(q, r)], pos[(r, t)], pos[(t, p)]))
    m = len(pairs)
    tri_at = [[] for _ in range(m)]
    for t in tris:
        tri_at[max(t)].append(t)
    quad_at = [[] for _ in range(m)]
    for q in quads:
        quad_at[max(q)].append(q)
    adj = [0] * m                                                   # positions sharing a body with position i
    for i, (a, b) in enumerate(pairs):
        for j, (c, d) in enumerate(pairs):
            if j != i and len({a, b} & {c, d}) == 1:
                adj[i] |= 1 << j
    return pairs, pos, tri_at, quad_at, adj


def edge_assignments(n, pairs, tri_at, quad_at):
    """All edge-value vectors passing the triangle (E2, E3) and 4-cycle (E6) rules, by a pruned depth-first search."""
    m = len(pairs)
    v = [0] * m
    out = []

    def rec(j):
        if j == m:
            out.append(tuple(v))
            return
        for val in range(4):
            v[j] = val
            if all(tri_ok(v[t[0]], v[t[1]], v[t[2]]) for t in tri_at[j]) and \
               all(quad_ok(v[q[0]], v[q[1]], v[q[2]], v[q[3]]) for q in quad_at[j]):
                rec(j + 1)
        v[j] = 0

    rec(0)
    return out


def masks(v):
    mz = mw = 0
    for i, x in enumerate(v):
        if x & 1:
            mz |= 1 << i
        if x & 2:
            mw |= 1 << i
    return mz, mw


def popcount(x):
    return bin(x).count('1')


def edge_global(mz, mw, adj, m):
    """E1 (a stroke of each colour), E5 (not exactly one zw-edge), E4 (each zw-edge shares a body with another stroke of
    each colour)."""
    if mz == 0 or mw == 0:
        return False
    zw = mz & mw
    if popcount(zw) == 1:
        return False
    for i in range(m):
        if (zw >> i) & 1:
            if (mz & adj[i]) == 0 or (mw & adj[i]) == 0:
                return False
    return True


def neighbours(M, k, pairs):
    s = 0
    for i, (a, b) in enumerate(pairs):
        if (M >> i) & 1:
            if a == k:
                s |= 1 << b
            elif b == k:
                s |= 1 << a
    return s


def component(M, k, pairs, n):
    comp = 1 << k
    changed = True
    while changed:
        changed = False
        for i, (a, b) in enumerate(pairs):
            if (M >> i) & 1:
                ia, ib = (comp >> a) & 1, (comp >> b) & 1
                if ia != ib:
                    comp |= (1 << a) | (1 << b)
                    changed = True
    return comp


def cut(C, pairs):
    s = 0
    for i, (a, b) in enumerate(pairs):
        if ((C >> a) & 1) != ((C >> b) & 1):
            s |= 1 << i
    return s


def pin(Q, pairs):
    s = 0
    for i, (a, b) in enumerate(pairs):
        if (Q >> a) & 1 and (Q >> b) & 1:
            s |= 1 << i
    return s


def colour_rules(MX, MY, C, pairs, n):
    """C1 (no stroke: no circle; one stroke: a circle), C2 (no stroke of the other colour is cut by the circles),
    C5 (the circled neighbours of an uncircled body are pairwise joined), C4 (for a circled body k with the component K:
    the circled bodies of K are not all in the component of k for the other colour)."""
    for k in range(n):
        nb = neighbours(MX, k, pairs)
        b = (C >> k) & 1
        if nb == 0 and b:
            return False
        if nb != 0 and popcount(nb) == 1 and not b:
            return False
    if MY & cut(C, pairs):
        return False
    full = (1 << len(pairs)) - 1
    for l in range(n):
        if not (C >> l) & 1:
            if pin(neighbours(MX, l, pairs) & C, pairs) & (MX ^ full):
                return False
    for k in range(n):
        if (C >> k) & 1:
            K = component(MX, k, pairs, n)
            KY = component(MY, k, pairs, n)
            if (C & K) & ~KY == 0:
                return False
    return True


def circle_candidates(MX, pairs, n):
    choices = []
    for k in range(n):
        nb = neighbours(MX, k, pairs)
        if nb == 0:
            choices.append([0])
        elif popcount(nb) == 1:
            choices.append([1])
        else:
            choices.append([0, 1])
    for bits in itertools.product(*choices):
        yield sum(b << k for k, b in enumerate(bits))


def enumerate_diagrams(n):
    pairs, pos, tri_at, quad_at, adj = setup(n)
    m = len(pairs)
    t0 = time.time()
    edges = edge_assignments(n, pairs, tri_at, quad_at)
    t1 = time.time()
    out = []
    for v in edges:
        mz, mw = masks(v)
        if not edge_global(mz, mw, adj, m):
            continue
        cz_list = [C for C in circle_candidates(mz, pairs, n) if colour_rules(mz, mw, C, pairs, n)]
        if not cz_list:
            continue
        cw_list = [C for C in circle_candidates(mw, pairs, n) if colour_rules(mw, mz, C, pairs, n)]
        for cz in cz_list:
            for cw in cw_list:
                out.append((v, cz, cw))
    t2 = time.time()
    return pairs, pos, edges, out, (t1 - t0, t2 - t1)


def canonical(d, n, pairs, pos, perms):
    """The least key of the orbit of the labelled diagram d under S_n and the exchange of the colours."""
    v, cz, cw = d
    best = None
    sw = (0, 2, 1, 3)
    for p in perms:
        # body k goes to p[k]
        nv = [0] * len(pairs)
        for i, (a, b) in enumerate(pairs):
            nv[pos[(p[a], p[b])]] = v[i]
        ncz = sum(((cz >> k) & 1) << p[k] for k in range(n))
        ncw = sum(((cw >> k) & 1) << p[k] for k in range(n))
        for swap in (False, True):
            if swap:
                key = (tuple(sw[x] for x in nv), ncw, ncz)
            else:
                key = (tuple(nv), ncz, ncw)
            if best is None or key < best:
                best = key
    return best


def main():
    n = int(sys.argv[1])
    outf = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
    pairs, pos, edges, diags, (te, tc) = enumerate_diagrams(n)
    print(f'n={n}: {len(pairs)} pairs; {len(edges)} edge vectors pass E2/E3/E6 ({te:.1f} s); '
          f'{len(diags)} labelled diagrams pass all rules ({tc:.1f} s)', flush=True)
    perms = list(itertools.permutations(range(n)))
    classes = {}
    t0 = time.time()
    for d in diags:
        c = canonical(d, n, pairs, pos, perms)
        classes.setdefault(c, 0)
        classes[c] += 1
    print(f'{len(classes)} classes under S_{n} x colour exchange ({time.time() - t0:.1f} s)', flush=True)
    if outf:
        rep = []
        for c, cnt in sorted(classes.items()):
            v, cz, cw = c
            rep.append({'edges': {f'{a}{b}': v[i] for i, (a, b) in enumerate(pairs) if v[i]},
                        'zcircles': [k for k in range(n) if (cz >> k) & 1],
                        'wcircles': [k for k in range(n) if (cw >> k) & 1], 'labelled': cnt})
        json.dump({'n': n, 'labelled': len(diags), 'classes': rep}, open(outf, 'w'), indent=1)
        print('wrote', outf)


if __name__ == '__main__':
    main()
