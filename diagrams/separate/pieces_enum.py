"""Independent enumeration of connected pieces: connected labelled diagrams on k bodies satisfying the LOCAL rules
E2, E3, E4, E6, C1, C2, C4, C5 (E1 and E5 are global and are not imposed). Written from the verbal rules, without the
engine's bit tables. Output: classes up to relabelling (S_k only, no colour exchange), with the labelled counts.
Usage: pieces_enum.py K OUT.json"""
import itertools, json, sys, time
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from zwlib import SW

def setup(k):
    pairs = [(a, b) for b in range(k) for a in range(b)]
    pos = {}
    for i, (a, b) in enumerate(pairs):
        pos[(a, b)] = pos[(b, a)] = i
    tri_at = [[] for _ in pairs]
    for a, b, c in itertools.combinations(range(k), 3):
        t = (pos[(a, b)], pos[(a, c)], pos[(b, c)])
        tri_at[max(t)].append(t)
    quad_at = [[] for _ in pairs]
    for s in itertools.combinations(range(k), 4):
        a, b, c, d = s
        for cyc in [(a, b, c, d), (a, b, d, c), (a, c, b, d)]:
            p, q, r, t = cyc
            qq = (pos[(p, q)], pos[(q, r)], pos[(r, t)], pos[(t, p)])
            quad_at[max(qq)].append(qq)
    return pairs, pos, tri_at, quad_at

def tri_good(x, y, z):
    v = (x, y, z)
    if sum(1 for t in v if t == 3) == 2:
        return False                                     # E2
    if x and y and z and not (x == y == z):
        return False                                     # E3
    return True

def quad_good(a, b, c, d):
    if a and b and c and d:
        return a == c and b == d                         # E6
    return True

def edge_vectors(k):
    pairs, pos, tri_at, quad_at = setup(k)
    m = len(pairs)
    v = [0] * m
    out = []
    def rec(j):
        if j == m:
            out.append(tuple(v)); return
        for val in range(4):
            v[j] = val
            if all(tri_good(v[t[0]], v[t[1]], v[t[2]]) for t in tri_at[j]) and \
               all(quad_good(v[q[0]], v[q[1]], v[q[2]], v[q[3]]) for q in quad_at[j]):
                rec(j + 1)
        v[j] = 0
    rec(0)
    return pairs, pos, out

def comp_of(adj, s, allowed=None):
    C, st = {s}, [s]
    while st:
        u = st.pop()
        for x in adj[u]:
            if x not in C:
                C.add(x); st.append(x)
    return frozenset(C)

def analyse(k, pairs, v):
    adjG = {i: set() for i in range(k)}
    adjZ = {i: set() for i in range(k)}
    adjW = {i: set() for i in range(k)}
    for i, (a, b) in enumerate(pairs):
        t = v[i]
        if t:
            adjG[a].add(b); adjG[b].add(a)
        if t & 1:
            adjZ[a].add(b); adjZ[b].add(a)
        if t & 2:
            adjW[a].add(b); adjW[b].add(a)
    return adjG, adjZ, adjW

def local_edge_ok(k, pairs, pos, v, adjZ, adjW):
    # E4: each zw-edge ab has another z-stroke and another w-stroke at a or b
    for i, (a, b) in enumerate(pairs):
        if v[i] == 3:
            if not ((adjZ[a] - {b}) or (adjZ[b] - {a})):
                return False
            if not ((adjW[a] - {b}) or (adjW[b] - {a})):
                return False
    return True

def circle_sets(k, adjX, adjY):
    """All X-circle sets satisfying C1, C2, C4, C5 for the X-strokes adjX and the other strokes adjY."""
    compY = {i: comp_of(adjY, i) for i in range(k)}
    compX = {i: comp_of(adjX, i) for i in range(k)}
    res = []
    for bits in itertools.product((0, 1), repeat=k):
        C = {i for i in range(k) if bits[i]}
        ok = True
        for i in range(k):                                   # C1
            d = len(adjX[i])
            if (d == 0 and i in C) or (d == 1 and i not in C):
                ok = False; break
        if not ok: continue
        for i in range(k):                                   # C2
            for j in adjY[i]:
                if (i in C) != (j in C):
                    ok = False; break
            if not ok: break
        if not ok: continue
        for l in range(k):                                   # C5
            if l not in C:
                cn = [x for x in adjX[l] if x in C]
                if any(y not in adjX[x] for x, y in itertools.combinations(cn, 2)):
                    ok = False; break
        if not ok: continue
        for i in C:                                          # C4
            if not ((C & compX[i]) - compY[i]):
                ok = False; break
        if ok:
            res.append(frozenset(C))
    return res

def canon(k, pairs, pos, v, cz, cw, perms):
    best = None
    for p in perms:
        nv = [0] * len(pairs)
        for i, (a, b) in enumerate(pairs):
            nv[pos[(p[a], p[b])]] = v[i]
        key = (tuple(nv), tuple(sorted(p[x] for x in cz)), tuple(sorted(p[x] for x in cw)))
        if best is None or key < best:
            best = key
    return best

def main():
    k = int(sys.argv[1]); outp = sys.argv[2]
    t0 = time.time()
    pairs, pos, vecs = edge_vectors(k)
    perms = list(itertools.permutations(range(k)))
    classes = {}
    nlab = 0
    for v in vecs:
        if not any(v): continue
        adjG, adjZ, adjW = analyse(k, pairs, v)
        if len(comp_of(adjG, 0)) != k: continue              # connected
        if not local_edge_ok(k, pairs, pos, v, adjZ, adjW): continue
        CZ = circle_sets(k, adjZ, adjW)
        if not CZ: continue
        CW = circle_sets(k, adjW, adjZ)
        for cz in CZ:
            for cw in CW:
                nlab += 1
                key = canon(k, pairs, pos, v, cz, cw, perms)
                classes[key] = classes.get(key, 0) + 1
    out = []
    for key, cnt in sorted(classes.items()):
        nv, cz, cw = key
        out.append({'edges': {f'{a}{b}': nv[i] for i, (a, b) in enumerate(pairs) if nv[i]},
                    'zcircles': list(cz), 'wcircles': list(cw), 'labelled': cnt})
    json.dump({'k': k, 'labelled': nlab, 'classes': out}, open(outp, 'w'), indent=1)
    print(f'k={k}: {len(vecs)} edge vectors pass E2/E3/E6; {nlab} labelled connected pieces; {len(out)} classes up to '
          f'relabelling ({time.time()-t0:.1f} s)', flush=True)

if __name__ == '__main__':
    main()
