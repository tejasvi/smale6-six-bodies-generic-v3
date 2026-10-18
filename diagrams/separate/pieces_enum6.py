"""Connected 6-body diagrams satisfying ALL rules (local rules plus E1, E5), enumerated independently of the engine
(verbal rules from pieces_enum.py), canonicalized under S_6 x colour exchange with numpy.
Usage: pieces_enum6.py OUT.json"""
import itertools, json, sys, time
import numpy as np
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from pieces_enum import edge_vectors, analyse, comp_of, local_edge_ok, circle_sets

def main():
    outp = sys.argv[1]
    k = 6
    t0 = time.time()
    pairs, pos, vecs = edge_vectors(k)
    t1 = time.time()
    rows = []
    for v in vecs:
        nz = sum(1 for x in v if x & 1); nw = sum(1 for x in v if x & 2); nzw = sum(1 for x in v if x == 3)
        if nz == 0 or nw == 0 or nzw == 1:          # E1, E5
            continue
        adjG, adjZ, adjW = analyse(k, pairs, v)
        if len(comp_of(adjG, 0)) != k:
            continue
        if not local_edge_ok(k, pairs, pos, v, adjZ, adjW):
            continue
        CZ = circle_sets(k, adjZ, adjW)
        if not CZ: continue
        CW = circle_sets(k, adjW, adjZ)
        for cz in CZ:
            for cw in CW:
                rows.append((v, cz, cw))
    t2 = time.time()
    m = len(pairs); n = k
    E = np.array([r[0] for r in rows], dtype=np.int64)
    CZa = np.array([[1 if i in r[1] else 0 for i in range(n)] for r in rows], dtype=np.int64)
    CWa = np.array([[1 if i in r[2] else 0 for i in range(n)] for r in rows], dtype=np.int64)
    sw = np.array([0, 2, 1, 3], dtype=np.int64)
    w4 = 4 ** np.arange(m, dtype=np.int64)[::-1]
    w2 = 2 ** np.arange(n, dtype=np.int64)[::-1]
    def key(Ev, Cz, Cw):
        return ((Ev * w4).sum(1) << 12) + ((Cz * w2).sum(1) << 6) + (Cw * w2).sum(1)
    best = None
    for p in itertools.permutations(range(n)):
        idx = np.empty(m, dtype=np.int64)
        for i, (a, b) in enumerate(pairs):
            idx[pos[(p[a], p[b])]] = i
        pinv = np.empty(n, dtype=np.int64)
        for q in range(n):
            pinv[p[q]] = q
        Ev = E[:, idx]; Cz = CZa[:, pinv]; Cw = CWa[:, pinv]
        kk = np.minimum(key(Ev, Cz, Cw), key(sw[Ev], Cw, Cz))
        best = kk if best is None else np.minimum(best, kk)
    cls, counts = np.unique(best, return_counts=True)
    reps = []
    for c, cnt in zip(cls.tolist(), counts.tolist()):
        cw = c & 63; cz = (c >> 6) & 63; ev = c >> 12
        vv = [(ev // (4 ** (m - 1 - i))) % 4 for i in range(m)]
        reps.append({'edges': {f'{a}{b}': vv[i] for i, (a, b) in enumerate(pairs) if vv[i]},
                     'zcircles': [q for q in range(n) if (cz >> (n - 1 - q)) & 1],
                     'wcircles': [q for q in range(n) if (cw >> (n - 1 - q)) & 1], 'labelled': cnt})
    json.dump({'n': 6, 'labelled': len(rows), 'classes': reps}, open(outp, 'w'), indent=1)
    print(f'{len(vecs)} edge vectors ({t1-t0:.0f} s); {len(rows)} labelled connected diagrams ({t2-t1:.0f} s); '
          f'{len(reps)} classes ({time.time()-t2:.0f} s)', flush=True)

if __name__ == '__main__':
    main()
