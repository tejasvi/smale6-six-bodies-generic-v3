"""Shared helpers: diagrams as (edge dict {(a,b): t}, zcircles set, wcircles set), t in {1: z, 2: w, 3: zw}.
The rules E1-E6, C1, C2, C4, C5 are re-implemented here from their verbal statements (not from the bit tables),
so that agreement with the engine's output is an independent check."""
import itertools, json

Z, W, ZW = 1, 2, 3
SW = {0: 0, 1: 2, 2: 1, 3: 3}


def load(path):
    d = json.load(open(path))
    out = []
    for c in d['classes']:
        E = {}
        for k, v in c['edges'].items():
            a, b = int(k[0]), int(k[1])
            E[(min(a, b), max(a, b))] = v
        out.append((E, frozenset(c['zcircles']), frozenset(c['wcircles']), c['labelled']))
    return d['n'], out


def val(E, a, b):
    return E.get((min(a, b), max(a, b)), 0)


def strokes(E, bit):
    return {e for e, t in E.items() if t & bit}


def nbrs(S, k):
    return {b if a == k else a for (a, b) in S if k in (a, b)}


def comp(S, k, n):
    C, st = {k}, [k]
    while st:
        u = st.pop()
        for v in nbrs(S, u):
            if v not in C:
                C.add(v)
                st.append(v)
    return frozenset(C)


def comps(S, n):
    seen, out = set(), []
    for k in range(n):
        if k not in seen:
            C = comp(S, k, n)
            seen |= C
            out.append(C)
    return out


def rules_ok(n, E, cz, cw, why=False):
    fails = []
    P = list(itertools.combinations(range(n), 2))
    Sz, Sw = strokes(E, 1), strokes(E, 2)
    zw = {e for e, t in E.items() if t == 3}
    # E1
    if not Sz or not Sw:
        fails.append('E1')
    # E2, E3 (triangles)
    for a, b, c in itertools.combinations(range(n), 3):
        v = (val(E, a, b), val(E, a, c), val(E, b, c))
        if sum(1 for t in v if t == 3) == 2:
            fails.append('E2')
        if all(v) and len(set(v)) > 1:
            fails.append('E3')
    # E4
    for (a, b) in zw:
        others = [(x, y) for (x, y) in P if (x, y) != (a, b) and len({x, y} & {a, b}) == 1]
        if not any(e in Sz for e in others) or not any(e in Sw for e in others):
            fails.append('E4')
    # E5
    if len(zw) == 1:
        fails.append('E5')
    # E6 (4-cycles)
    for q in itertools.combinations(range(n), 4):
        a, b, c, d = q
        for cyc in [(a, b, c, d), (a, b, d, c), (a, c, b, d)]:
            p, qq, r, s = cyc
            v = (val(E, p, qq), val(E, qq, r), val(E, r, s), val(E, s, p))
            if all(v) and not (v[0] == v[2] and v[1] == v[3]):
                fails.append('E6')
    # circle rules per colour
    for (SX, SY, CX, tag) in ((Sz, Sw, cz, 'z'), (Sw, Sz, cw, 'w')):
        for k in range(n):
            d = len(nbrs(SX, k))
            if d == 0 and k in CX:
                fails.append('C1' + tag)
            if d == 1 and k not in CX:
                fails.append('C1' + tag)
        for (a, b) in SY:
            if (a in CX) != (b in CX):
                fails.append('C2' + tag)
        for l in range(n):
            if l not in CX:
                cn = [x for x in nbrs(SX, l) if x in CX]
                for x, y in itertools.combinations(cn, 2):
                    if (min(x, y), max(x, y)) not in SX:
                        fails.append('C5' + tag)
        for k in CX:
            K = comp(SX, k, n)
            KY = comp(SY, k, n)
            if not ((CX & K) - KY):
                fails.append('C4' + tag)
    fails = sorted(set(fails))
    return (not fails, fails) if why else (not fails)


def canon(n, E, cz, cw):
    """Least key of the orbit under S_n x colour exchange (key: sorted tuple representation)."""
    best = None
    for p in itertools.permutations(range(n)):
        for s in (False, True):
            ne = []
            for (a, b), t in E.items():
                x, y = p[a], p[b]
                ne.append((min(x, y), max(x, y), SW[t] if s else t))
            ncz = tuple(sorted(p[k] for k in (cw if s else cz)))
            ncw = tuple(sorted(p[k] for k in (cz if s else cw)))
            key = (tuple(sorted(ne)), ncz, ncw)
            if best is None or key < best:
                best = key
    return best


def show(n, E, cz, cw):
    sym = {1: 'z', 2: 'w', 3: 'zw'}
    es = ' '.join(f'{sym[t]}{a}{b}' for (a, b), t in sorted(E.items()))
    return f'{es} | zc{"".join(map(str, sorted(cz)))} wc{"".join(map(str, sorted(cw)))}'
