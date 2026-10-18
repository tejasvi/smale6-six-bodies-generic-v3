"""Theorem 1 check (decomposition into pieces): assemble all n-body diagram classes from connected pieces, and compare
with the engine's nN.json (classes and labelled counts).
Pieces of size k < n: data/pieces_kK.json (classes up to relabelling, all local rules, no E1/E5).
Pieces of size n: the connected classes (all rules), from a file given on the command line.
Usage: assemble.py N CONNECTED_N_JSON ENGINE_N_JSON"""
import sys, json, itertools
from math import factorial
from collections import Counter
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from zwlib import SW, canon, load

def piece_key(c):
    E = {}
    for kk, v in c['edges'].items():
        E[(int(kk[0]), int(kk[1]))] = v
    return (tuple(sorted((a, b, t) for (a, b), t in E.items())), tuple(sorted(c['zcircles'])), tuple(sorted(c['wcircles'])))

def canon_rel(k, key):
    """canonical form under relabelling only"""
    ne, cz, cw = key
    best = None
    for p in itertools.permutations(range(k)):
        e2 = tuple(sorted((min(p[a], p[b]), max(p[a], p[b]), t) for a, b, t in ne))
        k2 = (e2, tuple(sorted(p[x] for x in cz)), tuple(sorted(p[x] for x in cw)))
        if best is None or k2 < best:
            best = k2
    return best

def swap_key(key):
    ne, cz, cw = key
    return (tuple(sorted((a, b, SW[t]) for a, b, t in ne)), cw, cz)

def main():
    n = int(sys.argv[1])
    pieces = {}            # size -> list of (key, labelled count on a fixed k-set, nz, nw, nzw)
    for k in range(2, n):
        d = json.load(open(f'data/pieces_k{k}.json'))
        lst = []
        for c in d['classes']:
            key = canon_rel(k, piece_key(c))
            ne = key[0]
            lst.append((key, c['labelled'], any(t & 1 for *_, t in ne), any(t & 2 for *_, t in ne),
                        sum(1 for *_, t in ne if t == 3)))
        pieces[k] = lst
    # swap map within each size
    swapmap = {}
    for k, lst in pieces.items():
        keys = {p[0] for p in lst}
        for p in lst:
            s = canon_rel(k, swap_key(p[0]))
            assert s in keys, 'swap of a piece is not a piece?'
            swapmap[(k, p[0])] = (k, s)
    info = {(k, p[0]): p for k, lst in pieces.items() for p in lst}
    # multisets of pieces with total size <= n (sizes < n), plus connected n-classes
    allp = [(k, p[0]) for k in sorted(pieces) for p in pieces[k]]
    result = Counter()
    def rec(start, remaining, chosen):
        if chosen:
            hz = any(info[x][2] for x in chosen); hw = any(info[x][3] for x in chosen)
            nzw = sum(info[x][4] for x in chosen)
            if hz and hw and nzw != 1:
                s = n - sum(x[0] for x in chosen)
                ms = tuple(sorted(chosen))
                sw = tuple(sorted(swapmap[x] for x in chosen))
                cls = min(ms, sw)
                # labelled count of this multiset (no swap)
                cnt = Counter(chosen)
                lab = factorial(n) // factorial(s)
                for x, mult in cnt.items():
                    lab //= (factorial(x[0]) ** mult) * factorial(mult)
                    lab *= info[x][1] ** mult
                tot = lab if ms == sw else 2 * lab
                if cls in result:
                    assert result[cls] == tot
                result[cls] = tot
        for i in range(start, len(allp)):
            k = allp[i][0]
            if k <= remaining:
                rec(i, remaining - k, chosen + [allp[i]])
    rec(0, n, [])
    ndisc = len(result)
    labdisc = sum(result.values())
    # connected n-classes
    conn = json.load(open(sys.argv[2]))['classes']
    labconn = sum(c['labelled'] for c in conn)
    eng_n, eng = load(sys.argv[3])
    # engine classes split into connected / not
    from zwlib import comps
    econn = [c for c in eng if len(comps(set(c[0]), n)) == 1]
    print(f'n={n}: assembled disconnected classes {ndisc} (labelled {labdisc}); connected classes given {len(conn)} '
          f'(labelled {labconn}); total {ndisc + len(conn)} classes, {labdisc + labconn} labelled')
    print(f'engine: {len(eng)} classes ({len(econn)} connected, {len(eng)-len(econn)} not), labelled '
          f'{sum(c[3] for c in eng)} ({sum(c[3] for c in econn)} connected)')
    # compare disconnected classes by canonical forms under S_n x swap
    def to_global(ms):
        """realise a multiset of pieces as a labelled n-body diagram and canonicalise under S_n x swap"""
        E, cz, cw = {}, set(), set()
        off = 0
        for (k, key) in ms:
            ne, z, w = key
            for a, b, t in ne:
                E[(a + off, b + off)] = t
            cz |= {x + off for x in z}; cw |= {x + off for x in w}
            off += k
        return canon(n, E, frozenset(cz), frozenset(cw)), (E, cz, cw)
    mine = {}
    for ms, lab in result.items():
        g, _ = to_global(ms)
        mine[g] = lab
    engd = {}
    for (E, cz, cw, lab) in eng:
        if len(comps(set(E), n)) > 1:
            engd[canon(n, E, cz, cw)] = lab
    print('disconnected: assembled == engine (as sets):', set(mine) == set(engd),
          '; labelled counts agree:', all(mine[g] == engd.get(g) for g in mine))
    # connected comparison
    gc = {canon(n, {(int(c2[0]), int(c2[1])): v for c2, v in c['edges'].items()}, frozenset(c['zcircles']),
                frozenset(c['wcircles'])): c['labelled'] for c in conn}
    ec = {canon(n, E, cz, cw): lab for (E, cz, cw, lab) in econn}
    print('connected: given == engine (as sets):', set(gc) == set(ec), '; labelled agree:',
          all(gc[g] == ec.get(g) for g in gc))

if __name__ == '__main__':
    main()
