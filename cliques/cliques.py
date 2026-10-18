#!/usr/bin/env python3
"""Diagram-level clique structures: maximal zw-cliques (size >= 3) and maximal one-colour stroke cliques (size >= 3,
not all zw), with circles and outside strokes (forcing) per colour."""
import json, itertools, os, sys
E = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'diagrams') + '/'
cls = json.load(open(E + 'n6.json'))['classes']
cc = json.load(open(E + 'cc_compare.json'))
ours2cc = {r['ours']: r['cc'] for r in cc['per_cc']}
n = 6

def maxcliques(adj):
    out = []
    for r in range(n, 2, -1):
        for K in itertools.combinations(range(n), r):
            if all((a, b) in adj for a, b in itertools.combinations(K, 2)):
                if not any(set(K) <= set(L) for L in out):
                    out.append(K)
    return out

def info(c):
    zs = {(int(k[0]), int(k[1])) for k, v in c['edges'].items() if v & 1}
    ws = {(int(k[0]), int(k[1])) for k, v in c['edges'].items() if v & 2}
    zc, wc = set(c['zcircles']), set(c['wcircles'])
    zw = zs & ws
    res = []
    for kind, adj in (('zw', zw), ('z', zs), ('w', ws)):
        for K in maxcliques(adj):
            if kind != 'zw' and all((a, b) in zw for a, b in itertools.combinations(K, 2)):
                continue
            fz = sorted({t for t in K for e in zs if t in e and (set(e) - set(K))})
            fw = sorted({t for t in K for e in ws if t in e and (set(e) - set(K))})
            cz = sorted(set(K) & zc)
            cw = sorted(set(K) & wc)
            res.append({'kind': kind, 'K': K, 'zforced': fz, 'wforced': fw, 'zcirc': cz, 'wcirc': cw})
    return res

if __name__ == '__main__':
    for i, c in enumerate(cls):
        print(i, 'CC' + str(ours2cc.get(i, '-')), json.dumps(info(c)))
