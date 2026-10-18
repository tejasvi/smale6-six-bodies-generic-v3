#!/usr/bin/env python3
"""For every local nonpositive engine cell (read-only: results/exact6/c*/cells.jsonl of the supplement):
does it contain a killer clique (Theorem 3.7 / d64 Lemma E)? zw-cliques at the diagram level; uncircled one-colour
cliques from the cell's exact argmin sets of the body equations (cleanliness, forcing and constant of the other colour
are read off the argmin of the other-colour equations of the clique bodies).
Output: per class counts (cells, killed, cells with phi<0 at the interior point, of these killed)."""
import json, os, sys, glob, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cliques as CQ
import cliquemilp as CM
BASE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..') + '/'
n = 6


def one_colour_killer(it, argmin):
    K = list(it['K'])
    col = it['kind']
    oth = 'w' if col == 'z' else 'z'
    if (it['zcirc'] if col == 'z' else it['wcirc']):
        return False
    if (it['wforced'] if col == 'z' else it['zforced']):
        return False
    forced_same = it['zforced'] if col == 'z' else it['wforced']
    dz = max(len(forced_same) - 1, 0)
    am = {}
    for name, labs in argmin:
        if name[0] == oth and name[1] == 'S' and len(name[2]) == 1:
            am[name[2][0]] = [tuple(l) for l in labs]
    kappa = 0
    g = 0
    for t in K:
        if t not in am:
            return False
        labs = am[t]
        internal = [l for l in labs if l[0] == 'cross' and l[2] in K]
        if len(internal) != len(K) - 1:
            return False                  # not clean: the internal terms are not minimal
        if any(l[0] == 'cross' and l[2] not in K for l in labs):
            g += 1
        if ('pos', t) in labs:
            kappa = 1
    dimLw = min(kappa + g, len(K))
    dw = max(dimLw - 1, 0)
    if len(K) == 3:
        ex = 1 if (dz == 0 and dw == 0) else 2 - dz - dw
        return ex >= 1
    return dz == 0 and dw == 0


def phineg(x):
    for a, b in itertools.combinations(range(n), 2):
        s = sum(v for k, v in x.items() if k == f'{a}{b}' or not ({int(k[0]), int(k[1])} & {a, b}))
        if s < -1e-9:
            return True
    return False


if __name__ == '__main__':
    res = {}
    for fpath in sorted(glob.glob(BASE + '*/exact6/c*/cells.jsonl')):
        import re; ci = int(re.search(r'/c(\d+)/cells', fpath).group(1))
        c = CQ.cls[ci]
        zwk = CM.zw_killer(c) is not None
        its = [it for it in CQ.info(c) if it['kind'] in ('z', 'w') and len(it['K']) in (3, 4)]
        tot = kil = neg = negkil = 0
        for line in open(fpath):
            cell = json.loads(line)
            tot += 1
            k = zwk or any(one_colour_killer(it, cell['argmin']) for it in its)
            pn = phineg(cell['x'])
            kil += k
            neg += pn
            negkil += (k and pn)
        r = res.setdefault(ci, [0, 0, 0, 0])
        r[0] += tot; r[1] += kil; r[2] += neg; r[3] += negkil
    tot = [sum(v[i] for v in res.values()) for i in range(4)]
    print('classes', len(res), 'cells', tot[0], 'killed', tot[1], '; cells with phi<0 at the interior point', tot[2],
          'killed', tot[3])
    full = [c for c, v in res.items() if v[0] and v[1] == v[0]]
    fulln = [c for c, v in res.items() if v[2] and v[3] == v[2]]
    print('classes with all local cells killed:', sorted(full))
    print('classes with all local phi<0 cells killed:', sorted(fulln))
    for c in sorted(res):
        print(c, 'CC' + str(CQ.ours2cc.get(c, '-')), res[c])
    json.dump({str(k): v for k, v in res.items()}, open(sys.argv[1], 'w'))
