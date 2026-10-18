#!/usr/bin/env python3
"""Per-cell data of the 22 open cells (read-only use of the engine's cell files): x on the K4, x on the cross pairs,
exponents b_k of the K4 bodies relative to the w-origin, and whether the position term is in the argmin of each K4
w-equation (b_k = 2 - 4x on the whole cell).  Usage: cells_table.py > certificates/cells_22.txt"""
import json, os
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results') + '/'
SETS = [(124, ROOT + 'exact6/c124/cells.jsonl', [0, 16, 17, 30, 46, 83, 105, 109, 110, 111, 121], [1, 2, 3, 4], [0, 5]),
        (143, ROOT + 'exact6/c143/cells.jsonl', [3, 13, 14, 23, 29, 35, 47, 53, 59, 65, 71], [1, 2, 3, 5], [0, 4])]
for cls, path, cells, K, W in SETS:
    L = [json.loads(l) for l in open(path)]
    for c in cells:
        d = L[c]
        wt, hw, x = d['wtree'], d['hw'], d['x']
        ch = {int(a): b for a, b in wt['children'].items()}
        leaf = {int(a): b for a, b in wt['leaf'].items()}
        par = {y: a for a, b in ch.items() for y in b}
        def anc(v):
            out = [v]
            while v in par:
                v = par[v]
                out.append(v)
            return out
        def meet(p, q):
            if leaf[p] == leaf[q]:
                return None
            A, S = anc(leaf[p]), set(anc(leaf[q]))
            return next(w for w in A if w in S)
        bk = {k: (None if meet(k, 6) is None else hw[str(meet(k, 6))]) for k in K}
        xk = sorted(set(x['%d%d' % (min(k, l), max(k, l))] for k in K for l in K if k < l))
        xc = sorted(set(x['%d%d' % (min(j, k), max(j, k))] for j in W for k in K
                        if not (cls == 143 and k == 5)))
        pos = all(['pos', k] in labs for name, labs in d['argmin'] if name[0] == 'w' and name[1] == 'S'
                  and len(name[2]) == 1 and name[2][0] in K and not (cls == 143 and name[2][0] == 5)
                  for k in [name[2][0]]) if True else None
        posk = [name[2][0] for name, labs in d['argmin'] if name[0] == 'w' and name[1] == 'S' and len(name[2]) == 1
                and name[2][0] in K and ['pos', name[2][0]] in labs]
        print('class %d cell %3d sumx %5.2f | x(K4) %s x(cross) %s | b_k(K4, engine labels) %s | pos in argmin of w-eq of %s'
              % (cls, c, d['sumx'], xk, xc, bk, posk))
