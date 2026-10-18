#!/usr/bin/env python3
"""Relaxed excess of every maximal zw-clique (r >= 3) of each class.
dim L_c = [clique circled in colour c] + #(bodies of K with a c-stroke leaving K); d_c = max(dim L_c - 1, 0)
(the sum rule sum_t m_t F^c_t = 0 removes one direction). excess = 1 if d_z = d_w = 0, else 2 - d_z - d_w.
'single' = uncircled in a colour, exactly one forced body, with exactly one outside stroke: impossible at positive
masses (its forcing is one nonzero term and must vanish)."""
import json, itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cliques as CQ

def excess(c):
    out = []
    for it in CQ.info(c):
        if it['kind'] != 'zw':
            continue
        K = it['K']
        zs = {(int(k[0]), int(k[1])) for k, v in c['edges'].items() if v & 1}
        ws = {(int(k[0]), int(k[1])) for k, v in c['edges'].items() if v & 2}
        cz = 1 if it['zcirc'] else 0
        cw = 1 if it['wcirc'] else 0
        Lz = cz + len(it['zforced'])
        Lw = cw + len(it['wforced'])
        dz, dw = max(Lz - 1, 0), max(Lw - 1, 0)
        single = False
        for col, cc_, forced in (('z', cz, it['zforced']), ('w', cw, it['wforced'])):
            if cc_ == 0 and len(forced) == 1:
                t = forced[0]
                strokes = zs if col == 'z' else ws
                outs = [e for e in strokes if t in e and (set(e) - set(K))]
                if len(outs) == 1:
                    single = True
        ex = 1 if (dz == 0 and dw == 0) else 2 - dz - dw
        out.append({'K': K, 'r': len(K), 'Lz': Lz, 'Lw': Lw, 'dz': dz, 'dw': dw, 'excess': ex, 'single': single})
    return out

if __name__ == '__main__':
    dom = set(map(int, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'dom_classes.txt')).read().split()))
    killed = []
    for i, c in enumerate(CQ.cls):
        ex = excess(c)
        if not ex:
            continue
        k = any(e['excess'] >= 1 or e['single'] for e in ex)
        if k:
            killed.append(i)
        print(i, 'CC' + str(CQ.ours2cc.get(i, '-')), 'dom' if i in dom else '   ', 'KILLED' if k else '      ', ex)
    print('classes with a zw-clique of positive excess or single forcing:', len(killed))
    print('among the 85 dom classes:', len([i for i in killed if i in dom]), sorted(i for i in killed if i in dom))
