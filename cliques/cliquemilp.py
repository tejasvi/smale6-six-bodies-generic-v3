#!/usr/bin/env python3
"""Cells not killed by the clique lemmas (OVERDET.md, Theorem 5 and Lemma E of d64), as a MILP over level 1.

For a class, the cliques K (|K| = 3 or 4) of strokes: zw-cliques (diagram level) and one-colour cliques without
circles of their colour (cell level). A clique is a *killer* on a cell if it is clean in both colours and its forcing
pattern has excess >= 1 (|K| = 3: Theorem 5) or is unforced (|K| = 4: E_4, d64 Lemma E). This script adds, for every
such clique, the constraint 'K is not a killer', and asks whether a level-1 cell remains (optionally with phi_kl < 0).

Encoding for an uncircled z-clique K (common x_K, internal w-order e_K = 2 - 4 x_K):
  d_tX = e(W_tX) - e_K  (t in K, X not in K);  clean <=> all d_tX >= 0;
  g_t = 1 => some d_tX = 0 (w-forcing at t);  kappa = 1 => b_t = e_K (common w-constant);
  L^w = span(1 [kappa], e_t [g_t]),  L^z = span(e_t : t has a z-stroke leaving K) (no constant: uncircled);
  d_c = max(dim L^c - 1, 0);  excess = 1 if d_z = d_w = 0 else 2 - d_z - d_w.
'Not a killer' = (some d_tX <= -s) or (clean and kappa + sum g_t >= T_K), with T_K = 3 - d_z (|K| = 3, d_z <= 1),
T_K = 0 if d_z >= 2; for |K| = 4: T_K = 2 - [d_z >= 1]*2 (any forcing beyond the unforced pattern)."""
import itertools, json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ordmilp as OM
import cliques as CQ
import zwexcess as ZX

BIG = OM.BIGM


def clique_list(c):
    """[(kind, K, zforced, wforced, zcirc, wcirc)] for |K| in (3, 4)."""
    out = []
    for it in CQ.info(c):
        if len(it['K']) in (3, 4):
            out.append(it)
    return out


def zw_killer(c):
    """Diagram-level: a zw-clique of size 3 with excess >= 1 or single forcing (Theorem 5), or of size 4 unforced
    (effective, E_4)."""
    for e in ZX.excess(c):
        if e['r'] == 3 and (e['excess'] >= 1 or e['single']):
            return e
        if e['r'] == 4 and e['dz'] == 0 and e['dw'] == 0:
            return e
    return None


def add_not_killer(Mo, H, c, it):
    n = H['n']
    U = H['U']
    s = H['s']
    O = n
    K = list(it['K'])
    col = it['kind']                     # 'z' or 'w': the colour of the strokes
    oth = 'w' if col == 'z' else 'z'
    circ = it['zcirc'] if col == 'z' else it['wcirc']
    if circ:
        return False                     # circled one-colour clique: not an equilibrium clique, no constraint
    forced_same = it['zforced'] if col == 'z' else it['wforced']
    forced_oth = it['wforced'] if col == 'z' else it['zforced']
    if forced_oth:
        return False                     # a stroke of the other colour leaves K: never clean, no constraint
    r = len(K)
    dz = max(len(forced_same) - 1, 0)    # same-colour side (uncircled: no constant)
    t1, t2 = K[0], K[1]
    # e_K in the other colour: -(3 zeta + omega)/2 for col = z (W-terms), -(zeta + 3 omega)/2 for col = w (Z-terms)
    def eterm(t, X):
        Z, W = U['z', t, X], U['w', t, X]
        return {Z: -1.5, W: -0.5} if col == 'z' else {Z: -0.5, W: -1.5}
    eK = eterm(t1, t2)
    outside = [X for X in range(n) if X not in K]
    ncs, hs = [], {}
    yu = Mo.var(0, 1, True)              # unclean branch
    ye = Mo.var(0, 1, True)              # clean with excess <= 0 branch
    Mo.add({yu: 1, ye: 1}, 1, None)
    for t in K:
        for X in outside:
            d = dict(eterm(t, X))
            for j, cf in eK.items():
                d[j] = d.get(j, 0.0) - cf
            nc = Mo.var(0, 1, True)
            ncs.append(nc)
            # nc = 1 => d + s <= 0
            dd = dict(d); dd[s] = dd.get(s, 0.0) + 1.0; dd[nc] = BIG
            Mo.add(dd, None, BIG)
            # ye = 1 => d >= 0
            dd = dict(d); dd[ye] = -BIG
            Mo.add(dd, -BIG, None)
            h = Mo.var(0, 1, True)
            hs[t, X] = h
            # h = 1 => d <= 0
            dd = dict(d); dd[h] = BIG
            Mo.add(dd, None, BIG)
    # yu = 1 => sum nc >= 1
    d = {nc: 1.0 for nc in ncs}; d[yu] = -1.0
    Mo.add(d, 0, None)
    # forcing indicators g_t <= sum_X h_tX
    gs = []
    for t in K:
        g = Mo.var(0, 1, True)
        gs.append(g)
        d = {hs[t, X]: 1.0 for X in outside}; d[g] = -1.0
        Mo.add(d, 0, None)
    # kappa = 1 => position of the other colour of t1 equals e_K (b_t1 = e_K for col = z)
    kap = Mo.var(0, 1, True)
    pos = U[oth, t1, O]
    d = {pos: 1.0}
    for j, cf in eK.items():
        d[j] = d.get(j, 0.0) - cf
    dd = dict(d); dd[kap] = BIG
    Mo.add(dd, None, BIG)                # kappa = 1 => pos - eK <= 0
    if r == 3:
        T = 3 - dz if dz <= 1 else 0
    else:
        T = 2 if dz == 0 else 0
    if T > 0:
        d = {g: 1.0 for g in gs}; d[kap] = 1.0; d[ye] = -float(T)
        Mo.add(d, 0, None)               # ye = 1 => kappa + sum g >= T
    return True


def test_class(n, c, groups, phi=None, time_limit=None):
    if zw_killer(c) is not None:
        return False, None, 'zw-killer'
    Mo, H = OM.build(n, c, groups, phi)
    used = 0
    for it in clique_list(c):
        if it['kind'] in ('z', 'w'):
            if add_not_killer(Mo, H, c, it):
                used += 1
    val, sol, st = Mo.solve({H['s']: 1.0}, time_limit)
    if val is None:
        return None, None, st
    if val > OM.EPS:
        return True, OM.witness(Mo, H, sol), {'slack': round(val, 6), 'cliques_used': used}
    if st != 'ok':
        return None, None, st
    return False, None, {'slack': round(val, 9), 'cliques_used': used}


if __name__ == '__main__':
    n = 6
    cls = json.load(open(OM.E + 'n6.json'))['classes']
    out = sys.argv[1]
    which = [int(a) for a in sys.argv[2].split(',')] if len(sys.argv) > 2 and sys.argv[2] != 'all' else range(len(cls))
    tl = float(sys.argv[3]) if len(sys.argv) > 3 else 1800
    groups = 'T,O,C,M,B,U,I,Ip'.split(',')
    import time, os
    done = set()
    if os.path.exists(out):
        done = {json.loads(l)['class'] for l in open(out)}
    with open(out, 'a') as f:
        for ci in which:
            if ci in done:
                continue
            t = time.time()
            ok, w, info = test_class(n, cls[ci], groups, time_limit=tl)
            f.write(json.dumps({'class': ci, 'survivor': ok, 'info': info, 'time': round(time.time() - t, 1),
                                'x': (w or {}).get('x')}) + '\n')
            f.flush()
