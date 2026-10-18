#!/usr/bin/env python3
"""Data for the Lean checks of Lemma 6.19(a): G with the masses as parameters (grouped by xi-monomials), Gbar = G at
mu0 mod p in the same term order, the cofactors of the identities (*) of gsys.py, and the comparison with the gfan
inputs of the d88 run. Usage: mkdata.py n4|kc OUTDIR GFAN_INPUT"""
import json
import os
import re
import sys

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gsys

P = 65521
MU0 = (1, 2, 3, 30)


def grouped(g, gens):
    """list of (xi-exponent tuple, list of (int coeff, mu-exponent tuple)) in sympy's lex order."""
    Pg = sp.Poly(g, *gens)
    out = []
    for e, c in Pg.terms():
        cp = sp.Poly(sp.expand(c), *gsys.mu)
        out.append((tuple(e), [(int(cc), tuple(me)) for me, cc in cp.terms()]))
    return out


def main():
    kind, outdir, gf = sys.argv[1], sys.argv[2], sys.argv[3]
    os.makedirs(outdir, exist_ok=True)
    res, gens, B = gsys.certify(kind)
    G = [grouped(r['g'], gens) for r in res]
    Gbar = []
    nterms = 0
    for g in G:
        gb = []
        for e, cp in g:
            v = sum(c * MU0[0] ** me[0] * MU0[1] ** me[1] * MU0[2] ** me[2] * MU0[3] ** me[3] for c, me in cp)
            assert v % P != 0, 'coefficient vanishes at mu0 mod p'
            gb.append((v % P, list(e)))
            nterms += 1
        Gbar.append(gb)
    print(kind, len(G), 'polynomials,', nterms, 'xi-terms, all coefficients units at mu0 mod p')
    json.dump(Gbar, open(os.path.join(outdir, '%s_gbar.json' % kind), 'w'))
    # gfan input of the d88 run: letters a.. = gens in order
    txt = open(gf).read()
    body = txt[txt.index('{') + 1:txt.rindex('}')]
    gpolys = [s.strip() for s in body.split(',')]
    assert len(gpolys) == len(G), (len(gpolys), len(G))
    letters = 'abcdefghijklmnopq'
    syms = sp.symbols(' '.join(letters))
    scal = []
    for k, (s, gb) in enumerate(zip(gpolys, Gbar)):
        f = sp.Poly(sp.sympify(s.replace('^', '**'), locals=dict(zip(letters, syms))), *syms)
        fd = {tuple(e): int(c) % P for e, c in f.terms()}
        gd = {tuple(e): c for c, e in gb}
        assert set(fd) == set(gd), k
        e0 = next(iter(gd))
        sc = gd[e0] * pow(fd[e0], P - 2, P) % P
        assert all(gd[e] == sc * fd[e] % P for e in gd), k
        scal.append(sc)
    print('gfan input of the d88 run = Gbar up to unit scalars (term by term)')
    json.dump(dict(G=[[[list(e), [[c, list(me)] for c, me in cp]] for e, cp in g] for g in G],
                   gens=[str(x) for x in gens], v=[str(x) for x in B['v']],
                   cof=[[str(c) for c in r['cof']] + [str(r['c0'])] for r in res],
                   kinds=[str(r['kind']) for r in res], gfan=[ [[list(e), int(c)] for e, c in sp.Poly(sp.sympify(s.replace('^', '**'), locals=dict(zip(letters, syms))), *syms).terms()] for s in gpolys],
                   scal=scal),
              open(os.path.join(outdir, '%s_data.json' % kind), 'w'))


if __name__ == '__main__':
    main()
