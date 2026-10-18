#!/usr/bin/env python3
"""Good-reduction certificate for the 'K4 with centre' system KC (diagram 94), DERIVATION B.5.

Step 1: G1 = generators + identities with Y4 eliminated through body 1 only (69 polynomials).  The tropical
        prevariety of G1 (gfan) and, on every cone meeting {some valuation < 0}, the initial system of G1 over F_p
        (tropcheck.run).
Step 2: G2 = G1 + the same identities with Y4 eliminated through bodies 2 and 3 (101 polynomials, all in the ideal).
        Prev(G2) is contained in Prev(G1); on a cone of Prev(G1) the initial forms of G1 are constant, so only the cones
        that failed in step 1 need G2.  Those are rays, on whose open part every initial form is constant: test the
        initial system of G2 at the ray.
Usage: kc_trop_cert.py mu1 mu2 mu3 mu4 p WORKDIR
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import n4_trop
import tropcheck
import sympy as sp


def main():
    mu = [int(x) for x in sys.argv[1:5]]
    p = int(sys.argv[5])
    wd = sys.argv[6]
    os.makedirs(wd, exist_ok=True)
    out = {'masses': mu, 'p': p}
    for v in (1, 3):
        # support check with symbolic masses for both sets
        musym = sp.symbols('mu1 mu2 mu3 mu4')
        polys, gens = n4_trop.kc_system(list(musym), 'all', variants=v)
        sub = dict(zip(musym, [sp.Integer(x) for x in mu]))
        bad = 0
        nterm = 0
        for f in polys:
            num, den = sp.fraction(sp.together(f))
            dval = sp.Rational(den.subs(sub))
            assert dval != 0 and sp.fraction(dval)[0] % p != 0
            for mon, c in sp.Poly(sp.expand(num), *gens).terms():
                nterm += 1
                cv = sp.Rational(sp.expand(c).subs(sub))
                if cv == 0 or sp.fraction(cv)[0] % p == 0:
                    bad += 1
        out['support_check_variants_%d' % v] = {'terms': nterm, 'vanishing': bad}
        assert bad == 0
    G1, gens = n4_trop.kc_system(mu, 'all', variants=1)
    G2, gens2 = n4_trop.kc_system(mu, 'all', variants=3)
    assert gens == gens2
    out['n_G1'], out['n_G2'] = len(G1), len(G2)
    res = tropcheck.run(G1, gens, p, wd, 'kc_G1')
    out['step1'] = {k: v for k, v in res.items() if k != 'failures'}
    out['step1_failures'] = res['failures']
    rays, cones, lin = tropcheck.parse_fan(os.path.join(wd, 'kc_G1.fan'))
    step2 = []
    allok = True
    for f in res['failures']:
        assert len(f['cone']) == 1, 'a failing cone of dimension > 1 would need a finer test'
        pt = f['point']
        ini = [tropcheck.initial_form(g, gens, pt) for g in G2]
        empty = tropcheck.singular_torus_empty(ini, gens, p, os.path.join(wd, 'kc_G2_ray%d.sing' % f['cone'][0]))
        step2.append({'ray': f['cone'][0], 'point': pt, 'torus_empty_G2': empty})
        allok = allok and empty
    out['step2'] = step2
    out['verdict_all_integral'] = allok
    json.dump(out, open(os.path.join(wd, 'kc_trop_cert.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k not in ('step1_failures',)}, indent=1))


if __name__ == '__main__':
    main()
