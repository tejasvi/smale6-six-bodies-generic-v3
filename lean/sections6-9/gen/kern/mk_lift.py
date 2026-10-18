#!/usr/bin/env python3
"""Write the Singular inputs that compute the cofactor certificates (liftstd) for the kernel versions.

Usage: mk_lift.py OUTDIR HYPSDIR
  OUTDIR:  receives c4_3_5_7_11_<chart>.sing (Lemma 7.9: the 14 charts at mu0 = (3,5,7,11) over F_32003) and
           esc_<kind>_<k>.sing (Lemma 6.19(a): the systems of the leaves `hyp`, over F_65521);
  HYPSDIR: the directory of n4_hyps.json, kc_hyps.json (the output of gen/d88trop/run.sh; the same polynomials as
           DataN4.hypStr, DataKC.hypStr).
Each script computes `liftstd(I, T)`, writes the first column of T (the cofactors of the standard basis {1}) to
cof/<name>.txt ("#k", then the Singular string of cofactor k), and prints the number of terms. The certificates are
then checked and written by verify_cof.py / verify_esc.py."""
import json
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'c4'))
from c4sys import equations, dehom, chart_vars, to_str, VARS, CHARTS, chart_name

TAIL = '''int t0 = rtimer; matrix T; ideal G = liftstd(I, T); "size", size(G), "deg G1", deg(G[1]), "rtime", rtimer - t0;
link l = ":w cof/%s.txt";
int k; int tot = 0;
for (k = 1; k <= nrows(T); k++) { tot = tot + size(T[k,1]); write(l, "#" + string(k)); write(l, string(T[k,1])); }
close(l);
"terms", tot, "G1", string(G[1]);
quit;
'''


def sing_poly17(f):
    out = []
    for c, e in f:
        mon = '*'.join(('x(%d)^%d' % (i, k) if k > 1 else 'x(%d)' % i) for i, k in enumerate(e) if k)
        out.append('%d%s' % (c, ('*' + mon) if mon else ''))
    return '+'.join(out) if out else '0'


def main():
    outdir, hypsdir = sys.argv[1], sys.argv[2]
    mu, p = (3, 5, 7, 11), 32003
    for ch in CHARTS:
        name = 'c4_3_5_7_11_%s' % chart_name(ch)
        keep = chart_vars(ch)
        eqs = [dehom(f, ch) for f in equations(mu)]
        s = 'ring R = %d, (%s), dp;\n' % (p, ','.join(VARS[i] for i in keep))
        s += 'ideal I = ' + ',\n'.join(to_str(f, VARS, keep) for f in eqs) + ';\n'
        open(os.path.join(outdir, name + '.sing'), 'w').write(s + TAIL % name)
    for kind in ('n4', 'kc'):
        for k, system in enumerate(json.load(open(os.path.join(hypsdir, '%s_hyps.json' % kind)))):
            name = 'esc_%s_%d' % (kind, k)
            s = 'ring r = 65521,(%s),dp;\n' % ','.join('x(%d)' % i for i in range(17))
            s += 'ideal I = %s;\n' % ',\n'.join(sing_poly17(f) for f in system)
            open(os.path.join(outdir, name + '.sing'), 'w').write(s + TAIL % name)


main()
