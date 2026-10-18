#!/usr/bin/env python3
"""Write a Singular input for one chart: mk_sing.py MU P CHART MODE > file.sing
MODE: std (standard basis with protocol), liftstd (cofactors of the standard basis), sub (test subsets)."""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4sys import equations, dehom, chart_vars, to_str, VARS, CHARTS, chart_name

mu = tuple(int(x) for x in sys.argv[1].split(','))
p = int(sys.argv[2])
ch = [c for c in CHARTS if chart_name(c) == sys.argv[3]][0]
mode = sys.argv[4]
order = sys.argv[5] if len(sys.argv) > 5 else 'dp'
keep = chart_vars(ch)
names = [VARS[i] for i in keep]
eqs = [dehom(f, ch) for f in equations(mu)]
print('ring R = %d, (%s), %s;' % (p, ','.join(names), order))
print('ideal I = ' + ',\n'.join(to_str(f, VARS, keep) for f in eqs) + ';')
if mode == 'std':
    print('option(prot); option(redSB); int t0 = rtimer; ideal G = std(I); "size", size(G), "deg", deg(G[1]), "rtime", rtimer - t0;')
elif mode == 'liftstd':
    print('int t0 = rtimer; matrix T; ideal G = liftstd(I, T); "size", size(G), "deg G1", deg(G[1]), "rtime", rtimer - t0;')
    print('int tot = 0; int d = 0; int k; for (k = 1; k <= nrows(T); k++) { tot = tot + size(T[k,1]); if (deg(T[k,1]) > d) { d = deg(T[k,1]); } }')
    print('"terms", tot, "maxdeg", d;')
elif mode == 'sub':
    print('int n = ncols(I); int m; int k; ideal J; ideal G;')
    print('for (k = 1; k <= n; k++) { J = I; J[k] = 0; G = std(J); if (deg(G[1]) == 0) { "drop", k, "still unit"; } }')
print('quit;')
