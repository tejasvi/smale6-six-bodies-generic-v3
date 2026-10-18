#!/usr/bin/env python3
"""Write a Macaulay2 input for one chart: mk_m2.py MU P CHART > file.m2 (Groebner basis with change matrix)."""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4sys import equations, dehom, chart_vars, to_str, VARS, CHARTS, chart_name

mu = tuple(int(x) for x in sys.argv[1].split(','))
p = int(sys.argv[2])
ch = [c for c in CHARTS if chart_name(c) == sys.argv[3]][0]
keep = chart_vars(ch)
names = [VARS[i] for i in keep]
eqs = [dehom(f, ch) for f in equations(mu)]
print('R = ZZ/%d[%s, MonomialOrder=>GRevLex];' % (p, ','.join(names)))
print('I = ideal(' + ',\n'.join(to_str(f, VARS, keep) for f in eqs) + ');')
print('t0 = cpuTime(); G = gb(I, ChangeMatrix=>true); t1 = cpuTime();')
print('<< "gb time " << (t1 - t0) << " gens " << numColumns gens G << endl;')
print('C = getChangeMatrix G;')
print('<< "change matrix " << numRows C << "x" << numColumns C << endl;')
print('t2 = cpuTime(); q = (matrix{{1_R}}) // (gens I); t3 = cpuTime();')
print('<< "lift time " << (t3 - t2) << endl;')
print('<< "check " << ((gens I) * q == matrix{{1_R}}) << endl;')
print('tot = sum(flatten entries q, f -> #(terms f)); md = max(flatten entries q / (f -> if f == 0 then -1 else first degree f));')
print('<< "terms " << tot << " maxdeg " << md << endl;')
print('exit 0')
