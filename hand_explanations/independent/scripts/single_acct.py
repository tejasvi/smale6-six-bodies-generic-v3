import json, os
from collections import Counter
exec(open('cumul_ref.py').read().split("F = {k: flags(k) for k in mine}")[0])
F = {k: flags(k) for k in mine}
S = {k for k in F if k in single}
out = {k for k in S if not F[k] & {'T', 'P', 'C', 'B'}}
print('single-term cells', len(S), 'outside T,P,C,B:', len(out))
g = {k for k in out if F[k] & {'E', 'E1', 'R1', 'R5', 'R6', 'Q'}}
print('  covered by E/E1/R1/R5/R6/Q:', len(g), '; rest:', len(out - g))
print('  of the 1,102: B0', sum('B0' in F[k] for k in out), 'K', sum('K' in F[k] for k in out), 'L', sum('L' in F[k] for k in out))
print('  every-mass (B0/K) among the 1,102:', sum(bool(F[k] & {'B0','K'}) for k in out))
# MECHANISMS 2.1 table: engine identity types
eng = Counter(); cov = Counter()
for k in S:
    idt = mech[k]['engine_single']
    nm = str(idt[0])
    eng[nm] += 1
print(len(eng), 'engine identity names (top):', eng.most_common(12))
