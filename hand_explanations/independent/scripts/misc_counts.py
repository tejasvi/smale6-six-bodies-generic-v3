import json, os, itertools
from collections import Counter
import sys
sys.path.insert(0, '.')
import refkit as K
import ref_lemmas as L
exec(open('cumul_ref.py').read().split("F = {k: flags(k) for k in mine}")[0])
F = {k: flags(k) for k in mine}
print('B cells', sum('B' in f for f in F.values()), 'B not in T or C:', sum('B' in f and not f & {'T', 'C'} for f in F.values()))
print('R5 beyond E,E1,R1,R6:', sum('R5' in f and not f & {'E', 'E1', 'R1', 'R6'} for f in F.values()))
print('R5 beyond E,E1:', sum('R5' in f and not f & {'E', 'E1'} for f in F.values()))
resid = [k for k, r in mech.items() if r['first'] == 'comp']
print('residue classes:', len({k[0] for k in resid}), sorted({k[0] for k in resid}))
# E1: all three vertices balanced in both colours on some triangle with (H1)
n3 = 0
for c, i, rec in K.iter_cells():
    if 'E1' not in F[(c, i)]:
        continue
    C = K.RCell(rec, c, i)
    for T in L.TRIS:
        if L.one_node(C.zt, T) is None or L.one_node(C.wt, T) is None:
            continue
        if all(L.is_balanced(C, col, k, T) for col in 'zw' for k in T):
            n3 += 1
            break
print('E1 cells with a triangle balanced at all three vertices in both colours:', n3)
n_w = 0
for c, i, rec in K.iter_cells():
    if 'E1' not in F[(c, i)]:
        continue
    C = K.RCell(rec, c, i)
    main, _ = L.lemma_E1(C)
    T = main[0]
    if all(L.is_balanced(C, col, k, T) for col in 'zw' for k in T):
        n_w += 1
print('E1 cells whose FIRST witness triangle is balanced at all three vertices in both colours:', n_w)
