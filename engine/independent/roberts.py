#!/usr/bin/env python3
"""Positive control (Roberts' continuum, n = 5, diagram 5 = fig11 class 4, cell containing the place of
roberts_a0.json): build the exact pipeline's system for the cell (tsec_exact's construction: primary initial forms plus
the secondary identities whose argmin set is constant on the cell, verdicts certified), then decide in characteristic 0
with Singular, saturating by every variable and every same-node difference (tcert's set):
  (a) at the Roberts masses (1/2,1/2,1/2,1/2,-1/8): must be consistent (dim >= 0);
  (b) over Q(m0..m4) with m0 fixed to 1 (homogeneity), and (c) at random rational masses: expected unit ideal.
Usage: roberts.py CODE_DIR CELLS.jsonl CELL_INDEX"""
import itertools, json, os, re, subprocess, sys, tempfile, random
sys.path.insert(0, sys.argv[1])
import tengine as T
import tinit as I
import tsec as S
import treplay as R
import tsec_exact as SE

n = 5
cls = json.load(open(os.path.join(sys.argv[1], 'fig11.json')))['classes']
cells = [json.loads(l) for l in open(sys.argv[2])]
ci = int(sys.argv[3])
cell = cells[ci]
D = T.Diagram.from_json(n, cls[4])
zt, wt = S.tree_from_json(n, cell['ztree']), S.tree_from_json(n, cell['wtree'])
L = S.cell_lp(D, zt, wt, cell['argmin'])
msym = [f'm{k}' for k in range(n)]
vsym, eqsym, _ = I.system(n, cell, msym)
ms = {k: f'(m{k})' for k in range(n)}
C = R.Certifier()
nsec = 0
single = None
for name, terms in S.secondary(D, zt, wt, L):
    r = SE.constant_argmin_exact(L, terms, C, {'cell': ci, 'identity': repr(name)})
    if r is None:
        continue
    if r[0] == 'single':
        single = (name, terms[r[1]][1])
        break
    eqsym.append('+'.join(S.term_expr(n, cell['ztree'], cell['wtree'], terms[i][1], ms) for i in r[1]).replace('+-', '-'))
    nsec += 1
print(f'cell {ci}: {len(eqsym)} equations ({nsec} secondary), single-term exclusion: {single}, '
      f'certifier counts {dict((k, v) for k, v in C.c.items() if v)}')
VAR = re.compile(r'\b(?:X\d+_\d+|Y\d+_\d+|D\d+_\d+|E)\b')
vs = sorted(set(VAR.findall(' '.join(eqsym))))
sats = list(vs)
bynode = {}
for v in vs:
    if v[0] in 'XY':
        bynode.setdefault(v.split('_')[0], []).append(v)
for node, lst in bynode.items():
    for i in range(len(lst)):
        for j in range(i + 1, len(lst)):
            sats.append(f'({lst[i]}-{lst[j]})')


def sing(eqs, ring, timeout=3600):
    s = [ring, f'ideal I = {",".join(eqs)};'] + [f'I = sat(I, ideal({f}));' for f in sats]
    s += ['ideal G = std(I);', 'print("DIM " + string(dim(G)));', 'quit;']
    fd, path = tempfile.mkstemp(suffix='.sing')
    with os.fdopen(fd, 'w') as fh:
        fh.write('\n'.join(s) + '\n')
    try:
        out = subprocess.run(['nice', '-n', '10', 'Singular', '-q', path], capture_output=True, text=True, timeout=timeout).stdout
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    os.unlink(path)
    m = re.search(r'DIM (-?\d+)', out)
    return int(m.group(1)) if m else out[-200:]


def subst(masses):
    return [re.sub(r'\bm(\d)\b', lambda mm: '(' + masses[int(mm.group(1))] + ')', e) for e in eqsym]


ring0 = f'ring R = 0, ({",".join(vs)}), dp;'
print('(a) Roberts masses (1/2,1/2,1/2,1/2,-1/8), char 0: dim', sing(subst(['1/2'] * 4 + ['-1/8']), ring0))
rnd = random.Random(3)
for t in range(2):
    mm = [f'{rnd.randint(2, 50)}/{rnd.randint(2, 50)}' for _ in range(n)]
    print(f'(c) random rational masses {mm}, char 0: dim', sing(subst(mm), ring0))
ringq = f'ring R = (0,m1,m2,m3,m4), ({",".join(vs)}), dp;'
print('(b) over Q(m1..m4), m0 = 1: dim', sing(subst(['1', 'm1', 'm2', 'm3', 'm4']), ringq))
