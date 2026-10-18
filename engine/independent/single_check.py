#!/usr/bin/env python3
"""Consistency check of stored single-term exclusions (not a proof; the proof is the certified LP verdicts): for a random
sample of cells excluded by a single minimal term, recompute the identity's terms (tsec.secondary on the cell's trees)
and check, in exact arithmetic at the stored interior point (heights hz, hw rounded to 6 digits, re-centred by an exact
LP-free test), that the named term is the unique term of least exponent. Also re-derives the exclusion with an
independent exact method: for every other term k, the LP  min (t_k - t_i) over the closure of the cell  is solved by
HiGHS and its value must be > 0, or = 0 only on the boundary (then the strict check is done by treplay's certifier).
Usage: single_check.py CODE_DIR EXACT_COLLECT N SEED"""
import glob, json, os, random, sys
from fractions import Fraction
sys.path.insert(0, sys.argv[1])
import tengine as T
import tsec as S
import treplay as R
import texact as X

n = 6
root, N, seed = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
cls = json.load(open(os.path.join(sys.argv[1], 'n6.json')))['classes']
pool = []
for d in sorted(glob.glob(os.path.join(root, '*', 'exact6', 'c*'))):
    c = int(os.path.basename(d)[1:])
    for f in glob.glob(d + '/sec/p*.sec.jsonl'):
        for l in open(f):
            r = json.loads(l)
            if 'excluded_by' in r:
                pool.append((c, r['cell'], r['excluded_by']))
rng = random.Random(seed)
sample = rng.sample(pool, min(N, len(pool)))
cells_cache = {}
ok_point = ok_cert = 0
bad = []
for c, cell, ex in sample:
    if c not in cells_cache:
        d = glob.glob(os.path.join(root, '*', 'exact6', f'c{c}'))[0]
        cells_cache[c] = open(d + '/cells.jsonl').read().splitlines()
    cj = json.loads(cells_cache[c][cell])
    D = T.Diagram.from_json(n, cls[c])
    zt, wt = S.tree_from_json(n, cj['ztree']), S.tree_from_json(n, cj['wtree'])
    L = S.cell_lp(D, zt, wt, cj['argmin'])
    ids = {repr(name): terms for name, terms in S.secondary(D, zt, wt, L)}
    terms = ids[ex['identity']]
    i0 = [repr(sym) for _, sym in terms].index(ex['term'])
    # (1) at the stored interior point
    pt = [Fraction(0)] * L.nv
    for v, h in cj['hz'].items():
        pt[L.zv[int(v)]] = Fraction(h)
    for v, h in cj['hw'].items():
        pt[L.wv[int(v)]] = Fraction(h)
    val = lambda f: sum(Fraction(cf) * pt[j] for j, cf in f.items())
    vals = [val(f) for f, _ in terms]
    if all(vals[k] > vals[i0] for k in range(len(terms)) if k != i0):
        ok_point += 1
    # (2) the certified verdicts, recomputed: no point of the open cell with t_k <= t_i0
    C = R.Certifier()
    good = True
    for k in range(len(terms)):
        if k == i0:
            continue
        dlt = S.add(terms[k][0], S.scale(terms[i0][0], -1.0))
        if C.feasible(X.sub(L, [(dlt, None, 0.0)]), ('single', zt, wt)):
            good = False
    if good and C.c['fail'] == 0:
        ok_cert += 1
    else:
        bad.append((c, cell, ex, dict(C.c)))
print(json.dumps({'pool': len(pool), 'sample': len(sample), 'unique_min_at_stored_point': ok_point,
                  'recertified_single': ok_cert, 'bad': bad[:5]}))
