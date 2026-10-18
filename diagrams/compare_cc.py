#!/usr/bin/env python3
"""Compare the 117 six-body diagrams of Chang-Chen (transcribed from their notebook: CC_JSON is the list under the key "diagrams"
of chang_chen_diagrams.json) with our 191 classes (enum/n6.json): rule check of each of theirs under our okR rule set,
canonical forms under S6 x colour exchange, and the classes on each side only.
Usage: compare_cc.py CC_JSON N6_JSON OUT_JSON"""
import itertools, json, sys
sys.path.insert(0, '.')
import zwenum as Z

cc_path, n6_path, out_path = sys.argv[1:4]
n = 6
pairs, pos, tri_at, quad_at, adj = Z.setup(n)
m = len(pairs)
perms = list(itertools.permutations(range(n)))


def from_cc(d):
    v = [0] * m
    for a, b in d['z_strokes']:
        v[pos[(a - 1, b - 1)]] |= 1
    for a, b in d['w_strokes']:
        v[pos[(a - 1, b - 1)]] |= 2
    cz = sum(1 << (k - 1) for k in d['z_circled'])
    cw = sum(1 << (k - 1) for k in d['w_circled'])
    return tuple(v), cz, cw


def from_ours(c):
    v = [0] * m
    for key, val in c['edges'].items():
        v[pos[(int(key[0]), int(key[1]))]] = val
    return tuple(v), sum(1 << k for k in c['zcircles']), sum(1 << k for k in c['wcircles'])


def rule_report(d):
    """Which okR rules the labelled diagram fails (empty list: it passes)."""
    v, cz, cw = d
    fails = []
    for j in range(m):
        for t in tri_at[j]:
            if not Z.tri_ok(v[t[0]], v[t[1]], v[t[2]]):
                fails.append('E2/E3 triangle ' + '/'.join(f'{pairs[i][0]+1}{pairs[i][1]+1}' for i in t))
        for q in quad_at[j]:
            if not Z.quad_ok(v[q[0]], v[q[1]], v[q[2]], v[q[3]]):
                fails.append('E6 4-cycle ' + '/'.join(f'{pairs[i][0]+1}{pairs[i][1]+1}' for i in q))
    mz, mw = Z.masks(v)
    if not Z.edge_global(mz, mw, adj, m):
        fails.append('E1/E4/E5')
    if not Z.colour_rules(mz, mw, cz, pairs, n):
        fails.append('C (z)')
    if not Z.colour_rules(mw, mz, cw, pairs, n):
        fails.append('C (w)')
    return fails


ours = json.load(open(n6_path))['classes']
our_canon = {}
for i, c in enumerate(ours):
    our_canon[Z.canonical(from_ours(c), n, pairs, pos, perms)] = i
assert len(our_canon) == len(ours)

cc = json.load(open(cc_path))
res = []
cc_canon = {}
for d in cc:
    L = from_cc(d)
    k = Z.canonical(L, n, pairs, pos, perms)
    fails = rule_report(L)
    cc_canon.setdefault(k, []).append(d['number'])
    res.append({'cc': d['number'], 'ours': our_canon.get(k), 'fails': fails})

print(f'Chang-Chen: {len(cc)} diagrams, {len(cc_canon)} distinct under S6 x colour exchange')
dup = {tuple(v) for v in cc_canon.values() if len(v) > 1}
print('their diagrams equal under colour exchange:', sorted(dup))
bad = [r for r in res if r['fails']]
print(f'{len(bad)} of theirs fail our rules:', [(r['cc'], r['fails']) for r in bad][:20])
missing = [r['cc'] for r in res if r['ours'] is None]
print(f'{len(missing)} of theirs not among our 191:', missing)
covered = sorted({r['ours'] for r in res if r['ours'] is not None})
extra = [i for i in range(len(ours)) if i not in covered]
print(f'our classes covered: {len(covered)}; ours only: {len(extra)}')
json.dump({'per_cc': res, 'ours_only': extra, 'cc_classes': {str(our_canon.get(k)): v for k, v in cc_canon.items()}},
          open(out_path, 'w'), indent=1)
print('wrote', out_path)
