#!/usr/bin/env python3
"""The matrix rules of Chang-Chen (arXiv:2303.02853, Theorems 3.1-3.8) on our classes: for each class of
enum/nN.json, the list of their rules that it fails. The rules are invariant under relabelling, and each is applied to
(A, B) and to (B, A), so a class representative suffices. Theorem 3.3(d) carries the mass condition m3i + m3j != 0
of [AK12, Prop. 4]; it is reported separately as 'T3.3d*'.
A = z-matrix (a_ij = z-stroke, a_ii = z-circle), B = w-matrix, C = A + B.
Usage: ccrules.py N N_JSON OUT_JSON"""
import itertools, json, sys

n = int(sys.argv[1])
cls = json.load(open(sys.argv[2]))['classes']
out_path = sys.argv[3]
R = range(n)


def matrices(c):
    A = [[0] * n for _ in R]
    B = [[0] * n for _ in R]
    for key, val in c['edges'].items():
        i, j = int(key[0]), int(key[1])
        if val & 1:
            A[i][j] = A[j][i] = 1
        if val & 2:
            B[i][j] = B[j][i] = 1
    for k in c['zcircles']:
        A[k][k] = 1
    for k in c['wcircles']:
        B[k][k] = 1
    return A, B


def components(A):
    """Connected components of the stroke graph (circles ignored), as frozensets, singletons included."""
    seen, comps = set(), []
    for s in R:
        if s in seen:
            continue
        comp, stack = {s}, [s]
        while stack:
            u = stack.pop()
            for v in R:
                if v != u and A[u][v] and v not in comp:
                    comp.add(v)
                    stack.append(v)
        seen |= comp
        comps.append(frozenset(comp))
    return comps


def tr(A):
    return sum(A[i][i] for i in R)


def mono(A, B, tag):
    """Rules on one colour (A) with its companion (B); tag names the colour of A."""
    f = []
    # 3.1(a) column sums
    cs = [sum(A[i][j] for i in R) for j in R]
    if 1 in cs or all(x == 0 for x in cs):
        f.append('T3.1a' + tag)
    # 3.1(b) two column sums (symmetric in A, B; checked once per call is harmless)
    for i, j in itertools.combinations(R, 2):
        if A[i][j] + B[i][j] == 2:
            if sum(A[k][i] + A[k][j] for k in R if k not in (i, j)) == 0 or \
               sum(B[k][i] + B[k][j] for k in R if k not in (i, j)) == 0:
                f.append('T3.1b')
                break
    # 3.2 circling: a_ij (b_ii + b_jj) != 1
    for i, j in itertools.combinations(R, 2):
        if A[i][j] * (B[i][i] + B[j][j]) == 1:
            f.append('T3.2' + tag)
            break
    # 3.3(a)
    if tr(A) == 1:
        f.append('T3.3a' + tag)
    # 3.3(c), (d)
    if tr(A) == 2:
        i, j = [k for k in R if A[k][k]]
        if A[i][j] != 1 or any(A[i][k] != A[j][k] for k in R if k not in (i, j)):
            f.append('T3.3c' + tag)
        if all(A[k][l] == 0 for k in R for l in R if k != l and {k, l} != {i, j}):
            if any(B[i][k] or B[j][k] for k in R):
                f.append('T3.3d' + tag)
            elif tr(B) == n - 3:
                f.append('T3.3d*' + tag)
    # 3.3(e)
    if tr(A) == 3:
        circ = [k for k in R if A[k][k]]
        for i in circ:
            j, k = [x for x in circ if x != i]
            for l in R:
                if l in circ:
                    continue
                if A[i][j] == A[i][k] == A[i][l] == 1 and A[j][l] + A[k][l] == 0:
                    f.append('T3.3e' + tag)
    # 3.4(a), (b)
    for i, j, k in itertools.combinations(R, 3):
        a = A
        if (a[i][i] + a[j][j] + a[k][k]) * (a[i][i] + a[i][j] + a[i][k]) * (a[i][k] + a[j][k] + a[k][k]) * \
           (a[i][j] + a[j][j] + a[j][k]) == 16:
            f.append('T3.4a' + tag)
        mx = max(a[i][i] + a[i][j] + a[i][k], a[j][i] + a[j][j] + a[j][k], a[k][i] + a[k][j] + a[k][k])
        if (a[i][i] + a[i][j] + a[i][k] + a[j][j] + a[j][k] + a[k][k]) * mx == 9:
            f.append('T3.4b' + tag)
    # 3.5(a)
    for q in itertools.combinations(R, 4):
        if sum(A[x][y] for x, y in itertools.combinations(q, 2)) == 5:
            f.append('T3.5a' + tag)
    # 3.7(a) fully connected companions
    if len(components(A)) == 1 and tr(B) != 0:
        f.append('T3.7a' + tag)
    # 3.7(b) connected components (of size > 1, as in the notebook; singletons are covered by 3.1a)
    for I in components(A):
        if len(I) < 2:
            continue
        s = sum(A[i][i] for i in I)
        if s == 1:
            f.append('T3.7bi' + tag)
        if s == len(I) and all(A[i][j] + B[i][j] == 2 for i, j in itertools.combinations(sorted(I), 2)):
            f.append('T3.7bii' + tag)
    # 3.8 trace-0 principal minors
    for r in range(1, n):
        for I in itertools.combinations(R, r):
            if all(A[i][i] == 0 for i in I):
                if sum(A[i][j] for i in I for j in R if j not in I) == 1:
                    f.append('T3.8' + tag)
                    break
        else:
            continue
        break
    return f


def bi(A, B):
    f = []
    C = [[A[i][j] + B[i][j] for j in R] for i in R]
    # 3.3(b)
    if all(C[i][j] != 1 for i, j in itertools.combinations(R, 2)) and tr(A) + tr(B) != 0:
        f.append('T3.3b')
    # 3.4(c), (d)
    for i, j, k in itertools.combinations(R, 3):
        if C[i][j] + C[j][k] + C[i][k] in (4, 5):
            f.append('T3.4c')
        if C[i][j] * C[j][k] * C[i][k] * max(A[i][j] + A[j][k] + A[i][k], B[i][j] + B[j][k] + B[i][k]) not in (0, 3, 24):
            f.append('T3.4d')
    # 3.5(b), all three 4-cycles of each 4-set
    for q in itertools.combinations(R, 4):
        a, b, c, d = q
        for (i, j, k, l) in [(a, b, c, d), (a, b, d, c), (a, c, b, d)]:
            if C[i][j] * C[j][k] * C[k][l] * C[l][i]:
                if 1 in (A[i][j] + A[k][l], A[j][k] + A[l][i], B[i][j] + B[k][l], B[j][k] + B[l][i]):
                    f.append('T3.5b')
    # 3.6 pentagons: every 5-cycle (5 distinct vertices up to rotation and reflection)
    for five in itertools.combinations(R, 5):
        first = five[0]
        for rest in itertools.permutations(five[1:]):
            if rest[0] > rest[-1]:
                continue
            cyc = (first,) + rest
            es = [(cyc[t], cyc[(t + 1) % 5]) for t in range(5)]
            if all(C[x][y] for x, y in es):
                Nz = sum(1 for x, y in es if (A[x][y], B[x][y]) == (1, 0))
                Nw = sum(1 for x, y in es if (A[x][y], B[x][y]) == (0, 1))
                Nzw = sum(1 for x, y in es if (A[x][y], B[x][y]) == (1, 1))
                if Nz == 1 or Nw == 1 or (Nz, Nw, Nzw) in ((4, 0, 1), (0, 4, 1)):
                    f.append('T3.6')
    return f


res = []
for idx, c in enumerate(cls):
    A, B = matrices(c)
    fails = sorted(set(mono(A, B, 'z') + mono(B, A, 'w') + bi(A, B)))
    res.append({'class': idx, 'fails': fails})
hard = [r for r in res if any(not x.startswith('T3.3d*') for x in r['fails'])]
massc = [r for r in res if r['fails'] and all(x.startswith('T3.3d*') for x in r['fails'])]
print(f'n={n}: {len(cls)} classes; {len(hard)} fail a rule of Chang-Chen; {len(massc)} fail only T3.3d* (mass condition);'
      f' {len(cls) - len(hard) - len(massc)} pass all')
from collections import Counter
cnt = Counter(x for r in res for x in r['fails'])
print('failures by rule:', dict(sorted(cnt.items())))
json.dump(res, open(out_path, 'w'), indent=1)
print('wrote', out_path)
