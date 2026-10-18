#!/usr/bin/env python3
"""Splits the modules of one class of the kernel run of F2-F4 (deps.txt and groups.txt of CLASSDIR, from kf34k_gen.py)
into K parts for K machines, by export run (groups never span runs), balanced by weight (largest run first, to the
lightest part); each part also gets the class module. The modules that import modules of several runs (the prefix
levels and their covering modules) and the class theorem go to a final part, built after the K parts are gathered.
Writes OUTPREFIX<i>.txt (i < K) and OUTPREFIXfinal.txt in the format of deps.txt.
Usage: kf34k_split.py CLASSDIR K OUTPREFIX"""
import os, sys

cdir, k, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
cls = os.path.basename(os.path.normpath(cdir))
pre = f'L6CheckF.{cls}.'
run, weight = {}, {}
for line in open(os.path.join(cdir, 'groups.txt')):
    t = line.split()
    d = dict(zip(t[1::2], t[2::2]))
    run[t[0]] = int(d['run'])
    weight[t[0]] = int(d['weight'])
deps, order = {}, []
for line in open(os.path.join(cdir, 'deps.txt')):
    m, _, ds = line.partition(':')
    deps[m.strip()] = ds.split()
    order.append(m.strip())


def group(m):
    # NG<g> and VG<g> belong to group NG<g>
    s = m[len(pre):]
    return 'NG' + s[2:] if s[:2] in ('NG', 'VG') else None


def runs_of(m):
    return {run[group(d)] for d in [m] + deps[m] if d.startswith(pre) and group(d)}


final = set()
for m in order:
    if group(m) is None and m != pre + 'Class' or len(runs_of(m)) > 1 or any(d in final for d in deps[m]):
        final.add(m)
rw = {}
for m in order:
    if m not in final and group(m) and m[len(pre):].startswith('NG'):
        rw[run[group(m)]] = rw.get(run[group(m)], 0) + weight[group(m)]
load, part = [0] * k, {}
for r in sorted(rw, key=lambda r: (-rw[r], r)):
    i = min(range(k), key=lambda i: (load[i], i))
    part[r] = i
    load[i] += rw[r]
for i in range(k):
    with open(f'{out}{i}.txt', 'w') as f:
        for m in order:
            if m == pre + 'Class' or m not in final and group(m) and part[run[group(m)]] == i:
                f.write(f'{m}: {" ".join(deps[m])}\n')
with open(f'{out}final.txt', 'w') as f:
    for m in order:
        if m in final:
            f.write(f'{m}: {" ".join(deps[m])}\n')
print(cls, 'runs', len(rw), 'parts', ' '.join(str(x) for x in load), 'final', ' '.join(sorted(final)))
