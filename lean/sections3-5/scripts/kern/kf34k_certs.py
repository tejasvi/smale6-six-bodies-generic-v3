#!/usr/bin/env python3
"""Writes ROOT/L6CheckF/Certs.lean: the certificates of the F4 kernel modules (`L6CheckK.F4.C<H>.certH`, under
F4ROOT), in the order of CERTNAMES, as one list `L6CheckF.csAll`, with `L6CheckF.Certs.mem_<H> : certH ∈ csAll` for
each; the certificates of the cores of the kernel run of F2-F4 are taken from it (`ClaimMeaningFinK csAll`). The list
is a balanced tree of appends (`Certs.t<a>_<b>`: the certificates `a` to `b - 1`), so that each membership is a path
of `List.mem_append_left`/`right` of logarithmic length. Also ROOT/L6CheckF/deps_certs.txt for the build scheduler.
Usage: kf34k_certs.py CERTNAMES F4ROOT ROOT"""
import os, re, sys

certnames, f4root, root = sys.argv[1:4]
names = [l.strip() for l in open(certnames) if l.strip()]
data_mod = {}
base = os.path.join(f4root, 'L6CheckK', 'F4')
for f in os.listdir(base):
    p = os.path.join(base, f)
    if f.endswith('.lean') and re.match(r'P\d+\.lean$', f):
        for line in open(p):
            m = re.match(r'namespace L6CheckK\.F4\.C(\w+)$', line.strip())
            if m:
                data_mod.setdefault(m.group(1), 'L6CheckK.F4.' + f[:-5])
    elif os.path.isdir(p) and f.startswith('C') and os.path.exists(os.path.join(p, 'Data.lean')):
        data_mod[f[1:]] = f'L6CheckK.F4.{f}.Data'
L = [f'import {m}' for m in sorted({data_mod[h] for h in names})] + [
    '', 'set_option maxRecDepth 100000', '',
    '/-! # The certificates of the F4 kernel modules, as one list',
    '',
    f'The {len(names)} certificates `L6CheckK.F4.C<H>.certH` (each with `CertMeaning`, `L6CheckK.F4.C<H>.cert`): the',
    'certificates of the cores of the kernel run of F2-F4 are taken from this list. -/', '',
    'namespace L6CheckF.Certs', '']


def tree(a, b):
    # the definition of t<a>_<b> after those of its halves
    if b - a == 1:
        L.append(f'def t{a}_{b} : List L6.Poly.Cert := [L6CheckK.F4.C{names[a]}.certH]')
    else:
        m = (a + b) // 2
        tree(a, m)
        tree(m, b)
        L.append(f'def t{a}_{b} : List L6.Poly.Cert := t{a}_{m} ++ t{m}_{b}')


def mem(i, a, b):
    if b - a == 1:
        return f'List.mem_singleton_self L6CheckK.F4.C{names[i]}.certH'
    m = (a + b) // 2
    if i < m:
        return f'List.mem_append_left t{m}_{b} ({mem(i, a, m)})'
    return f'List.mem_append_right t{a}_{m} ({mem(i, m, b)})'


n = len(names)
tree(0, n)
L += ['', 'end L6CheckF.Certs', '', 'namespace L6CheckF', '', '/-- The certificates of the F4 kernel modules. -/',
      f'def csAll : List L6.Poly.Cert := Certs.t0_{n}', '', 'end L6CheckF', '', 'namespace L6CheckF.Certs', '']
for i, h in enumerate(names):
    L.append(f'theorem mem_{h} : L6CheckK.F4.C{h}.certH ∈ csAll :=')
    L.append(f'  {mem(i, 0, n)}')
L += ['', 'end L6CheckF.Certs']
out = os.path.join(root, 'L6CheckF')
os.makedirs(out, exist_ok=True)
open(os.path.join(out, 'Certs.lean'), 'w').write('\n'.join(L) + '\n')
open(os.path.join(out, 'deps_certs.txt'), 'w').write('L6CheckF.Certs: \n')
print('certs', len(names))
