#!/usr/bin/env python3
"""Writes the version-1 links between lean6's certificate texts and the literal certificates of the kernel check:
L6CheckK/F4Link/L<k>.lean, 64 certificates per module (and All.lean importing them), with for each certificate H
  link_H    : the text `L6.Certs.C<H>` parses to a certificate with the generators, h, nvar and fixed of `certH`
              (native_decide, version 1);
  meaning_H : the text parses to a certificate with its meaning (`L6K.F4.meaning_of_link` from link_H and the
              kernel theorem `L6CheckK.F4.C<H>.cert`).
The modules holding each certificate are read from the generated sources under ROOT (packs P<n>, C<H>/Data, M<n>).
Usage: kf4_link_gen.py ROOT"""
import os, re, sys

root = sys.argv[1]
base = os.path.join(root, 'L6CheckK', 'F4')
data_mod, main_mod = {}, {}
for f in os.listdir(base):
    p = os.path.join(base, f)
    if f.endswith('.lean') and re.match(r'[PM]\d+\.lean$', f):
        mod = 'L6CheckK.F4.' + f[:-5]
        for line in open(p):
            m = re.match(r'namespace L6CheckK\.F4\.C(\w+)$', line.strip())
            if m:
                (data_mod if f.startswith('P') else main_mod).setdefault(m.group(1), mod)
    elif os.path.isdir(p) and f.startswith('C') and os.path.exists(os.path.join(p, 'Data.lean')):
        data_mod[f[1:]] = f'L6CheckK.F4.{f}.Data'
hs = sorted(main_mod)
assert set(hs) == set(data_mod), 'certificates without data or main module'
outdir = os.path.join(root, 'L6CheckK', 'F4Link')
os.makedirs(outdir, exist_ok=True)
for k in range(0, len(hs), 64):
    grp = hs[k:k + 64]
    imports = ['L6SoundK.F4.Link'] + [f'L6Check.Certs.C{h}' for h in grp]
    for h in grp:
        for m in (data_mod[h], main_mod[h]):
            if m not in imports:
                imports.append(m)
    L = [f'import {m}' for m in imports] + ['', 'set_option maxHeartbeats 0',
         '-- the decidability instance of the 4-tuple equality is larger than the default bound',
         'set_option synthInstance.maxSize 1024', '',
         f'/-! Links of the certificate texts to the literal certificates, certificates {k}–{k + len(grp) - 1}. -/', '',
         'namespace L6CheckK.F4Link', '', 'open L6.Poly', '']
    for h in grp:
        c = f'L6CheckK.F4.C{h}.certH'
        L.append(f'theorem link_{h} : (parseCert L6.Certs.C{h}).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = '
                 f'some ({c}.nvar, {c}.fixed, {c}.gens, {c}.h) := by native_decide')
        L.append(f'theorem meaning_{h} : ∃ c, parseCert L6.Certs.C{h} = some c ∧ CertMeaning c := '
                 f'L6K.F4.meaning_of_link link_{h} L6CheckK.F4.C{h}.cert')
    L += ['', 'end L6CheckK.F4Link']
    open(os.path.join(outdir, f'L{k // 64}.lean'), 'w').write('\n'.join(L) + '\n')
nmod = (len(hs) + 63) // 64
open(os.path.join(outdir, 'All.lean'), 'w').write(
    '\n'.join([f'import L6CheckK.F4Link.L{i}' for i in range(nmod)] +
              ['', f'/-! The links of all {len(hs)} certificate texts (`L6CheckK.F4Link.link_<H>`, `meaning_<H>`). -/']) + '\n')
print('certificates', len(hs), 'modules', nmod)
