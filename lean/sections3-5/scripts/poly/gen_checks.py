#!/usr/bin/env python3
"""Writes the modules L6Check/Poly/B<k>.lean: one `native_decide` theorem per cofactor certificate,
`L6.Poly.Checks.cert_<certid> : L6.Poly.checkCert L6.Certs.C<certid> = true`, about 24 certificates per module and
the largest ones (compressed in data/f4/certs) one per module; and L6Check/Poly/Index.lean, which imports them all.
Run from the package root after scripts/poly/gen_cert_modules.py."""
import os
files = sorted(os.listdir('data/f4/certs'))
big = [f.split('.')[0] for f in files if f.endswith('.gz')]
small = [f.split('.')[0] for f in files if not f.endswith('.gz')]
small.sort(key=lambda i: os.path.getsize(f'data/f4/certs/{i}.txt'))
batches = [[i] for i in big] + [small[k:k + 24] for k in range(0, len(small), 24)]
os.makedirs('L6Check/Poly', exist_ok=True)
for k, b in enumerate(batches):
    lines = ['import L6Poly.Basic'] + [f'import L6Check.Certs.C{i}' for i in b] + [
        '', f'/-! Cofactor certificates, batch {k}: `checkCert` of each embedded text (`native_decide`). -/', '',
        'namespace L6.Poly.Checks', '']
    for i in b:
        lines += [f'set_option maxHeartbeats 0 in',
                  f'theorem cert_{i} : L6.Poly.checkCert L6.Certs.C{i} = true := by native_decide', '']
    lines += ['end L6.Poly.Checks', '']
    open(f'L6Check/Poly/B{k}.lean', 'w').write('\n'.join(lines))
open('L6Check/Poly/Index.lean', 'w').write(
    '\n'.join(f'import L6Check.Poly.B{k}' for k in range(len(batches))) + '\n')
print(len(big) + len(small), 'certificates in', len(batches), 'modules')
