#!/usr/bin/env python3
"""Writes one Lean module per certificate, L6Check/Certs/C<certid>.lean, defining the embedded text
`L6.Certs.C<certid> : String := include_str "../../data/f4/certs_txt/<certid>.txt"`, so that every check that uses a
certificate (the cofactor checks and the links of the cores to the cells) refers to the same constant.
Run from the package root."""
import os
ids = sorted({f.split('.')[0] for f in os.listdir('data/f4/certs')})
os.makedirs('L6Check/Certs', exist_ok=True)
for i in ids:
    p = f'L6Check/Certs/C{i}.lean'
    txt = (f'/-! The cofactor certificate `{i}` (`data/f4/certs/{i}.txt[.gz]`, embedded as plain text). -/\n\n'
           f'namespace L6.Certs\n\n'
           f'/-- The text of certificate `{i}`. -/\n'
           f'def C{i} : String := include_str "../../data/f4/certs_txt/{i}.txt"\n\n'
           f'end L6.Certs\n')
    if not os.path.exists(p) or open(p).read() != txt:
        open(p, 'w').write(txt)
print(len(ids), 'certificate modules')
