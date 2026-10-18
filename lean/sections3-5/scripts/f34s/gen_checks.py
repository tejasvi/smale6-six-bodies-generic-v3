#!/usr/bin/env python3
"""Writes L6Check/F34S/C<N>K<k>.lean: for each chunk of F3/F4 (L6Check/F34/C<N>K<k>.lean, same cells, certificates
and counts), the theorem that `checkChunkS` (the checks on the cells of the specification search) passes, by
native_decide. Run from the package root (untrusted: Lean checks what it writes)."""
import os, re
SRC, DST = 'L6Check/F34', 'L6Check/F34S'
os.makedirs(DST, exist_ok=True)
files = sorted((f for f in os.listdir(SRC) if re.fullmatch(r'C\d+K\d+\.lean', f)),
               key=lambda f: tuple(int(x) for x in re.findall(r'\d+', f)))
for f in files:
    t = open(os.path.join(SRC, f)).read()
    m = re.search(r'theorem F34_c(\d+)_k(\d+) : checkChunk (\d+) n6 cells_\d+ (single_\d+) (links_\d+) (pass_\d+) open43\s*'
                  r'(\[.*?\])\s*(\d+) (\d+) (\{[^}]*\}) = true', t, re.S)
    assert m, f
    cls, k, cls2, single, links, pas, certs, lo, hi, cnt = m.groups()
    assert cls == cls2
    cert_imports = re.findall(r'^import (L6Check\.Certs\.C[0-9a-f]+)$', t, re.M)
    imports = '\n'.join(['import L6F34S.Check', 'import L6F2.Check', f'import L6Check.F2.Data.C{cls}',
                         'import L6Check.F34.Data.Common', f'import L6Check.F34.Data.C{cls}'] +
                        [f'import {c}' for c in cert_imports])
    out = f'''{imports}

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class {cls}, cells {lo} ≤ cell < {hi} of
`data/cells/c{cls}.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `{lo} ≤ cell < {hi}` of class {cls} is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts {cnt}. -/
theorem F34S_c{cls}_k{k} : checkChunkS {cls} (L6.F2.diagOf {cls}) L6.F2.Data.cells_c{cls} {single} {links} {pas} open43
    {certs}
    {lo} {hi} {cnt} = true := by
  native_decide

end L6.F34S.Checks
'''
    open(os.path.join(DST, f), 'w').write(out)
print(len(files), 'chunk modules')
