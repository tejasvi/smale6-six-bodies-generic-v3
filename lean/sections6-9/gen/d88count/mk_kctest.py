#!/usr/bin/env python3
"""Write a Lean module that runs the Buchberger engine of Comp.K4.C4.GB on the msolve input of KC′ (a measurement,
not part of the proof). Usage: mk_kctest.py MSFILE OUT.lean"""
import re
import sys

lines = open(sys.argv[1]).read().split('\n')
names = lines[0].strip().split(',')
p = int(lines[1].strip())
body = ''.join(lines[2:]).replace(' ', '')
polys = []
for ptxt in body.split(','):
    if not ptxt:
        continue
    terms = []
    for t in re.findall(r'[+-]?[^+-]+', ptxt):
        sg = -1 if t[0] == '-' else 1
        t = t.lstrip('+-')
        c, e = 1, [0] * len(names)
        for f in t.split('*'):
            if re.fullmatch(r'\d+', f):
                c *= int(f)
            else:
                m = re.fullmatch(r'([A-Za-z0-9]+?)(\^(\d+))?', f)
                e[names.index(m.group(1))] += int(m.group(3) or 1)
        terms.append(((sg * c) % p, e))
    polys.append(terms)
with open(sys.argv[2], 'w') as out:
    out.write('import Lean6.Special.Comp.K4.C4.GB\n\nopen Lean6.Special.Comp\n\n')
    out.write('def kcF : List (Poly Nat) := [\n')
    out.write(',\n'.join('  [' + ', '.join('(%d, [%s])' % (c, ', '.join(map(str, e))) for c, e in P) + ']' for P in polys))
    out.write(']\n\n')
    out.write('''#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  let st ← IO.lazyPure (fun _ => GB.run %d %d 10000000 1000000000 kcF)
  let t1 ← IO.monoMsNow
  IO.println s!"basis {st.basis.size}, active {st.act.length}, pairs left {st.pairs.length}, found {st.found}, {t1 - t0} ms"
  for i in st.act do
    IO.println s!"LEAD {st.lead.getD i []}"
''' % (p, len(names)))
print('ok', len(polys), 'polynomials in', len(names), 'variables, p =', p)
