#!/usr/bin/env python3
"""Turns the output of L6Check/F5/Print.lean in a build log into the Lean literals of L6Check/F5/Census.lean:
* default: `L6F5.table` from the lines `class cells clique three four forced` (possibly after an
  `info: <file>:<line>:<col>: ` prefix), 191 entries `⟨cells, clique, three, four, forced⟩`, the class c at position c;
* `--open`: `L6F5.openTable` from the printed value of `openStatus` (entries `(class, diagram, cell, status)`).
Untrusted helper: the theorems `census_table` and `open_status` re-check the literals against the Lean census.
Usage: gen_table.py BUILD_LOG [--open]"""
import re, sys


def wrap(items):
    out, cur = [], '  ['
    for i, it in enumerate(items):
        tok = it + (', ' if i < len(items) - 1 else ']')
        if len(cur) + len(tok) > 118:
            out.append(cur.rstrip())
            cur = '   '
        cur += tok
    out.append(cur)
    return '\n'.join(out)


text = open(sys.argv[1]).read()
if '--open' in sys.argv:
    i = text.index('some [(')
    j = text.index(')]', i) + 2
    pat = (r'\((\d+), (\d+), (\d+), \{ clique := (true|false), three := (true|false), four := (true|false) \}\)')
    items = [f'({a}, {b}, {c}, ⟨{d}, {e}, {f}⟩)' for a, b, c, d, e, f in re.findall(pat, text[i:j])]
    assert len(items) == 43, len(items)
    print(wrap(items))
else:
    rows = {}
    for line in text.splitlines():
        m = re.match(r'^(?:info: \S+ )?(\d+) (\d+) (\d+) (\d+) (\d+) (\d+)$', line.strip())
        if m:
            v = list(map(int, m.groups()))
            rows[v[0]] = tuple(v[1:])
    assert sorted(rows) == list(range(191)), sorted(rows)[:5]
    print(wrap([f'⟨{a}, {b}, {c}, {d}, {e}⟩' for (a, b, c, d, e) in (rows[k] for k in range(191))]))
