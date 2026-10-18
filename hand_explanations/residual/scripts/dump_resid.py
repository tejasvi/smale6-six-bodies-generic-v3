#!/usr/bin/env python3
"""Human-readable dump of residual cells: diagram, trees (heights), x, argmin sets, the core or the single term.
Usage: dump_resid.py [CLASS [CELL ...]]   (default: all 115 residual cells) > ../data/resid_dump.txt"""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
from cellkit import Cell, tree_str


def fmt_argmin(argmin):
    out = []
    for name, labs in argmin:
        nm = ''.join(str(x) for x in (name if isinstance(name, list) else [name]))
        terms = []
        for l in labs:
            if l[0] == 'pos':
                terms.append(f'p{l[1]}')
            elif l[0] == 'cross':
                terms.append(f'F{l[1]}{l[2]}')
            elif l[0] == 'delta':
                terms.append(f'd{l[1]}{l[2]}')
            elif l[0] == 'zw':
                terms.append(f'r{l[1]}{l[2]}')
            elif l[0] == 'E':
                terms.append('E')
            else:
                terms.append(str(l))
        out.append(f'{nm}: {" ".join(terms)}')
    return out


def main():
    res = R.residual()
    sel = None
    if len(sys.argv) > 1:
        c0 = int(sys.argv[1])
        cells = [int(a) for a in sys.argv[2:]]
        sel = [(r['class'], r['cell']) for r in res if r['class'] == c0 and (not cells or r['cell'] in cells)]
        if not sel:
            sel = [(c0, i) for i in cells]
    else:
        sel = [(r['class'], r['cell']) for r in res]
    lab = {(r['class'], r['cell']): r for r in res}
    for c, i in sel:
        rec = R.load_cell(c, i)
        C = Cell(rec)
        r = lab.get((c, i), {})
        print(f'=== class {c} cell {i}  [{R.diag_str(c)}]  kind={r.get("kind")} label={r.get("label")}')
        print('  z:', tree_str(C.zt))
        print('  w:', tree_str(C.wt))
        print('  x:', ' '.join(f'{k}:{v:g}' for k, v in sorted(rec['x'].items())), ' sumx', rec['sumx'])
        for s in fmt_argmin(rec['argmin']):
            print('   ', s)
        sg = R.single_of(c, i)
        if sg:
            print('  SINGLE:', sg)
        cr = R.core_of(c, i)
        if cr:
            print('  CORE (', cr.get('source'), '):')
            for n, e in zip(cr['names'], cr['core_sym']):
                print('     ', n, ' : ', e)
        print()


if __name__ == '__main__':
    main()
