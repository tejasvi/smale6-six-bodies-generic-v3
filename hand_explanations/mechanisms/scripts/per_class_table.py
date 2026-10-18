#!/usr/bin/env python3
"""Producer of data/per_class_table.md (added in v2; the table itself dates from the refereed version): one row per
diagram class with nonpositive cells, in decreasing order of the number of cells (ties in the order in which the
classes first occur in data/coverage.jsonl), with Chang-Chen's label (`diagrams/cc_compare.json`,
'–' for classes without one), the class diagram (`diagrams/n6.json`) and the number of cells per
first-applicable lemma of data/coverage.jsonl. Read-only on the engine data.
Usage: per_class_table.py [OUT]  (default: standard output)"""
import json, os, sys
from collections import Counter

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')
ENUM = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'diagrams')
# columns: header -> value of 'first' in coverage.jsonl
COLS = [('E', 'E'), ('T', 'T'), ('P', 'P'), ('C', 'C'), ('E1', 'E1'), ('R1', 'R1'), ('R6', 'R6'), ('Q', 'Q'),
        ('LIN', 'coreLIN-generic'), ('LIN*', 'coreLIN-all'), ('P4', 'coreP4'), ('d64', 'd64'), ('d88', 'd88'),
        ('d98', 'd98'), ('comp', 'comp')]


def diag_str(cl):
    s = ' '.join(f'{k}:{v}' for k, v in cl['edges'].items())
    if cl['zcircles']:
        s += ' zc' + ''.join(map(str, cl['zcircles']))
    if cl['wcircles']:
        s += ' wc' + ''.join(map(str, cl['wcircles']))
    return s


def main():
    classes = json.load(open(os.path.join(ENUM, 'n6.json')))['classes']
    cc = {r['ours']: r['cc'] for r in json.load(open(os.path.join(ENUM, 'cc_compare.json')))['per_cc']}
    pc = {}
    for l in open(os.path.join(DATA, 'coverage.jsonl')):
        r = json.loads(l)
        pc.setdefault(r['class'], Counter())[r['first']] += 1
    known = {f for _, f in COLS}
    other = {f for v in pc.values() for f in v} - known
    assert not other, other          # every first-applicable value has a column
    out = ['| class | CC | diagram (1 z-, 2 w-, 3 zw-edge; circles) | cells | '
           + ' | '.join(h for h, _ in COLS) + ' |',
           '|' + '---|' * (4 + len(COLS))]
    for c, v in sorted(pc.items(), key=lambda t: -sum(t[1].values())):
        row = [str(c), str(cc[c]) if c in cc else '–', diag_str(classes[c]), str(sum(v.values()))]
        row += [str(v[f]) if v[f] else '' for _, f in COLS]
        out.append('| ' + ' | '.join(row) + ' |')
    text = '\n'.join(out) + '\n'
    if len(sys.argv) > 1:
        open(sys.argv[1], 'w').write(text)
    else:
        sys.stdout.write(text)


if __name__ == '__main__':
    main()
