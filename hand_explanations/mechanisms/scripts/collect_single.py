#!/usr/bin/env python3
"""Collect the single-term exclusions (tsec_exact 'excluded_by') of all classes, joined with the cell data.
Output: data/single.jsonl, one line per excluded cell: class, cell, identity, term, ztree, wtree, argmin, x, sumx.
Also data/systems_index.jsonl: (class, cell, file, line) of the cells that carry a system (core cells).
Read-only on the engine data."""
import glob, json, os, sys
from collections import Counter

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')


def main():
    dirs = sorted(glob.glob(os.path.join(ROOT, '*', 'exact6', 'c*')))
    fs = open(os.path.join(OUT, 'single.jsonl'), 'w')
    fi = open(os.path.join(OUT, 'systems_index.jsonl'), 'w')
    tot = Counter()
    for d in dirs:
        c = int(d.rsplit('/c', 1)[1])
        cells_path = os.path.join(d, 'cells.jsonl')
        if not os.path.exists(cells_path) or os.path.getsize(cells_path) == 0:
            continue
        excl = {}
        sysidx = {}
        for f in glob.glob(os.path.join(d, 'sec', 'p*.sec.jsonl')):
            with open(f) as fh:
                for ln, line in enumerate(fh):
                    head = line[:400]
                    if '"excluded_by"' in head:
                        r = json.loads(line)
                        excl[r['cell']] = r['excluded_by']
                    else:
                        # only parse the cell id
                        j = head.index('"cell": ') + 8
                        k = head.index(',', j)
                        sysidx[int(head[j:k])] = (f, ln)
        with open(cells_path) as fh:
            for i, line in enumerate(fh):
                if i in excl:
                    cell = json.loads(line)
                    rec = {'class': c, 'cell': i, 'identity': excl[i]['identity'], 'term': excl[i]['term'],
                           'ztree': cell['ztree'], 'wtree': cell['wtree'], 'argmin': cell['argmin'], 'x': cell['x'],
                           'sumx': cell['sumx'], 'hz': cell['hz'], 'hw': cell['hw']}
                    fs.write(json.dumps(rec) + '\n')
                    tot['single'] += 1
                elif i in sysidx:
                    fi.write(json.dumps({'class': c, 'cell': i, 'file': sysidx[i][0], 'line': sysidx[i][1]}) + '\n')
                    tot['system'] += 1
                else:
                    tot['missing'] += 1
        print(c, len(excl), len(sysidx), flush=True)
    fs.close()
    fi.close()
    print(dict(tot))


if __name__ == '__main__':
    main()
