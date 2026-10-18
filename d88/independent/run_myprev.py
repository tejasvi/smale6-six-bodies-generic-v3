#!/usr/bin/env python3
"""Driver: referee's independent prevariety of the author's G (gfan input file), then the distinct face vectors
(= cones of the common refinement inside Prev(G)), each with an exact relative-interior point.
Writes JSON with, per distinct face vector: point w (min convention), the faces, dimension of the span.
Usage: run_myprev.py GFAN_INPUT OUT.json
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import myprev


def main():
    gf, out = sys.argv[1], sys.argv[2]
    names, polys = myprev.parse_gfan(gf)
    n = len(names)
    supports = [sorted(p.keys()) for p in polys]
    order = sorted(range(len(polys)), key=lambda i: (len(supports[i]), i))
    t0 = time.time()
    logf = open(out + '.log', 'w')

    def log(s):
        logf.write('%.1fs %s\n' % (time.time() - t0, s))
        logf.flush()
    cells = myprev.prevariety(supports, n, order, log=log)
    groups = {}
    for c in cells:
        key = tuple(sorted(c.faces))
        if key not in groups:
            groups[key] = {'w': c.w, 'dim': len(c.basis), 'faces': [[gi, list(F)] for gi, F in sorted(c.faces)],
                           'ncells': 0}
        groups[key]['ncells'] += 1
    res = {'names': names, 'n_polys': len(polys), 'n_cells': len(cells), 'n_face_vectors': len(groups),
           'dims': {}, 'stats': myprev.STATS, 'time': time.time() - t0,
           'face_vectors': list(groups.values())}
    for g in groups.values():
        res['dims'][g['dim']] = res['dims'].get(g['dim'], 0) + 1
    json.dump(res, open(out, 'w'))
    log('done: %d cells, %d distinct face vectors, dims %s' % (len(cells), len(groups), res['dims']))


if __name__ == '__main__':
    main()
