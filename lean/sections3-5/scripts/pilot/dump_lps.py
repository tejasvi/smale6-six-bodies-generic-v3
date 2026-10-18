#!/usr/bin/env python3
"""Pilot tool (untrusted): run the engine's search (texact.enumerate_cells, mode le, base identities) on one class and
part, and write every LP it solves, with the verdict of the floating-point solver, as integer rows (all data times 2).
Format, one LP per block:
  LP <n> <m> <verdict 1=kept 0=pruned>
  <c> <lo|x> <hi|x> <a_0> ... <a_{n-1}>      (m lines)
Usage: dump_lps.py ENGINE_TYPES_DIR N6_JSON CLASS PART NPARTS OUT [MAXLP]"""
import json, sys
sys.path.insert(0, sys.argv[1])
import tengine as T
import texact as X

cls = json.load(open(sys.argv[2]))['classes']
ci, part, nparts, outp = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
maxlp = int(sys.argv[7]) if len(sys.argv) > 7 else 10 ** 12
out = open(outp, 'w')
count = [0]
orig = T.feasible


def num(x):
    v = 2 * x
    assert v == int(v), x
    return str(int(v))


def dumping(L):
    ok, sol = orig(L)
    if count[0] < maxlp:
        n = L.ns
        out.write(f'LP {n} {len(L.rows)} {1 if ok else 0}\n')
        for coefs, lo, hi in L.rows:
            a = [0] * n
            c = 0
            for j, v in coefs.items():
                if j == n:
                    c = v
                else:
                    a[j] += v
            out.write(' '.join([num(c), 'x' if lo is None else num(lo), 'x' if hi is None else num(hi)] + [num(v) for v in a]) + '\n')
    count[0] += 1
    if count[0] >= maxlp:
        raise StopIteration
    return ok, sol


T.feasible = dumping
X.T.feasible = dumping
D = T.Diagram.from_json(6, cls[ci])
gf = lambda name: (name[0] in ('z', 'w') and len(name[2]) == 1) or name[0] in ('U', 'I')
import io
try:
    st = X.enumerate_cells(D, io.StringIO(), 3, part, nparts, groups_filter=gf, mode='le')
except StopIteration:
    st = 'stopped at MAXLP'
out.close()
print(json.dumps({'class': ci, 'part': part, 'lps': count[0], 'stats': st}))
