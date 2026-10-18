"""Census of Proposition 9.19: cells of Proposition 4.5 with a clique as in Corollary 9.18.

Usage: python3 -I -B clique_census.py CONCEPT_SCRIPTS ENGINE_RUNS GENERIC_OPEN SINGULAR_ONLY

Reuses the clique bookkeeping of the conceptual note (CONCEPT_SCRIPTS = the directory of cliques.py, zwexcess.py and
cell_killers.py, whose one_colour_killer is the cell-level test of Corollary 9.18 for z- and w-cliques; read-only, run with -B so that nothing is written there) on the stored cells
ENGINE_RUNS/*/exact6/c*/cells.jsonl (a cell's number is its line number, from 0), and prints: the total, the classes all of whose cells are covered, and the
status of the cells listed in GENERIC_OPEN (the 43 open cells; tab-separated class, CC, cell) and of the cells given as class:cell in
SINGULAR_ONLY (comma separated).
"""
import glob, json, re, sys

sys.path.insert(0, sys.argv[1])
import cliques as CQ
import zwexcess as ZX
import cell_killers as CK

runs, open_path, single = sys.argv[2], sys.argv[3], sys.argv[4]
want = {}
for line in open(open_path):
    f = line.rstrip('\n').split('\t')
    if line.startswith('#') or len(f) < 3:
        continue
    want[(int(f[0]), int(f[2]))] = 'open'
for item in single.split(','):
    c, k = item.split(':')
    want[(int(c), int(k))] = 'singular-only'
tot = kil = three = 0
per = {}
status = {}
for fpath in sorted(glob.glob(runs + '/*/exact6/c*/cells.jsonl')):
    ci = int(re.search(r'/c(\d+)/cells', fpath).group(1))
    c = CQ.cls[ci]
    # Corollary 9.18 for zw-cliques, read off the diagram: three bodies with dim L^z, dim L^w <= 2 and
    # dim L^z + dim L^w <= 3 (excess >= 1 in the note's terms), or four bodies with dim L^z, dim L^w <= 1.
    zwk = any((e['r'] == 3 and e['excess'] >= 1) or (e['r'] == 4 and e['dz'] == 0 and e['dw'] == 0)
              for e in ZX.excess(c))
    its = [it for it in CQ.info(c) if it['kind'] in ('z', 'w') and len(it['K']) in (3, 4)]
    zwk3 = any(e['r'] == 3 and e['excess'] >= 1 for e in ZX.excess(c))
    for idx, line in enumerate(open(fpath)):
        cell = json.loads(line)
        k = zwk or any(CK.one_colour_killer(it, cell['argmin']) for it in its)
        three += zwk3 or any(len(it['K']) == 3 and CK.one_colour_killer(it, cell['argmin']) for it in its)
        tot += 1
        kil += k
        r = per.setdefault(ci, [0, 0])
        r[0] += 1
        r[1] += k
        if (ci, idx) in want:
            status[(ci, idx)] = k
print(f'cells {tot}; with a clique {kil}; without {tot - kil}; with a three-body clique {three}; '
      f'with a four-body clique only {kil - three}')
full = sorted(c for c, (n, k) in per.items() if n and n == k)
print(f'classes all of whose cells have a clique ({len(full)}):', full)
for key in sorted(want):
    print(want[key], key, 'clique' if status.get(key) else ('no clique' if key in status else 'NOT FOUND'))
