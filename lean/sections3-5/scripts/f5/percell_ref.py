"""Per-cell output of the census program of the paper (tools/clique_census.py), for comparison with the Lean census.

Usage: python3 -B percell_ref.py CONCEPT_SCRIPTS ENGINE_RUNS

Imports the clique bookkeeping of the conceptual note (CONCEPT_SCRIPTS = the directory of cliques.py, zwexcess.py and
cell_killers.py, read-only) and evaluates, for each stored cell ENGINE_RUNS/*/exact6/c<N>/cells.jsonl (cell k = line
k), the same expressions as clique_census.py: `k` (a clique as in Corollary 5.8) and `three` (one of three bodies).
Prints `none <class> <cell>` for each cell without a clique, `four <class> <cell>` for each cell with a clique but no
clique of three bodies, and a final line with the totals. Untrusted helper: only used to compare with the Lean output.
"""
import glob, json, re, sys

sys.path.insert(0, sys.argv[1])
import cliques as CQ
import zwexcess as ZX
import cell_killers as CK

runs = sys.argv[2]
tot = kil = three = 0
for fpath in sorted(glob.glob(runs + '/*/exact6/c*/cells.jsonl'), key=lambda p: int(re.search(r'/c(\d+)/cells', p).group(1))):
    ci = int(re.search(r'/c(\d+)/cells', fpath).group(1))
    c = CQ.cls[ci]
    zwk = any((e['r'] == 3 and e['excess'] >= 1) or (e['r'] == 4 and e['dz'] == 0 and e['dw'] == 0)
              for e in ZX.excess(c))
    its = [it for it in CQ.info(c) if it['kind'] in ('z', 'w') and len(it['K']) in (3, 4)]
    zwk3 = any(e['r'] == 3 and e['excess'] >= 1 for e in ZX.excess(c))
    for idx, line in enumerate(open(fpath)):
        cell = json.loads(line)
        k = zwk or any(CK.one_colour_killer(it, cell['argmin']) for it in its)
        t = zwk3 or any(len(it['K']) == 3 and CK.one_colour_killer(it, cell['argmin']) for it in its)
        tot += 1
        kil += bool(k)
        three += bool(t)
        if not k:
            print(f'none {ci} {idx}')
        elif not t:
            print(f'four {ci} {idx}')
print(f'total cells {tot} clique {kil} three {three}')
