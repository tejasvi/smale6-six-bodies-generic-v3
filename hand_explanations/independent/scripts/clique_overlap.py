"""Per-cell clique flags (paper Prop. 5.9 census, reusing the census code read-only) vs the referee's E/E1 flags."""
import glob, json, re, sys, os
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'cliques'))
import cliques as CQ
import zwexcess as ZX
import cell_killers as CK
from collections import Counter
runs = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')
mine = {}
for l in open('ref_cover.jsonl'):
    r = json.loads(l); mine[(r['class'], r['cell'])] = r
cnt = Counter()
for fpath in sorted(glob.glob(runs + '/*/exact6/c*/cells.jsonl')):
    ci = int(re.search(r'/c(\d+)/cells', fpath).group(1))
    c = CQ.cls[ci]
    zwk = any((e['r'] == 3 and e['excess'] >= 1) or (e['r'] == 4 and e['dz'] == 0 and e['dw'] == 0) for e in ZX.excess(c))
    its = [it for it in CQ.info(c) if it['kind'] in ('z', 'w') and len(it['K']) in (3, 4)]
    for idx, line in enumerate(open(fpath)):
        cell = json.loads(line)
        k = zwk or any(CK.one_colour_killer(it, cell['argmin']) for it in its)
        m = mine[(ci, idx)]
        e1 = bool(m['E1']) or bool(m['Eclass'])
        cnt[('clique', k, 'E/E1', e1)] += 1
print(dict(cnt))
print('clique:', sum(v for kk, v in cnt.items() if kk[1]), ' E/E1:', sum(v for kk, v in cnt.items() if kk[3]),
      ' union:', sum(v for kk, v in cnt.items() if kk[1] or kk[3]))
