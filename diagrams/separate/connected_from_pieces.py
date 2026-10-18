"""Connected N-body diagram classes (all rules) from my own piece list data/pieces_kN.json: impose E1, E5 and
identify colour-exchanged pieces. Usage: connected_from_pieces.py N OUT.json"""
import sys, json
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from zwlib import canon
n = int(sys.argv[1])
d = json.load(open(f'data/pieces_k{n}.json'))
seen = {}
for c in d['classes']:
    E = {(int(k[0]), int(k[1])): v for k, v in c['edges'].items()}
    if not any(t & 1 for t in E.values()) or not any(t & 2 for t in E.values()):
        continue
    if sum(1 for t in E.values() if t == 3) == 1:
        continue
    g = canon(n, E, frozenset(c['zcircles']), frozenset(c['wcircles']))
    seen[g] = seen.get(g, 0) + c['labelled']
out = []
for g, lab in sorted(seen.items()):
    ne, cz, cw = g
    out.append({'edges': {f'{a}{b}': t for a, b, t in ne}, 'zcircles': list(cz), 'wcircles': list(cw), 'labelled': lab})
json.dump({'n': n, 'classes': out}, open(sys.argv[2], 'w'), indent=1)
print(f'n={n}: {len(out)} connected classes, {sum(x["labelled"] for x in out)} labelled')
