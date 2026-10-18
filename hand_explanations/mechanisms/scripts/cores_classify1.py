import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'engine'))
import tcorehash as H
from collections import Counter
cert = {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'inputs', 'certified_cores.jsonl')):
    r = json.loads(l); cert[r['hash']] = r
def abstract(nm):
    t = eval(nm)
    if t[0] == 'D' and len(t) == 3: return 'dist'
    if t[0] in ('z', 'w') and t[1] == 'S': return 'B' + t[0]
    if t[0] == 'S': return 'S%s%d' % (t[1], len(t[2]))
    if t[0] == 'T': return 'T%d' % min(len(t[1]), 6 - len(t[1]))
    if t[0] == 'V': return 'V%d' % len(t[1])
    if t[0] == 'D': return 'Diff' + t[1]
    return t[0]
pat = Counter(); patcells = Counter(); certc = Counter(); sizes = Counter()
out = open('../data/cores_h.jsonl', 'w')
for l in open('../data/cores.jsonl'):
    r = json.loads(l)
    old, new = H.hashes(r['core_sym'])
    ok = (new in cert) or (old in cert)
    if old in cert: r["hash_old"] = old
    if r['source'] != 'first': ok = 'alt'
    certc[ok] += 1
    a = tuple(sorted(abstract(n) for n in r['names']))
    # colour-symmetric canonical form
    a2 = tuple(sorted(x.replace('z', '#').replace('w', 'z').replace('#', 'w') for x in a))
    key = min(a, a2)
    pat[key] += 1
    sizes[r['size']] += 1
    r['hash'] = new; r['certified'] = ok
    out.write(json.dumps(r) + '\n')
print(certc)
print(sorted(sizes.items()))
for k, v in pat.most_common(60): print(v, k)
print(len(pat))
