"""Group all cores (first-pass certified + alt) by canonical relation pattern (bodies relabelled, colours swapped)
and label type. Output data/core_patterns.json and per-core pattern ids data/core_pat_ids.jsonl."""
import json, sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coreparse import relation
from collections import Counter, defaultdict
ctype = {}
for l in open('../data/core_types.jsonl'):
    r = json.loads(l); ctype[r['hash']] = r
S = json.load(open('../data/core_types_summary.json'))
tnames = {}
for i, (k, v) in enumerate(sorted(S.items(), key=lambda t: -t[1]['cells'])): tnames[k] = 'L%d' % i
SW = {'z': 'w', 'w': 'z'}
def relabel(rel, p, sw):
    """apply body permutation p (dict) and colour swap sw to a relation."""
    c = (lambda x: SW[x]) if sw else (lambda x: x)
    P = lambda k: p[k]
    pr = lambda e: tuple(sorted((P(e[0]), P(e[1]))))
    k = rel[0]
    if k == 'dist': return ('dist', pr(rel[1]))
    if k == 'bal': return ('bal', c(rel[1]), P(rel[2]), rel[3], tuple(sorted(P(x) for x in rel[4])))
    if k == 'sum':
        J = set(P(x) for x in rel[2])
        if len(J) > 3:  # complement for canonical
            pass
        return ('sum', c(rel[1]), tuple(sorted(J)), tuple(sorted(P(x) for x in rel[3])), rel[4], tuple(sorted(pr(e) for e in rel[5])))
    if k == 'U': return ('U', tuple(sorted(pr(e) for e in rel[1])), rel[2])
    if k == 'V': return ('V', tuple(sorted(P(x) for x in rel[1])), tuple(sorted(pr(e) for e in rel[2])), tuple(sorted(P(x) for x in rel[3])), rel[4])
    if k == 'T': return ('T', tuple(sorted(P(x) for x in rel[1])), tuple(sorted(tuple((P(a), P(b))) for a, b in rel[2])))
    if k == 'Diff': return ('Diff', c(rel[1]), pr(rel[2]), rel[3], tuple(sorted(pr(e) for e in rel[4])))
    if k in ('Ip', 'I'): return (k, tuple(sorted(P(x) for x in rel[1])), rel[2])
    return rel
def bodies(rel):
    s = set()
    def add(x):
        if isinstance(x, int): s.add(x)
        elif isinstance(x, (tuple, list)):
            for y in x: add(y)
    for x in rel[1:]:
        if isinstance(x, (tuple, list, int)) and not isinstance(x, bool): add(x)
    return s
def canon(rels):
    B = sorted(set().union(*[bodies(r) for r in rels]))
    best = None
    for perm in itertools.permutations(range(len(B))):
        p = {B[i]: perm[i] for i in range(len(B))}
        for sw in (False, True):
            key = repr(sorted(repr(relabel(r, p, sw)) for r in rels))
            if best is None or key < best: best = key
    return best
pats = defaultdict(lambda: {'cells': 0, 'classes': Counter(), 'labels': Counter(), 'ex': None})
out = open('../data/core_pat_ids.jsonl', 'w')
for l in open('../data/cores_h.jsonl'):
    r = json.loads(l)
    if r['certified'] is False: continue
    rels = [relation(n, e) for n, e in zip(r['names'], r['core_sym'])]
    key = canon(rels)
    h = r.get('hash_old') or r['hash']
    lab = tnames.get(ctype[h]['type'], '?') + ':' + ctype[h]['status'] if (r['certified'] is True and h in ctype) else 'alt'
    d = pats[key]; d['cells'] += 1; d['classes'][r['class']] += 1; d['labels'][lab] += 1
    if d['ex'] is None: d['ex'] = (r['class'], r['cell'], r['names'], r['core_sym'])
    out.write(json.dumps({'class': r['class'], 'cell': r['cell'], 'pattern': key, 'label': lab}) + '\n')
res = sorted(pats.items(), key=lambda t: -t[1]['cells'])
json.dump([{'pattern': k, 'cells': v['cells'], 'classes': dict(v['classes']), 'labels': dict(v['labels']), 'ex': v['ex']} for k, v in res],
          open('../data/core_patterns.json', 'w'), indent=1)
print(len(res), 'patterns')
for k, v in res[:50]:
    print(v['cells'], dict(v['labels']), k[:230])
