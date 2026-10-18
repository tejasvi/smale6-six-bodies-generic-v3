#!/usr/bin/env python3
"""Which centre relations does Lemma R1* use on the cells (RESIDUAL_v2.md §4, referee item R3)?
The checker lemma_R1star (lemmas_resid.py) accepts, for a triangle (a, b, s) satisfying (R1)-(R3), the centre
relation (alpha) 'full' (v the root with three children), (beta) 'full-minus-S' (v the root; the bodies of the other
non-O children covered by Lemma-S sets lying in these children) and a third branch 'S' (one Lemma-S set at v whose
bodies lie below A and B only), and on the residual cells (gamma) a subset sum. It returns the first witness only.
Here every (colour, s, a, b) is tried without the subset sum, and the branches available on each cell are recorded.
Output ../data/r1star_branches_v2.json."""
import glob, itertools, json, os, sys, time
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rkit as R
import exactlp as X
import lemmas_resid as LR

N, O = LR.N, LR.O


def branches(C):
    out = set()
    for c in 'zw':
        cb = LR.OTHER[c]
        for s in range(N):
            for a, b in itertools.combinations([x for x in range(N) if x != s], 2):
                tri = (a, b, s)
                v = C.common_node(c, tri)
                if v is None or C.common_node(cb, tri) is None:
                    continue
                if C.ochild(c, v) is None or not C.in_ochild(c, v, s):
                    continue
                if C.in_ochild(c, v, a) or C.in_ochild(c, v, b):
                    continue
                if C.A[(c, a)] != frozenset({s, b}) or C.A[(c, b)] != frozenset({s, a}):
                    continue
                ca, cbb = C.child(c, v, a), C.child(c, v, b)
                rels = LR.centre_relations(C, c, v)
                for rel in rels:
                    r = rel[1]
                    if rel[0] == 'full':
                        extra = [ch for ch in r if ch not in (ca, cbb)]
                        covered = {}
                        for rel2 in rels:
                            if rel2[0] == 'S' and all(ch in extra for ch in rel2[1]):
                                for ch, bs in rel2[1].items():
                                    covered.setdefault(ch, []).extend(bs)
                        if all(sorted(covered.get(ch, [])) == sorted(r[ch]) for ch in extra) and ca in r and cbb in r:
                            out.add('alpha' if not extra else 'beta')
                    elif set(r) == {ca, cbb}:
                        out.add('S')
    return out


def main():
    cnt = Counter()
    cls = R.classes()
    t0 = time.time()
    n = 0
    for d in sorted(glob.glob(os.path.join(R.ENG, '*', 'exact6', 'c*'))):
        c = int(d.rsplit('/c', 1)[1])
        pth = os.path.join(d, 'cells.jsonl')
        if not os.path.exists(pth) or os.path.getsize(pth) == 0:
            continue
        D = X.Diag(cls[c])
        for line in open(pth):
            rec = json.loads(line)
            rec['class'] = c
            br = branches(LR.Ctx(rec, D))
            cnt['branches ' + (','.join(sorted(br)) if br else 'none')] += 1
            cnt['R1* without subset sum'] += bool(br)
            cnt['R1* by alpha or beta'] += bool(br & {'alpha', 'beta'})
            cnt['R1* only by the S branch'] += (br == {'S'})
            n += 1
            if n % 10000 == 0:
                print(n, round(time.time() - t0), flush=True)
    cnt['cells'] = n
    summary = dict(sorted(cnt.items()))
    json.dump(summary, open(os.path.join(R.DATA, 'r1star_branches_v2.json'), 'w'), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    main()
