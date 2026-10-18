"""For the template cores (B, LIN, P4): the hand-computed condition agrees with the engine's label (labels_all.jsonl):
every engine generator vanishes on the hand condition's zero set? We test the converse direction that matters:
the radical of the engine's ideal equals the hand condition. Practical test: each engine generator is divisible by
(or a polynomial multiple of) the hand polynomial, and the hand polynomial divides some generator's factorization."""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
from corefam import classify, M
from collections import Counter
R = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'inputs') + '/'
lab = {json.loads(l)['hash']: json.loads(l) for l in open(R + 'labels_all.jsonl')}
LOC = {str(v): v for v in M}
res = Counter(); bad = []
seen = {}
for l in open('../data/cores_h.jsonl'):
    r = json.loads(l)
    if r['certified'] is not True: continue
    h = r.get('hash_old') or r['hash']
    if h in seen:
        res[seen[h]] += 1; continue
    f, x = classify(r['names'], r['core_sym'])
    if f is None:
        seen[h] = ('none',); res[('none',)] += 1; continue
    hand = [sp.expand(p) for p in x if not isinstance(p, tuple)]
    L = lab.get(h)
    if L is None or not L.get('gens'):
        seen[h] = (f, 'nolabel'); res[(f, 'nolabel')] += 1; continue
    gens = [sp.expand(sp.sympify(g.replace('^', '**'), locals=LOC)) for g in L['gens']]
    # irreducible factors (non-monomial) of the engine generators and of the hand polynomials
    def facs(p):
        return set(sp.factor_list(p)[1][i][0] for i in range(len(sp.factor_list(p)[1])))
    def nonmono(S):
        return {sp.expand(q) for q in S if not sp.Poly(q, *M).is_monomial and not q.is_number}
    hf = set()
    for p in hand:
        hf |= nonmono(facs(p))
    gf = [nonmono(facs(g)) for g in gens]
    # agreement: the engine ideal's zero set equals the hand zero set iff (single generator case) same factor sets
    norm = lambda S: {q if sp.Poly(q, *M).LC() > 0 else -q for q in S}
    hf = norm(hf); gf = [norm(S) for S in gf]
    if len(gens) == 1 and gf[0] == hf:
        key = (f, 'equal')
    elif any(S == hf for S in gf):
        key = (f, 'one generator equal')
    elif all(S >= hf or not S.isdisjoint(hf) for S in gf):
        key = (f, 'shares factors')
    else:
        key = (f, 'DIFFERENT')
        bad.append((h, [str(q) for q in hf], [[str(q) for q in S] for S in gf]))
    seen[h] = key; res[key] += 1
print(res)
for b in bad[:10]: print(b)
