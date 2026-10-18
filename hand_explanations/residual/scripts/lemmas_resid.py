#!/usr/bin/env python3
"""Combinatorial checkers of the residual lemmas of RESIDUAL.md on one cell (trees + argmin sets + exact LP
certificates for secondary identities). Each checker returns a witness (dict) or None.

Notation: colours 'z', 'w'; A[(c, k)] = the minimal terms of body k's c-equation: 'pos' and partner indices j
(force C_kj); T_c the c-tree; v-children; 'O-child' = the child of v containing O (or O itself).
  B0   binary, one body in the origin's child in one colour            (every mass)
  K    Kepler binary with one extra force                                (every mass)
  R1*  centred triangle (centre of mass of clusters, or a subset sum)   (generic; R(ab;s) and its cluster form)
  W3   triangle balanced at two vertices with its c-shape fixed by centre relations   (generic)
  L    Lagrange triangle: three-body CC in one colour, centred and balanced at s in the other  (every positive mass)
  EQ2  centred triangle with a doubly positioned vertex                  (generic; m_a M_A^2 = +-m_b M_B^2)
  TQ   torque of a centred pair against a Kepler pair                    (generic; positive zeros only on
       {m_k1 = m_k2, m_l1 = m_l2})
  TD   the engine's torque single term, re-certified exactly             (every mass)
"""
import itertools, os, sys
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exactlp as X

N, O = 6, 6
OTHER = {'z': 'w', 'w': 'z'}


class Ctx:
    def __init__(self, rec, D):
        self.rec = rec
        self.D = D
        self._P = None
        self.T = {'z': X.Tree(rec['ztree']), 'w': X.Tree(rec['wtree'])}
        self.A = {}
        self.AU = None
        for nm, labs in rec['argmin']:
            if nm[0] in ('z', 'w'):
                k = nm[2][0]
                s = set()
                for l in labs:
                    s.add('pos' if l[0] == 'pos' else l[2])
                self.A[(nm[0], k)] = frozenset(s)
            elif nm[0] == 'U':
                self.AU = frozenset(tuple(l) for l in labs)
        assert len(self.A) == 12, len(self.A)

    @property
    def P(self):
        """the exact cell polyhedron (built on first use: only the secondary-identity checks need it)."""
        if self._P is None:
            self._P = X.Poly(self.rec, self.D)
        return self._P

    # tree helpers
    def meet(self, c, p, q):
        return self.T[c].meet(p, q)

    def ochild(self, c, v):
        return self.T[c].child_of(v, O)

    def child(self, c, v, p):
        return self.T[c].child_of(v, p)

    def in_ochild(self, c, v, k):
        """k lies in the child of v containing O, or sits at O."""
        return self.T[c].at_O(k) or (self.child(c, v, k) is not None and self.child(c, v, k) == self.ochild(c, v))

    def common_node(self, c, tri):
        a, b, s = tri
        v = self.meet(c, a, b)
        if v is None or self.meet(c, b, s) != v or self.meet(c, a, s) != v:
            return None
        return v

    def bodies_below(self, c, node):
        return [p for p in self.T[c].below(node) if p != O]


# ------------------------------------------------------------------ B0 and K (every mass)

def lemma_B0(C):
    for cp in 'zw':
        c = OTHER[cp]
        for l in range(N):
            for k in range(N):
                if k == l:
                    continue
                if C.A[(cp, l)] != frozenset({'pos', k}):
                    continue
                v = C.meet(cp, l, k)
                if v is None or v != C.meet(cp, l, O) or not C.in_ochild(cp, v, k):
                    continue
                if C.A[(c, l)] != frozenset({'pos', k}):
                    continue
                u = C.meet(c, l, k)
                if u is None or u != C.meet(c, l, O):
                    continue
                if C.in_ochild(c, u, k):
                    continue
                return {'k': k, 'l': l, 'colour_origin': cp, 'colour_contra': c}
    return None


def lemma_K(C):
    for cp in 'zw':
        c = OTHER[cp]
        for k, l in itertools.combinations(range(N), 2):
            if C.A[(cp, k)] != frozenset({'pos', l}) or C.A[(cp, l)] != frozenset({'pos', k}):
                continue
            v = C.meet(cp, k, l)
            if v is None or C.meet(cp, k, O) != v or C.meet(cp, l, O) != v:
                continue
            u = C.meet(c, k, l)
            if u is None or C.meet(c, k, O) != u or C.meet(c, l, O) != u:
                continue
            for p, q in ((k, l), (l, k)):
                if C.A[(c, p)] != frozenset({'pos', q}):
                    continue
                extra = set(C.A[(c, q)]) - {'pos', p}
                if 'pos' in C.A[(c, q)] and p in C.A[(c, q)] and len(extra) == 1:
                    j = extra.pop()
                    return {'pair': (k, l), 'binary_colour': cp, 'colour': c, 'clean': p, 'extra_on': q, 'j': j}
    return None


# ------------------------------------------------------------------ Lemma S (sums of initial forms) helpers

def lemmaS_sets(C, c, node):
    """Sets K of bodies whose c-equations all have the position as minimal term at exponent h(node)
    (meet_c(k, O) = node) and whose minimal forces come from K only: the connected components of the force graph
    among such bodies that are closed. Returns a list of frozensets."""
    cand = [k for k in range(N) if C.meet(c, k, O) == node and 'pos' in C.A[(c, k)]]
    cs = set(cand)
    adj = {k: {j for j in C.A[(c, k)] if j != 'pos'} for k in cand}
    out, seen = [], set()
    for k in cand:
        if k in seen:
            continue
        comp, stack = set(), [k]
        ok = True
        while stack:
            x = stack.pop()
            if x in comp:
                continue
            comp.add(x)
            for j in adj[x]:
                if j not in cs:
                    ok = False
                else:
                    stack.append(j)
        seen |= comp
        if ok:
            out.append(frozenset(comp))
    return out


def centre_relations(C, c, node):
    """Linear relations among the coordinates of the non-O children of `node` in colour c, valid on the cell:
    (full) the centre of mass, if node is the root; (S) Lemma S for every closed set K at this node.
    Each relation: dict child -> list of bodies (masses add up), plus a tag."""
    rels = []
    T = C.T[c]
    oc = C.ochild(c, node)
    if node == T.root:
        r = {}
        for ch in T.children[node]:
            if ch == oc:
                continue
            bs = [p for p in T.below(ch) if p != O] if ch in T.children else [p for p, lf in T.leaf.items()
                                                                              if lf == ch and p != O]
            r[ch] = bs
        rels.append(('full', r))
    for K in lemmaS_sets(C, c, node):
        r = {}
        for k in K:
            r.setdefault(C.child(c, node, k), []).append(k)
        rels.append(('S', r, tuple(sorted(K))))
    return rels


# ------------------------------------------------------------------ R1* (generic)

def lemma_R1star(C, try_subset=True):
    for c in 'zw':
        cb = OTHER[c]
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
                # centre relation for the coordinates of ca, cbb only
                for rel in centre_relations(C, c, v):
                    r = rel[1]
                    if rel[0] == 'full':
                        extra = [ch for ch in r if ch not in (ca, cbb)]
                        # eliminate extra children by Lemma S sets lying entirely in extra children
                        sub = []
                        for rel2 in centre_relations(C, c, v):
                            if rel2[0] == 'S' and all(ch in extra for ch in rel2[1]):
                                sub.append(rel2)
                        covered = {}
                        for rel2 in sub:
                            for ch, bs in rel2[1].items():
                                covered.setdefault(ch, []).extend(bs)
                        if all(sorted(covered.get(ch, [])) == sorted(r[ch]) for ch in extra):
                            if ca in r and cbb in r:
                                return {'colour': c, 'a': a, 'b': b, 's': s, 'MA': sorted(r[ca]), 'MB': sorted(r[cbb]),
                                        'centre': 'full' if not extra else 'full-minus-S',
                                        'S_sets': [x[2] for x in sub]}
                    else:
                        if set(r) == {ca, cbb}:
                            return {'colour': c, 'a': a, 'b': b, 's': s, 'MA': sorted(r[ca]), 'MB': sorted(r[cbb]),
                                    'centre': 'S', 'S_sets': [rel[2]]}
                if try_subset:
                    for J in candidate_J(C, c, v, tri):
                        S = [('pos', k) for k in J if not C.in_ochild(c, v, k) and C.meet(c, k, O) == v]
                        if not S or not any(l == ('pos', a) for l in S) or not any(l == ('pos', b) for l in S):
                            continue
                        if any(C.child(c, v, k) not in (ca, cbb) for (_, k) in S):
                            continue
                        terms = C.P.subset_terms(c, J)
                        ok, cert = C.P.argmin_is(terms, S)
                        if ok:
                            MA = sorted(k for (_, k) in S if C.child(c, v, k) == ca)
                            MB = sorted(k for (_, k) in S if C.child(c, v, k) == cbb)
                            return {'colour': c, 'a': a, 'b': b, 's': s, 'MA': MA, 'MB': MB, 'centre': 'subset',
                                    'J': list(J), 'cert': cert}
    return None


def candidate_J(C, c, v, tri):
    a, b, s = tri
    cands = [tuple(sorted(tri)), tuple(sorted(C.bodies_below(c, v)))]
    out = []
    for J in cands:
        if 2 <= len(J) <= 4 and J not in out:
            out.append(J)
    return out


# ------------------------------------------------------------------ W3 (generic)

def lemma_W3(C):
    for c in 'zw':
        cb = OTHER[c]
        T = C.T[c]
        for tri in itertools.combinations(range(N), 3):
            v = C.common_node(c, tri)
            if v is None or C.common_node(cb, tri) is None:
                continue
            bal = [k for k in tri if C.A[(c, k)] == frozenset(set(tri) - {k})]
            if len(bal) < 2:
                continue
            if C.ochild(c, v) is None or any(C.in_ochild(c, v, k) for k in tri):
                continue
            chs = [C.child(c, v, k) for k in tri]
            rels = centre_relations(C, c, v)
            if not rels:
                continue
            # unknowns: all non-O children of v that occur
            allch = sorted({ch for rel in rels for ch in rel[1]} | set(chs))
            M = [[rel[1].get(ch, []) for ch in allch] for rel in rels]
            # need: the solution space projected to chs is one-dimensional (checked symbolically elsewhere);
            # here a rank test at random rational masses
            if shape_rank_ok(M, allch, chs):
                return {'colour': c, 'tri': list(tri), 'balanced': bal, 'children': allch, 'tri_children': chs,
                        'relations': [(rel[0], {str(ch): bs for ch, bs in rel[1].items()}) for rel in rels]}
    return None


def shape_rank_ok(M, allch, chs, trials=3):
    import random
    rng = random.Random(1)
    for _ in range(trials):
        m = [Fr(rng.randint(2, 97)) for _ in range(N)]
        A = [[sum(m[k] for k in cell) for cell in row] for row in M]
        ns = nullspace(A, len(allch))
        idx = [allch.index(ch) for ch in chs]
        proj = [[vec[i] for i in idx] for vec in ns]
        # rank of projection must be 1 and the projected vectors must have all entries nonzero
        if rank(proj) != 1 or len(ns) != 1:
            return False
        if any(x == 0 for x in proj[0]):
            return False
    return True


def rank(A):
    A = [r[:] for r in A]
    if not A:
        return 0
    rk, ncol = 0, len(A[0])
    for col in range(ncol):
        piv = next((i for i in range(rk, len(A)) if A[i][col] != 0), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        for i in range(len(A)):
            if i != rk and A[i][col] != 0:
                f = A[i][col] / A[rk][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk


def nullspace(A, n):
    A = [r[:] for r in A]
    piv_cols, rk = [], 0
    for col in range(n):
        piv = next((i for i in range(rk, len(A)) if A[i][col] != 0), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        pv = A[rk][col]
        A[rk] = [x / pv for x in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][col] != 0:
                f = A[i][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[rk])]
        piv_cols.append(col)
        rk += 1
    free = [j for j in range(n) if j not in piv_cols]
    out = []
    for fj in free:
        vec = [Fr(0)] * n
        vec[fj] = Fr(1)
        for r, pc in enumerate(piv_cols):
            vec[pc] = -A[r][fj]
        out.append(vec)
    return out


# ------------------------------------------------------------------ L (every positive mass)

def lemma_L(C):
    for c in 'zw':
        cb = OTHER[c]
        for s in range(N):
            for a, b in itertools.combinations([x for x in range(N) if x != s], 2):
                tri = (a, b, s)
                v = C.common_node(c, tri)
                vb = C.common_node(cb, tri)
                if v is None or vb is None:
                    continue
                okc = all(C.A[(c, k)] == frozenset({'pos'} | (set(tri) - {k})) and C.meet(c, k, O) == v for k in tri)
                if not okc:
                    continue
                if C.ochild(cb, vb) is None or not C.in_ochild(cb, vb, s):
                    continue
                if C.in_ochild(cb, vb, a) or C.in_ochild(cb, vb, b):
                    continue
                if C.A[(cb, s)] != frozenset({a, b}):
                    continue
                if C.A[(cb, a)] != frozenset({'pos', s, b}) or C.A[(cb, b)] != frozenset({'pos', s, a}):
                    continue
                if C.meet(cb, a, O) != vb or C.meet(cb, b, O) != vb:
                    continue
                return {'cc_colour': c, 'a': a, 'b': b, 's': s}
    return None


# ------------------------------------------------------------------ EQ2 (generic)

def lemma_EQ2(C):
    for c in 'zw':
        cb = OTHER[c]
        for s in range(N):
            for a, b in itertools.permutations([x for x in range(N) if x != s], 2):
                tri = (a, b, s)
                v = C.common_node(c, tri)
                vb = C.common_node(cb, tri)
                if v is None or vb is None:
                    continue
                if C.ochild(c, v) is None or not C.in_ochild(c, v, s):
                    continue
                if C.in_ochild(c, v, a) or C.in_ochild(c, v, b):
                    continue
                if C.ochild(cb, vb) is None or not C.in_ochild(cb, vb, s):
                    continue
                if C.in_ochild(cb, vb, a) or C.in_ochild(cb, vb, b):
                    continue
                if C.A[(c, s)] != frozenset({a, b}):
                    continue
                if C.A[(c, a)] != frozenset({'pos', s, b}) or C.A[(cb, a)] != frozenset({'pos', s, b}):
                    continue
                if C.meet(c, a, O) != v or C.meet(cb, a, O) != vb:
                    continue
                ca, cbb = C.child(c, v, a), C.child(c, v, b)
                for rel in centre_relations(C, c, v):
                    r = rel[1]
                    if set(r) == {ca, cbb}:
                        return {'colour': c, 'a': a, 'b': b, 's': s, 'MA': sorted(r[ca]), 'MB': sorted(r[cbb]),
                                'centre': rel[0]}
    return None


# ------------------------------------------------------------------ TQ (generic)

def lemma_TQ(C):
    for c in 'zw':
        cb = OTHER[c]
        T = C.T[c]
        root = T.root
        oc = C.ochild(c, root)
        nono = [ch for ch in T.children[root] if ch != oc]
        if len(nono) != 2:
            continue
        L1 = [p for p in T.below(nono[0]) if p != O] if nono[0] in T.children else \
            [p for p, lf in T.leaf.items() if lf == nono[0] and p != O]
        L2 = [p for p in T.below(nono[1]) if p != O] if nono[1] in T.children else \
            [p for p, lf in T.leaf.items() if lf == nono[1] and p != O]
        if len(L1) != 1 or len(L2) != 1:
            continue
        l1, l2 = L1[0], L2[0]
        for k1, k2 in itertools.combinations([x for x in range(N) if x not in (l1, l2)], 2):
            if not (C.in_ochild(c, root, k1) and C.in_ochild(c, root, k2)):
                continue
            vb = C.meet(cb, k1, k2)
            if vb is None or C.meet(cb, k1, O) != vb or C.meet(cb, k2, O) != vb:
                continue
            if frozenset({k1, k2}) not in lemmaS_sets(C, cb, vb):
                continue
            if not (C.in_ochild(cb, vb, l1) and C.in_ochild(cb, vb, l2)):
                continue
            # torque T_{l1,l2}: minimal terms = the four (l, k) terms with z from colour c side
            J = (l1, l2)
            terms = C.P.torque_terms(J)
            if c == 'z':
                S = [('zw', l, k) for l in J for k in (k1, k2)]
            else:
                S = [('zw', k, l) for l in J for k in (k1, k2)]
            ok, cert = C.P.argmin_is(terms, S)
            if ok:
                return {'colour': c, 'l': [l1, l2], 'k': [k1, k2], 'J': list(J), 'cert': cert}
    return None


# ------------------------------------------------------------------ TD: engine torque single term re-certified

def lemma_TD(C, J, lab):
    terms = C.P.torque_terms(J)
    ok, cert = C.P.argmin_is(terms, [lab])
    return {'J': list(J), 'term': lab, 'cert': cert} if ok else None
