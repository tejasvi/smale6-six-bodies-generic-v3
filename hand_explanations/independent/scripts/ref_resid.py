#!/usr/bin/env python3
"""Referee's independent checkers for the lemmas of RESIDUAL.md (B0, K, L, R1*, W3, EQ2, TQ), written from the
statements. Secondary-identity hypotheses ((gamma) of R1*, (T3) of TQ, TD) are returned as LP obligations and
discharged separately (ref_resid_lp.py)."""
import itertools
from fractions import Fraction
from refkit import O, BODIES

COLS = ('z', 'w')


def oc(col):
    return 'w' if col == 'z' else 'z'


def pos(k):
    return ('pos', k)


def cr(k, l):
    return ('cross', k, l)


def ochild(tr, v):
    """the child of v containing O (None if O is not below v)"""
    return tr.child_to(v, O)


def in_ochild(tr, v, k):
    """k lies in the O-child of v or sits at O"""
    if tr.at_origin(k):
        return True
    c = ochild(tr, v)
    return c is not None and tr.child_to(v, k) == c


# ---------------------------------------------------------------- B0
def lemma_B0(C):
    out = []
    for y in COLS:
        x = oc(y)
        ty, tx = C.tree(y), C.tree(x)
        for l in BODIES:
            for k in BODIES:
                if k == l:
                    continue
                if C.A[(y, l)] != frozenset({pos(l), cr(l, k)}) or C.A[(x, l)] != frozenset({pos(l), cr(l, k)}):
                    continue
                if ty.at_origin(l) or tx.at_origin(l):
                    continue
                v = ty.meet(l, k)
                if v != ty.meet(l, O) or not in_ochild(ty, v, k):
                    continue
                u = tx.meet(l, k)
                if u != tx.meet(l, O) or tx.at_origin(k):
                    continue
                if tx.child_to(u, k) == ochild(tx, u):
                    continue
                out.append((y, l, k))
    return out


# ---------------------------------------------------------------- K
def three_children(tr, p, q):
    """p, q, O in three distinct children of one node: returns the node or None"""
    if tr.at_origin(p) or tr.at_origin(q):
        return None
    v = tr.meet(p, q)
    if tr.meet(p, O) != v or tr.meet(q, O) != v:
        return None
    cs = {tr.child_to(v, p), tr.child_to(v, q), tr.child_to(v, O)}
    return v if len(cs) == 3 else None


def lemma_K(C):
    out = []
    for y in COLS:
        x = oc(y)
        for k, l in itertools.combinations(BODIES, 2):
            if C.A[(y, k)] != frozenset({pos(k), cr(k, l)}) or C.A[(y, l)] != frozenset({pos(l), cr(l, k)}):
                continue
            if three_children(C.tree(y), k, l) is None or three_children(C.tree(x), k, l) is None:
                continue
            for p, q in ((k, l), (l, k)):
                if C.A[(x, p)] != frozenset({pos(p), cr(p, q)}):
                    continue
                Aq = C.A[(x, q)]
                if pos(q) in Aq and cr(q, p) in Aq and len(Aq) == 3:
                    j = [t[2] for t in Aq if t[0] == 'cross' and t[2] != p]
                    if len(j) == 1 and j[0] not in (k, l):
                        out.append((y, p, q, j[0]))
    return out


# ---------------------------------------------------------------- L
def lemma_L(C):
    out = []
    for y in COLS:
        x = oc(y)
        ty, tx = C.tree(y), C.tree(x)
        for T in itertools.combinations(BODIES, 3):
            v = ty.meet(T[0], T[1])
            if v is None or ty.meet(T[0], T[2]) != v or ty.meet(T[1], T[2]) != v:
                continue
            co = ochild(ty, v)
            chs = [ty.child_to(v, k) for k in T]
            if co is None or len(set(chs)) != 3 or co in chs:
                continue
            if not all(C.A[(y, k)] == frozenset({pos(k)} | {cr(k, j) for j in T if j != k}) for k in T):
                continue
            vb = tx.meet(T[0], T[1])
            if vb is None or tx.meet(T[0], T[2]) != vb or tx.meet(T[1], T[2]) != vb:
                continue
            if len({tx.child_to(vb, k) for k in T}) != 3:
                continue
            for s in T:
                a, b = [k for k in T if k != s]
                if not in_ochild(tx, vb, s):
                    continue
                if tx.at_origin(a) or tx.at_origin(b) or tx.meet(a, O) != vb or tx.meet(b, O) != vb:
                    continue
                if in_ochild(tx, vb, a) or in_ochild(tx, vb, b):
                    continue
                if C.A[(x, s)] != frozenset({cr(s, a), cr(s, b)}):
                    continue
                if C.A[(x, a)] != frozenset({pos(a), cr(a, s), cr(a, b)}):
                    continue
                if C.A[(x, b)] != frozenset({pos(b), cr(b, s), cr(b, a)}):
                    continue
                out.append((y, T, s))
    return out


# ---------------------------------------------------------------- Lemma-S sets and centre relations
def lemma_S_sets(C, y, v):
    """maximal sets K of bodies, each with pos minimal in its y-equation and meet_y(k, O) = v, such that every force
    term of A_k^y (k in K) comes from K, and K is connected by those forces (closed components)."""
    tr = C.tree(y)
    cand = [k for k in BODIES if not tr.at_origin(k) and tr.meet(k, O) == v and pos(k) in C.A[(y, k)]]
    cs = set(cand)
    # union-find on force partners
    comp = {k: {k} for k in cand}
    for k in cand:
        for t in C.A[(y, k)]:
            if t[0] == 'cross':
                j = t[2]
                if j in cs and comp[j] is not comp[k]:
                    m = comp[k] | comp[j]
                    for i in m:
                        comp[i] = m
    sets = []
    for k in cand:
        K = comp[k]
        if K in sets:
            continue
        closed = all(t[0] == 'pos' or t[2] in K for i in K for t in C.A[(y, i)])
        if closed:
            sets.append(K)
    return [frozenset(K) for K in sets]


def mass_vec(bodies):
    v = [0] * 6
    for k in bodies:
        v[k] = 1
    return tuple(v)


def centre_relations(C, y, v):
    """linear relations among the coordinates X(u) of the non-O children u of node v (relative to the O-child):
    each relation is a dict child -> mass vector (coefficient = sum of masses of the listed bodies).
    (i) full centre of mass if v is the root; (ii) each Lemma-S set at v."""
    tr = C.tree(y)
    co = ochild(tr, v)
    rels = []
    if v == tr.root:
        rel = {}
        for u in tr.ch[v]:
            if u == co:
                continue
            bs = [k for k in tr.pts[u] if k != O]
            rel[u] = mass_vec(bs)
        rels.append(('full', rel))
    for K in lemma_S_sets(C, y, v):
        rel = {}
        for k in K:
            u = tr.child_to(v, k)
            rel.setdefault(u, [])
            rel[u].append(k)
        rels.append(('S', {u: mass_vec(bs) for u, bs in rel.items()}, tuple(sorted(K))))
    return rels


# ---------------------------------------------------------------- R1*
def lemma_R1star(C):
    """returns list of (y, (a,b,s), how, MA-bodies, MB-bodies); how in alpha/beta, or ('gamma', J) as obligation"""
    out = []
    for y in COLS:
        x = oc(y)
        ty, tx = C.tree(y), C.tree(x)
        for T in itertools.combinations(BODIES, 3):
            v = ty.meet(T[0], T[1])
            if v is None or ty.meet(T[0], T[2]) != v or ty.meet(T[1], T[2]) != v:
                continue
            vb = tx.meet(T[0], T[1])
            if vb is None or tx.meet(T[0], T[2]) != vb or tx.meet(T[1], T[2]) != vb:
                continue
            if len({ty.child_to(v, k) for k in T}) != 3 or len({tx.child_to(vb, k) for k in T}) != 3:
                continue
            co = ochild(ty, v)
            if co is None:
                continue
            for s in T:
                a, b = sorted(k for k in T if k != s)
                if not in_ochild(ty, v, s):
                    continue
                A_, B_ = ty.child_to(v, a), ty.child_to(v, b)
                if A_ == co or B_ == co:
                    continue
                if C.A[(y, a)] != frozenset({cr(a, s), cr(a, b)}) or C.A[(y, b)] != frozenset({cr(b, s), cr(b, a)}):
                    continue
                belowA = sorted(k for k in ty.pts[A_] if k != O)
                belowB = sorted(k for k in ty.pts[B_] if k != O)
                # (alpha)
                if v == ty.root and len(ty.ch[v]) == 3:
                    out.append((y, (a, b, s), 'alpha', tuple(belowA), tuple(belowB)))
                    continue
                # (beta): root; the bodies of the other non-O children are a disjoint union of Lemma-S sets
                if v == ty.root:
                    others = set()
                    for u in ty.ch[v]:
                        if u not in (co, A_, B_):
                            others |= {k for k in ty.pts[u] if k != O}
                    Ssets = [K for K in lemma_S_sets(C, y, v) if K <= others]
                    cover = set()
                    disjoint = True
                    for K in Ssets:
                        if cover & K:
                            disjoint = False
                        cover |= K
                    if disjoint and cover == others:
                        out.append((y, (a, b, s), 'beta', tuple(belowA), tuple(belowB)))
                        continue
                # (gamma): obligation for every J with J below A or B nonempty on both sides (checked by LP)
                out.append((y, (a, b, s), 'gamma?', tuple(belowA), tuple(belowB)))
    return out


# ---------------------------------------------------------------- W3
def nullspace_Q(rows, ncols):
    """rational null space of a matrix given as list of lists of Fractions"""
    M = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [e * inv for e in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [Fraction(0)] * ncols
        v[f] = Fraction(1)
        for i, c in enumerate(piv):
            v[c] = -M[i][f]
        basis.append(v)
    return basis


def lemma_W3(C, masses_list):
    """(W1), (W2), and the one-dimensionality of the restricted solution space at every mass vector of masses_list
    (random rationals; the symbolic shape is computed in sympy separately). Returns (y, T, v, relations)."""
    out = []
    for y in COLS:
        x = oc(y)
        ty, tx = C.tree(y), C.tree(x)
        for T in itertools.combinations(BODIES, 3):
            v = ty.meet(T[0], T[1])
            if v is None or ty.meet(T[0], T[2]) != v or ty.meet(T[1], T[2]) != v:
                continue
            vb = tx.meet(T[0], T[1])
            if vb is None or tx.meet(T[0], T[2]) != vb or tx.meet(T[1], T[2]) != vb:
                continue
            co = ochild(ty, v)
            chs = [ty.child_to(v, k) for k in T]
            if co is None or len(set(chs)) != 3 or co in chs or len({tx.child_to(vb, k) for k in T}) != 3:
                continue
            bal = [k for k in T if C.A[(y, k)] == frozenset({cr(k, j) for j in T if j != k})]
            if len(bal) < 2:
                continue
            rels = centre_relations(C, y, v)
            if not rels:
                continue
            kids = [u for u in ty.ch[v] if u != co]
            ok = True
            for ms in masses_list:
                rows = []
                for rel in rels:
                    d = rel[1]
                    rows.append([sum(Fraction(ms[k]) * d.get(u, (0,) * 6)[k] for k in range(6)) for u in kids])
                ns = nullspace_Q(rows, len(kids))
                idx = [kids.index(u) for u in chs]
                proj = [[vec[i] for i in idx] for vec in ns]
                # dimension of the projection of the solution space onto the three children of T
                rk = rank_Q(proj)
                if rk != 1:
                    ok = False
                    break
            if ok:
                out.append((y, T, v, [r[0] if r[0] == 'full' else ('S', r[2]) for r in rels], tuple(bal)))
    return out


def rank_Q(vecs):
    M = [list(r) for r in vecs]
    if not M:
        return 0
    n = len(M[0])
    r = 0
    for c in range(n):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        for i in range(r + 1, len(M)):
            if M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r


# ---------------------------------------------------------------- EQ2
def lemma_EQ2(C, masses_list):
    out = []
    for y in COLS:
        x = oc(y)
        ty, tx = C.tree(y), C.tree(x)
        for T in itertools.combinations(BODIES, 3):
            v = ty.meet(T[0], T[1])
            if v is None or ty.meet(T[0], T[2]) != v or ty.meet(T[1], T[2]) != v:
                continue
            vb = tx.meet(T[0], T[1])
            if vb is None or tx.meet(T[0], T[2]) != vb or tx.meet(T[1], T[2]) != vb:
                continue
            if len({ty.child_to(v, k) for k in T}) != 3 or len({tx.child_to(vb, k) for k in T}) != 3:
                continue
            if ochild(ty, v) is None or ochild(tx, vb) is None:
                continue
            for s in T:
                if not (in_ochild(ty, v, s) and in_ochild(tx, vb, s)):
                    continue
                for a in T:
                    if a == s:
                        continue
                    b = [k for k in T if k not in (a, s)][0]
                    if in_ochild(ty, v, a) or in_ochild(ty, v, b) or in_ochild(tx, vb, a) or in_ochild(tx, vb, b):
                        continue
                    if C.A[(y, s)] != frozenset({cr(s, a), cr(s, b)}):
                        continue
                    want = frozenset({pos(a), cr(a, s), cr(a, b)})
                    if C.A[(y, a)] != want or C.A[(x, a)] != want:
                        continue
                    if ty.meet(a, O) != v or tx.meet(a, O) != vb:
                        continue
                    # (E2): a relation between X(c(a)) and X(c(b)) alone, derivable from the centre relations at v:
                    # the solution space of the relations, projected to (X(c(a)), X(c(b))), is one-dimensional
                    rels = centre_relations(C, y, v)
                    co = ochild(ty, v)
                    kids = [u for u in ty.ch[v] if u != co]
                    ca, cb = ty.child_to(v, a), ty.child_to(v, b)
                    ok = bool(rels)
                    for ms in masses_list:
                        if not ok:
                            break
                        rows = [[sum(Fraction(ms[k]) * r[1].get(u, (0,) * 6)[k] for k in range(6)) for u in kids]
                                for r in rels]
                        ns = nullspace_Q(rows, len(kids))
                        proj = [[vec[kids.index(ca)], vec[kids.index(cb)]] for vec in ns]
                        if rank_Q(proj) != 1:
                            ok = False
                    if ok:
                        out.append((y, (s, a, b)))
    return out


# ---------------------------------------------------------------- TQ (combinatorial part; (T3) is an LP obligation)
def lemma_TQ(C):
    out = []
    for y in COLS:
        x = oc(y)
        ty, tx = C.tree(y), C.tree(x)
        r = ty.root
        co = ochild(ty, r)
        if co is None or len(ty.ch[r]) != 3:
            continue
        others = [u for u in ty.ch[r] if u != co]
        single = []
        for u in others:
            bs = [k for k in ty.pts[u] if k != O]
            if len(bs) != 1:
                break
            single.append(bs[0])
        if len(single) != 2:
            continue
        l1, l2 = sorted(single)
        for k1, k2 in itertools.combinations([k for k in BODIES if k not in (l1, l2)], 2):
            if not (in_ochild(ty, r, k1) and in_ochild(ty, r, k2)):
                continue
            vb = three_children(tx, k1, k2)
            if vb is None:
                continue
            if not (in_ochild(tx, vb, l1) and in_ochild(tx, vb, l2)):
                continue
            Ss = lemma_S_sets(C, x, vb)
            if frozenset({k1, k2}) not in Ss:
                continue
            out.append((y, (l1, l2), (k1, k2)))
    return out
