#!/usr/bin/env python3
"""Referee's independent implementation of the hypothesis checks of MECHANISMS.md (E, E1, R1, R5, R6, Q, T, P, C, B).
Written from the lemma statements, not from concept/mechanisms/scripts/lemmas.py."""
import itertools
from refkit import O, BODIES

TRIS = list(itertools.combinations(BODIES, 3))


def pair(k, l):
    return (k, l) if k < l else (l, k)


# ------------------------------------------------------------------ Lemma E (class level)
def lemma_E_class(D):
    """a zw-triangle whose vertices carry no circle (either colour) and no stroke (either colour) besides the three
    pairs of the triangle."""
    out = []
    for T in TRIS:
        prs = [pair(a, b) for a, b in itertools.combinations(T, 2)]
        if not all(p in D.zw for p in prs):
            continue
        if any(k in D.zc or k in D.wc for k in T):
            continue
        bad = False
        for e in D.z | D.w:
            if e in prs:
                continue
            if e[0] in T or e[1] in T:
                bad = True
        if not bad:
            out.append(T)
    return out


# ------------------------------------------------------------------ triangle helpers
def one_node(tr, T):
    a, b, c = T
    v = tr.meet(a, b)
    if v is None or tr.meet(a, c) != v or tr.meet(b, c) != v:
        return None
    return v


def is_balanced(C, col, k, T):
    o = [j for j in T if j != k]
    return C.A[(col, k)] == frozenset({('cross', k, o[0]), ('cross', k, o[1])})


def U_is_T(C, T):
    return C.A['U'] == frozenset({('delta',) + pair(a, b) for a, b in itertools.combinations(T, 2)})


def lemma_E1(C):
    """returns (main, uvariant): lists of triangles where (H1)+(H2) hold, resp. (H1) + B_z, B_w nonempty + A_U = T."""
    main, uvar = [], []
    for T in TRIS:
        if one_node(C.zt, T) is None or one_node(C.wt, T) is None:
            continue
        bz = [k for k in T if is_balanced(C, 'z', k, T)]
        bw = [k for k in T if is_balanced(C, 'w', k, T)]
        if (len(bz) >= 2 and len(bw) >= 1) or (len(bw) >= 2 and len(bz) >= 1):
            main.append(T)
        elif bz and bw and U_is_T(C, T):
            uvar.append(T)
    return main, uvar


def is_centred(C, col, T, s):
    """s is col-centred: at the common node v of T in the col-tree, a and b are the only points of their children,
    and s, O and every body outside T lie in one further child (so v is the root with three children)."""
    tr = C.tree(col)
    v = one_node(tr, T)
    if v is None:
        return False
    a, b = [k for k in T if k != s]
    ca, cb, cs = tr.child_to(v, a), tr.child_to(v, b), tr.child_to(v, s)
    if tr.pts[ca] != frozenset({a}) or tr.pts[cb] != frozenset({b}):
        return False
    rest = frozenset(set(range(7)) - {a, b})
    return tr.pts[cs] == rest


def lemma_R1(C):
    main, var = [], []
    for T in TRIS:
        if one_node(C.zt, T) is None or one_node(C.wt, T) is None:
            continue
        for col in 'zw':
            for s in T:
                if not is_centred(C, col, T, s):
                    continue
                a, b = [k for k in T if k != s]
                na = is_balanced(C, col, a, T)
                nb = is_balanced(C, col, b, T)
                if na and nb:
                    main.append((T, col, s))
                elif (na or nb) and U_is_T(C, T):
                    var.append((T, col, s))
    return main, var


def lemma_R5(C):
    out = []
    for T in TRIS:
        if one_node(C.zt, T) is None or one_node(C.wt, T) is None or not U_is_T(C, T):
            continue
        for col in 'zw':           # col: balance colour; centre in the other colour
            oc = C.other(col)
            for s in T:
                if not is_centred(C, oc, T, s):
                    continue
                for a in T:
                    if a != s and is_balanced(C, col, a, T):
                        out.append((T, col, s, a))
    return out


def lemma_R6(C):
    out = []
    for T in TRIS:
        if one_node(C.zt, T) is None or one_node(C.wt, T) is None:
            continue
        for col in 'zw':           # centre and balance at s in col, balance at a in the other colour
            oc = C.other(col)
            for s in T:
                if not (is_centred(C, col, T, s) and is_balanced(C, col, s, T)):
                    continue
                for a in T:
                    if a != s and is_balanced(C, oc, a, T):
                        out.append((T, col, s, a))
    return out


def lemma_Q(C):
    out = []
    for col in 'zw':
        for s in BODIES:
            A = C.A[(col, s)]
            if len(A) < 2 or any(t[0] != 'cross' for t in A):
                continue
            K = sorted(t[2] for t in A)
            ok = True
            for tr in (C.zt, C.wt):
                vs = {tr.meet(s, k) for k in K}
                if len(vs) != 1:
                    ok = False
                    break
                v = vs.pop()
                if len({tr.child_to(v, k) for k in K}) != 1:
                    ok = False
                    break
            if ok:
                out.append((col, s, tuple(K)))
    return out


# ------------------------------------------------------------------ Lemma T
def torque_sets():
    for r in range(1, 6):
        for J in itertools.combinations(BODIES, r):
            if 0 in J:
                yield J


def torque_terms(C, J):
    """ordered cross pairs (p, q) whose term z_p w_q exists."""
    Jc = [j for j in BODIES if j not in J]
    out = []
    for k in J:
        for l in Jc:
            for p, q in ((k, l), (l, k)):
                if C.zt.at_origin(p) or C.wt.at_origin(q):
                    continue
                out.append((p, q))
    return out


def lemma_T_literal(C):
    """(Z), (W), (S) of Lemma T, read literally. Returns list of (J, (p,q))."""
    res = []
    zt, wt = C.zt, C.wt
    for J in torque_sets():
        Jc = [j for j in BODIES if j not in J]
        cross = [(k, l) for k in J for l in Jc]
        terms = torque_terms(C, J)
        sig = {}
        for p, q in terms:
            sig[(p, q)] = (zt.meet(p, q), zt.meet(p, O), wt.meet(p, q), wt.meet(q, O))
        for p, q in terms:
            tz, uz, tw, uw = sig[(p, q)]
            if not zt.is_anc(uz, tz) or not wt.is_anc(uw, tw):
                continue
            if not all(zt.is_anc(zt.meet(k, l), tz) for k, l in cross):
                continue
            if not all(wt.is_anc(wt.meet(k, l), tw) for k, l in cross):
                continue
            if any(sig[t] == sig[(p, q)] for t in terms if t != (p, q)):
                continue
            res.append((J, (p, q)))
    return res


def expo_torque(C, p, q):
    """exponent of z_p w_q delta_pq^3 as a linear form {('z', node) or ('w', node): coef}."""
    f = {}

    def add(key, c):
        f[key] = f.get(key, 0) + c
    add(('z', C.zt.meet(p, O)), 1)
    add(('w', C.wt.meet(q, O)), 1)
    add(('z', C.zt.meet(p, q)), -1.5)
    add(('w', C.wt.meet(p, q)), -1.5)
    return f


def subtree_vector(C, p, q):
    """subtree sums (non-root internal nodes of both trees) of the exponent form of z_p w_q delta_pq^3:
    S(n) = sum of the coefficients at nodes below or equal to n. Root sums are -1/2 in each tree for every term."""
    zt, wt = C.zt, C.wt
    uz, tz = zt.meet(p, O), zt.meet(p, q)
    uw, tw = wt.meet(q, O), wt.meet(p, q)
    v = []
    for tr, u, t in ((zt, uz, tz), (wt, uw, tw)):
        for n in tr.internal:
            if n == tr.root:
                continue
            v.append((2 if tr.is_anc(n, u) else 0) - (3 if tr.is_anc(n, t) else 0))   # doubled to stay integral
    return tuple(v)


def lemma_T_domination(C):
    """the term t0 of T_J is below every other term by tree order alone: exponent(t) - exponent(t0) is a nonnegative
    combination of the edge increments h(child) - h(parent) (all > 0 on the open cell), not identically zero."""
    res = []
    for J in torque_sets():
        terms = torque_terms(C, J)
        if len(terms) < 2:
            continue
        vec = {t: subtree_vector(C, *t) for t in terms}
        mn = tuple(min(col) for col in zip(*vec.values()))
        cands = [t for t in terms if vec[t] == mn]
        if len(cands) == 1:
            res.append((J, cands[0]))
    return res


# ------------------------------------------------------------------ positivity of x on a pair
def forced_positive_pairs(C, D):
    out = set(D.zw)                                    # (x1)
    for e in D.z:                                      # (x2)
        if e[0] not in D.zc and e[1] not in D.zc:
            out.add(e)
    for e in D.w:
        if e[0] not in D.wc and e[1] not in D.wc:
            out.add(e)
    AU = C.A['U']                                      # (x3)
    if ('E',) not in AU:
        for t in AU:
            assert t[0] == 'delta'
            out.add(pair(t[1], t[2]))
    for col in 'zw':                                   # (x4)
        tr = C.tree(col)
        for k in BODIES:
            A = C.A[(col, k)]
            if ('pos', k) in A or tr.at_origin(k):
                continue
            u = tr.meet(k, O)
            for t in A:
                if t[0] == 'cross' and tr.meet(k, t[2]) == u:
                    out.add(pair(k, t[2]))
    return out


def lemma_P(C, D):
    pos = forced_positive_pairs(C, D)
    wit = []
    for k in BODIES:
        if C.zt.at_origin(k) or C.wt.at_origin(k):
            continue
        found = None
        for l in BODIES:
            if l == k or pair(k, l) not in pos:
                continue
            if O in C.zt.pts[C.zt.meet(k, l)] and O in C.wt.pts[C.wt.meet(k, l)]:
                found = l
                break
        if found is None:
            return None
        wit.append((k, found))
    return wit


# ------------------------------------------------------------------ Lemma C
def lemma_C(C):
    res = []
    for col in 'zw':
        tr = C.tree(col)
        for r in range(2, 6):
            for J in itertools.combinations(BODIES, r):
                Js = set(J)
                # graph
                adj = {i: set() for i in J}
                for i, l in itertools.combinations(J, 2):
                    Ai, Al = C.A[(col, i)], C.A[(col, l)]
                    e = False
                    if ('cross', i, l) in Ai and ('cross', l, i) in Al:
                        e = True
                    if ('pos', i) in Ai and ('pos', l) in Al and tr.meet(i, O) == tr.meet(l, O):
                        e = True
                    if e:
                        adj[i].add(l)
                        adj[l].add(i)
                seen, st = {J[0]}, [J[0]]
                while st:
                    v = st.pop()
                    for u in adj[v]:
                        if u not in seen:
                            seen.add(u)
                            st.append(u)
                if seen != Js:
                    continue
                X = []
                for i in J:
                    for t in C.A[(col, i)]:
                        if t[0] == 'pos':
                            X.append(t)
                        elif t[0] == 'cross' and t[2] not in Js:
                            X.append(t)
                if len(X) == 1:
                    res.append((col, J, 'single', X[0]))
                    continue
                if X and all(t[0] == 'pos' for t in X):
                    keys = set()
                    for t in X:
                        i = t[1]
                        assert not tr.at_origin(i)
                        v = tr.meet(i, O)
                        keys.add((v, tr.child_to(v, i)))
                    if len(keys) == 1:
                        res.append((col, J, 'merged', tuple(sorted(t[1] for t in X))))
    return res


# ------------------------------------------------------------------ Lemma B
def lemma_B(C, D):
    pos = forced_positive_pairs(C, D)
    res = []
    for col in 'zw':
        for k, l in itertools.combinations(BODIES, 2):
            Ak, Al = C.A[(col, k)], C.A[(col, l)]
            if ('cross', k, l) not in Ak or ('cross', l, k) not in Al:
                continue
            if not Ak <= {('cross', k, l), ('pos', k)} or not Al <= {('cross', l, k), ('pos', l)}:
                continue
            if (k, l) in pos:
                res.append((col, k, l))
    return res
