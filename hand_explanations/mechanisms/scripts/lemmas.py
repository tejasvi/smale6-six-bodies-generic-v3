#!/usr/bin/env python3
"""Combinatorial checkers for the hand lemmas of MECHANISMS.md. Each checker takes a cellkit.Cell (trees of the cell)
and a cellkit.Diag, and returns a witness (a tuple) if the lemma's hypotheses hold on the cell, else None.
The hypotheses are statements about the two trees, the diagram and the cell's argmin sets only (no heights)."""
import itertools
from cellkit import O, N

BODIES = range(N)


def anc_eq(T, a, b):
    """a is an ancestor of b or equal (nodes)."""
    return a in T.anc(b)


def nonempty_proper_subsets():
    for r in range(1, N):
        for J in itertools.combinations(BODIES, r):
            yield J


# ---------------------------------------------------------------- Lemma T (torque, deepest cross pair)

def lemma_T_witness(C, J):
    """Lemma T for the torque T_J: an ordered cross pair (p, q), p carrying z and q carrying w, with
    (Z) every cross pair meets in the z-tree at an ancestor-or-equal of meet_z(p,q), and meet_z(p,O) is an
        ancestor-or-equal of meet_z(p,q) (a_p <= zeta_pq);
    (W) the same in the w-tree for meet_w(p,q) and meet_w(q,O) (b_q <= omega_pq);
    (S) no other ordered cross pair (k,l) has the same four nodes meet_z(k,l), meet_z(k,O), meet_w(k,l), meet_w(l,O).
    Positions identically zero (a body at O) give no term."""
    zt, wt = C.zt, C.wt
    Jc = [j for j in BODIES if j not in J]
    cross = [(k, l) for k in J for l in Jc]
    terms = []
    for k, l in cross:
        for p, q in ((k, l), (l, k)):
            up = zt.meet(p, O)
            uq = wt.meet(q, O)
            if up is None or uq is None:
                continue
            terms.append((p, q, zt.meet(p, q), up, wt.meet(p, q), uq))
    zmeets = [zt.meet(k, l) for k, l in cross]
    wmeets = [wt.meet(k, l) for k, l in cross]
    for (p, q, tz, uz, tw, uw) in terms:
        if not anc_eq(zt, uz, tz) or not anc_eq(wt, uw, tw):
            continue
        if not all(anc_eq(zt, m, tz) for m in zmeets):
            continue
        if not all(anc_eq(wt, m, tw) for m in wmeets):
            continue
        tie = any((p2, q2) != (p, q) and (tz2, uz2, tw2, uw2) == (tz, uz, tw, uw)
                  for (p2, q2, tz2, uz2, tw2, uw2) in terms)
        if tie:
            continue
        return (p, q)
    return None


def lemma_T(C, D=None):
    for J in nonempty_proper_subsets():
        if 0 not in J:
            continue                      # T_J = -T_{J^c}
        w = lemma_T_witness(C, J)
        if w is not None:
            return (J, w)
    return None


# ---------------------------------------------------------------- argmin data of a cell

def argmins(rec):
    """dict: ('z', i) / ('w', i) -> set of labels of the minimal terms of body i's equation; ('U',), ('I',) -> sets."""
    out = {}
    for nm, labs in rec['argmin']:
        labs = set(tuple(x) for x in labs)
        if nm[0] in ('z', 'w') and nm[1] == 'S' and len(nm[2]) == 1:
            out[(nm[0], nm[2][0])] = labs
        else:
            out[tuple(nm) if not isinstance(nm, str) else (nm,)] = labs
    return out


# ---------------------------------------------------------------- Lemma S (subset sum of a cluster)

def lemma_S_witness(rec, J, col):
    """S_J in colour col = sum over i in J of the equations of i (internal forces cancel). Hypotheses (argmin data):
    every body i of J has its minimal terms recorded; the relation i ~ l (Z_il minimal in i's equation and Z_li minimal
    in l's) connects J, so all the minima are equal; exactly one non-internal term (a position or a force from outside J)
    is minimal in the equations of J. Then S_J has a unique minimal term."""
    A = argmins(rec)
    Js = set(J)
    for i in J:
        if (col, i) not in A:
            return None
    # connectivity by mutual internal minimal forces
    adj = {i: set() for i in J}
    for i in J:
        for lab in A[(col, i)]:
            if lab[0] == 'cross' and lab[2] in Js:
                l = lab[2]
                if ('cross', l, i) in A[(col, l)]:
                    adj[i].add(l)
                    adj[l].add(i)
    seen = {J[0]}
    stack = [J[0]]
    while stack:
        v = stack.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u)
                stack.append(u)
    if seen != Js:
        return None
    ext = []
    for i in J:
        for lab in A[(col, i)]:
            if lab[0] == 'pos' or (lab[0] == 'cross' and lab[2] not in Js):
                ext.append(lab)
    if len(ext) == 1:
        return ext[0]
    return None


def lemma_S(rec, D=None):
    for col in 'zw':
        for r in range(2, N):
            for J in itertools.combinations(BODIES, r):
                w = lemma_S_witness(rec, J, col)
                if w is not None:
                    return (col, J, w)
    return None


# ---------------------------------------------------------------- Lemma P (positive I')

def positive_pairs(D):
    """pairs {k,l} with x_kl > 0 forced by the diagram: zw-edges (x = 1); z-strokes with no z-circled end and
    w-strokes with no w-circled end (zeta (resp. omega) = 3x - 2 > -2)."""
    out = set(D.zw)
    for (k, l) in D.zs:
        if k not in D.zc and l not in D.zc:
            out.add((k, l))
    for (k, l) in D.ws:
        if k not in D.wc and l not in D.wc:
            out.add((k, l))
    return out


def lemma_P(C, D):
    """Every body k (not at O in both colours... a body at O has no term) has a partner l with kl in positive_pairs(D),
    O below meet_z(k,l) and below meet_w(k,l). Then a_k + b_k >= zeta_kl + omega_kl = 2 x_kl > 0 for all k, so the
    identity sum m_k z_k w_k = E has the single minimal term E."""
    pos = positive_pairs(D)
    wit = []
    for k in BODIES:
        if C.zt.meet(k, O) is None or C.wt.meet(k, O) is None:
            wit.append((k, 'O'))
            continue
        found = None
        for l in BODIES:
            if l == k or (min(k, l), max(k, l)) not in pos:
                continue
            if anc_eq(C.zt, C.zt.meet(k, l), C.zt.leaf[O]) and anc_eq(C.wt, C.wt.meet(k, l), C.wt.leaf[O]):
                found = l
                break
        if found is None:
            return None
        wit.append((k, found))
    return tuple(wit)


def positive_pairs_cell(C, D, rec):
    """pairs with x_kl > 0 forced by the diagram or by the cell's argmin data:
    (i) positive_pairs(D);
    (ii) kl in the argmin of U while E is not (x_kl = max x > 0);
    (iii) body k's equation in a colour has the force of l among its minimal terms but not its position, and k's
          position meets O at the meet of k and l in that colour (a_k = zeta_kl, resp. b_k = omega_kl)."""
    out = set(positive_pairs(D))
    A = argmins(rec)
    U = A.get(('U',))
    if U is not None and ('E',) not in U:
        for lab in U:
            out.add((min(lab[1], lab[2]), max(lab[1], lab[2])))
    for col, T in (('z', C.zt), ('w', C.wt)):
        for k in BODIES:
            am = A.get((col, k))
            if am is None or ('pos', k) in am:
                continue
            u = T.meet(k, O)
            if u is None:
                continue
            for lab in am:
                if lab[0] == 'cross' and T.meet(k, lab[2]) == u:
                    l = lab[2]
                    out.add((min(k, l), max(k, l)))
    return out


def lemma_P2(C, D, rec):
    """Lemma P with x_kl > 0 also from the argmin data (positive_pairs_cell)."""
    pos = positive_pairs_cell(C, D, rec)
    wit = []
    for k in BODIES:
        if C.zt.meet(k, O) is None or C.wt.meet(k, O) is None:
            wit.append((k, 'O'))
            continue
        found = None
        for l in BODIES:
            if l == k or (min(k, l), max(k, l)) not in pos:
                continue
            if anc_eq(C.zt, C.zt.meet(k, l), C.zt.leaf[O]) and anc_eq(C.wt, C.wt.meet(k, l), C.wt.leaf[O]):
                found = l
                break
        if found is None:
            return None
        wit.append((k, found))
    return tuple(wit)


# ---------------------------------------------------------------- Lemma C (cluster sum, merged positions)

def lead_key(T, k):
    """identifier of the leading coefficient of the position of k in tree T: (node meet(k,O), child containing k);
    None if k sits at O."""
    v = T.meet(k, O)
    if v is None:
        return None
    return (v, T.child_of(v, k))


def lemma_C_witness(C, rec, J, col):
    """S_J (colour col) = sum of the equations of the bodies of J. Hypotheses: the minimal exponents of the equations
    of J are all equal (the mutual internal-force graph, together with bodies whose position is minimal and lies at
    one common node, connects J), and the minimal non-internal terms are either a single term, or positions of
    bodies of J that share one leading coefficient (same child of the same node). Then the initial form of S_J is a
    single monomial times a positive mass sum."""
    A = argmins(rec)
    T = C.zt if col == 'z' else C.wt
    Js = set(J)
    for i in J:
        if (col, i) not in A:
            return None
    adj = {i: set() for i in J}
    for i in J:
        for lab in A[(col, i)]:
            if lab[0] == 'cross' and lab[2] in Js and ('cross', lab[2], i) in A[(col, lab[2])]:
                adj[i].add(lab[2])
                adj[lab[2]].add(i)
    # positions in argmin, grouped by node: bodies whose position is minimal at the same node have equal minima
    posnode = {}
    for i in J:
        if ('pos', i) in A[(col, i)]:
            posnode.setdefault(T.meet(i, O), []).append(i)
    for node, lst in posnode.items():
        for a in lst:
            for b in lst:
                if a != b:
                    adj[a].add(b)
    seen = {J[0]}
    stack = [J[0]]
    while stack:
        v = stack.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u)
                stack.append(u)
    if seen != Js:
        return None
    ext = []
    for i in J:
        for lab in A[(col, i)]:
            if lab[0] == 'pos' or (lab[0] == 'cross' and lab[2] not in Js):
                ext.append(lab)
    if len(ext) == 1:
        return ('single', ext[0])
    if ext and all(l[0] == 'pos' for l in ext):
        keys = set(lead_key(T, l[1]) for l in ext)
        if len(keys) == 1 and None not in keys:
            return ('merged-positions', tuple(l[1] for l in ext))
    return None


def lemma_C(C, rec):
    for col in 'zw':
        for r in range(2, N):
            for J in itertools.combinations(BODIES, r):
                w = lemma_C_witness(C, rec, J, col)
                if w is not None:
                    return (col, J, w)
    return None


# ---------------------------------------------------------------- Lemma B (binary)

def lemma_B(C, D, rec):
    """A pair {k,l} and a colour c with argmin(c,k) a subset of {Z_kl, z_k} containing Z_kl, the same for l, and
    x_kl > 0 forced (positive_pairs_cell). The difference of the two equations, z_kl = sum_j m_j Z_kj - sum_j m_j Z_lj,
    then has the single minimal monomial -(m_k + m_l) Z_kl."""
    A = argmins(rec)
    pos = positive_pairs_cell(C, D, rec)
    for col in 'zw':
        for k, l in itertools.combinations(BODIES, 2):
            ak, al = A.get((col, k)), A.get((col, l))
            if ak is None or al is None:
                continue
            if ('cross', k, l) not in ak or ('cross', l, k) not in al:
                continue
            if not ak <= {('cross', k, l), ('pos', k)} or not al <= {('cross', l, k), ('pos', l)}:
                continue
            if (k, l) in pos:
                return (col, k, l)
    return None


# ---------------------------------------------------------------- triangle families (generic mass conditions)

def common_meet(T, tri):
    a, b, c = tri
    v = T.meet(a, b)
    return v if (v is not None and T.meet(b, c) == v and T.meet(a, c) == v) else None


def balanced(A, col, k, tri):
    """body k's equation in colour col has exactly the two internal forces of tri as minimal terms."""
    others = [l for l in tri if l != k]
    return A.get((col, k)) == {('cross', k, others[0]), ('cross', k, others[1])}


def U_tri(A, tri):
    U = A.get(('U',))
    if U is None:
        return False
    want = {('delta',) + p for p in itertools.combinations(sorted(tri), 2)}
    return U == want


def lemma_E1(C, D, rec):
    """Balanced triangle: three bodies whose pairs meet at one node in each tree, with balance (exactly the two
    internal forces minimal) in z at the vertices Bz and in w at the vertices Bw. E(T) follows if
    (|Bz| >= 2 and |Bw| >= 1) or (|Bw| >= 2 and |Bz| >= 1), or if Bz and Bw are nonempty and the minimal terms of U
    are exactly the three pairs of T (U_T = 0)."""
    A = argmins(rec)
    for tri in itertools.combinations(BODIES, 3):
        if common_meet(C.zt, tri) is None or common_meet(C.wt, tri) is None:
            continue
        Bz = {k for k in tri if balanced(A, 'z', k, tri)}
        Bw = {k for k in tri if balanced(A, 'w', k, tri)}
        if (len(Bz) >= 2 and len(Bw) >= 1) or (len(Bw) >= 2 and len(Bz) >= 1):
            return (tri, tuple(sorted(Bz)), tuple(sorted(Bw)), 'bal')
        if Bz and Bw and U_tri(A, tri):
            return (tri, tuple(sorted(Bz)), tuple(sorted(Bw)), 'U')
    return None


def lemma_R1(C, D, rec):
    """R(ab;s): three bodies whose pairs meet at one node in each tree; in a colour c, balance at a and b; in the
    c-tree, at the meet node v of T, the bodies a and b lie in children containing no other body, and s, O and all
    other bodies lie in one further child (so the centre of mass gives m_a Y_a + m_b Y_b = 0 at exponent h(v), with
    the c-separations of s from a, b equal to Y_a, Y_b). Variant: balance at only one of a, b, and U_T. Then
    prod over cube roots of unity w of [m_s^2 (m_a+m_b) (m_b + w m_a)^3 - m_a^3 m_b^3] = 0 (w = 1: AK's R(ab;s))."""
    A = argmins(rec)
    for tri in itertools.combinations(BODIES, 3):
        if common_meet(C.zt, tri) is None or common_meet(C.wt, tri) is None:
            continue
        for col, T in (('z', C.zt), ('w', C.wt)):
            v = common_meet(T, tri)
            for s in tri:
                a, b = [k for k in tri if k != s]
                nb = balanced(A, col, a, tri) + balanced(A, col, b, tri)
                if nb == 0 or (nb == 1 and not U_tri(A, tri)):
                    continue
                cs = T.child_of(v, s)
                if T.child_of(v, O) != cs:
                    continue
                if all(T.child_of(v, j) == cs for j in BODIES if j not in tri):
                    return (tri, col, s, 'bal2' if nb == 2 else 'bal1+U')
    return None


def centred(T, tri, s):
    """at the common meet node v of tri in tree T: the two vertices other than s lie in children that contain no other
    body and not O; s, O and all bodies outside tri lie in one further child. Then the centre of mass at exponent
    h(v) reads m_a Y_a + m_b Y_b = 0 and the separations of s from a, b have leading coefficients Y_a, Y_b."""
    v = common_meet(T, tri)
    if v is None:
        return False
    cs = T.child_of(v, s)
    if T.child_of(v, O) != cs:
        return False
    return all(T.child_of(v, j) == cs for j in BODIES if j not in tri)


def lemma_R5(C, D, rec):
    """R5(ab;s): common meets; balance in colour c at a (or b); centre at s in the other colour; U_T (the minimal terms
    of U are exactly the pairs of T). Then m_s^2 (m_a+m_b)^3 (m_a^5+m_b^5) = m_a^5 m_b^5."""
    A = argmins(rec)
    for tri in itertools.combinations(BODIES, 3):
        if common_meet(C.zt, tri) is None or common_meet(C.wt, tri) is None or not U_tri(A, tri):
            continue
        for col, To in (('z', C.wt), ('w', C.zt)):
            for s in tri:
                if not centred(To, tri, s):
                    continue
                if any(balanced(A, col, a, tri) for a in tri if a != s):
                    return (tri, col, s)
    return None


def lemma_R6(C, D, rec):
    """R6(a,b;s): common meets; centre at s and balance at s in colour c; balance at a in the other colour.
    Then m_s^2 (m_a+m_b)^4 = m_a m_b^5 (times a factor from the other cube roots of unity)."""
    A = argmins(rec)
    for tri in itertools.combinations(BODIES, 3):
        if common_meet(C.zt, tri) is None or common_meet(C.wt, tri) is None:
            continue
        for col, T, oc in (('z', C.zt, 'w'), ('w', C.wt, 'z')):
            for s in tri:
                if not centred(T, tri, s) or not balanced(A, col, s, tri):
                    continue
                for a in tri:
                    if a != s and balanced(A, oc, a, tri):
                        return (tri, col, s, a)
    return None


def lemma_Q(C, D, rec):
    """Equidistant forces: body s's equation in colour c has minimal terms exactly the forces Z_sk, k in K, |K| >= 2,
    and all bodies of K lie in one child of one node in each tree, the node being meet(s, k) (so the separations of s
    from K have one common leading coefficient in each colour). Then delta_sk^2 = 1/(z w) is the same for k in K,
    delta_sk = eps_k delta, and the balance gives sum_k eps_k m_k = 0 (eps_k = +-1): for |K| = 2, m_a = m_b at positive
    masses (AK's EQ); for |K| = 3 one mass is the sum of the other two."""
    A = argmins(rec)
    for col in 'zw':
        for s in BODIES:
            am = A.get((col, s))
            if not am or any(l[0] != 'cross' for l in am) or len(am) < 2:
                continue
            K = [l[2] for l in am]
            ok = True
            for T in (C.zt, C.wt):
                nodes = {T.meet(s, k) for k in K}
                if len(nodes) != 1:
                    ok = False
                    break
                v = nodes.pop()
                if len({T.child_of(v, k) for k in K}) != 1:
                    ok = False
                    break
            if ok:
                return (col, s, tuple(sorted(K)))
    return None
