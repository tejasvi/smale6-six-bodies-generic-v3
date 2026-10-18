#!/usr/bin/env python3
"""The reduced systems for the four-body equilibrium system E4(mu) (DERIVATION.md, Lemma E).

Bodies 1..4 (indices 0..3).  Pairs in the order 01, 02, 03, 12, 13, 23.

(a) Non-collinear, beta != 0:  forms in P^4 with coordinates (q_1, q_2, q_3, q_4, b)   [b = 1/beta]
        R_k = b * sum_{l != k} w^{e_kl} mu_l q_l + q_k^2    (k = 1..4),     R_5 = sum_k mu_k q_k^3,
    one system for each class (B, C) in (Z/3)^2 of the exponents e_kl mod the action e_kl -> e_kl + a_k + a_l;
    representative e_01 = e_03 = e_13 = e_23 = 0, e_02 = -B, e_12 = -C (mod 3).
(b) Non-collinear, beta = 0: sum_{l != k} w^{e_kl} mu_l q_l = 0 for all k with q != 0, i.e. det(W_e) = 0 with
    (W_e)_kl = w^{e_kl} (k != l), 0 on the diagonal.
(c) Collinear: forms in P^2 with coordinates (d_2, d_3, d_4), d_k = xi_k - xi_1:
        G_k = sum_{l != k} s_kl mu_l prod_{j != k, l} (xi_k - xi_j)^2,   k = 1..4,
    for each antisymmetric sign pattern s (s_kl = -s_lk in {+1,-1}); patterns s and -s give the same forms up to sign.

Polynomials are dicts {exponent: (a, b)} = a + b w, as in macaulay_modp.py.
"""
import itertools

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def classes():
    return [(B, C) for B in range(3) for C in range(3)]


def eps_of_class(B, C):
    e = {pr: 0 for pr in PAIRS}
    e[(0, 2)] = (-B) % 3
    e[(1, 2)] = (-C) % 3
    return e


def w_pow(k):
    """w^k as (a, b): w^0 = 1, w^1 = w, w^2 = -1 - w."""
    k %= 3
    return [(1, 0), (0, 1), (-1, -1)][k]


def add_term(poly, e, c):
    a, b = poly.get(e, (0, 0))
    a += c[0]
    b += c[1]
    if a == 0 and b == 0:
        poly.pop(e, None)
    else:
        poly[e] = (a, b)


def scal(c, s):
    return (c[0] * s, c[1] * s)


def noncollinear_forms(mu, e):
    """Forms R_1..R_5 in variables (q1, q2, q3, q4, b)."""
    forms = []
    for k in range(4):
        f = {}
        for l in range(4):
            if l == k:
                continue
            ex = [0] * 5
            ex[l] += 1
            ex[4] += 1
            add_term(f, tuple(ex), scal(w_pow(e[(min(k, l), max(k, l))]), mu[l]))
        ex = [0] * 5
        ex[k] += 2
        add_term(f, tuple(ex), (1, 0))
        forms.append(f)
    f = {}
    for k in range(4):
        ex = [0] * 5
        ex[k] = 3
        add_term(f, tuple(ex), (mu[k], 0))
    forms.append(f)
    return forms


def zw_mul(x, y):
    """(a + b w)(c + d w) with w^2 = -1 - w."""
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def det_W(e):
    """det of (w^{e_kl})_{k != l}, zero diagonal, exactly in Z[w] (Leibniz)."""
    total = (0, 0)
    for perm in itertools.permutations(range(4)):
        if any(perm[k] == k for k in range(4)):
            continue
        sign = 1
        for i in range(4):
            for j in range(i + 1, 4):
                if perm[i] > perm[j]:
                    sign = -sign
        term = (sign, 0)
        for k in range(4):
            l = perm[k]
            term = zw_mul(term, w_pow(e[(min(k, l), max(k, l))]))
        total = (total[0] + term[0], total[1] + term[1])
    return total


def sign_patterns():
    """Antisymmetric sign patterns modulo s -> -s: s_01 = +1, the other five free (32 patterns)."""
    out = []
    for bits in itertools.product((1, -1), repeat=5):
        s = {(0, 1): 1}
        for pr, b in zip(PAIRS[1:], bits):
            s[pr] = b
        out.append(s)
    return out


def poly_mul(f, g):
    h = {}
    for e1, c1 in f.items():
        for e2, c2 in g.items():
            add_term(h, tuple(x + y for x, y in zip(e1, e2)), zw_mul(c1, c2))
    return h


def collinear_forms(mu, s):
    """G_1..G_4 in variables (d2, d3, d4); xi_1 = 0, xi_k = d_k."""
    def xi(k):  # linear form xi_k as a poly in (d2,d3,d4)
        if k == 0:
            return {}
        ex = [0, 0, 0]
        ex[k - 1] = 1
        return {tuple(ex): (1, 0)}

    def diff(k, j):
        f = dict(xi(k))
        for ex, c in xi(j).items():
            add_term(f, ex, scal(c, -1))
        return f

    def sgn(k, l):
        return s[(k, l)] if k < l else -s[(l, k)]
    forms = []
    for k in range(4):
        G = {}
        for l in range(4):
            if l == k:
                continue
            term = {(0, 0, 0): (sgn(k, l) * mu[l], 0)}
            for j in range(4):
                if j in (k, l):
                    continue
                dkj = diff(k, j)
                term = poly_mul(term, poly_mul(dkj, dkj))
            for ex, c in term.items():
                add_term(G, ex, c)
        forms.append(G)
    return forms


def noncollinear_forms_P3(mu, e):
    """Forms in P^3 (q1..q4): Q_jk = q_j^2 A_k - q_k^2 A_j (j < k) and R = sum mu_k q_k^3, where
    A_k = sum_{l != k} w^{e_kl} mu_l q_l.  (beta eliminated; covers beta = 0.)"""
    def A(k):
        f = {}
        for l in range(4):
            if l != k:
                ex = [0] * 4
                ex[l] = 1
                add_term(f, tuple(ex), scal(w_pow(e[(min(k, l), max(k, l))]), mu[l]))
        return f

    def sq(k):
        ex = [0] * 4
        ex[k] = 2
        return {tuple(ex): (1, 0)}
    forms = []
    for j in range(4):
        for k in range(j + 1, 4):
            f = poly_mul(sq(j), A(k))
            for ex, c in poly_mul(sq(k), A(j)).items():
                add_term(f, ex, scal(c, -1))
            forms.append(f)
    f = {}
    for k in range(4):
        ex = [0] * 4
        ex[k] = 3
        add_term(f, tuple(ex), (mu[k], 0))
    forms.append(f)
    return forms
