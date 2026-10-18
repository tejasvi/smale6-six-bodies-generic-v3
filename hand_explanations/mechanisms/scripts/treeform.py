#!/usr/bin/env python3
"""Tree-only reasoning about linear forms in the node heights of a rooted tree.

A height function h on the internal nodes is admissible if it strictly increases from a node to each internal child.
A linear form F = sum_v c_v h(v) satisfies F >= 0 for every admissible h (and every value of the root height) iff
sum_v c_v = 0 and for every non-root internal node w the subtree sum S(w) = sum_{v below or at w} c_v is >= 0;
then F > 0 for every admissible h iff moreover some S(w) > 0 (F is a positive combination of edge increments).
Exact arithmetic with Fractions."""
from fractions import Fraction


def subtree_sums(T, form):
    """T: cellkit.Tr; form: dict node -> coefficient. Returns (total, {node: subtree sum}) over internal nodes."""
    S = {}

    def rec(v):
        s = form.get(v, Fraction(0))
        for c in T.children.get(v, []):
            if c in T.children:
                s += rec(c)
        S[v] = s
        return s

    total = rec(T.root)
    return total, S


def sign_tree(T, form):
    """'pos' if F > 0 for all admissible h, 'nonneg' if F >= 0 (and can be 0), 'zero' if F == 0 identically,
    else None (no tree-only conclusion)."""
    form = {v: Fraction(c) for v, c in form.items() if c != 0}
    if not form:
        return 'zero'
    total, S = subtree_sums(T, form)
    if total != 0:
        return None
    pos = False
    for v, s in S.items():
        if v == T.root:
            continue
        if s < 0:
            return None
        if s > 0:
            pos = True
    return 'pos' if pos else 'zero'


def add(*forms):
    d = {}
    for f in forms:
        for v, c in f.items():
            d[v] = d.get(v, Fraction(0)) + Fraction(c)
    return {v: c for v, c in d.items() if c != 0}


def scale(f, c):
    return {v: Fraction(c) * x for v, x in f.items()}
