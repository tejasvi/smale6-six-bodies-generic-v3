#!/usr/bin/env python3
"""Certificate (checker 1) for Lemma E of DERIVATION.md: the four-body equilibrium system E4(mu) has no solution at
mu0 = (3, 5, 7, 11), hence (properness) none for mu outside a proper algebraic subset of C^4.

For every one of the 3^6 = 729 cube-root patterns e (not only the 9 class representatives) the beta-eliminated
non-collinear forms in P^3 (e4_systems.noncollinear_forms_P3) and, for every one of the 64 antisymmetric sign patterns
s, the collinear forms in P^2 (e4_systems.collinear_forms) are shown to have no common zero over C, by a full-rank
Macaulay matrix mod p (macaulay_modp: rank mod a prime of Z[w] above p bounds the rank over Q(w) from below).

Usage: e4_cert_macaulay.py [m1 m2 m3 m4] [p]      (defaults 3 5 7 11 and p = 2147483629)
Output: JSON summary on stdout; exit code 0 iff every system passes.
"""
import itertools
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from macaulay_modp import cube_root_of_unity, to_modp, first_full_degree, macaulay_rank  # noqa: E402
from e4_systems import PAIRS, noncollinear_forms_P3, collinear_forms  # noqa: E402


def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def main():
    args = sys.argv[1:]
    mu = tuple(int(a) for a in args[:4]) if len(args) >= 4 else (3, 5, 7, 11)
    p = int(args[4]) if len(args) >= 5 else 2147483629
    assert is_prime(p) and p % 3 == 1
    r = cube_root_of_unity(p)
    t0 = time.time()
    out = {'mu0': mu, 'p': p, 'w_mod_p': r}
    # non-collinear: all 729 patterns, degree 7 (Macaulay bound 4*(3-1)+1 = 9 not needed: we exhibit full rank at D)
    fails, degs = [], {}
    for exps in itertools.product(range(3), repeat=6):
        e = dict(zip(PAIRS, exps))
        F = [to_modp(f, p, r) for f in noncollinear_forms_P3(mu, e)]
        res = first_full_degree(F, 4, p, 12)
        if res is None:
            fails.append(exps)
        else:
            degs[res[0]] = degs.get(res[0], 0) + 1
    out['noncollinear'] = {'patterns': 729, 'fail': fails, 'full_rank_degree_histogram': degs}
    # collinear: all 64 antisymmetric sign patterns
    fails_c, degs_c = [], {}
    for bits in itertools.product((1, -1), repeat=6):
        s = dict(zip(PAIRS, bits))
        F = [to_modp(f, p, r) for f in collinear_forms(mu, s)]
        res = first_full_degree(F, 3, p, 16)
        if res is None:
            fails_c.append(bits)
        else:
            degs_c[res[0]] = degs_c.get(res[0], 0) + 1
    out['collinear'] = {'patterns': 64, 'fail': fails_c, 'full_rank_degree_histogram': degs_c}
    out['seconds'] = round(time.time() - t0, 2)
    ok = not fails and not fails_c
    out['verdict'] = 'PASS' if ok else 'FAIL'
    print(json.dumps(out, indent=1))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
