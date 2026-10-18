#!/usr/bin/env python3
"""Count the standard monomials of a monomial ideal given as msolve's '-g 1' leading-ideal output.
Prints the number of standard monomials (= dim of the quotient over the field if finite), or 'infinite'.
Usage: staircase.py FILE.out
"""
import re
import sys
from functools import lru_cache


def read_leading(path):
    txt = open(path).read()
    head = [l for l in txt.split('\n') if l.startswith('#variable order:')][0]
    names = [v.strip() for v in head.split(':', 1)[1].split(',')]
    body = txt[txt.index('['):txt.rindex(']')]
    mons = []
    for t in body.strip('[]').split(','):
        t = t.strip().rstrip(':').strip()
        if not t:
            continue
        e = [0] * len(names)
        for f in t.split('*'):
            m = re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*)\^(\d+)', f.strip())
            if m:
                e[names.index(m.group(1))] += int(m.group(2))
            else:
                e[names.index(f.strip())] += 1
        mons.append(tuple(e))
    return names, mons


def count_standard(mons, n):
    # minimalize
    mons = sorted(set(mons))
    mins = []
    for a in sorted(mons, key=sum):
        if not any(all(b[i] <= a[i] for i in range(n)) for b in mins):
            mins.append(a)
    # each variable must have a pure power, else infinite
    for i in range(n):
        if not any(sum(b) == b[i] and b[i] > 0 for b in mins):
            return None, mins
    # recursive count: standard monomials = sum over exponent of first var
    sys.setrecursionlimit(10000)

    def rec(gens, k):
        # gens: list of tuples over variables k..n-1 ; count monomials in vars k..n-1 not divisible by any gen
        if any(sum(g) == 0 for g in gens):
            return 0
        if k == n - 1:
            return min(g[0] for g in gens if len(g) == 1 or True)
        bound = min(g[0] for g in gens if sum(g[1:]) == 0)  # pure power of var k
        total = 0
        for e in range(bound):
            sub = [g[1:] for g in gens if g[0] <= e]
            # minimalize sub
            sub = list(set(sub))
            total += rec(sub, k + 1)
        return total
    return rec([tuple(b) for b in mins], 0), mins


if __name__ == '__main__':
    names, mons = read_leading(sys.argv[1])
    c, mins = count_standard(mons, len(names))
    print('variables', names)
    print('minimal generators', len(mins))
    print('standard monomials', c if c is not None else 'infinite')
