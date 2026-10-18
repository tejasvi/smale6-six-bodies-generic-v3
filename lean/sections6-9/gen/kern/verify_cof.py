#!/usr/bin/env python3
"""Verify a Singular liftstd cofactor file against the Lean chart equations and write the certificate.

Usage: verify_cof.py LEAN_EQS MU CHART P COFFILE OUTFILE
  LEAN_EQS: the dump of gen/c4/dump_eqs.lean (lines "[mu]|chart|c:e0,...,e8;...")
  COFFILE:  the export of the liftstd script ("#k" then the Singular string of cofactor k, for each k)
  OUTFILE:  the certificate: one line per term "k c e0 e1 ... e8" (k from 0, c in [0, P), exponents in the nine
            variables s, t, p12, p13, p14, p23, p24, p34, c of the Lean equations; the two chart variables have
            exponent 0), cofactors in the order of the equations.
Checks with python-flint (nmod_mpoly) that sum_k cof_k * f_k = 1 modulo P, f_k the Lean equations."""
import re
import sys
import flint

NAMES = ['s', 't', 'p12', 'p13', 'p14', 'p23', 'p24', 'p34', 'c']
CHARTS = {'s_p12': (0, 2), 's_p13': (0, 3), 's_p14': (0, 4), 's_p23': (0, 5), 's_p24': (0, 6), 's_p34': (0, 7),
          's_c': (0, 8), 't_p12': (1, 2), 't_p13': (1, 3), 't_p14': (1, 4), 't_p23': (1, 5), 't_p24': (1, 6),
          't_p34': (1, 7), 't_c': (1, 8)}

TERM = re.compile(r'([+-]?)([^+-]+)')


def parse_sing(s, P):
    """A Singular polynomial string -> dict exponent tuple (9 variables) -> coefficient mod P."""
    s = s.strip().rstrip(';')
    out = {}
    if s == '0':
        return out
    for sign, body in TERM.findall(s):
        c = 1
        e = [0] * 9
        for fac in body.split('*'):
            if fac[0].isdigit():
                c *= int(fac)
            else:
                if '^' in fac:
                    v, k = fac.split('^')
                    k = int(k)
                else:
                    v, k = fac, 1
                e[NAMES.index(v)] += k
        if sign == '-':
            c = -c
        key = tuple(e)
        out[key] = (out.get(key, 0) + c) % P
        if out[key] == 0:
            del out[key]
    return out


def lean_eqs(path, mu, chart):
    eqs = []
    for line in open(path):
        m, ch, body = line.rstrip('\n').split('|')
        if m != mu or ch != chart:
            continue
        f = {}
        for t in body.split(';'):
            c, e = t.split(':')
            f[tuple(int(x) for x in e.split(','))] = int(c)
        eqs.append(f)
    return eqs


def to_flint(ctx, f, P):
    return ctx.from_dict({k: v % P for k, v in f.items()})


def main():
    eqs_path, mu, chart, P, cof_path, out_path = sys.argv[1:7]
    P = int(P)
    eqs = lean_eqs(eqs_path, mu, chart)
    cofs = []
    cur = None
    for line in open(cof_path):
        line = line.rstrip('\n')
        if line.startswith('#'):
            cur = int(line[1:]) - 1
            cofs.append('')
            assert cur == len(cofs) - 1
        else:
            cofs[cur] += line
    assert len(cofs) == len(eqs), (len(cofs), len(eqs))
    cdicts = [parse_sing(s, P) for s in cofs]
    ch = CHARTS[chart]
    for d in cdicts:
        assert all(e[ch[0]] == 0 and e[ch[1]] == 0 for e in d), 'chart variable in a cofactor'
    ctx = flint.nmod_mpoly_ctx.get(names=tuple(NAMES), ordering='degrevlex', modulus=P)
    total = ctx.from_dict({})
    for d, f in zip(cdicts, eqs):
        total += to_flint(ctx, d, P) * to_flint(ctx, f, P)
    ok = total == ctx.from_dict({(0,) * 9: 1})
    nterms = sum(len(d) for d in cdicts)
    with open(out_path, 'w') as fh:
        for k, d in enumerate(cdicts):
            for e in sorted(d, reverse=True):
                fh.write('%d %d %s\n' % (k, d[e], ' '.join(map(str, e))))
    print('%s %s P=%d equations %d cofactor terms %d identity %s' % (mu, chart, P, len(eqs), nterms, ok))
    sys.exit(0 if ok else 1)


main()
