#!/usr/bin/env python3
"""Verify a Singular liftstd cofactor file for an escape-ray system of Lemma 6.19(a) and write the certificate.

Usage: verify_esc.py HYPS_JSON INDEX P COFFILE OUTFILE
  HYPS_JSON: the systems of the leaves `hyp` (a list of systems; a system is a list of polynomials [[c, [e0..e16]], ...]),
             the same data as `hypsN4` / `hypsKC` (`DataN4.hypStr` / `DataKC.hypStr`)
  COFFILE:   the export of the liftstd script ("#k" then the Singular string of cofactor k, variables x(0)..x(16))
  OUTFILE:   one line per term "k c e0 ... e16" (k from 0, c in [0, P)), cofactors in the order of the system.
Checks with python-flint (nmod_mpoly) that sum_k cof_k * f_k = 1 modulo P."""
import json
import re
import sys
import flint

NV = 17
TERM = re.compile(r'([+-]?)([^+-]+)')
VAR = re.compile(r'x\((\d+)\)(?:\^(\d+))?$')


def parse_sing(s, P):
    s = s.strip().rstrip(';')
    out = {}
    if s == '0':
        return out
    for sign, body in TERM.findall(s):
        c = 1
        e = [0] * NV
        for fac in body.split('*'):
            if fac[0].isdigit():
                c *= int(fac)
            else:
                m = VAR.match(fac)
                assert m, fac
                e[int(m.group(1))] += int(m.group(2) or 1)
        if sign == '-':
            c = -c
        key = tuple(e)
        out[key] = (out.get(key, 0) + c) % P
        if out[key] == 0:
            del out[key]
    return out


def main():
    hyps_path, idx, P, cof_path, out_path = sys.argv[1:6]
    P = int(P)
    system = json.load(open(hyps_path))[int(idx)]
    eqs = [{tuple(e): c % P for c, e in f} for f in system]
    cofs, cur = [], None
    for line in open(cof_path):
        line = line.rstrip('\n')
        if line.startswith('#'):
            cur = int(line[1:]) - 1
            cofs.append('')
            assert cur == len(cofs) - 1
        else:
            cofs[cur] += line
    assert len(cofs) == len(eqs), (len(cofs), len(eqs))
    cd = [parse_sing(s, P) for s in cofs]
    names = tuple('x%d' % i for i in range(NV))
    ctx = flint.nmod_mpoly_ctx.get(names=names, ordering='degrevlex', modulus=P)
    total = ctx.from_dict({})
    for d, f in zip(cd, eqs):
        total += ctx.from_dict(d) * ctx.from_dict({k: v for k, v in f.items() if v})
    ok = total == ctx.from_dict({(0,) * NV: 1})
    with open(out_path, 'w') as fh:
        for k, d in enumerate(cd):
            for e in sorted(d, reverse=True):
                fh.write('%d %d %s\n' % (k, d[e], ' '.join(map(str, e))))
    print('system %s P=%d polynomials %d cofactor terms %d identity %s' % (idx, P, len(eqs), sum(len(d) for d in cd), ok))
    sys.exit(0 if ok else 1)


main()
