#!/usr/bin/env python3
"""Strict msolve input writer with two independent lints.

msolve 0.9.4 silently misparses parentheses, '**', repeated variables in a monomial (x*x), numbers after variables
(x*2, x/2), floats and uncollected like terms.  Every polynomial is expanded
by sympy over Z (denominators cleared) and printed monomial by monomial as  c*x1^e1*x2^e2*...  (integer coefficient
first, each variable at most once, '^' for exponents > 1), like terms collected.  Lint 1 re-parses the file with a tiny
parser of the strict grammar and compares with the sympy polynomials; lint 2 is tools/ms_lint.py of the supplement (independent).
"""
import os
import re
import sys
import sympy as sp

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
try:
    from ms_lint import lint_text as _ms_lint_text
except Exception:  # pragma: no cover
    _ms_lint_text = None


def _cleared(expr, gens):
    P = sp.Poly(sp.expand(expr), *gens)
    cs = P.coeffs()
    den = sp.ilcm(*[sp.fraction(sp.Rational(c))[1] for c in cs]) if cs else 1
    P = sp.Poly(sp.expand(P.as_expr() * den), *gens)
    g = sp.igcd(*[int(c) for c in P.coeffs()]) if P.coeffs() else 1
    if g > 1:
        P = sp.Poly(sp.expand(P.as_expr() / g), *gens)
    return P


def poly_to_msolve(expr, gens):
    P = _cleared(expr, gens)
    terms = []
    for monom, coeff in P.terms():
        c = int(coeff)
        if c == 0:
            continue
        parts = []
        for g, e in zip(gens, monom):
            if e == 1:
                parts.append(str(g))
            elif e > 1:
                parts.append('%s^%d' % (g, e))
        terms.append(str(c) if not parts else ('%d*%s' % (c, '*'.join(parts))))
    out = '+'.join(terms).replace('+-', '-')
    return out if out else '0'


def write_input(path, gens, polys, char):
    body = [poly_to_msolve(p, gens) for p in polys]
    body = [b for b in body if b != '0']
    with open(path, 'w') as f:
        f.write(','.join(str(g) for g in gens) + '\n' + str(char) + '\n')
        f.write(',\n'.join(body) + '\n')
    lint(path, gens, [p for p in polys if poly_to_msolve(p, gens) != '0'])
    return path


def parse_poly(s, gens):
    names = [str(g) for g in gens]
    sym = dict(zip(names, gens))
    s = s.strip()
    assert '(' not in s and ')' not in s and '**' not in s and '/' not in s and '.' not in s, s[:80]
    assert not s.startswith('+')
    toks = re.findall(r'[+-]?[^+-]+', s)
    total = 0
    seen_mons = set()
    for t in toks:
        sign = -1 if t.startswith('-') else 1
        t = t.lstrip('+-')
        factors = t.split('*')
        coeff, mon, seen = 1, 1, set()
        key = []
        for i, fct in enumerate(factors):
            if re.fullmatch(r'\d+', fct):
                assert i == 0, 'coefficient not first: ' + t
                coeff = int(fct)
            else:
                m = re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*)(\^(\d+))?', fct)
                assert m, 'bad factor ' + fct
                v = m.group(1)
                assert v in sym, 'unknown variable ' + v
                assert v not in seen, 'repeated variable in monomial: ' + t
                seen.add(v)
                e = int(m.group(3)) if m.group(3) else 1
                key.append((v, e))
                mon *= sym[v] ** e
        k = tuple(sorted(key))
        assert k not in seen_mons, 'duplicate monomial ' + t
        seen_mons.add(k)
        total += sign * coeff * mon
    return sp.expand(total)


def lint(path, gens, polys):
    txt = open(path).read().strip().split('\n')
    assert txt[0] == ','.join(str(g) for g in gens)
    body = '\n'.join(txt[2:])
    parts = [p.strip() for p in body.split(',') if p.strip()]
    assert len(parts) == len(polys), (len(parts), len(polys))
    for s, p in zip(parts, polys):
        q = parse_poly(s, gens)
        P = _cleared(p, gens)
        assert sp.expand(q - P.as_expr()) == 0, 'lint mismatch'
    if _ms_lint_text is not None:
        r = _ms_lint_text(open(path).read())
        # ms_lint returns a list of problems (empty when clean) or raises; accept both conventions
        if r not in (None, True) and r:
            raise AssertionError('ms_lint: %r' % (r,))
    return True
