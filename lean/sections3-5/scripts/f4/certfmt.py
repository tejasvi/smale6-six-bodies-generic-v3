"""Shared helpers for the F4 cofactor certificates (untrusted; Lean re-checks everything):
an exact parser for the stored core polynomials, the certificate text format of scripts/f4/README.md, and an exact
check of a certificate file with python-flint (fmpz_mpoly arithmetic, no Groebner bases)."""
import gzip
import hashlib
import re

import flint

NMASS = 6
MASSES = tuple(f'm{k}' for k in range(NMASS))
POINT = (3, 5, 7, 11, 13, 17)

# ----------------------------------------------------------------------------------------------------------------
# Parser of the stored polynomial expressions: integers, identifiers, + - * / ^ and parentheses; division only by
# nonzero constants.  The result is an fmpq_mpoly in the given context.

_TOK = re.compile(r'\s*(?:(\d+)|([A-Za-z_][A-Za-z_0-9]*)|(\S))')


def _tokens(s):
    out = []
    pos = 0
    s = s.rstrip()
    while pos < len(s):
        m = _TOK.match(s, pos)
        if not m or m.end() == pos:
            raise ValueError(f'cannot tokenize at {pos}: {s[pos:pos + 20]!r}')
        pos = m.end()
        if m.group(1) is not None:
            out.append(('int', int(m.group(1))))
        elif m.group(2) is not None:
            out.append(('id', m.group(2)))
        else:
            out.append(('op', m.group(3)))
    out.append(('end', None))
    return out


def parse_poly(s, ctx, names):
    """Parse expression s; names maps identifiers to generators of the fmpq_mpoly context ctx."""
    toks = _tokens(s)
    pos = 0

    def peek():
        return toks[pos]

    def take():
        nonlocal pos
        t = toks[pos]
        pos += 1
        return t

    def expr():
        val = term()
        while peek() in (('op', '+'), ('op', '-')):
            op = take()[1]
            t = term()
            val = val + t if op == '+' else val - t
        return val

    def term():
        val = factor()
        while peek() in (('op', '*'), ('op', '/')):
            op = take()[1]
            f = factor()
            if op == '*':
                val = val * f
            else:
                if not f.is_constant() or f.is_zero():
                    raise ValueError('division by a nonconstant or zero expression')
                c = f.leading_coefficient()
                val = val * (flint.fmpq(1) / c)
        return val

    def factor():
        if peek() == ('op', '-'):
            take()
            return -factor()
        if peek() == ('op', '+'):
            take()
            return factor()
        b = base()
        if peek() == ('op', '^'):
            take()
            kind, e = take()
            if kind != 'int':
                raise ValueError('exponent must be an integer')
            b = b ** e
        return b

    def base():
        kind, v = take()
        if kind == 'int':
            return ctx.from_dict({(0,) * ctx.nvars(): flint.fmpq(v)})
        if kind == 'id':
            if v not in names:
                raise ValueError(f'unknown identifier {v}')
            return names[v]
        if (kind, v) == ('op', '('):
            val = expr()
            if take() != ('op', ')'):
                raise ValueError('expected )')
            return val
        raise ValueError(f'unexpected token {v!r}')

    val = expr()
    if peek()[0] != 'end':
        raise ValueError(f'trailing tokens in {s[:60]!r}')
    return val


# ----------------------------------------------------------------------------------------------------------------
# Certificate text format.  A polynomial is a dict {exponent tuple (e0..e5, x0..x(V-1)): nonzero int}.

def term_line(c, k):
    xs = [(j, e) for j, e in enumerate(k[NMASS:]) if e]
    parts = [str(c)] + [str(e) for e in k[:NMASS]] + [str(len(xs))]
    for j, e in xs:
        parts.append(str(j))
        parts.append(str(e))
    return ' '.join(parts)


def poly_lines(head, d):
    keys = sorted(d, reverse=True)
    yield f'{head} {len(keys)}'
    for k in keys:
        yield term_line(d[k], k)


def gen_block(nvar, fixed, gens):
    """The generator block (header and generators); its SHA-256 names the certificate."""
    lines = ['L6CERT 1', f'nmass {NMASS} nvar {nvar} fixed {fixed}', f'ngens {len(gens)}']
    for i, g in enumerate(gens):
        lines.extend(poly_lines(f'gen {i}', g))
    return '\n'.join(lines) + '\n'


def cert_id(block):
    return hashlib.sha256(block.encode()).hexdigest()[:16]


def open_text(path):
    if path.endswith('.gz'):
        return gzip.open(path, 'rt')
    return open(path)


def read_cert(path):
    """Read a certificate file -> (nvar, fixed, gens, cofs, h, generator block text)."""
    with open_text(path) as fh:
        lines = [ln for ln in fh.read().split('\n')]
    it = iter(i for i, ln in enumerate(lines) if ln.strip() and not ln.lstrip().startswith('#'))
    idx = list(it)
    p = 0

    def nxt():
        nonlocal p
        ln = lines[idx[p]]
        p += 1
        return ln.split()

    t = nxt()
    assert t == ['L6CERT', '1'], t
    t = nxt()
    assert t[0] == 'nmass' and int(t[1]) == NMASS and t[2] == 'nvar' and t[4] == 'fixed', t
    nvar, fixed = int(t[3]), int(t[5])
    t = nxt()
    assert t[0] == 'ngens'
    ng = int(t[1])
    nv = NMASS + nvar

    def poly(T):
        d = {}
        for _ in range(T):
            a = list(map(int, nxt()))
            c = a[0]
            k = [0] * nv
            k[:NMASS] = a[1:1 + NMASS]
            nx = a[1 + NMASS]
            assert len(a) == 2 + NMASS + 2 * nx, a
            prev = -1
            for q in range(nx):
                j, e = a[2 + NMASS + 2 * q], a[3 + NMASS + 2 * q]
                assert prev < j < nvar and e >= 1, a
                prev = j
                k[NMASS + j] = e
            assert all(e >= 0 for e in k[:NMASS]) and c != 0, a
            k = tuple(k)
            assert k not in d, 'repeated monomial'
            d[k] = c
        return d

    gens = []
    for i in range(ng):
        t = nxt()
        assert t[0] == 'gen' and int(t[1]) == i, t
        gens.append(poly(int(t[2])))
    gen_end = idx[p] if p < len(idx) else len(lines)
    block = '\n'.join(lines[:gen_end]) + '\n'
    cofs = []
    for i in range(ng):
        t = nxt()
        assert t[0] == 'cof' and int(t[1]) == i, t
        cofs.append(poly(int(t[2])))
    t = nxt()
    assert t[0] == 'h', t
    h = poly(int(t[1]))
    assert p == len(idx), 'trailing lines'
    return nvar, fixed, gens, cofs, h, block


def ctx_for(nvar):
    return flint.fmpz_mpoly_ctx.get(MASSES + tuple(f'x{j}' for j in range(nvar)), 'lex')


def eval_masses(h, fixed):
    pt = list(POINT)
    if fixed >= 0:
        pt[fixed] = 1
    tot = 0
    for k, c in h.items():
        v = c
        for e, x in zip(k[:NMASS], pt):
            if e:
                v *= x ** e
        tot += v
    return tot


def verify_cert(path, expect_id=None):
    """Exact check of a certificate file: sum_i cof_i * gen_i == h in Z[m, x], h free of x, h(point) != 0 (with
    m_F = 1 if F >= 0), no m_F in the generators when F >= 0, and the file name matches the generator block."""
    nvar, fixed, gens, cofs, h, block = read_cert(path)
    if expect_id is not None and cert_id(block) != expect_id:
        return False, 'certid mismatch'
    if fixed >= 0:
        for g in gens + cofs + [h]:
            if any(k[fixed] for k in g):
                return False, 'fixed mass occurs'
    if not h:
        return False, 'h = 0'
    if any(any(k[NMASS:]) for k in h):
        return False, 'h depends on the variables'
    ctx = ctx_for(nvar)
    tot = ctx.from_dict({})
    for c, g in zip(cofs, gens):
        if c and g:
            tot += ctx.from_dict(c) * ctx.from_dict(g)
    if tot != ctx.from_dict(h):
        return False, 'identity fails'
    val = eval_masses(h, fixed)
    if val == 0:
        return False, 'h vanishes at the point'
    return True, f'ok h_terms={len(h)} h_point_digits={len(str(abs(val)))}'
