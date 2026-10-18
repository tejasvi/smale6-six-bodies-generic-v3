#!/usr/bin/env python3
"""Parse core equations (Singular strings over X{v}_{i}, Y{v}_{i}, D{k}_{l}, E, masses (mK)) into terms with roles:
  pos(k,c)        m_k * lead            (a position, colour c)
  force(k,l,c)    m_k m_l D_kl^3 lead   (a force Z_kl / W_kl of the pair kl)
  pot(k,l)        m_k m_l D_kl          (a potential term)
  E               the energy constant
  zw(k)           m_k leadz leadw       (z_k w_k)
  torq(k,l)       m_k m_l D^3 leadz leadw
  sep(c)          a bare separation (the z_kl of a difference identity)
  dist(k,l)       D_kl^2 leadz leadw - 1
and abstract each equation as a relation (identity name + term roles)."""
import re

TERM_SPLIT = re.compile(r'(?<=[^\(\*\^eE])(?=[+-])')
MASS = re.compile(r'\(m(\d)\)')
DV = re.compile(r'D(\d)_(\d)(?:\^(\d))?')
LEAD = re.compile(r'\(([XY0][\w]*)-([XY0][\w]*)\)')


def split_terms(e):
    """split a sum at top-level + and - signs (parentheses aware)."""
    out, depth, cur = [], 0, ''
    for i, ch in enumerate(e):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if depth == 0 and ch in '+-' and cur.strip() and not cur.endswith(('*', '^', '(')):
            out.append(cur)
            cur = ch
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out


def parse_term(t):
    t = t.strip()
    masses = [int(x) for x in MASS.findall(t)]
    ds = [(int(a), int(b), int(p) if p else 1) for a, b, p in DV.findall(t)]
    leads = LEAD.findall(t)
    cols = []
    for a, b in leads:
        v = a if a != '0' else b
        cols.append('z' if v.startswith('X') else 'w')
    has_E = re.search(r'\bE\b', t) is not None
    if has_E:
        return ('E',)
    if t.lstrip('+-').strip() == '1':
        return ('one',)
    if ds and ds[0][2] == 2 and not masses:
        return ('dist', ds[0][0], ds[0][1])
    if not ds and len(masses) == 1 and len(leads) == 1:
        return ('pos', masses[0], cols[0], leads[0])
    if not ds and len(masses) == 1 and len(leads) == 2:
        return ('zw', masses[0])
    if ds and ds[0][2] == 3 and len(leads) == 1:
        k, l = ds[0][0], ds[0][1]
        return ('force', min(k, l), max(k, l), cols[0], tuple(masses))
    if ds and ds[0][2] == 3 and len(leads) == 2:
        return ('torq', ds[0][0], ds[0][1], tuple(masses))
    if ds and ds[0][2] == 1 and not leads:
        return ('pot', ds[0][0], ds[0][1])
    if not ds and not masses and len(leads) == 1:
        return ('sep', cols[0], leads[0])
    return ('?', t)


def parse_eq(e):
    terms = [parse_term(t) for t in split_terms(e)]
    if any(t[0] == 'dist' for t in terms):
        d = [t for t in terms if t[0] == 'dist'][0]
        return [('dist', d[1], d[2])]
    return terms


def relation(name, eq):
    """abstract relation: (kind, data)."""
    t = eval(name) if isinstance(name, str) else name
    terms = parse_eq(eq)
    if t[0] == 'D' and len(t) == 3:
        return ('dist', (t[1], t[2]))
    if t[0] in ('z', 'w') and t[1] == 'S' and len(t[2]) == 1:
        k = t[2][0]
        pos = any(x[0] == 'pos' for x in terms)
        fl = sorted(set(x[2] if x[1] == k else x[1] for x in terms if x[0] == 'force'))
        return ('bal', t[0], k, pos, tuple(fl))
    if t[0] == 'S':
        col, J = t[1], tuple(t[2])
        ps = sorted(set(x[1] for x in terms if x[0] == 'pos'))
        leads = set(x[3] for x in terms if x[0] == 'pos')
        fl = sorted(set((x[1], x[2]) for x in terms if x[0] == 'force'))
        return ('sum', col, J, tuple(ps), len(leads), tuple(fl))
    if t[0] == 'U':
        return ('U', tuple(sorted(set((x[1], x[2]) for x in terms if x[0] == 'pot'))), any(x[0] == 'E' for x in terms))
    if t[0] == 'V':
        return ('V', tuple(t[1]), tuple(sorted(set((x[1], x[2]) for x in terms if x[0] == 'pot'))),
                tuple(sorted(set(x[1] for x in terms if x[0] == 'zw'))), len([x for x in terms if x[0] == 'torq']))
    if t[0] == 'T':
        return ('T', tuple(t[1]), tuple(sorted(set((x[1], x[2]) for x in terms if x[0] == 'torq'))))
    if t[0] == 'D':
        return ('Diff', t[1], (t[2], t[3]), any(x[0] == 'sep' for x in terms),
                tuple(sorted(set((x[1], x[2]) for x in terms if x[0] == 'force'))))
    if t[0] in ('Ip', 'I'):
        return (t[0], tuple(sorted(set(x[1] for x in terms if x[0] == 'zw'))), any(x[0] == 'E' for x in terms))
    if t[0] == 'UI':
        return ('UI',)
    return ('other', t)
