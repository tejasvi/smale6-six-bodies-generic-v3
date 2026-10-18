#!/usr/bin/env python3
"""Families of cores (template match on the core's initial forms, parsed by coreparse)."""
import itertools, re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coreparse import relation, parse_eq, split_terms
import sympy as sp

M = sp.symbols('m0:6')
LEADRE = re.compile(r'\(([XY0][\w]*)-([XY0][\w]*)\)')


def pos_sum_rows(names, eqs):
    """linear relations among position leads: each 'sum' relation without forces, as {lead: mass-sum expr}."""
    rows = []
    for nm, e in zip(names, eqs):
        rel = relation(nm, e)
        if rel[0] != 'sum' or rel[5]:
            continue
        row = {}
        for t in parse_eq(e):
            if t[0] != 'pos':
                continue
            a, b = t[3]
            # lead = a - b ; normalise sign: variable minus 0 or 0 minus variable or difference
            if b == '0':
                key, sg = a, 1
            elif a == '0':
                key, sg = b, -1
            else:
                key, sg = (a, b), 1
            row[key] = row.get(key, 0) + sg * M[t[1]]
        rows.append(row)
    return rows


def fam_lin(names, eqs):
    """position-sum relations whose matrix in the lead variables has full column rank over Q(m) (on some subset of
    rows/columns closed under the leads they involve). Returns the label (list of maximal minors) or None."""
    rows = pos_sum_rows(names, eqs)
    if not rows:
        return None
    # try subsets of rows: the columns are the leads they involve
    for r in range(1, len(rows) + 1):
        for sub in itertools.combinations(rows, r):
            cols = sorted(set(k for row in sub for k in row), key=str)
            if len(cols) > r:
                continue
            # composite leads (differences) are not single variables: skip those systems
            if any(isinstance(c, tuple) for c in cols):
                continue
            Mx = sp.Matrix([[row.get(c, 0) for c in cols] for row in sub])
            if Mx.rank() == len(cols):
                minors = []
                for rr in itertools.combinations(range(r), len(cols)):
                    d = sp.factor(Mx.extract(list(rr), list(range(len(cols)))).det())
                    if d != 0:
                        minors.append(d)
                return minors
    return None


def fam_B(names, eqs):
    for nm, e in zip(names, eqs):
        rel = relation(nm, e)
        if rel[0] == 'Diff' and not rel[3] and rel[4] == (tuple(sorted(rel[2])),):
            k, l = rel[2]
            return [M[k] + M[l]]
    return None


def dist_leads(e):
    """the two leads of a distance equation, as (zlead, wlead) strings with sign normalised (variable, sign)."""
    leads = LEADRE.findall(e)
    out = {}
    for a, b in leads:
        v = a if a != '0' else b
        col = 'z' if v.startswith('X') else 'w'
        if b == '0':
            out[col] = ((a,), 1)
        elif a == '0':
            out[col] = ((b,), -1)
        else:
            out[col] = ((a, b), 1)
    return out


def fam_P4(names, eqs):
    """AK Prop. 4 / binary torque: body s's c-equation balanced by the forces of a and b only; the c-positions of a, b
    balance (two leads, the c-separations of s from a, b equal to minus these positions, i.e. s at the c-origin); the
    distance equations of sa and sb share the other colour's lead (s is c'-far from a, b in one common direction)."""
    rels = [relation(n, e) for n, e in zip(names, eqs)]
    dists = {}
    for n, e in zip(names, eqs):
        t = eval(n)
        if t[0] == 'D' and len(t) == 3:
            dists[(t[1], t[2])] = dist_leads(e)
    bals = [r for r in rels if r[0] == 'bal' and not r[3] and len(r[4]) == 2]
    # a torque (or a subset sum) whose initial form is c * (m_a F_sa + m_b F_sb) with a common factor c: the same
    # relation as the balance of s; recorded as ('bal', colour, s, False, (a, b))
    for n, e in zip(names, eqs):
        t = eval(n)
        terms = parse_eq(e)
        if t[0] == 'T' and len(terms) == 2 and all(x[0] == 'torq' for x in terms):
            prs = [tuple(sorted((x[1], x[2]))) for x in terms]
            common = set(prs[0]) & set(prs[1])
            if len(common) != 1:
                continue
            s0 = common.pop()
            others = tuple(sorted(set(prs[0]) ^ set(prs[1])))
            leads = [LEADRE.findall(tt) for tt in split_terms(e)]
            # the colour of the non-common lead: the lead not shared by the two terms
            l0 = set(leads[0]); l1 = set(leads[1])
            sh = l0 & l1
            if len(sh) != 1:
                continue
            v = [x for x in sh][0]
            vv = v[0] if v[0] != '0' else v[1]
            col = 'w' if vv.startswith('X') else 'z'
            bals.append(('bal', col, s0, False, others))
        if t[0] == 'S' and len(terms) == 2 and all(x[0] == 'force' for x in terms):
            prs = [(x[1], x[2]) for x in terms]
            common = set(prs[0]) & set(prs[1])
            if len(common) != 1:
                continue
            s0 = common.pop()
            others = tuple(sorted(set(prs[0]) ^ set(prs[1])))
            bals.append(('bal', terms[0][3], s0, False, others))
    sums = [(r, e) for r, e in zip(rels, eqs) if r[0] == 'sum' and not r[5] and len(r[3]) == 2 and r[4] == 2]
    for b in bals:
        c = b[1]
        o = 'w' if c == 'z' else 'z'
        s = b[2]
        a1, a2 = b[4]
        for sm, e in sums:
            if sm[1] != c or set(sm[3]) != {a1, a2}:
                continue
            d1 = dists.get((min(s, a1), max(s, a1)))
            d2 = dists.get((min(s, a2), max(s, a2)))
            if not d1 or not d2:
                continue
            if d1[o][0] != d2[o][0]:
                continue
            # c-separations of s from a1, a2 are single coordinates (s in the child of O): the position leads
            plead = {t[1]: t[3] for t in parse_eq(e) if t[0] == 'pos'}
            ok = True
            for ai, d in ((a1, d1), (a2, d2)):
                pl = plead[ai]
                v = pl[0] if pl[1] == '0' else pl[1]
                if d[c][0] != (v,):
                    ok = False
            if ok:
                return [M[a1] ** 3 + M[a2] ** 3, ('s', s)]
    return None


def classify(names, eqs):
    b = fam_B(names, eqs)
    if b:
        return 'B', b
    lin = fam_lin(names, eqs)
    if lin:
        return 'LIN', lin
    p4 = fam_P4(names, eqs)
    if p4:
        return 'P4', p4
    return None, None


def tri_template(names, eqs, tri_meets=None):
    """Triangle systems of §3.3-3.4 inside a core. Relations on a triple T: balances without positions (bal),
    centre relations (a sum with exactly two positions of T, two leads, no forces: centre at the third vertex s),
    U_T (U or a sub-virial whose initial form is the potential of T). tri_meets(T) -> True if the pairs of T meet at
    one node in each tree (closure); if None, closure is assumed. Returns (system name, T, data) or None."""
    rels = [relation(n, e) for n, e in zip(names, eqs)]
    bodies = set()
    for r in rels:
        if r[0] == 'bal':
            bodies.add(r[2])
            bodies.update(r[4])
    for T in itertools.combinations(sorted(bodies), 3):
        Ts = set(T)
        if tri_meets is not None and not tri_meets(T):
            continue
        bal = {'z': set(), 'w': set()}
        for r in rels:
            if r[0] == 'bal' and not r[3] and r[2] in Ts and set(r[4]) == Ts - {r[2]}:
                bal[r[1]].add(r[2])
        pairs = set(itertools.combinations(T, 2))
        UT = any((r[0] == 'U' and set(r[1]) == pairs and not r[2]) or
                 (r[0] == 'V' and set(r[2]) == pairs and not r[3] and r[4] == 0) for r in rels)
        cen = {'z': set(), 'w': set()}
        for r in rels:
            if r[0] == 'sum' and not r[5] and len(r[3]) == 2 and r[4] == 2 and set(r[3]) <= Ts:
                cen[r[1]].add((Ts - set(r[3])).pop())
        bz, bw = len(bal['z']), len(bal['w'])
        if (bz >= 2 and bw >= 1) or (bw >= 2 and bz >= 1) or (bz >= 1 and bw >= 1 and UT):
            return ('E', T)
        for c, o in (('z', 'w'), ('w', 'z')):
            for s in cen[c]:
                nb = len(bal[c] - {s})
                if nb >= 2 or (nb == 1 and UT):
                    return ('R', T, s)
            for s in cen[o]:
                if (bal[c] - {s}) and UT:
                    return ('R5', T, s)
            for s in cen[c]:
                if s in bal[c] and (bal[o] - {s}):
                    return ('R6', T, s)
    return None
