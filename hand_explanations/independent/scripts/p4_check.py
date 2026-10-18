#!/usr/bin/env python3
"""Independent check of the P4 template on the 41 template-only P4 cells: from the engine core's identities (whose
argmins were confirmed by verify_templates.py) and the referee's own trees:
 (i) a centre relation m_a Y_a + m_b Y_b = 0: a subset sum S_J^c (J = {a,b}) whose argmin is exactly pos a, pos b,
     with distinct position leads;
 (ii) s with yhat_sa = -Y_a, yhat_sb = -Y_b in colour c: s lies in the O-child (or at O) of u_a = meet_c(a,O) and
     meet_c(s,a) = u_a, same for b;
 (iii) a relation proportional to m_a P_sa^3 yhat_sa + m_b P_sb^3 yhat_sb: the c-equation of s with argmin exactly
     {cross(s,a), cross(s,b)}, or a torque/subset sum of the core whose argmin is two terms of the pairs sa, sb sharing
     the factor of s;
 (iv) in the other colour, meet(s,a) = meet(s,b) and a, b in one child (common lead of the distance equations).
Then m_a^3 + m_b^3 = 0 (Lemma P4), impossible at positive masses."""
import json, os, sys, re
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refkit as K
from refkit import O, BODIES
part = json.load(open('partition.json'))
TARGET = set(tuple(x) for x in part['P4'])
if os.environ.get('ALL_TEMPLATES'):
    TARGET = {(json.loads(l)['class'], json.loads(l)['cell']) for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'coverage.jsonl')) if json.loads(l)['first'] == 'coreP4'}
mech, cores, recs = {}, {}, {}
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'coverage.jsonl')):
    r = json.loads(l)
    if (r['class'], r['cell']) in TARGET and r['first'] == 'coreP4':
        mech[(r['class'], r['cell'])] = r
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data', 'cores_h.jsonl')):
    r = json.loads(l)
    k = (r['class'], r['cell'])
    if k in mech and r['certified'] is not False and (k not in cores or r['certified'] is True):
        cores[k] = r
for c, i, rec in K.iter_cells({c for c, _ in mech}):
    if (c, i) in mech:
        recs[(c, i)] = rec


def in_ochild(tr, v, k):
    if tr.at_origin(k):
        return True
    co = tr.child_to(v, O)
    return co is not None and tr.child_to(v, k) == co


res = Counter()
for key in sorted(mech):
    C = K.RCell(recs[key], *key)
    poly, s_lab = mech[key]['core_fam'][1]
    a, b = [int(x) for x in re.findall(r'm(\d)', poly)]
    s = int(re.search(r'\d', s_lab).group())
    names = [eval(n) for n in cores[key]['names']]
    found = False
    for col in 'zw':
        oc = 'w' if col == 'z' else 'z'
        tr, to = C.tree(col), C.tree(oc)
        # (i) centre relation: S_{a,b}^col in the core (its argmin was confirmed to be pos a, pos b by verify_templates)
        has_centre = ('S', col, tuple(sorted((a, b)))) in names
        if not has_centre:
            continue
        ua, ub = tr.meet(a, O), tr.meet(b, O)
        if ua is None or ub is None or (ua, tr.child_to(ua, a)) == (ub, tr.child_to(ub, b)):
            continue
        # (ii)
        if not (tr.meet(s, a) == ua and in_ochild(tr, ua, s) and tr.meet(s, b) == ub and in_ochild(tr, ub, s)):
            continue
        # (iv)
        v = to.meet(s, a)
        if v is None or to.meet(s, b) != v or to.child_to(v, a) != to.child_to(v, b):
            continue
        # (iii) balance of s in col with exactly the forces of a and b, or a torque/subset sum in the core
        bal = C.A[(col, s)] == frozenset({('cross', s, a), ('cross', s, b)})
        other = [n for n in names if n[0] in ('T', 'S') and n != ('S', col, tuple(sorted((a, b))))]
        res['(iii) balance' if bal else '(iii) via ' + ','.join(str(n[0]) for n in other)] += 1
        found = True
        break
    res['ok' if found else 'FAIL'] += 1
    if not found:
        print('fail', key, poly, s, names)
print(dict(res))
# (iii) for the torque cases: the minimal terms of the torque (confirmed equal to the engine's by verify_templates.py)
# are z_s w_a, z_s w_b (centre colour w) or z_a w_s, z_b w_s (centre colour z): recompute them here from the core text.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_templates import engine_terms_T
cnt = Counter()
for key in sorted(mech):
    C = K.RCell(recs[key], *key)
    poly, s_lab = mech[key]['core_fam'][1]
    a, b = [int(x) for x in re.findall(r'm(\d)', poly)]
    s = int(re.search(r'\d', s_lab).group())
    for nm, eq in zip(cores[key]['names'], cores[key]['core_sym']):
        t = eval(nm)
        if t[0] != 'T':
            continue
        terms = engine_terms_T(eq, C)
        ok = terms in ({(s, a), (s, b)}, {(a, s), (b, s)})
        col = 'w' if terms == {(s, a), (s, b)} else 'z'
        cen = ('S', col, tuple(sorted((a, b)))) in [eval(n) for n in cores[key]['names']]
        cnt[('torque terms ok', ok, 'centre colour matches', cen)] += 1
print(dict(cnt))
from verify_templates import engine_terms_S
cnt = Counter()
for key in sorted(mech):
    C = K.RCell(recs[key], *key)
    poly, s_lab = mech[key]['core_fam'][1]
    a, b = [int(x) for x in re.findall(r'm(\d)', poly)]
    s = int(re.search(r'\d', s_lab).group())
    for nm, eq in zip(cores[key]['names'], cores[key]['core_sym']):
        t = eval(nm)
        if t[0] != 'S' or t[2] == tuple(sorted((a, b))):
            continue
        J = t[2]
        terms = engine_terms_S(eq, J)
        if s in J:
            ok = terms == {('cross', s, a), ('cross', s, b)}
        else:
            ok = terms == {('cross', a, s), ('cross', b, s)}
        cnt[('S two forces of s', ok)] += 1
print(dict(cnt))
cnt = Counter()
for key in sorted(mech):
    poly, s_lab = mech[key]['core_fam'][1]
    a, b = [int(x) for x in re.findall(r'm(\d)', poly)]
    names = [eval(n) for n in cores[key]['names']]
    cen = {n[1] for n in names if n[0] == 'S' and n[2] == tuple(sorted((a, b)))}
    for n in names:
        if n[0] == 'S' and n[2] != tuple(sorted((a, b))):
            cnt[('S colour in centre colours', n[1] in cen, len(cen))] += 1
print(dict(cnt))
