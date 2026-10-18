#!/usr/bin/env python3
"""Mass conditions of the residual lemmas, instantiated per cell (needs SymPy).

For every residual cell and its first applicable lemma:
  B0, K, TD : no condition (excluded at every mass with the masses involved nonzero);
  L         : the norm of Lemma L (no positive zero; hand proof in RESIDUAL.md);
  R1*       : N(m_a, m_b, m_s, M_A, M_B) = Res_k(M_A m_b k^3 - M_B m_a, m_s^2 (M_A+M_B)(m_a+m_b k)^3 - m_a^3 m_b^2 M_B)
              / (m_a^3 m_b^3)  (irreducible; checks/R1star.sing);
  W3        : (u1 u2 + u2 u3 + u3 u1)^3 - 27 (u1 u2 u3)^2, u_kl = mbar_kl^2 (e_k - e_l), e = shape vector;
  EQ2       : m_a^2 M_A^4 - m_b^2 M_B^4;
  TQ        : the norm of the torque condition (checks/TQ.sing).
Checks: the polynomial is nonzero (generic exclusion); comparison with the engine's label of the cell's core
(labels_all.jsonl, by core hash) when there is one: common factors, and whether the engine label divides ours or
conversely. Output ../data/algebra_resid.jsonl."""
import json, os, sys, random
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
RUNS = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'inputs')   # labels_all.jsonl
MECH = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'hand_explanations', 'mechanisms', 'data')
m = sp.symbols('m0:6')
k = sp.symbols('k')


def R1star_poly(a, b, s, MA, MB):
    ma, mb, ms = m[a], m[b], m[s]
    A = sum(m[i] for i in MA)
    B = sum(m[i] for i in MB)
    res = sp.resultant(A * mb * k**3 - B * ma, ms**2 * (A + B) * (ma + mb * k)**3 - ma**3 * mb**2 * B, k)
    q, r = sp.div(sp.Poly(sp.expand(res), *m), sp.Poly(ma**3 * mb**3, *m))
    assert r.is_zero
    return sp.expand(q.as_expr())


def EQ2_poly(a, b, MA, MB):
    A = sum(m[i] for i in MA)
    B = sum(m[i] for i in MB)
    return sp.expand(m[a]**2 * A**4 - m[b]**2 * B**4)


def TQ_poly(k1, k2, l1, l2):
    n1, n2, M1, M2 = m[k1], m[k2], m[l1], m[l2]
    sext = (n1**6*M1**6 + 2*n1**3*n2**3*M1**6 + n2**6*M1**6 + 2*n1**6*M1**3*M2**3 - 12*n1**3*n2**3*M1**3*M2**3
            + 2*n2**6*M1**3*M2**3 + n1**6*M2**6 + 2*n1**3*n2**3*M2**6 + n2**6*M2**6)
    return sp.expand((n1**2 - n1*n2 + n2**2) * (M1**2 - M1*M2 + M2**2) * sext)


def L_poly(a, b):
    A, B, C = m[a]*m[b], -m[b]*(m[a]+m[b]), -m[a]*(m[a]+m[b])
    return sp.expand((A**3 + B**3 + C**3)**3 - 27*A**3*B**3*C**3)


def W3_poly(w):
    tri = w['tri']
    allch = [str(c) for c in w['children']]
    tch = [str(c) for c in w['tri_children']]
    rows = []
    for rel in w['relations']:
        r = rel[1]
        rows.append([sum((m[i] for i in r.get(ch, [])), sp.Integer(0)) for ch in allch])
    Mx = sp.Matrix(rows)
    ns = Mx.nullspace()
    assert len(ns) == 1, ns
    vec = ns[0]
    den = sp.lcm([sp.fraction(sp.together(x))[1] for x in vec])
    vec = [sp.factor(sp.together(x * den)) for x in vec]
    e = {tri[i]: vec[allch.index(tch[i])] for i in range(3)}
    a, b, c = tri
    u1 = m[c]**2 * (e[a] - e[b])
    u2 = m[a]**2 * (e[b] - e[c])
    u3 = m[b]**2 * (e[c] - e[a])
    H = sp.expand((u1*u2 + u2*u3 + u3*u1)**3 - 27*(u1*u2*u3)**2)
    return H, e


def nonzero(P):
    rng = random.Random(3)
    for _ in range(3):
        val = P.subs({x: sp.Rational(rng.randint(2, 50), rng.randint(1, 7)) for x in m})
        if val != 0:
            return True
    return False


def positive_zero_hint(P, trials=400):
    """sign change of P on random positive points: True if P takes both signs (so it has positive zeros)."""
    rng = random.Random(5)
    f = sp.lambdify(m, P, 'math')
    signs = set()
    for _ in range(trials):
        x = [rng.uniform(0.05, 3.0) for _ in range(6)]
        v = f(*x)
        if v > 0:
            signs.add(1)
        elif v < 0:
            signs.add(-1)
        if len(signs) == 2:
            return True
    return False


def engine_label(c, i):
    cores = {}
    for l in open(os.path.join(MECH, 'cores_h.jsonl')):
        if f'"class": {c}, "cell": {i},' not in l[:40]:
            continue
        r = json.loads(l)
        if r['certified'] is False:
            continue
        cores[(r['class'], r['cell'])] = r
    cr = cores.get((c, i))
    if cr is None:
        return None
    h = cr.get('hash_old') or cr.get('hash')
    for l in open(os.path.join(RUNS, 'labels_all.jsonl')):
        if h in l[:40]:
            r = json.loads(l)
            if r['hash'] == h:
                return r
    return None


def compare(P, lab):
    if lab is None or lab.get('timeout') or not lab.get('gens'):
        return 'no engine label'
    out = []
    for g in lab['gens']:
        G = sp.sympify(g.replace('^', '**'), locals={f'm{j}': m[j] for j in range(6)})
        gc = sp.gcd(sp.Poly(P, *m), sp.Poly(G, *m))
        if gc.total_degree() == 0:
            out.append('coprime')
            continue
        _, rP = sp.div(sp.Poly(P, *m), sp.Poly(G, *m))
        _, rG = sp.div(sp.Poly(G, *m), sp.Poly(P, *m))
        tag = 'equal' if rP.is_zero and rG.is_zero else ('label | ours' if rP.is_zero else
                                                        ('ours | label' if rG.is_zero else 'common factor'))
        out.append(f'{tag} (gcd degree {gc.total_degree()})')
    return '; '.join(out)


def main():
    cover = [json.loads(l) for l in open(os.path.join(DATA, 'resid_cover.jsonl'))]
    out = open(os.path.join(DATA, 'algebra_resid.jsonl'), 'w')
    for r in cover:
        c, i, f = r['class'], r['cell'], r['first']
        w = r['witness'][f]
        rec = {'class': c, 'cell': i, 'first': f}
        P = None
        if f == 'R1*':
            P = R1star_poly(w['a'], w['b'], w['s'], w['MA'], w['MB'])
            rec['roles'] = {'a': w['a'], 'b': w['b'], 's': w['s'], 'MA': w['MA'], 'MB': w['MB']}
        elif f == 'EQ2':
            P = EQ2_poly(w['a'], w['b'], w['MA'], w['MB'])
            rec['roles'] = {'a': w['a'], 'b': w['b'], 's': w['s'], 'MA': w['MA'], 'MB': w['MB']}
        elif f == 'TQ':
            P = TQ_poly(w['k'][0], w['k'][1], w['l'][0], w['l'][1])
            rec['roles'] = {'k': w['k'], 'l': w['l']}
        elif f == 'W3':
            P, e = W3_poly(w)
            rec['roles'] = {'tri': w['tri'], 'shape': {str(kk): str(v) for kk, v in e.items()}}
        elif f == 'L':
            P = L_poly(w['a'], w['b'])
            rec['roles'] = {'a': w['a'], 'b': w['b'], 's': w['s']}
        if P is not None:
            rec['nonzero'] = nonzero(P)
            rec['degree'] = sp.Poly(P, *m).total_degree()
            rec['positive_sign_change'] = positive_zero_hint(P)
            lab = engine_label(c, i) if r['kind'] == 'core' else None
            rec['engine_label_compare'] = compare(P, lab)
            rec['poly'] = str(sp.factor(P)) if len(str(P)) < 4000 else str(P)[:4000] + '...'
        out.write(json.dumps(rec) + '\n')
        print(c, i, f, rec.get('nonzero'), rec.get('degree'), rec.get('positive_sign_change'),
              rec.get('engine_label_compare'), flush=True)


if __name__ == '__main__':
    main()
