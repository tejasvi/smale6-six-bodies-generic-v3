#!/usr/bin/env python3
"""The sets G of Lemma 6.19(a) with the masses as parameters, and the identities that put each element of G into the
ideal of S12 (resp. KC12).

G is built exactly as in the d88 programs (n4_trop.py: n4_system(..., 'all'); kc_trop_cert.py / n4_trop.py:
kc_system(..., 'all', variants=3)); the code below is a transcription. For every g in G we also build cofactors with

    g(xi(v)) = sum_j c_j F_j + c_0 (mu_u * iu - 1)                                   (*)

in Z[mu, iu][v], where F_j are the twelve polynomials of S12 (resp. KC12), iu stands for 1/mu_4 (N4: the positions
X_4, Y_4 by the centre of mass) or 1/mu_3 (KC: the Y-equation of body 3 from the torque identity), and xi(v) are the
seventeen torus coordinates as polynomials in the unknowns v. The cofactors c_j come from the structural formulas
(torques, subset sums, virial, ...); c_0 is the exact quotient of the remainder by mu_u * iu - 1. sympy checks (*).
"""
import sympy as sp

PAIRS = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
mu = sp.symbols('mu1 mu2 mu3 mu4')
m = {i + 1: mu[i] for i in range(4)}
M = sum(mu)


# ------------------------------------------------------------------ G (transcribed from the d88 programs)
def n4_G():
    Xs = {pr: sp.Symbol('X%d%d' % pr) for pr in PAIRS}
    Ys = {pr: sp.Symbol('Y%d%d' % pr) for pr in PAIRS}
    Ps = {pr: sp.Symbol('p%d%d' % pr) for pr in PAIRS}
    Xs[(1, 2)] = sp.Integer(1)
    gens = [Xs[pr] for pr in PAIRS if pr != (1, 2)] + [Ys[pr] for pr in PAIRS] + [Ps[pr] for pr in PAIRS]

    def D(S, k, l):
        return S[(k, l)] if k < l else -S[(l, k)]

    def P(k, l):
        return Ps[(min(k, l), max(k, l))]
    polys, kinds = [], []
    for nm, S in (('X', Xs), ('Y', Ys)):
        for t, f in enumerate([D(S, 1, 3) - D(S, 1, 2) - D(S, 2, 3), D(S, 1, 4) - D(S, 1, 2) - D(S, 2, 4),
                               D(S, 3, 4) - D(S, 1, 4) + D(S, 1, 3)]):
            polys.append(f); kinds.append(('cycle', nm, t))
    pos = {}
    for name, S in (('X', Xs), ('Y', Ys)):
        pos[name] = {k: sum(m[l] * D(S, k, l) for l in m if l != k) / M for k in m}
    for name, S in (('X', Xs), ('Y', Ys)):
        for k in m:
            polys.append(sp.expand(M * (pos[name][k] - sum(m[l] * P(k, l) ** 3 * D(S, k, l) for l in m if l != k))))
            kinds.append(('body', name, k))
    for pr in PAIRS:
        polys.append(Ps[pr] ** 2 * Xs[pr] * Ys[pr] - 1); kinds.append(('dist', pr))
    X, Y = pos['X'], pos['Y']
    for J in [(1, 2), (1, 3), (1, 4)]:
        T = sum(m[k] * m[l] * P(k, l) ** 3 * (X[k] * Y[l] - X[l] * Y[k]) for k in J for l in m if l not in J)
        polys.append(sp.expand(M * M * T)); kinds.append(('torque', J))
    for J in [(1, 2), (1, 3), (1, 4)]:
        for name, S in (('X', Xs), ('Y', Ys)):
            Z = pos[name]
            SJ = sum(m[k] * Z[k] for k in J) - sum(m[k] * m[l] * P(k, l) ** 3 * D(S, k, l) for k in J for l in m if l not in J)
            polys.append(sp.expand(M * SJ)); kinds.append(('subset', name, J))
    U = sum(m[k] * m[l] * P(k, l) for (k, l) in PAIRS)
    V = sum(m[k] * X[k] * Y[k] for k in m)
    polys.append(sp.expand(M * M * (V - U))); kinds.append(('virial',))
    out = []
    for f, kd in zip(polys, kinds):
        f = sp.cancel(sp.together(sp.expand(f)))
        num, den = sp.fraction(f)
        assert den == 1, (kd, den)
        num = sp.expand(num)
        if num != 0:
            out.append((num, kd))
    return out, gens


def kc_G(variants=3):
    X = {1: sp.Integer(1), 2: sp.Symbol('X2'), 3: sp.Symbol('X3'), 4: sp.Integer(0)}
    U = {1: sp.Symbol('U1'), 2: sp.Symbol('U2'), 3: sp.Symbol('U3'), 4: sp.Integer(0)}
    Xd = {(1, 2): sp.Symbol('X12'), (1, 3): sp.Symbol('X13'), (2, 3): sp.Symbol('X23')}
    Ud = {(1, 2): sp.Symbol('U12'), (1, 3): sp.Symbol('U13'), (2, 3): sp.Symbol('U23')}
    Ps = {pr: sp.Symbol('p%d%d' % pr) for pr in PAIRS}
    gens = [X[2], X[3], Xd[(1, 2)], Xd[(1, 3)], Xd[(2, 3)], U[1], U[2], U[3], Ud[(1, 2)], Ud[(1, 3)], Ud[(2, 3)]] + \
        [Ps[pr] for pr in PAIRS]

    def DX(k, l):
        if l == 4:
            return X[k]
        if k == 4:
            return -X[l]
        return Xd[(k, l)] if k < l else -Xd[(l, k)]

    def DU(k, l):
        if l == 4:
            return U[k]
        if k == 4:
            return -U[l]
        return Ud[(k, l)] if k < l else -Ud[(l, k)]

    def P(k, l):
        return Ps[(min(k, l), max(k, l))]
    polys, kinds = [], []
    for (k, l) in [(1, 2), (1, 3), (2, 3)]:
        polys.append(Xd[(k, l)] - X[k] + X[l]); kinds.append(('xdiff', (k, l)))
        polys.append(Ud[(k, l)] - U[k] + U[l]); kinds.append(('udiff', (k, l)))
    for k in (1, 2, 3, 4):
        polys.append(X[k] - sum(m[l] * P(k, l) ** 3 * DX(k, l) for l in m if l != k)); kinds.append(('xbody', k))
    R = {k: U[k] - sum(m[l] * P(k, l) ** 3 * DU(k, l) for l in m if l != k) for k in (1, 2, 3)}
    polys.append(sp.expand(R[2] - R[1])); kinds.append(('ydiff', 2, 1))
    polys.append(sp.expand(R[3] - R[1])); kinds.append(('ydiff', 3, 1))
    for (k, l) in [(1, 2), (1, 3), (2, 3)]:
        Rk = -sum(m[j] * P(k, j) ** 3 * DU(k, j) for j in m if j != k)
        Rl = -sum(m[j] * P(l, j) ** 3 * DU(l, j) for j in m if j != l)
        polys.append(sp.expand(Ud[(k, l)] + Rk - Rl)); kinds.append(('ydiff', k, l))
    for (k, l) in PAIRS:
        polys.append(P(k, l) ** 2 * DX(k, l) * DU(k, l) - 1); kinds.append(('dist', (k, l)))
    for kk in ((1, 2, 3) if variants == 3 else (1,)):
        Y4 = -R[kk]
        Yp = {k: Y4 + U[k] for k in (1, 2, 3)}
        Yp[4] = Y4
        for J in [(1,), (2,), (3,), (1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (3, 4)]:
            T = sum(m[k] * m[l] * P(k, l) ** 3 * (X[k] * Yp[l] - X[l] * Yp[k]) for k in J for l in m if l not in J)
            polys.append(sp.expand(T)); kinds.append(('torque', kk, J))
    for J in [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (3, 4)]:
        SJ = sum(m[k] * X[k] for k in J) - sum(m[k] * m[l] * P(k, l) ** 3 * DX(k, l) for k in J for l in m if l not in J)
        polys.append(sp.expand(SJ)); kinds.append(('xsubset', J))
    polys.append(sp.expand(sum(m[k] * X[k] for k in (1, 2, 3)))); kinds.append(('xcentre',))
    for J in [(1, 2, 3), (1, 2, 4), (1, 3, 4), (2, 3, 4)]:
        SJ = sum(m[k] * X[k] for k in J) - sum(m[k] * m[l] * P(k, l) ** 3 * DX(k, l) for k in J for l in m if l not in J)
        polys.append(sp.expand(SJ)); kinds.append(('xsubset', J))
    SY = {}
    for kk in ((1, 2, 3) if variants == 3 else (1,)):
        Y4e = -R[kk]
        for J in [(1,), (2,), (3,), (1, 2), (1, 3), (2, 3), (1, 2, 3)]:
            SY[J] = sum(m[k] * (Y4e + U[k]) for k in J) - sum(m[k] * m[l] * P(k, l) ** 3 * DU(k, l) for k in J for l in m if l not in J)
            polys.append(sp.expand(SY[J])); kinds.append(('ysubset', kk, J))
    Uu = sum(m[k] * m[l] * P(k, l) for (k, l) in PAIRS)
    for kk in ((2, 3) if variants == 3 else ()):
        V = sum(m[k] * X[k] * (-R[kk] + U[k]) for k in (1, 2, 3))
        polys.append(sp.expand(V - Uu)); kinds.append(('virial', kk))
    Js = list(SY)
    for a in range(len(Js)):
        for b in range(a + 1, len(Js)):
            A, B = Js[a], Js[b]
            ma, mb = sum(m[k] for k in A), sum(m[k] for k in B)
            SA = sum(m[k] * U[k] for k in A) - sum(m[k] * m[l] * P(k, l) ** 3 * DU(k, l) for k in A for l in m if l not in A)
            SB = sum(m[k] * U[k] for k in B) - sum(m[k] * m[l] * P(k, l) ** 3 * DU(k, l) for k in B for l in m if l not in B)
            polys.append(sp.expand(mb * SA - ma * SB)); kinds.append(('ypair', A, B))
    Y4 = -R[1]
    V = sum(m[k] * X[k] * (Y4 + U[k]) for k in (1, 2, 3))
    polys.append(sp.expand(V - Uu)); kinds.append(('virial', 1))
    out = [(sp.expand(f), kd) for f, kd in zip(polys, kinds) if sp.expand(f) != 0]
    return out, gens


# ------------------------------------------------------------------ the systems S12, KC12 and xi(v)
iu = sp.Symbol('iu')


def n4_base():
    X2, X3, Y1, Y2, Y3 = sp.symbols('vX2 vX3 vY1 vY2 vY3')
    Pv = {pr: sp.Symbol('vp%d%d' % pr) for pr in PAIRS}
    v = [X2, X3, Y1, Y2, Y3] + [Pv[pr] for pr in PAIRS]
    X = {1: X2 + 1, 2: X2, 3: X3}
    Y = {1: Y1, 2: Y2, 3: Y3}
    X[4] = -(mu[0] * X[1] + mu[1] * X[2] + mu[2] * X[3]) * iu
    Y[4] = -(mu[0] * Y[1] + mu[1] * Y[2] + mu[2] * Y[3]) * iu

    def P(k, l):
        return Pv[(min(k, l), max(k, l))]
    Xeq = {k: X[k] - sum(m[l] * P(k, l) ** 3 * (X[k] - X[l]) for l in m if l != k) for k in m}
    Yeq = {k: Y[k] - sum(m[l] * P(k, l) ** 3 * (Y[k] - Y[l]) for l in m if l != k) for k in m}
    Dst = {pr: P(*pr) ** 2 * (X[pr[0]] - X[pr[1]]) * (Y[pr[0]] - Y[pr[1]]) - 1 for pr in PAIRS}
    F = [Xeq[1], Xeq[2], Xeq[3], Yeq[1], Yeq[2], Yeq[3]] + [Dst[pr] for pr in PAIRS]
    xi = {}
    for pr in PAIRS:
        if pr != (1, 2):
            xi['X%d%d' % pr] = X[pr[0]] - X[pr[1]]
    for pr in PAIRS:
        xi['Y%d%d' % pr] = Y[pr[0]] - Y[pr[1]]
    for pr in PAIRS:
        xi['p%d%d' % pr] = P(*pr)
    return dict(v=v, X=X, Y=Y, Xeq=Xeq, Yeq=Yeq, Dst=Dst, F=F, xi=xi, P=P, unit=mu[3])


def kc_base():
    X2, X3, Y1, Y2, Y3, Y4 = sp.symbols('vX2 vX3 vY1 vY2 vY3 vY4')
    Pv = {pr: sp.Symbol('vp%d%d' % pr) for pr in PAIRS}
    v = [X2, X3, Y1, Y2, Y3, Y4] + [Pv[pr] for pr in PAIRS]
    X = {1: sp.Integer(1), 2: X2, 3: X3, 4: sp.Integer(0)}
    Y = {1: Y1, 2: Y2, 3: Y3, 4: Y4}

    def P(k, l):
        return Pv[(min(k, l), max(k, l))]
    Xeq = {k: X[k] - sum(m[l] * P(k, l) ** 3 * (X[k] - X[l]) for l in m if l != k) for k in m}
    Yeq = {k: Y[k] - sum(m[l] * P(k, l) ** 3 * (Y[k] - Y[l]) for l in m if l != k) for k in m}
    Dst = {pr: P(*pr) ** 2 * (X[pr[0]] - X[pr[1]]) * (Y[pr[0]] - Y[pr[1]]) - 1 for pr in PAIRS}
    F = [Xeq[1], Xeq[2], Xeq[3], Xeq[4], Yeq[1], Yeq[2]] + [Dst[pr] for pr in PAIRS]
    xi = {'X2': X2, 'X3': X3, 'X12': X[1] - X2, 'X13': X[1] - X3, 'X23': X2 - X3,
          'U1': Y1 - Y4, 'U2': Y2 - Y4, 'U3': Y3 - Y4, 'U12': Y1 - Y2, 'U13': Y1 - Y3, 'U23': Y2 - Y3}
    for pr in PAIRS:
        xi['p%d%d' % pr] = P(*pr)
    return dict(v=v, X=X, Y=Y, Xeq=Xeq, Yeq=Yeq, Dst=Dst, F=F, xi=xi, P=P, unit=mu[2])


# ------------------------------------------------------------------ cofactors
def n4_combo(kd, B):
    """g(xi(v)) as a combination of the extended generators (Xeq_4, Yeq_4 allowed), as a dict gen -> cofactor."""
    X, Y, Xeq, Yeq, P = B['X'], B['Y'], B['Xeq'], B['Yeq'], B['P']
    c = {}

    def add(key, val):
        c[key] = sp.expand(c.get(key, 0) + val)
    if kd[0] == 'cycle':
        pass
    elif kd[0] == 'body':
        add((kd[1] + 'eq', kd[2]), M)
    elif kd[0] == 'dist':
        add(('D', kd[1]), 1)
    elif kd[0] == 'torque':
        for k in kd[1]:
            add(('Xeq', k), -M * M * m[k] * Y[k])
            add(('Yeq', k), M * M * m[k] * X[k])
    elif kd[0] == 'subset':
        for k in kd[2]:
            add((kd[1] + 'eq', k), M * m[k])
    elif kd[0] == 'virial':
        for k in m:
            add(('Xeq', k), M * M * m[k] * Y[k])
        for pr in PAIRS:
            add(('D', pr), M * M * m[pr[0]] * m[pr[1]] * P(*pr))
    else:
        raise ValueError(kd)
    return c


def kc_combo(kd, B):
    X, Y, Xeq, Yeq, P = B['X'], B['Y'], B['Xeq'], B['Yeq'], B['P']
    c = {}

    def add(key, val):
        c[key] = sp.expand(c.get(key, 0) + val)

    def torqueY(J, shift_k=None):
        # T_J(Y) = -sum_{k in J} mu_k (Y_k Xeq_k - X_k Yeq_k); with Y replaced by Y - Yeq_kk (all bodies):
        # T_J(Y - s) = T_J(Y) - s * sum_{k in J, l notin J} mu_k mu_l p^3 (X_k - X_l)
        for k in J:
            add(('Xeq', k), -m[k] * Y[k])
            add(('Yeq', k), m[k] * X[k])
        if shift_k is not None:
            add(('Yeq', shift_k), -sum(m[k] * m[l] * P(k, l) ** 3 * (X[k] - X[l]) for k in J for l in m if l not in J))
    if kd[0] in ('xdiff', 'udiff'):
        pass
    elif kd[0] == 'xbody':
        add(('Xeq', kd[1]), 1)
    elif kd[0] == 'ydiff':
        add(('Yeq', kd[1]), 1)
        add(('Yeq', kd[2]), -1)
    elif kd[0] == 'dist':
        add(('D', kd[1]), 1)
    elif kd[0] == 'torque':
        torqueY(kd[2], kd[1])
    elif kd[0] == 'xsubset':
        for k in kd[1]:
            add(('Xeq', k), m[k])
    elif kd[0] == 'xcentre':
        for k in m:
            add(('Xeq', k), m[k])
    elif kd[0] == 'ysubset':
        kk, J = kd[1], kd[2]
        for k in J:
            add(('Yeq', k), m[k])
        add(('Yeq', kk), -sum(m[k] for k in J))
    elif kd[0] == 'virial':
        kk = kd[1]
        for k in m:
            add(('Xeq', k), m[k] * Y[k])
        for pr in PAIRS:
            add(('D', pr), m[pr[0]] * m[pr[1]] * P(*pr))
        add(('Yeq', kk), -sum(m[k] * X[k] for k in (1, 2, 3)))
    elif kd[0] == 'ypair':
        A, Bb = kd[1], kd[2]
        ma, mb = sum(m[k] for k in A), sum(m[k] for k in Bb)
        for k in A:
            add(('Yeq', k), mb * m[k])
        for k in Bb:
            add(('Yeq', k), -ma * m[k])
    else:
        raise ValueError(kd)
    return c


def reduce_extended(c, B, kind):
    """Rewrite the extended generators through the base system F (indices 0..11) and the unit iu:
    N4: Xeq_4 = -iu (mu1 Xeq_1 + mu2 Xeq_2 + mu3 Xeq_3) (mod mu4 iu - 1), likewise Yeq_4;
    KC: Yeq_3 = iu p34^2 (Y3 - Y4) T - Yeq_3 D34 (mod mu3 iu - 1), T = sum_k mu_k Y_k Xeq_k - mu1 X1 Yeq1 - mu2 X2 Yeq2;
        Yeq_4 never occurs with a nonzero cofactor (X_4 = 0)."""
    X, Y, P = B['X'], B['Y'], B['P']
    if kind == 'n4':
        idx = {('Xeq', 1): 0, ('Xeq', 2): 1, ('Xeq', 3): 2, ('Yeq', 1): 3, ('Yeq', 2): 4, ('Yeq', 3): 5}
    else:
        idx = {('Xeq', 1): 0, ('Xeq', 2): 1, ('Xeq', 3): 2, ('Xeq', 4): 3, ('Yeq', 1): 4, ('Yeq', 2): 5}
    for j, pr in enumerate(PAIRS):
        idx[('D', pr)] = 6 + j
    out = [sp.Integer(0)] * 12
    for key, val in c.items():
        if val == 0:
            continue
        if key in idx:
            out[idx[key]] += val
        elif kind == 'n4' and key[1] == 4:
            nm = key[0]
            base = 0 if nm == 'Xeq' else 3
            for k in (1, 2, 3):
                out[base + k - 1] += -iu * m[k] * val
        elif kind == 'kc' and key == ('Yeq', 3):
            # Yeq_3 -> iu p34^2 (Y3 - Y4) T - Yeq_3 D34
            f = iu * P(3, 4) ** 2 * (Y[3] - Y[4]) * val
            for k in (1, 2, 3, 4):
                out[idx[('Xeq', k)]] += f * m[k] * Y[k]
            out[idx[('Yeq', 1)]] += -f * m[1] * X[1]
            out[idx[('Yeq', 2)]] += -f * m[2] * X[2]
            out[idx[('D', (3, 4))]] += -B['Yeq'][3] * val
        elif kind == 'kc' and key == ('Yeq', 4):
            raise ValueError('Yeq_4 with nonzero cofactor')
        else:
            raise ValueError(key)
    return [sp.expand(x) for x in out]


def certify(kind):
    G, gens = (n4_G() if kind == 'n4' else kc_G())
    B = n4_base() if kind == 'n4' else kc_base()
    sub = {g: B['xi'][str(g)] for g in gens}
    rel = sp.expand(B['unit'] * iu - 1)
    res = []
    for g, kd in G:
        gx = sp.expand(g.subs(sub, simultaneous=True))
        c = (n4_combo if kind == 'n4' else kc_combo)(kd, B)
        cof = reduce_extended(c, B, kind)
        D = sp.expand(gx - sum(cj * Fj for cj, Fj in zip(cof, B['F'])))
        q, r = sp.div(sp.Poly(D, iu, *B['v'], *mu), sp.Poly(rel, iu, *B['v'], *mu))
        assert r.is_zero, (kd, r)
        c0 = sp.expand(q.as_expr())
        assert sp.expand(gx - sum(cj * Fj for cj, Fj in zip(cof, B['F'])) - c0 * rel) == 0
        res.append(dict(g=g, kind=kd, cof=cof, c0=c0))
    return res, gens, B


if __name__ == '__main__':
    import sys
    import time
    for kind in sys.argv[1:] or ['n4', 'kc']:
        t0 = time.time()
        res, gens, B = certify(kind)
        print(kind, len(res), 'polynomials; identities verified (sympy) in %.1fs' % (time.time() - t0))
