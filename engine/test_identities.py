#!/usr/bin/env python3
"""Numerical check of the identities of texact.py/tsec.py on complex solutions of the normalized equations
z_k = sum_l m_l delta_kl^3 (z_k - z_l), w_k = sum_l m_l delta_kl^3 (w_k - w_l), delta_kl^2 z_kl w_kl = 1.
Solutions by Newton (least squares) from random complex starts. Each identity is evaluated term by term with the
same term definitions as the engine (signs and mass factors included); the sums must vanish."""
import itertools, sys
import numpy as np
sys.path.insert(0, '.')

rng = np.random.default_rng(7)


def solve(n, m, tries=200):
    P = list(itertools.combinations(range(n), 2))
    N = 2 * n + len(P)

    def F(u):
        z, w, d = u[:n], u[n:2 * n], u[2 * n:]
        out = []
        for k in range(n):
            out.append(z[k] - sum(m[l] * d[P.index((min(k, l), max(k, l)))] ** 3 * (z[k] - z[l]) for l in range(n) if l != k))
        for k in range(n):
            out.append(w[k] - sum(m[l] * d[P.index((min(k, l), max(k, l)))] ** 3 * (w[k] - w[l]) for l in range(n) if l != k))
        for i, (k, l) in enumerate(P):
            out.append(d[i] ** 2 * (z[k] - z[l]) * (w[k] - w[l]) - 1)
        return np.array(out)

    def J(u, h=1e-7):
        f0 = F(u)
        Jm = np.zeros((N, N), dtype=complex)
        for i in range(N):
            e = np.zeros(N, dtype=complex)
            e[i] = h
            Jm[:, i] = (F(u + e) - f0) / h
        return Jm

    sols = []
    for _ in range(tries):
        u = rng.normal(size=N) + 1j * rng.normal(size=N)
        for it in range(80):
            f = F(u)
            if np.linalg.norm(f) < 1e-13:
                break
            du = np.linalg.lstsq(J(u), -f, rcond=None)[0]
            u = u + du
        if np.linalg.norm(F(u)) < 1e-11:
            sols.append(u)
        if len(sols) >= 3:
            break
    return sols, P


def check(n):
    m = rng.uniform(0.5, 3.0, size=n)
    sols, P = solve(n, m)
    print(f'n={n}: {len(sols)} solutions')
    worst = {}
    for u in sols:
        z, w, d = u[:n], u[n:2 * n], u[2 * n:]
        D = lambda a, b: d[P.index((min(a, b), max(a, b)))]
        zs = lambda a, b: z[a] - z[b]
        ws = lambda a, b: w[a] - w[b]
        M = m.sum()
        E = sum(m[k] * m[l] * D(k, l) for k, l in P)
        vals = {}
        # (S_J) z and w
        for r in range(1, n):
            for J in itertools.combinations(range(n), r):
                Jc = [j for j in range(n) if j not in J]
                for col, X in (('z', zs), ('w', ws)):
                    pos = z if col == 'z' else w
                    s = sum(m[i] * pos[i] for i in J) - sum(m[i] * m[j] * D(i, j) ** 3 * X(i, j) for i in J for j in Jc)
                    vals[('S', col, J)] = s
                # (T_J)
                vals[('T', J)] = sum(m[k] * m[l] * D(k, l) ** 3 * (z[k] * w[l] - w[k] * z[l]) for k in J for l in Jc)
                # (V_J)
                vals[('V', J)] = (sum(m[k] * z[k] * w[k] for k in J) - sum(m[k] * m[l] * D(k, l) for k, l in itertools.combinations(J, 2))
                                  - 0.5 * sum(m[k] * m[l] * D(k, l) ** 3 * (w[k] * zs(k, l) + z[k] * ws(k, l)) for k in J for l in Jc))
        for k, l in P:
            for col, X in (('z', zs), ('w', ws)):
                vals[('D', col, k, l)] = (X(k, l) - sum(m[j] * D(k, j) ** 3 * X(k, j) for j in range(n) if j != k)
                                          + sum(m[j] * D(l, j) ** 3 * X(l, j) for j in range(n) if j != l))
        vals[('UI',)] = E - sum(m[k] * z[k] * w[k] for k in range(n))
        vals[('I',)] = sum(m[k] * m[l] * zs(k, l) * ws(k, l) for k, l in P) - M * E
        vals[('com',)] = sum(m[k] * z[k] for k in range(n))
        for key, v in vals.items():
            t = key[0]
            worst[t] = max(worst.get(t, 0.0), abs(v))
    print('  largest residual by identity type:', {k: f'{v:.1e}' for k, v in worst.items()})


for n in (4, 5):
    check(n)
