#!/usr/bin/env python3
"""Numerical sanity check (not part of the proof) of the compact model of C4 (DERIVATION.md, Lemma C).

Solve the ORIGINAL system C4 numerically with mu1, mu2, mu3 fixed (random complex) and mu4 unknown:
  unknowns xi2, xi3, eta2, eta3, p12..p34, c, mu4   (xi1 = eta1 = 1, xi4 = eta4 = 0)
  equations F^xi_k = 0 (k = 1,2,3), F^eta_k = c (k = 1,2,3), p_kl^2 xi_kl eta_kl = 1 (6 pairs)
(the centre condition sum_{k<=3} mu_k xi_k = 0 is NOT imposed; it must come out, by the torque identity).
Then check, at each solution: the centre condition, and the model equations (I), (II), (III) of c4_systems with
(s, t) = (xi1, xi2)/mu3 (complex masses are allowed in the identities).
"""
import random
import mpmath as mp

mp.mp.dps = 40
random.seed(7)
B = range(4)
PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def unpack(v, mu123):
    xi = [mp.mpf(1), v[0], v[1], mp.mpf(0)]
    eta = [mp.mpf(1), v[2], v[3], mp.mpf(0)]
    p = dict(zip(PAIRS, v[4:10]))
    c = v[10]
    mu = list(mu123) + [v[11]]
    return xi, eta, p, c, mu


def P(p, k, l):
    return p[(min(k, l), max(k, l))]


def F(v, mu123):
    xi, eta, p, c, mu = unpack(v, mu123)
    out = []
    for k in range(3):
        out.append(sum(mu[l] * P(p, k, l) ** 3 * (xi[k] - xi[l]) for l in B if l != k))
    for k in range(3):
        out.append(sum(mu[l] * P(p, k, l) ** 3 * (eta[k] - eta[l]) for l in B if l != k) - c)
    for (k, l) in PAIRS:
        out.append(p[(k, l)] ** 2 * (xi[k] - xi[l]) * (eta[k] - eta[l]) - 1)
    return out


def model_residuals(xi, p, c, mu):
    s, t = xi[0] / mu[2], xi[1] / mu[2]
    X = [mu[2] * s, mu[2] * t, -(mu[0] * s + mu[1] * t), mp.mpf(0)]
    res = []
    for k in B:
        res.append(sum(mu[l] * P(p, k, l) ** 3 * (X[k] - X[l]) for l in B if l != k))
    for k in range(3):
        tot = 0
        for l in B:
            if l != k:
                tm = mu[l] * P(p, k, l)
                for j in B:
                    if j not in (k, l):
                        tm *= (X[k] - X[j])
                tot += tm
        pr = 1
        for l in B:
            if l != k:
                pr *= (X[k] - X[l])
        res.append(tot - c * pr)
    a = lambda k, l: P(p, k, l) ** 2 * (X[k] - X[l])
    for (k, l, n) in [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]:
        res.append(a(l, n) * a(n, k) + a(k, l) * a(n, k) + a(k, l) * a(l, n))
    return res, X


def main():
    mu123 = [mp.mpc(random.uniform(1, 3), random.uniform(-.5, .5)) for _ in range(3)]
    found = []
    for trial in range(400):
        v0 = [mp.mpc(random.uniform(-2, 2), random.uniform(-2, 2)) for _ in range(12)]
        try:
            sol = mp.findroot(lambda *v: F(list(v), mu123), v0, tol=1e-30, maxsteps=60)
        except Exception:
            continue
        v = [sol[i] for i in range(12)]
        if max(abs(x) for x in F(v, mu123)) > 1e-25 or max(abs(x) for x in v) > 1e6:
            continue
        xi, eta, p, c, mu = unpack(v, mu123)
        if abs(c) < 1e-8 or min(abs(x) for x in p.values()) < 1e-6:
            continue
        if any(abs(v[11] - f[11]) < 1e-15 and abs(v[0] - f[0]) < 1e-15 for f in found):
            continue
        found.append(v)
        centre = sum(mu[k] * xi[k] for k in range(3))
        res, X = model_residuals(xi, p, c, mu)
        scale = max(abs(x) for x in v)
        print('sol %d: mu4 = %s  |c| = %.3g  centre = %.2e  max model residual = %.2e'
              % (len(found), mp.nstr(mu[3], 8), float(abs(c)), float(abs(centre)), float(max(abs(r) for r in res))))
        if len(found) >= 5:
            break
    print('solutions found:', len(found))


if __name__ == '__main__':
    main()
