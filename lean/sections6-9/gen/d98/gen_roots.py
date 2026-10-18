"""Root enclosures of S_mu at mu = (1,2,7) and (1,2,8) for the Lean check of the paragraph after Lemma 6.13.

Usage: python3 -I gen_roots.py OUT_LEAN OUT_LOG

For each factor f of S_mu (t^2 - t + 1, N01, N10, N11, Q_sigma(t - 1) for the four sigma; the integer coefficient lists
of the Lean functions lagUP, ..., UP.comp (QUP ...) tm1UP), the roots are computed by mpmath (proposals only) and
rounded to centres c = (a + b i) / 2^K. Lean checks, in integer arithmetic: |f(c)| < |lc(f)| r^d with r = 2^-m and
d = deg f (so each disk D(c, r) contains a root), the disks of one factor are pairwise disjoint and there are d of them
(so they contain all the roots of f), and on each disk the bounds of |l_k| and of the ratios A_1/A_3, A_2/A_3 that give
rho >= 0.7641079385 (resp. 0.7990358445 at (1,2,8)) and rho > 1/sqrt 2. For the disk of the smallest rho at (1,2,7),
lower bounds of the ratios give rho <= 0.7641079386 there.
"""
import sys
from fractions import Fraction as Fr
from math import isqrt
import mpmath as mp

mp.mp.dps = 120
K = 256
SIGMAS = [(1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)]


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def pcomp(p, q):
    acc = []
    for a in reversed(p):
        acc = padd([a], pmul(q, acc) if acc else [])
    return acc


def Qexp(m1, m2, m3, a, b, c):
    return [-(m2 + m3) * c, -(2 * m2 + 3 * m3) * c, m1 * (a - b) - (m2 + 3 * m3) * c,
            (3 * m1 + m2) * a + m3 * (b - c), (3 * m1 + 2 * m2) * a, (m1 + m2) * a]


def factors(mu):
    m1, m2, m3 = mu
    fs = [('lag', [1, -1, 1]), ('N01', [1, -5, 9, -5, 1]), ('N10', [1, -2, 0, 1, 1]), ('N11', [1, 1, 0, -2, 1])]
    for s in SIGMAS:
        fs.append((f'Q{s}', pcomp(Qexp(m1, m2, m3, *s), [-1, 1])))
    return fs


def gevalK(f, a, b):
    """2^{K d} f((a + b i)/2^K) as a Gaussian integer (Horner, as in the Lean checker)."""
    d = len(f) - 1
    re, im = 0, 0
    for k in range(d, -1, -1):
        # acc = acc * c + f_k, scaled: acc_K = acc_K * (a + b i) + f_k 2^{K (d - k)}
        re, im = re * a - im * b, re * b + im * a
        re += f[k] * (1 << (K * (d - k)))
    return re, im


def isqrt_floor(n):
    return isqrt(n)


def isqrt_ceil(n):
    s = isqrt(n)
    return s if s * s == n else s + 1


def main():
    out_lean, out_log = sys.argv[1:3]
    lines = []
    log = []
    for mu, theta_num, theta_den in [((1, 2, 7), 7641079385, 10 ** 10), ((1, 2, 8), 7990358445, 10 ** 10)]:
        m1, m2, m3 = mu
        M = m1 + m2 + m3
        name = '_'.join(map(str, mu))
        fac_entries = []
        worst = None
        for fname, f in factors(mu):
            d = len(f) - 1
            lc = f[-1]
            roots = mp.polyroots([mp.mpf(c) for c in reversed(f)], maxsteps=500, extraprec=400)
            cs = [(int(mp.nint(mp.re(z) * 2 ** K)), int(mp.nint(mp.im(z) * 2 ** K))) for z in roots]
            # radius exponent m: |f(c)|^2 < lc^2 r^{2d}, r = 2^-m  <=>  (re^2 + im^2) 2^{2 m d} < lc^2 2^{2 K d}
            m = 400
            for (a, b) in cs:
                re, im = gevalK(f, a, b)
                n2 = re * re + im * im
                while m > 0 and not (n2 * (1 << (2 * m * d)) < lc * lc * (1 << (2 * K * d))):
                    m -= 1
            m -= 2
            assert m > 40, (fname, m)
            # disjointness: |c_i - c_j|^2 2^{2m} > 4 2^{2K}
            for i in range(d):
                for j in range(i + 1, d):
                    da, db = cs[i][0] - cs[j][0], cs[i][1] - cs[j][1]
                    assert (da * da + db * db) * (1 << (2 * m)) > 4 * (1 << (2 * K))
            disks = []
            for (a, b) in cs:
                # l_k(c) 2^K = p_k 2^K + q_k (a + b i): l1 = m2 + m3 t, l2 = m2 - M + m3 t, l3 = m2 + (m3 - M) t
                ls = [(m2, m3), (m2 - M, m3), (m2, m3 - M)]
                n2s = [(p * (1 << K) + q * a) ** 2 + (q * b) ** 2 for p, q in ls]
                Lam = [isqrt_floor(n) for n in n2s]
                Ups = [isqrt_ceil(n) for n in n2s]
                sl = [abs(q) << (K - m) for p, q in ls]
                Lo = [Lam[k] - sl[k] for k in range(3)]
                Hi = [Ups[k] + sl[k] for k in range(3)]
                assert min(Lo) > 0
                # x1 >= (m1/m3) sqrt(Hi3/Lo1), x2 >= (m2/m3) sqrt(Hi3/Lo2), as X/2^K: X^2 m3^2 Lo1 >= m1^2 Hi3 2^{2K}
                X1 = isqrt_ceil(-(-(m1 * m1 * Hi[2] << (2 * K)) // (m3 * m3 * Lo[0]))) + 1
                X2 = isqrt_ceil(-(-(m2 * m2 * Hi[2] << (2 * K)) // (m3 * m3 * Lo[1]))) + 1
                assert X1 * X1 * m3 * m3 * Lo[0] >= m1 * m1 * Hi[2] << (2 * K)
                assert X2 * X2 * m3 * m3 * Lo[1] >= m2 * m2 * Hi[2] << (2 * K)
                # rho >= 1/(1 + x1 + x2) >= theta  <=>  theta (2^K + X1 + X2) <= 2^K
                assert theta_num * ((1 << K) + X1 + X2) <= theta_den * (1 << K), (fname, mu)
                # lower bounds Y: y1 <= (m1/m3) sqrt(Lo3/Hi1): Y^2 m3^2 Hi1 <= m1^2 Lo3 2^{2K}
                Y1 = isqrt_floor((m1 * m1 * Lo[2] << (2 * K)) // (m3 * m3 * Hi[0]))
                Y2 = isqrt_floor((m2 * m2 * Lo[2] << (2 * K)) // (m3 * m3 * Hi[1]))
                rho_lo = Fr(1 << K, (1 << K) + X1 + X2)
                if worst is None or rho_lo < worst[0]:
                    worst = (rho_lo, fname, len(disks), Y1, Y2, (a, b))
                disks.append((a, b, Lam, Ups, X1, X2))
            fac_entries.append((fname, f, m, disks))
            log.append(f'mu={mu} {fname}: d={d}, lc={lc}, radius 2^-{m}')
        rho_lo, fname, di, Y1, Y2, (a, b) = worst
        rho_hi = Fr(1 << K, (1 << K) + Y1 + Y2)
        log.append(f'mu={mu}: min over the disks of the lower bound of rho: {float(rho_lo):.12f} at {fname} disk {di}, '
                   f't ~ {a / 2 ** K:.6f} + {b / 2 ** K:.6f} i; upper bound of rho on that disk {float(rho_hi):.12f}')
        # Lean data
        lines.append(f'/-- The root disks of the factors of `S_μ` at `μ = {mu}`. -/')
        lines.append(f'def disks_{name} : List FacDisks := [')
        ents = []
        for _fn, f, m, disks in fac_entries:
            ds = ', '.join(f'⟨{a}, {b}, {Lam[0]}, {Lam[1]}, {Lam[2]}, {Ups[0]}, {Ups[1]}, {Ups[2]}, {X1}, {X2}⟩'
                           for (a, b, Lam, Ups, X1, X2) in disks)
            ents.append(f'  ⟨{m}, [{ds}]⟩')
        lines.append(',\n'.join(ents))
        lines.append(']')
        if mu == (1, 2, 7):
            lines.append(f'/-- The disk of the smallest `ρ` at `μ = (1,2,7)` ({fname}, disk {di}) and lower bounds of '
                         f'the ratios there. -/')
            lines.append(f'def minFac_{name} : Nat := {[e[0] for e in fac_entries].index(fname)}')
            lines.append(f'def minDisk_{name} : Nat := {di}')
            lines.append(f'def minY_{name} : Int × Int := ({Y1}, {Y2})')
    hdr = ('import Lean6.Special.Comp.D98.Roots\n\n/-!\n# Root disks of `S_μ` at `(1,2,7)` and `(1,2,8)`\n\n'
           'Generated by `gen/d98/gen_roots.py` (mpmath proposes the roots; Lean checks everything). Centres are\n'
           '`(a + b i)/2^256`, radii `2^-m`.\n-/\n\nnamespace Lean6.Special.Comp.D98\n\n')
    open(out_lean, 'w').write(hdr + '\n'.join(lines) + '\n\nend Lean6.Special.Comp.D98\n')
    open(out_log, 'w').write('\n'.join(log) + '\n')
    print('\n'.join(log))


main()
