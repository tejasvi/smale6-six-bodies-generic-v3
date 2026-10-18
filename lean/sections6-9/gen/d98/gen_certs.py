"""Certificates for the Lean checks of Lemma 6.9 (square-free parts) and Theorem 6.15 (P93(1,2,7) != 0).

Usage: python3 -I gen_certs.py ELIM_DIR OUT_LEAN OUT_LOG
  ELIM_DIR: the directory of the stored eliminants elim_1_2_7.txt, elim_1_2_8.txt, elim_2_3_11.txt (lines g=...).
  OUT_LEAN: the Lean data module to write (Lean6/Special/Comp/D98/Data.lean).
  OUT_LOG:  a text log of the sizes.

S_mu is built from the definitions of Sec. 6.4 (the expanded quintics Q_sigma composed with t - 1, checked against
the rational-function definition), in exactly the form of the Lean function `SUP`. All certificates are exact:
integer polynomials (coefficient lists, constant term first) with integer scalars. Nothing is trusted here: Lean
recomputes every product.
"""
import re, sys
import sympy as sp

t, x = sp.symbols('t x')
SIGMAS = [(1, 1, 1), (1, 1, -1), (1, -1, -1), (1, -1, 1)]


def Qexp(m1, m2, m3, a, b, c):
    # coefficients of x^0..x^5 (the Lean `QUP`)
    return [-(m2 + m3) * c, -(2 * m2 + 3 * m3) * c, m1 * (a - b) - (m2 + 3 * m3) * c,
            (3 * m1 + m2) * a + m3 * (b - c), (3 * m1 + 2 * m2) * a, (m1 + m2) * a]


def Qrat(m1, m2, m3, a, b, c):
    F1 = m2 * a + m3 * b / (1 + x) ** 2
    F2 = -m1 * a + m3 * c / x ** 2
    F3 = -m1 * b / (1 + x) ** 2 - m2 * c / x ** 2
    return sp.cancel(x ** 2 * (1 + x) ** 2 * (x * (F1 - F2) - (F2 - F3)))


def poly_from(coeffs, var):
    return sp.Poly(sum(sp.Integer(c) * var ** i for i, c in enumerate(coeffs)), var)


def S(mu):
    m1, m2, m3 = mu
    P = sp.Poly((t ** 2 - t + 1) * (t ** 4 - 5 * t ** 3 + 9 * t ** 2 - 5 * t + 1) * (t ** 4 + t ** 3 - 2 * t + 1)
                * (t ** 4 - 2 * t ** 3 + t + 1), t)
    for s in SIGMAS:
        q = poly_from(Qexp(m1, m2, m3, *s), x)
        assert sp.expand(q.as_expr() - Qrat(m1, m2, m3, *s)) == 0
        P = P * sp.Poly(q.as_expr().subs(x, t - 1), t)
    return P


def Phi3(mu):
    m1, m2, m3 = mu
    M = m1 + m2 + m3
    l1 = m2 + m3 * t
    l2 = l1 - M
    l3 = l1 - M * t
    Y = [m1 ** 2 * l2 * l3, m2 ** 2 * l1 * l3, m3 ** 2 * l1 * l2]
    return sp.Poly(sp.expand(Y[0] ** 2 + Y[1] ** 2 + Y[2] ** 2 - 2 * (Y[0] * Y[1] + Y[1] * Y[2] + Y[2] * Y[0])), t)


def coeffs(p):
    """integer coefficient list, constant term first"""
    p = sp.Poly(p, t)
    d = p.degree()
    return [int(p.coeff_monomial(t ** i)) for i in range(d + 1)]


def zscale(pq):
    """an integer multiple a*p of a rational polynomial p with integer coefficients: returns (a, coeffs)"""
    pq = sp.Poly(pq, t, domain='QQ')
    den = sp.ilcm(*[sp.fraction(c)[1] for c in pq.all_coeffs()]) if pq.all_coeffs() else 1
    return int(den), coeffs(sp.Poly(pq.as_expr() * den, t))


def divcert(num, den):
    """a * num = den * q with integer a > 0 and integer q (exact division over Q required)"""
    q, r = sp.div(sp.Poly(num, t, domain='QQ'), sp.Poly(den, t, domain='QQ'))
    assert r.is_zero
    a, qc = zscale(q)
    return a, qc


def bezout(f, g):
    """u f + v g = c with integer u, v and a nonzero integer c (gcd(f, g) = 1 over Q)"""
    u, v, h = sp.gcdex(sp.Poly(f, t, domain='QQ'), sp.Poly(g, t, domain='QQ'))
    assert h.degree() == 0 and not h.is_zero
    den = sp.ilcm(*[sp.fraction(cc)[1] for cc in list(u.all_coeffs()) + list(v.all_coeffs()) + list(h.all_coeffs())])
    uz = coeffs(sp.Poly(u.as_expr() * den, t))
    vz = coeffs(sp.Poly(v.as_expr() * den, t))
    c = int(h.as_expr() * den)
    # sanity
    assert sp.expand(sp.Poly(uz[::-1] if False else sum(sp.Integer(a) * t ** i for i, a in enumerate(uz)), t).as_expr() * f.as_expr()
                     + sum(sp.Integer(a) * t ** i for i, a in enumerate(vz)) * g.as_expr() - c) == 0
    return uz, vz, c


def lean_list(l):
    return '[' + ', '.join(str(v) for v in l) + ']'


def main():
    elim_dir, out_lean, out_log = sys.argv[1:4]
    log = []
    defs = []
    for mu in [(1, 2, 7), (1, 2, 8), (2, 3, 11)]:
        name = '_'.join(map(str, mu))
        txt = open(f'{elim_dir}/elim_{name}.txt').read()
        g = sp.Poly(sp.sympify(re.search(r'^g=(.*)$', txt, re.M).group(1)), t)
        s = S(mu)
        g0 = sp.Poly(sp.sqf_part(s.as_expr()), t)
        g0 = sp.Poly(sp.primitive(g0.as_expr())[1], t)
        if g0.LC() < 0:
            g0 = -g0
        assert sp.Poly(sp.sqf_part(g.as_expr()), t).monic() == g0.monic()
        # multiplicities
        kg = max(m for _, m in sp.factor_list(g.as_expr())[1])
        ks = max(m for _, m in sp.factor_list(s.as_expr())[1])
        a1, q1 = divcert(g, g0)
        a2, q2 = divcert(g0 ** kg, g)
        a3, q3 = divcert(s, g0)
        a4, q4 = divcert(g0 ** ks, s)
        dg0 = g0.diff(t)
        u, v, c = bezout(g0, dg0)
        assert coeffs(s) == coeffs(s)
        log.append(f'mu={mu}: deg g {g.degree()}, deg S {s.degree()}, lead S {s.LC()}, deg g0 {g0.degree()}, '
                   f'k_g {kg}, k_S {ks}, Bezout constant digits {len(str(abs(c)))}, '
                   f'max cofactor digits {max(len(str(abs(z))) for z in u + v)}')
        defs.append(f'/-- The eliminant stored for `μ = {mu}` (the line `g=` of `elim_{name}.txt`). -/\n'
                    f'def g_{name} : UP := {lean_list(coeffs(g))}\n')
        defs.append(f'/-- The primitive square-free part of `S_μ` at `μ = {mu}`. -/\n'
                    f'def g0_{name} : UP := {lean_list(coeffs(g0))}\n')
        defs.append(f'/-- `a₁ g = g₀ q₁`, `a₂ g₀^{kg} = g q₂`, `a₃ S = g₀ q₃`, `a₄ g₀^{ks} = S q₄` at `μ = {mu}`. -/\n'
                    f'def cert_{name} : SqfCert where\n'
                    f'  kg := {kg}\n  ks := {ks}\n'
                    f'  a1 := {a1}\n  q1 := {lean_list(q1)}\n  a2 := {a2}\n  q2 := {lean_list(q2)}\n'
                    f'  a3 := {a3}\n  q3 := {lean_list(q3)}\n  a4 := {a4}\n  q4 := {lean_list(q4)}\n'
                    f'  u := {lean_list(u)}\n  v := {lean_list(v)}\n  c := {c}\n')
    # Theorem 6.15: P93(1,2,7) != 0
    mu = (1, 2, 7)
    s = S(mu)
    ph = Phi3(mu)
    U, V, c = bezout(s, ph)
    log.append(f'P93 at {mu}: deg S {s.degree()}, deg Phi3 {ph.degree()}, lead Phi3 {ph.LC()}, '
               f'Bezout constant digits {len(str(abs(c)))}, deg U {len(U) - 1}, deg V {len(V) - 1}, '
               f'max cofactor digits {max(len(str(abs(z))) for z in U + V)}')
    defs.append('/-- `U S + V Φ₃ = c` at `μ = (1, 2, 7)`. -/\n'
                f'def bez93_U : UP := {lean_list(U)}\n'
                f'def bez93_V : UP := {lean_list(V)}\n'
                f'def bez93_c : Int := {c}\n')
    hdr = ('import Lean6.Special.Comp.D98.UPoly\n\n'
           '/-!\n# Certificates of Lemma 6.9 (square-free parts) and Theorem 6.15 (`P93(1,2,7) ≠ 0`)\n\n'
           'Generated by `gen/d98/gen_certs.py` from the eliminants `elim_1_2_7.txt`, `elim_1_2_8.txt`,\n'
           '`elim_2_3_11.txt` of the diagram-98 computations (their sha256 in `data/d98/SHA256SUMS`). Coefficient\n'
           'lists start with the constant term.\n-/\n\n'
           'namespace Lean6.Special.Comp.D98\n\nopen UP\n\n')
    open(out_lean, 'w').write(hdr + '\n'.join(defs) + '\nend Lean6.Special.Comp.D98\n')
    open(out_log, 'w').write('\n'.join(log) + '\n')
    print('\n'.join(log))


main()
