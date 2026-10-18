#!/usr/bin/env python3
"""Certificate for Theorem 1 of DERIVATION.md (diagram 98 is absent at generic masses): P_98(m0) != 0.

Rigorous ball arithmetic (python-flint / Arb). For the masses muA of the z-circled triangle and muB of the w-circled
triangle (rationals), it
  1. builds the integer shape polynomials of shape_polys.py (Lemma B) for muA and muB;
  2. encloses all their complex roots tau with Arb's certified root isolation (fmpz_poly.complex_roots: each ball
     contains exactly one root, multiplicities reported); checks that the root count equals the degree;
  3. for every root tau: l_j = M z_j(tau) (z_1 = (mu_2 + mu_3 tau)/M, z_2 = z_1 - 1, z_3 = z_1 - tau), checks
     0 not in l_j, and computes alpha_j = mu_j |l_j|^(-1/2);
  4. DOMINANT-TERM TEST: rho(tau) = alpha_3 / (alpha_1 + alpha_2 + alpha_3); if min rho_A * min rho_B > 1/2 then for
     every pair of roots and every sign matrix eps, |sum eps_jl c_jl| >= (2 rho_A rho_B - 1) sum |c_jl| > 0, where
     c_jl = mu_j mu'_l (l_j l'_l)^(-1/2) are, up to one common nonzero factor, the terms of the torque form;
  5. DIRECT TEST (redundant): for every pair of distinct roots and all 256 sign matrices with eps_11 = +1, the ball
     of sum eps_jl a_j b_l (a_j = mu_j l_j^(-1/2), b_l = mu'_l l'_l^(-1/2), any fixed square-root branches)
     does not contain 0;
  6. writes a JSON certificate with all enclosures and bounds.
Usage: d98_certify_arb.py muA1 muA2 muA3 muB1 muB2 muB3 OUT.json [PREC_BITS]
"""
import sys, os, json, itertools, time
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flint
from flint import arb, acb, fmpz_poly
import shape_polys as SP


def arb_str(x):
    return x.str(30, radius=True)


def acb_str(z):
    return {'re': arb_str(z.real), 'im': arb_str(z.imag)}


def q(x):
    return arb(x.numerator) / arb(x.denominator)


def triangle(mu):
    """Roots of all shape polynomials with their alpha bounds. Returns (records, distinct root list)."""
    mu = [Fraction(v) for v in mu]
    M = sum(mu)
    polys = SP.all_shape_polys(mu)
    recs = []
    for name, co in polys:
        P = fmpz_poly(co)
        roots = P.complex_roots()
        nroot = sum(m for _, m in roots)
        assert nroot == P.degree(), (name, nroot, P.degree())
        for r, mult in roots:
            tau = acb(r)
            l1 = q(mu[1]) + q(mu[2]) * tau
            l = [l1, l1 - q(M), l1 - q(M) * tau]
            for lj in l:
                assert not lj.contains(0), ('l_j may vanish', name, r)
            al = [q(mu[j]) / abs(l[j]).sqrt() for j in range(3)]
            rho = al[2] / (al[0] + al[1] + al[2])
            recs.append({'poly': name, 'mult': mult, 'tau': tau, 'l': l, 'alpha': al, 'rho': rho})
    return polys, recs


def sqrt_acb(z):
    # a square root avoiding the branch cut of acb.sqrt (the sign is irrelevant: all sign patterns are tested)
    if z.real < 0:
        return acb(0, 1) * (-z).sqrt()
    return z.sqrt()


def main():
    args = sys.argv[1:]
    muA = [Fraction(v) for v in args[0:3]]
    muB = [Fraction(v) for v in args[3:6]]
    out = args[6]
    flint.ctx.prec = int(args[7]) if len(args) > 7 else 256
    t0 = time.time()
    polysA, RA = triangle(muA)
    polysB, RB = triangle(muB)
    # distinct shapes (balls of different polynomials can describe the same root, e.g. tau = e^{i pi/3})
    def distinct(R):
        D = []
        for r in R:
            if not any(r['tau'].overlaps(d['tau']) for d in D):
                D.append(r)
        return D
    DA, DB = distinct(RA), distinct(RB)
    # dominant-term test over all roots (all of them, not only the distinct ones)
    rhoA = min((r['rho'] for r in RA), key=lambda x: x.lower())
    rhoB = min((r['rho'] for r in RB), key=lambda x: x.lower())
    rA_low = min(r['rho'].lower() for r in RA)
    rB_low = min(r['rho'].lower() for r in RB)
    margin = 2 * rA_low * rB_low - 1
    dominant_ok = bool(margin > 0)
    # direct test: every pair of distinct roots, every sign matrix
    signs = [e for e in itertools.product([1, -1], repeat=9) if e[0] == 1]
    a_list = [[q(muA[j]) / sqrt_acb(r['l'][j]) for j in range(3)] for r in DA]
    b_list = [[q(muB[l]) / sqrt_acb(r['l'][l]) for l in range(3)] for r in DB]
    direct_ok = True
    worst = None
    npairs = 0
    for a in a_list:
        for b in b_list:
            c = [a[j] * b[l] for j in range(3) for l in range(3)]
            den = sum((abs(x) for x in c), arb(0))
            npairs += 1
            for e in signs:
                s = acb(0)
                for k in range(9):
                    s = s + c[k] if e[k] > 0 else s - c[k]
                if s.contains(0):
                    direct_ok = False
                rel = abs(s) / den
                if worst is None or rel.lower() < worst.lower():
                    worst = rel
    cert = {
        'theorem': 'diagram 98 (z-circled triangle A, w-circled triangle B): P(muA, muB) != 0',
        'muA': [str(v) for v in muA], 'muB': [str(v) for v in muB],
        'precision_bits': flint.ctx.prec, 'flint_version': flint.__version__,
        'shape_polynomials_A': [{'name': n, 'coeffs_low_first': c} for n, c in polysA],
        'shape_polynomials_B': [{'name': n, 'coeffs_low_first': c} for n, c in polysB],
        'roots_A': [{'poly': r['poly'], 'mult': r['mult'], 'tau': acb_str(r['tau']),
                     'abs_l_lower': [arb_str(abs(x).lower()) for x in r['l']],
                     'alpha': [arb_str(x) for x in r['alpha']], 'rho': arb_str(r['rho'])} for r in RA],
        'roots_B': [{'poly': r['poly'], 'mult': r['mult'], 'tau': acb_str(r['tau']),
                     'abs_l_lower': [arb_str(abs(x).lower()) for x in r['l']],
                     'alpha': [arb_str(x) for x in r['alpha']], 'rho': arb_str(r['rho'])} for r in RB],
        'n_roots_with_multiplicity': [len(RA), len(RB)],
        'n_distinct_shapes': [len(DA), len(DB)],
        'min_rho_A_lower': arb_str(rA_low), 'min_rho_B_lower': arb_str(rB_low),
        'dominant_margin_lower': arb_str(margin),
        'dominant_term_test': dominant_ok,
        'direct_test': {'pairs': npairs, 'sign_matrices_per_pair': len(signs), 'all_exclude_zero': direct_ok,
                        'min_relative_size_lower': arb_str(worst.lower())},
        'seconds': round(time.time() - t0, 1),
    }
    with open(out, 'w') as f:
        json.dump(cert, f, indent=1)
    print('muA', [str(v) for v in muA], 'muB', [str(v) for v in muB])
    print('roots (with mult) A %d B %d, distinct shapes A %d B %d' % (len(RA), len(RB), len(DA), len(DB)))
    print('min rho_A >= %s, min rho_B >= %s, margin 2 rhoA rhoB - 1 >= %s : dominant test %s' % (
        rA_low.str(8), rB_low.str(8), margin.str(8), 'PASS' if dominant_ok else 'FAIL'))
    print('direct test: %d pairs x %d sign matrices, all exclude 0: %s; min |sum|/sum|c| >= %s' % (
        npairs, len(signs), 'PASS' if direct_ok else 'FAIL', worst.lower().str(8)))
    print('time %.1f s' % (time.time() - t0))
    sys.exit(0 if (dominant_ok and direct_ok) else 1)


if __name__ == '__main__':
    main()
