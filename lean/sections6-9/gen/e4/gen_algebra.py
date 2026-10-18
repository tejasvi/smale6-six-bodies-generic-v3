"""Generate Lean6/Special/K4/E4/AlgebraIds.lean: the identities of cases (I)-(III) of the proof of Lemma 7.7.

Each lemma: hypotheses h_i (polynomial equations over C, w = j with w^2 + w + 1 = 0) and a polynomial goal; the
cofactors q_i with goal = sum q_i h_i are found by exact linear algebra (SymPy) and checked by `linear_combination`.
Run: python3 -I gen_algebra.py OUT.lean
"""
import itertools
import sys
import sympy as sp


def monos(vs, d):
    out = []
    for deg in range(d + 1):
        for c in itertools.combinations_with_replacement(vs, deg):
            out.append(sp.Mul(*c))
    return out


def cofactors(goal, hyps, vs, d):
    """find q_i (total degree <= d) with goal = sum q_i * hyp_i; hyps given as expressions (lhs - rhs)."""
    ms = monos(vs, d)
    unk = []
    qs = []
    for i, h in enumerate(hyps):
        cs = sp.symbols(f'c{i}_0:{len(ms)}')
        unk += cs
        qs.append(sum(c * m for c, m in zip(cs, ms)))
    expr = sp.expand(sum(q * h for q, h in zip(qs, hyps)) - goal)
    eqs = sp.Poly(expr, *vs).coeffs()
    sol = sp.linsolve(eqs, unk)
    if not sol:
        return None
    sol = list(sol)[0]
    zero = {x: 0 for x in unk}
    sub = {u: sp.sympify(v).subs(zero) for u, v in zip(unk, sol)}
    res = [sp.expand(q.subs(sub)) for q in qs]
    assert sp.expand(sum(q * h for q, h in zip(res, hyps)) - goal) == 0
    return res


def lean(e):
    return str(sp.expand(e)).replace('**', '^')


def leanS(e):
    """a statement term, as written (not expanded)"""
    return str(e).replace('**', '^')


w, r1, r2, a, b, z, p0, p1, p2, p3, p4, s0, s1, s2, s3 = sp.symbols('w r1 r2 a b z p0 p1 p2 p3 p4 s0 s1 s2 s3')
HW = w**2 + w + 1
L2, L3 = -2 - 2*w, 2*w

# (name, doc, vars (lean binder string), hyps [(lean name, lhs, rhs)], goals [(lhs, rhs)], degree)
SPECS = [
    ('caseI_three_one', 'Case (I), three `p_k` equal to `r₁` and one to `r₂`: `r₁² − r₁ + 1 = 0` and '
     '`Σ p³ = 3r₁³ + r₂³ = −6 r₁`, a root of `x² + 6x + 36` (that is `−3 ∓ 3√3 i`).',
     '(r1 r2 : ℂ)', [('hsum', r1 + r2, -1), ('hprod', r1*r2, -(3*r1 + r2))],
     [(r1**2 - r1 + 1, 0), (3*r1**3 + r2**3, -6*r1), ((3*r1**3 + r2**3)**2 + 6*(3*r1**3 + r2**3) + 36, 0)], 3),
    ('caseI_two_two', 'Case (I), two `p_k` equal to `r₁` and two to `r₂`: `S = −2`, `r₁ r₂ = 2`, `Σ p³ = 10`.',
     '(r1 r2 : ℂ)', [('hsum', r1 + r2, -1), ('hprod', r1*r2, -(2*r1 + 2*r2))],
     [(2*r1 + 2*r2, -2), (r1*r2, 2), (2*(r1**3 + r2**3), 10)], 3),
    ('caseII_diff', 'Case (II): subtracting the equations of `E p = p ∘ p` gives `(p₂ − p₃)(p₂ + p₃ + 1) = 0` and '
     '`(p₁ − p₄)(p₁ + p₄ + j) = 0` (Lean indices `0, …, 3`).',
     '(w p0 p1 p2 p3 : ℂ)', [('e1', p1 + p2 + w*p3, p0**2), ('e2', p0 + p2 + p3, p1**2),
                             ('e3', p0 + p1 + p3, p2**2), ('e4', w*p0 + p1 + p2, p3**2)],
     [((p1 - p2)*(p1 + p2 + 1), 0), ((p0 - p3)*(p0 + p3 + w), 0)], 0),
    ('caseII_equal_eq', 'Case (II), `p₂ = p₃ = a = −ζ b`, `p₁ = p₄ = b`: with `2 − ζ = ζ² b` and `b = j − 2ζ` '
     '(the equations divided by `b ≠ 0`), `ζ² − 4ζ + j = 0`.',
     '(w z b : ℂ)', [('hz3', z**3, 1), ('k1', 2 - z, z**2*b), ('k2', b, w - 2*z)],
     [(z**2 - 4*z + w, 0)], 2),
    ('cube_roots_factor', 'The cube roots of unity: `(ζ − 1)(ζ − j)(ζ − j²) = ζ³ − 1`.',
     '(w z : ℂ)', [('hw', w**2 + w + 1, 0)], [((z - 1)*(z - w)*(z - w**2), z**3 - 1)], 3),
    ('caseII_b', 'Case (II), `p₂ = p₃ = a`, `p₁ + p₄ = −j`: `a² − a + j = 0`, `p₁ p₄ = j² − 2a` and '
     '`Σ p³ = 2a(1 − 4j) + 2 − 2j`.',
     '(w a p1 p4 : ℂ)', [('hw', w**2 + w + 1, 0), ('h1', a + a + w*p4, p1**2), ('h2', p1 + a + p4, a**2),
                         ('h4', w*p1 + a + a, p4**2), ('hs', p1 + p4, -w)],
     [(a**2 - a + w, 0), (p1*p4, w**2 - 2*a), (2*a**3 + p1**3 + p4**3, 2*a*(1 - 4*w) + 2 - 2*w)], 2),
    ('caseII_b_value', 'Case (II), at `a (1 − 4j) = j − 1`: `(1 − 4j)² (a² − a + j) = 21 − 3j`.',
     '(w a : ℂ)', [('hw', w**2 + w + 1, 0), ('ha', a*(1 - 4*w), w - 1)],
     [((1 - 4*w)**2 * (a**2 - a + w), 21 - 3*w)], 3),
    ('caseII_c', 'Case (II), `p₂ + p₃ = −1`, `p₁ = p₄ = b`: `b² − j b + 1 = 0`, `p₂ p₃ = 1 − 2b` and '
     '`Σ p³ = 2b(j² − 4) + 2 − 2j`.',
     '(w b p2 p3 : ℂ)', [('hw', w**2 + w + 1, 0), ('e1', p2 + p3 + w*b, b**2), ('e2', b + p3 + b, p2**2),
                         ('e3', b + p2 + b, p3**2), ('hs', p2 + p3, -1)],
     [(b**2 - w*b + 1, 0), (p2*p3, 1 - 2*b), (2*b**3 + p2**3 + p3**3, 2*b*(w**2 - 4) + 2 - 2*w)], 2),
    ('caseII_c_value', 'Case (II), at `b (j² − 4) = j − 1`: `(j² − 4)² (b² − j b + 1) = 21 − 3j`.',
     '(w b : ℂ)', [('hw', w**2 + w + 1, 0), ('hb', b*(w**2 - 4), w - 1)],
     [((w**2 - 4)**2 * (b**2 - w*b + 1), 21 - 3*w)], 3),
    ('caseII_d', 'Case (II), `p₂ + p₃ = −1`, `p₁ + p₄ = −j`: `p₂ p₃ = −j²`, `p₁ p₄ = −j`, `Σ p³ = 4 + 6j`.',
     '(w p0 p1 p2 p3 : ℂ)', [('hw', w**2 + w + 1, 0), ('e1', p1 + p2 + w*p3, p0**2), ('e2', p0 + p2 + p3, p1**2),
                             ('e3', p0 + p1 + p3, p2**2), ('e4', w*p0 + p1 + p2, p3**2), ('hs1', p1 + p2, -1),
                             ('hs2', p0 + p3, -w)],
     [(p1*p2, -w**2), (p0*p3, -w), (p0**3 + p1**3 + p2**3 + p3**3, 4 + 6*w)], 2),
    ('caseIII_lambda', 'Case (III): `4 + 2λ₂ + 2λ₃ = 0` and `8λ₂ + 8λ₃ + 4λ₂λ₃ = 0` for `λ₂ = −2 − 2j`, `λ₃ = 2j`.',
     '(w : ℂ)', [('hw', w**2 + w + 1, 0)], [(4 + 2*L2 + 2*L3, 0), (8*L2 + 8*L3 + 4*L2*L3, 0)], 1),
]

E3 = [[0, 1, w**2, w], [1, 0, w, w**2], [w**2, w, 0, 1], [w, w**2, 1, 0]]
CHI = [[1, 1, 1, 1], [1, 1, -1, -1], [1, -1, 1, -1], [1, -1, -1, 1]]
LAM = [0, 2, L2, L3]
eig_goals = []
for i in range(4):
    for k in range(4):
        eig_goals.append((sum(E3[k][l]*CHI[i][l] for l in range(4)), LAM[i]*CHI[i][k]))
SPECS.append(('caseIII_eigen', 'Case (III): `E χ_i = λ_i χ_i` with eigenvalues `0, 2, λ₂, λ₃` (row by row).',
              '(w : ℂ)', [('hw', w**2 + w + 1, 0)], eig_goals, 1))
P = [sum(CHI[i][k]*[s0, s1, s2, s3][i] for i in range(4))/4 for k in range(4)]
Ep = [sum(E3[k][l]*P[l] for l in range(4)) for k in range(4)]
seqs = [s0**2 + s1**2 + s2**2 + s3**2, s1*(4 - s0) - s2*s3, s2*(2*L2 - s0) - s1*s3, s3*(2*L3 - s0) - s1*s2]
goals3 = []
for m in range(4):
    comb = sum(CHI[m][k]*(Ep[k] - P[k]**2) for k in range(4))
    # sum_k chi_m,k (E p - p∘p)_k = -(1/4) * (s-equation m), up to the identity hw
    goals3.append((comb, sp.Rational(-1, 4) * seqs[m] if m == 0 else sp.Rational(1, 2) * seqs[m]))
SPECS.append(('caseIII_system', 'Case (III): with `p = ¼ Σ s_i χ_i`, the combinations `Σ_k χ_{m,k} (E p − p ∘ p)_k` '
              'are `−¼`, `½`, `½`, `½` times the four equations `s₀² + s₁² + s₂² + s₃² = 0`, `s₁(4 − s₀) = s₂ s₃`, '
              '`s₂(2λ₂ − s₀) = s₁ s₃`, `s₃(2λ₃ − s₀) = s₁ s₂`.',
              '(w s0 s1 s2 s3 : ℂ)', [('hw', w**2 + w + 1, 0)], goals3, 3))
SPECS.append(('caseIII_cubes', 'Case (III): `Σ p³ = (s₀³ + 3 s₀ (s₁² + s₂² + s₃²) + 6 s₁ s₂ s₃)/16`.',
              '(s0 s1 s2 s3 : ℂ)', [], [(sum(x**3 for x in P),
               (s0**3 + 3*s0*(s1**2 + s2**2 + s3**2) + 6*s1*s2*s3)/16)], 0))

out = ['''import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Complex.Basic

/-!
# The identities of cases (I)–(III) in the proof of Lemma 7.7

Generated by `gen/e4/gen_algebra.py`: each lemma states hypotheses and conclusions of one step of the hand proof,
over `ℂ` with `w = j` (`w² + w + 1 = 0` where needed), and is proved by `linear_combination` with cofactors found by
exact linear algebra. Lean's bodies are `0, …, 3` (the paper's `1, …, 4`).
-/

namespace Lean6.Special.K4.E4.Alg
''']
for name, doc, binders, hyps, goals, d in SPECS:
    vs = sorted({x for e in [h[1] - h[2] for h in hyps] + [g[0] - g[1] for g in goals] for x in sp.sympify(e).free_symbols},
                key=lambda x: x.name)
    hyp_exprs = [sp.expand(h[1] - h[2]) for h in hyps]
    hb = ' '.join(f'({hn} : {leanS(l)} = {leanS(rr)})' for hn, l, rr in hyps)
    concl = ' ∧ '.join(f'{leanS(g[0])} = {leanS(g[1])}' for g in goals)
    proofs = []
    for g in goals:
        gexpr = sp.expand(g[0] - g[1])
        if not hyps:
            proofs.append('ring')
            continue
        q = None
        for dd in range(0, d + 3):
            q = cofactors(gexpr, hyp_exprs, vs, dd)
            if q is not None:
                break
        assert q is not None, (name, g)
        terms = [f'({lean(qi)}) * {hn}' for qi, (hn, _, _) in zip(q, hyps) if qi != 0]
        proofs.append('linear_combination ' + (' + '.join(terms) if terms else '0'))
    out.append(f'\n/-- {doc} -/\ntheorem {name} {binders} {hb} :\n    {concl} := by\n')
    if len(goals) == 1:
        out.append(f'  {proofs[0]}\n')
    else:
        out.append('  refine ⟨' + ', '.join(['?_'] * len(goals)) + '⟩\n')
        for pr in proofs:
            out.append(f'  · {pr}\n')
out.append('\nend Lean6.Special.K4.E4.Alg\n')
open(sys.argv[1], 'w').write(''.join(out))
print('written')
