# Lean checks of the computations of Sections 6–9

Paper: "Smale's sixth problem for six bodies in the plane: finiteness of central configurations for generic masses"
(numbering of the paper's current version: Section 9 the hand explanations of the cells, Section 10 the verification
with Tables 2–5, §10.1 the checks in Lean). This file lists, for every computation of Sections 6–8 and every
computation inside a hand proof there, the Lean theorem that checks it, what the theorem says, what it assumes, how to
run it, its cost and its axioms; then the computations inside the hand proofs of Sections 2–9; then Proposition 9.23 (which cells the lemmas
of Section 9 cover); then the claims that are not checked in Lean, with the reason. Every computation on which the proof of Theorem 1.1 rests in Sections 6 and 7
is checked; the items left out are listed with the paper's own text showing that the proof does not use them.

## Trust base and conventions

* Lean `v4.35.0-rc3`, Mathlib `c55e6e7` (the revisions of `lean-toolchain`, `lake-manifest.json`).
* No `sorry`, no `admit`, no axiom declared in the sources. Every theorem below depends only on `propext`,
  `Classical.choice`, `Quot.sound` and, where a computation runs, on the axioms that `native_decide` creates. In this
  toolchain each use of `native_decide` adds one axiom `<decl>._native.native_decide.ax_1_1 : decide (P) = true`,
  where `P` is the stated Boolean equation `checker data = true`, after evaluating it with compiled code; the axiom
  trusts the compiler and the run, nothing else (example: `logs/integration/native_axiom_example.log`). All axioms are
  printed by `gen/axioms_all.lean` (344 theorems, `logs/integration/axioms_all.log`).
* Every check has two parts: a computable checker on `Nat`, `Int`, `Rat`, lists and strings (modules under
  `Lean6/Special/Comp/`, no Mathlib, compiled to shared libraries by `precompileModules`, so that `native_decide` runs
  native code), and a soundness theorem proved in Lean with Mathlib that turns `checker data = true` into a statement
  about `ℂ`, `ZMod p`, `MvPolynomial` or `Polynomial`. Floating point only proposes (centres, pivots, cofactors,
  linear-programming certificates); every trusted test is exact.
* The systems and forms are written in Lean from the definitions of the paper (the statement files cited below), and
  are compared with the inputs of the original computations where those exist.
* The ball arithmetic and the Krawczyk test (`Lean6/Special/Comp/Ball/`, `Lean6/Special/Ball/`) are taken from the
  Lean development of the five-body paper, with the namespaces renamed and two additions: uniqueness of the zero in
  the box (`kraw_unique`) and the derivative of the system at the zero (`Ball/Deriv.lean`, `hasFDerivAt_tpoly`).

## How to run

```
lake build                              # everything; with Mathlib's build present
lake env lean gen/axioms_all.lean       # the axioms of the 344 final theorems
```

On a machine with many cores run `ulimit -n 65536` first (with the default limit of 1024 open files, parallel builds
fail). Measured on a 384-core machine from a fresh `git archive` of the commit (`logs/integration/fresh_archive.log`):
10 min 19 s wall, 18,495 CPU-seconds, largest process 15.1 GB (the S12 run of Lemma 6.19(b): 10 min on 64 threads). The longest single modules are
`Lean6.Special.Comp.D88.Count.RunS12` (about 10 min, 64 threads) and `Lean6.Special.Comp.D88.Trop.HypRun` (415 s, one core). Each component can be built alone, e.g.
`lake build Lean6.Special.K4.E4`; the aggregators are listed in `Lean6/Special.lean`.

## Section 6

### Hand proofs of §§6.1–6.3, 6.7 (`Lean6/Special/Hand/`)

| claim | theorem | what is proved |
|---|---|---|
| Lemma 6.2 (`lem:rewrite`) | `Hand.rewrite_identity` | the identity Σ_{j∈S} m_j m_o p_jo³(z_j w_o − z_o w_j) = m_o(z_o A_w − w_o A_z) = m_o(w_o B_z − z_o B_w), with Z_kl = p_kl³(z_k − z_l), W_kl likewise |
| Lemma 6.3 (`lem:binary`) | `Hand.binary_masses`, `binary_ne_zero` | from m_5ẑ_5 + m_6ẑ_6 = 0, p̂_j²ẑ_jŵ = −1 and m_5p̂_5 = −m_6p̂_6: m_5³ + m_6³ = 0; hence the sum is nonzero for positive masses |
| Prop. 6.8 (`prop:d81`) | `Hand.prop68_ratio`, `prop68_equal`, `prop68_branch` | the algebra of the last step: (u_1/u_2)² = −m_2³/m_1³ with \|u_1\| = \|u_2\| forces m_1 = m_2, and then m_5^{3/2} = m_6^{3/2} |
| Lemma 6.17 (`lem:Ttest`) | `Hand.ttest_pair`, `ttest_dominant`, `ttest_reduction` | \|m_5p̂_5 + m_6p̂_6\|² = (m_5³ + m_6³)/(m_5m_6\|c\|\|X\|); (a): a dominant group cannot be cancelled; (b): the reduction of the sum (forward direction, the one used) |
| §6.7, systems | `Hand.torque_identity`, `com_identity` | Σ_k μ_k(Y_k Xeq_k − X_k Yeq_k) = 0 identically (four bodies), and the centre-of-mass identity |
| §6.7, S11 vs S12 | `Hand.N4.yeq2_of_S11` | every zero of `N4.S11` (the system of the boxes of Lemma 6.19(c)) satisfies the Y-equation of body 3, so it is a zero of S12 |
| §6.7, KC12 vs KC | `Hand.KC.yeq2_of_KC12` | every zero of `KC.KC12` satisfies the Y-equation of body 3 |

Standard axioms only. Build: `lake build Lean6.Special.Hand` (seconds).

### Lemma 6.9 (`lem:three`) (`Lean6/Special/D98/Shapes.lean`, `Lemma69.lean`, `Lemma69Check.lean`)

| claim | theorem | what is proved |
|---|---|---|
| Lagrange case: the quadratics t² − (1 + j^b − j^c)t + j^b | `D98.lq_00`, `lq_12`, `lq_21`, `lq_01_02`, `lq_10_20`, `lq_11_22`, `lagrange_shape` | over any commutative ring with ω² + ω + 1 = 0: class (0,0) gives t² − t + 1; (1,2) and (2,1) give (t − (1+ω))² and (t + ω)², whose roots are roots of t² − t + 1; the conjugate pairs {(0,1),(0,2)}, {(1,0),(2,0)}, {(1,1),(2,2)} give N01, N10, N11; over a domain every root of a class is a root of (t² − t + 1)N01N10N11 |
| collinear case | `D98.Q_eq_F` | the quintic Q_σ equals x²(1+x)²(x(F_1 − F_2) − (F_2 − F_3)) with F_k built from σ and z as in the paper |
| S_μ: degree 34, leading coefficient (μ_1+μ_2)⁴ | `D98.S_generic`, `Spol_natDegree_leadingCoeff`, `toPoly_SUP` | in ℤ[μ_1, μ_2, μ_3][t] (and over any domain with μ_1 + μ_2 ≠ 0); `toPoly_SUP`: the computable S_μ is the product of the factors of the definition |
| check (†): eliminants at (1,2,7), (1,2,8), (2,3,11) | `D98.lemma69_check_1_2_7`, `_1_2_8`, `_2_3_11` | for the stored eliminant g: a square-free g₀ of degree 32 (Bezout certificate) with g₀ ∣ g ∣ g₀³ and g₀ ∣ S_μ ∣ g₀² in ℚ[t]; hence g and S_μ have the same complex roots; S_μ has degree 34, 34 roots with multiplicity, 32 distinct |

Inputs: `d98/certificates/lemB/elim_{1_2_7,1_2_8,2_3_11}.txt` (sha256 in `data/d98/SHA256SUMS`). Generator:
`gen/d98/gen_certs.py` (square-free parts and Bezout cofactors, by python-flint; only proposals). Assumes nothing.
Native checks under 0.25 s each.

### Lemma 6.13 (`lem:dominant`) at (1,2,40), and its check at (1,2,7) (`D98/Heavy.lean`, `Check127*.lean`)

| claim | theorem | what is proved |
|---|---|---|
| the Lagrange factors near 0 and 1 | `D98.lagrange_bounds`, `tails` | for \|h\| ≤ 1/10: \|p(c+h) − 1\| ≤ 0.5951 for p ∈ {t² − t + 1, N01, N10, N11}, c ∈ {0, 1}; the exact tail sums 0.11, 0.5951, 0.2011, 0.1021 |
| the collinear factors | `D98.Q_heavy`, `collinear_tails`, `Q_ne_zero_near` | at μ = (1,2,40): Q_σ = 40C_σ + D_σ; \|C_σ(c)\| = 1, \|C_σ − C_σ(c)\| ≤ 0.332, \|D_σ\| ≤ 2.446 on \|x − c\| ≤ 1/10; so Q_σ has no root there |
| the first statement | `D98.heavy_roots`, `rho_bound` | every root t ∈ ℂ of S_μ has \|t\| > 1/10, \|t − 1\| > 1/10 and ρ(t) > 9/10 (with A_1 < 0.03A_3, A_2 < 0.05A_3) |
| "consequently" | `D98.heavy_signed_sums` | for roots t, t′ and any c_jl ∈ ℂ with c_jl² = μ_j²μ_l²Λ_j(t)Λ_l(t′), every signed sum Σ ε_jl c_jl (ε_jl = ±1) is nonzero, so no factor of Φ vanishes and Ψ(t, t′) ≠ 0 |
| check at (1,2,7) (†) | `D98.check_1_2_7`, `check_1_2_7_min`, `check_1_2_8`, `check_rho_product` | at every root of S_{(1,2,7)}: ℓ_1ℓ_2ℓ_3 ≠ 0 and ρ ≥ 0.7641079385 > 1/√2; some root of N11 has ρ ≤ 0.7641079386; at (1,2,8): ρ ≥ 0.7990358445; ρρ′ > 1/2 |

The analytic part (Taylor tails, triangle inequalities, the dominant term) is proved in Lean without `native_decide`.
The check at (1,2,7): mpmath proposes the root centres; Lean checks \|f(c)\| < \|lc\|·r^d at each centre, which puts
a root in each disk (factorization over ℂ), and the disks are disjoint, so a count against the degree shows they hold
all roots (`roots_in_disks`); exact bounds of \|ℓ_k\| on the disks then bound ρ. Assumes nothing. Generators:
`gen/d98/gen_roots.py`, `gen_hand.py`. The root disks are regenerated from the definition of S_μ (mpmath centres
rounded to multiples of 2⁻²⁵⁶, factor by factor), not read from the Arb root balls of the original run
(`d98_cert_127_12{7,8}.json`); the Lean statement does not depend on where the centres come from.

### Theorem 6.15 (`thm:d93`) (`D98/P93.lean`)

| claim | theorem | what is proved |
|---|---|---|
| P93(1,2,7) ≠ 0 | `D98.no_common_root_1_2_7`, `P93_eval_1_2_7_ne_zero` | S_{(1,2,7)} and Φ_3(t; (1,2,7)) have no common complex root (Bezout identity U·S + V·Φ_3 = c, c a nonzero integer of 191 digits); with P93 defined as Mathlib's `Polynomial.resultant` of S_μ and Φ_3 over `MvPolynomial (Fin 3) ℤ`, its value at (1,2,7) is nonzero |

### Lemma 6.19(a) (`Lean6/Special/D88/Trop/`)

The hypotheses of Lemma 6.18 for the ideals of S12 and KC12 at μ₀ = (1,2,3,30), p = 65521, with G of 30 and 101
polynomials in the 17 coordinates ξ (differences X_kl, Y_kl and the p_kl).

| claim | theorem | what is proved |
|---|---|---|
| (i) G lies in the ideal | `D88.Trop.n4_G_mem`, `kc_G_mem` | for each g ∈ G, explicit cofactors with g(ξ(v), μ) = Σ_j c_j F_j at every point of every commutative ring with μ_4·i = 1 (resp. μ_3·i = 1), F_j the equations of S12 (resp. KC12) written from §6.7 and the masses variables; so g lies in the ideal over ℤ[μ, 1/μ_4] (resp. 1/μ_3), hence over 𝒪 |
| (ii) unit coefficients | `D88.Trop.n4_units`, `kc_units`, `n4_size`, `kc_size` | every coefficient of every g (a polynomial in μ) is nonzero at μ₀ modulo p: 354 and 1133 coefficients; the ξ-monomials of each g are distinct; G has 30 and 101 polynomials |
| (iii)–(iv) prevariety and cone tests | `D88.Trop.n4_torus_all`, `kc_torus_all` | for every w ∈ ℚ¹⁷ with a negative entry and every field K of characteristic 65521, the initial forms at w of the polynomials of G specialized at μ₀ have no common zero in (K*)¹⁷ |
| comparison with the d88 run | `D88.Trop.n4_gfan`, `kc_gfan` | the gfan inputs of the d88 run are the reductions of G up to unit scalars, term by term |
| (iii)–(iv) over any ordered group | `D88.Trop.n4_torus_gamma`, `kc_torus_gamma`, `cover_soundG` (`D88/Trop/CoverG.lean`, `Gamma.lean`) | the same statement for weights w : ℕ → Γ in any linearly ordered abelian group Γ (`[AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]`), with `initialFormG w g` the terms of least weight Σ e_i • w_i; the certificates are integer combinations, so the same runs serve; `initialFormG_rat`, `torusEmptyG_rat` and `n4_torus_all_of_gamma` relate it to the ℚ version. This is the form a proof of Lemma 6.18 through a valuation ring with an arbitrary value group needs |

The statement of (iii)–(iv) is what the proof of Lemma 6.18 uses (w = ν(ξ) has a negative entry, lies in the
prevariety and the reduced initial forms vanish at the residues); it covers gfan's fan and its completeness at once.
The checker verifies a covering of w-space by polyhedral cells (every split exhaustive, every face certified by exact
Farkas or Motzkin multipliers), each leaf either a cell on which some initial form is a monomial, the cell {0}, or a
cone test: a certificate Σ c_i·in_w(g_i) + c_R(1 − y∏ξ) = 1 over F_p (Singular `lift`), the initial forms recomputed
in Lean from G and an exact interior point. Sizes: S12 3,734 splits, 12,327 faces, 5,519 monomial leaves, 1,948 cone
certificates; KC12 1,512, 5,363, 2,783, 240. One cell of each covering, the ray (X: 0, Y or U: 2, p: −1) along which
the Y-positions escape, had no feasible cofactor certificate; there the Buchberger engine of Section 7 (below) finds
the unit ideal in Lean (`D88.Trop.n4_hypsOK`, `kc_hypsOK`, module `Comp.D88.Trop.HypRun`, 415 s). The cell counts
differ from gfan's 2149/224 cones (the covering splits more finely), so those two numbers are not reproduced; the
mathematical content they serve is. Inputs: `data/d88trop/SHA256SUMS`; generated tree and data:
`data/d88trop/GENERATED.sha256`; regeneration `gen/d88trop/run.sh` (the linear-programming proposals come from
HiGHS, so a rerun may give another tree; any tree that passes proves the same theorem). Negative controls:
`logs/d88trop/negctl.log`. Assumes nothing (Lemma 6.18 itself is stated in the paper, not formalized).

### Lemma 6.19(b) (`Lean6/Special/D88/Count/`)

| claim | theorem | what is proved |
|---|---|---|
| (b) for KC′ | `D88.Count.count_KC` | `Module.Finite (ZMod 65521) AqKC ∧ finrank (ZMod 65521) AqKC ≤ 4788`, with `AqKC = (ZMod 65521)[v′] ⧸ ⟨KC′(μ₀)⟩` and KC′ written from §6.7 (`KCprimeEqs`: the four X-equations with X₁ = 1, X₄ = 0, the Y-equations of bodies 2, 3 after eliminating Y₄ through body 1, the six distances, in v′ = (X₂, X₃, U₁, U₂, U₃, p₁₂, …, p₃₄)) |
| (b) for S12 | `D88.Count.count_S12` | the same with `AqS12 = (ZMod 65521)[v] ⧸ ⟨S12(μ₀)⟩` and bound 20,316 (`S12eqs`: slice X₁ − X₂ = 1, X₄, Y₄ by the centre of mass, the X- and Y-equations of bodies 1, 2, 3, the six distances) |
| the engine | `D88.Count.f4_good` | for the F4 engine `Comp.Count.f4Basis` (symbolic preprocessing, sparse rows reduced modulo p with dense accumulators, parallel row reduction): every output polynomial vanishes at every common zero of the input in every commutative `ZMod p`-algebra (only monomial multiples and linear combinations create basis elements); standard axioms only |
| the check | `Comp.Count.dimCheck`, `D88.Count.dimCheck_sound`, `finrank_le_of_border`, `degRevLex`, `grevGtStd_iff`, `lead_toMv`, `mem_span_of_good` | each output polynomial is sorted strictly decreasing in the degree reverse lexicographic order (as msolve: first variable largest) with coefficients in [1, p); the staircase S of the leading monomials (computed by a search, not trusted) contains 0, is closed under the border and has at most N elements; with the order built as a Mathlib `MonomialOrder` (`degRevLex`) and Mathlib's division algorithm `MonomialOrder.div_set`, the monomials of S span the quotient |
| the runs | `Comp.Count.kc_f4_ok`, `s12_f4_ok` | `dimCheck 65521 11 (f4Basis kcCfg kcInputs) 4788 = true` (33 s, 1.8 GB) and `dimCheck 65521 11 (f4Basis s12Cfg s12Inputs) 20316 = true` (10 min wall on 64 threads, 15 GB), `native_decide` |
| the inputs | `D88.Count.eval_s12InputsZ`, `eval_kcInputsZ`, `span_s12Inputs_le`, `span_kcInputs_le` | the engine inputs (the msolve input files of the original run, sha256 in `data/d88count/SHA256SUMS_br`) are the rows of §6.7 up to unit factors (900 on three rows of S12, −1 on the centre row of KC′), so their ideal is contained in the paper's |

Cross-checks (not part of the proof): the minimal leading monomials of the engine's bases equal the leading ideals
that msolve 0.9.4 printed in the original run (2,074 for KC′, 7,411 for S12; compared with a development driver of the
engine that is not included in the release, `logs/d88count/f4_runs.log`); and `dimCheck` also passes on msolve's
reduced bases at exactly 4788 and 20,316 and fails one below (`gen/d88count/br_testdim.lean`,
`logs/d88count/br_native_test.log`; these bases were computed with msolve 0.7.5, the version installed on the build
machine, not with the paper's 0.9.4); so do the sizes of KC′'s reduced basis in `logs/d88count/kc_gb_size.log` and
the measurements in `PLAN.md`. The monomial order matters only for speed; the dimension does not depend on it. With (a)
and Lemma 6.18 this gives the paper's conclusion that the boxes of (c), (d) contain all zeros at μ₀; Lemma 6.18 and
Nakayama's lemma remain stated, not formalized.

### Lemma 6.19(c), (d) and the last paragraph of §6.7 (`Lean6/Special/D88/Boxes/`)

| claim | theorem | what is proved |
|---|---|---|
| (c) | `D88.Boxes.lemma_6_19_c` | 20,316 pairwise disjoint closed polydiscs in ℂ¹¹ of radius < 6·10⁻⁴⁷; each contains exactly one zero z of `N4.S11`, `N4.S11` has derivative `toLin' J` at z with `IsUnit J.det`, and at every point of the polydisc X_3 − X_4 ≠ 0, X_l ≠ 0 for l = 1, …, 4, and the T-test of Lemma 6.17(a) holds for some k with margin 0.1756 (`TTest4`, with t_l = \|X_l\|^{-1/2} and the masses (1,2,3,30)) |
| (d) | `D88.Boxes.lemma_6_19_d` | 4788 pairwise disjoint closed polydiscs in ℂ¹² of radius < 5·10⁻⁵⁴; each contains exactly one zero of `KC.KC12`, with invertible Jacobian; at every point X_l ≠ 0 for l = 1, 2, 3 and, for every choice of square roots w_l² = X_l and all ε, s ∈ {±1}³, \|Σ ε_lβ_l(1 + i s_lρ)\| ≥ 1.47·10⁻⁶(1+ρ²)^{1/2}Σ\|β_l\| with β_l = m_l/w_l, ρ = 2√2 = (m_6/m_5)^{3/2} at (m_5, m_6) = (1,2) |
| §6.7, last paragraph (†) | `D88.Boxes.sec_6_7_counts` | at the 4788 zeros of (d): the T-test over the bodies 1, 2, 3 fails at exactly 1092 and passes at exactly 3696; the smallest of the 32 sums has relative margin below 10⁻⁴ at exactly 36 zeros (for every branch choice), and at those ‖Y_4‖ > 5000 and ‖Y_l‖ < 3·10⁻⁵‖Y_4‖ for l ≤ 3 |

The systems `N4.S11`, `KC.KC12` are written from §6.7 (`D88/Boxes/Systems.lean`); `N4.eval_s11T`, `KC.eval_kc12T`
prove that the term lists checked by Krawczyk are these equations up to nonzero row factors (900 on the distance rows
14, 24, 34 of S11; −1 on the equation of the centre of KC12), and the S11 rows are those of the msolve input of S12.
With `Hand.N4.yeq2_of_S11` the zeros of (c) are zeros of S12. Inputs: the certificate files of diagrams 88 and 94
(centres and radii copied verbatim; sha256 in `data/d88boxes/SHA256SUMS`), radii rounded up to multiples of 2⁻²⁵⁶;
393 generated modules of 64 boxes (`gen/d88boxes/gen.py`, byte-identical regeneration, `manifest.sha256`). The
checks are exact (moduli and inverse square roots by squared inequalities, a complex square-root covering, reciprocal
discs, an O(n²) separation test). Negative controls (`logs/d88boxes/negctl.log`): perturbed centres and radius
10⁻⁹⁰ fail. Cost: about 2 s per module of 64 boxes, disjointness of the 20,316 boxes 71 s, the counts 16 s; clean
build of the component 1 min 36 s wall, 14.4 CPU-minutes.

## Section 7

### Lemma 7.7 (`lem:E4cert`), the check after Proposition 7.8, Remark 7.14 (`Lean6/Special/K4/E4/`)

| claim | theorem | what is proved |
|---|---|---|
| Lemma 7.7, the statement | `K4.E4.lemma_7_7` | for every ω ∈ ℂ with ω² + ω + 1 = 0, at μ = (1,1,1,1): for every symmetric pattern e (ε_kl = ω^{e_kl}) the seven cubic forms F_ε have no common zero in ℂ⁴ other than 0, and for every antisymmetric sign pattern σ the four quartic forms G_σ (ξ_1 = 0) have no common zero in ℂ³ other than 0 |
| the check after Prop. 7.8 (†) | `K4.E4.check_3_5_7_11` | the same at μ₀ = (3,5,7,11), so μ₀ ∉ B_E |
| hand proof, F_ε: patterns and types | `Comp.E4.free`, `orbit_size`, `inv_invariant`, `inv_separates`, `nine_values`, `relabel_triple`, `conj_triple`, `reduction` | the substitutions act freely on the 729 patterns with 9 orbits of 81; the triple separates the orbits; relabelling permutes and conjugation negates it; every pattern reduces to the types (0,0,0), (0,0,1), (0,1,2) |
| hand proof, cases (I)–(III) | `K4.E4.Alg.*` (`AlgebraIds.lean`, `Algebra.lean`), `Alg.caseIII` | every identity of the text over ℂ with ω = j: Σp³ ∈ {108, −3 ∓ 3√3 i, 10}, the case-II factorizations, ζ² − 4ζ + j ≠ 0 for ζ ∈ {1, j, j²}, (21 − 3j)/(1 − 4j)², (21 − 3j)/(j² − 4)², 4 + 6j, the eigen-data, 4 + 2λ_2 + 2λ_3 = 0, 8λ_2 + 8λ_3 + 4λ_2λ_3 = 0; `caseIII`: the s-equations and Σp³ = 0 force s = 0 |
| hand proof, G_σ: tournaments | `Comp.E4.score_counts`, `score_determines`, `reduce_tournaments`, `rep_scores` | score sequences (3,2,1,0): 24, (3,1,1,1): 8, (2,2,2,0): 8, (2,2,1,1): 24; equal scores ⇒ isomorphic; the three representatives |
| hand proof, G_σ: resultants | `K4.E4.no_zero_T1`, `no_zero_T2`, `no_zero_T3`, `res12_T*`, `res13_T*`, `resR_T*`, `R1*_zero` | no common zero of e_1, e_2, e_3 in ℂ² (Bezout identities, R_1(0) = 1); Res_s(e_1,e_2) = R_1 and Res_s(e_1,e_3) = t⁴R_2′ as printed, with Mathlib's `Polynomial.resultant`; Res_t(R_1,R_2′) = 2^16 3^4 5^4 7^2·3881, 2^16 3^8 5^10, −2^16 5^4·23·433 (exact LU factorization over ℚ, `det_of_LU`, `resultant_of_LU`) |
| Remark 7.14 (†) | `K4.E4.remark_7_14_1112`, `_5_2_11_3`, `_1234`, `_2357` | at each of the four mass points, the construction applies to exactly 36, 16, 28, 28 of the 64 sign patterns; for those G_σ has a nonzero common zero (exact evaluation), and every nonzero common zero has two coinciding points (a certificate d·ξ_i in the span in degree 7, d ≠ 0), so none survives the saturation; for the other patterns there is no common zero |
| Prop. 7.8, the determinants (export) | `K4.E4.macF`, `macFpoly`, `macF_row`, `macFpoly_map_eval`, `macF_det_ne_zero_3_5_7_11`, `macF_det_ne_zero_1111`, `macFpoly_det_ne_zero`, `F_eq_zero_of_macF_det`, and the same for `macG` (`K4/E4/Export.lean`) | the Macaulay matrices as functions of the masses (entries linear in μ, also as matrices over `MvPolynomial (Fin 4) ℂ`), each row the coefficient vector of x^α·F_{ε,i} (resp. ξ^α·G_{σ,k}); at μ₀ = (3,5,7,11) and at (1,1,1,1) the square submatrix on the rows the checker selects has nonzero determinant, so its determinant is a nonzero polynomial in μ, and wherever it is nonzero the forms have no common zero (the generic transfer of Prop. 7.8). One extra run (`Comp/K4/E4/ExportRun.lean`, 44 s) checks the matrices against the forms entry by entry |

Method for the first two rows: Lean builds the Macaulay matrices from the definitions (degree 7: 245 × 120 for F_ε,
degree 8: 60 × 45 for G_σ, entries in ℤ[j]); an untrusted elimination proposes a square block and its inverse modulo
p = 2147483629 with j ↦ 882503254; the trusted test is block × inverse ≡ 1. `macCheck_sound` (standard axioms only)
carries this to ℂ: through ℤ√−3 to `ZMod p` and to ℂ (`Zsqrtd.lift_injective`), a nonzero determinant, and the pure
powers x_k^D in the span. p need not be prime for this; r² + r + 1 ≡ 0 and s² ≡ −3 modulo p are checked by `decide`.
No certificate file is read (`data/e4/SHA256SUMS` lists the files consulted for parameters and printed values).
Runs: 85 s natively; clean build of the component 1 min 35 s wall. Negative controls
(`Comp/K4/E4/NegCtl.lean`, outside the library): three Remark 7.14 patterns at (1,1,1,2), F_ε without its cubic form,
and a wrong inverse are rejected.

### Lemma 7.9 (`lem:C4cert`) and §7.4 (`Lean6/Special/K4/C4/`)

| claim | theorem | what is proved |
|---|---|---|
| Lemma 7.9 (†) | `K4.C4.lemma_7_9` | at μ₀ = (3,5,7,11), for p = 32003 and p = 1073741789, on each of the 14 charts the equations of Z(μ₀) (§7.3: (I), (II), (III) with ξ = (μ_3s, μ_3t, −(μ_1s + μ_2t), 0), `eqsZ`) have no common zero in any nontrivial commutative `ZMod p`-algebra with the two chart coordinates equal to 1 (`NoZero`), and 1 lies in the ideal they generate in `MvPolynomial ℕ (ZMod p)` (`UnitIdeal`) |
| §7.4 (†) | `K4.C4.sec_7_4` | the same at μ = (1,1,1,1), for both primes (the paper claims 32003) |
| support | `K4.C4.unitTest_sound`, `chart_no_zero`, `chart_span`, `eval_eqs`, `prime_of_trialPrime` | soundness of the engine (p prime); the integer polynomials are the equations `eqsZ`; primality by checked trial division |

The checker is a Buchberger engine written in Lean (`Comp/K4/C4/GB.lean`, sugar strategy, Gebauer–Möller): every
polynomial it adds to its basis is a combination of the input, so reaching a nonzero constant is the proof
(`unitTest_sound`). These checks use no cofactor certificate. (With a limit of about 22 minutes, Singular `liftstd` (8.9 GB) and
Macaulay2 with a change matrix (12.9 GB) did not finish on one chart, of sugar degree 33. Without that limit `liftstd`
finishes on all 14 charts at μ₀ over F_32003, in 12–170 min and at most 34 GB, with 0.62–2.33 M cofactor terms; these
are the certificates for the kernel versions below.) The equations built in Lean agree
with the builders of the original run and its msolve inputs on all 28 chart systems (`logs/c4/compare_d64.log`;
sha256 of the 22 files compared in `data/c4/SHA256SUMS`). Cost: 28–125 s per chart, clean build 134 s wall, 4,235
CPU-seconds, largest process 3.5 GB. Lemma 7.10 (transfer from F_p to ℚ) and Proposition 7.11 are hand proofs, not
formalized.

## Computations inside the hand proofs of Sections 2–9 (`Lean6/Special/Hand/`)

The items of `PLAN.md` ("Computations inside hand proofs"). Each is a lemma over a commutative ring, a field, ℚ, ℝ or
ℂ, with the relations the paper's proof uses as hypotheses and its conclusion as stated; none uses `native_decide`
(standard axioms only). Where a step of the paper is linear algebra or tree bookkeeping rather than an identity, only
its algebraic consequence is proved, and the docstring says so.

| item | place | theorems (namespace `Lean6.Special.Hand`; Section 9 in `Hand.Sec9`) | what is proved |
|---|---|---|---|
| H2.1 | §2.3 | `body_eq_of_rows`, `subset_sum`, `mass_sum_zero`, `torque_zero`, `partial_virial`, `partial_virial_half`, `difference`, `U_eq_sum`, `sep_sum_algebra`, `sep_sum` | for any finite set of bodies over any commutative ring with symmetric p: the rows give the equations of the bodies; subset sums, T_J = 0, partial virials (doubled form in any characteristic, the printed form when 2 ≠ 0), differences, Σ m_k z_k = 0, U = Σ m_k z_k w_k, Σ_{k<l} m_k m_l z_kl w_kl = M·U |
| H2.2 | Lemma 2.3(a) | `lemma_2_3_a` | U = Σ m_k z_k w_k, and U = I when M ≠ 0 |
| H2.3 | Lemmas 2.2, 2.9(b) | `rows_swap_D`, `rows_swap_Z`, `rows_rotate`, `iota_slice`, `iota_invol`, `iota_rows`, `z_iota`, `w_iota` | the rows are invariant under (u, v) ↦ (v, u) and equivariant under the rotation; ι maps the slice to itself, is an involution, preserves X_m; z_k∘ι = w_k/v₁, w_k∘ι = v₁z_k |
| H2.4 | Lemmas 2.8, 2.11 | `O1_bounds`, `O3_zstroke`, `edgeF_strictAnti`, `omega_eq_edgeF`, `zstroke_kind`, `wstroke_kind`, `zwedge_kind`, `E2_arith`, `E3_arith`, `E6_arith`, `C2_arith`, `C4_arith` | the arithmetic steps over ℚ: f strictly decreasing, ω = f(ζ) on edges, the inequalities of (E2), (E3), (E6), (C2), (C4) from (O1)–(O6) |
| H2.5 | Cor. 2.4 | `fibre_bound` | 2⁴·2¹⁵ = 2¹⁹ |
| H3.1 | §3 | `triangle_one_circle` | a triangle of strokes of one colour with exactly one circled vertex is impossible |
| H4.1 | Lemma 4.3(b) | `root_coefficient`, `root_two_children_ne_zero` | the coefficient of exponent h_r in Σ m_k z_k = 0 is Σ_c (X_c − X_{c_O}) M_c; with two children it is nonzero at positive masses |
| H6.1 | Lemma 6.1 | `F1_exp`, `F1_coeff`, `F2_exp`, `F4_exp`, `F4_coeff` | the exponents and coefficients of (F1), (F2), (F4): p̂²ẑ_jŵ_l = −1, the leading coefficient −m_j m_l p̂ |
| H6.2 | Props 6.4, 6.7, 6.8, Thm 6.5 | `d90_F4`, `d90_a4`, `d90_exponents`, `d89_sum_zero`, `d89_F4`, `d89_torque_exponents`, `d82_exponents`, `d81_exponents` | the exponent comparisons |
| H6.3 | Lemmas 6.2, 6.3, Prop. 6.8, Lemma 6.17, §6.7 | (v1) `rewrite_identity`, `binary_masses`, `prop68_*`, `ttest_*`, `torque_identity`, `com_identity`, `N4.yeq2_of_S11`, `KC.yeq2_of_KC12` | as in the Section 6 table above |
| H6.4 | Lemma 6.9, Thm 6.12 | `shape_positions`, `shape_positions_unique`, `lagrange_p3`, `lagrange_quadratic`, `lagrange_quadratic_j`, `collinear_p`, `collinear_force`, `collinear_shape`, `cross_square`, `torque_lead_coeff` | z_k = ℓ_k(τ)/M; L + I = uμᵀ gives p³ = 1/M; the quadratic of the Lagrange case; p z_kl = ±κ and x(F₁ − F₂) = F₂ − F₃ in the collinear case; c_jl² = κ m_j²m_l²Λ_j(τ)Λ_l(τ′); the leading torque coefficient |
| H6.5 | Remark 6.14 | `split_signed_sum` | ε_jl = δ_jη_l splits the signed sum into a product |
| H6.6 | Thm 6.15 | `d93_signs`, `Phi3_product`, `Phi3_zero_of_signed`, `d93_Phi3_zero` | Σ m_l p̂_4l = 0 gives Σ ε_l m_l ŵ_l^{−1/2} = 0; Φ₃ is the product of the four signed sums, so it vanishes |
| H7.1 | Lemmas 7.1–7.5 | `sum_mass_Phi`, `const_force`, `d64_exponents`, `d64_F4`, `d64_Zjk` | Σ m_k Φ^η_k = 0; the constant force gives c′Σ m_k = 0; the exponents |
| H7.2 | Lemma 7.6 | `cube_root_cases`, `E4_noncollinear`, `E4_collinear` | from the two conclusions of the linear-algebra case split (P_kl³ = u_k u_l with ξ not constant; η = λξ + θ), some pattern ε (resp. σ) has a nonzero common zero of F_ε (resp. G_σ), in terms of `K4.E4.FZero`, `GZero` |
| H7.3 | §7.3 | `II_of_iii`, `III_of_eta`, `xiZ_param`, `bideg_I`, `bideg_II`, `bideg_III` | on `K4.C4.eqsZ`: (II) is (iii) times ∏(ξ_k − ξ_l), (III) is the cycle relation of η times a_kl a_ln a_nk; the parametrization of ξ; the bidegrees (1,3), (2,1), (2,4) |
| H9.1 | Lemma 9.1 | `Sec9.ssum`, `ssum_zero` | the mass-weighted sum of the initial forms is Σ δ_k m_k ĉ_k |
| H9.2 | Lemmas 9.2–9.4 | `handT_le_of_below`, `handT_le_of_not_below`, `handP_pos`, `forced_x2`, `forced_x4`, `handC_ne_zero` | the exponent inequalities with their strict cases; (Σ m_k)X ≠ 0 |
| H9.3 | Lemmas 9.5, 9.6 | `handB0`, `handK_c`, `handK_c'`, `handK` | the initial forms cannot all vanish |
| H9.4 | Lemma 9.7 | `handL_relations`, `handL_impossible`, `handL` | P_sa³ = P_sb³ = P_ab³ = 1/M_T and the relation of the cube roots of unity (divided by ε_ab), impossible at positive masses by the modulus bounds |
| H9.5 | Lemma 9.8 | `cliquesum`, `sum_symm_antisymm` | the three identities, for any finite set and symmetric P |
| H9.6 | Thm 9.9 | `collinear_dist`, `collinear_force`, `clique3_i_ratios`, `one_is_sum`, `clique3_i`, `clique3_ii_relation`, `clique3_ii`, `clique3_iii` | (i) one of the m^{−1/2} is the sum of the other two; (ii) m_a³m_b³ = m_s²(m_a + m_b)(j^{2k}m_a + m_b)³ and k = 0 at positive masses; (iii) Φ^z = 0 (from the rank-one form of L, which stays hand) |
| H9.7 | after Thm 9.9 | `QT_identity`, `QT_zero_iff` | Q_T = m_a²m_b²m_s² ∏(n_a ± n_b ± n_s) with m n² = 1; at positive masses Q_T = 0 iff one n is the sum of the other two |
| H9.8 | Lemma 9.11 | `handR_lambda`, `handR_relations`, `N`, `N_eval_zero`, `N_special`, `N_ne_zero`, `handR_kappa` | the relations give a common root κ, so N = 0 (N as Mathlib's `Polynomial.resultant`); with M_A = m_a, M_B = m_b and m_s = 0, N = −m_a¹²m_b¹², so N ≠ 0; κ = 1 at positive masses |
| H9.9 | Lemma 9.12 | `handR6_relation`, `handR6_product`, `H6poly_ms_zero`, `H6poly_ne_zero`, `handR6_pos` | m_a m_b⁵ = m_s²(m_a + m_b)³(m_a + ω m_b); the product over ω equals (m_a m_b⁵)³ at m_s = 0; ω = 1 at positive masses |
| H9.10 | Lemma 9.13 | `handW3_core`, `handW3` | α + β + γ = 0 with α³u₁ = β³u₂ = γ³u₃ ≠ 0 gives H_W = 0 |
| H9.11 | Lemma 9.14 | `handEQ2`, `handEQ2_pos` | m_a²M_A⁴ = m_b²M_B⁴ (the case M_B = 0 included), m_a M_A² = m_b M_B² at positive values |
| H9.12 | Lemma 9.15 | `handQ_signs`, `handQ_prod_ne_zero`, `handQ_not_all_equal`, `handQ_two` | P_sk = ε_k P and Σ ε_k m_k = 0; the product over the signs is a nonzero polynomial; the signs are not all equal at positive masses; m_a = m_b for \|K\| = 2 |
| H9.13 | Lemmas 9.16, 9.17 | `clique_x_zero`, `clique_orders` | the exponent arithmetic |
| H9.14 | Lemma 9.20 | `handP4`, `handP4_pos` | m_a P_sa = −m_b P_sb, then m_a³ + m_b³ = 0, impossible at positive masses |
| H9.15 | Lemma 9.22 | `handTQ` | m_{l₁} = m_{l₂} and m_{k₁} = m_{k₂} |

Build: `lake build Lean6.Special.Hand` (the Section 7 module imports the E4 and C4 runs). The axioms of the 155
theorems are in `logs/hand/axioms_HA.log`, `logs/hand/HB_build_axioms.log` and in `gen/axioms_all.lean`.

## Section 9: Proposition 9.23 (`prop:handcover`) (`Cover/`)

Not part of the version-2 release, which is pinned at commit `ef35952`; these checks (commits `5766a93` to `009fcfd` and
later on the branch `update`) are for the next version.

A sub-package with its own `lakefile.toml`: it requires the companion project `lean6` by path (`../../lean6` from
`Cover/`, i.e. `lean6` checked out beside this repository; built against its commit `d593063`, branch `upd-exclusion`;
the modules used are unchanged since `lean6`'s release `6fb8b01`) and
reuses its reader of the stored cells and diagrams (`L6.F34.Cell.ofJson`, `L6.F34.Diagram.ofN6`), the embedded cell
files and `n6.json` (`L6F5.Data`, whose SHA-256 digests `lean6` checks: `L6F5.cells_sha256`, `L6F5.n6_sha256`), the
clique test of Corollary 9.18 (`L6F5.cliqueOK`), the core links of Proposition 5.3 (`L6Check.F34.Data`, `parseLink`)
and its certification of argmin sets on the cell polyhedron (`Ctx.cellRows`, `interiorPoint`, `guessArgmin`,
`constantArgmin`, `strictlyLeast`: a floating-point guess, then exact Farkas certificates, Lemma 4.6). The main package
does not depend on it.

| item | Lean (namespace `Lean6.Special.Cover`) | statement |
|---|---|---|
| (a) | `prop_9_23`: `aTotal`, `aEvery`, `aP4`, `aLinAll`, `aTD` | 70,406 cells are excluded at every positive mass: 70,233 satisfy the hypotheses of one of Lemmas 9.2–9.7, 171 have a core of template `P4` (Lemma 9.20) and one a core `LIN` with a minor of one sign (Lemma 9.21), among the cells where the notes' program classified the core and none of Lemmas 9.2–9.7 holds, and one (cell 0 of class 15) has a torque, `T_{0,3,4}`, with one term strictly least on the cell (Lemma 5.1); the four sets are disjoint |
| (b), first group | `prop_9_23` (`first`), `prop_9_23_first` | 90,943 cells satisfy the hypotheses of one of Lemmas 9.2–9.7, Corollary 9.10 (with its class-level case), Lemma 9.11 (a), (b), Lemmas 9.12–9.15 and Corollary 9.18 for a clique of three bodies; 90,919 without Corollary 9.18, which alone covers one cell of class 4, 22 of class 47 and one of class 53 (the diagrams 31, 48 and 95 by the supplement's table of classes) |
| (b), second group | `prop_9_23`: `second`, `secondRc`, `secondTq`, `secondP4`, `secondLin` | 287 of the other cells satisfy those of Lemma 9.11(c) (1 cell), Lemma 9.22 (1), Lemma 9.20 (169) or Lemma 9.21 (116), counted by the first lemma of this list that holds |
| (b), the rest | `prop_9_23`: `remaining` | the remaining 43 cells: 1 of class 31, 10 of class 124, 9 of class 127, 2 of class 132, 1 of class 133, 11 of class 143, 9 of class 147, the diagrams 89, 64, 88, 93, 98, 66, 94 (`L6F5.F5_cc`) |
| proof of 9.23: the 74 cells | `prop_9_23_first`: `w3Only`, `eq2Only`, `w3OnlyNonzero`, `eq2OnlyNonzero` | Lemma 9.13 is the only test of the first group that holds in 16 cells and Lemma 9.14 in 58; in each, at every instance, `g` and `H_W` (resp. `m_a²M_A⁴ − m_b²M_B⁴`) are nonzero at m = (1,…,6) |
| the tests one by one | `prop_9_23_first`: `perTest` | Lemma 9.2: 40,084 cells; 9.3: 13,293; 9.4: 46,289; 9.5: 7,722; 9.6: 532; 9.7: 2,111; the class-level case of Cor. 9.10: 50,399; Cor. 9.10: 86,875; 9.11(a): 77,927; 9.11(b): 79,318; 9.12: 54,208; 9.13: 2,241; 9.14: 2,654; 9.15: 2,105; Cor. 9.18 for three bodies: 86,842 (the census of Prop. 9.19, checked in `lean6`) |
| without the programs' order | `prop_9_23_broad` | of the 21,040 cells without Lemmas 9.2–9.7 (20,226 with a core), the templates give `P4` in 401, `LIN` with a minor of one sign in 2,742 and `LIN` otherwise in 2,105 (see the remark below) |

* **Assumes** that each test is the hypothesis of its lemma read off the trees, the argmin sets and the diagram (a
  literal transcription, `Comp/Every.lean`, `Generic.lean`, `Lines.lean`, `Secondary.lean`; the module docstrings give
  each reading); for Lemmas 9.20 and 9.21, that the templates of the programs (`Comp/Templates.lean`, transcribed from
  the supplement's `corefam.py` and `coreparse.py`) state their hypotheses on the initial forms of the core; and that
  the stored cells are the cells of Proposition 4.5 and the cores those of Proposition 5.3 (both checked in `lean6`).
* **Readings.** A meet of two points that share a leaf does not exist, and a comparison involving it is false. Lemma
  9.4 takes every set of at least two bodies (both programs stop at five; the results are the same in every cell). In
  Lemma 9.11(b) the bodies below the other children of `v` meet `O` at `v`, so "a disjoint union of sets as in Lemma
  9.1" is a set closed under minimal forces (the program's classes give the same witnesses). In Lemmas 9.13 and 9.14
  "the relations of Lemma 9.1 at `v`" (and in Lemma 9.22(ii) "a set as in Lemma 9.1") are read as both programs read
  them (`Lines.sSets`): the candidates are the bodies `k` with `meet_c(k, O) = v` whose position is minimal (their
  equations then have the least exponent `h_v`); for each candidate `k` not in an earlier set, `K(k)` is the set of
  candidates reached from `k` along minimal forces (`l` is reached from `j` when the force of `l` on `j` is minimal);
  `K(k)` is used if it is closed (every minimal force on a body of `K(k)` is the force of a body of `K(k)`), and it
  gives the relation `Σ_{k∈K(k)} m_k X^c_{v,u(k)} = 0`. Under a broader reading (`Lines.sSetsBroad`: all closed
  components of the graph of minimal forces on all bodies in which every minimal force is mutual, that contain a body
  with a minimal position and whose bodies with a minimal position meet `O` at `v`) Lemma 9.13 would hold in 1,791
  cells instead of 2,241 and Lemma 9.14 in 2,750 instead of 2,654; it is computed only to compare. The linear algebra over ℚ(m) is exact, over ℤ[m₁,…,m₆]
  (`Comp/MPoly.lean`): ranks are the sizes of the largest nonzero minors, `e` and `M_A`, `M_B` come from Cramer's rule
  on a maximal nonzero minor, and `g` is that minor times a nonzero entry. In Lemma 9.14 the relation exists exactly
  when the projection onto `(ĉ_a, ĉ_b)` has dimension at most 1; it is 1 in every instance. Lemma 9.11(c) is tried with
  every `J ⊇ {a, b}` (the certificates of the supplement use `J = T`; the same cells). The cores are `lean6`'s link
  lines, the engine's cores except 66 cells that `lean6` replaced, all inside the first group. A `LIN` template has a
  matrix of full column rank over ℚ(m), so some maximal minor is a nonzero polynomial.
* **Where the programs applied the templates.** The template matching mirrors the procedure of the supplement's
  programs: the identities are those of the cell's core, and the templates `B`, `LIN`, `P4` are tried in this order on
  their certified initial forms. The notes' program classified the core of a cell only if none of its cell-level tests
  held (`Templates.notesLemma`; among them three tests that the paper does not state); (a) counts the cells so
  classified, and the theorem reproduces that order. A broader search (over other identities than those of the core,
  or ignoring that order) could only cover more cells.
* **Agreement.** The tests of Lemmas 9.2–9.15 and of the class-level case agree cell by cell with the independent
  program of the supplement (`final_classification.jsonl`), and those of Lemmas 9.2–9.7 also with the notes' program
  (`tiers_v2.jsonl`); the notes read Lemma 9.13 more strictly (650 cells). The templates agree with the notes' program
  on its 781 classified cores (the LIN minors up to sign, the body `s` of P4), and Lemmas 9.11(c), 9.22 hold exactly in
  the supplement's cells (3 and 1 of them when Corollary 9.18 is left out). The clique test is `lean6`'s; the cells that
  Corollary 9.18 adds are the 24 of the paper. No core identity of a counted cell fails certification.
* **Remark: (a) is a lower bound.** `prop_9_23_broad` shows that Lemmas 9.20 and 9.21 (a minor of one sign does not
  vanish at positive masses) apply, on certified cores, to many more of the cells without Lemmas 9.2–9.7 than the 172
  of (a); the notes' program did not classify those cores because a cell-level lemma of generic masses already held.
  So "70,406 are excluded at every positive mass" (and "71,235" after the proposition) counts the cells so reached, not
  all cells that these lemmas exclude at every positive mass.
* **Cost.** `prop_9_23_first` and `prop_9_23` are one `native_decide` each, about 50 and 60 s on one core;
  `prop_9_23_broad` about 115 s. A fresh `cd Cover && lake build` takes 178 s wall (230 CPU-seconds, largest process
  1.2 GB) once `lean6`'s libraries are built (`logs/cover/`).

## Kernel-only versions

The libraries `L6KSpec` (computational code over `Nat` and `List`, no Mathlib, with the loaders of the data),
`L6SoundKSpec` (soundness lemmas) and the check modules `L6CheckKSpec`, `L6CheckC4`, `L6CheckTrop` prove the
statements below again without `native_decide`: the kernel reduces every check, so each of these theorems depends only
on `propext`, `Classical.choice` and `Quot.sound` (`logs/kern/axioms.txt`). They were written in a companion project
and are merged here with their layout unchanged; their statements are checked to be those of this package
by `example`s (`L6CheckKSpec/Final.lean`, `E4Final.lean`, `TropSame.lean`, and the generated `Final` modules). Every
check module is compiled by `lean` directly, one process per module, under a memory budget (`scripts/kern/build.sh`);
generated modules and data are compared with committed SHA-256 lists before they are compiled.

| claim | kernel theorem | module | how | build |
|---|---|---|---|---|
| Lemma 6.19(c), (d) and the counts of §6.7 | `D88.BoxesK.lemma_6_19_c`, `lemma_6_19_d`, `sec_6_7_counts` | `L6CheckKSpec/Final.lean` | the boxes as literals (`data/ksp`, 8 per literal, parsed exactly as `parseBox` does and sorted by the real part of the first centre), this package's post-parse test of each box, the sweep `sweepOK` (`sweepOK_pairwise`: `Pairwise sepBoxes`), the counts per module of 64 boxes, and the Box-level soundness lemmas `n4_box_soundB`, `kc_box_soundB` | 472 modules, 8.6 CPU-hours, largest process 15.7 GB (`N4/All`) |
| Lemma 6.9 and the check at (1,2,7) after Lemma 6.13 | the ten theorems of `Comp.D98K` | `L6CheckKSpec/D98.lean` | the checkers of `Comp.D98` by `decide +kernel`, unchanged | 5 s, 0.8 GB |
| Lemma 7.7 and the check after Proposition 7.8 | `K4.E4K.lemma_7_7`, `check_3_5_7_11` | `L6CheckKSpec/E4Final.lean` | `macCheckK` (`macCheck` arranged for the kernel: rows not normalized, the product checked on packed rows; the selection and the inverse computed at elaboration, untrusted), 1,586 patterns in 200 modules; `macCheckK_sound` | 202 modules, 8.9 CPU-hours, largest process 9.4 GB |
| Lemma 7.9 at μ₀ = (3,5,7,11) over F_32003 | `L6CheckC4.lemma_7_9_32003`, the first half of `K4.C4.lemma_7_9` | `L6CheckC4/Final.lean` (generated) | the cofactor certificates below, checked bucket by bucket modulo p with a cover of the products (`cofmod_sound_ivl`); `Bridge`: the equations of the paper are the packed ones at every point of a chart | 643 modules, 16.6 CPU-hours, 42 min, largest process 33.1 GB (an interval module) |
| Lemma 6.19(a)(i) | `D88.TropK.n4_G_mem`, `kc_G_mem` | `L6CheckKSpec/TropMem.lean` | the systems and the relation written with the kernel normal form `normalizeK` (`eval_normalizeK`), `checkMemK` on the literal cofactors (`mem_soundK`) | with `TropUnits` and `TropSame`: 97 s, largest process 15.4 GB |
| Lemma 6.19(a)(ii) | `Comp.D88.TropK.n4_units_ok`, `kc_units_ok` | `L6CheckKSpec/TropUnits.lean` | `checkUnits` on the literals `GN4`, `GKC` | (with the above) |
| Lemma 6.19(a)(iii)–(iv) | `D88.TropK.kc_torus_gamma`, `n4_torus_gamma` | `L6CheckTrop/KC/Final.lean`, `L6CheckTrop/N4/Final.lean` (generated) | this package's coverings with each leaf replaced by an assumed system, so that `chk` and `cover_soundG` apply unchanged; each system empty on the torus by a certificate checked by the kernel: for KC 241 systems (232 leaf identities by `normalizeK`, 8 large leaves and the escape-ray system `hypsKC` by bucket checks), for N4 1,949 (1,946 leaf identities, 2 large leaves by bucket checks, and the escape-ray system `hypsN4` from the trace of a Buchberger run, checked as a chain of 2,044 identities each over the inputs and the earlier elements: `L6KSpec.TropChain`, `sysEmpty_of_chain`, 104.8 M term products); `HypsOK` assembled by `hypsOK_cons` | 401 modules (89 of KC, 312 of N4 with the 294 of the chain): 5.4 CPU-hours, 23 min, largest process 40.7 GB (the covering check of N4) |

Lemma 6.19(b) and the second half of Lemma 7.9 (p = 1,073,741,789) stay native: no certificate of them is within
reach (below).

**Build.** `bash scripts/kern/build.sh libs boxes d98 e4 c4gen c4 tropgen trop tropmem axioms` (stages in this order;
`BUDGET_GB`, `MAXJOBS`, `JOBS` in the environment). The box and E4 modules are committed; the stages check first that
`ksp_gen.py`, `kc_classes.lean`, `kspc_gen.py` and `ke4_gen.py` write exactly these files. `c4gen` and `tropgen` read
the certificates and the trace of `hypsN4` from `data/kern/cert/` (distributed separately, compared with
`data/kern/SHA256SUMS`), write the chart equations with
`gen/c4/dump_eqs.lean`, and generate `L6CheckC4`, `data/c4k` (`kc4_gen.py`) and `L6CheckTrop`, `data/tropk`
(`ktrop_gen.py`), compared with `data/c4k/SHA256SUMS` and `data/tropk/SHA256SUMS`; each generation was run twice and
gave the same files, and the files of C4, KC and N4 are those that the companion project compiled (its lists of 671,
108 and 903 files; `logs/kern/compare.log`). The memory estimate of every module is set in the driver per kind of module, from
the largest peaks measured. On one machine with 384 cores and 708 GB, after the libraries: about 40 CPU-hours and
84 minutes (boxes 7 min, E4 9 min, C4 42 min, Trop 23 min, the rest under 4 min), at most 464 GB in use at once (in
the interval modules of C4); logs in `logs/kern/`.

**Cofactor certificates for kernel versions** (`gen/kern/`, `data/kern/`; the files are distributed separately, their
SHA-256 digests in `data/kern/SHA256SUMS`; for the build they go, compressed with `xz`, in `data/kern/cert/`). For each of the 14 charts of Lemma 7.9 at μ₀ = (3,5,7,11) over F_32003 (the
case the main theorem uses) and for the escape-ray system `hypsKC` of Lemma 6.19(a) over F_65521: polynomials `c_k`
with `Σ_k c_k f_k = 1`, the `f_k` the equations as the checks build them (`C4.chartEqs [3, 5, 7, 11] ch`, `hypsKC`).
Computed by Singular `liftstd` (`gen/kern/mk_lift.py`), checked independently with python-flint against the equations
dumped from Lean (`gen/kern/verify_cof.py`, `verify_esc.py`). Sizes: 0.62–2.33 M terms per chart, 17,721,624 in all;
2,167,298 for `hypsKC` (`data/kern/summary.txt`). The system `hypsN4` has none (`liftstd` did not finish in 6 h, 56 GB);
for it the kernel checks the trace of a run of the Buchberger engine of Section 7 instead (`trace_hypN4.txt`, 81 MB,
2,605 elements, written by `Comp.K4.C4.TraceGB` of the branch `update`; distributed separately like the certificates,
its digest in `data/kern/SHA256SUMS`): the 2,044 ancestors of the constant `1`, each an identity over the inputs and
the earlier ancestors.
Lemma 6.19(b) has no certificate of this kind within reach: the bound needs every element of the reduced Gröbner basis
in the ideal (2,074 elements with 3.06 M terms for KC′, 7,411 with 42.3 M terms for S12), and any certificate of that
(cofactors, or the reductions of the F4 matrices, up to 56,801 × 58,918 for KC′ and 298,465 × 309,168 for S12) is
orders of magnitude larger than those above.

## Not checked in Lean

Each item says what the paper's proof relies on there, and what would fail if the unchecked computation were wrong.

### Lemma 6.19(b): what the Lean statement covers

Lemma 6.19(b) is checked (`count_KC`, `count_S12`, above). The Lean statement is the upper bound for the dimension of
(ZMod 65521)[v] ⧸ I at μ₀, the only direction the proof uses. The step from it to the generic fibre is the paper's:
Lemma 6.18 (good reduction at 𝔪 = (p, μ − μ₀), p = 65521) with Lemma 6.19(a) makes R = 𝒪[v]/⟨S12⟩ finite, and by
Nakayama dim_{ℚ(μ)} R ⊗ ℚ(μ) ≤ dim_{F_p} R/𝔪R ≤ 20,316 (4788 for KC12, through the isomorphic coordinate rings of
KC12, KC and KC′ when μ₃ is a unit mod p); the paragraph after Lemma 6.19 and Theorem 6.20 then put all zeros near μ₀
on the certified branches. Lemma 6.18, Nakayama's lemma and the isomorphism of the coordinate rings of KC12, KC and KC′
(a hand step in §6.7) are stated, not formalized. The paper's msolve runs (msolve 0.9.4, p = 65521, and p = 2³¹ − 1 as a
cross-check of the leading ideal) are no longer in the trusted base.

### Items not used by the proof of the main theorem

| item | why the proof does not use it (the paper's text) | status |
|---|---|---|
| Lemma 6.13, check at (1,2,7): the direct test of the 1024 × 256 signed sums (minimum 0.4537) | Lemma 6.13 is proved by hand at (1,2,40) ("By Lemma 6.13 below, P((1,2,40),(1,2,40)) ≠ 0" in the proof of Theorem 6.12); the paragraph after it begins "At μ = (1,2,7) we have checked the same conclusion by computation", and Table 3 lists Lemma 6.13 as "hand proof" with the (1,2,7) runs among the checks. The rest of that check (root disks, ρ ≥ 0.7641… > 1/√2, ρρ′ > 1/2) is checked in Lean | later |
| Theorem 6.15: the factorization of P93 into L₁L₂L₃L₄(L₅L₅′)²L₆L₇L₈ (degrees 28/36/22, 433/565/264 terms) and the agreement with the terms printed by Albouy–Kaloshin | Section 8 puts P93(m₁,m₂,m₃) into F₀ and needs only P93 ≠ 0; the proof of Theorem 6.15 gets it from (1,2,40): "By the proof of Lemma 6.13, at μ = (1,2,40) every root t of S_μ has A₃(t) > A₁(t) + A₂(t) … and P93(1,2,40) … is not zero" (checked in Lean: `heavy_roots`, `heavy_signed_sums`, and `P93_eval_1_2_7_ne_zero` at the second point). The factorization identifies P93 with Albouy–Kaloshin's polynomials, a comparison with the literature | later (needs resultants in ℤ[μ₁, μ₂, μ₃]) |
| Lemma 6.9, check: that the stored g is Singular's eliminant; the counts 102 solutions, 114 with multiplicity | Lemma 6.9 is proved by hand; Table 3: "Lemma 6.9 \| hand proof \| eliminations in Singular at (1,2,7), (1,2,8) and (2,3,11), compared with S_μ in SymPy". The comparison of square-free parts is checked in Lean | later (Gröbner bases over ℚ) |
| the correspondence of the factors of S_μ with S₁–S₈ of the Albouy–Kaloshin appendix (remark after Lemma 6.9) | a remark comparing with a printed source | not checked |
| Lemma 6.19(a): gfan's counts 2149 / 224 cones (2148 / 223 tested) | the hypothesis of Lemma 6.18 is what the proof uses; Lean proves it for all weight vectors at once with its own finer covering, so these counts are not reproduced | not needed |
| §6.6, numerical zeros of P93 on twelve rays | "Numerical minimization, which the proof does not use" | not a claim |

### Hand proofs (stated, not formalized)

Lemma 6.1, Props 6.4, 6.7, Thm 6.5 (exponent arithmetic), Lemmas 6.10, 6.11, Thm 6.12 (Φ ∈ ℤ[Y] homogeneous of degree
128, and the resultant formula for P), Lemma 6.16, Lemma 6.18 (good reduction), Thm 6.20; Lemmas 7.1–7.6, Prop. 7.8,
Lemma 7.10, Prop. 7.11, Thms 7.12, 7.13; Section 8; in Section 9 the tree-meet facts (9.1), (9.2), the linear algebra
of Thm 9.9 (dependence of 1, ξ, η; the rank-one form of L) and of Lemma 9.13 (the line over ℚ(m)); in Lemma 7.6 the case
split on dim span(1, ξ, η). Their computational ingredients are checked above. The algebraic
identities and finite computations inside them, and inside the hand proofs of Sections 2–5, are listed in `PLAN.md`
("Computations inside hand proofs") with their status.

### Primes and Singular modulo 2³¹ − 1

Singular 4.4.1 gives wrong verdicts modulo 2147483647 = 2³¹ − 1. The computations of Sections 6–7 were audited for this
(every script and log under the directories of diagrams 64/66, 88/94, 89/90/93/98 and their referees). The prime
2147483647 occurs only in the msolve cross-check of Lemma 6.19(b) (`count/full_1_2_3_30_p2147483647.*` and
`kc/kc_full_1_2_3_30_p2147483647.*`, msolve 0.9.4); no Singular computation used by the paper ran at that prime. The
Singular runs are modulo 65521 (Lemma 6.19(a) cone tests and the four-body systems; the KC′ count), modulo 32003
(Lemma 7.9 and §7.4), and over ℚ or ℚ(j). The Lean checks do not depend on these runs: the cone-test cofactors from
Singular `lift` (modulo 65521) are verified in Lean; Lemma 7.9 and §7.4 are decided by the Lean engine (32003 and
1073741789); Lemma 7.7 and the check at (3,5,7,11) compute modulo 2147483629 in Lean itself.

## Data and regeneration

| component | inputs (sha256) | generated data |
|---|---|---|
| D98 | `data/d98/SHA256SUMS` | `Comp/D98/Data.lean`, `RootsData.lean` by `gen/d98/gen_certs.py`, `gen_roots.py` |
| D88 Trop | `data/d88trop/SHA256SUMS` | trees and data, `data/d88trop/GENERATED.sha256`, `gen/d88trop/run.sh` |
| D88 Boxes | `data/d88boxes/SHA256SUMS` | 393 modules, `gen/d88boxes/manifest.sha256`, `gen/d88boxes/gen.py` |
| K4 E4 | none read (`data/e4/SHA256SUMS`: references) | `gen/e4/gen_resultants.py`, `gen_algebra.py` |
| K4 C4 | `data/c4/SHA256SUMS` (comparison only) | `gen/c4/gen_runs.py` (56 run modules) |
| kernel: boxes | the box strings of D88 Boxes | `L6CheckKSpec/N4`, `KC`, `data/ksp` by `scripts/kern/ksp_gen.py`, `kspc_gen.py` (committed; reproduced by the build) |
| kernel: E4 | none | `L6CheckKSpec/E4` by `scripts/kern/ke4_gen.py` (committed; reproduced by the build) |
| kernel: C4 | `data/kern/SHA256SUMS` (certificates), the chart equations (`gen/c4/dump_eqs.lean`) | `L6CheckC4`, `data/c4k` by `scripts/kern/kc4_gen.py`, `data/c4k/SHA256SUMS` |
| kernel: Trop | `data/kern/SHA256SUMS` (`esc_kc_0`, `trace_hypN4`), `Comp/D88/Trop/Data*.lean`, `Tree*/` | `L6CheckTrop`, `data/tropk` by `scripts/kern/ktrop_gen.py`, `data/tropk/SHA256SUMS` |

The generators run with `python3 -I` in an environment with python-flint 0.9.0, mpmath, sympy and HiGHS; Singular
4.4.1 for the cofactor certificates of the cone tests.

## Merge with the companion project

All modules are under `Lean6.Special` (directory `Lean6/Special/`). Copy the directory, the aggregator
`Lean6/Special.lean`, `gen/`, `data/`, `logs/` and this file, and add the two libraries of `lakefile.toml`: the
statements and proofs (`roots = ["Lean6.Special"]`) and the checkers (`roots = ["Lean6.Special.Comp"]`,
`precompileModules = true`), declared in this order (Lake assigns a module to the last library that contains it).
Also `L6KSpec/`, `L6SoundKSpec/` with their two libraries, `L6CheckKSpec/`, `scripts/kern/`
and `data/ksp/`, `data/c4k/SHA256SUMS`, `data/tropk/SHA256SUMS`.
