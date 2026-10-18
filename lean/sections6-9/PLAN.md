# Lean 4 checks of the computations of Sections 6–9: inventory and plan

**Status (2026-10-17): the plan below was written first; the result is `LEAN_CHECKS.md`.** Built in v1 beyond the
plan: Lemma 6.19(a)(iii) (the covering of w-space), Lemma 7.9 and §7.4 (by a Buchberger engine in Lean instead of
cofactors), Remark 7.14, and the check of Lemma 6.13 at (1,2,7) except the direct test of the signed sums. Not built:
Lemma 6.19(b), the factorization of P93, the counts of the eliminations of Lemma 6.9.

Paper: "Smale's sixth problem for six bodies in the plane: finiteness of central configurations for generic masses"
(numbering of the build of 2026-10-17). Toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `c55e6e7`, the revisions
of the five-body development. Modules live under `Lean6.Special` (directory `Lean6/Special/`).

## Design

* **Checkers** (`Lean6/Special/Comp/`, no Mathlib, library `Lean6SpecialComp` with `precompileModules = true`): exact
  arithmetic on `Nat`, `Int`, `Rat`, lists and arrays. Each run is a theorem `checker data = true := by native_decide`
  in a `Comp` module, so that it runs compiled code. Floating point may propose (centres, pivots, cofactors computed
  by the generators); the trusted check is exact.
* **Soundness** (`Lean6/Special/` outside `Comp/`, with Mathlib): for each checker a lemma, proved without `sorry`,
  that turns `checker data = true` into a mathematical statement about Mathlib objects (`ℂ`, `MvPolynomial`, `ZMod p`,
  `Matrix`). No axioms besides the standard ones and `Lean.ofReduceBool` (and `Lean.trustCompiler`) of `native_decide`.
* **Data**: where a certificate file of the supplement exists it is the input (its sha256 recorded in `data/SHA256SUMS`);
  where only a program exists, the generator in `gen/` regenerates the certificate from the program's inputs and
  `LEAN_CHECKS.md` records how.
* Logs under `logs/`.

Shared infrastructure (built first):

| module | content |
|---|---|
| `Comp/Poly` | sparse multivariate polynomials over a coefficient type with computable `+`, `*` (`ℤ`, `ℚ`, `ℤ/p`, `ℤ[j]` as pairs with `j² = −1 − j`), normal form, identity test |
| `Poly/Sem` | evaluation in any commutative ring through a coefficient map that respects `+`, `*`: `eval (p * q) = eval p * eval q`, `normalize` preserves `eval`, so a successful identity test gives an identity of polynomial functions over every commutative ring (hence in `MvPolynomial`) |
| `Comp/UPoly` | dense univariate polynomials over `ℤ`, `ℚ`: Taylor shift, division with remainder, Bezout identities |
| `Comp/Ball/*`, `Ball/*` | copied from the five-body development (`CC5Full.Core.Ball`, `CC5Full.Core.D14a.Ball`): complex balls, Krawczyk checker `krawOK` with `kraw_exists`, and the Krawczyk theorem `krawczyk` (exactly one zero, nonsingular slopes) |

## Inventory

Status: **v1** = built in this release; **later** = a later version; **hand** = no computation (or the computation is
the hand proof itself, nothing to check by machine). Costs: E = estimated, M = measured.

### Section 6

| claim (label) | computation | files | Lean check | status, cost |
|---|---|---|---|---|
| Lemma 6.2 (`lem:rewrite`) | identity Σ_j m_j m_o p³(z_j w_o − z_o w_j) = m_o(z_o A_w − w_o A_z) | — | `ring` identity in the variables (`Hand/Identities`) | v1, minutes |
| Lemma 6.3 (`lem:binary`) | m_5 ẑ_5 + m_6 ẑ_6 = 0, p̂² = −1/(ẑŵ), m_5p̂_5 = −m_6p̂_6 ⇒ m_5³ + m_6³ = 0 | — | field identity (`Hand/Identities`) | v1, minutes |
| Props 6.4, 6.7, 6.8, Thm 6.5 | exponent comparisons (linear inequalities); Prop 6.8: (u_1/u_2)² = −m_2³/m_1³ ⇒ m_1 = m_2 | — | the algebraic steps as lemmas over ℝ, ℂ (`Hand/Identities`) | v1 (algebra only), 1 h E |
| Lemma 6.9 (`lem:three`), hand proof | Lagrange case: t² − (1 + j^b − j^c)t + j^b, the classes (0,0), (1,2), (2,1) give t² − t + 1, the conjugate pairs give the products N01, N10, N11 | — | products in ℤ[j][t] (`D98/Shapes`) | v1, minutes |
| Lemma 6.9, definitions | Q_σ(x) = x²(1+x)²(x(F_1−F_2) − (F_2−F_3)) is a quintic; S_μ has degree 34 and leading coefficient (μ_1+μ_2)⁴ | — | `S_μ` built in `ℤ[μ][t]` from the definitions; degree and leading coefficient by evaluation of the coefficient list; Q_σ against the rational-function definition by `field_simp` | v1, 1 h E |
| Lemma 6.9, check (†) | eliminant at (1,2,7), (1,2,8), (2,3,11): square-free part = that of S_μ, degree 32 | d98/certificates/lemB/elim_*.txt | the stored eliminant g and S_μ: a square-free g₀ (Bezout certificate u g₀ + v g₀' = c ≠ 0) with g₀ ∣ g ∣ g₀^k and g₀ ∣ S_μ ∣ g₀^k (exact divisions) | v1, 1 h E. Not checked: that g is the eliminant (Singular), and the counts 102/114 (Gröbner bases); later |
| Thm 6.12 (`thm:d98`) | Φ ∈ ℤ[Y] homogeneous of degree 128; resultant formula for P | — | hand (Galois symmetry, resultant theory) | hand |
| Lemma 6.13 (`lem:dominant`), hand proof at (1,2,40) | the four Lagrange factors: Σ_{k≥1}\|a_k\|10^{-k} ≤ 0.5951 at c = 0, 1; Q_σ = 40C_σ + D_σ; \|C_σ(c)\| = 1, \|C_σ − C_σ(c)\| ≤ 0.332, \|D_σ\| ≤ 2.446 on \|x − c\| ≤ 1/10; ℓ formulas; 1/40·(23/20)^{1/2} < 0.03, 1/20·(13/20)^{1/2} < 0.05, 1/1.08 > 9/10 | paper_generic/tools/p98_heavy_mass.py, audit/p98_heavy_mass.txt | exact Taylor shifts and coefficient sums (`Comp/D98/Heavy`); soundness proves the analytic statements: every root t ∈ ℂ of S_μ has \|t\| > 1/10, \|t − 1\| > 1/10, ρ(t) > 9/10; and \|Σ ε_{jl} c_{jl}\| > 0 whenever \|c_{jl}\| = A_j(t)A_l(t′) (the "consequently" step) | v1, 4 h E |
| Lemma 6.13, check at (1,2,7) (†) | 34 roots, 32 distinct, min ρ = 0.7641… > 1/√2, Rouché disks 2^-120; 1024 × 256 signed sums ≥ 0.4537; ρρ′ > 1/2 at (1,2,7 \| 1,2,8) | d98/certificates/d98_cert_127_12{7,8}.json, d98_check_rational.log; d98/scripts/d98_check_rational.py | root isolation by exact Rouché disks (a disk certificate per root, multiplicities by a degree count) and exact lower bounds of ρ | later (a check of a statement proved by hand at (1,2,40)); 1 day E |
| Thm 6.15 (`thm:d93`) (†) | factorization of P93 into L1…L8 (Singular), degrees and term counts; AK's printed terms | d98/certificates/p93_factors.txt, p93_analyze_127.log; d98/scripts/p93_resultants.sing | needs resultants in ℤ[μ_1,μ_2,μ_3] (Sylvester determinants with polynomial entries): a verified determinant (LU certificate over ℚ at grid points + the combinatorial Nullstellensatz of Mathlib, or Laplace by column subsets) | later (comparison with AK, not used in the proof); 1–2 days E |
| Thm 6.15, P93(1,2,7) ≠ 0 | exact evaluation | p93_analyze_127.log | Bezout certificate U·S_μ + V·Φ_3 = c ≠ 0 at μ = (1,2,7) in ℤ[t]: S_μ and Φ_3 have no common root in ℂ, so the resultant is nonzero | v1, 1 h E |
| §6.7, systems | the torque identity Σ_k μ_k(Y_k Xeq_k − X_k Yeq_k) = 0; S11/S12, KC12/KC′ written from the definitions | d88/scripts/k4sys.py, kc_sys.py | polynomial identity; the msolve inputs (`*.ms`) compared with the systems built in Lean | v1, 2 h E |
| Lemma 6.19(a) (†) | (i) each of the 30 / 101 polynomials of G lies in the ideal (explicit identities over ℤ[μ, 1/M, 1/μ_4]); (ii) no coefficient vanishes at μ_0 mod p (354 / 1133 terms); (iii) the prevarieties: 2149 / 224 cones (gfan), all faces, initial forms constant on relative interiors; (iv) cone tests: the initial system at a relative interior point of each of the 2148 / 223 cones meeting {min w_i < 0}, saturated by the product of the coordinates, is the unit ideal over F_p | d88/certificates/n4_trop/, kc_trop/ (gfan fans, Singular inputs); d88_referee/work/myprev (exact partition with Motzkin certificates) | (i) identities in `Poly`; (ii) evaluation mod p; (iv) per cone a monomial certificate ∏ξ^N = Σ c_i in_w(g_i) over F_p (cofactors from Singular `lift`), with the initial forms recomputed in Lean from G and w; (iii) a depth-first partition of w-space with exact Motzkin certificates for the empty pieces and exact interior points, and per leaf either a polynomial whose initial form is a monomial on the cell or a cone test | (i), (ii), (iv): v1, 1 day E (certificate sizes to be measured); (iii): v1 if time allows, else later; 1–2 days E |
| Lemma 6.19(b) (†) | dim F_p[v]/⟨S12(μ_0)⟩ = 20,316, dim F_p[v′]/⟨KC′(μ_0)⟩ = 4788 (msolve; only ≤ is used) | d88/certificates/count/, kc/ (leading ideals only) | the upper bound needs elements of the ideal (not only their leading monomials): a Gröbner basis with derivations. For S12 the reduced basis has 7,411 elements and 42.3 million terms (msolve log), and a derivation is larger; a Lean run of F4 would take tens of CPU-hours single-threaded | **later** (S12 infeasible for v1); KC: size to be measured (msolve -g 2), v1 only if the basis is small |
| Lemma 6.19(c) (†) | 20,316 pairwise disjoint boxes in ℂ¹¹, each with exactly one zero of S11(μ_0), Jacobian invertible, X_3 − X_4 ≠ 0, T-test margin ≥ 0.1756 | d88/certificates/k4_cert_1_2_3_30.jsonl (34 MB, 60-digit centres, radii ≤ 5.9e-47) | Krawczyk (`krawOK`, `kraw_exists`, `krawczyk`: one zero, nonsingular); disjointness by a sort on one coordinate plus pairwise checks; X_34 ≠ 0 by ball exclusion; T-test by exact lower bounds of \|X_k\|^{-1/2} (rational fourth roots) | v1; 650 modules of 32 boxes, about 1 CPU-h E (native) |
| Lemma 6.19(d) (†) | 4788 boxes in ℂ¹², one zero of KC12(μ_0) each, X_3 ≠ 0, the 32 sums ≥ 1.47e-6 (1+ρ²)^{1/2}Σ\|β_l\| at (m_5, m_6) = (1, 2) | d88/certificates/kc/kc_cert_1_2_3_30.jsonl (9.6 MB, radii ≤ 5e-54) | as (c); square roots of complex balls by an exact covering (\|s₀² − X\| ≤ δ ⇒ ±√X ∈ B(±s₀, δ/\|s₀\|)), ρ = 2^{3/2} in a rational interval, exact lower bounds of the moduli | v1; 150 modules, < 1 CPU-h E |
| §6.7, last paragraph (†) | the T-test at every solution of N_4 (= (c)); over the bodies 1, 2, 3 it fails at 1092 of 4788 KC solutions; the 36 solutions with relative margin < 1e-4 have \|Y_4\| > 5·10³ and \|Y_l/Y_4\| < 3·10⁻⁵ | paper_generic/tools/kc_ttest_count.py, audit/d88_ttest/ | decided per box in ball arithmetic in the checker of (d): count of certain passes and certain failures (no undecided box), and bounds at the boxes with margin < 1e-4 | v1, with (d) |

### Section 7

| claim (label) | computation | files | Lean check | status, cost |
|---|---|---|---|---|
| Lemmas 7.1–7.5 | exponent arithmetic | — | hand | hand |
| Lemma 7.6 (`lem:E4`) | rank-one stress reduction; collinear case | — | hand (algebraic steps as lemmas if cheap) | hand |
| Lemma 7.7 (`lem:E4cert`), hand proof (†) | F_ε: 729 patterns, 9 orbits, the invariant separates them, three types; (I) Σp³ ∈ {108, −3 ∓ 3√3 i, 10}; (II), (III) identities in ℤ[j] (eigenvalues, 4 + 2λ₂ + 2λ₃ = 0, 8λ₂ + 8λ₃ + 4λ₂λ₃ = 0, …); G_σ: score sequences of the 64 tournaments; e_k, R_1 = Res_s(e_1,e_2), R_2 = Res_s(e_1,e_3) = t⁴R_2′ as printed; R_1(0) = 1; Res_t(R_1,R_2′) = 2^16 3^4 5^4 7^2·3881, 2^16 3^8 5^10, −2^16 5^4·23·433 | paper_generic/tools/e4_equal_mass.py, audit/e4_equal_mass.txt | finite enumerations (orbits, scores); identities in ℤ[j]; resultants: Bezout identities A e_1 + B e_2 = R_1 (in ℤ[s,t]) and U R_1 + V R_2′ = c ≠ 0, which give the use in the proof (no common zero); the exact printed values of the resultants by a verified determinant of the Sylvester matrix (LU certificate over ℚ against `Matrix.det`) | v1, 4 h E |
| Lemma 7.7, statement, as a complete computation | at μ = (1,1,1,1) no F_ε (729 patterns) has a common zero in P³(ℂ), no G_σ (64) in P²(ℂ) | audit/d64_equal/ (Singular), d64_referee/scratch/scope/ (python-flint) | Macaulay matrices built in Lean from the forms (degree 7: 245 × 120; degree 8: 60 × 45), entries in ℤ[j]; a 120 × 120 (resp. 45 × 45) submatrix inverted mod p in Lean; soundness: det ≠ 0 mod p ⇒ det ≠ 0 in ℤ[j] ⇒ invertible over ℂ (j ↦ e^{2πi/3}) ⇒ every monomial of the degree lies in the span ⇒ no common zero | v1, 1 day E (with the next row) |
| §7.2, μ_0 = (3,5,7,11) (†) | p = 2147483629, j ↦ 882503254, ranks 120 (729 patterns, degree 7) and 45 (64 patterns, degree 8) | d64/certificates/e4_cert_macaulay_3_5_7_11.json; d64/scripts/e4_cert_macaulay.py | the same checker at μ_0 with the paper's p and root of t² + t + 1 | v1, with the previous row; seconds M (python-flint 3.7 s) |
| Lemma 7.9 (`lem:C4cert`) (†) | 14 charts, unit ideal over F_32003 and F_1073741789 at μ_0 | d64/certificates/c4_cert_*; d64/scripts/c4_cert_singular.sing, c4_systems.py | per chart a cofactor certificate 1 = Σ c_i f_i over F_p, with the equations built in Lean from the definitions of §7.3 | v1 if certificates of manageable size can be generated: Singular `lift` on one chart did not finish in 10 minutes (2.1 GB); alternatives (Macaulay-matrix solve, triangular chains) to be tried; else later |
| Lemma 7.10, Prop. 7.11 | Nullstellensatz transfer from F_p to ℚ | — | hand (stated) | hand |
| §7.4, C_4 at (1,1,1,1) (†) | the 14 charts at μ = (1,1,1,1) mod 32003 | audit/d64_equal/c4_cert_singular_1_1_1_1.* | as Lemma 7.9 | as Lemma 7.9 |
| Remark 7.14 (†) | the construction applies to 36, 16, 28, 28 patterns at four mass points; exactly these patterns have common zeros of G_σ; none survives the saturation | d64_referee/tools/collinear_saturated.sing, scratch/collinear_saturated.log | counts by enumeration; existence by evaluation at the explicit zeros; nonexistence for the other patterns by the Macaulay checker; saturation by Bezout certificates | later (a remark); 1 day E |

### Sections 8, 9

| claim | computation | Lean check | status |
|---|---|---|---|
| Sec. 8: F ≠ 0 | product of nonzero polynomials | hand | hand |
| Sec. 9, Tables 3, 4 | the checks listed above | as above | — |
| Sec. 9, Table 2 (Sections 3–5) | engine counts | the sibling project `lean6` | — |

### Computations inside hand proofs elsewhere

Section 2 (`lem:U`, `lem:balance`, the identities of §2.3) and Section 5 (`thm:clique3`, `lem:cliquesum`) contain
algebraic identities. They will be added to `Hand/Identities` as `ring`/`field_simp` lemmas once the sibling
project confirms it does not cover them.

## Order of work

1. Infrastructure: project, `Poly` + soundness, the Ball/Krawczyk port.
2. Section 7: Lemma 7.7 (hand computations and the complete Macaulay check), μ_0 = (3,5,7,11).
3. Section 6.4–6.6: Lemma 6.9 items, Lemma 6.13 at (1,2,40), P93(1,2,7) ≠ 0.
4. Lemma 6.19(c), (d) and the last paragraph of §6.7 (fleet runs).
5. Lemma 6.19(a) (i), (ii), (iv); then (iii).
6. Lemma 7.9 and C_4 at (1,1,1,1) if the certificates are small enough.
7. `LEAN_CHECKS.md`, axioms, logs.

## Computations inside hand proofs (added 2026-10-17, second round)

Scope: every algebraic identity or finite computation on which a hand proof relies, in
Sections 2–9 (the companion project `lean6` owns only the diagrams, the cell enumeration, the single-term exclusions
and the core cofactors). Numbering of the build of 2026-10-17 11:11 UTC (Section 9 = hand explanations of the cells,
Section 10 = verification). Each item becomes a Lean lemma over a commutative ring or field (`ring`, `field_simp`,
`linear_combination`, `norm_num`), or a `native_decide` check for finite computations. Status after the second round: every item is done (`LEAN_CHECKS.md`, section "Computations inside the hand
proofs") except H4.2 (owned by `lean6`), H9.16, C9.1 and C9.2 (later: they need the cell list in Lean).

| id | place | computation | status |
|---|---|---|---|
| H2.1 | §2.3 | the identities on X_m for any number of bodies: subset sums, torques T_J = 0, partial virials, differences, U = Σ m_k z_k w_k, Σ_{k<l} m_k m_l z_kl w_kl = M U (from Σ m_k z_k = Σ m_k w_k = 0), the partial virial of all bodies = U | done (`LEAN_CHECKS.md`) |
| H2.2 | Lemma 2.3(a) | U = Σ m_k z_k w_k on X_m and U = I when M ≠ 0 | done (`LEAN_CHECKS.md`) |
| H2.3 | Lemma 2.2, Lemma 2.9(b) | the rows are invariant under (u, v) ↦ (v, u); ι is an involution; z_k∘ι = w_k/v_1, w_k∘ι = v_1 z_k | done (`LEAN_CHECKS.md`) |
| H2.4 | Lemma 2.11 (proof) | f(ζ) = (4 − ζ)/3 (ζ ≤ 1), 4 − 3ζ (ζ ≥ 1) is strictly decreasing and ω = f(ζ) on edges; the inequalities of (E6) (β + 4 − α > 4, 3β + 4 − 3α > 4) and of (C4), (E3) from (O1)–(O6) | done (`LEAN_CHECKS.md`) |
| H2.5 | Cor. 2.4 (remark) | the fibre bound 2^19 = 2^4 · 2^15 | done (`LEAN_CHECKS.md`) |
| H3.1 | §3 | a triangle of strokes of one colour does not have exactly one circled vertex of that colour (from (E3), (O6)) | done (`LEAN_CHECKS.md`) |
| H4.1 | Lemma 4.3(b) | the coefficient of exponent h_r in Σ m_k z_k = 0 is Σ_c (X_{r,c} − X_{r,c_O}) M_c | done (`LEAN_CHECKS.md`) |
| H4.2 | Prop. 4.5 (proof) | 55,720 = 39,208 + 16,512 trees (rooted trees on 7 labelled leaves; 6 · 2,752 with a body on the leaf of O) | lean6 (cell enumeration) |
| H6.1 | Lemma 6.1 (F1)–(F4) | the coefficient identities of (F1), (F2), (F4): p̂² ẑ_j ŵ_l = −1, the coefficient −m_j m_l p̂ of the leading torque term | done (`LEAN_CHECKS.md`) |
| H6.2 | Props 6.4, 6.7, Thm 6.5 | the exponent comparisons (E_{4l} − E_{41} = 1 + b_1/2 > 0, …; e(Z_41) = a_1 when a_1 + b_1 = 0) | done (`LEAN_CHECKS.md`) |
| H6.3 | Lemmas 6.2, 6.3, Prop. 6.8, Lemma 6.17, §6.7 identities | (done: `Hand.*`) | done (`LEAN_CHECKS.md`) |
| H6.4 | Lemma 6.11, Thm 6.12 | c_jl² = κ m_j² m_l² Λ_j(τ) Λ_l(τ′) with κ = −M_A M_B/(s s′ ∏ℓ_j(τ) ∏ℓ_l(τ′)); the leading torque coefficient −Σ m_j m_l p̂_jl | done (`LEAN_CHECKS.md`) |
| H6.5 | Remark 6.14 | ε_jl = δ_j η_l splits the signed sum into a product | done (`LEAN_CHECKS.md`) |
| H6.6 | Thm 6.15 (proof) | Σ_l m_l p̂_4l = 0 with p̂_4l² = −1/(ẑ_4 ŵ_l) gives Σ ε_l m_l ŵ_l^{−1/2} = 0 | done (`LEAN_CHECKS.md`) |
| H7.1 | Lemmas 7.3, 7.5 | Σ_{k∈K} m_k Φ^η_k = 0 (antisymmetry); the constant-force case c′ Σ m_k = 0 | done (`LEAN_CHECKS.md`) |
| H7.2 | Lemma 7.6 | the algebra of the reduction: rank-one L with symmetric L diag(μ)^{-1} gives P_kl³ = u_k u_l; with q_k³ = u_k, P_kl = ε_kl q_k q_l and A_k = −β q_k²; the collinear case gives the forms G_σ | done (`LEAN_CHECKS.md`) |
| H7.3 | §7.3 | (II) is (iii) times ∏_{l≠k}(ξ_k − ξ_l); (III) is η_kl + η_ln + η_nk = 0 times a_kl a_ln a_nk; the bidegrees (1,3), (2,1), (2,4) | done (`LEAN_CHECKS.md`) |
| H9.1 | Lemma 9.1 | the weighted sum of the initial forms is Σ δ_k m_k ĉ_k (antisymmetry of the internal forces) | done (`LEAN_CHECKS.md`) |
| H9.2 | Lemmas 9.2–9.4 | exponent comparisons | done (`LEAN_CHECKS.md`) |
| H9.3 | Lemmas 9.5, 9.6 | the initial-form algebra: m_k P³ = 1 ⇒ the c′ form is ĉ′_k ≠ 0; (m_k + m_l)P³ = 1 and the forced contradiction | done (`LEAN_CHECKS.md`) |
| H9.4 | Lemma 9.7 | P_sa³ = P_sb³ = 1/M_T, P_ab³ = 1/M_T, the relation m_a m_b ε_ab = m_b(m_a + m_b) ε_bs + m_a(m_a + m_b) ε_sa, and the modulus bounds that exclude it (\|·\|² = β² + γ² − βγ ≥ βγ) | done (`LEAN_CHECKS.md`) |
| H9.5 | Lemma 9.8 | Σ m_t Φ^z_t = Σ m_t Φ^w_t = Σ m_t(ξ_t Φ^w_t − η_t Φ^z_t) = 0 identically | done (`LEAN_CHECKS.md`) |
| H9.6 | Thm 9.9 | (i): ξ_as = α ξ_ab n_b/n_s … gives n_s + β n_a = α n_b; (ii): m_a³ m_b³ = m_s²(m_a + m_b)(j^{2k} m_a + m_b)³ and k = 0 at positive masses; (iii) | done (`LEAN_CHECKS.md`) |
| H9.7 | after Thm 9.9 | Q_T = m_a² m_b² m_s² ∏(n_a ± n_b ± n_s) with n = m^{−1/2}, and Q_T = 0 at positive masses iff one n is the sum of the other two | done (`LEAN_CHECKS.md`) |
| H9.8 | Lemma 9.11 | the derivation of N = Res_κ(…) = 0, the specialization with M_A = m_a, M_B = m_b and its value −m_a^{12} m_b^{12} at m_s = 0 (so N ≠ 0), and κ = 1 at positive masses | done (`LEAN_CHECKS.md`) |
| H9.9 | Lemma 9.12 | the derivation of m_a m_b^5 = m_s²(m_a + m_b)³(m_a + ω m_b); the product over ω is (m_a m_b^5)³ at m_s = 0; ω = 1 at positive masses | done (`LEAN_CHECKS.md`) |
| H9.10 | Lemma 9.13 | α + β + γ = 0 with α³ = λ/(τu_1) etc. gives H_W = (u_1u_2 + u_2u_3 + u_3u_1)³ − 27(u_1u_2u_3)² = 0 | done (`LEAN_CHECKS.md`) |
| H9.11 | Lemma 9.14 | X_b Y_a = X_a Y_b, ρ = m_a r/m_b, m_a² r⁴ = m_b² | done (`LEAN_CHECKS.md`) |
| H9.12 | Lemma 9.15 | the product of Σ ε_k m_k over all signs is a nonzero polynomial | done (`LEAN_CHECKS.md`) |
| H9.13 | Lemmas 9.16, 9.17 | exponent arithmetic (1 > −2, 3x − 2 > −2, 2 − x > 2 − 4x) | done (`LEAN_CHECKS.md`) |
| H9.14 | Lemma 9.20 | P_sk³ Y_k = −P_sk/ξ, reduction to Lemma 6.3 | done (`LEAN_CHECKS.md`) |
| H9.15 | Lemma 9.22 | the P_ij² values, the four-term initial form and A_11 = A_22, A_12 = A_21 ⇒ m_{l1} = m_{l2}, m_{k1} = m_{k2} | done (`LEAN_CHECKS.md`) |
| H9.16 | Prop. 9.23 (proof) | H_W and m_a² M_A⁴ − m_b² M_B⁴ nonzero at m = (1,…,6) in the 74 cells; the minors of Lemma 9.21 nonzero | checked (`Cover/`: `prop_9_23_first`; the LIN templates have full column rank over ℚ(m), `prop_9_23`) |
| C9.1 | Prop. 9.19 (†) | 86,938 cells with a clique as in Cor. 9.18; all cells of 18 classes | checked in `lean6` (F5) |
| C9.2 | Prop. 9.23 (†) | the coverage counts 70,406 / 90,943 / 287 / 43 | checked (`Cover/`: `prop_9_23`, `prop_9_23_first`; `prop_9_23_broad`: (a) is a lower bound, see LEAN_CHECKS) |

## Lemma 6.19(b) in Lean (started 2026-10-17)

**Target.** For KC′ (4788) and S12 (20,316) at μ₀ = (1,2,3,30), p = 65521: `Module.Finite` and
`finrank (ZMod p) (ZMod p)[v] ⧸ I ≤ N`, with I the ideal of the msolve inputs (the systems written from §6.7).

**Proof shape (all in Lean).**
1. Ideal elements G, computed by an engine written in Lean whose only operations are monomial multiples and linear
   combinations, so every element lies in I by construction (as the Section 7 engine: for every commutative
   `ZMod p`-algebra R and every common zero x of the inputs in R, every element vanishes at x; with R = (ZMod p)[v] ⧸ I
   this is membership).
2. A finite set S of exponents with 0 ∈ S, closed under the border of the leading exponents of G (for s ∈ S and each
   variable i: s + eᵢ ∈ S or some leading exponent divides s + eᵢ); S is the staircase of msolve's leading ideal
   (data), the check is a native computation.
3. `D88.Count.finrank_le_of_border` (done, `Lean6/Special/D88/Count/Dim.lean`, standard axioms only): Mathlib's
   division algorithm `MonomialOrder.div_set` plus the border closure give that the monomials of S span the quotient,
   hence dimension ≤ |S|.
4. The bridge from the engine's polynomials (sorted term lists mod p) to `MvPolynomial (Fin 11) (ZMod p)` and to
   `m.degree` for a Mathlib `MonomialOrder` m (Mathlib has `degLex`; grevlex would need a `MonomialOrder.degRevLex`
   built here).

**KC′.** The reduced basis has 2,074 elements, 3,059,205 terms, leading monomials of degree ≤ 8 (msolve 9.9 s on 32
threads; Singular std 1,474 s with grevlex, 1,991 s and a basis of 3,110 elements / 4.65M terms with deglex). The Section 7 engine would need about 12–13 h;
the F4 engine below does it in 33 s. **Done** (`count_KC`).

**S12 — options (sizes measured or estimated).** The msolve measurements of this table were made with msolve 0.7.5,
the version installed on the build machine (the paper's runs used 0.9.4).

| option | idea | size / cost | verdict |
|---|---|---|---|
| A. Buchberger in Lean (Section 7 engine) | recompute the basis | reduced basis 7,411 elements, 42.3M terms, leading monomials of degree ≤ 10; Singular std > 2.7 h, so > 80 h in Lean | infeasible |
| B. F4 in Lean, sound by construction | symbolic preprocessing + sparse elimination mod p, rows are monomial multiples of basis elements; all operations linear combinations | msolve: 3,191 CPU-s, largest matrix 285,365 × 296,591 at 0.4 %; the Lean F4 (packed monomials, dense accumulators, parallel reduction) took 10 min wall on 64 threads (15 GB) for S12 and 33 s for KC′ | **done** (`count_S12`, `count_KC`) |
| C. Replay of a derivation trace from an external engine | the checker replays S-pair reductions only | needs an external engine with traces (none available: msolve/Singular print none); replay cost ≈ the useful reductions of Buchberger, still > Singular's useful work | not pursued |
| D. Smaller equivalent system | eliminate Y by the distance equations (Y_kl = 1/(p_kl² X_kl), cycle relations) or X by Cramer's rule; or u = p³ | Y eliminated (9 unknowns with a saturation variable, `gen/d88count/reform.py`): msolve basis of 14,941 elements and 100.3M terms in 24,733 CPU-s, against 42.3M terms and 3,191 CPU-s for the original | worse; not needed |
| E. Symmetry (Y, p) ↦ (νY, νp), ν³ = 1 | quotient by ℤ/3 (6,772 orbits) | invariant coordinates are not free; needs a free-action/covering argument for dimensions | not pursued |
| F. Decomposition (collinear 3,360 + Dziobek 16,956) | dim A = dim A/(h) + dim A/(0 : h) | the large part keeps ≈ 84 % of the work, plus colon-ideal certificates | not pursued |
| G. Degree/mixed-volume bound | count by Bernstein or multihomogeneous Bezout | mixed volume of S11 is 37,152 ≠ 20,316 (gfan); Bernstein's theorem is not in Mathlib | not applicable |
| H. Other variable orders (same system) | grevlex with permuted variables | msolve: 42.4M terms (Y first), 54.9M and 55.8M (p first, reversed) against 42.3M | no gain |
