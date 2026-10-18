# CC6Full: plan of the Lean formalization of the six-body theorem

Project `rung3/lean6_full` (this directory), Lean package `CC6Full`. Started 2026-10-16 (Pacific).

Target: a hypothesis-free Lean proof of Theorem 1.1 (`thm:main`) of the paper *Smale's sixth problem for six bodies
in the plane: finiteness of central configurations for generic masses* (`rung3/paper_generic`, `main.tex`,
`sec/*.tex`; statement numbers below are those of `main.aux` of 2026-10-17 04:41 UTC; the LaTeX labels are the
stable references). `native_decide` is allowed in this version; a later version replaces it by kernel evaluation.

The certificates of the paper are checked by two sibling projects: `rung3/lean6` (Sections 3–5: diagrams, cells,
single-term exclusions, cores) and `rung3/lean6_special` (Sections 6–7). Their checkers' soundness lemmas become
lemmas of this proof (§5). Toolchain and Mathlib are those of the five-body formalization `rung2/lean_full`
(`leanprover/lean4:v4.35.0-rc3`, Mathlib `c55e6e7`), from which we reuse the theory of curves, places and
expansions (§4).

---

## 1. The Lean statement

`CC6Full/Statement.lean` (builds):

```lean
abbrev Conf (n : ℕ) := Fin n → ℂ
def CollisionFree {n : ℕ} (q : Conf n) : Prop := ∀ i j, i ≠ j → q i ≠ q j
def IsCC {n : ℕ} (m : Fin n → ℝ) (q : Conf n) : Prop :=
  CollisionFree q ∧ ∃ (lam : ℝ) (c : ℂ), ∀ i,
    ((lam * m i : ℝ) : ℂ) * (q i - c) =
      ∑ j ∈ univ.erase i, ((m i * m j / ‖q i - q j‖ ^ 3 : ℝ) : ℂ) * (q i - q j)
def Similar {n : ℕ} (q q' : Conf n) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ ((∀ i, q' i = a * q i + b) ∨ (∀ i, q' i = a * starRingEnd ℂ (q i) + b))
def FinitelyManyCC {n : ℕ} (m : Fin n → ℝ) : Prop :=
  ∃ F : Finset (Conf n), ∀ q, IsCC m q → ∃ q' ∈ F, Similar q' q
def GenericFiniteness (n : ℕ) : Prop :=
  ∃ F : MvPolynomial (Fin n) ℤ, F ≠ 0 ∧
    ∀ m : Fin n → ℝ, (∀ i, 0 < m i) → MvPolynomial.aeval m F ≠ 0 → FinitelyManyCC m
def MainTheorem : Prop := GenericFiniteness 6
```

Justification.
* `IsCC`, `Similar`, `FinitelyManyCC` are the definitions of the five-body formalization (`CC5Full/System.lean`)
  with `Fin 5` replaced by `Fin n`, so that the two theorems are stated in the same terms. `IsCC` is (1.1) with the
  plane taken as `ℂ`. Admitting reflections in `Similar` does not change finiteness (the conjugate of a central
  configuration is one).
* `F ∈ ℤ[m₁, …, m₆]` as in the paper; with `ℚ` the statement is equivalent (clear denominators). `aeval m F` is
  `F(m)`.
* The statement is not vacuous: a nonzero polynomial does not vanish on a nonempty open subset of `ℝ⁶`, so the
  masses covered are dense and open in `(ℝ_{>0})⁶`. A sanity lemma `exists_pos_aeval_ne_zero` (every nonzero
  `F` is nonzero at some positive mass vector) goes in a separate file, not in the statement.
* Generic in `n`: the n-independent half of the proof (§2, Part I and II) is stated for every `n ≥ 2`.

---

## 2. Architecture: two halves joined by germs

The paper argues on curves `C ⊆ Y_m` and their singular places. Everything after Corollary 2.7 (`cor:sum`) uses only
the expansions of the functions `z_k, w_k, p_kl` at one singular place, rotated as in Lemma 2.5 (`lem:place`). We
therefore cut the proof at a **germ**: a solution of the equations of the bodies in Hahn series.

```lean
/-- The expansions at a singular place, rotated, in the variable `τ = ϑ^d`, so that `f = τ^{e(f)} y_f(τ)`
(`Germ.orderTop = exponent`). -/
structure Germ (n : ℕ) (m : Fin n → ℝ) where
  z : Fin n → HahnSeries ℚ ℂ
  w : Fin n → HahnSeries ℚ ℂ
  p : Fin n → Fin n → HahnSeries ℚ ℂ
  p_symm : ∀ k l, p k l = p l k
  body_z : ∀ k, z k = ∑ l ∈ univ.erase k, HahnSeries.C (m l : ℂ) * p k l ^ 3 * (z k - z l)   -- (2.2)
  body_w : ∀ k, w k = ∑ l ∈ univ.erase k, HahnSeries.C (m l : ℂ) * p k l ^ 3 * (w k - w l)
  dist : ∀ k l, k ≠ l → p k l ^ 2 * (z k - z l) * (w k - w l) = 1
  E : ℂ
  E_ne : E ≠ 0
  pot : ∑ k, ∑ l ∈ Ioi k, HahnSeries.C ((m k * m l : ℝ) : ℂ) * p k l = HahnSeries.C E      -- U = E
  low_z : (∀ k, (-2 : WithTop ℚ) ≤ (z k).orderTop) ∧ (∀ k l, k ≠ l → -2 ≤ (p k l ^ 3 * (z k - z l)).orderTop) ∧
          ((∃ k, (z k).orderTop = -2) ∨ ∃ k l, k ≠ l ∧ (p k l ^ 3 * (z k - z l)).orderTop = -2)
  low_w : -- the same for w
```

`Germ.x k l = −orderTop (p k l)` is the type, `Germ.ell = ∑_{k<l} x_kl` is `ℓ(x(P))`; the diagram, the trees and the
leading coefficients are read off the series. The proof is

```lean
-- Part I (n-generic, curves and places; §§2.1–2.2 of the paper)
theorem exists_germ (hn : 2 ≤ n) (hm : ∀ i, 0 < m i) (h : ¬ FinitelyManyCC m) : ∃ G : Germ n m, G.ell ≤ 0
-- Parts II–V (germs; §2.3 to §8)
theorem no_germ : ∃ F : MvPolynomial (Fin 6) ℤ, F ≠ 0 ∧
    ∀ m, (∀ i, 0 < m i) → MvPolynomial.aeval m F ≠ 0 → ∀ G : Germ 6 m, 0 < G.ell
theorem main : MainTheorem   -- from the two
```

Why germs. (i) Relabelling and the exchange of the colours (Lemmas 2.2, 2.9, `lem:exchange`, `lem:symm`) are
trivial on germs (`G.relabel σ`, `G.swap`), while on curves they need the involution `ι` of `Y_m`, which is not a
polynomial map. (ii) All identities of §2.3 are ring identities in `HahnSeries ℚ ℂ` that follow from `body_z`,
`body_w`, `dist`, `pot`, and Lemma 2.10 (`lem:initial`) is the additivity of coefficients. (iii) The certificates
(cells, initial systems, leading systems of Sections 6–7) only see exponents and leading coefficients. (iv) Part I
is a port of proved five-body theory (`CC5Full/Theory/{CorU,FunctionField,…}`), Parts II–V are new.

The variety. Part I uses the coordinates `z_k, w_k` (all `k`) and `p_kl` (`k < l`) instead of the paper's
`u, v, p`: rows `z_k − Σ_l m_l p_kl³ (z_k − z_l)`, the same in `w`, `p_kl² (z_k − z_l)(w_k − w_l) − 1`, and the
slice `z_1 − z_2 = 1`. This variety is isomorphic to the paper's `Y_m` (`u_k = z_k − z_6`, `z_k = u_k − F_6(u)`),
the relabellings act by permuting coordinates, and `U = Σ_k m_k z_k w_k` holds on it without dividing by `M`, so
Lemma 2.3 (b) (`U` constant on curves) holds for all masses by the derivation identity `dU = −½ d(Σ m_k z_k w_k)`.

---

## 3. The chain of results as Lean statements

Notation: `Germ n m` as above; `hm : ∀ i, 0 < m i`. Namespaces: `CC6Full` (statements), `CC6Full.Curve` (Part I),
`CC6Full.Germ` (Part II), `CC6Full.Six` (Parts III–V). Each paper result becomes a theorem (or a `Prop` in
`CC6Full/Interface.lean` while unproved, with `main_of_interface : Interface → MainTheorem`).

### Part I — from infinitely many central configurations to a germ (n-generic)

| paper | Lean statement (sketch) | source |
|---|---|---|
| [Tom26, L. 2.1], `lem:slice` (a) | `exists_slice_point : IsCC m q → ∃ y ∈ Ym m, eval y U ≠ 0 ∧ Similar (conf y) q`; `finitelyManyCC_of_finite : {y ∈ Ym m \| eval y U ≠ 0}.Finite → FinitelyManyCC m` | port of `CorU/SlicePoint.lean`, `RealPos.lean` (λ > 0, the cube root scaling) to `Fin n` and the z-w-p variety |
| proof of `cor:curve` (fibres) | `r2_fibre_finite : {y ∈ Ym m \| ∀ k l, eval y (r2 k l) = c k l}.Finite` (`M ≠ 0`) | port of `CorU/Fibre.lean` (≤ 2^{n−2}·2^{n(n−1)/2} points) |
| `cor:curve` (Cor. 2.4) | `exists_curve : hm → ¬ FinitelyManyCC m → ∃ C : Curve m, C.Nontrivial` (`Curve m`: prime of dimension one containing the ideal of `Y_m`; nontrivial: `U ∉ 𝔭` and some `r²_kl` not constant) | `CorU/Algebra.lean` (general σ), `CorU/CorU.lean` |
| `lem:U` (a), (b), (c) | `U_eq_virial` (in the ideal), `Curve.U_const : ∃ c, U − C c ∈ C.ideal` (every `m`), `U_pos` | new derivation identity; `ConstU.lean` mechanism (expansion at a centred place); `RealPos.lean` |
| places | `Place C` (normalized discrete valuation of `ℂ(C)` trivial on `ℂ`), `vZ`, `vW`, `Singular`, `d`, `γ`, exponents `e_κ(f) = (2/d)(ν f + κ γ)` for rotation weight `κ ∈ ℤ` | `CC5Full/Places.lean` generalized |
| `lem:place` (L. 2.5), last statement | `Expansion_exists` (residue fields `ℂ`, `ℂ(C) ↪ ℂ((t))`) | `FunctionField/{Dim,AlgRel,Residue,Expansion}.lean`, generalized to `ACurve σ` |
| `lem:balance` (L. 2.6) | `balancing : C.Nontrivial → ∃ S : Finset (Place C), (∀ P, P ∈ S ↔ P.Singular) ∧ S.Nonempty ∧ (∀ P ∈ S, 0 < P.d) ∧ ∑ P ∈ S, P.d • P.type = 0` | `FunctionField/{ValLemmas,Degree,Places,Divisor}.lean`, `Orders.lean` |
| `cor:sum` (Cor. 2.7) | `exists_place_ell_nonpos : C.Nontrivial → ∃ P, P.Singular ∧ ∑_{k<l} P.type k l ≤ 0` | new (3 lines) |
| `lem:place` (L. 2.5), exponents | `germ_of_place : P.Singular → C.Nontrivial → (E : P.Expansion) → Germ n m` with `(germ).x = P.type`; `low_z`, `low_w` from `ν 𝒵 = min`; `pot` from `Curve.U_const` | `GermPlace.lean` (`tauEmb`, rotation `s = τ^{2γ/d}`) |
| target | `exists_germ` | assembly |

### Part II — germ-level theory (n-generic)

| paper | Lean statement (sketch) | source |
|---|---|---|
| `lem:slice` (b), `lem:exchange`, `lem:symm` | `Germ.relabel (σ) : Germ n m → Germ n (m ∘ σ)`, `Germ.swap : Germ n m → Germ n m`, `Germ.scale (t > 0) : Germ n m → Germ n (t • m)`; their action on orders, diagram, type | new (trivial on series) |
| §2.3 identities | `subsetSum_z J`, `torque J`, `partialVirial J`, `difference k l`, `virial : Σ m_k z_k w_k = C E`, `lagrange : Σ_{k<l} m_k m_l z_kl w_kl = C (M E)`, `com_z : Σ m_k z_k = 0` | new (ring identities, antisymmetric double sums as in `RealPos.sum_antisymm_q`) |
| `lem:initial` (L. 2.10) | `initial : ∑ i ∈ s, C (c i) * g i = 0 → (∀ i ∈ s, c i ≠ 0 ∧ g i ≠ 0) → s.Nonempty → (min attained twice) ∧ ∑_{i : order = min} c i * (g i).leadingCoeff = 0` | new (HahnSeries coefficients) |
| `lem:orders` (L. 2.8) (O1)–(O6) | `Germ.O1 … Germ.O6` on `ζ_kl = ord(z_k − z_l)`, `ω_kl`, `x_kl` | port of `OrderCalc.lean`, `Types/Rules.lean` (valuation arguments become `orderTop` arguments) |
| `lem:rules` (L. 2.11) | `Germ.rules (hm) : RulesComb G.diagram ∧ (E3, E6 with equal ζ, ω)` | port of `Types/Rules.lean` (`tri_rule`, `quad_rule`, `circ_*`, `rule1d_closed`, `c5_rule`, `e1/e4/e5_rule`) |
| `def:tree`, `lem:tree` (L. 4.2) | `Germ.hz p q = ord (zpos p − zpos q)` on `B = Option (Fin n)` (`zpos none = 0`) is an ultrametric with at most one infinite pair; the balls form the tree; `Germ.nodeCoord v c` with `lc(z_p − z_q) = X_{v,c(p)} − X_{v,c(q)}` | new |
| `lem:constraints` (L. 4.3) | `Germ.constraints (hm) : (a) ∧ (b) root has ≥ 3 children ∧ (c) min attained twice in the 14 base identities` | new |
| `def:cell` (Def. 4.4) | `Cell` data and `Cell.Realizes c G` (a height assignment on the internal nodes, strictly increasing, reproduces `hz`, `hw`, and the argmin sets are those of `G`) | new; must match lean6's encoding (§5) |
| `lem:single` (L. 5.1) | `single : Cell.Realizes c G → SingleMin c I → False` | new, from `initial` |
| initial systems | `initForm I S : MvPolynomial (NodeVar ⊕ PairVar ⊕ Unit) ℚ[m]` and `Germ.leadPoint` with `eval (leadPoint) (initForm I S) = 0` when `S` is the argmin set of `I` at `G`, `Θ(leadPoint) ≠ 0` | new |
| `lem:core` (L. 5.2) (a), (b) | `core_a : Σ g_i f_i = C h → (f_i initial forms constant on c) → Cell.Realizes c G → aeval m h = 0`; `core_b` with one mass set to `1` (via `Germ.scale`) | new |
| `lem:common` (L. 6.1) (F1)–(F4), `lem:rewrite` (L. 6.2), `lem:binary` (L. 6.3) | `Germ.F1 … F4`, `Germ.rewrite`, `Germ.binary` for a colour-generic pair (as `ColPair` in `Types/Rules.lean`) | new |

### Part III — the computations of Sections 3–5 (n = 6; checkers of `rung3/lean6`)

| paper | needed statement | discharged by |
|---|---|---|
| `prop:enum` (3.1) | `enum_sound : ∀ D : Diagram 6, RulesComb D → ∃ σ sw, D.act σ sw ∈ reps` (191 representatives) | lean6 enumeration checker (`native_decide`) + soundness |
| `prop:cells` (4.5), `lem:farkas` (4.6) | `cells_sound : D ∈ reps → ∀ X : ExpData 6, X.diagram = D → X.Constraints → X.ell ≤ 0 → ∃ c ∈ cellList D, c.Realizes X` | lean6 cell checker (76,087,734 Farkas certificates) + soundness |
| `prop:exclusion` (5.3) | for each `c ∈ cellList D` not among the 43: `SingleMin c I` (184,997,938 certified argmin decisions in total) or a core `(G_c, cofactors, h_c ≠ 0)` with `Σ g_i f_i = h_c`, `f_i` initial forms whose argmin sets are constant on `Π_c` | lean6 checkers; the cofactors of the 2,413 cores are not in the paper's runs and must be computed (Singular `lift`, already sampled on 40 cores, ≤ 1.7 MB each) |

### Part IV — the seven diagrams (n = 6)

| paper | Lean statement (sketch) | certificate |
|---|---|---|
| `thm:d89` (6.5) | `d89 (hm) (G : Germ 6 m) : G.diagram ≠ D89` (and all labellings, by `relabel`, `swap`) | none (hand) |
| `lem:three` (6.9) | `three : sol of N(μ) → μ_k ≠ 0 → M_μ ≠ 0 → (Lagrange ∨ collinear) ∧ eval τ (S μ) = 0` with the explicit `S_μ` of degree 34 | none (hand; explicit identities) |
| `lem:d98type`, `lem:d98lead` (6.10, 6.11) | `d98_lead : G.diagram = D98 → N(m_A)` solution, `N(m_B)` solution, cross relations, `Σ m_j m_l p̂_jl = 0` | none |
| `thm:d98` (6.12) | `d98 : ∃ P : MvPolynomial (Fin 3 ⊕ Fin 3) ℤ, P ≠ 0 ∧ ∀ m G, hm → G.diagram = D98 → aeval (m_A, m_B) P = 0` | via `elim_integral` (below) instead of the resultants; needs `lem:dominant` |
| `lem:dominant` (6.13) | at `μ = (1,2,40)`: every root `t` of `S_μ` has `|t|, |t−1| > 1/10` and `ρ(t) > 9/10`; hence no `(t, t', c)` with `Σ c_jl = 0` | exact rational bounds (`norm_num`/`decide`) |
| `thm:d93` (6.15), first statement | `d93 : ∃ P93 ≠ 0, ∀ …, G.diagram = D93 → P93(m_B) = 0` (the factorization into `L_1 … L_8` is not needed) | via `elim_integral` and `lem:dominant` |
| `lem:d88lead` (6.16), `lem:Ttest` (6.17) | leading data of 88 and 94 solve `N_4`, resp. `KC`, with the torque relations (6.1), (6.2); the T-test and the 32 sums | none |
| `lem:goodred` (6.18) | `goodred`: an ideal `I ⊆ O[v]` (`O = ℤ[μ]_𝔪`) with units `ξ`, a finite `G ⊆ I` in `ξ` with unit coefficients, and for every initial pattern of `G` that is realizable with some `w_i < 0` a cofactor certificate `(Π ξ)^a = Σ c_g in(g) mod 𝔪`, ⟹ every `v_i` satisfies a monic relation over `O` mod `I` | lean6_special: the patterns (DFS with Farkas certificates, valid over any ordered abelian group) and the cofactors mod `p` |
| `lem:d88comp` (6.19) | (a) the hypotheses of `goodred` for `S12`, `KC12`; (b) `dim_{F_p} ≤ 20316`, `≤ 4788` (upper bounds suffice: a set in the ideal with cofactors whose leading monomials leave that many standard monomials); (c), (d) disjoint boxes, each with a zero (Krawczyk ⇒ contraction ⇒ Banach) and the test margins | lean6_special |
| `thm:d88` (6.20) | `d88 : ∃ P88 ≠ 0, …` and `d94 : ∃ P94 ≠ 0, …` | `elim_integral` with the integrality of `goodred` and the empty fibre at `(μ₀, 1, 2)` (all zeros in the boxes by the dimension count and pigeonhole; none satisfies the torque relation by the tests) |
| `lem:d64type`, `lem:d64centre`, `lem:d64lead` (7.1–7.3) | leading data of 64 solve `E_4(m_K)` | none |
| `lem:E4` (7.6) | `E4 : sol of E_4(μ) → Π μ_k ≠ 0 → ∃ ε, common projective zero of F_ε ∨ ∃ σ, of G_σ` | none (hand) |
| `lem:E4cert` (7.7), `prop:E4` (7.8) | `E4_generic : ∃ h_E : MvPolynomial (Fin 4) ℤ, h_E ≠ 0 ∧ ∀ μ, aeval μ h_E ≠ 0 → no solution of E_4(μ)` | Macaulay transfer: a nonzero maximal minor of the degree-7 (resp. 8) Macaulay matrices of the 729 `F_ε` (64 `G_σ`) at `(3,5,7,11)` mod `p`, certified by an inverse matrix mod `p`; or the hand proof at `(1,1,1,1)` |
| `lem:d66type`, `lem:d66lead` (7.4, 7.5) | leading data of 66 solve `C_4` | none |
| `lem:C4cert` (7.9), `lem:transfer` (7.10), `prop:C4` (7.11) | `C4_generic : ∃ h_C ≠ 0, ∀ μ, aeval μ h_C ≠ 0 → μ_3 ≠ 0 → Z(μ) = ∅` | lean6_special: the 14 chart cofactor identities mod `p`; then homogenization, all monomials of bidegree `(N, N)` in the ideal mod `p`, a nonzero maximal minor (abstract, not computed) |
| `thm:d64`, `thm:d66` (7.12, 7.13) | `d64 : G.diagram = D64 → aeval (m_K) h_E = 0`; `d66 : … → aeval (m_{K∖o}, m_o) h_C = 0` | — |

### Part V — assembly (Section 8)

`F0 = Π_{cells with a core} h_c · P98 · P93(m₁,m₂,m₃) · P88 · P94 · h_E(m₃,…,m₆) · h_C(m₃,…,m₆)` and
`F = Π_{g ∈ S₆} F0 ∘ g` (`Finset.prod`; never expanded). `F ≠ 0` because `ℤ[m]` is a domain and relabelling
preserves nonzeroness. `no_germ`: a germ with `ell ≤ 0` is relabelled (and swapped) to a representative
(`enum_sound`), lies in a listed cell (`cells_sound`), and is excluded by `prop:exclusion` or by Part IV (for the
seven engine classes 124, 143, 127, 31, 132, 147, 133, with explicit relabellings to the labelling of Table 1).
`main` combines `exists_germ` and `no_germ`.

---

## 4. What carries over from the five-body formalization

`CC5Full` (`rung2/lean_full`) is written for `Fin 5`, ten pairs indexed by `Fin 10`, and the paper's `u, v, p`
slice coordinates. Decisions:

| CC5Full | decision | notes |
|---|---|---|
| `Statement` part of `System.lean` (`IsCC`, `Similar`, `FinitelyManyCC`) | generalized to `Fin n` | done (`Statement.lean`) |
| `Theory/CorU/Algebra.lean` (Noetherian primes, dimension one, zero loci) | copy, general `σ` | n-independent already |
| `Theory/CorU/{SlicePoint,Fibre,CorU}.lean`, `RealPos.lean` | redo for `Fin n` and the z-w-p variety | same arguments; sums over `univ.erase i` carry over |
| `Theory/FunctionField/*.lean` (≈2,070 lines) | generalize `Curve m` to `ACurve σ` (prime of dimension one in `MvPolynomial σ ℂ`, `Finite σ`) | the proofs are about the field `K = ℂ(C)`; only `curve_noether`, `trdeg_eq_one`, `finiteDimensional_of_transcendental` mention the coordinates |
| `Places.lean` (definitions), `Orders.lean`, `GermPlace.lean` | redo for `Fin n` with rotation weights `κ ∈ ℤ` | `tauEmb` copied |
| `ConstU.lean`, `PotentialDeriv.lean` | redo with the new identity `dU = −½ d(Σ m z w)` | simpler than Lemma 2.3 |
| `OrderCalc.lean`, `Types/Rules.lean`, `Types/Basic.lean` | port the arguments to `orderTop` on germs, `Fin n` | E1–E6, C1–C4 are the same rules; the five-body proofs are valuation arguments |
| `Types/Enum*.lean` (kernel-checked enumeration for five bodies) | not reused | the six-body enumeration is lean6's |
| `Expansion.lean` (formal model of `V_n`), `Germs.lean` (weighted germs, formal IFT), `Energy/`, `D*/`, `Core/` | not needed | the six-body proof has no energy identities, no formal IFT, no germ obstructions |

Estimate of reused lines: ≈ 4,000 (Part I); everything in Parts II–V is new.

---

## 5. Interfaces with the certificate projects

Neither `rung3/lean6/PLAN.md` nor `rung3/lean6_special/PLAN.md` existed when this plan was written (the projects
had a pilot module only). The statements below are what this proof consumes; they will be replaced by the exact
statements of the checkers' soundness lemmas once those are fixed, recorded here verbatim, and connected by bridge
lemmas in `CC6Full/Bridge/` (this project does not edit the sibling projects).

### lean6 (Sections 3–5)

1. **Diagrams.** A decidable predicate on labelled diagrams equal to the combinatorial parts of E1–E6, C1–C4
   (E3, E6 on kinds), the 191 representatives, and
   `∀ D, RulesComb D → ∃ (σ : Equiv.Perm (Fin 6)) (sw : Bool), D.act σ sw ∈ reps`.
   Bridge: their diagram encoding ↔ `Diagram 6`; their rules = `RulesComb` (proved equal, or proved implied by the
   rules at germs).
2. **Cells.** For each representative `D`, the list of cells, each with: the internal nodes of the two trees and
   their parent maps, the lowest common ancestor of each pair of `B = {1,…,6,O}` (or "same leaf"), the argmin sets
   of the 14 base identities. Soundness in the form: every exponent assignment `X` (ultrametrics `hz`, `hw` on `B`)
   satisfying Lemma 4.3 (a)–(c) for `D` with `ℓ ≤ 0` is realized by a listed cell (a strictly increasing height
   assignment on the cell's nodes reproduces `hz`, `hw`, and the argmin sets agree). Realization, not equality of
   canonical forms, so that no canonical labelling of trees is needed.
3. **Exclusion.** For each listed cell other than the 43: either an identity (by an explicit term list) whose term
   of least exponent is unique on all of `Π_c` (Farkas certificates), or a core: polynomials `f_i` given as initial
   forms of identities with argmin sets constant on `Π_c` (certificates), integer polynomial cofactors `g_i` and
   `h_c ∈ ℤ[m]` (or in five masses with one set to `1`), `h_c ≠ 0`, with `Σ g_i f_i = h_c` checked. Bridge: each
   identity of their term lists holds at every germ (a ring identity), and the exponent of a term is the linear form
   in the heights that their certificates use.

### lean6_special (Sections 6–7)

4. **`lem:dominant`** (if they do it): the disk bounds of the Lagrange and collinear factors of `S_μ` at
   `(1,2,40)`; else done here by `norm_num`.
5. **`lem:E4cert` / `prop:E4`**: for each of the 729 `ε` and 64 `σ`, row indices of a square submatrix of the
   Macaulay matrix at `(3,5,7,11)` and an inverse modulo `p` (entries in `ℤ[j]` sent to `𝔽_p` by
   `j ↦ 882503254`); or the hand proof at `(1,1,1,1)`.
6. **`lem:C4cert`**: the 14 chart cofactor identities modulo a prime `p` at `(3,5,7,11)`.
7. **`lem:d88comp`**: (a) for `S12` and `KC12` the initial patterns of `G` with `min w < 0` and for each a cofactor
   certificate `(Π ξ)^a = Σ c_g in(g)` mod `p`, plus a pruning certificate for all other patterns; (b) a set of
   polynomials in the ideal mod `p` (with cofactors) whose leading monomials leave ≤ 20,316 (≤ 4,788) standard
   monomials; (c), (d) the boxes, a contraction certificate per box (Krawczyk), pairwise disjointness, and the test
   margins on each box.

---

## 6. Hand proofs to formalize (by label)

Section 2: `lem:slice` (a), (b) [via Tom26 L. 2.1, 2.2], `lem:exchange` (germ form), `lem:U` (a)–(c), `cor:curve`,
`lem:place`, `lem:balance`, `cor:sum`, `lem:orders`, `lem:symm`, the identities of §2.3, `lem:initial`,
`lem:rules`.
Section 4: `lem:tree`, `lem:constraints`, `lem:farkas` (inside lean6's soundness).
Section 5: `lem:single`, `lem:core` (a), (b), the initial-system construction.
Section 6: `lem:common`, `lem:rewrite`, `lem:binary`, `thm:d89`, `lem:three`, `lem:d98type`, `lem:d98lead`,
`thm:d98`, `lem:dominant`, `thm:d93` (first statement and `P93 ≠ 0`), `lem:d88lead`, `lem:Ttest`, `lem:goodred`,
`thm:d88`.
Section 7: `lem:d64type`, `lem:d64centre`, `lem:d64lead`, `lem:d66type`, `lem:d66lead`, `lem:E4`, `lem:E4cert`
(or its computational replacement), `prop:E4`, `lem:transfer`, `prop:C4`, `thm:d64`, `thm:d66`.
Section 8: the proof of Theorem 1.1.

Not used by Theorem 1.1, not formalized: `thm:d90`, `prop:d82`, `prop:d81`, `rem:d89lead`, `rem:P98set`, §5.2
(`lem:clique` … `prop:cliquecount`), `rem:BEsums`, the factorization in `thm:d93`, the checks at `(1,2,7)` and the
second mass point of §7.2.

## 7. Where the Lean proof departs from the paper's proofs

* **Integral elimination instead of resultants and constructible sets.** `thm:d98`, `thm:d93` and `thm:d88` use
  one lemma: if the unknowns of a polynomial system over `ℚ[μ]` are integral over `ℚ[μ][1/g]` modulo the system
  and there is no complex solution at a rational `μ₀` with `g(μ₀) ≠ 0`, then some `h ∈ ℚ[μ]` with `h(μ₀) ≠ 0`
  vanishes wherever a solution exists and `g ≠ 0` (lying over at the maximal ideal of `μ₀`, the residue field
  embedded in `ℂ`). For 98 and 93 the integrality is that of the roots of `S_μ` (leading coefficient
  `(μ₁+μ₂)⁴`) and of the square roots `c_jl`; the polynomial `Φ` with 256 sign matrices and the resultants are
  not needed. For 88 and 94 it is `lem:goodred`, and the empty fibre at one point replaces the implicit function
  theorem, the continuity of the tests and the density of real points in the proof of `thm:d88`.
* **Macaulay transfer instead of projective elimination** in `prop:E4`, `prop:C4`: full column rank of a Macaulay
  matrix at `μ₀` gives a nonzero maximal minor `h(μ)`; where `h ≠ 0` all monomials of the degree are in the ideal,
  so there is no projective zero. `h` is never computed.
* **Valuations instead of DVRs** in `lem:goodred`: Mathlib has `LocalSubring.exists_le_valuationSubring`, not the
  domination of Noetherian local domains by discrete valuation rings; the value group may then be any ordered
  abelian group, the residues of `ξ_i / s(w_i)` use a section `s` on the free group generated by the `w_i`, and the
  pruning certificates are integer Farkas combinations, valid in every ordered abelian group.
* **Germs** for the symmetries and the identities (§2).

## 8. Effort and compute

Calibration: the five-body formalization took about 2.5 days of several agents in parallel for ≈ 66,000 lines of
theory and ≈ 220,000 lines in all.

| part | new Lean lines (estimate) | agent-days (one agent) | risk |
|---|---|---|---|
| I (port, generalize) | 5,000–6,000 | 3–4 | low |
| II (germ theory, trees, cells semantics, core lemma) | 5,000–7,000 | 4–6 | medium (the cell semantics must match lean6's) |
| III (bridges to lean6) | 1,000–3,000 | 1–3 | depends on lean6's encodings |
| IV: d89, d98, d93, `lem:three`, `elim_integral`, `lem:dominant` | 4,000–5,000 | 3–5 | low |
| IV: d64, d66, `lem:E4`, Macaulay transfers, homogenization | 3,000–4,000 | 3–4 | low–medium |
| IV: d88, d94, `lem:goodred`, Nakayama and point count, Krawczyk bridge | 4,000–6,000 | 5–8 | high (`goodred`; the certificate side of 6.19 (a), (b) is new work for lean6_special) |
| V | 500 | 1 | low |
| total | 23,000–31,000 | 20–31 | |

With three helpers in parallel on Parts I, II and IV, about 8–12 calendar days for this project's own proofs; the
end date of the full theorem is set by the certificate projects (computing the 2,413 core cofactors, the goodred
cone certificates and the dimension upper bounds).

Compute of this project: builds of the theory on one 384-core machine (a full rebuild of this project's own modules
is estimated at well under 1 CPU-hour per 10,000 lines); the `native_decide` checks owned here (the Macaulay inverses
for `E_4`: 729 matrices 120 × 120 and 64 matrices 45 × 45 mod `p`, and the `lem:dominant` bounds) take seconds to
minutes. The composed build of the main theorem imports the certificate modules of lean6 and lean6_special; its cost
is theirs (on the order of the five-body replay, hundreds of CPU-hours, to be measured).

## 9. Schedule (Pacific dates)

1. 2026-10-16/17 (day 0): this plan; `Statement.lean` (done); `Interface.lean` with every result above as a `Prop`
   and `main_of_interface`; start Part I (the variety, slice point, fibres, `exists_curve`).
2. Days 1–3: Part I to `exists_germ` (curves, places, expansions, balancing, `U` constant, `germ_of_place`).
3. Days 1–5 (in parallel): Part II (identities, `initial`, (O1)–(O6), rules, trees, constraints).
4. Days 4–8: cells semantics and core lemma; bridges to lean6 as its checkers land.
5. Days 3–9: Part IV d89, d98, d93, d64, d66 with their tools.
6. Days 6–15: d88, d94 (`goodred`, point count); with lean6_special's certificates.
7. As the parts land: `main` with `native_decide`; then the update requested by the author; then the kernel-only
   version (`decide +kernel` throughout).

Reports: `PROGRESS.md` (theorems proved, `sorry` count by file, build times), and a final report at the first
natural milestone or after about 24 hours.

## 10. Risks and open questions

* `lem:goodred` and the certificates of 6.19 (a), (b) are the long pole. The cone tests of the paper were run with
  saturation in Singular; Lean needs cofactor identities, which have to be computed.
* The cofactors of the 2,413 cores of `prop:exclusion` were never computed (the paper notes it); their size
  decides the cost of lean6's core checks.
* The cell semantics (trees with a body on the leaf of `O`, the base identities' terms, the node coordinates and the
  choice of the first child `c_0` at each node) must agree exactly with lean6's encoding; the bridge is where
  mismatches will show.
* The paper's `KC_{12}` and `S_{12}` eliminate `X_4, Y_4` with `1/μ_4` and `1/M`; the integrality statements are
  over `ℤ[μ, 1/μ_4, 1/M]_𝔪`.

---

## 11. Update of 2026-10-17, 12:30 UTC (05:30 Pacific)

Parts I, II, IV and V are proved (`PROGRESS.md`): Theorem 1.1 is reduced to `ClassesExcluded` (Sections 3–5) and
`SevenCerts` (the computations at one mass point of Sections 6 and 7), `Interface.lean`. The sibling plans exist now;
the interfaces recorded so far:

* `rung3/lean6` (PLAN.md of 05:20 UTC): checkers in Mathlib-free libraries, soundness in `L6Sound` with Mathlib, the
  framework "stated, not formalized". F1 soundness is in progress with permutations as `Equiv.Perm (Fin n)`
  (`L6Sound/F1/Complete.lean`, `mem_search`: every labelled diagram satisfying `okRules` is listed by `search n`;
  `Classes.lean`: orbits). F2 (cells) and F3, F4 (exclusions, cores) are not started; the core certificate format is
  fixed (`L6CERT 1`: `Σ cof_i gen_i = h` in `ℤ[m, x]`, `h` nonzero at `(3,5,7,11,13,17)`); `L6F34/Ident.lean` has
  term lists of the identities that differ from `CellIds.lean` only in the order of the terms and in dropping terms
  with a vanishing position. Bridge needed: their codes and `okRules` ↔ `Diagram` and the rules at germs; their cells ↔
  `TreeShape`, `Cell`, `Germ.LiesIn`; their term lists and initial forms ↔ `Identity`, `initForm`.
* `rung3/lean6_special` (PLAN.md of 05:10 UTC and its sources): `D98/Heavy.lean` (`heavy_roots`,
  `heavy_signed_sums`: the statements of `HeavyFact`, `HeavyFact3` with their `S`, `Lam`, which are the paper's
  formulas as here); `K4/C4/Final.lean` (`lemma_7_9 : NoZero [3,5,7,11] 32003 ∧ UnitIdeal …`, same equations and
  order as `D66Poly.lean`); `D88/Boxes/Final.lean` (`lemma_6_19_c`, `lemma_6_19_d`: disjoint balls with exactly one
  zero each and the test margins; `D88Sys.lean`, `D94Sys.lean` define the same systems with symbolic masses, the
  bridge being `rfl`); `D88/Trop/Hyp.lean` (`n4_torus_all`, `kc_torus_all : TorusEmpty …` for weights in ℚ).
  Requests sent: the tropical soundness for every ordered value group (or a reduction to rational weights here),
  the Macaulay determinant itself for `E4Cert`, `X_l ≠ 0` at the box zeros, and a certificate for Lemma 6.19(b),
  which their plan marks as later for S12 (Gröbner basis of 7,411 elements and 42.3 million terms).
* Found while proving: `Diagram.relabel` reproduces the diagram of the relabelled germ only for diagrams whose stored
  pairs are ordered (`Diagram.Ordered`, true for every diagram built by `ofLists` or `relabel`); the T-test hypothesis
  must include `X_l ≠ 0` (in Lean `‖0‖^(-1/2) = 0`).

Revised estimate. This project's remaining own work is the bridges: diagrams (1–2 days after lean6's F1 is final),
cells and exclusions (3–5 days after lean6's F2–F4 exist, the largest bridge), the certificates of Sections 6 and 7
(1–2 days), and either a reduction of `TropCert` to rational weights (2–3 days, Hahn embedding of finitely generated
ordered groups) or its generalization in the checker. The end date of the full theorem is set by lean6's F2–F4 and by
a certificate for Lemma 6.19(b).

## 12. Update of 2026-10-17, 17:20 UTC (10:20 Pacific): the composed theorem

`CC6Compose.main_of_dims : D88Dim → D94Dim → MainTheorem` (`Compose/CC6Compose/Final.lean`) proves Theorem 1.1 from the
two dimension bounds of Lemma 6.19(b), the only computations of the paper not yet checked in Lean. All other
statements of `SevenCerts'` and `ClassesExcluded` are proved from the theorems of the certificate projects, through
the bridges of `Compose/` (`PROGRESS.md` lists them). The composition was built against the working trees of `lean6`
(after its commit d593063) and `lean6_special` (after its commit ef35952) as of 2026-10-17, about 16:30 UTC.

Changes of route made while bridging:
* §7.2: the certificate project proves that the forms have no common nonzero zero at `(3, 5, 7, 11)`; the generic
  statement follows by the Nullstellensatz (all monomials of some degree in the ideal) and the Macaulay transfer
  (`d64_poly_of_noZero`), so the determinant itself is not needed.
* Lemma 6.18: `goodred_torus_opt` takes the torus form of the tropical certificates (no common zero of the initial
  forms in the torus of any field of characteristic `p`), which the certificate project proves for every ordered
  value group (`cover_soundG`).
* Proposition 5.3: the bridge uses the certificate project's specification checks (`L6F34S`), whose meaning is stated
  at every pair of exponent trees satisfying the conditions of Lemma 4.3, so the stored lines need not be parsed.

Remaining: Lemma 6.19(b) (`D88Dim`, `D94Dim`), a certificate of an upper bound of the dimension of the quotient
modulo `p` (polynomials of the ideal with cofactors whose leading monomials leave at most `20316`, resp. `4788`,
standard monomials); then the kernel-only version (`decide +kernel` in the certificate projects).

## 13. Update of 2026-10-17, 19:55 UTC (12:55 Pacific): the theorem without hypotheses

The certificate project `lean6_special` now proves Lemma 6.19(b) (`count_S12`, `count_KC`, at its commit ef35952:
Gröbner bases modulo `65521` computed in Lean by an F4 implementation run as compiled code, every element proved to
lie in the ideal). `Compose/CC6Compose/Dims.lean` bridges them to `D88Dim` and `D94Dim`: the rows of `S12` here are
those of the certificate project times units, and the quotient by the system `KC′` there (eleven unknowns, `Y₄`
eliminated) maps onto the quotient by `KC` here under `U_k ↦ Y_k − Y₄`. So `CC6Compose.main_theorem : MainTheorem`
(`Compose/CC6Compose/Theorem.lean`) has no hypotheses. Its axioms are `propext`, `Classical.choice`, `Quot.sound` and
the auxiliary axioms of `native_decide`. `check.sh` now scans all four packages, builds the composition and checks
these axioms; it passed on a fresh build from git archives of the release versions (this project at c29be82,
whose Lean sources are those of 3ca5293, `lean6` at d593063, `lean6_special` at ef35952), and also with `lean6` at
69a5dc7 (`PROGRESS.md`).

Next: the kernel-only version, in which the checks run by kernel evaluation (`decide +kernel`) instead of
`native_decide`. The bridges use the statements of the certificate projects' theorems, not their proofs, so they need
no change if those statements stay the same; `open_specials` (`Final.lean`) uses `native_decide` itself and must be
changed.

## 14. The kernel-only composition: interface and plan (2026-10-17, 21:30 UTC)

**Interface.** `Compose/tools/NativeInterface.lean` walks the proof of `main_theorem` (2,983 declarations of
`CC6Full` and `CC6Compose`) and lists the declarations of the certificate projects that it uses directly and that
depend on `native_decide`:
* `lean6`: `L6F1.F1_main`; `L6.F2S.Checks.f2s_cells_sound`; `L6.F34S.Checks.lines_ok`, `L6.F34S.Checks.open_ok`;
  the chunk theorems `L6.F34S.Checks.F34S_c<k>_k<j>` (123) and `L6.F34.Checks.certsOK_c<k>_k<j>` (120), used by
  `classClaim_c<k>` (`ExclusionClasses.lean`).
* `lean6_special`: `count_S12`, `count_KC`, `lemma_6_19_c`, `lemma_6_19_d`, `Comp.D88.Trop.n4_units_ok`,
  `Comp.D88.Trop.kc_units_ok`, `D88.Trop.n4_G_mem`, `D88.Trop.kc_G_mem`, `D88.Trop.n4_torus_gamma`,
  `D88.Trop.kc_torus_gamma`, `K4.C4.lemma_7_9`, `K4.C4.fact_prime_32003`, `K4.E4.check_3_5_7_11`.
* the composition itself: `open_specials` (`Final.lean`).

**What the bridges need from kernel versions.**
1. The bridges use the statements of these theorems, not their proofs. If the kernel versions keep the names and the
   statements, the composition builds unchanged against them, except for `open_specials` (item 3).
2. Proposition 5.3 needs, for each class, a finite list of certificate texts fixed before the germ: `DiagExcluded`
   asks for finitely many nonzero polynomials, and the germs of a class have infinitely many exponent trees with
   heights. The chunk theorems give these lists (`ClassClaim k n certs`). `f34s_excluded` and `f34s_excluded_of`,
   whose `ClaimMeaning` quantifies over all certificates, do not give them; a kernel version must keep the chunk
   statements or state the exclusion with the certificates drawn from explicit finite lists.
3. `open_specials`: `OpenKernel.lean` proves its statement by kernel evaluation (`open_specials_lit`, about 4 s) from
   the equation `L6F1.classes6 = classes6Lit` with the literal of `ClassesLit.lean` (`open_specials_of_eq`;
   `classes6_eq_of_parse` from `parseFile n6json = some (6, 82712, classes6Lit)`); all three use only the standard
   axioms. Evaluating the reading of `n6.json` in the kernel does not work: a prefix of 5 classes (833 bytes) passes
   in 28.7 s, prefixes of 20 and 60 classes fail within 3 s (also with larger stacks), the whole file fails after
   213 s at 47 GB. The equation has to come from the kernel version of F1, which needs the same reading
   (`F1_main` contains `parseFile n6json = some (6, 82712, classes6)`).

**Assembly.** When kernel versions of the listed theorems exist: point `Compose/lakefile.toml` at them, replace
`open_specials` in `hcells` by `open_specials_of_eq` with the equation of item 3, and let `check.sh` require that
`main_theorem` depends on `propext`, `Classical.choice` and `Quot.sound` only. If some kernel versions change names
or statements, the bridges take the native statements as hypotheses bundled in one proposition (`main_of_certs`, from
the standard axioms only) and small lemmas derive them from the kernel versions.

## 15. Version 3: the string-free interface and its assembly (2026-10-17, 23:00 UTC)

`Compose/CC6Compose/V3/`:
* `Interface.lean`: the statements on which the kernel-only proof rests, for a class list `L` given as data:
  `F1Cover L` (191 classes; every labelled diagram satisfying the rules is in the orbit of a representative),
  `FusedExclusion L` (for each class a finite list `cs` of certificates such that every pair satisfying `Cond` for
  the diagram of the class lies in a class with open cells or satisfies `ClaimMeaningIn cs`: `ClaimMeaning` with the
  certificate from `cs` and items `ItemOK`, whose argmin lists have no repetition), and `OpenCheck L`;
  `openCheck_lit : OpenCheck classes6Lit` by kernel evaluation.
* `Main.lean`: `main_of_v3 L (hF1 : F1Cover L) (hF : FusedExclusion L) (hO : OpenCheck L) (h7 : SevenCerts') :
  MainTheorem`, on the three standard axioms.
* `Native.lean`: the instances from the checks of version 2 for `classes6Lit` (`f1Cover_native`, `fused_native`; the
  class list equals the literal by one `native_decide`) and `main_theorem_v3_native`, whose axioms are the standard
  three and 3,158 auxiliary axioms, the same families as those of `main_theorem`, with `classes6_eq_lit` in place of
  `open_specials`.

The kernel-only theorem is `main_of_v3 L hF1 hF hO h7` with `L` a literal class list and
* `hF1`, `hF` from kernel versions in `lean6` (for `hF` the fused search in `lean6`, stated for the literal class
  list, with finitely many certificates per class and argmin lists without repetition);
* `hO := openCheck_lit` if `L = classes6Lit` (otherwise the same `decide +kernel` on `L`);
* `h7 := sevenCerts'_of d88Dim d94Dim`, with the theorems of `lean6_special` in kernel versions with the same
  statements.

Update (2026-10-18, 00:10 UTC). `V3/Special.lean`: `SpecialFacts`, the twelve statements of `lean6_special` that the
bridges use (each the type of the theorem that proves it), with the bridges of Sections 6 and 7 parameterized by them
(`d88Dim_of`, `d94Dim_of`, `d88Box_of`, `d94Box_of`, `e4NoZero_of`, `c4Cert_of`, `d88Int_of`, `d94Int_of`) and
`sevenCerts'_of_facts`; `main_of_facts L hF1 hF hO h : MainTheorem` (all of the consumed statements as hypotheses)
is on the three standard axioms, and `main_theorem_v3_native := main_of_facts classes6Lit … specialFacts_native` has the
axioms of `main_theorem`. The primality of `32003` used by the bridge of Lemma 7.9 is now proved by `norm_num`.
Decided on 2026-10-17: the kernel-only theorem uses the literal class list `classes6L` of `lean6`
(`L6CheckK.F1.F1_main_k` gives `F1Cover classes6L`, kernel-checked), its fused search for `FusedExclusion classes6L`
(target: certificates from one literal list of the 1,928 certificates, argmin lists without repetition), and kernel
versions of the theorems of `lean6_special` over the same constants (data as literals in `lean6_special` itself).

Update (2026-10-18, 02:35 UTC). `V3/Kernel.lean`: the instances of the string-free statements from the kernel
checks of the certificate project for its literal class list `L6CheckK.F1.classes6L` (`f1Cover_K` from
`L6CheckK.F1.F1_main_k`, `fused_K` from `L6CheckF.fusedK` with the certificates `L6CheckF.csAll`, `openCheck_K` by
`decide +kernel`) and `main_theorem_k_of (h : SpecialFacts) : MainTheorem`. Elaborated on the build machine of the
kernel checks against their modules (`lean6` 69a5dc7 with the kernel libraries, and the generated modules of the fused
search): `#print axioms CC6Compose.V3.main_theorem_k_of` gives `propext`, `Classical.choice`, `Quot.sound`. The
module is not imported by `CC6Compose.lean` until the kernel libraries are in the `lean6` that `Compose` requires.
What remains for the kernel-only theorem is `SpecialFacts` from kernel versions of the theorems of `lean6_special`.
