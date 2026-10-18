import CC6Full.Six.Systems
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# The four-body equilibria (Lemma 7.6, `lem:E4`)

§7.2 (`ss:E4`). For four masses `μ` with `μ₁μ₂μ₃μ₄ ≠ 0`, a solution of the system `E₄(μ)` (`IsE4`) gives a common
zero of one of the systems of forms

* `ℱ_ε = {q_j² A_k − q_k² A_j (j < k), Σ_k μ_k q_k³}`, with `A_k = Σ_{l≠k} ε_kl μ_l q_l`: seven cubic forms in
  `q ∈ ℂ⁴`, for each of the `3⁶` symmetric patterns `ε` of cube roots of unity;
* `𝒢_σ = {Σ_{l≠k} σ_kl μ_l Π_{j≠k,l} (ξ_k − ξ_j)² (k = 1, …, 4)}`: four quartic forms in `(ξ₂, ξ₃, ξ₄)`, with
  `ξ₁ = 0`, for each of the `2⁶` antisymmetric patterns `σ` of signs.

## Encoding

Bodies are numbered `0, 1, 2, 3` (body `k` of the paper is `k − 1`). The six pairs `k < l` are numbered
`0, …, 5` in lexicographic order (`E4.pr`, with inverse `E4.pidx`). A symmetric pattern of cube roots of unity is
`E4.eps e`, `ε_kl = j^{e_{kl}}` for `e : Fin 6 → ZMod 3` and `j = e^{2πi/3}` (`E4.jj`); an antisymmetric sign
pattern is `E4.sgn s` for `s : Fin 6 → Bool` (`σ_kl = 1` for `k < l` iff `s` is `true` on the pair `kl`). The forms
are polynomials: `E4.Fforms μ e : Fin 7 → MvPolynomial (Fin 4) ℂ` lists `q₀² A₁ − q₁² A₀, …, q₂² A₃ − q₃² A₂`
(the pairs in lexicographic order) and `Σ_k μ_k q_k³`; `E4.Gforms μ s : Fin 4 → MvPolynomial (Fin 3) ℂ` lists the
four quartic forms in the variables `X₀, X₁, X₂`, which stand for `ξ₂ − ξ₁, ξ₃ − ξ₁, ξ₄ − ξ₁` (`E4.Xi`).

## The proof (the paper's)

Let `L` be the matrix with `L_kl = μ_l P_kl³` for `k ≠ l` and zero row sums. The equations of `E₄` say
`L ξ = L η = 0`, and `L 𝟙 = 0`.

* If `𝟙, ξ, η` are linearly independent, the range of `L` has dimension at most one, so `L_kl = v_k w_l`. All
  `v_k, w_l` are nonzero, `Σ w_l = Σ w_l ξ_l = Σ w_l η_l = 0`, and the symmetry of `P` gives `P_kl³ = λ β_k β_l`
  with `β_k = w_k/μ_k`. With `q_k³ = β_k`, `ρ³ = λ` and `ε_kl = P_kl/(ρ q_k q_l)`, the identity
  `Σ_{l≠k} w_l (ξ_k − ξ_l)(η_k − η_l) = Σ_l w_l ξ_l η_l` (independent of `k`) and `(ξ_k − ξ_l)(η_k − η_l) = P_kl^{-2}`
  give `A_k = ρ² q_k² Σ_l w_l ξ_l η_l`, and `Σ_k μ_k q_k³ = Σ_k w_k = 0`. (The paper normalises `ρ = 1` with a
  square root; the forms are homogeneous, so the factor `ρ` changes nothing.)
* Otherwise `η = λξ + θ𝟙` with `λ ≠ 0`, `P_kl(ξ_k − ξ_l) = σ_kl κ` with `κ² = 1/λ` and `σ` antisymmetric, and
  `Π_{j≠k} (ξ_k − ξ_j)² Φ_k(ξ) = κ³ 𝒢_σ,k(ξ)`.

Main result: `CC6Full.lem_E4`.
-/

namespace CC6Full

open Finset MvPolynomial

noncomputable section

namespace E4

/-! ## Patterns and forms -/

/-- `j = e^{2πi/3}`. -/
def jj : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem jj_prim : IsPrimitiveRoot jj 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  norm_num at h
  exact h

/-- The six pairs `k < l` of `Fin 4`, in lexicographic order. -/
def pr : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The number of the pair `{k, l}` (junk `0` on the diagonal). -/
def pidx (k l : Fin 4) : Fin 6 :=
  (![![0, 0, 1, 2], ![0, 0, 3, 4], ![1, 3, 0, 5], ![2, 4, 5, 0]] : Fin 4 → Fin 4 → Fin 6) k l

theorem pidx_comm (k l : Fin 4) : pidx k l = pidx l k := by
  revert k l
  decide

theorem pr_pidx {k l : Fin 4} (h : k < l) : pr (pidx k l) = (k, l) := by
  revert k l
  decide

theorem pr_lt (i : Fin 6) : (pr i).1 < (pr i).2 := by
  revert i
  decide

/-- The symmetric pattern `ε_kl = j^{e_kl}` of cube roots of unity given by `e : Fin 6 → ZMod 3`. -/
def eps (e : Fin 6 → ZMod 3) (k l : Fin 4) : ℂ := jj ^ (e (pidx k l)).val

/-- The antisymmetric pattern of signs given by `s : Fin 6 → Bool`: for `k < l`, `σ_kl = 1` if `s` is `true` on the
pair `kl` and `σ_kl = −1` otherwise, and `σ_lk = −σ_kl` (`σ_kk = 0`). -/
def sgn (s : Fin 6 → Bool) (k l : Fin 4) : ℂ :=
  if k < l then (if s (pidx k l) then 1 else -1) else if l < k then (if s (pidx k l) then -1 else 1) else 0

/-- `A_k = Σ_{l ≠ k} ε_kl μ_l q_l`. -/
def Aform (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (k : Fin 4) : MvPolynomial (Fin 4) ℂ :=
  ∑ l ∈ univ.erase k, C (eps e k l * μ l) * X l

/-- `q_j² A_k − q_k² A_j`. -/
def Fpair (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (j k : Fin 4) : MvPolynomial (Fin 4) ℂ :=
  X j ^ 2 * Aform μ e k - X k ^ 2 * Aform μ e j

/-- `Σ_k μ_k q_k³`. -/
def Fcub (μ : Fin 4 → ℂ) : MvPolynomial (Fin 4) ℂ := ∑ k, C (μ k) * X k ^ 3

/-- The seven cubic forms `ℱ_ε` of Lemma 7.6 (`lem:E4`): the six forms `q_j² A_k − q_k² A_j`, `j < k`, in
lexicographic order, and `Σ_k μ_k q_k³`. -/
def Fforms (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) : Fin 7 → MvPolynomial (Fin 4) ℂ :=
  ![Fpair μ e 0 1, Fpair μ e 0 2, Fpair μ e 0 3, Fpair μ e 1 2, Fpair μ e 1 3, Fpair μ e 2 3, Fcub μ]

/-- The coordinates `(ξ₁, ξ₂, ξ₃, ξ₄) = (0, X₀, X₁, X₂)`. -/
def Xi : Fin 4 → MvPolynomial (Fin 3) ℂ := ![0, X 0, X 1, X 2]

/-- The four quartic forms `𝒢_σ` of Lemma 7.6 (`lem:E4`): `Σ_{l≠k} σ_kl μ_l Π_{j≠k,l} (ξ_k − ξ_j)²` with
`ξ = (0, X₀, X₁, X₂)`. -/
def Gforms (μ : Fin 4 → ℂ) (s : Fin 6 → Bool) (k : Fin 4) : MvPolynomial (Fin 3) ℂ :=
  ∑ l ∈ univ.erase k, C (sgn s k l * μ l) * ∏ j ∈ (univ.erase k).erase l, (Xi k - Xi j) ^ 2

/-! ## Evaluation -/

theorem eval_Aform (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (k : Fin 4) (q : Fin 4 → ℂ) :
    eval q (Aform μ e k) = ∑ l ∈ univ.erase k, eps e k l * μ l * q l := by
  simp [Aform, map_sum]

theorem eval_Fpair (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (j k : Fin 4) (q : Fin 4 → ℂ) :
    eval q (Fpair μ e j k) = q j ^ 2 * eval q (Aform μ e k) - q k ^ 2 * eval q (Aform μ e j) := by
  simp [Fpair]

theorem eval_Fcub (μ : Fin 4 → ℂ) (q : Fin 4 → ℂ) : eval q (Fcub μ) = ∑ k, μ k * q k ^ 3 := by
  simp [Fcub, map_sum]

theorem eval_Xi (y : Fin 3 → ℂ) (k : Fin 4) : eval y (Xi k) = (![0, y 0, y 1, y 2] : Fin 4 → ℂ) k := by
  fin_cases k <;> simp [Xi]

theorem eval_Gforms (μ : Fin 4 → ℂ) (s : Fin 6 → Bool) (k : Fin 4) (y : Fin 3 → ℂ) :
    eval y (Gforms μ s k) = ∑ l ∈ univ.erase k, sgn s k l * μ l * ∏ j ∈ (univ.erase k).erase l,
      ((![0, y 0, y 1, y 2] : Fin 4 → ℂ) k - (![0, y 0, y 1, y 2] : Fin 4 → ℂ) j) ^ 2 := by
  simp only [Gforms, map_sum, map_mul, map_prod, map_pow, map_sub, eval_C, eval_Xi]

/-! ## Linear algebra: a matrix killing three independent vectors has rank one -/

/-- If a `4 × 4` matrix `L` kills three linearly independent vectors, then `L_kl = v_k w_l` (its range has
dimension at most one, by rank-nullity). -/
theorem rank_one_of_ker {L : Fin 4 → Fin 4 → ℂ} {a b c : Fin 4 → ℂ}
    (hli : LinearIndependent ℂ ![a, b, c]) (ha : ∀ k, ∑ l, L k l * a l = 0) (hb : ∀ k, ∑ l, L k l * b l = 0)
    (hc : ∀ k, ∑ l, L k l * c l = 0) :
    ∃ v w : Fin 4 → ℂ, ∀ k l, L k l = v k * w l := by
  set f := Matrix.mulVecLin (Matrix.of L) with hf
  have hker : ∀ g : Fin 4 → ℂ, (∀ k, ∑ l, L k l * g l = 0) → g ∈ LinearMap.ker f := by
    intro g hg
    rw [LinearMap.mem_ker, hf, Matrix.mulVecLin_apply]
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    exact hg k
  have hspan : Submodule.span ℂ (Set.range ![a, b, c]) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hker a ha
    · exact hker b hb
    · exact hker c hc
  have h3 : Module.finrank ℂ (Submodule.span ℂ (Set.range ![a, b, c])) = 3 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hk3 : 3 ≤ Module.finrank ℂ (LinearMap.ker f) := h3 ▸ Submodule.finrank_mono hspan
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrn
  have hr : Module.finrank ℂ (LinearMap.range f) ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hr
  have hcol : ∀ l : Fin 4, ∃ t : ℂ, ∀ k, L k l = t * (v : Fin 4 → ℂ) k := by
    intro l
    obtain ⟨t, ht⟩ := hv ⟨f (Pi.single l 1), LinearMap.mem_range_self f _⟩
    refine ⟨t, fun k => ?_⟩
    have h2 := congrArg (fun u : LinearMap.range f => (u : Fin 4 → ℂ) k) ht
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, f, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, Matrix.col_apply, Matrix.of_apply] at h2
    exact h2.symm
  choose t ht using hcol
  exact ⟨fun k => (v : Fin 4 → ℂ) k, t, fun k l => by rw [ht l k, mul_comm]⟩

/-! ## The system `E₄` -/

theorem sgn_pow_three (s : Fin 6 → Bool) (k l : Fin 4) : sgn s k l ^ 3 = sgn s k l := by
  unfold sgn
  split_ifs <;> norm_num

/-- The nonvanishing facts of a solution of `E₄`: `ξ_k ≠ ξ_l`, `η_k ≠ η_l` and `P_kl ≠ 0` for `k ≠ l`. -/
theorem isE4_ne {μ : Fin 4 → ℂ} {ξ η : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ} (h : IsE4 μ ξ η P)
    {k l : Fin 4} (hkl : k ≠ l) : ξ k - ξ l ≠ 0 ∧ η k - η l ≠ 0 ∧ P k l ≠ 0 := by
  have d := h.2.2.2 k l hkl
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩ <;> simp [h0] at d

/-- The matrix `L` of the proof of Lemma 7.6: `L_kl = μ_l P_kl³` for `k ≠ l`, with zero row sums. -/
def Lmat (μ : Fin 4 → ℂ) (P : Fin 4 → Fin 4 → ℂ) (k l : Fin 4) : ℂ :=
  if k = l then -∑ l' ∈ univ.erase k, μ l' * P k l' ^ 3 else μ l * P k l ^ 3

theorem Lmat_sum (μ : Fin 4 → ℂ) (P : Fin 4 → Fin 4 → ℂ) (h : Fin 4 → ℂ) (k : Fin 4) :
    ∑ l, Lmat μ P k l * h l = -force μ P h k := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have e2 : ∑ l ∈ univ.erase k, Lmat μ P k l * h l = ∑ l ∈ univ.erase k, μ l * P k l ^ 3 * h l :=
    Finset.sum_congr rfl fun l hl => by
      have hkl : k ≠ l := (Finset.ne_of_mem_erase hl).symm
      simp only [Lmat, hkl, ↓reduceIte]
  have e3 : Lmat μ P k k = -∑ l' ∈ univ.erase k, μ l' * P k l' ^ 3 := by simp [Lmat]
  rw [e2, e3]
  simp only [force, neg_mul, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The case `dim V = 2` of the proof of Lemma 7.6: `η = λξ + θ𝟙` gives a common zero of some `𝒢_σ`. -/
theorem caseB {μ : Fin 4 → ℂ} {ξ η : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ} (h : IsE4 μ ξ η P)
    {lam θ : ℂ} (hη : ∀ k, η k = lam * ξ k + θ) :
    ∃ s : Fin 6 → Bool, ∃ y : Fin 3 → ℂ, y ≠ 0 ∧ ∀ k, eval y (Gforms μ s k) = 0 := by
  have hlam : lam ≠ 0 := by
    intro h0
    have := (isE4_ne h (show (0 : Fin 4) ≠ 1 by decide)).2.1
    rw [hη 0, hη 1, h0] at this
    simp at this
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq lam⁻¹ (by norm_num : 0 < 2)
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hκ
    exact inv_ne_zero hlam hκ.symm
  have hsq : ∀ k l, k ≠ l → (P k l * (ξ k - ξ l)) ^ 2 = κ ^ 2 := by
    intro k l hkl
    have d := h.2.2.2 k l hkl
    rw [hη k, hη l] at d
    rw [hκ]
    apply eq_inv_of_mul_eq_one_left
    linear_combination d
  have hpm : ∀ k l, k ≠ l → P k l * (ξ k - ξ l) = κ ∨ P k l * (ξ k - ξ l) = -κ := fun k l hkl =>
    sq_eq_sq_iff_eq_or_eq_neg.mp (hsq k l hkl)
  obtain ⟨s, hs⟩ : ∃ s : Fin 6 → Bool,
      s = fun i => decide (P (pr i).1 (pr i).2 * (ξ (pr i).1 - ξ (pr i).2) = κ) := ⟨_, rfl⟩
  have hsgn : ∀ k l, k < l → P k l * (ξ k - ξ l) = sgn s k l * κ := by
    intro k l hlt
    have hp := pr_pidx hlt
    have hsi : s (pidx k l) = decide (P k l * (ξ k - ξ l) = κ) := by rw [hs]; simp only [hp]
    simp only [sgn, hlt, ↓reduceIte, hsi]
    by_cases hc : P k l * (ξ k - ξ l) = κ
    · simp [hc]
    · simp only [hc, decide_false]
      rcases hpm k l hlt.ne with h1 | h1
      · exact absurd h1 hc
      · rw [h1]; simp
  have hsg : ∀ k l, k ≠ l → P k l * (ξ k - ξ l) = sgn s k l * κ := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with hlt | hlt
    · exact hsgn k l hlt
    · have h1 := hsgn l k hlt
      have h2 : sgn s k l = -sgn s l k := by
        simp only [sgn, hlt, not_lt.mpr hlt.le, ↓reduceIte, pidx_comm k l]
        split_ifs <;> norm_num
      rw [h2, h.1 k l]
      linear_combination -h1
  refine ⟨s, fun i => ξ i.succ - ξ 0, ?_, fun k => ?_⟩
  · intro h0
    have h1 := congrFun h0 0
    simp only [Pi.zero_apply] at h1
    exact (isE4_ne h (show (1 : Fin 4) ≠ 0 by decide)).1 h1
  · rw [eval_Gforms]
    have hy : ∀ j : Fin 4, (![0, ξ (Fin.succ 0) - ξ 0, ξ (Fin.succ 1) - ξ 0, ξ (Fin.succ 2) - ξ 0] :
        Fin 4 → ℂ) j = ξ j - ξ 0 := by
      intro j
      fin_cases j <;> simp
    simp only [hy, sub_sub_sub_cancel_right]
    have key : κ ^ 3 * (∑ l ∈ univ.erase k, sgn s k l * μ l * ∏ j ∈ (univ.erase k).erase l, (ξ k - ξ j) ^ 2) =
        (∏ j ∈ univ.erase k, (ξ k - ξ j) ^ 2) * force μ P ξ k := by
      rw [force, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hlk : k ≠ l := (Finset.ne_of_mem_erase hl).symm
      rw [← Finset.mul_prod_erase (univ.erase k) (fun j => (ξ k - ξ j) ^ 2) hl]
      have h1 := hsg k l hlk
      have h3 := sgn_pow_three s k l
      linear_combination (-(∏ j ∈ (univ.erase k).erase l, (ξ k - ξ j) ^ 2) * μ l *
          ((P k l * (ξ k - ξ l)) ^ 2 + P k l * (ξ k - ξ l) * (sgn s k l * κ) + (sgn s k l * κ) ^ 2)) * h1 +
        (-(∏ j ∈ (univ.erase k).erase l, (ξ k - ξ j) ^ 2) * μ l * κ ^ 3) * h3
    rw [h.2.1 k, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 3 hκ0)

/-- The case `dim V = 3` of the proof of Lemma 7.6: if `𝟙, ξ, η` are linearly independent, some `ℱ_ε` has a common
zero `q ≠ 0`. -/
theorem caseA {μ : Fin 4 → ℂ} (hμ : ∀ k, μ k ≠ 0) {ξ η : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ}
    (h : IsE4 μ ξ η P) (hli : LinearIndependent ℂ ![fun _ => (1 : ℂ), ξ, η]) :
    ∃ e : Fin 6 → ZMod 3, ∃ q : Fin 4 → ℂ, q ≠ 0 ∧ ∀ i, eval q (Fforms μ e i) = 0 := by
  have hL : ∀ g : Fin 4 → ℂ, (∀ k, force μ P g k = 0) → ∀ k, ∑ l, Lmat μ P k l * g l = 0 := by
    intro g hg k
    rw [Lmat_sum, hg k, neg_zero]
  have h1 : ∀ k, force μ P (fun _ => (1 : ℂ)) k = 0 := by
    intro k
    simp [force]
  obtain ⟨v, w, hvw⟩ := rank_one_of_ker hli (hL _ h1) (hL _ h.2.1) (hL _ h.2.2.1)
  have hoff : ∀ k l, k ≠ l → v k * w l = μ l * P k l ^ 3 := by
    intro k l hkl
    rw [← hvw]
    simp [Lmat, hkl]
  have hPne : ∀ k l, k ≠ l → P k l ≠ 0 := fun k l hkl => (isE4_ne h hkl).2.2
  have hother : ∀ k : Fin 4, ∃ l, k ≠ l := by
    intro k
    by_cases hk : k = 0
    · exact ⟨1, by rw [hk]; decide⟩
    · exact ⟨0, hk⟩
  have hv : ∀ k, v k ≠ 0 := by
    intro k h0
    obtain ⟨l, hl⟩ := hother k
    have := hoff k l hl
    rw [h0, zero_mul] at this
    exact mul_ne_zero (hμ l) (pow_ne_zero 3 (hPne k l hl)) this.symm
  have hw : ∀ l, w l ≠ 0 := by
    intro l h0
    obtain ⟨k, hk⟩ := hother l
    have := hoff k l (Ne.symm hk)
    rw [h0, mul_zero] at this
    exact mul_ne_zero (hμ l) (pow_ne_zero 3 (hPne k l (Ne.symm hk))) this.symm
  have hsum : ∀ g : Fin 4 → ℂ, (∀ k, force μ P g k = 0) → ∑ l, w l * g l = 0 := by
    intro g hg
    have h0 := hL g hg 0
    simp only [hvw] at h0
    have h2 : v 0 * ∑ l, w l * g l = 0 := by
      rw [Finset.mul_sum, ← h0]
      exact Finset.sum_congr rfl fun l _ => by ring
    exact (mul_eq_zero.mp h2).resolve_left (hv 0)
  have hw1 : ∑ l, w l = 0 := by simpa using hsum _ h1
  have hwξ : ∑ l, w l * ξ l = 0 := hsum _ h.2.1
  have hwη : ∑ l, w l * η l = 0 := hsum _ h.2.2.1
  obtain ⟨β, hβ⟩ : ∃ β : Fin 4 → ℂ, ∀ k, β k = w k / μ k := ⟨_, fun _ => rfl⟩
  have hβ0 : ∀ k, β k ≠ 0 := fun k => by rw [hβ]; exact div_ne_zero (hw k) (hμ k)
  have hP3 : ∀ k l, k ≠ l → P k l ^ 3 = v k * β l := by
    intro k l hkl
    rw [hβ l, mul_div_assoc', eq_div_iff (hμ l)]
    linear_combination -hoff k l hkl
  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ, lam = v 0 / β 0 := ⟨_, rfl⟩
  have hvlam : ∀ k, v k = lam * β k := by
    intro k
    rw [hlam, div_mul_eq_mul_div, eq_div_iff (hβ0 0)]
    by_cases hk : k = 0
    · rw [hk]
    · have e1 := hP3 k 0 hk
      have e2 := hP3 0 k (Ne.symm hk)
      rw [h.1 k 0] at e1
      linear_combination e2 - e1
  have hlam0 : lam ≠ 0 := by rw [hlam]; exact div_ne_zero (hv 0) (hβ0 0)
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq lam (by norm_num : 0 < 3)
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hρ
    exact hlam0 hρ.symm
  choose q hq using fun k => IsAlgClosed.exists_pow_nat_eq (β k) (by norm_num : 0 < 3)
  have hq0 : ∀ k, q k ≠ 0 := by
    intro k h0
    have := hq k
    rw [h0, zero_pow (by norm_num)] at this
    exact hβ0 k this.symm
  obtain ⟨ε, hε⟩ : ∃ ε : Fin 4 → Fin 4 → ℂ, ∀ k l, ε k l = P k l / (ρ * q k * q l) :=
    ⟨_, fun _ _ => rfl⟩
  have hε3 : ∀ k l, k ≠ l → ε k l ^ 3 = 1 := by
    intro k l hkl
    rw [hε, div_pow, mul_pow, mul_pow, hρ, hq k, hq l, hP3 k l hkl, hvlam k]
    exact div_self (mul_ne_zero (mul_ne_zero hlam0 (hβ0 k)) (hβ0 l))
  have hεsymm : ∀ k l, ε k l = ε l k := by
    intro k l
    rw [hε, hε, h.1 k l]
    ring
  have hPε : ∀ k l, P k l = ε k l * ρ * q k * q l := by
    intro k l
    rw [hε]
    field_simp [hρ0, hq0 k, hq0 l]
  have hex : ∀ i : Fin 6, ∃ n : ℕ, n < 3 ∧ jj ^ n = ε (pr i).1 (pr i).2 := fun i =>
    jj_prim.eq_pow_of_pow_eq_one (hε3 _ _ (pr_lt i).ne)
  choose n hn3 hn using hex
  refine ⟨fun i => (n i : ZMod 3), q, fun h0 => hq0 0 (congrFun h0 0), ?_⟩
  have heps : ∀ k l, k ≠ l → eps (fun i => (n i : ZMod 3)) k l = ε k l := by
    intro k l hkl
    simp only [eps, ZMod.val_natCast, Nat.mod_eq_of_lt (hn3 _)]
    rw [hn]
    rcases lt_or_gt_of_ne hkl with hlt | hlt
    · rw [pr_pidx hlt]
    · rw [pidx_comm, pr_pidx hlt, hεsymm]
  obtain ⟨S, hS⟩ : ∃ S : ℂ, S = ∑ l, w l * (ξ l * η l) := ⟨_, rfl⟩
  have hA : ∀ k, eval q (Aform μ (fun i => (n i : ZMod 3)) k) = ρ ^ 2 * q k ^ 2 * S := by
    intro k
    rw [eval_Aform]
    have hd : ∑ l ∈ univ.erase k, w l * ((ξ k - ξ l) * (η k - η l)) = S := by
      rw [Finset.sum_erase _ (by simp), hS]
      have e : ∀ l, w l * ((ξ k - ξ l) * (η k - η l)) =
          ξ k * η k * w l - ξ k * (w l * η l) - η k * (w l * ξ l) + w l * (ξ l * η l) := fun l => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, hwξ, hwη]
      ring
    rw [← hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hkl : k ≠ l := (Finset.ne_of_mem_erase hl).symm
    rw [heps k l hkl]
    have hdist := h.2.2.2 k l hkl
    have hwl : w l = μ l * q l ^ 3 := by
      rw [hq l, hβ l]
      field_simp [hμ l]
    rw [hwl]
    linear_combination (-(ε k l) * μ l * q l) * hdist +
      (μ l * q l * ((ξ k - ξ l) * (η k - η l)) * ε k l * (P k l + ε k l * ρ * q k * q l)) * hPε k l +
      (μ l * q l * ((ξ k - ξ l) * (η k - η l)) * (ρ * q k * q l) ^ 2) * hε3 k l hkl
  have hpair : ∀ j k, eval q (Fpair μ (fun i => (n i : ZMod 3)) j k) = 0 := by
    intro j k
    rw [eval_Fpair, hA, hA]
    ring
  have hcub : eval q (Fcub μ) = 0 := by
    rw [eval_Fcub, ← hw1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hq k, hβ k]
    field_simp [hμ k]
  intro i
  fin_cases i <;> simp [Fforms, hpair, hcub]

end E4

/-- **Lemma 7.6** (`lem:E4`). Let `μ₁μ₂μ₃μ₄ ≠ 0`. If `E₄(μ)` has a solution, then for some symmetric pattern `ε` of
cube roots of unity (`E4.eps e`, `e : Fin 6 → ZMod 3`) the seven cubic forms `ℱ_ε` (`E4.Fforms μ e`) have a common
zero `q ≠ 0` in `ℂ⁴`, or for some antisymmetric pattern `σ` of signs (`E4.sgn s`, `s : Fin 6 → Bool`) the four
quartic forms `𝒢_σ` (`E4.Gforms μ s`) have a common zero `(ξ₂, ξ₃, ξ₄) ≠ 0` (with `ξ₁ = 0`). -/
theorem lem_E4 {μ : Fin 4 → ℂ} (hμ : μ 0 * μ 1 * μ 2 * μ 3 ≠ 0) {ξ η : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ}
    (h : IsE4 μ ξ η P) :
    (∃ e : Fin 6 → ZMod 3, ∃ q : Fin 4 → ℂ, q ≠ 0 ∧ ∀ i, eval q (E4.Fforms μ e i) = 0) ∨
      ∃ s : Fin 6 → Bool, ∃ y : Fin 3 → ℂ, y ≠ 0 ∧ ∀ k, eval y (E4.Gforms μ s k) = 0 := by
  have hμ' : ∀ k, μ k ≠ 0 := by
    intro k
    simp only [mul_ne_zero_iff] at hμ
    fin_cases k
    · exact hμ.1.1.1
    · exact hμ.1.1.2
    · exact hμ.1.2
    · exact hμ.2
  by_cases hB : ∃ lam θ : ℂ, ∀ k, η k = lam * ξ k + θ
  · obtain ⟨lam, θ, hη⟩ := hB
    exact Or.inr (E4.caseB h hη)
  · left
    refine E4.caseA hμ' h ?_
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hk : ∀ k, g 0 + g 1 * ξ k + g 2 * η k = 0 := by
      intro k
      have h0 := congrFun hg k
      simp [Fin.sum_univ_three] at h0
      linear_combination h0
    have hg2 : g 2 = 0 := by
      by_contra h2
      refine hB ⟨-g 1 / g 2, -g 0 / g 2, fun k => ?_⟩
      rw [div_mul_eq_mul_div, ← add_div, eq_div_iff h2]
      linear_combination hk k
    have hg1 : g 1 = 0 := by
      have h0 := hk 0
      have h1 := hk 1
      rw [hg2] at h0 h1
      have hne := (E4.isE4_ne h (show (0 : Fin 4) ≠ 1 by decide)).1
      have h3 : g 1 * (ξ 0 - ξ 1) = 0 := by linear_combination h0 - h1
      exact (mul_eq_zero.mp h3).resolve_right hne
    have hg0 : g 0 = 0 := by
      have h0 := hk 0
      rw [hg1, hg2] at h0
      simpa using h0
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2

end

end CC6Full
