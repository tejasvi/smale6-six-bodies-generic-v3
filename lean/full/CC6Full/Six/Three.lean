import CC6Full.Six.ThreeDefs
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex central configurations of three bodies (Lemma 6.9, `lem:three`)

§6.4 (`ss:three`). Let `μ = (μ₁, μ₂, μ₃)` with `μ_k ≠ 0` and `M_μ = μ₁ + μ₂ + μ₃ ≠ 0`, and let `(z, w, p)` be a
solution of the system `N(μ)` (`IsNSys μ z w p` for `N = 3`):
`z_k = Σ_{l≠k} μ_l p_kl³ (z_k − z_l)`, the same in `w`, and `p_kl² (z_k − z_l)(w_k − w_l) = 1`.

* `three_dichotomy`: the solution is of Lagrange type, `p_kl³ = 1/M_μ` for all pairs, or of collinear type,
  `w = λ z` with `λ ≠ 0`;
* `three_shape`: with `s = z₁ − z₂` (nonzero) and the shape `τ = (z₁ − z₃)/s`, the positions are
  `z_k/s = ℓ_k(τ)/M_μ`, and `τ` is a root of `S_μ`.

The polynomials `ℓ_k`, `S_μ` are those of `CC6Full.Six.ThreeDefs`. Bodies are numbered `0, 1, 2` (body `k` of the
paper is `k − 1`).

## The proof (the paper's)

Let `L` be the matrix with `L_kl = μ_l p_kl³` for `k ≠ l` and zero row sums (`Lmat`, `Lmat_row_sum`). The equations
say `(L + I) z = (L + I) w = 0` (`Lmat_mulVec`), and `μᵀ L = 0` (`vecMul_Lmat`), so `z` and `w` lie in the plane
`H = {v : Σ μ_k v_k = 0}` (`dot_eq_zero_of_mulVec`). If `z` and `w` are independent (in coordinates: the determinant
`(z₁ − z₂)(w₁ − w₃) − (w₁ − w₂)(z₁ − z₃)` of their differences is nonzero), `L + I` vanishes on `H`, so each row `r`
of `L + I`, which has `Σ_l r_l = 1`, agrees with `μᵀ/M_μ` in the columns `2, 3` (`row_of_indep`), and the
off-diagonal entries give `p_kl³ = 1/M_μ`. Otherwise `w = λ z`, since `z ≠ 0`.

In the Lagrange case, with `R_kl = p_kl^{-2}`, `z₁₂ = s`, `z₁₃ = τ s`, the distance equation of `23` becomes
`R₁₂ τ² − (R₁₂ + R₁₃ − R₂₃) τ + R₁₃ = 0`, that is `τ² − (1 + j^b − j^c) τ + j^b = 0` for some `(b, c)`
(`lagrange_shape`), and `lagQuad_root` finishes. In the collinear case `p_kl = σ_kl κ / z_kl` with `κ² = 1/λ` and
`σ` an antisymmetric sign pattern, so `z_k = κ³ F_k`, and `z₁₂ = s`, `z₂₃ = x s` give `x(F₁ − F₂) = F₂ − F₃`,
the vanishing of `Q_σ(x)` with `x = τ − 1` (`collinear_Q`, `collinear_shape`); `Qσ_classes` finishes.
-/

namespace CC6Full.Six

open Polynomial Finset Matrix

noncomputable section

/-! ## Three bodies -/

/-- The force as a sum over all three bodies (the term `l = k` vanishes). -/
theorem force_eq_sum_three (μ : Fin 3 → ℂ) (p : Fin 3 → Fin 3 → ℂ) (h : Fin 3 → ℂ) (k : Fin 3) :
    force μ p h k = ∑ l, μ l * p k l ^ 3 * (h k - h l) :=
  Finset.sum_erase _ (by simp)

theorem force_zero_eq (μ : Fin 3 → ℂ) (p : Fin 3 → Fin 3 → ℂ) (h : Fin 3 → ℂ) :
    force μ p h 0 = μ 1 * p 0 1 ^ 3 * (h 0 - h 1) + μ 2 * p 0 2 ^ 3 * (h 0 - h 2) := by
  rw [force_eq_sum_three, Fin.sum_univ_three]
  ring

theorem force_one_eq (μ : Fin 3 → ℂ) {p : Fin 3 → Fin 3 → ℂ} (hp : IsSymm p) (h : Fin 3 → ℂ) :
    force μ p h 1 = μ 0 * p 0 1 ^ 3 * (h 1 - h 0) + μ 2 * p 1 2 ^ 3 * (h 1 - h 2) := by
  rw [force_eq_sum_three, Fin.sum_univ_three, hp 1 0]
  ring

theorem force_two_eq (μ : Fin 3 → ℂ) {p : Fin 3 → Fin 3 → ℂ} (hp : IsSymm p) (h : Fin 3 → ℂ) :
    force μ p h 2 = μ 0 * p 0 2 ^ 3 * (h 2 - h 0) + μ 1 * p 1 2 ^ 3 * (h 2 - h 1) := by
  rw [force_eq_sum_three, Fin.sum_univ_three, hp 2 0, hp 2 1]
  ring

/-- The distance equations force `p_kl ≠ 0`, `z_k ≠ z_l` and `w_k ≠ w_l` for `k ≠ l`. -/
theorem distEqs_ne {N : ℕ} {p : Fin N → Fin N → ℂ} {z w : Fin N → ℂ} (hd : DistEqs p z w) {k l : Fin N}
    (hkl : k ≠ l) : p k l ≠ 0 ∧ z k - z l ≠ 0 ∧ w k - w l ≠ 0 := by
  have h := hd k l hkl
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩ <;> rw [h0] at h <;> simp at h

/-! ## The matrix `L` -/

/-- The matrix `L` of the proof of Lemma 6.9: `L_kl = μ_l p_kl³` for `k ≠ l`, with zero row sums. -/
def Lmat (μ : Fin 3 → ℂ) (p : Fin 3 → Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun k l => if k = l then -∑ l' ∈ univ.erase k, μ l' * p k l' ^ 3 else μ l * p k l ^ 3

/-- The rows of `L` sum to zero. -/
theorem Lmat_row_sum (μ : Fin 3 → ℂ) (p : Fin 3 → Fin 3 → ℂ) (k : Fin 3) : ∑ l, Lmat μ p k l = 0 := by
  have h : ∀ l ∈ univ.erase k, Lmat μ p k l = μ l * p k l ^ 3 := fun l hl => by
    simp only [Lmat, Matrix.of_apply, (Finset.ne_of_mem_erase hl).symm, ↓reduceIte]
  rw [← Finset.add_sum_erase _ _ (mem_univ k), Finset.sum_congr rfl h]
  simp only [Lmat, Matrix.of_apply, ↓reduceIte]
  ring

/-- `((L + I) h)_k = h_k − Φ_k(h)`: the equations of `N(μ)` say `(L + I) z = (L + I) w = 0` (Lemma 6.9). -/
theorem Lmat_mulVec (μ : Fin 3 → ℂ) (p : Fin 3 → Fin 3 → ℂ) (h : Fin 3 → ℂ) (k : Fin 3) :
    ((Lmat μ p + 1) *ᵥ h) k = h k - force μ p h k := by
  rw [force_eq_sum_three]
  rcases fin3_cases k with rfl | rfl | rfl <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Lmat, Matrix.one_apply, sum_erase_eq_sub] <;> ring

/-- `μᵀ L = 0` for symmetric `p` (Lemma 6.9). -/
theorem vecMul_Lmat {μ : Fin 3 → ℂ} {p : Fin 3 → Fin 3 → ℂ} (hp : IsSymm p) : μ ᵥ* Lmat μ p = 0 := by
  funext l
  rcases fin3_cases l with rfl | rfl | rfl <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Lmat, sum_erase_eq_sub, hp 1 0, hp 2 0, hp 2 1] <;>
    ring

/-- A solution of `(L + I) h = 0` lies in the plane `H = {v : Σ μ_k v_k = 0}`. -/
theorem dot_eq_zero_of_mulVec {μ : Fin 3 → ℂ} {p : Fin 3 → Fin 3 → ℂ} (hp : IsSymm p) {h : Fin 3 → ℂ}
    (hL : (Lmat μ p + 1) *ᵥ h = 0) : μ ⬝ᵥ h = 0 := by
  have e := congrArg (fun v => μ ⬝ᵥ v) hL
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_add, vecMul_Lmat hp, Matrix.vecMul_one, zero_add,
    dotProduct_zero] at e
  exact e

/-- If `z, w ∈ H` are independent, a row `r` of a matrix `A` with `Σ_l r_l = 1` and `r · z = r · w = 0` is `μᵀ/M_μ`
in the columns `2, 3` (Lemma 6.9: `L + I` vanishes on `H`, so `L + I = 𝟙 μᵀ / M_μ`). -/
theorem row_of_indep {μ z w : Fin 3 → ℂ} {A : Matrix (Fin 3) (Fin 3) ℂ} {k : Fin 3} (hr : ∑ l, A k l = 1)
    (hAz : (A *ᵥ z) k = 0) (hAw : (A *ᵥ w) k = 0) (hz : μ ⬝ᵥ z = 0) (hw : μ ⬝ᵥ w = 0)
    (hD : (z 0 - z 1) * (w 0 - w 2) - (w 0 - w 1) * (z 0 - z 2) ≠ 0) :
    μ 1 = Mμ μ * A k 1 ∧ μ 2 = Mμ μ * A k 2 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hr hAz hAw hz hw
  have e1 : (μ 1 - Mμ μ * A k 1) * (z 0 - z 1) + (μ 2 - Mμ μ * A k 2) * (z 0 - z 2) = 0 := by
    simp only [Mμ]
    linear_combination (μ 0 + μ 1 + μ 2) * hAz - hz - (μ 0 + μ 1 + μ 2) * z 0 * hr
  have e2 : (μ 1 - Mμ μ * A k 1) * (w 0 - w 1) + (μ 2 - Mμ μ * A k 2) * (w 0 - w 2) = 0 := by
    simp only [Mμ]
    linear_combination (μ 0 + μ 1 + μ 2) * hAw - hw - (μ 0 + μ 1 + μ 2) * w 0 * hr
  have h1 : (μ 1 - Mμ μ * A k 1) * ((z 0 - z 1) * (w 0 - w 2) - (w 0 - w 1) * (z 0 - z 2)) = 0 := by
    linear_combination (w 0 - w 2) * e1 - (z 0 - z 2) * e2
  have h2 : (μ 2 - Mμ μ * A k 2) * ((z 0 - z 1) * (w 0 - w 2) - (w 0 - w 1) * (z 0 - z 2)) = 0 := by
    linear_combination (z 0 - z 1) * e2 - (w 0 - w 1) * e1
  exact ⟨by linear_combination (mul_eq_zero.1 h1).resolve_right hD,
    by linear_combination (mul_eq_zero.1 h2).resolve_right hD⟩

/-! ## The dichotomy -/

/-- **Lemma 6.9** (`lem:three`), first part: for `μ_k ≠ 0` and `M_μ ≠ 0`, every solution of `N(μ)` is of Lagrange
type, `p_kl³ = 1/M_μ` for all pairs, or of collinear type, `w = λ z` with `λ ≠ 0`. -/
theorem three_dichotomy {μ : Fin 3 → ℂ} (hμ : ∀ k, μ k ≠ 0) (hM : Mμ μ ≠ 0) {z w : Fin 3 → ℂ}
    {p : Fin 3 → Fin 3 → ℂ} (h : IsNSys μ z w p) :
    (∀ k l, k ≠ l → p k l ^ 3 = 1 / Mμ μ) ∨ ∃ c : ℂ, c ≠ 0 ∧ ∀ k, w k = c * z k := by
  obtain ⟨hp, hz, hw, hd⟩ := h
  have hLz : (Lmat μ p + 1) *ᵥ z = 0 := funext fun k => by
    rw [Lmat_mulVec, ← hz k, sub_self, Pi.zero_apply]
  have hLw : (Lmat μ p + 1) *ᵥ w = 0 := funext fun k => by
    rw [Lmat_mulVec, ← hw k, sub_self, Pi.zero_apply]
  have hHz := dot_eq_zero_of_mulVec hp hLz
  have hHw := dot_eq_zero_of_mulVec hp hLw
  have hz01 := (distEqs_ne hd (by decide : (0 : Fin 3) ≠ 1)).2.1
  have hw01 := (distEqs_ne hd (by decide : (0 : Fin 3) ≠ 1)).2.2
  by_cases hD : (z 0 - z 1) * (w 0 - w 2) - (w 0 - w 1) * (z 0 - z 2) = 0
  · -- `z` and `w` are dependent: `w = λ z`
    right
    obtain ⟨c, hc⟩ : ∃ c, c = (w 0 - w 1) / (z 0 - z 1) := ⟨_, rfl⟩
    have hcu : c * (z 0 - z 1) = w 0 - w 1 := by rw [hc]; exact div_mul_cancel₀ _ hz01
    have hcv : c * (z 0 - z 2) = w 0 - w 2 := by
      have h' : (z 0 - z 1) * ((w 0 - w 2) - c * (z 0 - z 2)) = 0 := by
        linear_combination hD - (z 0 - z 2) * hcu
      linear_combination -(mul_eq_zero.1 h').resolve_left hz01
    simp only [dotProduct, Fin.sum_univ_three] at hHz hHw
    have hc0 : w 0 = c * z 0 := by
      have h' : Mμ μ * (w 0 - c * z 0) = 0 := by
        simp only [Mμ]
        linear_combination hHw - c * hHz - μ 1 * hcu - μ 2 * hcv
      linear_combination (mul_eq_zero.1 h').resolve_left hM
    refine ⟨c, ?_, fun k => ?_⟩
    · rw [hc]
      exact div_ne_zero hw01 hz01
    · rcases fin3_cases k with rfl | rfl | rfl
      · exact hc0
      · linear_combination hc0 + hcu
      · linear_combination hc0 + hcv
  · -- `z` and `w` are independent: `L + I` vanishes on `H`
    left
    have hrow : ∀ k, ∑ l, (Lmat μ p + 1) k l = 1 := fun k => by
      simp [Matrix.add_apply, Finset.sum_add_distrib, Lmat_row_sum, Matrix.one_apply]
    obtain ⟨h01, h02⟩ := row_of_indep (hrow 0) (congrFun hLz 0) (congrFun hLw 0) hHz hHw hD
    obtain ⟨-, h12⟩ := row_of_indep (hrow 1) (congrFun hLz 1) (congrFun hLw 1) hHz hHw hD
    have e01 : (Lmat μ p + 1) 0 1 = μ 1 * p 0 1 ^ 3 := by simp [Lmat]
    have e02 : (Lmat μ p + 1) 0 2 = μ 2 * p 0 2 ^ 3 := by simp [Lmat]
    have e12 : (Lmat μ p + 1) 1 2 = μ 2 * p 1 2 ^ 3 := by simp [Lmat]
    rw [e01] at h01
    rw [e02] at h02
    rw [e12] at h12
    have key : ∀ {m q : ℂ}, m ≠ 0 → m = Mμ μ * (m * q) → q = 1 / Mμ μ := by
      intro m q hm hmq
      rw [eq_div_iff hM]
      have h' : m * (q * Mμ μ - 1) = 0 := by linear_combination -hmq
      linear_combination (mul_eq_zero.1 h').resolve_left hm
    have p01 := key (hμ 1) h01
    have p02 := key (hμ 2) h02
    have p12 := key (hμ 2) h12
    intro k l hkl
    rcases fin3_cases k with rfl | rfl | rfl <;> rcases fin3_cases l with rfl | rfl | rfl
    · exact absurd rfl hkl
    · exact p01
    · exact p02
    · rw [hp 1 0]; exact p01
    · exact absurd rfl hkl
    · exact p12
    · rw [hp 2 0]; exact p02
    · rw [hp 2 1]; exact p12
    · exact absurd rfl hkl

/-! ## The shapes -/

/-- Lemma 6.9, the Lagrange case: if `p_kl³ = 1/M_μ` for all pairs, the shape `τ` is a root of
`t² − (1 + j^b − j^c) t + j^b` for some `(b, c)`. With `R_kl = p_kl^{-2}`, the distance equations give
`R₁₂ τ² − (R₁₂ + R₁₃ − R₂₃) τ + R₁₃ = 0`, and `R₁₃/R₁₂`, `R₂₃/R₁₂` are cube roots of unity. -/
theorem lagrange_shape {μ : Fin 3 → ℂ} (hM : Mμ μ ≠ 0) {z w : Fin 3 → ℂ} {p : Fin 3 → Fin 3 → ℂ}
    (hd : DistEqs p z w) (hL : ∀ k l, k ≠ l → p k l ^ 3 = 1 / Mμ μ) {τ : ℂ}
    (hτs : τ * (z 0 - z 1) = z 0 - z 2) : ∃ b c : Fin 3, (lagQuad b c).IsRoot τ := by
  have d01 := hd 0 1 (by decide)
  have d02 := hd 0 2 (by decide)
  have d12 := hd 1 2 (by decide)
  have h02 : p 0 2 ^ 2 ≠ 0 := pow_ne_zero 2 (distEqs_ne hd (by decide : (0 : Fin 3) ≠ 2)).1
  have h12 : p 1 2 ^ 2 ≠ 0 := pow_ne_zero 2 (distEqs_ne hd (by decide : (1 : Fin 3) ≠ 2)).1
  have e12 : z 1 - z 2 = (τ - 1) * (z 0 - z 1) := by linear_combination -hτs
  rw [← hτs] at d02
  rw [e12] at d12
  -- `R₁₂ τ² − (R₁₂ + R₁₃ − R₂₃) τ + R₁₃ = 0`, multiplied by `p₁₂² p₁₃² p₂₃²`
  have G : p 0 2 ^ 2 * p 1 2 ^ 2 * τ ^ 2
      - (p 0 1 ^ 2 * p 1 2 ^ 2 + p 0 2 ^ 2 * p 1 2 ^ 2 - p 0 1 ^ 2 * p 0 2 ^ 2) * τ
      + p 0 1 ^ 2 * p 1 2 ^ 2 = 0 := by
    linear_combination (-(p 0 1 ^ 2 * p 0 2 ^ 2 * τ)) * d12 + (p 1 2 ^ 2 * (τ - 1) * p 0 1 ^ 2) * d02
      - (p 1 2 ^ 2 * (τ - 1) * p 0 2 ^ 2 * τ) * d01
  -- `β = R₁₃/R₁₂` and `γ = R₂₃/R₁₂`
  obtain ⟨β, hβ⟩ : ∃ β, β = p 0 1 ^ 2 / p 0 2 ^ 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = p 0 1 ^ 2 / p 1 2 ^ 2 := ⟨_, rfl⟩
  have hβ' : β * p 0 2 ^ 2 = p 0 1 ^ 2 := by rw [hβ]; exact div_mul_cancel₀ _ h02
  have hγ' : γ * p 1 2 ^ 2 = p 0 1 ^ 2 := by rw [hγ]; exact div_mul_cancel₀ _ h12
  have hq : τ ^ 2 - (1 + β - γ) * τ + β = 0 := by
    have h' : p 0 2 ^ 2 * p 1 2 ^ 2 * (τ ^ 2 - (1 + β - γ) * τ + β) = 0 := by
      linear_combination G + (-(p 1 2 ^ 2) * τ + p 1 2 ^ 2) * hβ' + (p 0 2 ^ 2 * τ) * hγ'
    exact (mul_eq_zero.1 h').resolve_left (mul_ne_zero h02 h12)
  have hM2 : (1 / Mμ μ) ^ 2 ≠ 0 := pow_ne_zero 2 (one_div_ne_zero hM)
  have hβ3 : β ^ 3 = 1 := by
    have h' : β ^ 3 * (p 0 2 ^ 3) ^ 2 = (p 0 1 ^ 3) ^ 2 := by
      linear_combination ((β * p 0 2 ^ 2) ^ 2 + β * p 0 2 ^ 2 * p 0 1 ^ 2 + (p 0 1 ^ 2) ^ 2) * hβ'
    rw [hL 0 2 (by decide), hL 0 1 (by decide)] at h'
    exact mul_right_cancel₀ hM2 (h'.trans (one_mul _).symm)
  have hγ3 : γ ^ 3 = 1 := by
    have h' : γ ^ 3 * (p 1 2 ^ 3) ^ 2 = (p 0 1 ^ 3) ^ 2 := by
      linear_combination ((γ * p 1 2 ^ 2) ^ 2 + γ * p 1 2 ^ 2 * p 0 1 ^ 2 + (p 0 1 ^ 2) ^ 2) * hγ'
    rw [hL 1 2 (by decide), hL 0 1 (by decide)] at h'
    exact mul_right_cancel₀ hM2 (h'.trans (one_mul _).symm)
  obtain ⟨b, hb⟩ := eq_jj_pow_of_pow_three hβ3
  obtain ⟨c, hc⟩ := eq_jj_pow_of_pow_three hγ3
  refine ⟨b, c, ?_⟩
  rw [IsRoot.def, eval_lagQuad, ← hb, ← hc]
  exact hq

/-- A sign: `σ² = 1` gives `σ = ±1`. -/
theorem sign_cases {σ : ℂ} (h : σ ^ 2 = 1) : σ = 1 ∨ σ = -1 := by
  have h' : (σ - 1) * (σ + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact Or.inl (by linear_combination h1)
  · exact Or.inr (by linear_combination h1)

/-- Lemma 6.9, the collinear case, as an identity: with `z₁₂ = s`, `z₁₃ = τ s`, `z₂₃ = (τ − 1) s` and
`p_kl z_kl = σ_kl κ` (`σ_kl² = 1`, `κ ≠ 0`), the equations of `z` give `Q_σ(τ − 1) = 0`: they say `z_k = κ³ F_k`,
and `κ³ Q_σ(x)`, `x = τ − 1`, is a combination of them (the identity `x(F₁ − F₂) = F₂ − F₃` cleared of
denominators). -/
theorem collinear_Q (μ : Fin 3 → ℂ) {z0 s τ κ p01 p02 p12 a b c : ℂ} (hκ : κ ≠ 0)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hz0 : z0 = μ 1 * p01 ^ 3 * s + μ 2 * p02 ^ 3 * (τ * s))
    (hz1 : z0 - s = μ 0 * p01 ^ 3 * (-s) + μ 2 * p12 ^ 3 * ((τ - 1) * s))
    (hz2 : z0 - τ * s = μ 0 * p02 ^ 3 * (-(τ * s)) + μ 1 * p12 ^ 3 * (-((τ - 1) * s)))
    (e01 : p01 * s = a * κ) (e02 : p02 * (τ * s) = b * κ) (e12 : p12 * ((τ - 1) * s) = c * κ) :
    (Qσ μ a b c).eval (τ - 1) = 0 := by
  have c01 : p01 ^ 3 * s ^ 3 = a * κ ^ 3 := by
    linear_combination ((p01 * s) ^ 2 + p01 * s * (a * κ) + (a * κ) ^ 2) * e01 + a * κ ^ 3 * ha
  have c02 : p02 ^ 3 * (τ * s) ^ 3 = b * κ ^ 3 := by
    linear_combination ((p02 * (τ * s)) ^ 2 + p02 * (τ * s) * (b * κ) + (b * κ) ^ 2) * e02 + b * κ ^ 3 * hb
  have c12 : p12 ^ 3 * ((τ - 1) * s) ^ 3 = c * κ ^ 3 := by
    linear_combination ((p12 * ((τ - 1) * s)) ^ 2 + p12 * ((τ - 1) * s) * (c * κ) + (c * κ) ^ 2) * e12 +
      c * κ ^ 3 * hc
  -- the equations of `z₁₂ = s` and `z₂₃ = (τ − 1) s`
  have eA : s = (μ 0 + μ 1) * p01 ^ 3 * s + μ 2 * p02 ^ 3 * (τ * s) - μ 2 * p12 ^ 3 * ((τ - 1) * s) := by
    linear_combination hz0 - hz1
  have eB : (τ - 1) * s = -(μ 0 * p01 ^ 3 * s) + μ 0 * p02 ^ 3 * (τ * s) +
      (μ 1 + μ 2) * p12 ^ 3 * ((τ - 1) * s) := by
    linear_combination hz1 - hz2
  -- `s³ τ² x² = κ³ x²(1+x)²(F₁ − F₂)` and `x s³ τ² x² = κ³ x²(1+x)²(F₂ − F₃)` with `x = τ − 1`
  have hA : s ^ 3 * τ ^ 2 * (τ - 1) ^ 2 = κ ^ 3 * ((μ 0 + μ 1) * a * τ ^ 2 * (τ - 1) ^ 2 +
      μ 2 * b * (τ - 1) ^ 2 - μ 2 * c * τ ^ 2) := by
    linear_combination s ^ 2 * τ ^ 2 * (τ - 1) ^ 2 * eA + (μ 0 + μ 1) * τ ^ 2 * (τ - 1) ^ 2 * c01 +
      μ 2 * (τ - 1) ^ 2 * c02 - μ 2 * τ ^ 2 * c12
  have hB : (τ - 1) * s ^ 3 * τ ^ 2 * (τ - 1) ^ 2 = κ ^ 3 * (-(μ 0 * a * τ ^ 2 * (τ - 1) ^ 2) +
      μ 0 * b * (τ - 1) ^ 2 + (μ 1 + μ 2) * c * τ ^ 2) := by
    linear_combination s ^ 2 * τ ^ 2 * (τ - 1) ^ 2 * eB - μ 0 * τ ^ 2 * (τ - 1) ^ 2 * c01 +
      μ 0 * (τ - 1) ^ 2 * c02 + (μ 1 + μ 2) * τ ^ 2 * c12
  have hQ : κ ^ 3 * (Qσ μ a b c).eval (τ - 1) = 0 := by
    rw [eval_Qσ]
    linear_combination (-(τ - 1)) * hA + hB
  exact (mul_eq_zero.1 hQ).resolve_left (pow_ne_zero 3 hκ)

/-- Lemma 6.9, the collinear case: if `w = λ z` with `λ ≠ 0`, then `p_kl = σ_kl κ / z_kl` with `κ² = 1/λ` and
`σ` an antisymmetric sign pattern, and the shape `τ` is a root of `∏_σ Q_σ(t − 1)`. -/
theorem collinear_shape {μ : Fin 3 → ℂ} {z w : Fin 3 → ℂ} {p : Fin 3 → Fin 3 → ℂ} (hp : IsSymm p)
    (hz : ∀ k, z k = force μ p z k) (hd : DistEqs p z w) {c : ℂ} (hc : c ≠ 0) (hwc : ∀ k, w k = c * z k)
    {τ : ℂ} (hτs : τ * (z 0 - z 1) = z 0 - z 2) :
    (Qσ μ 1 1 1).eval (τ - 1) * (Qσ μ 1 1 (-1)).eval (τ - 1) * (Qσ μ 1 (-1) (-1)).eval (τ - 1) *
      (Qσ μ 1 (-1) 1).eval (τ - 1) = 0 := by
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ two_pos
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hκ
    exact inv_ne_zero hc hκ.symm
  -- `(p_kl z_kl)² = κ²`
  have hsq : ∀ k l, k ≠ l → (p k l * (z k - z l)) ^ 2 = κ ^ 2 := by
    intro k l hkl
    have h := hd k l hkl
    rw [hwc k, hwc l] at h
    rw [hκ]
    exact eq_inv_of_mul_eq_one_left (by linear_combination h)
  -- the signs `σ_kl = p_kl z_kl / κ`
  have hsig : ∀ k l, k ≠ l → ∃ σ : ℂ, σ ^ 2 = 1 ∧ p k l * (z k - z l) = σ * κ := by
    intro k l hkl
    refine ⟨p k l * (z k - z l) / κ, ?_, (div_mul_cancel₀ _ hκ0).symm⟩
    rw [div_pow, hsq k l hkl, div_self (pow_ne_zero 2 hκ0)]
  obtain ⟨a, ha, e01⟩ := hsig 0 1 (by decide)
  obtain ⟨b, hb, e02⟩ := hsig 0 2 (by decide)
  obtain ⟨c', hc', e12⟩ := hsig 1 2 (by decide)
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  rw [force_zero_eq] at hz0
  rw [force_one_eq μ hp] at hz1
  rw [force_two_eq μ hp] at hz2
  have key := collinear_Q μ (z0 := z 0) (s := z 0 - z 1) (τ := τ) (κ := κ) (p01 := p 0 1) (p02 := p 0 2)
    (p12 := p 1 2) (a := a) (b := b) (c := c') hκ0 ha hb hc'
    (by linear_combination hz0 - μ 2 * p 0 2 ^ 3 * hτs)
    (by linear_combination hz1 - μ 2 * p 1 2 ^ 3 * hτs)
    (by linear_combination hz2 + (-1 + μ 0 * p 0 2 ^ 3 + μ 1 * p 1 2 ^ 3) * hτs)
    e01 (by linear_combination e02 + p 0 2 * hτs) (by linear_combination e12 + p 1 2 * hτs)
  exact Qσ_classes μ (sign_cases ha) (sign_cases hb) (sign_cases hc') key

/-- **Lemma 6.9** (`lem:three`), second part: for `μ_k ≠ 0` and `M_μ ≠ 0`, let `(z, w, p)` be a solution of `N(μ)`.
Then `s = z₁ − z₂` is nonzero, and with the shape `τ = (z₁ − z₃)/s` the positions are `z_k/s = ℓ_k(τ)/M_μ`, and `τ`
is a root of `S_μ`. -/
theorem three_shape {μ : Fin 3 → ℂ} (hμ : ∀ k, μ k ≠ 0) (hM : Mμ μ ≠ 0) {z w : Fin 3 → ℂ}
    {p : Fin 3 → Fin 3 → ℂ} (h : IsNSys μ z w p) :
    z 0 - z 1 ≠ 0 ∧
      (∀ k, z k / (z 0 - z 1) = (ellP μ k).eval ((z 0 - z 2) / (z 0 - z 1)) / Mμ μ) ∧
      (Sμ μ).IsRoot ((z 0 - z 2) / (z 0 - z 1)) := by
  have hdich := three_dichotomy hμ hM h
  obtain ⟨hp, hz, hw, hd⟩ := h
  have hs0 := (distEqs_ne hd (by decide : (0 : Fin 3) ≠ 1)).2.1
  refine ⟨hs0, ?_⟩
  generalize hτ : (z 0 - z 2) / (z 0 - z 1) = τ
  have hτs : τ * (z 0 - z 1) = z 0 - z 2 := by
    rw [← hτ]
    exact div_mul_cancel₀ _ hs0
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  rw [force_zero_eq] at hz0
  rw [force_one_eq μ hp] at hz1
  rw [force_two_eq μ hp] at hz2
  -- the centre of mass: `Σ μ_k z_k = 0`
  have hcm : μ 0 * z 0 + μ 1 * z 1 + μ 2 * z 2 = 0 := by
    linear_combination μ 0 * hz0 + μ 1 * hz1 + μ 2 * hz2
  refine ⟨fun k => ?_, ?_⟩
  · rw [div_eq_div_iff hs0 hM]
    rcases fin3_cases k with rfl | rfl | rfl
    · rw [eval_ellP_zero]
      simp only [Mμ]
      linear_combination hcm - μ 2 * hτs
    · rw [eval_ellP_one]
      simp only [Mμ]
      linear_combination hcm - μ 2 * hτs
    · rw [eval_ellP_two]
      simp only [Mμ]
      linear_combination hcm + (μ 0 + μ 1) * hτs
  · rw [IsRoot.def, eval_Sμ]
    rcases hdich with hL | ⟨c, hc, hwc⟩
    · obtain ⟨b, c, hbc⟩ := lagrange_shape hM hd hL hτs
      rw [(lagQuad_root b c hbc).eq_zero, zero_mul]
    · rw [collinear_shape hp hz hd hc hwc hτs, mul_zero]

end

end CC6Full.Six
