import CC6Full.Six.E4
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The forms of Lemma 7.6 with the masses as variables

Proposition 7.8 (`prop:E4`) and Theorem 7.12 (`thm:d64`) of the paper use that the forms `ℱ_ε` and `𝒢_σ` of
Lemma 7.6 (`lem:E4`, `CC6Full.lem_E4`) have coefficients in `ℤ[j][μ₁, …, μ₄]`. This file gives them in this form.

* `E4P.ZJ`: the subring `ℤ[j] = {a + b j : a, b ∈ ℤ}` of `ℂ`, `j = e^{2πi/3}` (`E4.jj`). It is closed under
  products since `j² = −1 − j` (`E4P.jj_sq`), and under complex conjugation since `conj j = −1 − j`
  (`E4P.conj_jj`, `E4P.conj_mem_ZJ`), and `ℤ[j] ∩ ℝ = ℤ` (`E4P.eq_intCast_of_mem_ZJ`), because `j` is not real.
* `E4P.Fforms e`, `E4P.Gforms s`: the forms `ℱ_ε` and `𝒢_σ` with coefficients in `ℤ[j][μ]`
  (`MvPolynomial (Fin 4) ZJ`; the variable `X k` is the mass `μ_{k+1}`), homogeneous of degree `3` in `q`, resp.
  `4` in `(ξ₂, ξ₃, ξ₄)` (`E4P.Fforms_hom`, `E4P.Gforms_hom`).
* `E4P.map_Fforms`, `E4P.map_Gforms`: specialized at `μ ∈ ℂ⁴` (the coefficient map `eval₂Hom ZJ.subtype μ`), they
  are the forms `E4.Fforms μ e` and `E4.Gforms μ s` of Lemma 7.6.
-/

namespace CC6Full.Six

open MvPolynomial Finset ComplexConjugate

noncomputable section

namespace E4P

/-! ## The ring `ℤ[j]` -/

/-- `j² + j + 1 = 0` for `j = e^{2πi/3}`. -/
theorem jj_sq : E4.jj ^ 2 + E4.jj + 1 = 0 := by
  have h3 : E4.jj ^ 3 = 1 := E4.jj_prim.pow_eq_one
  have h1 : E4.jj ≠ 1 := E4.jj_prim.ne_one (by norm_num)
  have h : (E4.jj - 1) * (E4.jj ^ 2 + E4.jj + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h1)

/-- `j` is not real: `t² + t + 1` has no real root. -/
theorem jj_im_ne_zero : E4.jj.im ≠ 0 := by
  intro h
  have h2 := congrArg Complex.re jj_sq
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re, h, mul_zero,
    sub_zero] at h2
  nlinarith [sq_nonneg (E4.jj.re + 1 / 2)]

/-- `conj j ≠ j`, since `j` is not real. -/
theorem conj_jj_ne : conj E4.jj - E4.jj ≠ 0 :=
  sub_ne_zero.mpr fun h => jj_im_ne_zero (Complex.conj_eq_iff_im.mp h)

/-- `conj j = j² = −1 − j`. -/
theorem conj_jj : conj E4.jj = -1 - E4.jj := by
  have hc : conj E4.jj ^ 2 + conj E4.jj + 1 = 0 := by
    have h := congrArg (starRingEnd ℂ) jj_sq
    simpa only [map_add, map_pow, map_one, map_zero] using h
  have h : (conj E4.jj - E4.jj) * (conj E4.jj + E4.jj + 1) = 0 := by linear_combination hc - jj_sq
  linear_combination (mul_eq_zero.mp h).resolve_left conj_jj_ne

/-- The ring `ℤ[j] = {a + b j : a, b ∈ ℤ}` as a subring of `ℂ`; it is closed under products because
`j² = −1 − j`. -/
def ZJ : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = a + b * E4.jj}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a * c - b * d, a * d + b * c - b * d, by push_cast; linear_combination ((b : ℂ) * d) * jj_sq⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩

theorem mem_ZJ {z : ℂ} : z ∈ ZJ ↔ ∃ a b : ℤ, z = a + b * E4.jj := Iff.rfl

theorem jj_mem : E4.jj ∈ ZJ := ⟨0, 1, by simp⟩

/-- `ℤ[j]` is closed under complex conjugation: `conj (a + b j) = (a − b) − b j`. -/
theorem conj_mem_ZJ {z : ℂ} (hz : z ∈ ZJ) : conj z ∈ ZJ := by
  obtain ⟨a, b, rfl⟩ := mem_ZJ.mp hz
  refine ⟨a - b, -b, ?_⟩
  rw [map_add, map_mul, map_intCast, map_intCast, conj_jj]
  push_cast
  ring

/-- `ℤ[j] ∩ ℝ = ℤ`: an element `a + b j` of `ℤ[j]` fixed by complex conjugation has `b = 0`. -/
theorem eq_intCast_of_mem_ZJ {z : ℂ} (hz : z ∈ ZJ) (hr : conj z = z) : ∃ n : ℤ, z = n := by
  obtain ⟨a, b, rfl⟩ := mem_ZJ.mp hz
  refine ⟨a, ?_⟩
  rw [map_add, map_mul, map_intCast, map_intCast] at hr
  have hb : (b : ℂ) * (conj E4.jj - E4.jj) = 0 := by linear_combination hr
  rw [(mul_eq_zero.mp hb).resolve_right conj_jj_ne, zero_mul, add_zero]

/-- `ε_kl = j^{e_kl}` (`E4.eps`) as an element of `ℤ[j]`. -/
def epsZ (e : Fin 6 → ZMod 3) (k l : Fin 4) : ZJ := ⟨E4.eps e k l, pow_mem jj_mem _⟩

/-- `σ_kl ∈ {1, −1, 0}` (`E4.sgn`) as an element of `ℤ[j]`. -/
def sgnZ (s : Fin 6 → Bool) (k l : Fin 4) : ZJ :=
  ⟨E4.sgn s k l, by
    unfold E4.sgn
    split_ifs <;> first | exact one_mem ZJ | exact neg_mem (one_mem ZJ) | exact zero_mem ZJ⟩

@[simp] theorem coe_epsZ (e : Fin 6 → ZMod 3) (k l : Fin 4) : (epsZ e k l : ℂ) = E4.eps e k l := rfl

@[simp] theorem coe_sgnZ (s : Fin 6 → Bool) (k l : Fin 4) : (sgnZ s k l : ℂ) = E4.sgn s k l := rfl

@[simp] theorem subtype_epsZ (e : Fin 6 → ZMod 3) (k l : Fin 4) : ZJ.subtype (epsZ e k l) = E4.eps e k l := rfl

@[simp] theorem subtype_sgnZ (s : Fin 6 → Bool) (k l : Fin 4) : ZJ.subtype (sgnZ s k l) = E4.sgn s k l := rfl

/-! ## The forms with coefficients in `ℤ[j][μ]` -/

/-- `A_k = Σ_{l ≠ k} ε_kl μ_l q_l`, with coefficients `ε_kl μ_l ∈ ℤ[j][μ]`. -/
def Aform (e : Fin 6 → ZMod 3) (k : Fin 4) : MvPolynomial (Fin 4) (MvPolynomial (Fin 4) ZJ) :=
  ∑ l ∈ univ.erase k, C (C (epsZ e k l) * X l : MvPolynomial (Fin 4) ZJ) * X l

/-- `q_j² A_k − q_k² A_j`. -/
def Fpair (e : Fin 6 → ZMod 3) (j k : Fin 4) : MvPolynomial (Fin 4) (MvPolynomial (Fin 4) ZJ) :=
  X j ^ 2 * Aform e k - X k ^ 2 * Aform e j

/-- `Σ_k μ_k q_k³`. -/
def Fcub : MvPolynomial (Fin 4) (MvPolynomial (Fin 4) ZJ) :=
  ∑ k, C (X k : MvPolynomial (Fin 4) ZJ) * X k ^ 3

/-- The seven cubic forms `ℱ_ε` of Lemma 7.6 (`lem:E4`) with coefficients in `ℤ[j][μ₁, …, μ₄]`, in the order of
`E4.Fforms`: the forms `q_j² A_k − q_k² A_j`, `j < k`, in lexicographic order, and `Σ_k μ_k q_k³`. -/
def Fforms (e : Fin 6 → ZMod 3) : Fin 7 → MvPolynomial (Fin 4) (MvPolynomial (Fin 4) ZJ) :=
  ![Fpair e 0 1, Fpair e 0 2, Fpair e 0 3, Fpair e 1 2, Fpair e 1 3, Fpair e 2 3, Fcub]

/-- The coordinates `(ξ₁, ξ₂, ξ₃, ξ₄) = (0, X₀, X₁, X₂)`. -/
def Xi : Fin 4 → MvPolynomial (Fin 3) (MvPolynomial (Fin 4) ZJ) := ![0, X 0, X 1, X 2]

/-- The four quartic forms `𝒢_σ` of Lemma 7.6 (`lem:E4`) with coefficients in `ℤ[μ₁, …, μ₄] ⊂ ℤ[j][μ₁, …, μ₄]`:
`Σ_{l≠k} σ_kl μ_l Π_{j≠k,l} (ξ_k − ξ_j)²` with `ξ = (0, X₀, X₁, X₂)`. -/
def Gforms (s : Fin 6 → Bool) (k : Fin 4) : MvPolynomial (Fin 3) (MvPolynomial (Fin 4) ZJ) :=
  ∑ l ∈ univ.erase k, C (C (sgnZ s k l) * X l : MvPolynomial (Fin 4) ZJ) *
    ∏ j ∈ (univ.erase k).erase l, (Xi k - Xi j) ^ 2

/-! ## Specialization of the masses -/

theorem map_Aform (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (k : Fin 4) :
    map (eval₂Hom ZJ.subtype μ) (Aform e k) = E4.Aform μ e k := by
  simp only [Aform, E4.Aform, map_sum, map_mul, map_C, map_X, eval₂Hom_C, eval₂Hom_X', subtype_epsZ]

theorem map_Fpair (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (j k : Fin 4) :
    map (eval₂Hom ZJ.subtype μ) (Fpair e j k) = E4.Fpair μ e j k := by
  simp only [Fpair, E4.Fpair, map_sub, map_mul, map_pow, map_X, map_Aform]

theorem map_Fcub (μ : Fin 4 → ℂ) : map (eval₂Hom ZJ.subtype μ) Fcub = E4.Fcub μ := by
  simp only [Fcub, E4.Fcub, map_sum, map_mul, map_pow, map_C, map_X, eval₂Hom_X']

/-- Specialized at `μ ∈ ℂ⁴`, the forms `E4P.Fforms e` are the forms `ℱ_ε` of Lemma 7.6 (`E4.Fforms μ e`). -/
theorem map_Fforms (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (i : Fin 7) :
    map (eval₂Hom ZJ.subtype μ) (Fforms e i) = E4.Fforms μ e i := by
  fin_cases i <;> simp [Fforms, E4.Fforms, map_Fpair, map_Fcub]

theorem map_Xi (μ : Fin 4 → ℂ) (k : Fin 4) : map (eval₂Hom ZJ.subtype μ) (Xi k) = E4.Xi k := by
  fin_cases k <;> simp [Xi, E4.Xi]

/-- Specialized at `μ ∈ ℂ⁴`, the forms `E4P.Gforms s` are the forms `𝒢_σ` of Lemma 7.6 (`E4.Gforms μ s`). -/
theorem map_Gforms (μ : Fin 4 → ℂ) (s : Fin 6 → Bool) (k : Fin 4) :
    map (eval₂Hom ZJ.subtype μ) (Gforms s k) = E4.Gforms μ s k := by
  simp only [Gforms, E4.Gforms, map_sum, map_mul, map_prod, map_pow, map_sub, map_C, map_Xi, eval₂Hom_C,
    eval₂Hom_X', subtype_sgnZ]

/-! ## Homogeneity -/

theorem Aform_hom (e : Fin 6 → ZMod 3) (k : Fin 4) : (Aform e k).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem Fpair_hom (e : Fin 6 → ZMod 3) (j k : Fin 4) : (Fpair e j k).IsHomogeneous 3 :=
  ((isHomogeneous_X_pow (R := MvPolynomial (Fin 4) ZJ) j 2).mul (Aform_hom e k)).sub
    ((isHomogeneous_X_pow (R := MvPolynomial (Fin 4) ZJ) k 2).mul (Aform_hom e j))

theorem Fcub_hom : Fcub.IsHomogeneous 3 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X_pow _ _ _

/-- The forms `ℱ_ε` are cubic. -/
theorem Fforms_hom (e : Fin 6 → ZMod 3) (i : Fin 7) : (Fforms e i).IsHomogeneous 3 := by
  fin_cases i <;> simp [Fforms, Fpair_hom, Fcub_hom]

theorem Xi_hom (k : Fin 4) : (Xi k).IsHomogeneous 1 := by
  fin_cases k <;> simp [Xi, isHomogeneous_zero, isHomogeneous_X]

/-- The forms `𝒢_σ` are quartic: each term is a constant times a product of two squares of linear forms. -/
theorem Gforms_hom (s : Fin 6 → Bool) (k : Fin 4) : (Gforms s k).IsHomogeneous 4 := by
  unfold Gforms
  refine IsHomogeneous.sum _ _ _ fun l hl => ?_
  have hcard : ((univ.erase k).erase l).card = 2 := by
    rw [card_erase_of_mem hl, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin]
  have hp := IsHomogeneous.prod ((univ.erase k).erase l) (fun j => (Xi k - Xi j) ^ 2) (fun _ => 2)
    fun j _ => by
      have h := ((Xi_hom k).sub (Xi_hom j)).pow 2
      rwa [one_mul] at h
  rw [sum_const, hcard, smul_eq_mul] at hp
  exact hp.C_mul _

end E4P

end

end CC6Full.Six
