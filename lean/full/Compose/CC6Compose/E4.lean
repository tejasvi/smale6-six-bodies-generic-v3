import CC6Full.Six.D64NoZero
import Lean6.Special.K4.E4.Final

/-!
# Bridge: the fact `E4NoZero` at `μ₀ = (3, 5, 7, 11)` from the certificate project

`E4NoZero` (the hypothesis of `d64_poly_of_noZero`) from `check_3_5_7_11` of the certificate project
(`Lean6.Special.K4.E4`). There the forms of Lemma 7.6 are the paper's formulas written as functions: `FZero ω μ e q`
says that `q` is a common zero of the seven cubic forms `ℱ_ε`, for a symmetric pattern `e : Fin 4 → Fin 4 → ℕ`
(`ε_kl = ω ^ e_kl`, with `ω² + ω + 1 = 0`), and `GZero μ σ ξ` says that `ξ` is a common zero of the four quartic
forms `𝒢_σ`, for an antisymmetric sign matrix `σ : Fin 4 → Fin 4 → ℤ`.

* `expPat e`: the symmetric matrix `e_kl = e_{pidx k l}` of the pattern `e : Fin 6 → ZMod 3` of `CC6Full.Six.E4`;
  with `ω = j` (`E4.jj`), `ω ^ e_kl = ε_kl` (`E4.eps e k l`).
* `sgnPat s`: the antisymmetric sign matrix of the pattern `s : Fin 6 → Bool`, with entries `σ_kl` (`E4.sgn s k l`,
  `cast_sgnPat`).
* `aeps_eq`, `gsig_eq`: the linear forms `A_k` and the quartic forms `𝒢_σ,k` of the certificate project are the
  evaluations of `E4.Aform` and `E4.Gforms`.
* `e4NoZero`: `E4NoZero`.
-/

namespace CC6Compose

open CC6Full CC6Full.Six MvPolynomial Finset

/-! ## Patterns -/

/-- The symmetric pattern of exponents for the pattern `e : Fin 6 → ZMod 3`: `e_kl = e_{pidx k l} ∈ {0, 1, 2}`
(on the diagonal, where it is not used, the value on the pair `{0, 1}`). -/
def expPat (e : Fin 6 → ZMod 3) (k l : Fin 4) : ℕ := (e (E4.pidx k l)).val

theorem expPat_symm (e : Fin 6 → ZMod 3) (k l : Fin 4) : expPat e k l = expPat e l k := by
  rw [expPat, expPat, E4.pidx_comm]

/-- The antisymmetric sign matrix of the pattern `s : Fin 6 → Bool`: the entries of `E4.sgn s` as integers. -/
def sgnPat (s : Fin 6 → Bool) (k l : Fin 4) : ℤ :=
  if k < l then (if s (E4.pidx k l) then 1 else -1) else if l < k then (if s (E4.pidx k l) then -1 else 1) else 0

theorem cast_sgnPat (s : Fin 6 → Bool) (k l : Fin 4) : (sgnPat s k l : ℂ) = E4.sgn s k l := by
  unfold sgnPat E4.sgn
  split_ifs <;> simp

theorem sgnPat_antisymm (s : Fin 6 → Bool) (k l : Fin 4) : sgnPat s l k = -sgnPat s k l := by
  unfold sgnPat
  rw [E4.pidx_comm l k]
  rcases lt_trichotomy k l with h | rfl | h
  · have h' : ¬l < k := not_lt.mpr h.le
    cases s (E4.pidx k l) <;> simp [h, h']
  · simp
  · have h' : ¬k < l := not_lt.mpr h.le
    cases s (E4.pidx k l) <;> simp [h, h']

theorem sgnPat_pm (s : Fin 6 → Bool) (k l : Fin 4) (hkl : k ≠ l) :
    sgnPat s k l = 1 ∨ sgnPat s k l = -1 := by
  unfold sgnPat
  rcases lt_or_gt_of_ne hkl with h | h
  · cases s (E4.pidx k l) <;> simp [h]
  · have h' : ¬k < l := not_lt.mpr h.le
    cases s (E4.pidx k l) <;> simp [h, h']

/-! ## Sums and products over the other bodies -/

theorem sum_ite_eq_sum_erase {M : Type*} [AddCommMonoid M] (k : Fin 4) (g : Fin 4 → M) :
    (∑ l, if l = k then 0 else g l) = ∑ l ∈ univ.erase k, g l := by
  rw [← Finset.add_sum_erase _ _ (mem_univ k), ite_eq_left rfl, zero_add]
  exact Finset.sum_congr rfl fun l hl => ite_eq_right (ne_of_mem_erase hl)

theorem prod_ite_eq_prod_erase {M : Type*} [CommMonoid M] {k l : Fin 4} (hlk : l ≠ k) (g : Fin 4 → M) :
    (∏ j, if j = k ∨ j = l then 1 else g j) = ∏ j ∈ (univ.erase k).erase l, g j := by
  rw [← Finset.mul_prod_erase _ _ (mem_univ k), ite_eq_left (Or.inl rfl), one_mul,
    ← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hlk, mem_univ l⟩), ite_eq_left (Or.inr rfl), one_mul]
  refine Finset.prod_congr rfl fun j hj => ite_eq_right ?_
  obtain ⟨hjl, hj'⟩ := mem_erase.mp hj
  obtain ⟨hjk, -⟩ := mem_erase.mp hj'
  rintro (h | h)
  · exact hjk h
  · exact hjl h

/-! ## The forms -/

/-- `A_k = Σ_{l ≠ k} ω^{e_kl} μ_l q_l` of the certificate project, with `ω = j` and the pattern `expPat e`, is
`E4.Aform μ e k` evaluated at `q`. -/
theorem aeps_eq (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (q : Fin 4 → ℂ) (k : Fin 4) :
    Lean6.Special.K4.E4.Aeps E4.jj μ (expPat e) q k = eval q (E4.Aform μ e k) := by
  rw [E4.eval_Aform, Lean6.Special.K4.E4.Aeps, sum_ite_eq_sum_erase]
  rfl

/-- The quartic form `𝒢_σ,k` of the certificate project, with the sign matrix `sgnPat s` and
`ξ = (0, y₀, y₁, y₂)`, is `E4.Gforms μ s k` evaluated at `y`. -/
theorem gsig_eq (μ : Fin 4 → ℂ) (s : Fin 6 → Bool) (y : Fin 3 → ℂ) (k : Fin 4) :
    Lean6.Special.K4.E4.Gsig μ (sgnPat s) ![0, y 0, y 1, y 2] k = eval y (E4.Gforms μ s k) := by
  rw [E4.eval_Gforms, Lean6.Special.K4.E4.Gsig, sum_ite_eq_sum_erase]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [cast_sgnPat, prod_ite_eq_prod_erase (ne_of_mem_erase hl)]

/-- The form of `E4.Fforms` with number `pidx j k` (`j < k`) is `q_j² A_k − q_k² A_j`. -/
theorem Fforms_pidx (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) {j k : Fin 4} (hjk : j < k) :
    E4.Fforms μ e (E4.pidx j k).castSucc = E4.Fpair μ e j k := by
  fin_cases j <;> fin_cases k <;> first | exact absurd hjk (by decide) | rfl

/-- A common zero of the forms `E4.Fforms μ₀ e` is a common zero of the forms `ℱ_ε` of the certificate project
(`FZero`), with `ω = j` and the pattern `expPat e`. -/
theorem fZero_of_eval (e : Fin 6 → ZMod 3) (q : Fin 4 → ℂ) (hq : ∀ i, eval q (E4.Fforms E4P.μ₀ e i) = 0) :
    Lean6.Special.K4.E4.FZero E4.jj E4P.μ₀ (expPat e) q := by
  refine ⟨fun j k hjk => ?_, ?_⟩
  · have h := hq (E4.pidx j k).castSucc
    rw [Fforms_pidx E4P.μ₀ e hjk, E4.eval_Fpair] at h
    rw [aeps_eq, aeps_eq]
    exact h
  · have h := hq 6
    rw [show E4.Fforms E4P.μ₀ e 6 = E4.Fcub E4P.μ₀ from rfl, E4.eval_Fcub] at h
    exact h

/-- A common zero of the forms `E4.Gforms μ₀ s` is a common zero of the forms `𝒢_σ` of the certificate project
(`GZero`), with the sign matrix `sgnPat s`. -/
theorem gZero_of_eval (s : Fin 6 → Bool) (y : Fin 3 → ℂ) (hy : ∀ k, eval y (E4.Gforms E4P.μ₀ s k) = 0) :
    Lean6.Special.K4.E4.GZero E4P.μ₀ (sgnPat s) y := by
  intro k
  rw [gsig_eq]
  exact hy k

/-! ## The fact at `μ₀` -/

/-- **`E4NoZero`** from `check_3_5_7_11` (with `ω = j`, a root of `ω² + ω + 1 = 0`): at `μ₀ = (3, 5, 7, 11)` no
`ℱ_ε` has a common zero `q ≠ 0` and no `𝒢_σ` has a common zero `≠ 0`. -/
theorem e4NoZero_of (h : type_of% @Lean6.Special.K4.E4.check_3_5_7_11) : E4NoZero := by
  obtain ⟨hF, hG⟩ := h E4.jj E4P.jj_sq
  exact ⟨fun e q hq => hF (expPat e) (expPat_symm e) q (fZero_of_eval e q hq),
    fun s y hy => hG (sgnPat s) (sgnPat_antisymm s) (sgnPat_pm s) y (gZero_of_eval s y hy)⟩

theorem e4NoZero : E4NoZero := e4NoZero_of Lean6.Special.K4.E4.check_3_5_7_11

end CC6Compose
