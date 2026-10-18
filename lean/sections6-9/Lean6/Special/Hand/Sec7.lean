import Mathlib
import Lean6.Special.Hand.Sec2
import Lean6.Special.K4.E4.Final
import Lean6.Special.K4.C4.Final

/-!
# Computations inside the hand proofs of Section 7

* Lemmas 7.1–7.5: `sum_mass_Phi` (`Σ_{k∈K} m_k Φ^η_k = 0`, antisymmetry), `const_force` (the constant force `c′`
  gives `c′ Σ m_k = 0`), `d64_exponents`, `d64_F4`, `d64_Zjk`.
* Lemma 7.6 (`lem:E4`), the algebra of the reduction, as bridges to the forms of `K4.E4.Final`:
  * `E4_noncollinear`: if the solution of `E_4(μ)` has `P_kl³ = u_k u_l` (`k ≠ l`, all `u_k ≠ 0`; the rank-one case)
    and `ξ` is not constant, then some pattern `ε` has a nonzero common zero of `F_ε` (`K4.E4.FZero`);
  * `E4_collinear`: if `η = λξ + θ` (`λ ≠ 0`), then some antisymmetric sign pattern `σ` has a nonzero common zero of
    `G_σ` (`K4.E4.GZero`).
  The step from "the span of `1, ξ, η` has dimension `3`" to `P_kl³ = u_k u_l` (rank one, symmetry) and from dimension
  `2` to `η = λξ + θ` is linear algebra and stays a hand step.
* §7.3, the equations of `Z(μ)` (`K4.C4.eqsZ`): `II_of_iii` ((II) is (iii) times `∏_{l≠k}(ξ_k − ξ_l)`), `III_of_eta`
  ((III) is `η_kl + η_ln + η_nk = 0` times `a_kl a_ln a_nk`), `xiZ_centre`, `xiZ_param` (the solutions of `ξ_4 = 0`,
  `Σ_{k≤3} μ_k ξ_k = 0`), `bideg_I`, `bideg_II`, `bideg_III` (the bidegrees `(1,3)`, `(2,1)`, `(2,4)`).
-/

namespace Lean6.Special.Hand

open Finset

/-! ## Lemmas 7.1–7.5 -/

/-- **Lemmas 7.3, 7.5**: `Σ_{k∈K} m_k Φ^η_k = 0` identically, with `Φ^η_k = Σ_{l∈K, l≠k} m_l P_kl³ (η_k − η_l)` and
symmetric `P`. -/
theorem sum_mass_Phi {ι R : Type*} [DecidableEq ι] [CommRing R] (K : Finset ι) (m : ι → R) (P : ι → ι → R)
    (hP : ∀ k l, P k l = P l k) (η : ι → R) :
    ∑ k ∈ K, m k * ∑ l ∈ K.erase k, m l * P k l ^ 3 * (η k - η l) = 0 := by
  have h : ∀ k ∈ K, m k * ∑ l ∈ K.erase k, m l * P k l ^ 3 * (η k - η l) =
      ∑ l ∈ K, m k * m l * P k l ^ 3 * (η k - η l) := by
    intro k hk
    rw [Finset.mul_sum, ← Finset.sum_erase_add K _ hk]
    simp only [sub_self, mul_zero, add_zero]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl h]
  exact sum_sum_antisymm K _ (fun k l => by rw [hP l k]; ring) (fun k => by simp)

/-- **Lemma 7.3**: if `Φ^η_l = c′` for all `l ∈ K`, then `c′ Σ_{k∈K} m_k = 0` (with `Σ m_k Φ^η_k = 0`). -/
theorem const_force {ι R : Type*} [CommRing R] (K : Finset ι) (m Φ : ι → R) (c : R) (hΦ : ∀ k ∈ K, Φ k = c)
    (hsum : ∑ k ∈ K, m k * Φ k = 0) : c * ∑ k ∈ K, m k = 0 := by
  rw [Finset.mul_sum, ← hsum]
  exact Finset.sum_congr rfl fun k hk => by rw [hΦ k hk]; ring

/-- **Lemma 7.3**, exponents (on the pairs of `K`: `ζ = 3x − 2`, `ω = 2 − x`; for `j ∈ {1, 2}`: `ζ_jk = 3x − 2`,
`ω_jk = −2`): `e(Z_kj) = 4 − 3x/2 > −2` (for `x < 1`), `e(W_kl) = 2 − 4x`, `e(W_kj) = (2 − 4x) + (2 − x/2)`. -/
theorem d64_exponents (x : ℚ) :
    -(1 / 2) * ((3 * x - 2) + 3 * (-2)) = 4 - 3 / 2 * x ∧
      -(1 / 2) * (3 * (3 * x - 2) + (2 - x)) = 2 - 4 * x ∧
      -(1 / 2) * (3 * (3 * x - 2) + (-2)) = (2 - 4 * x) + (2 - x / 2) ∧
      (x < 1 → -2 < 4 - 3 / 2 * x) := by
  refine ⟨by ring, by ring, by ring, fun h => by linarith⟩

/-- **Lemma 7.2**: for `k ∈ K`, `j ∈ {1, 2}`: `a_k < 2 ≤ a_j`, `b_j = −2 < b_k` give the hypotheses of (F4), and the
torque term of `jk` has exponent `−½(a_k + b_j) = 1 − a_k/2`. -/
theorem d64_F4 (ak aj bk : ℚ) (h1 : ak < 2) (h2 : 2 ≤ aj) (h3 : -2 < bk) :
    ak < aj ∧ -2 < bk ∧ ak + -2 < aj + bk ∧ -(1 / 2) * (ak + -2) = 1 - ak / 2 := by
  refine ⟨by linarith, h3, by linarith, by ring⟩

/-- **Lemma 7.1(c), (d)**: with `ω_jk = −2`, `e(Z_jk) = 3 − ζ_jk/2 > 2` when `ζ_jk < 2`. -/
theorem d64_Zjk (ζ : ℚ) : -(1 / 2) * (ζ + 3 * (-2)) = 3 - ζ / 2 ∧ (ζ < 2 → 2 < 3 - ζ / 2) := by
  refine ⟨by ring, fun h => by linarith⟩

/-! ## Lemma 7.6 -/

/-- The cube roots of unity: `x³ = 1` and `ω² + ω + 1 = 0` give `x ∈ {1, ω, ω²}`. -/
theorem cube_root_cases {K : Type*} [Field K] (ω x : K) (hω : ω ^ 2 + ω + 1 = 0) (hx : x ^ 3 = 1) :
    x = ω ^ 0 ∨ x = ω ^ 1 ∨ x = ω ^ 2 := by
  have h : (x - 1) * (x - ω) * (x - ω ^ 2) = 0 := by
    linear_combination hx + (-x ^ 2 + ω * x - ω + 1) * hω
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · left; rw [pow_zero]; exact sub_eq_zero.mp h
    · right; left; rw [pow_one]; exact sub_eq_zero.mp h
  · right; right; exact sub_eq_zero.mp h

/-- **Lemma 7.6**, the case `dim V = 3`: if `P_kl³ = u_k u_l` for `k ≠ l` with all `u_k ≠ 0` (the rank-one form of
`L diag(μ)⁻¹`), and `ξ` is not constant, a solution of `E_4(μ)` gives a pattern `ε` and a nonzero common zero `q` of
the forms `F_ε` (`q_k³ = u_k`, `P_kl = ε_kl q_k q_l`, `A_k = −β q_k²`). -/
theorem E4_noncollinear (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (μ ξ η : Fin 4 → ℂ) (P : Fin 4 → Fin 4 → ℂ)
    (hP : ∀ k l, P k l = P l k) (u : Fin 4 → ℂ) (hu : ∀ k, u k ≠ 0) (hPu : ∀ k l, k ≠ l → P k l ^ 3 = u k * u l)
    (hξeq : ∀ k, ∑ l, (if l = k then 0 else μ l * P k l ^ 3 * (ξ k - ξ l)) = 0)
    (hηeq : ∀ k, ∑ l, (if l = k then 0 else μ l * P k l ^ 3 * (η k - η l)) = 0)
    (hd : ∀ k l, k ≠ l → P k l ^ 2 * (ξ k - ξ l) * (η k - η l) = 1) (hξ : ∃ k l, ξ k ≠ ξ l) :
    ∃ (e : Fin 4 → Fin 4 → ℕ) (q : Fin 4 → ℂ), (∀ k l, e k l = e l k) ∧ q ≠ 0 ∧ K4.E4.FZero ω μ e q := by
  set α : Fin 4 → ℂ := fun l => μ l * u l with hα
  -- the equations of the bodies in the rank-one form
  have hS : ∀ (V : Fin 4 → ℂ) (k : Fin 4), ∑ l, (if l = k then 0 else μ l * P k l ^ 3 * (V k - V l)) =
      u k * (V k * ∑ l, α l - ∑ l, α l * V l) := by
    intro V k
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h
    · subst h; ring
    · rw [hPu k l (Ne.symm h)]; simp only [hα]; ring
  have hV : ∀ (V : Fin 4 → ℂ), (∀ k, ∑ l, (if l = k then 0 else μ l * P k l ^ 3 * (V k - V l)) = 0) →
      ∀ k, V k * ∑ l, α l = ∑ l, α l * V l := by
    intro V hV k
    have := hV k
    rw [hS V k] at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (hu k))
  obtain ⟨k0, l0, hkl0⟩ := hξ
  have hξV := hV ξ hξeq
  have hS0 : ∑ l, α l = 0 := by
    have h1 := hξV k0
    have h2 := hξV l0
    have : (ξ k0 - ξ l0) * ∑ l, α l = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hkl0)
  have hS1 : ∑ l, α l * ξ l = 0 := by have := hξV k0; rw [hS0, mul_zero] at this; exact this.symm
  have hS2 : ∑ l, α l * η l = 0 := by
    have := hV η hηeq k0; rw [hS0, mul_zero] at this; exact this.symm
  -- `Σ_l α_l d_kl = Σ_l α_l ξ_l η_l =: −β`
  set β : ℂ := -∑ l, α l * ξ l * η l with hβ
  have hdk : ∀ k, ∑ l, α l * ((ξ k - ξ l) * (η k - η l)) = -β := by
    intro k
    have : ∑ l, α l * ((ξ k - ξ l) * (η k - η l)) =
        ξ k * η k * ∑ l, α l - ξ k * ∑ l, α l * η l - η k * ∑ l, α l * ξ l + ∑ l, α l * ξ l * η l := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, hS0, hS1, hS2, hβ]
    ring
  -- cube roots `q_k³ = u_k`
  have hq : ∀ k, ∃ q : ℂ, q ^ 3 = u k := fun k => IsAlgClosed.exists_pow_nat_eq (u k) (by norm_num)
  choose q hq using hq
  have hq0 : ∀ k, q k ≠ 0 := fun k h => hu k (by rw [← hq k, h]; ring)
  -- `ε_kl = P_kl / (q_k q_l)` is a cube root of unity
  set ε : Fin 4 → Fin 4 → ℂ := fun k l => P k l / (q k * q l) with hε
  have hε3 : ∀ k l, k ≠ l → ε k l ^ 3 = 1 := by
    intro k l hkl
    simp only [hε, div_pow, mul_pow, hq, hPu k l hkl]
    exact div_self (mul_ne_zero (hu k) (hu l))
  have hεsymm : ∀ k l, ε k l = ε l k := fun k l => by simp only [hε]; rw [hP k l, mul_comm (q k)]
  have hPε : ∀ k l, P k l = ε k l * (q k * q l) := fun k l => by
    simp only [hε]; rw [div_mul_cancel₀ _ (mul_ne_zero (hq0 k) (hq0 l))]
  -- the exponents
  classical
  let e : Fin 4 → Fin 4 → ℕ := fun k l => if k = l then 0 else if ε k l = 1 then 0 else if ε k l = ω then 1 else 2
  have he : ∀ k l, k ≠ l → ω ^ e k l = ε k l := by
    intro k l hkl
    simp only [e, if_neg hkl]
    rcases cube_root_cases ω (ε k l) hω (hε3 k l hkl) with h | h | h
    · rw [pow_zero] at h; rw [if_pos h, pow_zero, h]
    · rw [pow_one] at h
      by_cases h1 : ε k l = 1
      · rw [if_pos h1, pow_zero, h1]
      · rw [if_neg h1, if_pos h, pow_one, h]
    · by_cases h1 : ε k l = 1
      · rw [if_pos h1, pow_zero, h1]
      · by_cases h2 : ε k l = ω
        · rw [if_neg h1, if_pos h2, pow_one, h2]
        · rw [if_neg h1, if_neg h2, h]
  have hesymm : ∀ k l, e k l = e l k := by
    intro k l
    simp only [e]
    by_cases hkl : k = l
    · rw [if_pos hkl, if_pos hkl.symm]
    · rw [if_neg hkl, if_neg (Ne.symm hkl), hεsymm k l]
  -- `A_k = −β q_k²`
  have hA : ∀ k, K4.E4.Aeps ω μ e q k = -β * q k ^ 2 := by
    intro k
    have h1 : ∀ l, α l * ((ξ k - ξ l) * (η k - η l)) =
        (if l = k then 0 else ω ^ e k l * μ l * q l) / q k ^ 2 := by
      intro l
      by_cases hlk : l = k
      · subst hlk; simp
      · rw [if_neg hlk, he k l (Ne.symm hlk)]
        have hd' := hd k l (Ne.symm hlk)
        rw [hPε k l] at hd'
        have hε3' := hε3 k l (Ne.symm hlk)
        have hd'' : ε k l ^ 2 * (q k ^ 2 * q l ^ 2 * ((ξ k - ξ l) * (η k - η l))) = 1 := by
          linear_combination hd'
        have hX : q k ^ 2 * q l ^ 2 * ((ξ k - ξ l) * (η k - η l)) = ε k l := by
          linear_combination ε k l * hd'' - q k ^ 2 * q l ^ 2 * ((ξ k - ξ l) * (η k - η l)) * hε3'
        simp only [hα]
        rw [← hq l, eq_div_iff (pow_ne_zero 2 (hq0 k))]
        linear_combination μ l * q l * hX
    have h2 : ∑ l, α l * ((ξ k - ξ l) * (η k - η l)) = K4.E4.Aeps ω μ e q k / q k ^ 2 := by
      rw [Finset.sum_congr rfl fun l _ => h1 l, ← Finset.sum_div]
      rfl
    rw [hdk k] at h2
    rw [eq_div_iff (pow_ne_zero 2 (hq0 k))] at h2
    linear_combination -h2
  refine ⟨e, q, hesymm, fun h => hq0 0 (by rw [h]; rfl), ?_, ?_⟩
  · intro j k _
    rw [hA j, hA k]
    ring
  · have : ∑ k, μ k * q k ^ 3 = ∑ l, α l := Finset.sum_congr rfl fun k _ => by rw [hq k]
    rw [this, hS0]

/-- `∏_j (if j = k then 1 else g j) = g l · ∏_j (if j = k ∨ j = l then 1 else g j)` for `l ≠ k`. -/
theorem prod_drop_one {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℂ) (k l : ι) (hlk : l ≠ k) :
    ∏ j, (if j = k then 1 else g j) = g l * ∏ j, (if j = k ∨ j = l then 1 else g j) := by
  rw [← Finset.mul_prod_erase univ (fun j => if j = k then 1 else g j) (Finset.mem_univ l),
    ← Finset.mul_prod_erase univ (fun j => if j = k ∨ j = l then 1 else g j) (Finset.mem_univ l)]
  simp only [if_neg hlk, or_true, if_true, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have hjl : j ≠ l := Finset.ne_of_mem_erase hj
  by_cases hjk : j = k
  · simp [hjk]
  · simp [hjk, hjl]

/-- **Lemma 7.6**, the case `dim V = 2`: if `η = λξ + θ` with `λ ≠ 0`, a solution of `E_4(μ)` gives an antisymmetric
sign pattern `σ` and a nonzero common zero `(ξ_2 − ξ_1 : ξ_3 − ξ_1 : ξ_4 − ξ_1)` of the forms `G_σ`
(`P_kl (ξ_k − ξ_l) = σ_kl κ`, `κ² = 1/λ`). -/
theorem E4_collinear (μ ξ η : Fin 4 → ℂ) (P : Fin 4 → Fin 4 → ℂ) (hP : ∀ k l, P k l = P l k) (lam θ : ℂ)
    (hlam : lam ≠ 0) (hηξ : ∀ k, η k = lam * ξ k + θ)
    (hξeq : ∀ k, ∑ l, (if l = k then 0 else μ l * P k l ^ 3 * (ξ k - ξ l)) = 0)
    (hd : ∀ k l, k ≠ l → P k l ^ 2 * (ξ k - ξ l) * (η k - η l) = 1) :
    ∃ σ : Fin 4 → Fin 4 → ℤ, (∀ k l, σ l k = -σ k l) ∧ (∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) ∧
      ∃ ξ' : Fin 3 → ℂ, ξ' ≠ 0 ∧ K4.E4.GZero μ σ ξ' := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ ^ 2 = 1 / lam := IsAlgClosed.exists_pow_nat_eq (1 / lam) (by norm_num)
  have hκ0 : κ ≠ 0 := by
    intro h
    have h1 : (1 : ℂ) / lam ≠ 0 := one_div_ne_zero hlam
    apply h1
    rw [← hκ, h]
    ring
  have hsq : ∀ k l, k ≠ l → (P k l * (ξ k - ξ l)) ^ 2 = κ ^ 2 := by
    intro k l hkl
    have h := hd k l hkl
    rw [hηξ k, hηξ l] at h
    rw [hκ, eq_div_iff hlam]
    linear_combination h
  have hdist : ∀ k l, k ≠ l → ξ k - ξ l ≠ 0 := by
    intro k l hkl h
    have := hd k l hkl
    rw [h] at this
    simp at this
  classical
  let σ : Fin 4 → Fin 4 → ℤ := fun k l => if k = l then 0 else if P k l * (ξ k - ξ l) = κ then 1 else -1
  have hσκ : ∀ k l, k ≠ l → P k l * (ξ k - ξ l) = (σ k l : ℂ) * κ := by
    intro k l hkl
    simp only [σ, if_neg hkl]
    by_cases h : P k l * (ξ k - ξ l) = κ
    · rw [if_pos h]; push_cast; rw [one_mul, h]
    · rw [if_neg h]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq k l hkl) with h' | h'
      · exact absurd h' h
      · push_cast; rw [h']; ring
  have hσ1 : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1 := by
    intro k l hkl
    simp only [σ, if_neg hkl]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hσanti : ∀ k l, σ l k = -σ k l := by
    intro k l
    by_cases hkl : k = l
    · subst hkl; simp [σ]
    · have h1 := hσκ k l hkl
      have h2 := hσκ l k (Ne.symm hkl)
      have h3 : P l k * (ξ l - ξ k) = -(P k l * (ξ k - ξ l)) := by rw [hP l k]; ring
      rw [h1, h2] at h3
      have h4 : ((σ l k : ℂ) + σ k l) * κ = 0 := by linear_combination h3
      have h5 : ((σ l k + σ k l : ℤ) : ℂ) = 0 := by
        push_cast
        exact (mul_eq_zero.mp h4).resolve_right hκ0
      have h6 : σ l k + σ k l = 0 := by exact_mod_cast h5
      linarith
  -- each `G_σ,k` vanishes at `ξ`
  have hG : ∀ k, K4.E4.Gsig μ σ ξ k = 0 := by
    intro k
    set D : ℂ := ∏ j, (if j = k then 1 else (ξ k - ξ j) ^ 2) with hD
    have hterm : ∀ l, (if l = k then 0 else (σ k l : ℂ) * μ l * ∏ j, (if j = k ∨ j = l then 1 else (ξ k - ξ j) ^ 2)) =
        D / κ ^ 3 * (if l = k then 0 else μ l * P k l ^ 3 * (ξ k - ξ l)) := by
      intro l
      by_cases hlk : l = k
      · simp [hlk]
      · rw [if_neg hlk, if_neg hlk]
        have hne : ξ k - ξ l ≠ 0 := hdist k l (Ne.symm hlk)
        have hPv : P k l = (σ k l : ℂ) * κ / (ξ k - ξ l) := by
          rw [eq_div_iff hne]; exact hσκ k l (Ne.symm hlk)
        have hσ3 : (σ k l : ℂ) ^ 3 = σ k l := by
          rcases hσ1 k l (Ne.symm hlk) with h | h <;> rw [h] <;> norm_num
        have hDl : D = (ξ k - ξ l) ^ 2 * ∏ j, (if j = k ∨ j = l then 1 else (ξ k - ξ j) ^ 2) :=
          prod_drop_one (fun j => (ξ k - ξ j) ^ 2) k l hlk
        rw [hDl, hPv]
        field_simp
        rw [hσ3]
    unfold K4.E4.Gsig
    rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, hξeq k, mul_zero]
  -- translate so that `ξ₁ = 0`
  refine ⟨σ, hσanti, hσ1, ![ξ 1 - ξ 0, ξ 2 - ξ 0, ξ 3 - ξ 0], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    exact hdist 1 0 (by decide) this
  · intro k
    have hξ' : (![0, ξ 1 - ξ 0, ξ 2 - ξ 0, ξ 3 - ξ 0] : Fin 4 → ℂ) = fun i => ξ i - ξ 0 := by
      funext i
      fin_cases i <;> simp
    have : (![0, (![ξ 1 - ξ 0, ξ 2 - ξ 0, ξ 3 - ξ 0] : Fin 3 → ℂ) 0, (![ξ 1 - ξ 0, ξ 2 - ξ 0, ξ 3 - ξ 0] : Fin 3 → ℂ) 1,
        (![ξ 1 - ξ 0, ξ 2 - ξ 0, ξ 3 - ξ 0] : Fin 3 → ℂ) 2] : Fin 4 → ℂ) = fun i => ξ i - ξ 0 := by
      rw [← hξ']
      rfl
    rw [this]
    have hT : K4.E4.Gsig μ σ (fun i => ξ i - ξ 0) k = K4.E4.Gsig μ σ ξ k := by
      unfold K4.E4.Gsig
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 1
      ring
    rw [hT, hG k]

/-! ## §7.3: the compact model of `C₄` -/

section C4

open K4.C4

/-- **§7.3**: equation (II) is (iii), `Σ_{l≠k} μ_l P_kl³ η_kl = c` with `η_kl = 1/(P_kl² (ξ_k − ξ_l))`, multiplied by
`∏_{l≠k} (ξ_k − ξ_l)` (for distinct `ξ` and nonzero `P`). -/
theorem II_of_iii {K : Type*} [Field K] (μ ξ : Fin 4 → K) (P : Fin 4 → Fin 4 → K) (c : K) (k : Fin 4)
    (hξ : ∀ l, l ≠ k → ξ k - ξ l ≠ 0) (hP0 : ∀ l, l ≠ k → P k l ≠ 0) :
    (∑ l ∈ univ.filter (· ≠ k), μ l * P k l ^ 3 * (1 / (P k l ^ 2 * (ξ k - ξ l))) - c) *
        ∏ l ∈ univ.filter (· ≠ k), (ξ k - ξ l) = eqIIZ μ ξ P c k := by
  unfold eqIIZ
  rw [sub_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlk : l ≠ k := (Finset.mem_filter.mp hl).2
  have hsplit : ∏ j ∈ univ.filter (· ≠ k), (ξ k - ξ j) =
      (ξ k - ξ l) * ∏ j ∈ univ.filter (fun j => j ≠ k ∧ j ≠ l), (ξ k - ξ j) := by
    rw [← Finset.mul_prod_erase _ _ hl]
    congr 1
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext j
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hsplit]
  have h1 := hξ l hlk
  have h2 := hP0 l hlk
  field_simp

/-- **§7.3**: equation (III) is `η_kl + η_ln + η_nk = 0` (`η = 1/a`) multiplied by `a_kl a_ln a_nk`. -/
theorem III_of_eta {K : Type*} [Field K] (ξ : Fin 4 → K) (P : Fin 4 → Fin 4 → K) (k l n : Fin 4)
    (h1 : aZ ξ P k l ≠ 0) (h2 : aZ ξ P l n ≠ 0) (h3 : aZ ξ P n k ≠ 0) :
    (1 / aZ ξ P k l + 1 / aZ ξ P l n + 1 / aZ ξ P n k) * (aZ ξ P k l * aZ ξ P l n * aZ ξ P n k) =
      eqIIIZ ξ P k l n := by
  unfold eqIIIZ
  field_simp

/-- **§7.3**: `ξ = (μ₃ s, μ₃ t, −μ₁ s − μ₂ t, 0)` satisfies `ξ_4 = 0` and `Σ_{k≤3} μ_k ξ_k = 0`. -/
theorem xiZ_centre {R : Type*} [CommRing R] (μ : Fin 4 → R) (s t : R) :
    xiZ μ s t 3 = 0 ∧ μ 0 * xiZ μ s t 0 + μ 1 * xiZ μ s t 1 + μ 2 * xiZ μ s t 2 = 0 := by
  simp only [xiZ]
  constructor
  · rfl
  · simp
    ring

/-- **§7.3**: when `μ₃ ≠ 0`, every solution of `ξ_4 = 0`, `Σ_{k≤3} μ_k ξ_k = 0` is of this form. -/
theorem xiZ_param {K : Type*} [Field K] (μ ξ : Fin 4 → K) (h3 : μ 2 ≠ 0) (hξ4 : ξ 3 = 0)
    (hc : μ 0 * ξ 0 + μ 1 * ξ 1 + μ 2 * ξ 2 = 0) : ξ = xiZ μ (ξ 0 / μ 2) (ξ 1 / μ 2) := by
  funext i
  fin_cases i
  · simp [xiZ]; field_simp
  · simp [xiZ]; field_simp
  · simp [xiZ]
    field_simp
    linear_combination hc
  · simp [xiZ, hξ4]

theorem xiZ_smul {R : Type*} [CommRing R] (μ : Fin 4 → R) (a s t : R) (i : Fin 4) :
    xiZ μ (a * s) (a * t) i = a * xiZ μ s t i := by
  fin_cases i <;> simp [xiZ] <;> ring

theorem prod_smul_sub {R : Type*} [CommRing R] (S : Finset (Fin 4)) (a : R) (x : Fin 4 → R) (k : Fin 4) :
    ∏ j ∈ S, (a * x k - a * x j) = a ^ S.card * ∏ j ∈ S, (x k - x j) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by ring

/-- **§7.3, bidegree `(1, 3)`** of (I): under `(s, t, P, c) ↦ (λ₁ s, λ₁ t, λ₂ P, λ₁⁻¹ λ₂ c)` it is multiplied by
`λ₁ λ₂³`. -/
theorem bideg_I {R : Type*} [CommRing R] (μ : Fin 4 → R) (s t a b : R) (P : Fin 6 → R) (k : Fin 4) :
    eqIZ μ (xiZ μ (a * s) (a * t)) (Pm fun i => b * P i) k = a * b ^ 3 * eqIZ μ (xiZ μ s t) (Pm P) k := by
  unfold eqIZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pm, xiZ_smul]
  ring

/-- **§7.3, bidegree `(2, 1)`** of (II). -/
theorem bideg_II {K : Type*} [Field K] (μ : Fin 4 → K) (s t a b c : K) (ha : a ≠ 0) (P : Fin 6 → K) (k : Fin 4) :
    eqIIZ μ (xiZ μ (a * s) (a * t)) (Pm fun i => b * P i) (b * c / a) k =
      a ^ 2 * b * eqIIZ μ (xiZ μ s t) (Pm P) c k := by
  have hc3 : ∀ k : Fin 4, (univ.filter (· ≠ k)).card = 3 := by decide
  have hc2 : ∀ k l : Fin 4, l ≠ k → (univ.filter (fun j => j ≠ k ∧ j ≠ l)).card = 2 := by decide
  unfold eqIIZ
  have e1 : ∀ l ∈ univ.filter (· ≠ k), ∏ j ∈ univ.filter (fun j => j ≠ k ∧ j ≠ l),
      (xiZ μ (a * s) (a * t) k - xiZ μ (a * s) (a * t) j) =
        a ^ 2 * ∏ j ∈ univ.filter (fun j => j ≠ k ∧ j ≠ l), (xiZ μ s t k - xiZ μ s t j) := by
    intro l hl
    simp only [xiZ_smul]
    rw [prod_smul_sub, hc2 k l (Finset.mem_filter.mp hl).2]
  have e2 : ∏ l ∈ univ.filter (· ≠ k), (xiZ μ (a * s) (a * t) k - xiZ μ (a * s) (a * t) l) =
      a ^ 3 * ∏ l ∈ univ.filter (· ≠ k), (xiZ μ s t k - xiZ μ s t l) := by
    simp only [xiZ_smul]
    rw [prod_smul_sub, hc3 k]
  rw [e2, Finset.sum_congr rfl fun l hl => by rw [e1 l hl], mul_sub, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pm]
    ring
  · field_simp

/-- **§7.3, bidegree `(2, 4)`** of (III). -/
theorem bideg_III {R : Type*} [CommRing R] (μ : Fin 4 → R) (s t a b : R) (P : Fin 6 → R) (k l n : Fin 4) :
    eqIIIZ (xiZ μ (a * s) (a * t)) (Pm fun i => b * P i) k l n = a ^ 2 * b ^ 4 * eqIIIZ (xiZ μ s t) (Pm P) k l n := by
  simp only [eqIIIZ, aZ, Pm, xiZ_smul]
  ring

end C4

end Lean6.Special.Hand
