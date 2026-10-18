import Mathlib

/-!
# Algebra inside the hand proofs of Section 6

* `rewrite_identity` (Lemma 6.2, `lem:rewrite`): `Σ_{j∈S} m_j m_o p_{jo}³(z_j w_o − z_o w_j) = m_o(z_o A_w − w_o A_z)
  = m_o(w_o B_z − z_o B_w)`.
* `binary_masses` (Lemma 6.3, `lem:binary`): from `m₅ẑ₅ + m₆ẑ₆ = 0`, `p̂_j² ẑ_j ŵ = −1` and `m₅p̂₅ = −m₆p̂₆`,
  `m₅³ + m₆³ = 0`; hence `m₅p̂₅ + m₆p̂₆ ≠ 0` for positive masses.
* `prop68_ratio`, `prop68_equal`, `prop68_branch` (Proposition 6.8, `prop:d81`): the algebra of the torques.
* `ttest_pair`, `ttest_dominant`, `ttest_reduction` (Lemma 6.17, `lem:Ttest`).
-/

namespace Lean6.Special.Hand

open Complex

/-! ## Lemma 6.2 -/

/-- **Lemma 6.2.** `q j` is `p_{jo} = p_{oj}`; `A_z = Σ_{j∈S} m_j Z_{oj}`, `Z_{oj} = p_{oj}³ (z_o − z_j)`, and likewise
`A_w`; `B_z = z_o − A_z`, `B_w = w_o − A_w`. -/
theorem rewrite_identity {R ι : Type*} [CommRing R] (S : Finset ι) (m z w q : ι → R) (mo zo wo : R) :
    (∑ j ∈ S, m j * mo * q j ^ 3 * (z j * wo - zo * w j)) =
        mo * (zo * (∑ j ∈ S, m j * (q j ^ 3 * (wo - w j))) - wo * (∑ j ∈ S, m j * (q j ^ 3 * (zo - z j)))) ∧
      (∑ j ∈ S, m j * mo * q j ^ 3 * (z j * wo - zo * w j)) =
        mo * (wo * (zo - ∑ j ∈ S, m j * (q j ^ 3 * (zo - z j))) -
          zo * (wo - ∑ j ∈ S, m j * (q j ^ 3 * (wo - w j)))) := by
  have h1 : (∑ j ∈ S, m j * mo * q j ^ 3 * (z j * wo - zo * w j)) =
      mo * (zo * (∑ j ∈ S, m j * (q j ^ 3 * (wo - w j))) - wo * (∑ j ∈ S, m j * (q j ^ 3 * (zo - z j)))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨h1, ?_⟩
  rw [h1]
  ring

/-! ## Lemma 6.3 -/

/-- **Lemma 6.3**, the algebra: `m₅ẑ₅ + m₆ẑ₆ = 0`, `p̂₅² ẑ₅ ŵ = −1`, `p̂₆² ẑ₆ ŵ = −1` and `m₅p̂₅ = −m₆p̂₆` give
`m₅³ + m₆³ = 0`. -/
theorem binary_masses {K : Type*} [Field K] (m5 m6 z5 z6 w p5 p6 : K) (h1 : m5 * z5 + m6 * z6 = 0)
    (h2 : p5 ^ 2 * z5 * w = -1) (h3 : p6 ^ 2 * z6 * w = -1) (h4 : m5 * p5 = -(m6 * p6)) : m5 ^ 3 + m6 ^ 3 = 0 := by
  have hz5 : z5 ≠ 0 := by
    intro h; rw [h] at h2; simp at h2
  have key : (m5 ^ 3 + m6 ^ 3) * z5 = 0 := by
    linear_combination m5 ^ 2 * h1 -
      m6 * (m5 ^ 2 * z6 * h2 - m6 ^ 2 * z5 * h3 - z5 * z6 * w * (m5 * p5 - m6 * p6) * h4)
  exact (mul_eq_zero.mp key).resolve_right hz5

/-- **Lemma 6.3** for positive masses: `m₅ p̂₅ + m₆ p̂₆ ≠ 0`. -/
theorem binary_ne_zero (m5 m6 : ℝ) (hm5 : 0 < m5) (hm6 : 0 < m6) (z5 z6 w p5 p6 : ℂ)
    (h1 : (m5 : ℂ) * z5 + m6 * z6 = 0) (h2 : p5 ^ 2 * z5 * w = -1) (h3 : p6 ^ 2 * z6 * w = -1) :
    (m5 : ℂ) * p5 + m6 * p6 ≠ 0 := by
  intro h
  have := binary_masses (m5 : ℂ) m6 z5 z6 w p5 p6 h1 h2 h3 (by linear_combination h)
  have h' : ((m5 ^ 3 + m6 ^ 3 : ℝ) : ℂ) = 0 := by push_cast; exact this
  have : m5 ^ 3 + m6 ^ 3 = 0 := by exact_mod_cast h'
  have : 0 < m5 ^ 3 + m6 ^ 3 := by positivity
  linarith

/-! ## Proposition 6.8 -/

/-- **Proposition 6.8**, first step: from `m₁ u₁/s₁ + m₂ u₂/s₂ = 0` with `s_k² = ŵ_k` and `m₁ŵ₁ = −m₂ŵ₂`
(`ŵ₁/ŵ₂ = −m₂/m₁`), `m₁³ u₁² = −m₂³ u₂²`, i.e. `(u₁/u₂)² = −m₂³/m₁³`. -/
theorem prop68_ratio {K : Type*} [Field K] (m1 m2 w1 w2 s1 s2 u1 u2 : K) (hs1 : s1 ^ 2 = w1) (hs2 : s2 ^ 2 = w2)
    (hs1' : s1 ≠ 0) (hs2' : s2 ≠ 0) (hw : m1 * w1 = -(m2 * w2)) (h : m1 * u1 / s1 + m2 * u2 / s2 = 0) :
    m1 ^ 3 * u1 ^ 2 = -(m2 ^ 3 * u2 ^ 2) := by
  have e : m1 * u1 * s2 = -(m2 * u2 * s1) := by
    field_simp at h
    linear_combination h
  have e2 : m1 ^ 2 * u1 ^ 2 * w2 = m2 ^ 2 * u2 ^ 2 * w1 := by
    rw [← hs1, ← hs2]
    linear_combination (m1 * u1 * s2 - m2 * u2 * s1) * e
  have hw2 : w2 ≠ 0 := by rw [← hs2]; exact pow_ne_zero 2 hs2'
  have e3 : (m1 ^ 3 * u1 ^ 2 + m2 ^ 3 * u2 ^ 2) * w2 = 0 := by
    linear_combination m1 * e2 + m2 ^ 2 * u2 ^ 2 * hw
  linear_combination (mul_eq_zero.mp e3).resolve_right hw2

/-- **Proposition 6.8**, second step: with positive masses and `|u₁| = |u₂| ≠ 0`, `m₁ = m₂` and `u₁ = ± i u₂`. -/
theorem prop68_equal (m1 m2 : ℝ) (hm1 : 0 < m1) (hm2 : 0 < m2) (u1 u2 : ℂ) (hu : ‖u1‖ = ‖u2‖) (hu2 : u2 ≠ 0)
    (h : (m1 : ℂ) ^ 3 * u1 ^ 2 = -((m2 : ℂ) ^ 3 * u2 ^ 2)) : m1 = m2 ∧ (u1 = I * u2 ∨ u1 = -(I * u2)) := by
  have hn := congrArg norm h
  simp only [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm1,
    abs_of_pos hm2, hu] at hn
  have hu2' : 0 < ‖u2‖ ^ 2 := by positivity
  have h3 : m1 ^ 3 = m2 ^ 3 := by
    have := mul_right_cancel₀ hu2'.ne' hn
    exact this
  have hm : m1 = m2 := (pow_left_inj₀ hm1.le hm2.le (by norm_num)).mp h3
  refine ⟨hm, ?_⟩
  rw [hm] at h
  have hm3 : ((m2 : ℂ)) ^ 3 ≠ 0 := by
    have : (m2 : ℂ) ≠ 0 := by exact_mod_cast hm2.ne'
    exact pow_ne_zero 3 this
  have h2 : u1 ^ 2 = -(u2 ^ 2) := by
    have := mul_left_cancel₀ hm3 (h.trans (by ring : -((m2 : ℂ) ^ 3 * u2 ^ 2) = (m2 : ℂ) ^ 3 * -(u2 ^ 2)))
    exact this
  have h4 : (u1 - I * u2) * (u1 + I * u2) = 0 := by
    linear_combination h2 - u2 ^ 2 * Complex.I_sq
  rcases mul_eq_zero.mp h4 with h5 | h5
  · left; linear_combination h5
  · right; linear_combination h5

/-- **Proposition 6.8**, third step: if `u_k = σ_k a + i τ_k b` with signs `σ_k, τ_k = ±1` and `a, b > 0`
(`a = m₆^{3/2}`, `b = m₅^{3/2}`), then `u₁ = ± i u₂` forces `a = b`. -/
theorem prop68_branch (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (σ1 τ1 σ2 τ2 : ℝ) (hσ1 : σ1 = 1 ∨ σ1 = -1)
    (hτ1 : τ1 = 1 ∨ τ1 = -1) (hσ2 : σ2 = 1 ∨ σ2 = -1) (hτ2 : τ2 = 1 ∨ τ2 = -1)
    (h : (σ1 * a + I * (τ1 * b) : ℂ) = I * (σ2 * a + I * (τ2 * b)) ∨
      (σ1 * a + I * (τ1 * b) : ℂ) = -(I * (σ2 * a + I * (τ2 * b)))) : a = b := by
  have hre : ∀ z w : ℂ, z = w → z.re = w.re := fun z w h => by rw [h]
  rcases h with h | h
  · have h1 := hre _ _ h
    simp at h1
    rcases hσ1 with rfl | rfl <;> rcases hτ2 with rfl | rfl <;> linarith
  · have h1 := hre _ _ h
    simp at h1
    rcases hσ1 with rfl | rfl <;> rcases hτ2 with rfl | rfl <;> linarith

/-! ## Lemma 6.17 -/

/-- **Lemma 6.17**, one group: with `ẑ₅ = c m₆`, `ẑ₆ = −c m₅` and `p̂_{jl}² ẑ_j X = −1`,
`m₅p̂₅ + m₆p̂₆ = m₅p̂₅ (1 + i s ρ)` for a sign `s`, `ρ = (m₆/m₅)^{3/2}`, and
`|m₅p̂₅ + m₆p̂₆|² = (m₅³ + m₆³)/(m₅ m₆ |c| |X|)` (the modulus `K' |X|^{-1/2}` of the proof). -/
theorem ttest_pair (m5 m6 : ℝ) (hm5 : 0 < m5) (hm6 : 0 < m6) (c X p5 p6 : ℂ) (hc : c ≠ 0) (hX : X ≠ 0)
    (h5 : p5 ^ 2 * (c * m6) * X = -1) (h6 : p6 ^ 2 * (-(c * m5)) * X = -1) :
    (∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      (m5 : ℂ) * p5 + m6 * p6 = m5 * p5 * (1 + I * s * ((Real.sqrt (m6 / m5)) ^ 3 : ℝ))) ∧
    ‖(m5 : ℂ) * p5 + m6 * p6‖ ^ 2 = (m5 ^ 3 + m6 ^ 3) / (m5 * m6 * ‖c‖ * ‖X‖) := by
  have hp5 : p5 ≠ 0 := by intro h; rw [h] at h5; simp at h5
  set r : ℝ := Real.sqrt (m6 / m5) with hr
  have hr2 : r ^ 2 = m6 / m5 := Real.sq_sqrt (by positivity)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  -- (p₆/p₅)² = −m₆/m₅
  have hq : (p6 / p5) ^ 2 = -((m6 : ℂ) / m5) := by
    have hm5' : (m5 : ℂ) ≠ 0 := by exact_mod_cast hm5.ne'
    have hcX : c * X ≠ 0 := mul_ne_zero hc hX
    have e : (p6 ^ 2 * m5 + p5 ^ 2 * m6) * (c * X) = 0 := by linear_combination h5 - h6
    have e' : p6 ^ 2 * m5 + p5 ^ 2 * m6 = 0 := (mul_eq_zero.mp e).resolve_right hcX
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hp5)]
    field_simp
    linear_combination e'
  have hq2 : (p6 / p5 - I * r) * (p6 / p5 + I * r) = 0 := by
    have : ((r : ℂ)) ^ 2 = (m6 : ℂ) / m5 := by exact_mod_cast hr2
    linear_combination hq + this - (r : ℂ) ^ 2 * Complex.I_sq
  have hrat : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ p6 = I * s * r * p5 := by
    rcases mul_eq_zero.mp hq2 with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      have : p6 / p5 = I * r := by linear_combination h
      field_simp at this
      push_cast
      linear_combination this
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have : p6 / p5 = -(I * r) := by linear_combination h
      field_simp at this
      push_cast
      linear_combination this
  obtain ⟨s, hs, hp6⟩ := hrat
  have hm5' : (m5 : ℂ) ≠ 0 := by exact_mod_cast hm5.ne'
  have hr3 : (m6 : ℂ) * r = m5 * ((r ^ 3 : ℝ) : ℂ) := by
    have h1 : r ^ 2 * m5 = m6 := by rw [hr2]; field_simp
    have hc2 : (r : ℂ) ^ 2 * m5 = m6 := by exact_mod_cast h1
    push_cast
    linear_combination (-(r : ℂ)) * hc2
  refine ⟨⟨s, hs, ?_⟩, ?_⟩
  · rw [hp6]
    linear_combination (I * s * p5) * hr3
  · -- the modulus
    rw [hp6]
    have hn5 : ‖p5‖ ^ 2 = 1 / (‖c‖ * m6 * ‖X‖) := by
      have := congrArg norm h5
      simp only [norm_mul, norm_pow, norm_neg, norm_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hm6] at this
      have hX' : 0 < ‖X‖ := norm_pos_iff.mpr hX
      have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
      field_simp
      linarith
    have hsn : ‖((s : ℝ) : ℂ)‖ = 1 := by rcases hs with rfl | rfl <;> simp
    have e : (m5 : ℂ) * p5 + m6 * (I * s * r * p5) = p5 * (m5 + I * (s * m6 * r)) := by ring
    rw [e, norm_mul, mul_pow, hn5]
    have : ‖(m5 : ℂ) + I * ((s * m6 * r : ℝ) : ℂ)‖ ^ 2 = m5 ^ 2 + (s * m6 * r) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have e2 : (m5 : ℂ) + I * (s * m6 * r) = (m5 : ℂ) + I * ((s * m6 * r : ℝ) : ℂ) := by push_cast; ring
    rw [e2, this]
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hX' : 0 < ‖X‖ := norm_pos_iff.mpr hX
    have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
    rw [mul_pow, mul_pow, hs2, hr2]
    field_simp
    try ring

/-- A sum of complex numbers with one dominant term is not zero. -/
theorem sum_ne_zero_of_dominant {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℂ) (i0 : ι)
    (h : ∑ i ∈ Finset.univ.erase i0, ‖w i‖ < ‖w i0‖) : ∑ i, w i ≠ 0 := by
  intro h0
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at h0
  have : w i0 = -∑ i ∈ Finset.univ.erase i0, w i := by linear_combination h0
  have h2 := norm_sum_le (Finset.univ.erase i0) w
  rw [this, norm_neg] at h
  linarith

/-- **Lemma 6.17(a)**: if `m_k |X_k|^{-1/2} > Σ_{l≠k} m_l |X_l|^{-1/2}` for some `k`, then
`Σ_{j∈{5,6}, l} m_j m_l p̂_{jl} ≠ 0`, for every choice of the `p̂_{jl}` with `p̂_{5l}² ẑ₅ X_l = −1`,
`p̂_{6l}² ẑ₆ X_l = −1`, `ẑ₅ = c m₆`, `ẑ₆ = −c m₅`, and all `m₅, m₆ > 0`. -/
theorem ttest_dominant {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℝ) (hm : ∀ l, 0 < m l) (m5 m6 : ℝ)
    (hm5 : 0 < m5) (hm6 : 0 < m6) (c : ℂ) (hc : c ≠ 0) (X p5 p6 : ι → ℂ) (hX : ∀ l, X l ≠ 0)
    (h5 : ∀ l, p5 l ^ 2 * (c * m6) * X l = -1) (h6 : ∀ l, p6 l ^ 2 * (-(c * m5)) * X l = -1) (k : ι)
    (hk : ∑ l ∈ Finset.univ.erase k, m l / Real.sqrt ‖X l‖ < m k / Real.sqrt ‖X k‖) :
    ∑ l, (m l : ℂ) * (m5 * p5 l + m6 * p6 l) ≠ 0 := by
  set K : ℝ := Real.sqrt ((m5 ^ 3 + m6 ^ 3) / (m5 * m6 * ‖c‖)) with hK
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hK0 : 0 < K := Real.sqrt_pos.mpr (by positivity)
  have hnorm : ∀ l, ‖(m l : ℂ) * (m5 * p5 l + m6 * p6 l)‖ = K * (m l / Real.sqrt ‖X l‖) := by
    intro l
    have h2 := (ttest_pair m5 m6 hm5 hm6 c (X l) (p5 l) (p6 l) hc (hX l) (h5 l) (h6 l)).2
    have hX' : 0 < ‖X l‖ := norm_pos_iff.mpr (hX l)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hm l)]
    have e : ‖(m5 : ℂ) * p5 l + m6 * p6 l‖ = K / Real.sqrt ‖X l‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), h2, hK, ← Real.sqrt_div' _ hX'.le]
      congr 1
      field_simp
    rw [e]
    ring
  apply sum_ne_zero_of_dominant _ k
  simp only [hnorm]
  rw [← Finset.mul_sum]
  exact mul_lt_mul_of_pos_left hk hK0

/-- **Lemma 6.17(b)**, the reduction: with fixed square roots `w_l² = X_l` and `κ² (c m₆) = −1`, every choice of the
`p̂_{jl}` gives signs `ε_l, s_l = ±1` with `Σ_l m_l (m₅p̂_{5l} + m₆p̂_{6l}) = m₅ κ Σ_l ε_l β_l (1 + i s_l ρ)`,
`β_l = m_l / w_l`, `ρ = (m₆/m₅)^{3/2}`. -/
theorem ttest_reduction {ι : Type*} [Fintype ι] (m : ι → ℝ) (m5 m6 : ℝ) (hm5 : 0 < m5) (hm6 : 0 < m6) (c κ : ℂ)
    (hc : c ≠ 0) (hκ : κ ^ 2 * (c * m6) = -1) (X w p5 p6 : ι → ℂ) (hw : ∀ l, w l ^ 2 = X l) (hX : ∀ l, X l ≠ 0)
    (h5 : ∀ l, p5 l ^ 2 * (c * m6) * X l = -1) (h6 : ∀ l, p6 l ^ 2 * (-(c * m5)) * X l = -1) :
    ∃ ε s : ι → ℝ, (∀ l, ε l = 1 ∨ ε l = -1) ∧ (∀ l, s l = 1 ∨ s l = -1) ∧
      ∑ l, (m l : ℂ) * (m5 * p5 l + m6 * p6 l) =
        m5 * κ * ∑ l, (ε l : ℂ) * (m l / w l) * (1 + I * s l * ((Real.sqrt (m6 / m5)) ^ 3 : ℝ)) := by
  have hw0 : ∀ l, w l ≠ 0 := fun l h => hX l (by rw [← hw l, h]; ring)
  have hsgn : ∀ l, ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ p5 l = e * κ / w l := by
    intro l
    have : (p5 l * w l - κ) * (p5 l * w l + κ) = 0 := by
      have hcm : c * (m6 : ℂ) ≠ 0 := mul_ne_zero hc (by exact_mod_cast hm6.ne')
      have e1 : (p5 l * w l) ^ 2 * (c * m6) = κ ^ 2 * (c * m6) := by
        rw [mul_pow, hw l, hκ]; linear_combination h5 l
      have e2 : (p5 l * w l) ^ 2 = κ ^ 2 := mul_right_cancel₀ hcm e1
      linear_combination e2
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨1, Or.inl rfl, by field_simp [hw0 l]; push_cast; linear_combination h⟩
    · exact ⟨-1, Or.inr rfl, by field_simp [hw0 l]; push_cast; linear_combination h⟩
  choose ε hε hp5 using hsgn
  have hpair : ∀ l, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      (m5 : ℂ) * p5 l + m6 * p6 l = m5 * p5 l * (1 + I * s * ((Real.sqrt (m6 / m5)) ^ 3 : ℝ)) :=
    fun l => (ttest_pair m5 m6 hm5 hm6 c (X l) (p5 l) (p6 l) hc (hX l) (h5 l) (h6 l)).1
  choose s hs hps using hpair
  refine ⟨ε, s, hε, hs, ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hps l, hp5 l]
  field_simp [hw0 l]

end Lean6.Special.Hand
