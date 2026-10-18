import Mathlib

/-!
# Computations inside the hand proofs of Section 6

The items of `Hand/Identities.lean` and `Hand/Systems.lean` (Lemmas 6.2, 6.3, Proposition 6.8, Lemma 6.17, the torque
identity of §6.7) are not repeated here.

* Lemma 6.1 (`lem:common`): `F1_exp`, `F1_coeff`, `F2_exp`, `F4_exp`, `F4_coeff`.
* Propositions 6.4, 6.7, 6.8 and Theorem 6.5, the exponent comparisons: `d90_F4`, `d90_a4`, `d90_exponents`,
  `d89_sum_zero`, `d89_F4`, `d89_torque_exponents`, `d82_exponents`, `d81_exponents`.
* Lemma 6.9 (`lem:three`): `shape_positions`, `shape_positions_unique` (`z_k = ℓ_k(τ)/M`), `lagrange_p3`
  (`L + I = u μᵀ` gives `p_kl³ = 1/M`), `lagrange_quadratic`, `lagrange_quadratic_j` (the distance equation of `23`),
  `collinear_p`, `collinear_force`, `collinear_shape` (the collinear case).
* Lemma 6.11 and Theorem 6.12: `cross_square` (`c_jl² = κ m_j² m_l² Λ_j(τ) Λ_l(τ′)`), `torque_lead_coeff`.
* Remark 6.14: `split_signed_sum`.
* Theorem 6.15: `d93_signs`, `Phi3_product`, `Phi3_zero_of_signed`, `d93_to_Y`, `d93_Phi3_zero`.
-/

namespace Lean6.Special.Hand

open Finset

/-! ## Lemma 6.1 -/

/-- **(F1)**: on a `z`-stroke `ζ = 3x − 2`; if `x > 0` then `ζ > −2`. -/
theorem F1_exp (x : ℚ) (hx : 0 < x) : -2 < 3 * x - 2 := by linarith

/-- **(F1)**: the coefficient of exponent `−2` in `Σ_k m_k z_k = 0`, when the bodies of `A` have one leading
coefficient `c ≠ 0`, is `c Σ_{k∈A} m_k ≠ 0` (positive masses). -/
theorem F1_coeff {ι : Type*} (A : Finset ι) (hA : A.Nonempty) (m : ι → ℝ) (hm : ∀ k, 0 < m k) (c : ℂ) (hc : c ≠ 0) :
    ∑ k ∈ A, (m k : ℂ) * c ≠ 0 := by
  rw [← Finset.sum_mul]
  refine mul_ne_zero ?_ hc
  have hpos : (0 : ℝ) < ∑ k ∈ A, m k := Finset.sum_pos (fun k _ => hm k) hA
  have h' : ((∑ k ∈ A, m k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast at h'
  exact h'

/-- **(F2)**: `e(W_kl) = −½(3ζ_kl + ω_kl)` is `2` on the pairs of `A` (`ζ = −2`, `ω = 2`) and at least `2` on the
pairs with `ζ = −2`, `ω ≤ 2`. -/
theorem F2_exp (ω : ℚ) (hω : ω ≤ 2) : -(1 / 2) * (3 * (-2) + 2) = (2 : ℚ) ∧ 2 ≤ -(1 / 2) * (3 * (-2) + ω) := by
  constructor
  · norm_num
  · linarith

/-- **(F4)**, exponents: with `ζ_jl = a_j`, `ω_jl = b_l` and `e(p_jl) = −½(a_j + b_l)`, the term `p_jl³ z_j w_l` has
exponent `−½(a_j + b_l)`, and `p_jl³ z_l w_j` has a larger one when `a_l + b_j > a_j + b_l`. -/
theorem F4_exp (aj al bj bl : ℚ) (h : aj + bl < al + bj) :
    3 * (-(1 / 2) * (aj + bl)) + aj + bl = -(1 / 2) * (aj + bl) ∧
      -(1 / 2) * (aj + bl) < 3 * (-(1 / 2) * (aj + bl)) + al + bj := by
  constructor <;> linarith

/-- **(F4)**, coefficients: the distance equation at exponent `0`, `p̂² ẑ_j (−ŵ_l) = 1`, gives `p̂² ẑ_j ŵ_l = −1`; the
term `p³ z_j w_l` has leading coefficient `p̂³ ẑ_j ŵ_l = −p̂`, and the torque term `m_j m_l p³ z_j w_l` has `−m_j m_l p̂`. -/
theorem F4_coeff {K : Type*} [Field K] (p zj wl mj ml : K) (hd : p ^ 2 * zj * (-wl) = 1) :
    p ^ 2 * zj * wl = -1 ∧ p ^ 3 * zj * wl = -p ∧ mj * ml * (p ^ 3 * zj * wl) = -(mj * ml * p) := by
  have h1 : p ^ 2 * zj * wl = -1 := by linear_combination -hd
  exact ⟨h1, by linear_combination p * h1, by linear_combination mj * ml * p * h1⟩

/-! ## Propositions 6.4, 6.7, 6.8 and Theorem 6.5: exponent comparisons -/

/-- **Proposition 6.4**: `a_j < 2 ≤ a_l` and `b_l < 2 ≤ b_j` give the hypotheses of (F4). -/
theorem d90_F4 (aj al bj bl : ℚ) (h1 : aj < 2) (h2 : 2 ≤ al) (h3 : bl < 2) (h4 : 2 ≤ bj) :
    aj < al ∧ bl < bj ∧ aj + bl < al + bj := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Proposition 6.4**: if `a_4 ≥ 2` (and `a_2 ≥ 2`), then `ζ_42 ≥ min(a_4, a_2) ≥ 2`, so `ζ_42 = 2` by (O1). -/
theorem d90_a4 (a4 a2 ζ : ℚ) (h4 : 2 ≤ a4) (h2 : 2 ≤ a2) (hmin : min a4 a2 ≤ ζ) (hle : ζ ≤ 2) : ζ = 2 := by
  have : 2 ≤ min a4 a2 := le_min h4 h2
  linarith

/-- **Proposition 6.4**: with `E(a, b) = −½(a + b)`, `a_5 = a_6 = −2`, `b_2 = b_3 = −2` and `−2 < a_4, b_1 < 2`, the
least exponent `E_41` of the torque `T_A` is attained by the single term of the pair `41`. -/
theorem d90_exponents (a4 b1 : ℚ) (ha1 : -2 < a4) (ha2 : a4 < 2) (hb1 : -2 < b1) (hb2 : b1 < 2) :
    -(1 / 2) * (a4 + b1) < -(1 / 2) * (a4 + -2) ∧ -(1 / 2) * (a4 + b1) < -(1 / 2) * (-2 + b1) ∧
      -(1 / 2) * (a4 + b1) < -(1 / 2) * ((-2 : ℚ) + -2) ∧
      -(1 / 2) * (a4 + -2) = 1 - a4 / 2 ∧ -(1 / 2) * (-2 + b1) = 1 - b1 / 2 ∧
      -(1 / 2) * ((-2 : ℚ) + -2) = 2 := by
  refine ⟨by linarith, by linarith, by linarith, by ring, by ring, by norm_num⟩

/-- **Theorem 6.5**, `a_1 + b_1 = 0`: for `−2 < a_1, b_1 < 2` the exponents `1 − a_1/2`, `1 − b_1/2` of the terms of
`12, 13, 15, 16` in `U` are positive, and that of `14`, `−½(a_1 + b_1)`, is negative when `a_1 + b_1 > 0`. -/
theorem d89_sum_zero (a1 b1 : ℚ) (ha : a1 < 2) (hb : b1 < 2) :
    0 < 1 - a1 / 2 ∧ 0 < 1 - b1 / 2 ∧ (0 < a1 + b1 → -(1 / 2) * (a1 + b1) < 0) := by
  refine ⟨by linarith, by linarith, fun h => by linarith⟩

/-- **Theorem 6.5**: the pairs `(j, 1)`, `j = 5, 6`, satisfy (F4): `a_j = −2 < a_1`, `b_1 < 2 ≤ b_j` and
`a_1 + b_j > −2 + b_1`. -/
theorem d89_F4 (a1 b1 bj : ℚ) (ha : -2 < a1) (hb : b1 < 2) (hbj : 2 ≤ bj) : -2 < a1 ∧ b1 < bj ∧ -2 + b1 < a1 + bj := by
  refine ⟨ha, by linarith, by linarith⟩

/-- **Theorem 6.5**, the torque of `{5, 6}`: with `a_1 + b_1 = 0` and `−2 < a_1 < 2`: `1 − b_1/2 = 1 + a_1/2`,
`e(Z_41) = −½(a_1 + 3b_1) = a_1`, and `min(2 + a_1, 4)` and `2` exceed `1 + a_1/2`. -/
theorem d89_torque_exponents (a1 b1 : ℚ) (hab : a1 + b1 = 0) (ha : -2 < a1) (ha' : a1 < 2) :
    1 - b1 / 2 = 1 + a1 / 2 ∧ -(1 / 2) * (a1 + 3 * b1) = a1 ∧ 1 + a1 / 2 < min (2 + a1) 4 ∧ 1 + a1 / 2 < 2 := by
  refine ⟨by linarith, by linarith, lt_min (by linarith) (by linarith), by linarith⟩

/-- **Proposition 6.7**: from `2x_12 = a_1 + ω_12 ≤ 0`, `ω_12 ≥ b` and `a_1 + b ≥ 0`: `a_1 = −b`, `ω_12 = b`,
`e(Z_21) = −½(ζ_12 + 3ω_12) = −b` (with `ζ_12 = a_1`), and in the `z`-equation of body `2` the exponent `−b` is below
`2` and below `1 − 3b/2` (`−2 < b < 2`); also `1 − b/2 < 2` for the terms of the torque. -/
theorem d82_exponents (a1 b ω12 : ℚ) (hb : -2 < b) (hb' : b < 2) (h2x : a1 + ω12 ≤ 0) (hω : b ≤ ω12)
    (hge : 0 ≤ a1 + b) :
    a1 = -b ∧ ω12 = b ∧ -(1 / 2) * (a1 + 3 * ω12) = -b ∧ -b < 2 ∧ -b < 1 - 3 / 2 * b ∧ 1 - b / 2 < 2 := by
  have h1 : a1 = -b := by linarith
  have h2 : ω12 = b := by linarith
  refine ⟨h1, h2, by rw [h1, h2]; ring, by linarith, by linarith, by linarith⟩

/-- **Proposition 6.8**, the case analysis of the pair `12`. -/
theorem d81_exponents (a b ζ ω : ℚ) :
    (a = 1 - 3 / 2 * b → a + b ≤ 0 → 2 ≤ b) ∧
      (1 - 3 / 2 * b ≤ -(1 / 2) * (a + 3 * b) → a ≤ -2) ∧
      (a = -(1 / 2) * (ζ + 3 * ω) → b = -(1 / 2) * (3 * ζ + ω) → a + b = -4 * ((ζ + ω) / 2)) ∧
      (-2 < a → a < 2 → a < 1 + 3 / 2 * a ∧ a < 3 - a / 2) := by
  refine ⟨fun h1 h2 => by linarith, fun h => by linarith, fun h1 h2 => by rw [h1, h2]; ring,
    fun h1 h2 => ⟨by linarith, by linarith⟩⟩

/-! ## Lemma 6.9 -/

/-- **§6.4**: with the slice `z_1 − z_2 = 1`, the shape `τ = z_1 − z_3` and the centre of mass, the positions are
`z_k = ℓ_k(τ)/M`, `ℓ_1 = μ_2 + μ_3 τ`, `ℓ_2 = ℓ_1 − M`, `ℓ_3 = ℓ_1 − Mτ`. -/
theorem shape_positions {K : Type*} [Field K] (μ1 μ2 μ3 t : K) (hM : μ1 + μ2 + μ3 ≠ 0) :
    (μ2 + μ3 * t) / (μ1 + μ2 + μ3) - (μ2 + μ3 * t - (μ1 + μ2 + μ3)) / (μ1 + μ2 + μ3) = 1 ∧
      (μ2 + μ3 * t) / (μ1 + μ2 + μ3) - (μ2 + μ3 * t - (μ1 + μ2 + μ3) * t) / (μ1 + μ2 + μ3) = t ∧
      μ1 * ((μ2 + μ3 * t) / (μ1 + μ2 + μ3)) + μ2 * ((μ2 + μ3 * t - (μ1 + μ2 + μ3)) / (μ1 + μ2 + μ3)) +
        μ3 * ((μ2 + μ3 * t - (μ1 + μ2 + μ3) * t) / (μ1 + μ2 + μ3)) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The positions are determined by the slice, the shape and the centre of mass. -/
theorem shape_positions_unique {K : Type*} [Field K] (μ1 μ2 μ3 t z1 z2 z3 : K) (hM : μ1 + μ2 + μ3 ≠ 0)
    (h12 : z1 - z2 = 1) (h13 : z1 - z3 = t) (hc : μ1 * z1 + μ2 * z2 + μ3 * z3 = 0) :
    z1 = (μ2 + μ3 * t) / (μ1 + μ2 + μ3) ∧ z2 = (μ2 + μ3 * t - (μ1 + μ2 + μ3)) / (μ1 + μ2 + μ3) ∧
      z3 = (μ2 + μ3 * t - (μ1 + μ2 + μ3) * t) / (μ1 + μ2 + μ3) := by
  have hz1 : (μ1 + μ2 + μ3) * z1 = μ2 + μ3 * t := by linear_combination hc + μ2 * h12 + μ3 * h13
  have e1 : z1 = (μ2 + μ3 * t) / (μ1 + μ2 + μ3) := by rw [eq_div_iff hM]; linear_combination hz1
  refine ⟨e1, ?_, ?_⟩
  · rw [eq_div_iff hM]; linear_combination hz1 - (μ1 + μ2 + μ3) * h12
  · rw [eq_div_iff hM]; linear_combination hz1 - (μ1 + μ2 + μ3) * h13

/-- **Lemma 6.9**, the Lagrange case: if `L + I = u μᵀ`, where `L` has the entries `μ_l P_kl` off the diagonal
(`P_kl = p_kl³`) and zero row sums, and `M = Σ μ_l ≠ 0`, then `u_k = 1/M` and `p_kl³ = 1/M` for `k ≠ l` (`μ_l ≠ 0`). -/
theorem lagrange_p3 {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] (μ : ι → K) (P : ι → ι → K) (u : ι → K)
    (hM : ∑ l, μ l ≠ 0)
    (hL : ∀ k l, (if k = l then 1 - ∑ j ∈ univ.erase k, μ j * P k j else μ l * P k l) = u k * μ l) :
    (∀ k, u k = 1 / ∑ l, μ l) ∧ ∀ k l, k ≠ l → μ l ≠ 0 → P k l = 1 / ∑ j, μ j := by
  have hu : ∀ k, u k = 1 / ∑ l, μ l := by
    intro k
    have hsum : ∑ l, (if k = l then 1 - ∑ j ∈ univ.erase k, μ j * P k j else μ l * P k l) = u k * ∑ l, μ l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => hL k l
    have hrow : ∑ l, (if k = l then 1 - ∑ j ∈ univ.erase k, μ j * P k j else μ l * P k l) = 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), if_pos rfl]
      have : ∑ l ∈ univ.erase k, (if k = l then 1 - ∑ j ∈ univ.erase k, μ j * P k j else μ l * P k l) =
          ∑ l ∈ univ.erase k, μ l * P k l :=
        Finset.sum_congr rfl fun l hl => if_neg (Finset.ne_of_mem_erase hl).symm
      rw [this]
      ring
    rw [hrow] at hsum
    rw [eq_div_iff hM]
    exact hsum.symm
  refine ⟨hu, fun k l hkl hμ => ?_⟩
  have h := hL k l
  rw [if_neg hkl, hu k] at h
  have : μ l * P k l = μ l * (1 / ∑ j, μ j) := by rw [h]; ring
  exact mul_left_cancel₀ hμ this

/-- **Lemma 6.9**, the distance equation of `23` in the Lagrange case: with `z_12 = 1`, `z_13 = τ`, `w_12 = R_12`,
`w_13 = R_13/τ` and `z_23 w_23 = R_23` (`R_kl = p_kl^{−2}`), `R_12 τ² − (R_12 + R_13 − R_23)τ + R_13 = 0`. -/
theorem lagrange_quadratic {K : Type*} [Field K] (τ R12 R13 R23 : K) (hτ : τ ≠ 0) :
    (τ - 1) * (R13 / τ - R12) = R23 ↔ R12 * τ ^ 2 - (R12 + R13 - R23) * τ + R13 = 0 := by
  have key : τ * ((τ - 1) * (R13 / τ - R12) - R23) = -(R12 * τ ^ 2 - (R12 + R13 - R23) * τ + R13) := by
    field_simp
    ring
  constructor
  · intro h
    have : τ * ((τ - 1) * (R13 / τ - R12) - R23) = 0 := by rw [h, sub_self, mul_zero]
    rw [key, neg_eq_zero] at this
    exact this
  · intro h
    have : τ * ((τ - 1) * (R13 / τ - R12) - R23) = 0 := by rw [key, h, neg_zero]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hτ)

/-- **Lemma 6.9**: with `R_13 = R_12 j^b` and `R_23 = R_12 j^c` (`R_12 ≠ 0`), the quadratic becomes
`t² − (1 + j^b − j^c) t + j^b`. -/
theorem lagrange_quadratic_j {K : Type*} [Field K] (τ R12 jb jc : K) (hR : R12 ≠ 0) :
    R12 * τ ^ 2 - (R12 + R12 * jb - R12 * jc) * τ + R12 * jb = 0 ↔ τ ^ 2 - (1 + jb - jc) * τ + jb = 0 := by
  have e : R12 * τ ^ 2 - (R12 + R12 * jb - R12 * jc) * τ + R12 * jb = R12 * (τ ^ 2 - (1 + jb - jc) * τ + jb) := by
    ring
  rw [e, mul_eq_zero, or_iff_right hR]

/-- **Lemma 6.9**, the collinear case: `w = λ z` and the distance equation give `(p_kl z_kl)² = 1/λ = κ²`, so
`p_kl z_kl = ±κ`. -/
theorem collinear_p {K : Type*} [Field K] (p zkl lam κ : K) (hd : p ^ 2 * zkl * (lam * zkl) = 1)
    (hκ : κ ^ 2 * lam = 1) : p * zkl = κ ∨ p * zkl = -κ := by
  have hlam : lam ≠ 0 := by
    intro h
    rw [h, mul_zero] at hκ
    exact zero_ne_one hκ
  have : (p * zkl) ^ 2 = κ ^ 2 := by
    apply mul_right_cancel₀ hlam
    linear_combination hd - hκ
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

/-- **Lemma 6.9**, the collinear case: with `p_kl = σ_kl κ / z_kl` (`σ = ±1`), the force `μ_l p_kl³ z_kl` is
`κ³ σ_kl μ_l z_kl^{−2}`. -/
theorem collinear_force {K : Type*} [Field K] (μl zkl κ σ : K) (hσ : σ = 1 ∨ σ = -1) (hz : zkl ≠ 0) :
    μl * (σ * κ / zkl) ^ 3 * zkl = κ ^ 3 * (σ * μl / zkl ^ 2) := by
  rcases hσ with rfl | rfl <;> field_simp <;> ring

/-- **Lemma 6.9**, the collinear case: `z_k = κ³ F_k`, `z_12 = 1` and `z_23 = x` give `x(F_1 − F_2) = F_2 − F_3`. -/
theorem collinear_shape {K : Type*} [Field K] (κ F1 F2 F3 x : K) (h12 : κ ^ 3 * F1 - κ ^ 3 * F2 = 1)
    (h23 : κ ^ 3 * F2 - κ ^ 3 * F3 = x) : x * (F1 - F2) = F2 - F3 := by
  linear_combination (F2 - F3) * h12 - (F1 - F2) * h23

/-! ## Lemma 6.11 and Theorem 6.12 -/

/-- **Theorem 6.12**: with `ẑ_j = s ℓ_j(τ)/M_A`, `ŵ_l = s′ ℓ_l(τ′)/M_B` and `p̂_jl² ẑ_j ŵ_l = −1`, the number
`c_jl = m_j m_l p̂_jl` satisfies `c_jl² = κ m_j² m_l² Λ_j(τ) Λ_l(τ′)` with
`κ = −M_A M_B / (s s′ ∏ℓ_j(τ) ∏ℓ_l(τ′))`, where `∏ℓ(τ) = ℓ_j Λ_j` and `∏ℓ(τ′) = ℓ_l Λ_l`. -/
theorem cross_square {K : Type*} [Field K] (mj ml s s' MA MB lj ll Λj Λl p : K)
    (hs : s ≠ 0) (hs' : s' ≠ 0) (hMA : MA ≠ 0) (hMB : MB ≠ 0) (hlj : lj ≠ 0) (hll : ll ≠ 0)
    (hΛj : Λj ≠ 0) (hΛl : Λl ≠ 0) (hd : p ^ 2 * (s * lj / MA) * (s' * ll / MB) = -1) :
    (mj * ml * p) ^ 2 = -(MA * MB) / (s * s' * (lj * Λj) * (ll * Λl)) * mj ^ 2 * ml ^ 2 * Λj * Λl := by
  have hp2 : p ^ 2 = -(MA * MB) / (s * s' * lj * ll) := by
    rw [eq_div_iff (by positivity)]
    field_simp at hd
    linear_combination hd
  rw [mul_pow, mul_pow, hp2]
  field_simp

/-- **Lemma 6.11(d)**: by (F4) each pair of `A × B` contributes `−m_j m_l p̂_jl` to the coefficient of exponent `2` of
`T_A`. -/
theorem torque_lead_coeff {ι κ R : Type*} [CommRing R] (A : Finset ι) (B : Finset κ) (m : ι → R) (m' : κ → R)
    (p : ι → κ → R) : ∑ j ∈ A, ∑ l ∈ B, -(m j * m' l * p j l) = -∑ j ∈ A, ∑ l ∈ B, m j * m' l * p j l := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_neg_distrib]

/-! ## Remark 6.14 -/

/-- **Remark 6.14**: a sign matrix `ε_jl = δ_j η_l` splits the signed sum into a product. -/
theorem split_signed_sum {ι κ R : Type*} [CommRing R] (s : Finset ι) (t : Finset κ) (δ a : ι → R) (η b : κ → R) :
    ∑ j ∈ s, ∑ l ∈ t, (δ j * η l) * (a j * b l) = (∑ j ∈ s, δ j * a j) * (∑ l ∈ t, η l * b l) := by
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

/-! ## Theorem 6.15 -/

/-- **Theorem 6.15**: `Σ_l m_l p̂_4l = 0` with `p̂_4l² ẑ_4 ŵ_l = −1` gives `Σ_l ε_l m_l ŵ_l^{−1/2} = 0` for some signs,
for any choice of square roots `r_l² = ŵ_l` (and `c² ẑ_4 = −1`). -/
theorem d93_signs {ι K : Type*} [Field K] (B : Finset ι) (m p r w : ι → K) (z c : K) (hc : c ^ 2 * z = -1)
    (hr : ∀ l ∈ B, r l ^ 2 = w l) (hr0 : ∀ l ∈ B, r l ≠ 0) (hp : ∀ l ∈ B, p l ^ 2 * z * w l = -1)
    (hsum : ∑ l ∈ B, m l * p l = 0) :
    ∃ ε : ι → K, (∀ l ∈ B, ε l = 1 ∨ ε l = -1) ∧ ∑ l ∈ B, ε l * m l / r l = 0 := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  refine ⟨fun l => p l * r l / c, fun l hl => ?_, ?_⟩
  · have h1 := hp l hl
    rw [← hr l hl] at h1
    have hz : z ≠ 0 := by
      intro h
      rw [h, mul_zero] at hc
      norm_num at hc
    have h2 : (p l * r l) ^ 2 = c ^ 2 := by
      apply mul_right_cancel₀ hz
      linear_combination h1 - hc
    have hsq : (p l * r l / c) ^ 2 = 1 ^ 2 := by rw [div_pow, h2, div_self (pow_ne_zero 2 hc0), one_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Or.inl h
    · exact Or.inr h
  · have : ∑ l ∈ B, p l * r l / c * m l / r l = (1 / c) * ∑ l ∈ B, m l * p l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have := hr0 l hl
      field_simp
    rw [this, hsum, mul_zero]

/-- `Φ₃ = Y₁² + Y₂² + Y₃² − 2(Y₁Y₂ + Y₂Y₃ + Y₃Y₁)` is the product of the four sums `√Y₁ ± √Y₂ ± √Y₃` (§6.6). -/
theorem Phi3_product {R : Type*} [CommRing R] (a b c : R) :
    (a + b + c) * (a + b - c) * (a - b + c) * (a - b - c) =
      (a ^ 2) ^ 2 + (b ^ 2) ^ 2 + (c ^ 2) ^ 2 - 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  ring

/-- A vanishing signed sum `ε₁a + ε₂b + ε₃c = 0` makes `Φ₃(a², b², c²)` vanish. -/
theorem Phi3_zero_of_signed {R : Type*} [CommRing R] (a b c e1 e2 e3 : R) (h1 : e1 = 1 ∨ e1 = -1)
    (h2 : e2 = 1 ∨ e2 = -1) (h3 : e3 = 1 ∨ e3 = -1) (h : e1 * a + e2 * b + e3 * c = 0) :
    (a ^ 2) ^ 2 + (b ^ 2) ^ 2 + (c ^ 2) ^ 2 - 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) = 0 := by
  rw [← Phi3_product]
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl
  all_goals first
    | linear_combination ((a + b - c) * (a - b + c) * (a - b - c)) * h
    | linear_combination (-(a + b - c) * (a - b + c) * (a - b - c)) * h
    | linear_combination ((a + b + c) * (a - b + c) * (a - b - c)) * h
    | linear_combination (-(a + b + c) * (a - b + c) * (a - b - c)) * h
    | linear_combination ((a + b + c) * (a + b - c) * (a - b - c)) * h
    | linear_combination (-(a + b + c) * (a + b - c) * (a - b - c)) * h
    | linear_combination ((a + b + c) * (a + b - c) * (a - b + c)) * h
    | linear_combination (-(a + b + c) * (a + b - c) * (a - b + c)) * h

/-- With `ŵ_l = s′ ℓ_l(τ′)/M_B = r_l²` and `Y_l = m_l² Λ_l = y_l²` (`ℓ_l Λ_l = L`), `(m_l/r_l)² = (M_B/(s′L)) y_l²`:
the relation of Theorem 6.15 is a signed sum of the `√Y_l`. -/
theorem d93_to_Y {K : Type*} [Field K] (ml rl yl s' MB ll Λl : K) (hrl : rl ^ 2 = s' * ll / MB)
    (hyl : yl ^ 2 = ml ^ 2 * Λl) (hs' : s' ≠ 0) (hMB : MB ≠ 0) (hll : ll ≠ 0) (hΛ : Λl ≠ 0) :
    (ml / rl) ^ 2 = MB / (s' * (ll * Λl)) * yl ^ 2 := by
  have hrl0 : rl ≠ 0 := by
    intro h
    have h0 : s' * ll / MB = 0 := by rw [← hrl, h]; ring
    rcases div_eq_zero_iff.mp h0 with h' | h'
    · exact mul_ne_zero hs' hll h'
    · exact hMB h'
  rw [div_pow, hrl, hyl]
  field_simp

/-- **Theorem 6.15**, the last step: if `(m_l/r_l)² = ν² y_l²` (`ν ≠ 0`) and `Σ_l ε_l m_l/r_l = 0` for signs `ε`, then
`Φ₃(y₁², y₂², y₃²) = 0`. -/
theorem d93_Phi3_zero (m r y : Fin 3 → ℂ) (ν : ℂ) (hν : ν ≠ 0) (hmy : ∀ l, (m l / r l) ^ 2 = ν ^ 2 * y l ^ 2)
    (ε : Fin 3 → ℂ) (hε : ∀ l, ε l = 1 ∨ ε l = -1) (hsum : ∑ l, ε l * m l / r l = 0) :
    (y 0 ^ 2) ^ 2 + (y 1 ^ 2) ^ 2 + (y 2 ^ 2) ^ 2 - 2 * (y 0 ^ 2 * y 1 ^ 2 + y 1 ^ 2 * y 2 ^ 2 + y 2 ^ 2 * y 0 ^ 2)
      = 0 := by
  have hδ : ∀ l, ∃ δ : ℂ, (δ = 1 ∨ δ = -1) ∧ m l / r l = δ * (ν * y l) := by
    intro l
    have h := hmy l
    have : (m l / r l) ^ 2 = (ν * y l) ^ 2 := by rw [h]; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h' | h'
    · exact ⟨1, Or.inl rfl, by rw [h', one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h']; ring⟩
  choose δ hδ1 hδ2 using hδ
  have hs : ν * ((ε 0 * δ 0) * y 0 + (ε 1 * δ 1) * y 1 + (ε 2 * δ 2) * y 2) = 0 := by
    have : ∑ l, ε l * m l / r l = ∑ l, ε l * (m l / r l) := Finset.sum_congr rfl fun l _ => by ring
    rw [this, Fin.sum_univ_three, hδ2 0, hδ2 1, hδ2 2] at hsum
    linear_combination hsum
  have hs' := (mul_eq_zero.mp hs).resolve_left hν
  have sgn : ∀ l, ε l * δ l = 1 ∨ ε l * δ l = -1 := by
    intro l
    rcases hε l with h1 | h1 <;> rcases hδ1 l with h2 | h2 <;> simp [h1, h2]
  exact Phi3_zero_of_signed (y 0) (y 1) (y 2) _ _ _ (sgn 0) (sgn 1) (sgn 2) hs'

end Lean6.Special.Hand
