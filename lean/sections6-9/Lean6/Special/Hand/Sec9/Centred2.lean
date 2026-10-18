import Lean6.Special.Hand.Sec9.Basic

/-!
# Algebra inside the hand proofs of Section 9 (IV): Lemmas 9.14, 9.15, 9.22

* H9.11, Lemma 9.14 (`lem:handEQ2`): `handEQ2` (`X_b Y_a = X_a Y_b`, `ρ = m_a r/m_b`, `m_a² r⁴ = m_b²`, hence
  `m_a² M_A⁴ = m_b² M_B⁴`), `handEQ2_pos` (at positive values `m_a M_A² = m_b M_B²`).
* H9.12, Lemma 9.15 (`lem:handQ`): `handQ_signs` (`P_sk = ε_k P` and `Σ ε_k m_k = 0`), `signedSum`,
  `handQ_prod_ne_zero` (the product of the signed sums over all signs is a nonzero polynomial),
  `handQ_not_all_equal` (at positive masses the signs are not all equal), `handQ_two` (`|K| = 2`: `m_a = m_b`).
* H9.15, Lemma 9.22 (`lem:handTQ`): `sq_real_pos`, `sq_real_neg`, `cube_inj_pos`, `handTQ`
  (`m_{l₁} = m_{l₂}` and `m_{k₁} = m_{k₂}`).
-/

namespace Lean6.Special.Hand.Sec9

open Complex Finset

/-! ## H9.11, Lemma 9.14 -/

/-- **Lemma 9.14.** With `Y_k = ĉ_k`, `X_k = ĉ′_k` (`k = a, b`): the initial forms of the two equations of `a`,
`Y_a (1 − m_s P_sa³) = m_b P_ab³ (Y_a − Y_b)` and the same with `X`, the initial form of the `c`-equation of `s`,
the distance rows `P_sa² X_a Y_a = P_sb² X_b Y_b = 1`, and `M_A Y_a + M_B Y_b = 0`, give `m_a² M_A⁴ = m_b² M_B⁴`. -/
theorem handEQ2 {K : Type*} [Field K] (ma mb ms MA MB Ya Yb Xa Xb Pab Psa Psb : K) (hmb : mb ≠ 0)
    (hab : Ya ≠ Yb) (hPab : Pab ≠ 0)
    (hY : Ya * (1 - ms * Psa ^ 3) = mb * Pab ^ 3 * (Ya - Yb))
    (hX : Xa * (1 - ms * Psa ^ 3) = mb * Pab ^ 3 * (Xa - Xb))
    (hs : ma * Psa ^ 3 * Ya + mb * Psb ^ 3 * Yb = 0)
    (hda : Psa ^ 2 * Xa * Ya = 1) (hdb : Psb ^ 2 * Xb * Yb = 1) (hM : MA * Ya + MB * Yb = 0) :
    ma ^ 2 * MA ^ 4 - mb ^ 2 * MB ^ 4 = 0 := by
  have hYa : Ya ≠ 0 := by intro h0; rw [h0] at hda; simp at hda
  have hPsa : Psa ≠ 0 := by intro h0; rw [h0] at hda; simp at hda
  have hYb : Yb ≠ 0 := by intro h0; rw [h0] at hdb; simp at hdb
  have h1m : 1 - ms * Psa ^ 3 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hY
    have : mb * Pab ^ 3 * (Ya - Yb) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hmb (pow_ne_zero 3 hPab)) (sub_ne_zero.mpr hab)
    exact this hY.symm
  have hXY0 : (1 - ms * Psa ^ 3) * (Xa * Yb - Xb * Ya) = 0 := by
    linear_combination (Xa - Xb) * hY - (Ya - Yb) * hX
  have hXY : Xb * Ya = Xa * Yb := by
    linear_combination -((mul_eq_zero.mp hXY0).resolve_left h1m)
  by_cases hMB : MB = 0
  · have : MA * Ya = 0 := by rw [hMB] at hM; linear_combination hM
    have hMA : MA = 0 := (mul_eq_zero.mp this).resolve_right hYa
    rw [hMA, hMB]; ring
  · set r := MA / MB with hr
    have hYb' : Yb = -r * Ya := by rw [hr]; field_simp; linear_combination hM
    have hXb' : Xb = -r * Xa := by
      have : (Xb + r * Xa) * Ya = 0 := by rw [hYb'] at hXY; linear_combination hXY
      linear_combination (mul_eq_zero.mp this).resolve_right hYa
    set ρ := Psb / Psa with hρ
    have hPsb' : Psb = ρ * Psa := by rw [hρ]; field_simp
    have h3 : ρ ^ 3 * (mb * r) = ma := by
      rw [hPsb', hYb'] at hs
      have : Ya * Psa ^ 3 * (ma - ρ ^ 3 * (mb * r)) = 0 := by linear_combination hs
      linear_combination -((mul_eq_zero.mp this).resolve_left (mul_ne_zero hYa (pow_ne_zero 3 hPsa)))
    have h4 : ρ ^ 2 * r ^ 2 = 1 := by
      rw [hPsb', hXb', hYb'] at hdb
      linear_combination hdb - ρ ^ 2 * r ^ 2 * hda
    have h5 : ma ^ 2 * r ^ 4 = mb ^ 2 := by
      rw [← h3]; linear_combination mb ^ 2 * ((ρ ^ 2 * r ^ 2) ^ 2 + ρ ^ 2 * r ^ 2 + 1) * h4
    rw [hr] at h5
    field_simp at h5
    linear_combination h5

/-- **Lemma 9.14** at positive values: `m_a² M_A⁴ = m_b² M_B⁴` says `m_a M_A² = m_b M_B²`. -/
theorem handEQ2_pos (ma mb MA MB : ℝ) (hma : 0 < ma) (hmb : 0 < mb) (hMA : 0 < MA) (hMB : 0 < MB)
    (h : ma ^ 2 * MA ^ 4 - mb ^ 2 * MB ^ 4 = 0) : ma * MA ^ 2 = mb * MB ^ 2 := by
  have e : (ma * MA ^ 2 - mb * MB ^ 2) * (ma * MA ^ 2 + mb * MB ^ 2) = 0 := by linear_combination h
  have hp : 0 < ma * MA ^ 2 + mb * MB ^ 2 := by positivity
  linarith [(mul_eq_zero.mp e).resolve_right hp.ne']

/-! ## H9.12, Lemma 9.15 -/

/-- **Lemma 9.15.** If the distance rows give `P_sk² g = 1` with one `g = γ γ′` for all `k ∈ K`, and the initial
form `−γ Σ_k m_k P_sk³` of the `c`-equation of `s` vanishes (`γ ≠ 0`), then `P_sk = ε_k P` for signs `ε_k` and
`Σ_k ε_k m_k = 0`. -/
theorem handQ_signs {F ι : Type*} [Field F] (S : Finset ι) (k0 : ι) (hk0 : k0 ∈ S) (m P : ι → F) (g γ : F)
    (hγ : γ ≠ 0) (hP : ∀ k ∈ S, P k ^ 2 * g = 1) (h : -γ * ∑ k ∈ S, m k * P k ^ 3 = 0) :
    ∃ ε : ι → F, (∀ k ∈ S, ε k = 1 ∨ ε k = -1) ∧ (∀ k ∈ S, P k = ε k * P k0) ∧ ∑ k ∈ S, ε k * m k = 0 := by
  classical
  set p := P k0 with hp
  have hp0 : p ≠ 0 := by
    intro h0; have := hP k0 hk0; rw [← hp, h0] at this; simp at this
  have hsq : ∀ k ∈ S, P k = p ∨ P k = -p := by
    intro k hk
    have e : (P k - p) * (P k + p) * g = 0 := by
      linear_combination hP k hk - hP k0 hk0
    have hg : g ≠ 0 := by
      intro h0; have := hP k0 hk0; rw [h0, mul_zero] at this; exact zero_ne_one this
    rcases mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hg) with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  refine ⟨fun k => if P k = p then 1 else -1, fun k _ => ?_, fun k hk => ?_, ?_⟩
  · by_cases hk : P k = p
    · left; simp [hk]
    · right; simp [hk]
  · show P k = (if P k = p then 1 else -1) * p
    by_cases hk' : P k = p
    · simp [hk']
    · rcases hsq k hk with h1 | h1
      · exact absurd h1 hk'
      · simp only [hk', ↓reduceIte]; rw [h1]; ring
  · have hsum : ∑ k ∈ S, m k * P k ^ 3 = p ^ 3 * ∑ k ∈ S, (if P k = p then 1 else -1) * m k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      by_cases hk' : P k = p
      · simp only [hk', ↓reduceIte]; ring
      · rcases hsq k hk with h1 | h1
        · exact absurd h1 hk'
        · simp only [hk', ↓reduceIte]; rw [h1]; ring
    have h' : ∑ k ∈ S, m k * P k ^ 3 = 0 := (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr hγ)
    rw [hsum] at h'
    exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 3 hp0)

/-- The signed sum `Σ_k ε_k m_k` for a sign vector `s` (`true ↦ +1`, `false ↦ −1`), in `ℤ[m_0, …, m_{n−1}]`. -/
noncomputable def signedSum (n : ℕ) (s : Fin n → Bool) : MvPolynomial (Fin n) ℤ :=
  ∑ k, MvPolynomial.C (if s k then 1 else -1) * MvPolynomial.X k

/-- **Lemma 9.15**: the product of the sums `Σ_k ε_k m_k` over all choices of signs is a nonzero polynomial (its value
at `m_k = 2^k` is a product of odd integers). -/
theorem handQ_prod_ne_zero (n : ℕ) (hn : 0 < n) : (∏ s : Fin n → Bool, signedSum n s) ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval (fun k : Fin n => (2 : ℤ) ^ (k : ℕ))) h
  rw [map_prod, map_zero] at h1
  obtain ⟨s, -, hs⟩ := Finset.prod_eq_zero_iff.mp h1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [signedSum, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at hs
  rw [Fin.sum_univ_succ] at hs
  have h2 : ∀ i : Fin m, (if s i.succ = true then (1 : ℤ) else -1) * 2 ^ ((i.succ : Fin (m + 1)) : ℕ) =
      2 * ((if s i.succ = true then (1 : ℤ) else -1) * 2 ^ (i : ℕ)) := by
    intro i; rw [Fin.val_succ, pow_succ]; ring
  rw [Finset.sum_congr rfl fun i _ => h2 i, ← Finset.mul_sum] at hs
  simp only [Fin.val_zero, pow_zero, mul_one] at hs
  by_cases h0 : s 0 = true <;> simp [h0] at hs <;> omega

/-- **Lemma 9.15** at positive masses: the signs are not all equal. -/
theorem handQ_not_all_equal {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (m ε : ι → ℝ) (hm : ∀ k ∈ S, 0 < m k)
    (h : ∑ k ∈ S, ε k * m k = 0) : ¬ (∀ k ∈ S, ε k = 1) ∧ ¬ (∀ k ∈ S, ε k = -1) := by
  constructor
  · intro hall
    have : ∑ k ∈ S, ε k * m k = ∑ k ∈ S, m k := Finset.sum_congr rfl fun k hk => by rw [hall k hk, one_mul]
    have hpos : 0 < ∑ k ∈ S, m k := Finset.sum_pos hm hS
    linarith
  · intro hall
    have : ∑ k ∈ S, ε k * m k = -∑ k ∈ S, m k := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k hk => by rw [hall k hk]; ring
    have hpos : 0 < ∑ k ∈ S, m k := Finset.sum_pos hm hS
    linarith

/-- **Lemma 9.15** for `|K| = 2`: `ε_a m_a + ε_b m_b = 0` with signs and positive masses gives `m_a = m_b`. -/
theorem handQ_two (ma mb εa εb : ℝ) (ha : 0 < ma) (hb : 0 < mb) (hεa : εa = 1 ∨ εa = -1) (hεb : εb = 1 ∨ εb = -1)
    (h : εa * ma + εb * mb = 0) : ma = mb := by
  rcases hεa with rfl | rfl <;> rcases hεb with rfl | rfl <;> linarith

/-! ## H9.15, Lemma 9.22 -/

/-- A complex number whose square is a positive real is real. -/
theorem sq_real_pos (q : ℂ) (r : ℝ) (hr : 0 < r) (h : q ^ 2 = (r : ℂ)) : q.im = 0 ∧ q.re ^ 2 = r := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hm : q.re * q.im = 0 := by linarith
  rcases mul_eq_zero.mp hm with h0 | h0
  · rw [h0] at hre; nlinarith [sq_nonneg q.im]
  · refine ⟨h0, ?_⟩; rw [h0] at hre; nlinarith

/-- A complex number whose square is a negative real is purely imaginary. -/
theorem sq_real_neg (q : ℂ) (r : ℝ) (hr : 0 < r) (h : q ^ 2 = -(r : ℂ)) : q.re = 0 ∧ q.im ^ 2 = r := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero] at hre him
  have hm : q.re * q.im = 0 := by linarith
  rcases mul_eq_zero.mp hm with h0 | h0
  · refine ⟨h0, ?_⟩; rw [h0] at hre; nlinarith
  · rw [h0] at hre; nlinarith [sq_nonneg q.re]

/-- Cubes of positive reals are injective. -/
theorem cube_inj_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ^ 3 = b ^ 3) : a = b := by
  have e : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by linear_combination h
  have hp : 0 < a ^ 2 + a * b + b ^ 2 := by positivity
  linarith [(mul_eq_zero.mp e).resolve_right hp.ne']

/-- **Lemma 9.22.** With `Y_i = ĉ_{l_i}`, `X_j = ĉ′_{k_j}`, `P_ij = P_{l_i k_j}`: the relations
`m_{l₁} Y₁ + m_{l₂} Y₂ = 0`, `m_{k₁} X₁ + m_{k₂} X₂ = 0`, the distance rows `P_ij² X_j Y_i = −1` and the initial form
`Σ m_{l_i} m_{k_j} P_ij³ Y_i X_j = 0` of the torque force, at positive masses, `m_{l₁} = m_{l₂}` and `m_{k₁} = m_{k₂}`. -/
theorem handTQ (ml1 ml2 mk1 mk2 : ℝ) (hl1 : 0 < ml1) (hl2 : 0 < ml2) (hk1 : 0 < mk1) (hk2 : 0 < mk2)
    (Y1 Y2 X1 X2 P11 P12 P21 P22 : ℂ) (hY : (ml1 : ℂ) * Y1 + ml2 * Y2 = 0) (hX : (mk1 : ℂ) * X1 + mk2 * X2 = 0)
    (d11 : P11 ^ 2 * X1 * Y1 = -1) (d12 : P12 ^ 2 * X2 * Y1 = -1) (d21 : P21 ^ 2 * X1 * Y2 = -1)
    (d22 : P22 ^ 2 * X2 * Y2 = -1)
    (hT : (ml1 : ℂ) * mk1 * P11 ^ 3 * Y1 * X1 + ml1 * mk2 * P12 ^ 3 * Y1 * X2 + ml2 * mk1 * P21 ^ 3 * Y2 * X1 +
      ml2 * mk2 * P22 ^ 3 * Y2 * X2 = 0) :
    ml1 = ml2 ∧ mk1 = mk2 := by
  -- the initial form of the torque is `−Σ m m P`
  have hT' : (ml1 : ℂ) * mk1 * P11 + ml1 * mk2 * P12 + ml2 * mk1 * P21 + ml2 * mk2 * P22 = 0 := by
    linear_combination -hT + (ml1 * mk1 * P11 : ℂ) * d11 + (ml1 * mk2 * P12 : ℂ) * d12 +
      (ml2 * mk1 * P21 : ℂ) * d21 + (ml2 * mk2 * P22 : ℂ) * d22
  -- a square root `s` of `m_{k₁} m_{l₁} u`, `u = −X₁ Y₁`
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((mk1 : ℂ) * ml1 * (-(X1 * Y1))) two_pos
  have sq11 : (P11 * s) ^ 2 = ((mk1 * ml1 : ℝ) : ℂ) := by
    rw [mul_pow, hs]; push_cast; linear_combination -(mk1 * ml1 : ℂ) * d11
  have sq12 : (P12 * s) ^ 2 = -((mk2 * ml1 : ℝ) : ℂ) := by
    rw [mul_pow, hs]; push_cast
    linear_combination (-(P12 ^ 2) * ml1 * Y1 : ℂ) * hX + (mk2 * ml1 : ℂ) * d12
  have sq21 : (P21 * s) ^ 2 = -((mk1 * ml2 : ℝ) : ℂ) := by
    rw [mul_pow, hs]; push_cast
    linear_combination (-(P21 ^ 2) * mk1 * X1 : ℂ) * hY + (mk1 * ml2 : ℂ) * d21
  have sq22 : (P22 * s) ^ 2 = ((mk2 * ml2 : ℝ) : ℂ) := by
    rw [mul_pow, hs]; push_cast
    linear_combination (-(P22 ^ 2) * ml1 * Y1 : ℂ) * hX + (P22 ^ 2 * mk2 * X2 : ℂ) * hY - (mk2 * ml2 : ℂ) * d22
  -- the four terms, multiplied by `s`
  have hsum : (ml1 : ℂ) * mk1 * (P11 * s) + ml1 * mk2 * (P12 * s) + ml2 * mk1 * (P21 * s) + ml2 * mk2 * (P22 * s) =
      0 := by linear_combination s * hT'
  set q11 := P11 * s with hq11
  set q12 := P12 * s with hq12
  set q21 := P21 * s with hq21
  set q22 := P22 * s with hq22
  obtain ⟨i11, r11⟩ := sq_real_pos q11 (mk1 * ml1) (by positivity) sq11
  obtain ⟨r12, i12⟩ := sq_real_neg q12 (mk2 * ml1) (by positivity) sq12
  obtain ⟨r21, i21⟩ := sq_real_neg q21 (mk1 * ml2) (by positivity) sq21
  obtain ⟨i22, r22⟩ := sq_real_pos q22 (mk2 * ml2) (by positivity) sq22
  have hre := congrArg Complex.re hsum
  have him := congrArg Complex.im hsum
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im, mul_zero, zero_mul, sub_zero, add_zero] at hre him
  rw [r12, r21] at hre
  rw [i11, i22] at him
  -- real part: `m_{l₁} m_{k₁} q₁₁ + m_{l₂} m_{k₂} q₂₂ = 0`; imaginary part: `m_{l₁} m_{k₂} q₁₂ + m_{l₂} m_{k₁} q₂₁ = 0`
  have eA : (ml1 * mk1) ^ 3 = (ml2 * mk2) ^ 3 := by
    have e1 : ml1 * mk1 * q11.re = -(ml2 * mk2 * q22.re) := by linarith
    have e2 : (ml1 * mk1) ^ 2 * q11.re ^ 2 = (ml2 * mk2) ^ 2 * q22.re ^ 2 := by
      have := congrArg (· ^ 2) e1; linear_combination this
    rw [r11, r22] at e2; linear_combination e2
  have eC : (ml1 * mk2) ^ 3 = (ml2 * mk1) ^ 3 := by
    have e1 : ml1 * mk2 * q12.im = -(ml2 * mk1 * q21.im) := by linarith
    have e2 : (ml1 * mk2) ^ 2 * q12.im ^ 2 = (ml2 * mk1) ^ 2 * q21.im ^ 2 := by
      have := congrArg (· ^ 2) e1; linear_combination this
    rw [i12, i21] at e2; linear_combination e2
  have hA := cube_inj_pos (by positivity) (by positivity) eA
  have hC := cube_inj_pos (by positivity) (by positivity) eC
  have hsq2 : (ml1 ^ 2 - ml2 ^ 2) * (mk1 * mk2) = 0 := by linear_combination ml1 * mk2 * hA + ml2 * mk2 * hC
  have hl3 : ml1 ^ 2 - ml2 ^ 2 = 0 := (mul_eq_zero.mp hsq2).resolve_right (by positivity)
  have hl4 : (ml1 - ml2) * (ml1 + ml2) = 0 := by linear_combination hl3
  have hl : ml1 = ml2 := by linarith [(mul_eq_zero.mp hl4).resolve_right (by positivity)]
  refine ⟨hl, ?_⟩
  rw [hl] at hA
  have : ml2 * (mk1 - mk2) = 0 := by linear_combination hA
  linarith [(mul_eq_zero.mp this).resolve_left hl2.ne']

end Lean6.Special.Hand.Sec9
