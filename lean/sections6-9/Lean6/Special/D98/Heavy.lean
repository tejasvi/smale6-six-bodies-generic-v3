import Lean6.Special.D98.Shapes

/-!
# Lemma 6.13 (`lem:dominant`) at `μ = (1, 2, 40)`

The computations of the hand proof, with their analytic conclusions proved here.

* `lag_bound_*`, `N01_bound_*`, …: for each Lagrange factor `p ∈ {t² − t + 1, N₀₁, N₁₀, N₁₁}` and `c ∈ {0, 1}`,
  `|p(c + h) − 1| ≤ 0.5951` for `|h| ≤ 1/10` (the triangle inequality on the coefficients of `p(c + h)`).
* `Q_heavy`: `Q_σ = 40 C_σ + D_σ` at `μ = (1, 2, 40)`; `C_bound_*`, `D_bound_*`: `|C_σ(c)| = 1`,
  `|C_σ − C_σ(c)| ≤ 0.332`, `|D_σ| ≤ 2.446` on `|x − c| ≤ 1/10`, `c ∈ {0, −1}`.
* **`heavy_roots`**: every root `t ∈ ℂ` of `S_μ` has `|t| > 1/10`, `|t − 1| > 1/10` and `ρ(t) > 9/10`, where
  `ρ = A₃/(A₁ + A₂ + A₃)`, `A_j = μ_j |Λ_j(t)|^{1/2}`.
* **`heavy_signed_sums`**: for roots `t`, `t'` and complex numbers `c_{jl}` with `c_{jl}² = μ_j² μ_l² Λ_j(t) Λ_l(t')`
  (any square roots of the entries of `Ψ(t, t')`), every signed sum `Σ ε_{jl} c_{jl}` with `ε_{jl} = ±1` is nonzero,
  so no factor of `Φ` vanishes and `Ψ(t, t') ≠ 0`.
-/

namespace Lean6.Special.D98

open Complex

/-! ## Coefficient bounds -/

/-- `Σ l[i] hⁱ`. -/
noncomputable def hornerC : List ℤ → ℂ → ℂ
  | [], _ => 0
  | a :: l, h => (a : ℂ) + h * hornerC l h

/-- `Σ |l[i]| rⁱ`. -/
noncomputable def hornerB : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: l, r => |(a : ℝ)| + r * hornerB l r

theorem hornerB_nonneg : ∀ (l : List ℤ) {r : ℝ}, 0 ≤ r → 0 ≤ hornerB l r
  | [], _, _ => le_refl _
  | a :: l, r, hr => by
    have := hornerB_nonneg l hr
    simp only [hornerB]
    positivity

/-- **The triangle inequality on the coefficients.** -/
theorem norm_hornerC_le : ∀ (l : List ℤ) {h : ℂ} {r : ℝ}, ‖h‖ ≤ r → ‖hornerC l h‖ ≤ hornerB l r
  | [], _, _, _ => by simp [hornerC, hornerB]
  | a :: l, h, r, hr => by
    have ih := norm_hornerC_le l hr
    have hr0 : 0 ≤ r := (norm_nonneg h).trans hr
    simp only [hornerC, hornerB]
    calc ‖(a : ℂ) + h * hornerC l h‖ ≤ ‖(a : ℂ)‖ + ‖h * hornerC l h‖ := norm_add_le _ _
      _ = |(a : ℝ)| + ‖h‖ * ‖hornerC l h‖ := by rw [norm_mul, Complex.norm_intCast]
      _ ≤ |(a : ℝ)| + r * hornerB l r := by
        gcongr

/-- If `p(c + h) = 1 + h · Σ T[i] hⁱ`, then `|p(c + h) − 1| ≤ (1/10) Σ |T[i]| 10⁻ⁱ` for `|h| ≤ 1/10`. -/
theorem taylor_bound {p : ℂ → ℂ} {c : ℂ} {T : List ℤ} (hT : ∀ h, p (c + h) = 1 + h * hornerC T h) {B : ℝ}
    (hB : (1 / 10 : ℝ) * hornerB T (1 / 10) ≤ B) {h : ℂ} (hh : ‖h‖ ≤ 1 / 10) : ‖p (c + h) - 1‖ ≤ B := by
  rw [hT, add_sub_cancel_left, norm_mul]
  calc ‖h‖ * ‖hornerC T h‖ ≤ (1 / 10) * hornerB T (1 / 10) := by
        gcongr
        exact norm_hornerC_le T hh
    _ ≤ B := hB

theorem ne_zero_of_bound {p : ℂ → ℂ} {c : ℂ} {T : List ℤ} (hT : ∀ h, p (c + h) = 1 + h * hornerC T h)
    (hB : (1 / 10 : ℝ) * hornerB T (1 / 10) < 1) {t : ℂ} (ht : ‖t - c‖ ≤ 1 / 10) : p t ≠ 0 := by
  intro h0
  have := taylor_bound (B := (1 / 10 : ℝ) * hornerB T (1 / 10)) hT le_rfl ht
  rw [add_sub_cancel, h0, zero_sub, norm_neg, norm_one] at this
  linarith

/-! ## The Lagrange factors -/

section Lagrange

theorem lag_T0 (h : ℂ) : lag (0 + h) = 1 + h * hornerC [-1, 1] h := by simp [lag, hornerC]; ring
theorem lag_T1 (h : ℂ) : lag (1 + h) = 1 + h * hornerC [1, 1] h := by simp [lag, hornerC]; ring
theorem N01_T0 (h : ℂ) : N01 (0 + h) = 1 + h * hornerC [-5, 9, -5, 1] h := by simp [N01, hornerC]; ring
theorem N01_T1 (h : ℂ) : N01 (1 + h) = 1 + h * hornerC [2, 0, -1, 1] h := by simp [N01, hornerC]; ring
theorem N10_T0 (h : ℂ) : N10 (0 + h) = 1 + h * hornerC [-2, 0, 1, 1] h := by simp [N10, hornerC]; ring
theorem N10_T1 (h : ℂ) : N10 (1 + h) = 1 + h * hornerC [5, 9, 5, 1] h := by simp [N10, hornerC]; ring
theorem N11_T0 (h : ℂ) : N11 (0 + h) = 1 + h * hornerC [1, 0, -2, 1] h := by simp [N11, hornerC]; ring
theorem N11_T1 (h : ℂ) : N11 (1 + h) = 1 + h * hornerC [-1, 0, 2, 1] h := by simp [N11, hornerC]; ring

/-- The exact tail sums of the hand proof: `0.11`, `0.11`, `0.5951`, `0.2011`, `0.2011`, `0.5951`, `0.1021`,
`0.1021`. -/
theorem tails :
    (1 / 10 : ℝ) * hornerB [-1, 1] (1 / 10) = 11 / 100 ∧ (1 / 10 : ℝ) * hornerB [1, 1] (1 / 10) = 11 / 100 ∧
    (1 / 10 : ℝ) * hornerB [-5, 9, -5, 1] (1 / 10) = 5951 / 10000 ∧
    (1 / 10 : ℝ) * hornerB [2, 0, -1, 1] (1 / 10) = 2011 / 10000 ∧
    (1 / 10 : ℝ) * hornerB [-2, 0, 1, 1] (1 / 10) = 2011 / 10000 ∧
    (1 / 10 : ℝ) * hornerB [5, 9, 5, 1] (1 / 10) = 5951 / 10000 ∧
    (1 / 10 : ℝ) * hornerB [1, 0, -2, 1] (1 / 10) = 1021 / 10000 ∧
    (1 / 10 : ℝ) * hornerB [-1, 0, 2, 1] (1 / 10) = 1021 / 10000 := by
  simp only [hornerB]; norm_num

/-- **The bound of the hand proof for the Lagrange factors**: `|p(c + h) − 1| ≤ 0.5951` for `|h| ≤ 1/10`,
`p ∈ {t² − t + 1, N₀₁, N₁₀, N₁₁}`, `c ∈ {0, 1}`. -/
theorem lagrange_bounds (h : ℂ) (hh : ‖h‖ ≤ 1 / 10) :
    ‖lag (0 + h) - 1‖ ≤ 5951 / 10000 ∧ ‖lag (1 + h) - 1‖ ≤ 5951 / 10000 ∧
    ‖N01 (0 + h) - 1‖ ≤ 5951 / 10000 ∧ ‖N01 (1 + h) - 1‖ ≤ 5951 / 10000 ∧
    ‖N10 (0 + h) - 1‖ ≤ 5951 / 10000 ∧ ‖N10 (1 + h) - 1‖ ≤ 5951 / 10000 ∧
    ‖N11 (0 + h) - 1‖ ≤ 5951 / 10000 ∧ ‖N11 (1 + h) - 1‖ ≤ 5951 / 10000 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := tails
  exact ⟨taylor_bound lag_T0 (by rw [t1]; norm_num) hh, taylor_bound lag_T1 (by rw [t2]; norm_num) hh,
    taylor_bound N01_T0 (by rw [t3]) hh, taylor_bound N01_T1 (by rw [t4]; norm_num) hh,
    taylor_bound N10_T0 (by rw [t5]; norm_num) hh, taylor_bound N10_T1 (by rw [t6]) hh,
    taylor_bound N11_T0 (by rw [t7]; norm_num) hh, taylor_bound N11_T1 (by rw [t8]; norm_num) hh⟩

theorem lagrange_ne_zero (t : ℂ) (ht : ‖t‖ ≤ 1 / 10 ∨ ‖t - 1‖ ≤ 1 / 10) :
    lag t ≠ 0 ∧ N01 t ≠ 0 ∧ N10 t ≠ 0 ∧ N11 t ≠ 0 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := tails
  rcases ht with ht | ht
  · have ht' : ‖t - 0‖ ≤ 1 / 10 := by simpa using ht
    exact ⟨ne_zero_of_bound lag_T0 (by rw [t1]; norm_num) ht', ne_zero_of_bound N01_T0 (by rw [t3]; norm_num) ht',
      ne_zero_of_bound N10_T0 (by rw [t5]; norm_num) ht', ne_zero_of_bound N11_T0 (by rw [t7]; norm_num) ht'⟩
  · exact ⟨ne_zero_of_bound lag_T1 (by rw [t2]; norm_num) ht, ne_zero_of_bound N01_T1 (by rw [t4]; norm_num) ht,
      ne_zero_of_bound N10_T1 (by rw [t6]; norm_num) ht, ne_zero_of_bound N11_T1 (by rw [t8]; norm_num) ht⟩

end Lagrange

/-! ## The collinear factors at `μ = (1, 2, 40)` -/

/-- The masses `(1, 2, 40)`. -/
noncomputable def μH : Fin 3 → ℂ := ![1, 2, 40]

/-- `C_σ = σ₁₃ x³ − σ₂₃ (1 + x)³`. -/
noncomputable def Cs (s : ℤ × ℤ × ℤ) (x : ℂ) : ℂ := (s.2.1 : ℂ) * x ^ 3 - (s.2.2 : ℂ) * (1 + x) ^ 3

/-- `D_σ = 3σ₁₂ x³(1+x)² + σ₁₂ x²(1+x)² − σ₁₃ x² − 2σ₂₃ (1+x)²`. -/
noncomputable def Ds (s : ℤ × ℤ × ℤ) (x : ℂ) : ℂ :=
  3 * (s.1 : ℂ) * x ^ 3 * (1 + x) ^ 2 + (s.1 : ℂ) * x ^ 2 * (1 + x) ^ 2 - (s.2.1 : ℂ) * x ^ 2 -
    2 * (s.2.2 : ℂ) * (1 + x) ^ 2

/-- **`Q_σ = 40 C_σ + D_σ`** at `μ = (1, 2, 40)`. -/
theorem Q_heavy (s : ℤ × ℤ × ℤ) (x : ℂ) : Q μH s x = 40 * Cs s x + Ds s x := by
  simp only [Q, μH, Cs, Ds, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- The bound of the hand proof for one `σ` and one centre `c`: `|C_σ(c)| = 1`, `|C_σ − C_σ(c)| ≤ 0.332`,
`|D_σ| ≤ 2.446` on `|x − c| ≤ 1/10`, and then `Q_σ ≠ 0` there. -/
theorem Q_ne_zero_near {s : ℤ × ℤ × ℤ} {c : ℂ} {TC TD : List ℤ} {C0 : ℤ} (hC0 : |C0| = 1)
    (hTC : ∀ h, Cs s (c + h) = C0 + h * hornerC TC h) (hTD : ∀ h, Ds s (c + h) = hornerC TD h)
    (hBC : (1 / 10 : ℝ) * hornerB TC (1 / 10) ≤ 332 / 1000) (hBD : hornerB TD (1 / 10) ≤ 2446 / 1000) {x : ℂ}
    (hx : ‖x - c‖ ≤ 1 / 10) :
    ‖Cs s c‖ = 1 ∧ ‖Cs s x - Cs s c‖ ≤ 332 / 1000 ∧ ‖Ds s x‖ ≤ 2446 / 1000 ∧ Q μH s x ≠ 0 := by
  have hc : Cs s c = C0 := by simpa using hTC 0
  have hxc : x = c + (x - c) := by ring
  have e1 : ‖Cs s c‖ = 1 := by rw [hc, Complex.norm_intCast]; exact_mod_cast hC0
  have e2 : ‖Cs s x - Cs s c‖ ≤ 332 / 1000 := by
    rw [hxc, hTC, hc, add_sub_cancel_left, norm_mul]
    calc ‖x - c‖ * ‖hornerC TC (x - c)‖ ≤ (1 / 10) * hornerB TC (1 / 10) := by
          gcongr
          exact norm_hornerC_le TC hx
      _ ≤ 332 / 1000 := hBC
  have e3 : ‖Ds s x‖ ≤ 2446 / 1000 := by
    rw [hxc, hTD]
    exact (norm_hornerC_le TD hx).trans hBD
  refine ⟨e1, e2, e3, ?_⟩
  intro h0
  rw [Q_heavy] at h0
  have hCx : 1 - 332 / 1000 ≤ ‖Cs s x‖ := by
    have := norm_sub_norm_le (Cs s c) (Cs s x)
    rw [norm_sub_rev] at this
    linarith
  have : ‖(40 : ℂ) * Cs s x‖ = ‖Ds s x‖ := by
    rw [show (40 : ℂ) * Cs s x = -Ds s x by linear_combination h0, norm_neg]
  rw [norm_mul, show ‖(40 : ℂ)‖ = 40 by norm_num] at this
  linarith

section Collinear

theorem C111_0 (h : ℂ) : Cs (1, 1, 1) (0 + h) = (-1 : ℤ) + h * hornerC [-3, -3] h := by simp [Cs, hornerC]; ring
theorem D111_0 (h : ℂ) : Ds (1, 1, 1) (0 + h) = hornerC [-2, -4, -2, 5, 7, 3] h := by simp [Ds, hornerC]; ring
theorem C111_1 (h : ℂ) : Cs (1, 1, 1) (-1 + h) = (-1 : ℤ) + h * hornerC [3, -3] h := by simp [Cs, hornerC]; ring
theorem D111_1 (h : ℂ) : Ds (1, 1, 1) (-1 + h) = hornerC [-1, 2, -5, 7, -8, 3] h := by simp [Ds, hornerC]; ring
theorem C112_0 (h : ℂ) : Cs (1, 1, -1) (0 + h) = (1 : ℤ) + h * hornerC [3, 3, 2] h := by simp [Cs, hornerC]; ring
theorem D112_0 (h : ℂ) : Ds (1, 1, -1) (0 + h) = hornerC [2, 4, 2, 5, 7, 3] h := by simp [Ds, hornerC]; ring
theorem C112_1 (h : ℂ) : Cs (1, 1, -1) (-1 + h) = (-1 : ℤ) + h * hornerC [3, -3, 2] h := by
  simp [Cs, hornerC]; ring
theorem D112_1 (h : ℂ) : Ds (1, 1, -1) (-1 + h) = hornerC [-1, 2, -1, 7, -8, 3] h := by simp [Ds, hornerC]; ring
theorem C122_0 (h : ℂ) : Cs (1, -1, -1) (0 + h) = (1 : ℤ) + h * hornerC [3, 3] h := by simp [Cs, hornerC]; ring
theorem D122_0 (h : ℂ) : Ds (1, -1, -1) (0 + h) = hornerC [2, 4, 4, 5, 7, 3] h := by simp [Ds, hornerC]; ring
theorem C122_1 (h : ℂ) : Cs (1, -1, -1) (-1 + h) = (1 : ℤ) + h * hornerC [-3, 3] h := by simp [Cs, hornerC]; ring
theorem D122_1 (h : ℂ) : Ds (1, -1, -1) (-1 + h) = hornerC [1, -2, 1, 7, -8, 3] h := by simp [Ds, hornerC]; ring
theorem C121_0 (h : ℂ) : Cs (1, -1, 1) (0 + h) = (-1 : ℤ) + h * hornerC [-3, -3, -2] h := by
  simp [Cs, hornerC]; ring
theorem D121_0 (h : ℂ) : Ds (1, -1, 1) (0 + h) = hornerC [-2, -4, 0, 5, 7, 3] h := by simp [Ds, hornerC]; ring
theorem C121_1 (h : ℂ) : Cs (1, -1, 1) (-1 + h) = (1 : ℤ) + h * hornerC [-3, 3, -2] h := by
  simp [Cs, hornerC]; ring
theorem D121_1 (h : ℂ) : Ds (1, -1, 1) (-1 + h) = hornerC [1, -2, -3, 7, -8, 3] h := by simp [Ds, hornerC]; ring

/-- The exact bounds of the hand proof: `B_C ≤ 0.332` and `B_D ≤ 2.446` in all eight cases. -/
theorem collinear_tails :
    (1 / 10 : ℝ) * hornerB [-3, -3] (1 / 10) ≤ 332 / 1000 ∧ hornerB [-2, -4, -2, 5, 7, 3] (1 / 10) ≤ 2446 / 1000 ∧
    (1 / 10 : ℝ) * hornerB [3, -3] (1 / 10) ≤ 332 / 1000 ∧ hornerB [-1, 2, -5, 7, -8, 3] (1 / 10) ≤ 2446 / 1000 ∧
    (1 / 10 : ℝ) * hornerB [3, 3, 2] (1 / 10) ≤ 332 / 1000 ∧ hornerB [2, 4, 2, 5, 7, 3] (1 / 10) ≤ 2446 / 1000 ∧
    (1 / 10 : ℝ) * hornerB [3, -3, 2] (1 / 10) ≤ 332 / 1000 ∧ hornerB [-1, 2, -1, 7, -8, 3] (1 / 10) ≤ 2446 / 1000 ∧
    (1 / 10 : ℝ) * hornerB [3, 3] (1 / 10) ≤ 332 / 1000 ∧ hornerB [2, 4, 4, 5, 7, 3] (1 / 10) ≤ 2446 / 1000 ∧
    (1 / 10 : ℝ) * hornerB [-3, 3] (1 / 10) ≤ 332 / 1000 ∧ hornerB [1, -2, 1, 7, -8, 3] (1 / 10) ≤ 2446 / 1000 ∧
    (1 / 10 : ℝ) * hornerB [-3, -3, -2] (1 / 10) ≤ 332 / 1000 ∧ hornerB [-2, -4, 0, 5, 7, 3] (1 / 10) ≤ 2446 / 1000 ∧
    (1 / 10 : ℝ) * hornerB [-3, 3, -2] (1 / 10) ≤ 332 / 1000 ∧
    hornerB [1, -2, -3, 7, -8, 3] (1 / 10) ≤ 2446 / 1000 := by
  simp only [hornerB]; norm_num

/-- **The collinear factors do not vanish near `x = 0` and `x = −1`.** -/
theorem collinear_ne_zero (i : Fin 4) (x : ℂ) (hx : ‖x - 0‖ ≤ 1 / 10 ∨ ‖x - (-1)‖ ≤ 1 / 10) : Q μH (sig i) x ≠ 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := collinear_tails
  fin_cases i <;> rcases hx with hx | hx <;> simp only [sig, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three]
  · exact (Q_ne_zero_near (C0 := -1) (by norm_num) C111_0 D111_0 a1 a2 hx).2.2.2
  · exact (Q_ne_zero_near (C0 := -1) (by norm_num) C111_1 D111_1 a3 a4 hx).2.2.2
  · exact (Q_ne_zero_near (C0 := 1) (by norm_num) C112_0 D112_0 a5 a6 hx).2.2.2
  · exact (Q_ne_zero_near (C0 := -1) (by norm_num) C112_1 D112_1 a7 a8 hx).2.2.2
  · exact (Q_ne_zero_near (C0 := 1) (by norm_num) C122_0 D122_0 a9 a10 hx).2.2.2
  · exact (Q_ne_zero_near (C0 := 1) (by norm_num) C122_1 D122_1 a11 a12 hx).2.2.2
  · exact (Q_ne_zero_near (C0 := -1) (by norm_num) C121_0 D121_0 a13 a14 hx).2.2.2
  · exact (Q_ne_zero_near (C0 := 1) (by norm_num) C121_1 D121_1 a15 a16 hx).2.2.2

end Collinear

/-! ## The roots of `S_μ` at `μ = (1, 2, 40)` -/

/-- **The roots avoid the two disks** (first statement of Lemma 6.13). -/
theorem roots_avoid (t : ℂ) (hS : S μH t = 0) : 1 / 10 < ‖t‖ ∧ 1 / 10 < ‖t - 1‖ := by
  by_contra hc
  rw [not_and_or, not_lt, not_lt] at hc
  obtain ⟨l1, l2, l3, l4⟩ := lagrange_ne_zero t hc
  have hq : ∀ i : Fin 4, Q μH (sig i) (t - 1) ≠ 0 := by
    intro i
    apply collinear_ne_zero
    rcases hc with h | h
    · right; simpa using h
    · left; simpa using h
  apply mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero l1 l2) l3) l4)
    (Finset.prod_ne_zero_iff.mpr fun i _ => hq i) hS

/-- The real masses `(1, 2, 40)`. -/
noncomputable def μR : Fin 3 → ℝ := ![1, 2, 40]

theorem μH_eq : μH = fun i => ((μR i : ℝ) : ℂ) := by
  funext i; fin_cases i <;> simp [μH, μR]

/-- `A_j(t) = μ_j |Λ_j(t)|^{1/2}` at `μ = (1, 2, 40)`. -/
noncomputable def Aj (t : ℂ) (j : Fin 3) : ℝ := μR j * Real.sqrt ‖Lam μH t j‖

/-- `ρ(t) = A₃ / (A₁ + A₂ + A₃)`. -/
noncomputable def rho (t : ℂ) : ℝ := Aj t 2 / (Aj t 0 + Aj t 1 + Aj t 2)

theorem ell_bounds (t : ℂ) (h0 : 1 / 10 < ‖t‖) (h1 : 1 / 10 < ‖t - 1‖) :
    20 * ‖t‖ < ‖ell1 μH t‖ ∧ 20 * ‖t - 1‖ < ‖ell2 μH t‖ ∧ ‖ell3 μH t‖ < 144 / 100 * ‖ell1 μH t‖ ∧
      ‖ell3 μH t‖ < ‖ell2 μH t‖ := by
  have e1 : ell1 μH t = 40 * t + 2 := by
    simp [ell1, μH]; ring
  have e2 : ell2 μH t = 40 * (t - 1) - 1 := by
    simp [ell2, ell1, Mtot, μH]; ring
  have e3a : ell3 μH t = 2 - 3 * t := by
    simp [ell3, ell1, Mtot, μH]; ring
  have e3b : ell3 μH t = -1 - 3 * (t - 1) := by
    rw [e3a]; ring
  have n1 : 40 * ‖t‖ - 2 ≤ ‖ell1 μH t‖ := by
    rw [e1]
    have := norm_sub_norm_le (40 * t + 2) (-2)
    simp only [sub_neg_eq_add, add_neg_cancel_right, norm_neg] at this
    have h40 : ‖(40 : ℂ) * t‖ = 40 * ‖t‖ := by rw [norm_mul]; norm_num
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have := norm_sub_norm_le ((40 : ℂ) * t) (-(2 : ℂ))
    rw [sub_neg_eq_add, norm_neg, h40, h2] at this
    linarith
  have n2 : 40 * ‖t - 1‖ - 1 ≤ ‖ell2 μH t‖ := by
    rw [e2]
    have h40 : ‖(40 : ℂ) * (t - 1)‖ = 40 * ‖t - 1‖ := by rw [norm_mul]; norm_num
    have := norm_sub_norm_le ((40 : ℂ) * (t - 1)) ((40 : ℂ) * (t - 1) - 1)
    rw [sub_sub_cancel, norm_one, h40] at this
    linarith
  have n3a : ‖ell3 μH t‖ ≤ 2 + 3 * ‖t‖ := by
    rw [e3a]
    calc ‖(2 : ℂ) - 3 * t‖ ≤ ‖(2 : ℂ)‖ + ‖(3 : ℂ) * t‖ := norm_sub_le _ _
      _ = 2 + 3 * ‖t‖ := by rw [norm_mul]; norm_num
  have n3b : ‖ell3 μH t‖ ≤ 1 + 3 * ‖t - 1‖ := by
    rw [e3b]
    calc ‖(-1 : ℂ) - 3 * (t - 1)‖ ≤ ‖(-1 : ℂ)‖ + ‖(3 : ℂ) * (t - 1)‖ := norm_sub_le _ _
      _ = 1 + 3 * ‖t - 1‖ := by rw [norm_mul]; norm_num
  refine ⟨by linarith, by linarith, by nlinarith, by linarith⟩

/-- **`ρ(t) > 9/10` at the roots** (and the bounds `A₁ < 0.03 A₃`, `A₂ < 0.05 A₃` of the hand proof). -/
theorem rho_bound (t : ℂ) (h0 : 1 / 10 < ‖t‖) (h1 : 1 / 10 < ‖t - 1‖) :
    Aj t 0 < 3 / 100 * Aj t 2 ∧ Aj t 1 < 5 / 100 * Aj t 2 ∧ 0 < Aj t 2 ∧
      9 / 10 * (Aj t 0 + Aj t 1 + Aj t 2) < Aj t 2 ∧ 9 / 10 < rho t := by
  obtain ⟨b1, b2, b3, b4⟩ := ell_bounds t h0 h1
  have p1 : 0 < ‖ell1 μH t‖ := by nlinarith [norm_nonneg t]
  have p2 : 0 < ‖ell2 μH t‖ := by nlinarith [norm_nonneg (t - 1)]
  have L0 : ‖Lam μH t 0‖ = ‖ell2 μH t‖ * ‖ell3 μH t‖ := by simp [Lam, norm_mul]
  have L1 : ‖Lam μH t 1‖ = ‖ell1 μH t‖ * ‖ell3 μH t‖ := by simp [Lam, norm_mul]
  have L2 : ‖Lam μH t 2‖ = ‖ell1 μH t‖ * ‖ell2 μH t‖ := by simp [Lam, norm_mul]
  have A0 : Aj t 0 = Real.sqrt (‖ell2 μH t‖ * ‖ell3 μH t‖) := by simp [Aj, μR, L0]
  have A1 : Aj t 1 = 2 * Real.sqrt (‖ell1 μH t‖ * ‖ell3 μH t‖) := by simp [Aj, μR, L1]
  have A2 : Aj t 2 = 40 * Real.sqrt (‖ell1 μH t‖ * ‖ell2 μH t‖) := by simp [Aj, μR, L2]
  have s2 : 0 < Real.sqrt (‖ell1 μH t‖ * ‖ell2 μH t‖) := Real.sqrt_pos.mpr (mul_pos p1 p2)
  have h3 : 3 / 100 * Aj t 2 = Real.sqrt (144 / 100 * (‖ell1 μH t‖ * ‖ell2 μH t‖)) := by
    have e : Real.sqrt (144 / 100 * (‖ell1 μH t‖ * ‖ell2 μH t‖)) =
        Real.sqrt (144 / 100) * Real.sqrt (‖ell1 μH t‖ * ‖ell2 μH t‖) := Real.sqrt_mul (by norm_num) _
    have e2 : Real.sqrt (144 / 100) = 12 / 10 := by
      rw [show (144 / 100 : ℝ) = (12 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e, e2, A2]
    ring
  have h5 : 5 / 100 * Aj t 2 = 2 * Real.sqrt (‖ell1 μH t‖ * ‖ell2 μH t‖) := by rw [A2]; ring
  have c0 : Aj t 0 < 3 / 100 * Aj t 2 := by
    rw [A0, h3]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith [norm_nonneg (ell3 μH t)]
  have c1 : Aj t 1 < 5 / 100 * Aj t 2 := by
    rw [A1, h5]
    have : Real.sqrt (‖ell1 μH t‖ * ‖ell3 μH t‖) < Real.sqrt (‖ell1 μH t‖ * ‖ell2 μH t‖) :=
      Real.sqrt_lt_sqrt (by positivity) (by nlinarith [norm_nonneg (ell3 μH t)])
    linarith
  have c2 : 0 < Aj t 2 := by rw [A2]; positivity
  have c3 : 9 / 10 * (Aj t 0 + Aj t 1 + Aj t 2) < Aj t 2 := by linarith
  refine ⟨c0, c1, c2, c3, ?_⟩
  have hA0 : 0 ≤ Aj t 0 := by rw [A0]; positivity
  have hA1 : 0 ≤ Aj t 1 := by rw [A1]; positivity
  rw [rho, lt_div_iff₀ (by linarith)]
  exact c3

/-- **Lemma 6.13, first statements**: every root `t` of `S_μ`, `μ = (1, 2, 40)`, has `|t| > 1/10`, `|t − 1| > 1/10`
and `ρ(t) > 9/10`. -/
theorem heavy_roots (t : ℂ) (hS : S μH t = 0) : 1 / 10 < ‖t‖ ∧ 1 / 10 < ‖t - 1‖ ∧ 9 / 10 < rho t := by
  obtain ⟨h0, h1⟩ := roots_avoid t hS
  exact ⟨h0, h1, (rho_bound t h0 h1).2.2.2.2⟩

/-! ## The signed sums -/

theorem sum_ne_zero_of_dominant {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℂ) (i0 : ι)
    (h : ∑ i ∈ Finset.univ.erase i0, ‖w i‖ < ‖w i0‖) : ∑ i, w i ≠ 0 := by
  intro h0
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at h0
  have : w i0 = -∑ i ∈ Finset.univ.erase i0, w i := by linear_combination h0
  have h2 := norm_sum_le (Finset.univ.erase i0) w
  rw [this, norm_neg] at h
  linarith

/-- **The "consequently" step of Lemma 6.13**: for roots `t`, `t'` of `S_μ` and complex `c_{jl}` with
`c_{jl}² = μ_j² μ_l² Λ_j(t) Λ_l(t')`, every signed sum `Σ ε_{jl} c_{jl}` (`ε_{jl} = ±1`) is nonzero. -/
theorem heavy_signed_sums (t t' : ℂ) (ht : S μH t = 0) (ht' : S μH t' = 0) (c : Fin 3 → Fin 3 → ℂ)
    (hc : ∀ j l, c j l ^ 2 = μH j ^ 2 * μH l ^ 2 * Lam μH t j * Lam μH t' l) (ε : Fin 3 → Fin 3 → ℤ)
    (hε : ∀ j l, ε j l = 1 ∨ ε j l = -1) : ∑ j, ∑ l, (ε j l : ℂ) * c j l ≠ 0 := by
  -- the moduli
  have hmod : ∀ j l, ‖c j l‖ = Aj t j * Aj t' l := by
    intro j l
    have h1 : ‖c j l‖ ^ 2 = (Aj t j * Aj t' l) ^ 2 := by
      rw [← norm_pow, hc j l, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, μH_eq]
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hj := Real.sq_sqrt (norm_nonneg (Lam (fun i => ((μR i : ℝ) : ℂ)) t j))
      have hl := Real.sq_sqrt (norm_nonneg (Lam (fun i => ((μR i : ℝ) : ℂ)) t' l))
      simp only [Aj, μH_eq]
      rw [mul_pow, mul_pow, mul_pow, hj, hl]
      ring
    have hA : 0 ≤ Aj t j * Aj t' l := by
      have h1 : ∀ s j, 0 ≤ Aj s j := fun s j => by
        simp only [Aj]; fin_cases j <;> simp [μR] <;> positivity
      exact mul_nonneg (h1 t j) (h1 t' l)
    exact (pow_left_inj₀ (norm_nonneg _) hA two_ne_zero).mp h1
  obtain ⟨a0, a1⟩ := roots_avoid t ht
  obtain ⟨b0, b1⟩ := roots_avoid t' ht'
  obtain ⟨-, -, p, q, -⟩ := rho_bound t a0 a1
  obtain ⟨-, -, p', q', -⟩ := rho_bound t' b0 b1
  have nn : ∀ s j, 0 ≤ Aj s j := fun s j => by
    simp only [Aj]; fin_cases j <;> simp [μR] <;> positivity
  -- the dominant term (2, 2)
  rw [← Finset.sum_product' (f := fun j l => (ε j l : ℂ) * c j l)]
  apply sum_ne_zero_of_dominant (fun x : Fin 3 × Fin 3 => (ε x.1 x.2 : ℂ) * c x.1 x.2) (2, 2)
  have hw : ∀ x : Fin 3 × Fin 3, ‖(ε x.1 x.2 : ℂ) * c x.1 x.2‖ = Aj t x.1 * Aj t' x.2 := by
    intro x
    rw [norm_mul, hmod]
    rcases hε x.1 x.2 with h | h <;> simp [h]
  simp only [hw]
  have hsum : ∑ x ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).erase (2, 2), Aj t x.1 * Aj t' x.2 =
      (Aj t 0 + Aj t 1 + Aj t 2) * (Aj t' 0 + Aj t' 1 + Aj t' 2) - Aj t 2 * Aj t' 2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fintype.sum_prod_type]
    simp only [Fin.sum_univ_three]
    ring
  rw [hsum]
  set S1 := Aj t 0 + Aj t 1 + Aj t 2
  set S2 := Aj t' 0 + Aj t' 1 + Aj t' 2
  have hS1 : 0 < S1 := by have := nn t 0; have := nn t 1; linarith
  have hS2 : 0 < S2 := by have := nn t' 0; have := nn t' 1; linarith
  rw [hw (2, 2)]
  have hm := mul_lt_mul'' q q' (by positivity) (by positivity)
  have hp := mul_pos hS1 hS2
  nlinarith

end Lean6.Special.D98
