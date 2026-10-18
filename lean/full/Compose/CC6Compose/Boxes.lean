import CC6Full.Six.D94
import CC6Full.Six.D88
import Lean6.Special.D88.Boxes.Final

/-!
# Bridge: the box facts of Lemma 6.19 (c), (d) from the certificate project

`D94Box` and `D88Box` (hypotheses of `d94_poly` and `d88_poly`) from `lemma_6_19_d` and `lemma_6_19_c` of the
certificate project (`Lean6.Special.D88.Boxes`). The systems of the two projects are written term for term alike:
`KC.KC12` is `D94.KC12 D94.μ0`, `N4.S11` is `D88.S11 D88.μ0`, and the positions `X` agree, definitionally.

The certificate project gives `N` pairwise disjoint closed polydiscs, each containing a zero of the system. One zero
is chosen in each polydisc (`choose`); the zeros are distinct since the polydiscs are disjoint
(`card_image_of_disjoint`), so they form the set `Z` of `N` elements.

* `d94Box`: on each polydisc of Lemma 6.19 (d) the certificate project gives `X₁, X₂, X₃ ≠ 0` and the lower bound
  `1.47·10⁻⁶ (1 + ρ²)^{1/2} Σ_l |β_l| ≤ |Σ_l ε_l β_l (1 + i s_l ρ)|`, with `ρ = 2√2 = 2^{3/2}` (`rho_eq`). The bound
  is positive (`kcSum_ne_zero`): the `β_l = m_l / w_l` do not vanish, since `w_l² = X_l ≠ 0`.
* `d88Box`: on each polydisc of Lemma 6.19 (c) the certificate project gives `X₃ − X₄ ≠ 0`, all `X_l ≠ 0` and the
  `T`-test with margin `0.1756` for `t_l = 1/√|X_l| = |X_l|^{−1/2}`; the margin times `Σ_l m_l t_l > 0` makes the
  `T`-test strict (`ttest_of_TTest4`).
-/

namespace CC6Compose

open CC6Full CC6Full.Six Finset Metric

namespace BoxBridge

/-! ## The systems of the two projects -/

/-- `KC₁₂(μ₀)` of the certificate project is `D94.KC12 D94.μ0`. -/
theorem KC12_eq (v : Fin 12 → ℂ) : Lean6.Special.D88.Boxes.KC.KC12 v = D94.KC12 D94.μ0 v := rfl

/-- The positions `X` on the slice `X₁ = 1` of the two projects agree. -/
theorem KC_X_eq (v : Fin 12 → ℂ) : Lean6.Special.D88.Boxes.KC.X v = D94.X v := rfl

/-- `S11(μ₀)` of the certificate project is `D88.S11 D88.μ0`. -/
theorem S11_eq (v : Fin 11 → ℂ) : Lean6.Special.D88.Boxes.N4.S11 v = D88.S11 D88.μ0 v := rfl

/-- The positions `X` on the slice `X₁ − X₂ = 1` of the two projects agree. -/
theorem N4_X_eq (v : Fin 11 → ℂ) : Lean6.Special.D88.Boxes.N4.X v = D88.X D88.μ0 v := rfl

/-- `ρ = 2√2 = 2^{3/2}`. -/
theorem rho_eq : Lean6.Special.D88.Boxes.rho = (2 : ℝ) ^ ((3 : ℝ) / 2) := by
  rw [Lean6.Special.D88.Boxes.rho, Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]

/-- The masses `(1, 2, 3)` of the bodies `1, 2, 3` in the two projects. -/
theorem μ3R_eq (l : Fin 3) : ((D94.μ3R l : ℝ) : ℂ) = Lean6.Special.D88.Boxes.μ3 l := by
  fin_cases l <;> simp [D94.μ3R, Lean6.Special.D88.Boxes.μ3]

/-- The masses `μ₀ = (1, 2, 3, 30)` of the two projects. -/
theorem μ0_re (l : Fin 4) : (Lean6.Special.D88.Boxes.μ0 l).re = D88.μ0R l := by
  fin_cases l <;> simp [Lean6.Special.D88.Boxes.μ0, D88.μ0R]

/-! ## One point in each of pairwise disjoint polydiscs -/

/-- Points `z k` in pairwise disjoint closed polydiscs are distinct: they form a set of `N` elements. -/
theorem card_image_of_disjoint {N n : ℕ} {c : Fin N → Fin n → ℂ} {r : Fin N → ℝ}
    (hdisj : Pairwise fun k l => Disjoint (closedBall (c k) (r k)) (closedBall (c l) (r l)))
    {z : Fin N → Fin n → ℂ} (hz : ∀ k, z k ∈ closedBall (c k) (r k)) : (univ.image z).card = N := by
  have hinj : Function.Injective z := by
    intro k l hkl
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hz k) (by rw [hkl]; exact hz l)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-! ## Diagram 94 -/

/-- The sums of Lemma 6.17 (b) do not vanish under the lower bound of the certificate project: the bound
`1.47·10⁻⁶ (1 + ρ²)^{1/2} Σ_l |β_l|` is positive when the square roots `w_l` do not vanish. -/
theorem kcSum_ne_zero {w : Fin 3 → ℂ} (hw : ∀ l, w l ≠ 0) {ε s : Fin 3 → ℤ}
    (hb : (147 / 100000000 : ℝ) * Real.sqrt (1 + Lean6.Special.D88.Boxes.rho ^ 2) *
      Lean6.Special.D88.Boxes.betaNorm w ≤ ‖Lean6.Special.D88.Boxes.kcSum w ε s‖) :
    Lean6.Special.D88.Boxes.kcSum w ε s ≠ 0 := by
  have hβ : 0 < Lean6.Special.D88.Boxes.betaNorm w := by
    unfold Lean6.Special.D88.Boxes.betaNorm
    refine Finset.sum_pos (fun l _ => norm_pos_iff.mpr (div_ne_zero ?_ (hw l))) Finset.univ_nonempty
    fin_cases l <;> norm_num [Lean6.Special.D88.Boxes.μ3]
  have hpos : 0 < (147 / 100000000 : ℝ) * Real.sqrt (1 + Lean6.Special.D88.Boxes.rho ^ 2) *
      Lean6.Special.D88.Boxes.betaNorm w := by
    rw [Lean6.Special.D88.Boxes.sqrt_one_add_rho_sq]
    exact mul_pos (by norm_num) hβ
  intro h0
  rw [h0, norm_zero] at hb
  linarith

end BoxBridge

open BoxBridge in
/-- **`D94Box`** (Lemma 6.19 (d)) from `lemma_6_19_d` of the certificate project: the set of the zeros of
`KC₁₂(μ₀)` chosen in the `4788` disjoint polydiscs. -/
theorem d94Box_of (h : type_of% @Lean6.Special.D88.Boxes.lemma_6_19_d) : D94Box := by
  obtain ⟨c, r, -, hdisj, hball⟩ := h
  choose z hz hzero using fun k => (hball k).1
  refine ⟨univ.image z, card_image_of_disjoint hdisj hz, fun v hv => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨-, hbound, hX⟩ := (hball k).2 (z k) (hz k)
  have hX' : ∀ l : Fin 3, D94.X (z k) l.castSucc ≠ 0 := fun l => by
    rw [← KC_X_eq]
    exact hX l
  refine ⟨by rw [← KC12_eq]; exact (hzero k).1, hX', fun w hw ε s hε hs => ?_⟩
  choose ε' hε' using fun l => Lean6.Special.D88.Boxes.int_sign (hε l)
  choose s' hs' using fun l => Lean6.Special.D88.Boxes.int_sign (hs l)
  have hw0 : ∀ l, w l ≠ 0 := fun l h0 => hX' l (by rw [← hw l, h0]; ring)
  have hw' : ∀ l, w l ^ 2 = Lean6.Special.D88.Boxes.KC.X (z k) l.castSucc := fun l => by
    rw [KC_X_eq]
    exact hw l
  have hne := kcSum_ne_zero hw0 (hbound w hw' ε' s' (fun l => (hε' l).1) (fun l => (hs' l).1))
  have hsum : ∑ l, ε l * ((D94.μ3R l : ℂ) / w l) * (1 + Complex.I * s l * (((2 : ℝ) ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) =
      Lean6.Special.D88.Boxes.kcSum w ε' s' := by
    unfold Lean6.Special.D88.Boxes.kcSum
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(hε' l).2, (hs' l).2, ← rho_eq, μ3R_eq]
    ring
  rw [hsum]
  exact hne

theorem d94Box : D94Box := d94Box_of Lean6.Special.D88.Boxes.lemma_6_19_d

/-! ## Diagram 88 -/

namespace BoxBridge

/-- The `T`-test of Lemma 6.17 (a) at the masses `μ₀`, strictly, from the `T`-test with margin `0.1756` of the
certificate project (`TTest4`, for `t_l = 1/√|X_l|`), when all `X_l ≠ 0`: `t_l = |X_l|^{−1/2} > 0`, and the margin
times `Σ_l m_l t_l > 0` bounds `m_k t_k − Σ_{l≠k} m_l t_l` from below. -/
theorem ttest_of_TTest4 {x : Fin 4 → ℂ} (hx : ∀ l, x l ≠ 0)
    (hT : Lean6.Special.D88.Boxes.TTest4 fun l => 1 / Real.sqrt ‖x l‖) :
    ∃ k : Fin 4, D88.μ0R k * ‖x k‖ ^ (-(1 / 2 : ℝ)) >
      ∑ l ∈ univ.erase k, D88.μ0R l * ‖x l‖ ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨k, hk⟩ := hT
  refine ⟨k, ?_⟩
  have ht : ∀ l, ‖x l‖ ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt ‖x l‖ := fun l => by
    rw [Real.rpow_neg (norm_nonneg _), ← Real.sqrt_eq_rpow, one_div]
  have hpos : ∀ l, 0 < D88.μ0R l * (1 / Real.sqrt ‖x l‖) := fun l => by
    have h1 : 0 < D88.μ0R l := by fin_cases l <;> norm_num [D88.μ0R]
    exact mul_pos h1 (one_div_pos.mpr (Real.sqrt_pos.mpr (norm_pos_iff.mpr (hx l))))
  have hS : 0 < ∑ l, D88.μ0R l * (1 / Real.sqrt ‖x l‖) :=
    Finset.sum_pos (fun l _ => hpos l) Finset.univ_nonempty
  simp only [μ0_re] at hk
  rw [CC6Full.Six.sum_ite_eq_sum_erase] at hk
  simp only [ht]
  linarith

end BoxBridge

open BoxBridge in
/-- **`D88Box`** (Lemma 6.19 (c)) from `lemma_6_19_c` of the certificate project: the set of the zeros of
`S11(μ₀)` chosen in the `20316` disjoint polydiscs. -/
theorem d88Box_of (h : type_of% @Lean6.Special.D88.Boxes.lemma_6_19_c) : D88Box := by
  obtain ⟨c, r, -, hdisj, hball⟩ := h
  choose z hz hzero using fun k => (hball k).1
  refine ⟨univ.image z, card_image_of_disjoint hdisj hz, fun v hv => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨h34, hT, hX⟩ := (hball k).2 (z k) (hz k)
  rw [← S11_eq, ← N4_X_eq]
  exact ⟨(hzero k).1, h34, hX, ttest_of_TTest4 hX hT⟩

theorem d88Box : D88Box := d88Box_of Lean6.Special.D88.Boxes.lemma_6_19_c

end CC6Compose
