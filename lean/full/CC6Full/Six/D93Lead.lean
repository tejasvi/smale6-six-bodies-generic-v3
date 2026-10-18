import CC6Full.Six.D98Lead

/-!
# Diagram 93: the leading data (the proof of Theorem 6.15)

§6.6 of the paper (`ss:d93`). At a singular place with diagram `93` (Table 1, `Diagram.d93`), `B = {1, 2, 3}` is the
fully `w`-circled triangle of `w`-strokes and `A = {4, 5, 6}` the triangle of `z`-strokes, in which `5`, `6` are
`z`-circled and `4` is not. In Lean body `k` of the paper is `k − 1`: `B = {0, 1, 2}` (renumbered by `Six.triB`),
`A = {3, 4, 5}`, and body `4` of the paper is `3`. Everything is stated for a germ `G : Germ 6 m` with positive masses
(`hm : ∀ i, 0 < m i`) and `G.HasDiagram Diagram.d93`.

The facts of the proof of Theorem 6.15 (`thm:d93`) that concern the leading data:

* `Six.d93_exps`: the exponents. By (F1) of Lemma 6.1 (`lem:common`), `ζ = −2`, `ω = 2`, `x = 0` on the pairs of
  `A` and `ω = −2`, `ζ = 2`, `x = 0` on the pairs of `B`; by (F2) and (F3), `b_4, b_5, b_6 ≥ 2` and `a_l ≥ 2` for
  `l ∈ B`; and `−2 < a_4 < 2`.
* `Six.d93_leadB`: the leading system of `B` in both colours is complete: `(ŵ_B, [z_B]_2, p̂_B)` with
  `ŵ_l = [w_l]_{−2}` and `p̂_ll' = [p_ll']_0` solves `N(m_B)` (`IsNSys`).
* `Six.d93_cross`: with `P_l = p̂_{4l}` the leading coefficient of `p_{4l}`, `P_l² ẑ_4 ŵ_l = −1` for `l ∈ B` ((F4)).
* `Six.d93_torque`: `Σ_{l∈B} m_l P_l = 0`, from the coefficient of exponent `1 − a_4/2` of the torque `T_A`.
* `Six.d93_lead`: the four facts in one statement.
-/

namespace CC6Full

open Finset

noncomputable section

namespace Six

/-! ## The diagram -/

theorem d93_zS (k l : Fin 6) : Diagram.d93.zS k l ↔ (k ≠ l ∧ 3 ≤ k.val ∧ 3 ≤ l.val) := by
  revert k l
  unfold Diagram.zS
  decide

theorem d93_wS (k l : Fin 6) : Diagram.d93.wS k l ↔ (k ≠ l ∧ k.val < 3 ∧ l.val < 3) := by
  revert k l
  unfold Diagram.wS
  decide

theorem d93_zC (k : Fin 6) : k ∈ Diagram.d93.zCircles ↔ 4 ≤ k.val := by
  revert k
  decide

theorem d93_wC (k : Fin 6) : k ∈ Diagram.d93.wCircles ↔ k.val < 3 := by
  revert k
  decide

variable {m : Fin 6 → ℝ}

/-- The diagram `93` read on the germ: `z`-strokes on the pairs of `A`, `w`-strokes on the pairs of `B`, the
`z`-circles `5, 6` of the paper (`4, 5` in Lean) and the `w`-circles `B`. -/
theorem d93_facts {G : Germ 6 m} (hD : G.HasDiagram Diagram.d93) :
    (∀ k l, G.zStroke k l ↔ (k ≠ l ∧ 3 ≤ k.val ∧ 3 ≤ l.val)) ∧
      (∀ k l, G.wStroke k l ↔ (k ≠ l ∧ k.val < 3 ∧ l.val < 3)) ∧ (∀ k, G.zCircle k ↔ 4 ≤ k.val) ∧
        (∀ k, G.wCircle k ↔ k.val < 3) :=
  ⟨fun k l => (hD.1 k l).trans (d93_zS k l), fun k l => (hD.2.1 k l).trans (d93_wS k l),
    fun k => (hD.2.2.1 k).trans (d93_zC k), fun k => (hD.2.2.2 k).trans (d93_wC k)⟩

/-! ## The exponents -/

/-- The exponents in the proof of **Theorem 6.15** (`thm:d93`), at a singular place with diagram `93`: by (F1) of
Lemma 6.1 (`lem:common`), `ζ = −2`, `ω = 2`, `x = 0` on the pairs of `A` and `ω = −2`, `ζ = 2`, `x = 0` on the pairs
of `B`; by (F2) and (F3), `b_k ≥ 2` for `k ∈ A` and `a_l ≥ 2` for `l ∈ B`; `a_5 = a_6 = −2` and `b_l = −2` for
`l ∈ B` (the circles); and `−2 < a_4 < 2`: `4` is not `z`-circled, and if `a_4 ≥ 2`, then `ζ_41 ≥ min(a_4, a_1) ≥ 2`,
so `ζ_41 = 2` and `41` would be a `w`-stroke by (O1) and (O6) of Lemma 2.8 (`lem:orders`). In Lean's numbering
`A = {3, 4, 5}`, `B = {0, 1, 2}` and body `4` of the paper is `3`. -/
theorem d93_exps (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d93) :
    (∀ j j' : Fin 6, 3 ≤ j.val → 3 ≤ j'.val → j ≠ j' →
        G.zeta j j' = -2 ∧ G.omega j j' = 2 ∧ G.x j j' = 0) ∧
      (∀ l l' : Fin 6, l.val < 3 → l'.val < 3 → l ≠ l' →
        G.omega l l' = -2 ∧ G.zeta l l' = 2 ∧ G.x l l' = 0) ∧
      (∀ k : Fin 6, 3 ≤ k.val → ((2 : ℚ) : WithTop ℚ) ≤ (G.w k).orderTop) ∧
      (∀ k : Fin 6, 4 ≤ k.val → (G.z k).orderTop = ((-2 : ℚ) : WithTop ℚ)) ∧
      (∀ l : Fin 6, l.val < 3 →
        (G.w l).orderTop = ((-2 : ℚ) : WithTop ℚ) ∧ ((2 : ℚ) : WithTop ℚ) ≤ (G.z l).orderTop) ∧
      ((-2 : ℚ) : WithTop ℚ) < (G.z 3).orderTop ∧ (G.z 3).orderTop < ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨hz, hw, hzc, hwc⟩ := d93_facts hD
  have hzA : ∀ k ∈ univ.image triA, ∀ l ∈ univ.image triA, k ≠ l → G.zStroke k l := fun k hk l hl hkl =>
    (hz k l).mpr ⟨hkl, (mem_image_triA k).mp hk, (mem_image_triA l).mp hl⟩
  have hcA : ∀ k, G.zCircle k → k ∈ univ.image triA := fun k hk => (mem_image_triA k).mpr (by
    have := (hzc k).mp hk
    omega)
  have hwB : ∀ k ∈ univ.image triB, ∀ l ∈ univ.image triB, k ≠ l → G.wStroke k l := fun k hk l hl hkl =>
    (hw k l).mpr ⟨hkl, (mem_image_triB k).mp hk, (mem_image_triB l).mp hl⟩
  have hcB : ∀ k, G.wCircle k → k ∈ univ.image triB := fun k hk => (mem_image_triB k).mpr ((hwc k).mp hk)
  -- (F1) on `A` and on `B`
  have hA : ∀ j j' : Fin 6, 3 ≤ j.val → 3 ≤ j'.val → j ≠ j' →
      G.zeta j j' = -2 ∧ G.omega j j' = 2 ∧ G.x j j' = 0 := fun j j' hj hj' hjj =>
    F1_z hm G hzA ⟨4, (mem_image_triA 4).mpr (by decide), (hzc 4).mpr (by decide)⟩ hcA
      ((mem_image_triA j).mpr hj) ((mem_image_triA j').mpr hj') hjj
  have hB : ∀ l l' : Fin 6, l.val < 3 → l'.val < 3 → l ≠ l' →
      G.omega l l' = -2 ∧ G.zeta l l' = 2 ∧ G.x l l' = 0 := fun l l' hl hl' hll =>
    F1_w hm G hwB ⟨0, (mem_image_triB 0).mpr (by decide), (hwc 0).mpr (by decide)⟩ hcB
      ((mem_image_triB l).mpr hl) ((mem_image_triB l').mpr hl') hll
  -- (F2): `b_5, b_6 ≥ 2`; (F3) on the `z`-stroke `45` with `x_45 = 0`: `b_4 ≥ min(b_5, 2) = 2`
  have hb56 : ∀ k : Fin 6, 4 ≤ k.val → ((2 : ℚ) : WithTop ℚ) ≤ (G.w k).orderTop := fun k hk =>
    F2_z hm G hzA hcA ((hzc k).mpr hk)
  have hbA : ∀ k : Fin 6, 3 ≤ k.val → ((2 : ℚ) : WithTop ℚ) ≤ (G.w k).orderTop := by
    intro k hk
    rcases Nat.lt_or_ge k.val 4 with h4 | h4
    · have hk3 : k = 3 := Fin.ext (show k.val = 3 by omega)
      subst hk3
      have h34 := F3_w G ((hz 3 4).mpr ⟨by decide, by decide, by decide⟩)
        (hA 3 4 (by decide) (by decide) (by decide)).2.2
      rw [min_eq_right (hb56 4 (by decide))] at h34
      exact h34
    · exact hb56 k h4
  -- (F2) on `B`
  have hBl : ∀ l : Fin 6, l.val < 3 →
      (G.w l).orderTop = ((-2 : ℚ) : WithTop ℚ) ∧ ((2 : ℚ) : WithTop ℚ) ≤ (G.z l).orderTop := fun l hl =>
    ⟨(hwc l).mpr hl, F2_w hm G hwB hcB ((hwc l).mpr hl)⟩
  -- `−2 < a_4`: the body `4` is not `z`-circled
  have ha1 : ((-2 : ℚ) : WithTop ℚ) < (G.z 3).orderTop :=
    lt_of_le_of_ne (G.low_z.1 3) fun h => absurd ((hzc 3).mp h.symm) (by decide)
  -- `a_4 < 2`: otherwise `ζ_41 = 2` and `41` would be a `w`-stroke
  have ha2 : (G.z 3).orderTop < ((2 : ℚ) : WithTop ℚ) := by
    by_contra hcon
    have h2 : ((2 : ℚ) : WithTop ℚ) ≤ (G.z 3).orderTop := not_lt.mp hcon
    have h30 : (3 : Fin 6) ≠ 0 := by decide
    have h4 : ((2 : ℚ) : WithTop ℚ) ≤ (G.zeta 3 0 : WithTop ℚ) :=
      le_trans (le_min h2 (hBl 0 (by decide)).2) (G.min_le_zeta h30)
    have hζ : G.zeta 3 0 = 2 := le_antisymm (G.O1_le h30).1 (WithTop.coe_le_coe.mp h4)
    have h3 := ((hw 3 0).mp (G.O6_z' hζ).2).2.1
    exact absurd h3 (by decide)
  exact ⟨hA, hB, hbA, fun k hk => (hzc k).mpr hk, hBl, ha1, ha2⟩

/-! ## The leading data -/

/-- The leading system of `B` in the proof of **Theorem 6.15** (`thm:d93`): at a singular place with diagram `93`,
`(ŵ_B, [z_B]_2, p̂_B)` with `ŵ_l = [w_l]_{−2}`, `[z_l]_2` and `p̂_ll' = [p_ll']_0` (`B` renumbered by `triB`) solves
`N(m_B)`. The system is complete: the cross terms in the `w`-equations of `B` at exponent `−2` and in the
`z`-equations at exponent `2` have exponents `1 − 3ζ_lj/2 > −2` and `3 − ζ_lj/2 > 2` (`ω_lj = −2`, `ζ_lj < 2` for
`j ∈ A`; for `j = 4`, `ζ_l4 = a_4`), so `Tri.lead_w` applies. -/
theorem d93_leadB (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d93) :
    IsNSys (fun l => (m (triB l) : ℂ)) (fun l => (G.w (triB l)).coeff (-2)) (fun l => (G.z (triB l)).coeff 2)
      (fun l l' => (G.p (triB l) (triB l')).coeff 0) := by
  obtain ⟨-, hw, -, hwc⟩ := d93_facts hD
  obtain ⟨-, hB, -⟩ := d93_exps hm G hD
  refine Tri.lead_w G triB_injective (fun l l' h => ?_) (fun l j hj => ?_)
  · obtain ⟨h1, h2, -⟩ := hB _ _ (triB_lt_three l) (triB_lt_three l') (triB_injective.ne h)
    exact ⟨h1, h2⟩
  · have hj3 : 3 ≤ j.val := by
      rw [mem_image_triB] at hj
      omega
    have hl3 := triB_lt_three l
    have hlj : triB l ≠ j := fun h => by
      rw [h] at hl3
      omega
    refine ⟨G.O6_w ((hwc _).mpr hl3) fun h => ?_, Tri.zeta_lt_two G hlj fun h => ?_⟩
    · have := (hwc j).mp h
      omega
    · have := ((hw _ j).mp h).2.2
      omega

/-- The cross relation in the proof of **Theorem 6.15** (`thm:d93`): at a singular place with diagram `93`, with
`P_l = p̂_{4l}` the leading coefficient of `p_{4l}`, `ẑ_4` that of `z_4` and `ŵ_l = [w_l]_{−2}`,
`P_l² ẑ_4 ŵ_l = −1` for `l ∈ B` ((F4) of Lemma 6.1, `lem:common`: `a_4 < 2 ≤ a_l` and `b_l = −2 < 2 ≤ b_4`). -/
theorem d93_cross (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d93) :
    ∀ l : Fin 3,
      (G.p 3 (triB l)).leadingCoeff ^ 2 * (G.z 3).leadingCoeff * (G.w (triB l)).coeff (-2) = -1 := by
  obtain ⟨-, -, hbA, -, hB, -, ha2⟩ := d93_exps hm G hD
  obtain ⟨A, hA, hA2⟩ := Tri.exists_coe_of_lt ha2
  intro l
  obtain ⟨hwl, hzl⟩ := hB _ (triB_lt_three l)
  have h := (F4_z G hA hwl (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hA2) hzl)
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (hbA 3 (by decide)))).2.2.2.2.2
  rw [Ser.coeff_of_orderTop_eq hwl]
  exact h

/-- The torque relation in the proof of **Theorem 6.15** (`thm:d93`): at a singular place with diagram `93`, with
`P_l = p̂_{4l}` the leading coefficient of `p_{4l}`, `Σ_{l∈B} m_l P_l = 0`. In the torque `T_A`, the pairs `(4, l)`
satisfy (F4) of Lemma 6.1 (`lem:common`) with exponent `1 − a_4/2 < 2` and leading coefficient `−m_4 m_l P_l`, and
the pairs `(j, l)`, `j = 5, 6`, give exponent `2`; the coefficient of exponent `1 − a_4/2` is
`−m_4 Σ_{l∈B} m_l P_l`. -/
theorem d93_torque (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d93) :
    ∑ l : Fin 3, (m (triB l) : ℂ) * (G.p 3 (triB l)).leadingCoeff = 0 := by
  obtain ⟨-, -, hbA, hzA, hB, ha1, ha2⟩ := d93_exps hm G hD
  obtain ⟨A, hA, hA2⟩ := Tri.exists_coe_of_lt ha2
  have hA1 : -2 < A := by
    rw [hA] at ha1
    exact WithTop.coe_lt_coe.mp ha1
  have hb3 : ((-2 : ℚ) : WithTop ℚ) < (G.w 3).orderTop :=
    lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (hbA 3 (by decide))
  -- the pairs `(4, l)`: exponent `1 − a_4/2` and leading coefficient `−m_4 m_l P_l`
  have h0 : ∀ l : Fin 3, (cS (m 3) * cS (m (triB l)) * (G.p 3 (triB l) ^ 3 *
      (G.z 3 * G.w (triB l) - G.z (triB l) * G.w 3))).coeff (-((A + -2) / 2)) =
        -((m 3 : ℂ) * (m (triB l) : ℂ) * (G.p 3 (triB l)).leadingCoeff) := by
    intro l
    have hal : (A : WithTop ℚ) < (G.z (triB l)).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hA2) (hB _ (triB_lt_three l)).2
    obtain ⟨ho, hc⟩ := F4_z_term hm G hA (hB _ (triB_lt_three l)).1 hal hb3 (K4.coe_add_lt hal.le hb3)
    rw [Ser.coeff_of_orderTop_eq ho, hc]
  -- the pairs `(j, l)`, `j = 5, 6`: exponent `2 > 1 − a_4/2`
  have hfar : ∀ k : Fin 6, 4 ≤ k.val → ∀ l : Fin 3, (cS (m k) * cS (m (triB l)) * (G.p k (triB l) ^ 3 *
      (G.z k * G.w (triB l) - G.z (triB l) * G.w k))).coeff (-((A + -2) / 2)) = 0 := by
    intro k hk l
    have hal : ((-2 : ℚ) : WithTop ℚ) < (G.z (triB l)).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (hB _ (triB_lt_three l)).2
    have hbk : ((-2 : ℚ) : WithTop ℚ) < (G.w k).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (hbA k (by omega))
    obtain ⟨ho, -⟩ := F4_z_term hm G (hzA k hk) (hB _ (triB_lt_three l)).1 hal hbk (K4.coe_add_lt hal.le hbk)
    apply Ser.coeff_eq_zero_of_lt
    rw [ho]
    exact WithTop.coe_lt_coe.mpr (by linarith)
  have hT := Tri.torque_coeff G (-((A + -2) / 2))
  rw [Fin.sum_univ_three, triA_zero, triA_one, triA_two] at hT
  simp only [h0, hfar 4 (by decide), hfar 5 (by decide), Finset.sum_const_zero, add_zero] at hT
  have h3 : (m 3 : ℂ) * ∑ l : Fin 3, (m (triB l) : ℂ) * (G.p 3 (triB l)).leadingCoeff = 0 := by
    simp only [Fin.sum_univ_three] at hT ⊢
    linear_combination -hT
  exact (mul_eq_zero.mp h3).resolve_left (K4.mass_ne_zero hm 3)

/-- The leading data in the proof of **Theorem 6.15** (`thm:d93`), in one statement. At a singular place with diagram
`93` (`B = {1, 2, 3}` of the paper renumbered `0, 1, 2` by `triB`; body `4` of the paper is `3` in Lean):
`−2 < a_4 < 2`; the leading data of `B` in both colours, `(ŵ_B, [z_B]_2, p̂_B)` with `ŵ_l = [w_l]_{−2}` and
`p̂_ll' = [p_ll']_0`, solve `N(m_B)`; and with `P_l` the leading coefficient of `p_{4l}` and `ẑ_4` that of `z_4`,
`P_l² ẑ_4 ŵ_l = −1` for `l ∈ B` and `Σ_{l∈B} m_l P_l = 0`. -/
theorem d93_lead (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d93) :
    (((-2 : ℚ) : WithTop ℚ) < (G.z 3).orderTop ∧ (G.z 3).orderTop < ((2 : ℚ) : WithTop ℚ)) ∧
    IsNSys (fun l => (m (triB l) : ℂ)) (fun l => (G.w (triB l)).coeff (-2)) (fun l => (G.z (triB l)).coeff 2)
      (fun l l' => (G.p (triB l) (triB l')).coeff 0) ∧
    (∀ l : Fin 3,
      (G.p 3 (triB l)).leadingCoeff ^ 2 * (G.z 3).leadingCoeff * (G.w (triB l)).coeff (-2) = -1) ∧
    ∑ l : Fin 3, (m (triB l) : ℂ) * (G.p 3 (triB l)).leadingCoeff = 0 := by
  obtain ⟨-, -, -, -, -, ha1, ha2⟩ := d93_exps hm G hD
  exact ⟨⟨ha1, ha2⟩, d93_leadB hm G hD, d93_cross hm G hD, d93_torque hm G hD⟩

end Six

end

end CC6Full
