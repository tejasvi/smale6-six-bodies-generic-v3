import CC6Full.Six.K4Aux

/-!
# Diagram 66: the leading system `C₄` (Lemmas 7.4, 7.5)

§7.1 of the paper. At a singular place with diagram `66` (Table 1, `Diagram.d66`): the bodies of
`K = {3, 4, 5, 6}` are pairwise joined by `z`-strokes, none is `z`-circled, the `w`-strokes form the triangle
`{1, 2, 6}`, and `1`, `2` are the `w`-circled bodies. Let `S = {3, 4, 5}`; the body `6` is the centre. In Lean body
`k` of the paper is `k − 1`: `K = {2, 3, 4, 5}`, `S = {2, 3, 4}`, the centre is `5` and the `w`-triangle is
`{0, 1, 5}`. The masses are arbitrary: unlike Lemmas 7.1–7.3, these two lemmas use no property of the masses
(no partial sum of masses is divided by).

* `Germ.d66type_a`, `Germ.d66type_tri`, `Germ.d66type_cross`, `Germ.d66type_bodies`, `Germ.d66type_sum`:
  Lemma 7.4 (`lem:d66type`): (a) of Lemma 7.1 on `K`; `ω = −2`, `ζ = 2`, `x = 0` on `12, 16, 26`;
  `ω_jk = −2` and `ζ_jk = a_k = 3x − 2` for `j ∈ {1, 2}`, `k ∈ S`; `b_1 = b_2 = −2`, `b_k > −2` for `k ∈ K`,
  `a_1, a_2, a_6 ≥ 2`; hence `[z_6]_{3x−2} = 0` and `Σ_{k∈S} m_k [z_k]_{3x−2} = 0`.
* `Germ.d66lead`: Lemma 7.5 (`lem:d66lead`): with `ξ_k = [z_k]_{3x−2}`, `η_k = [w_k]_{2−x}` (so that
  `η_k − η_l = [w_kl]_{2−x}`) and `P_kl = [p_kl]_{−x}` for `k, l ∈ K` (`K4.xiK`, `K4.etaK`, `K4.PK`, with `K`
  renumbered `0, 1, 2, 3` in increasing order by `K4.emb`, so that the centre `6` is last), the differences, the
  `η_kl` and the `P_kl` are nonzero, and `(ξ, η, P, c)` solves `C₄(m_3, m_4, m_5, m_6)` (`IsC4`) with
  `c = [w_6]_{2−4x}`: (i) the distance equations, (ii) `Φ^ξ_k = 0` for `k ∈ K`, (iii) `Φ^η_k = c` for `k ∈ S`,
  `ξ_6 = 0` and `Σ_{k∈S} m_k ξ_k = 0`.
* `Germ.d66_exists_C4`: `C₄(m_3, m_4, m_5, m_6)` has a solution.

In (iii) the common value `c` is `[w_k]_{2−4x}`, the same for all `k ∈ K` because `ω_kl = 2 − x > 2 − 4x` on `K`;
the paper's case distinction (`c = 0` if `b_k > 2 − 4x` for all `k ∈ S`) is not needed.
-/

namespace CC6Full

open Finset

noncomputable section

namespace Germ

variable {m : Fin 6 → ℝ} (G : Germ 6 m)

/-! ## The diagram -/

theorem d66_zS (k l : Fin 6) : Diagram.d66.zS k l ↔ (k ≠ l ∧ 2 ≤ k.val ∧ 2 ≤ l.val) := by
  revert k l
  unfold Diagram.zS
  decide

theorem d66_wS (k l : Fin 6) :
    Diagram.d66.wS k l ↔ (k ≠ l ∧ (k.val < 2 ∨ k.val = 5) ∧ (l.val < 2 ∨ l.val = 5)) := by
  revert k l
  unfold Diagram.wS
  decide

theorem d66_zC (k : Fin 6) : k ∉ Diagram.d66.zCircles := by
  revert k
  decide

theorem d66_wC (k : Fin 6) : k ∈ Diagram.d66.wCircles ↔ k.val < 2 := by
  revert k
  decide

/-- The diagram `66` read on the germ: `z`-strokes on the pairs of `K`, the `w`-strokes of the triangle
`{1, 2, 6}`, no `z`-circle, the `w`-circles `1, 2`. -/
theorem d66_facts (hD : G.HasDiagram Diagram.d66) :
    (∀ k l, G.zStroke k l ↔ (k ≠ l ∧ 2 ≤ k.val ∧ 2 ≤ l.val)) ∧
      (∀ k l, G.wStroke k l ↔ (k ≠ l ∧ (k.val < 2 ∨ k.val = 5) ∧ (l.val < 2 ∨ l.val = 5))) ∧
        (∀ k, ¬ G.zCircle k) ∧ (∀ k, G.wCircle k ↔ k.val < 2) :=
  ⟨fun k l => (hD.1 k l).trans (d66_zS k l), fun k l => (hD.2.1 k l).trans (d66_wS k l),
    fun k h => d66_zC k ((hD.2.2.1 k).mp h), fun k => (hD.2.2.2 k).trans (d66_wC k)⟩

theorem fin6_pair01 {j l : Fin 6} (hj : j.val < 2) (hl : l.val < 2) (hlj : l ≠ j) :
    (j = 0 ∧ l = 1) ∨ (j = 1 ∧ l = 0) := by
  revert j l
  decide

/-! ## Lemma 7.4 -/

/-- **Lemma 7.4** (`lem:d66type`), (a) of Lemma 7.1: on the six pairs of `K`, `ζ = 3x − 2` and `ω = 2 − x` with
one common `x = x_{34}`, and `0 < x < 1`. -/
theorem d66type_a (hD : G.HasDiagram Diagram.d66) :
    0 < G.x 2 3 ∧ G.x 2 3 < 1 ∧ K4.PairsK G (G.x 2 3) := by
  obtain ⟨hz, hw, hzc, -⟩ := G.d66_facts hD
  exact K4.pairsK G (fun k l hk hl hkl => (hz k l).mpr ⟨hkl, hk, hl⟩)
    (fun h => by have := ((hw 2 3).mp h).2.1; simp at this) (hzc 2) (hzc 3)

/-- **Lemma 7.4** (`lem:d66type`): on the pairs `12`, `16`, `26` of the `w`-triangle, `ω = −2`, `ζ = 2` and `x = 0`
((F1) with the colours exchanged). -/
theorem d66type_tri (hD : G.HasDiagram Diagram.d66) :
    ∀ j k : Fin 6, (j.val < 2 ∨ j.val = 5) → (k.val < 2 ∨ k.val = 5) → j ≠ k →
      G.omega j k = -2 ∧ G.zeta j k = 2 ∧ G.x j k = 0 := by
  obtain ⟨-, hw, -, hwc⟩ := G.d66_facts hD
  have hc5 : ¬ G.wCircle 5 := fun h => absurd ((hwc 5).mp h) (by decide)
  have hω05 : G.omega 0 5 = -2 := G.O6_w ((hwc 0).mpr (by decide)) hc5
  have hω15 : G.omega 1 5 = -2 := G.O6_w ((hwc 1).mpr (by decide)) hc5
  have hω01 : G.omega 0 1 = -2 := by
    have e := G.E3 (Or.inr ((hw 0 1).mpr ⟨by decide, by decide, by decide⟩))
      (Or.inr ((hw 1 5).mpr ⟨by decide, by decide, by decide⟩))
      (Or.inr ((hw 5 0).mpr ⟨by decide, by decide, by decide⟩))
    rw [e.2.2.1, hω15]
  have hω : ∀ j k : Fin 6, (j.val < 2 ∨ j.val = 5) → (k.val < 2 ∨ k.val = 5) → j ≠ k → G.omega j k = -2 := by
    intro j k hj hk hjk
    by_cases hj5 : j.val = 5
    · have hk2 : k.val < 2 := by
        rcases hk with hk | hk
        · exact hk
        · exact absurd (Fin.ext (hj5.trans hk.symm)) hjk
      rw [G.omega_comm]
      exact G.O6_w ((hwc k).mpr hk2) (fun h => by have := (hwc j).mp h; omega)
    · have hj2 : j.val < 2 := hj.resolve_right hj5
      by_cases hk5 : k.val = 5
      · exact G.O6_w ((hwc j).mpr hj2) (fun h => by have := (hwc k).mp h; omega)
      · rcases fin6_pair01 hj2 (hk.resolve_right hk5) (Ne.symm hjk) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hω01
        · rw [G.omega_comm]
          exact hω01
  intro j k hj hk hjk
  obtain ⟨hω3, hζ3, -, -⟩ := G.O3_w ((hw j k).mpr ⟨hjk, hj, hk⟩)
  have h1 := hω j k hj hk hjk
  have hx : G.x j k = 0 := by linarith
  exact ⟨h1, by rw [hζ3, hx]; ring, hx⟩

/-- **Lemma 7.4** (`lem:d66type`): `b_1 = b_2 = −2` (`w`-circles), `b_k > −2` for `k ∈ K`, and `a_1, a_2 ≥ 2` and
`a_6 ≥ 2` (the latter by (F3): `z_6 = z_1 + z_{61}` with `ζ_61 = 2`). -/
theorem d66type_bodies (hD : G.HasDiagram Diagram.d66) :
    (∀ j : Fin 6, j.val < 2 → G.wCircle j) ∧
      (∀ k : Fin 6, 2 ≤ k.val → ((-2 : ℚ) : WithTop ℚ) < (G.w k).orderTop) ∧
        ∀ j : Fin 6, (j.val < 2 ∨ j.val = 5) → ((2 : ℚ) : WithTop ℚ) ≤ (G.z j).orderTop := by
  obtain ⟨-, -, -, hwc⟩ := G.d66_facts hD
  have htri := G.d66type_tri hD
  have ha : ∀ j : Fin 6, j.val < 2 → ((2 : ℚ) : WithTop ℚ) ≤ (G.z j).orderTop := by
    intro j hj
    apply K4.two_le_orderTop_z
    intro l hlj
    by_cases hl : l.val < 2
    · exact (htri j l (Or.inl hj) (Or.inl hl) (Ne.symm hlj)).1
    · exact G.O6_w ((hwc j).mpr hj) (fun h => absurd ((hwc l).mp h) hl)
  refine ⟨fun j hj => (hwc j).mpr hj,
    fun k hk => lt_of_le_of_ne (G.low_w.1 k) (fun h => by have := (hwc k).mp h.symm; omega), ?_⟩
  intro j hj
  rcases hj with hj | hj
  · exact ha j hj
  · -- (F3) for the `w`-stroke `60` with `x = 0`
    have hj5 : j = 5 := Fin.ext hj
    subst hj5
    have h50 : (5 : Fin 6) ≠ 0 := by decide
    have hζ := (htri 5 0 (Or.inr rfl) (Or.inl (by decide)) h50).2.1
    have e : G.z 5 = G.z 0 + (G.z 5 - G.z 0) := by ring
    rw [e]
    refine le_trans (le_min (ha 0 (by decide)) ?_) HahnSeries.min_orderTop_le_orderTop_add
    rw [G.orderTop_z_sub h50, hζ]

/-- **Lemma 7.4** (`lem:d66type`): for `j ∈ {1, 2}` and `k ∈ S`, `ω_jk = −2` and `ζ_jk = a_k = 3x − 2`. -/
theorem d66type_cross (hD : G.HasDiagram Diagram.d66) :
    ∀ j k : Fin 6, j.val < 2 → 2 ≤ k.val → k.val < 5 →
      G.omega j k = -2 ∧ (G.z k).orderTop = ((3 * G.x 2 3 - 2 : ℚ) : WithTop ℚ) ∧
        G.zeta j k = 3 * G.x 2 3 - 2 := by
  obtain ⟨-, hw, -, hwc⟩ := G.d66_facts hD
  obtain ⟨hx0, hx1, hK⟩ := G.d66type_a hD
  obtain ⟨-, -, ha⟩ := G.d66type_bodies hD
  intro j k hj hk hk5
  have hjk : j ≠ k := fun h => by
    rw [h] at hj
    omega
  have hω : G.omega j k = -2 := G.O6_w ((hwc j).mpr hj) (fun h => by have := (hwc k).mp h; omega)
  -- `a_k = ζ_{6k} = 3x − 2`, since `a_6 ≥ 2`
  have h5k : (5 : Fin 6) ≠ k := fun h => by
    rw [← h] at hk5
    exact absurd hk5 (by decide)
  have hζ5k : G.zeta 5 k = 3 * G.x 2 3 - 2 := (hK 5 k (by decide) hk h5k).1
  have hak : (G.z k).orderTop = ((3 * G.x 2 3 - 2 : ℚ) : WithTop ℚ) := by
    have := (K4.orderTop_z_eq_zeta G h5k (ha 5 (Or.inr rfl)) (by rw [hζ5k]; linarith)).1
    rw [this, hζ5k]
  -- `ζ_jk < 2` (`jk` is not a `w`-stroke), so `ζ_jk = a_k`
  have hζ2 : G.zeta j k < 2 := by
    rcases (G.O1_le hjk).1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := ((hw j k).mp (G.O6_z' h).2).2.2
      omega
  have h1 := (K4.orderTop_z_eq_zeta G hjk (ha j (Or.inl hj)) hζ2).1
  rw [hak] at h1
  exact ⟨hω, hak, (WithTop.coe_inj.mp h1).symm⟩

/-- **Lemma 7.4** (`lem:d66type`), the conclusion: `[z_6]_{3x−2} = 0` and `Σ_{k∈S} m_k [z_k]_{3x−2} = 0` (at
exponent `3x − 2` only the bodies of `S` appear in `Σ_k m_k z_k = 0`). -/
theorem d66type_sum (hD : G.HasDiagram Diagram.d66) :
    (G.z 5).coeff (3 * G.x 2 3 - 2) = 0 ∧
      (m 2 : ℂ) * (G.z 2).coeff (3 * G.x 2 3 - 2) + (m 3 : ℂ) * (G.z 3).coeff (3 * G.x 2 3 - 2) +
        (m 4 : ℂ) * (G.z 4).coeff (3 * G.x 2 3 - 2) = 0 := by
  obtain ⟨hx0, hx1, -⟩ := G.d66type_a hD
  obtain ⟨-, -, ha⟩ := G.d66type_bodies hD
  have hlt : ∀ j : Fin 6, (j.val < 2 ∨ j.val = 5) → (G.z j).coeff (3 * G.x 2 3 - 2) = 0 := fun j hj =>
    Ser.coeff_eq_zero_of_lt (lt_of_lt_of_le (by exact_mod_cast (show 3 * G.x 2 3 - 2 < 2 by linarith))
      (ha j hj))
  have h5 := hlt 5 (Or.inr rfl)
  refine ⟨h5, ?_⟩
  have hc := K4.com_z_coeff G (3 * G.x 2 3 - 2)
  rw [Fin.sum_univ_six, hlt 0 (Or.inl (by decide)), hlt 1 (Or.inl (by decide)), h5] at hc
  linear_combination hc

/-! ## Lemma 7.5 -/

/-- **Lemma 7.5** (`lem:d66lead`). Put `ξ_k = [z_k]_{3x−2}`, `η_k = [w_k]_{2−x}` (so that
`η_kl = [w_kl]_{2−x} = η_k − η_l`) and `P_kl = [p_kl]_{−x}` for `k, l ∈ K`, with `K = {3, 4, 5, 6}` renumbered
`0, 1, 2, 3` in increasing order (the centre `6` last) and `x = x_{34}`. Then `(ξ, η, P, c)` with
`c = [w_6]_{2−4x}` solves `C₄(m_3, m_4, m_5, m_6)`: (i) `P_kl² (ξ_k − ξ_l)(η_k − η_l) = 1`, (ii) `Φ^ξ_k = 0` for
`k ∈ K`, (iii) `Φ^η_k = c` for `k ∈ S`, and `ξ_6 = 0`, `Σ_{k∈S} m_k ξ_k = 0` (Lemma 7.4). Moreover the differences
`ξ_k − ξ_l`, `η_k − η_l` and the `P_kl` (`k ≠ l`) are nonzero. -/
theorem d66lead (hD : G.HasDiagram Diagram.d66) :
    IsC4 (K4.muK m) (K4.xiK G (G.x 2 3)) (K4.etaK G (G.x 2 3)) (K4.PK G (G.x 2 3))
        ((G.w 5).coeff (2 - 4 * G.x 2 3)) ∧
      ∀ k l : Fin 4, k ≠ l → K4.xiK G (G.x 2 3) k - K4.xiK G (G.x 2 3) l ≠ 0 ∧
        K4.etaK G (G.x 2 3) k - K4.etaK G (G.x 2 3) l ≠ 0 ∧ K4.PK G (G.x 2 3) k l ≠ 0 := by
  obtain ⟨hz, -, hzc, -⟩ := G.d66_facts hD
  obtain ⟨hx0, hx1, hK⟩ := G.d66type_a hD
  have hcr := G.d66type_cross hD
  obtain ⟨h5, hS⟩ := G.d66type_sum hD
  have hns : ∀ k j : Fin 6, 2 ≤ k.val → j.val < 2 → ¬ G.zStroke k j := fun k j hk hj h => by
    have := ((hz k j).mp h).2.2
    omega
  -- (iii): for `k ∈ S`, the terms `W_kj`, `j = 1, 2`, vanish at `2 − 4x`, and `[w_k]_{2−4x} = [w_6]_{2−4x}`
  have heta : ∀ k : Fin 4, k ≠ 3 →
      force (K4.muK m) (K4.PK G (G.x 2 3)) (K4.etaK G (G.x 2 3)) k = (G.w 5).coeff (2 - 4 * G.x 2 3) := by
    intro k hk3
    have hk : 2 ≤ (K4.emb k).val := K4.two_le_emb k
    have hk5 : (K4.emb k).val < 5 := by
      rw [K4.emb_val]
      have : k.val ≠ 3 := fun h => hk3 (Fin.ext h)
      omega
    have hW : ∀ j : Fin 6, j.val < 2 → (termZ G.p G.w (K4.emb k) j).coeff (2 - 4 * G.x 2 3) = 0 := by
      intro j hj
      have hkj : K4.emb k ≠ j := fun h => by
        rw [h] at hk
        omega
      obtain ⟨hω, -, hζ⟩ := hcr j (K4.emb k) hj hk hk5
      rw [G.zeta_comm] at hζ
      rw [G.omega_comm] at hω
      exact K4.coeff_W_cross G hkj hζ hω (by linarith)
    rw [K4.lead_force_eta G hK k (hW 0 (by decide)) (hW 1 (by decide))]
    have hk5' : K4.emb k ≠ 5 := fun h => by
      rw [h] at hk5
      exact absurd hk5 (by decide)
    exact K4.coeff_w_eq_of_lt G hk5' (by rw [(hK _ 5 hk (by decide) hk5').2.1]; linarith)
  have hxi3 : K4.xiK G (G.x 2 3) 3 = 0 := h5
  have hC : IsC4 (K4.muK m) (K4.xiK G (G.x 2 3)) (K4.etaK G (G.x 2 3)) (K4.PK G (G.x 2 3))
      ((G.w 5).coeff (2 - 4 * G.x 2 3)) := by
    refine ⟨K4.PK_symm G _, K4.lead_dist G hK, fun k => K4.lead_force_xi G hK hns (fun k _ => hzc k) k,
      heta, hxi3, ?_⟩
    rw [Finset.sum_erase _ (by rw [hxi3, mul_zero]), Fin.sum_univ_four, hxi3, mul_zero, add_zero]
    exact hS
  refine ⟨hC, fun k l hkl => ?_⟩
  have d := hC.2.1 k l hkl
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩ <;> simp [h0] at d

/-- By Lemmas 7.4 and 7.5, at a singular place with diagram `66` the system `C₄(m_3, m_4, m_5, m_6)` has a
solution (the first step of the proof of Theorem 7.13, `thm:d66`). -/
theorem d66_exists_C4 (hD : G.HasDiagram Diagram.d66) :
    ∃ ξ η : Fin 4 → ℂ, ∃ P : Fin 4 → Fin 4 → ℂ, ∃ c : ℂ, IsC4 (K4.muK m) ξ η P c :=
  ⟨_, _, _, _, (G.d66lead hD).1⟩

end Germ

end

end CC6Full

