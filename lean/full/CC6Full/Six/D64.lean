import CC6Full.Six.K4Aux
import CC6Full.Six.E4

/-!
# Diagram 64: the leading system `E₄` (Lemmas 7.1–7.3)

§7.1 of the paper. At a singular place with diagram `64` (Table 1, `Diagram.d64`): the bodies of
`K = {3, 4, 5, 6}` are pairwise joined by `z`-strokes, none is `z`-circled, the only `w`-stroke is `12`, and `1`,
`2` are the `w`-circled bodies. In Lean body `k` of the paper is `k − 1`: `K = {2, 3, 4, 5}`, the binary is
`{0, 1}`. The masses are positive (`hm : ∀ i, 0 < m i`).

* `Germ.d64type_a`, `Germ.d64type_b`, `Germ.d64type_c`, `Germ.d64type_d`: Lemma 7.1 (`lem:d64type`) (a)–(d), with
  `x = x_{34}` the common type of the pairs of `K`.
* `Germ.d64centre`: Lemma 7.2 (`lem:d64centre`), `a_k = 3x − 2` for `k ∈ K`.
* `Germ.d64lead`: Lemma 7.3 (`lem:d64lead`): with `ξ_k = [z_k]_{3x−2}`, `η_k = [w_k]_{2−x}` (so that
  `η_k − η_l = [w_kl]_{2−x}`) and `P_kl = [p_kl]_{−x}` for `k, l ∈ K` (`K4.xiK`, `K4.etaK`, `K4.PK`, with `K`
  renumbered `0, 1, 2, 3` in increasing order by `K4.emb`), the differences `ξ_k − ξ_l`, `η_k − η_l` and the `P_kl`
  are nonzero and `(ξ, η, P)` solves `E₄(m_K)` (`IsE4`).
* `Germ.d64_exists_E4`: `E₄(m_K)` has a solution; `Germ.d64_forms`: with Lemma 7.6 (`lem:E4`, `lem_E4`), for some
  pattern the forms `ℱ_ε` or `𝒢_σ` at `μ = m_K` have a common zero (the input of Theorem 7.12, `thm:d64`).

The proofs are the paper's, with one simplification in Lemma 7.3: `Φ^η_k = [w_k]_{2−4x}` vanishes because the
coefficients `[w_k]_{2−4x}`, `k ∈ K`, are equal (`ω_kl = 2 − x > 2 − 4x` on `K`) and the subset sum of `K` gives
`Σ_{k∈K} m_k [w_k]_{2−4x} = 0` (its terms `W_kj`, `j = 1, 2`, have exponent `(2 − 4x) + (2 − x/2)`).
-/

namespace CC6Full

open Finset

noncomputable section

namespace Germ

variable {m : Fin 6 → ℝ} (G : Germ 6 m)

/-! ## The diagram -/

theorem d64_zS (k l : Fin 6) : Diagram.d64.zS k l ↔ (k ≠ l ∧ 2 ≤ k.val ∧ 2 ≤ l.val) := by
  revert k l
  unfold Diagram.zS
  decide

theorem d64_wS (k l : Fin 6) : Diagram.d64.wS k l ↔ (k ≠ l ∧ k.val < 2 ∧ l.val < 2) := by
  revert k l
  unfold Diagram.wS
  decide

theorem d64_zC (k : Fin 6) : k ∉ Diagram.d64.zCircles := by
  revert k
  decide

theorem d64_wC (k : Fin 6) : k ∈ Diagram.d64.wCircles ↔ k.val < 2 := by
  revert k
  decide

/-- The diagram `64` read on the germ: `z`-strokes on the pairs of `K`, the `w`-stroke `12`, no `z`-circle, the
`w`-circles `1, 2`. -/
theorem d64_facts (hD : G.HasDiagram Diagram.d64) :
    (∀ k l, G.zStroke k l ↔ (k ≠ l ∧ 2 ≤ k.val ∧ 2 ≤ l.val)) ∧
      (∀ k l, G.wStroke k l ↔ (k ≠ l ∧ k.val < 2 ∧ l.val < 2)) ∧ (∀ k, ¬ G.zCircle k) ∧
        (∀ k, G.wCircle k ↔ k.val < 2) :=
  ⟨fun k l => (hD.1 k l).trans (d64_zS k l), fun k l => (hD.2.1 k l).trans (d64_wS k l),
    fun k h => d64_zC k ((hD.2.2.1 k).mp h), fun k => (hD.2.2.2 k).trans (d64_wC k)⟩

theorem fin6_binary {j l : Fin 6} (hj : j.val < 2) (hl : l.val < 2) (hlj : l ≠ j) :
    (j = 0 ∧ l = 1) ∨ (j = 1 ∧ l = 0) := by
  revert j l
  decide

theorem exists_coe_of_lt {u : WithTop ℚ} {c : ℚ} (h : u < c) : ∃ A : ℚ, u = A ∧ A < c := by
  induction u using WithTop.recTopCoe with
  | top => exact absurd h not_top_lt
  | coe A => exact ⟨A, rfl, WithTop.coe_lt_coe.mp h⟩

/-! ## Lemma 7.1 -/

/-- **Lemma 7.1 (a)** (`lem:d64type`): on the six pairs of `K`, `ζ = 3x − 2` and `ω = 2 − x` with one common
`x = x_{34}`, and `0 < x < 1`. -/
theorem d64type_a (hD : G.HasDiagram Diagram.d64) :
    0 < G.x 2 3 ∧ G.x 2 3 < 1 ∧ K4.PairsK G (G.x 2 3) := by
  obtain ⟨hz, hw, hzc, -⟩ := G.d64_facts hD
  exact K4.pairsK G (fun k l hk hl hkl => (hz k l).mpr ⟨hkl, hk, hl⟩)
    (fun h => absurd ((hw 2 3).mp h).2.1 (by decide)) (hzc 2) (hzc 3)

/-- **Lemma 7.1 (b)** (`lem:d64type`): `ζ_12 = 2`, `ω_12 = −2`, `x_12 = 0` ((F1) with the colours exchanged). -/
theorem d64type_b (hm : ∀ i, 0 < m i) (hD : G.HasDiagram Diagram.d64) :
    G.zeta 0 1 = 2 ∧ G.omega 0 1 = -2 ∧ G.x 0 1 = 0 := by
  obtain ⟨hz, hw, -, hwc⟩ := G.d64_facts hD
  have hs : G.wStroke 0 1 := (hw 0 1).mpr ⟨by decide, by decide, by decide⟩
  obtain ⟨hω, hζ, hx0, -⟩ := G.O3_w hs
  suffices hx : G.x 0 1 = 0 by
    exact ⟨by rw [hζ, hx]; ring, by rw [hω, hx]; ring, hx⟩
  by_contra hx
  have hpos : 0 < G.x 0 1 := lt_of_le_of_ne hx0 (Ne.symm hx)
  have he : (G.w 0).coeff (-2) = (G.w 1).coeff (-2) :=
    K4.coeff_w_eq_of_lt G (by decide) (by rw [hω]; linarith)
  have hc := K4.com_w_coeff G (-2)
  rw [K4.sum_fin6] at hc
  have hK : ∑ l : Fin 4, (m (K4.emb l) : ℂ) * (G.w (K4.emb l)).coeff (-2) = 0 :=
    Finset.sum_eq_zero fun l _ => by
      have h2 := K4.two_le_emb l
      rw [K4.coeff_w_neg_two G (fun h => absurd ((hwc _).mp h) (by omega)), mul_zero]
  rw [hK, add_zero, ← he, ← add_mul] at hc
  have hm01 : (m 0 : ℂ) + (m 1 : ℂ) ≠ 0 := by
    have := K4.sum_mass_ne_zero hm (K := {0, 1}) ⟨0, by simp⟩
    rwa [Finset.sum_pair (by decide)] at this
  exact ((G.colW.circle_iff_coeff 0).mp ((hwc 0).mpr (by decide)))
    ((mul_eq_zero.mp hc).resolve_left hm01)

/-- **Lemma 7.1 (c)** (`lem:d64type`): `ω_jk = −2` and `ζ_jk = a_k < 2` for `j ∈ {1, 2}`, `k ∈ K`; on the way,
`a_1, a_2 ≥ 2` (part of (d)). -/
theorem d64type_c (hm : ∀ i, 0 < m i) (hD : G.HasDiagram Diagram.d64) :
    (∀ j : Fin 6, j.val < 2 → ((2 : ℚ) : WithTop ℚ) ≤ (G.z j).orderTop) ∧
      ∀ j k : Fin 6, j.val < 2 → 2 ≤ k.val →
        G.omega j k = -2 ∧ (G.z k).orderTop = (G.zeta j k : WithTop ℚ) ∧ G.zeta j k < 2 := by
  obtain ⟨-, hw, -, hwc⟩ := G.d64_facts hD
  obtain ⟨-, hω01, -⟩ := G.d64type_b hm hD
  have hne : ∀ j k : Fin 6, j.val < 2 → 2 ≤ k.val → j ≠ k := fun j k hj hk h => by
    rw [h] at hj
    omega
  have hωjk : ∀ j k : Fin 6, j.val < 2 → 2 ≤ k.val → G.omega j k = -2 := fun j k hj hk =>
    G.O6_w ((hwc j).mpr hj) (fun h => by have := (hwc k).mp h; omega)
  have hζjk : ∀ j k : Fin 6, j.val < 2 → 2 ≤ k.val → G.zeta j k < 2 := by
    intro j k hj hk
    rcases (G.O1_le (hne j k hj hk)).1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := ((hw j k).mp (G.O6_z' h).2).2.2
      omega
  have ha : ∀ j : Fin 6, j.val < 2 → ((2 : ℚ) : WithTop ℚ) ≤ (G.z j).orderTop := by
    intro j hj
    apply K4.two_le_orderTop_z
    intro l hlj
    by_cases hl : l.val < 2
    · rcases fin6_binary hj hl hlj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hω01
      · rw [G.omega_comm]
        exact hω01
    · exact hωjk j l hj (by omega)
  exact ⟨ha, fun j k hj hk => ⟨hωjk j k hj hk,
    (K4.orderTop_z_eq_zeta G (hne j k hj hk) (ha j hj) (hζjk j k hj hk)).1, hζjk j k hj hk⟩⟩

/-- **Lemma 7.1 (d)** (`lem:d64type`): `b_1 = b_2 = −2` (`w`-circles), `a_1, a_2 ≥ 2`, and for `k ∈ K`,
`b_k > −2` and `3x − 2 ≤ a_k < 2`, with equality for at least three `k ∈ K`: of any two bodies of `K`, one has
`a_k = 3x − 2`. -/
theorem d64type_d (hm : ∀ i, 0 < m i) (hD : G.HasDiagram Diagram.d64) :
    (∀ j : Fin 6, j.val < 2 → G.wCircle j ∧ ((2 : ℚ) : WithTop ℚ) ≤ (G.z j).orderTop) ∧
      (∀ k : Fin 6, 2 ≤ k.val → ((-2 : ℚ) : WithTop ℚ) < (G.w k).orderTop ∧
        ((3 * G.x 2 3 - 2 : ℚ) : WithTop ℚ) ≤ (G.z k).orderTop ∧
          (G.z k).orderTop < ((2 : ℚ) : WithTop ℚ)) ∧
      ∀ k l : Fin 6, 2 ≤ k.val → 2 ≤ l.val → k ≠ l →
        (G.z k).orderTop = ((3 * G.x 2 3 - 2 : ℚ) : WithTop ℚ) ∨
          (G.z l).orderTop = ((3 * G.x 2 3 - 2 : ℚ) : WithTop ℚ) := by
  obtain ⟨-, -, -, hwc⟩ := G.d64_facts hD
  obtain ⟨hx0, hx1, hK⟩ := G.d64type_a hD
  obtain ⟨ha, hc⟩ := G.d64type_c hm hD
  have hlt2 : ∀ k : Fin 6, 2 ≤ k.val → (G.z k).orderTop < ((2 : ℚ) : WithTop ℚ) := by
    intro k hk
    obtain ⟨-, h1, h2⟩ := hc 0 k (by decide) hk
    rw [h1]
    exact_mod_cast h2
  have hge : ∀ k : Fin 6, 2 ≤ k.val → ((3 * G.x 2 3 - 2 : ℚ) : WithTop ℚ) ≤ (G.z k).orderTop := by
    intro k hk
    by_contra hcon
    obtain ⟨A, hA, hAlt⟩ := exists_coe_of_lt (not_le.mp hcon)
    refine K4.com_contra G hm K4.Kset ((K4.mem_Kset k).mpr hk) hA (fun l hl hlk => ?_) (fun j hj => ?_)
    · rw [(hK k l hk ((K4.mem_Kset l).mp hl) (Ne.symm hlk)).1]
      exact hAlt
    · have hjv : j.val < 2 := by
        rw [K4.mem_Kset] at hj
        omega
      exact lt_of_lt_of_le (by exact_mod_cast (show A < 2 by linarith)) (ha j hjv)
  refine ⟨fun j hj => ⟨(hwc j).mpr hj, ha j hj⟩, fun k hk => ⟨?_, hge k hk, hlt2 k hk⟩, ?_⟩
  · exact lt_of_le_of_ne (G.low_w.1 k) (fun h => by have := (hwc k).mp h.symm; omega)
  · intro k l hk hl hkl
    by_contra hcon
    push Not at hcon
    have h1 := G.min_le_zeta hkl
    rw [(hK k l hk hl hkl).1] at h1
    rcases min_le_iff.mp h1 with h2 | h2
    · exact hcon.1 (le_antisymm h2 (hge k hk))
    · exact hcon.2 (le_antisymm h2 (hge l hl))

/-! ## Lemma 7.2 -/

/-- **Lemma 7.2** (`lem:d64centre`): `a_k = 3x − 2` for all `k ∈ K`. If `a_{k₀} > 3x − 2`, the torque of the
binary `{1, 2}` has the least exponent `1 − a_{k₀}/2`, attained only by the pairs `(j, k₀)` by (F4), with the
coefficient `m_{k₀}(m_1 [p_{1k₀}] + m_2 [p_{2k₀}])`, which is not zero by Lemma 6.3 (`lem:binary`) with the colours
exchanged: `m_1³ + m_2³ ≠ 0`. -/
theorem d64centre (hm : ∀ i, 0 < m i) (hD : G.HasDiagram Diagram.d64) :
    ∀ k : Fin 6, 2 ≤ k.val → (G.z k).orderTop = ((3 * G.x 2 3 - 2 : ℚ) : WithTop ℚ) := by
  obtain ⟨-, -, -, hwc⟩ := G.d64_facts hD
  obtain ⟨hj, hk, hone⟩ := G.d64type_d hm hD
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨k0, hk0, hne⟩ := hcon
  obtain ⟨hbk0, hge0, hlt0⟩ := hk k0 hk0
  obtain ⟨A, hA, hA2⟩ := exists_coe_of_lt hlt0
  have hAgt : 3 * G.x 2 3 - 2 < A := by
    rw [hA] at hge0 hne
    exact lt_of_le_of_ne (WithTop.coe_le_coe.mp hge0) (fun h => hne (by rw [h]))
  have hoth : ∀ k : Fin 6, 2 ≤ k.val → k ≠ k0 →
      (G.z k).orderTop = ((3 * G.x 2 3 - 2 : ℚ) : WithTop ℚ) := by
    intro k hk' hkk0
    rcases hone k k0 hk' hk0 hkk0 with h | h
    · exact h
    · exact absurd h hne
  have hjb : ∀ j : Fin 6, j.val < 2 → (G.w j).orderTop = ((-2 : ℚ) : WithTop ℚ) := fun j h => (hj j h).1
  have haj : ∀ j : Fin 6, j.val < 2 → ∀ a : ℚ, a < 2 → (a : WithTop ℚ) < (G.z j).orderTop :=
    fun j h a ha => lt_of_lt_of_le (by exact_mod_cast ha) (hj j h).2
  have hsum : ∀ j : Fin 6, j.val < 2 → ∀ l : Fin 6, 2 ≤ l.val → ∀ a : ℚ, a < 2 →
      ((a + -2 : ℚ) : WithTop ℚ) < (G.z j).orderTop + (G.w l).orderTop := by
    intro j hj' l hl a ha
    refine lt_trans ?_ (K4.coe_add_lt (hj j hj').2 (hk l hl).1)
    exact_mod_cast (show a + -2 < 2 + -2 by linarith)
  have hne' : ∀ j l : Fin 6, j.val < 2 → 2 ≤ l.val → l ≠ j := fun j l hj' hl h => by
    rw [h] at hl
    omega
  -- the coefficient of the torque terms at `1 − a_{k₀}/2`
  have hterm : ∀ j : Fin 6, j.val < 2 → ∀ l : Fin 6, 2 ≤ l.val →
      (G.p j l ^ 3 * (G.z j * G.w l - G.z l * G.w j)).coeff (-((A + -2) / 2)) =
        if l = k0 then (G.p k0 j).coeff (-((A + -2) / 2)) else 0 := by
    intro j hj' l hl
    have hswap : G.p j l ^ 3 * (G.z j * G.w l - G.z l * G.w j) =
        -(G.p l j ^ 3 * (G.z l * G.w j - G.z j * G.w l)) := by
      rw [G.p_symm j l]
      ring
    rw [hswap, Ser.coeff_neg]
    by_cases hlk : l = k0
    · subst hlk
      rw [ite_eq_left rfl]
      obtain ⟨-, hc⟩ := K4.f4_term G (hne' j l hj' hl) hA (hjb j hj') (haj j hj' A hA2) (hk l hl).1
        (hsum j hj' l hl A hA2)
      rw [hc, neg_neg]
    · rw [ite_eq_right hlk]
      have hx2 : 3 * G.x 2 3 - 2 < 2 := lt_trans hAgt hA2
      obtain ⟨hlo, -⟩ := K4.f4_term G (hne' j l hj' hl) (hoth l hl hlk) (hjb j hj') (haj j hj' _ hx2)
        (hk l hl).1 (hsum j hj' l hl _ hx2)
      have hlt : ((-((A + -2) / 2) : ℚ) : WithTop ℚ) < ((-((3 * G.x 2 3 - 2 + -2) / 2) : ℚ) : WithTop ℚ) := by
        exact_mod_cast (show -((A + -2) / 2) < -((3 * G.x 2 3 - 2 + -2) / 2) by linarith)
      rw [Ser.coeff_eq_zero_of_lt (lt_of_lt_of_le hlt hlo), neg_zero]
  have hT := congrArg (fun f : Ser => f.coeff (-((A + -2) / 2))) (G.torque {0, 1})
  simp only [HahnSeries.coeff_zero, Ser.coeff_sum] at hT
  rw [← K4.compl_Kset] at hT
  have hinner : ∀ j ∈ ({0, 1} : Finset (Fin 6)), ∑ l ∈ K4.Kset,
      (cS (m j) * cS (m l) * (G.p j l ^ 3 * (G.z j * G.w l - G.z l * G.w j))).coeff (-((A + -2) / 2)) =
        (m j : ℂ) * (m k0 : ℂ) * (G.p k0 j).coeff (-((A + -2) / 2)) := by
    intro j hj'
    have hjv : j.val < 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
      rcases hj' with rfl | rfl <;> decide
    rw [Finset.sum_eq_single_of_mem k0 ((K4.mem_Kset k0).mpr hk0)]
    · rw [← cS_mul, Ser.coeff_cS_mul, hterm j hjv k0 hk0, ite_eq_left rfl]
    · intro l hl hlk
      rw [← cS_mul, Ser.coeff_cS_mul, hterm j hjv l ((K4.mem_Kset l).mp hl), ite_eq_right hlk, mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_pair (by decide : (0 : Fin 6) ≠ 1)] at hT
  -- (F4) for the pairs `(k₀, j)`
  have hF : ∀ j : Fin 6, j.val < 2 →
      (G.p k0 j).coeff (-((A + -2) / 2)) ^ 2 * (G.z k0).coeff A * (G.w j).coeff (-2) = -1 :=
    fun j hj' => (K4.f4 G (hne' j k0 hj' hk0) hA (hjb j hj') (haj j hj' A hA2) hbk0).2.2.2
  have h1 := hF 0 (by decide)
  have h2 := hF 1 (by decide)
  -- the centre of mass at exponent `−2`: `m_1 ŵ_1 + m_2 ŵ_2 = 0`
  have h3 : (m 0 : ℂ) * (G.w 0).coeff (-2) + (m 1 : ℂ) * (G.w 1).coeff (-2) = 0 := by
    have hc := K4.com_w_coeff G (-2)
    rw [K4.sum_fin6] at hc
    have hK : ∑ l : Fin 4, (m (K4.emb l) : ℂ) * (G.w (K4.emb l)).coeff (-2) = 0 :=
      Finset.sum_eq_zero fun l _ => by
        have h2 := K4.two_le_emb l
        rw [K4.coeff_w_neg_two G (fun h => absurd ((hwc _).mp h) (by omega)), mul_zero]
    rwa [hK, add_zero] at hc
  have h4 : (m 0 : ℂ) * (G.p k0 0).coeff (-((A + -2) / 2)) +
      (m 1 : ℂ) * (G.p k0 1).coeff (-((A + -2) / 2)) = 0 := by
    have h5 : (m k0 : ℂ) * ((m 0 : ℂ) * (G.p k0 0).coeff (-((A + -2) / 2)) +
        (m 1 : ℂ) * (G.p k0 1).coeff (-((A + -2) / 2))) = 0 := by
      linear_combination hT
    exact (mul_eq_zero.mp h5).resolve_left (K4.mass_ne_zero hm k0)
  -- Lemma 6.3 with the colours exchanged
  have key : ((m 0 : ℂ) ^ 3 + (m 1 : ℂ) ^ 3) * ((G.p k0 1).coeff (-((A + -2) / 2)) ^ 2 *
      (G.z k0).coeff A * (G.w 0).coeff (-2)) = 0 := by
    linear_combination ((m 1 : ℂ) * (G.z k0).coeff A * (G.w 0).coeff (-2) *
        ((m 1 : ℂ) * (G.p k0 1).coeff (-((A + -2) / 2)) - (m 0 : ℂ) * (G.p k0 0).coeff (-((A + -2) / 2)))) * h4 +
      ((m 1 : ℂ) * (m 0 : ℂ) ^ 2) * h1 +
      ((m 0 : ℂ) ^ 2 * (G.p k0 1).coeff (-((A + -2) / 2)) ^ 2 * (G.z k0).coeff A) * h3 -
      ((m 0 : ℂ) ^ 2 * (m 1 : ℂ)) * h2
  have hm3 : (m 0 : ℂ) ^ 3 + (m 1 : ℂ) ^ 3 ≠ 0 := by
    have e : (m 0 : ℂ) ^ 3 + (m 1 : ℂ) ^ 3 = ((m 0 ^ 3 + m 1 ^ 3 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.ofReal_ne_zero]
    have := hm 0
    have := hm 1
    positivity
  have hZ : (G.z k0).coeff A ≠ 0 := fun h0 => by rw [h0] at h1; simp at h1
  have hW : (G.w 0).coeff (-2) ≠ 0 := fun h0 => by rw [h0] at h1; simp at h1
  have hP : (G.p k0 1).coeff (-((A + -2) / 2)) ≠ 0 := fun h0 => by rw [h0] at h2; simp at h2
  exact mul_ne_zero hm3 (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hP) hZ) hW) key

/-! ## Lemma 7.3 -/

/-- For `k ∈ K` and `j ∈ {1, 2}`: `ζ_kj = 3x − 2` and `ω_kj = −2` (Lemmas 7.1 (c) and 7.2). -/
theorem d64_cross (hm : ∀ i, 0 < m i) (hD : G.HasDiagram Diagram.d64) :
    ∀ k j : Fin 6, 2 ≤ k.val → j.val < 2 → G.zeta k j = 3 * G.x 2 3 - 2 ∧ G.omega k j = -2 := by
  intro k j hk hj
  obtain ⟨-, hc⟩ := G.d64type_c hm hD
  obtain ⟨hω, hζ, -⟩ := hc j k hj hk
  rw [G.d64centre hm hD k hk] at hζ
  rw [G.zeta_comm, G.omega_comm]
  exact ⟨(WithTop.coe_inj.mp hζ).symm, hω⟩

/-- **Lemma 7.3** (`lem:d64lead`). Put `ξ_k = [z_k]_{3x−2}`, `η_k = [w_k]_{2−x}` (so that
`η_kl = [w_kl]_{2−x} = η_k − η_l`) and `P_kl = [p_kl]_{−x}` for `k, l ∈ K`, with `K = {3, 4, 5, 6}` renumbered
`0, 1, 2, 3` in increasing order and `x = x_{34}`. Then `(ξ, η, P)` solves `E₄(m_K)`, and all `ξ_k − ξ_l`,
`η_k − η_l`, `P_kl` (`k ≠ l`) are nonzero. -/
theorem d64lead (hm : ∀ i, 0 < m i) (hD : G.HasDiagram Diagram.d64) :
    IsE4 (K4.muK m) (K4.xiK G (G.x 2 3)) (K4.etaK G (G.x 2 3)) (K4.PK G (G.x 2 3)) ∧
      ∀ k l : Fin 4, k ≠ l → K4.xiK G (G.x 2 3) k - K4.xiK G (G.x 2 3) l ≠ 0 ∧
        K4.etaK G (G.x 2 3) k - K4.etaK G (G.x 2 3) l ≠ 0 ∧ K4.PK G (G.x 2 3) k l ≠ 0 := by
  obtain ⟨hz, -, hzc, -⟩ := G.d64_facts hD
  obtain ⟨hx0, hx1, hK⟩ := G.d64type_a hD
  have hcr := G.d64_cross hm hD
  have hns : ∀ k j : Fin 6, 2 ≤ k.val → j.val < 2 → ¬ G.zStroke k j := fun k j hk hj h => by
    have := ((hz k j).mp h).2.2
    omega
  have hne : ∀ k j : Fin 6, 2 ≤ k.val → j.val < 2 → k ≠ j := fun k j hk hj h => by
    rw [h] at hk
    omega
  have hW : ∀ k j : Fin 6, 2 ≤ k.val → j.val < 2 → (termZ G.p G.w k j).coeff (2 - 4 * G.x 2 3) = 0 :=
    fun k j hk hj => K4.coeff_W_cross G (hne k j hk hj) (hcr k j hk hj).1 (hcr k j hk hj).2 (by linarith)
  -- `[w_k]_{2−4x} = 0` for `k ∈ K`, by the subset sum of `K`
  have hw0 : ∀ k : Fin 6, 2 ≤ k.val → (G.w k).coeff (2 - 4 * G.x 2 3) = 0 := by
    have hss := G.colW.coeff_subset_sum K4.Kset (2 - 4 * G.x 2 3)
    have hR : ∑ j ∈ K4.Kset, ∑ i ∈ univ \ K4.Kset,
        (m j : ℂ) * ((m i : ℂ) * (termZ G.p G.w j i).coeff (2 - 4 * G.x 2 3)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun i hi => ?_
      have hjv := (K4.mem_Kset j).mp hj
      have hiv : i.val < 2 := by
        have := (Finset.mem_sdiff.mp hi).2
        rw [K4.mem_Kset] at this
        omega
      rw [hW j i hjv hiv, mul_zero, mul_zero]
    have hsame : ∀ j : Fin 6, 2 ≤ j.val → (G.w j).coeff (2 - 4 * G.x 2 3) = (G.w 2).coeff (2 - 4 * G.x 2 3) := by
      intro j hj
      by_cases hj2 : j = 2
      · rw [hj2]
      · exact K4.coeff_w_eq_of_lt G hj2 (by rw [(hK j 2 hj (by decide) hj2).2.1]; linarith)
    have hL : ∑ j ∈ K4.Kset, (m j : ℂ) * (G.w j).coeff (2 - 4 * G.x 2 3) =
        (∑ j ∈ K4.Kset, (m j : ℂ)) * (G.w 2).coeff (2 - 4 * G.x 2 3) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j hj => by rw [hsame j ((K4.mem_Kset j).mp hj)]
    rw [hL, hR] at hss
    have h2 : (G.w 2).coeff (2 - 4 * G.x 2 3) = 0 :=
      (mul_eq_zero.mp hss).resolve_left (K4.sum_mass_ne_zero hm ⟨2, by decide⟩)
    intro k hk
    rw [hsame k hk, h2]
  have hE : IsE4 (K4.muK m) (K4.xiK G (G.x 2 3)) (K4.etaK G (G.x 2 3)) (K4.PK G (G.x 2 3)) := by
    refine ⟨K4.PK_symm G _, fun k => K4.lead_force_xi G hK hns (fun k _ => hzc k) k, fun k => ?_,
      K4.lead_dist G hK⟩
    rw [K4.lead_force_eta G hK k (hW _ 0 (K4.two_le_emb k) (by decide))
      (hW _ 1 (K4.two_le_emb k) (by decide)), hw0 _ (K4.two_le_emb k)]
  refine ⟨hE, fun k l hkl => ?_⟩
  have d := hE.2.2.2 k l hkl
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩ <;> simp [h0] at d

/-- By Lemmas 7.2 and 7.3, at a singular place with diagram `64` the system `E₄(m_K)` has a solution (the first
step of the proof of Theorem 7.12, `thm:d64`). -/
theorem d64_exists_E4 (hm : ∀ i, 0 < m i) (hD : G.HasDiagram Diagram.d64) :
    ∃ ξ η : Fin 4 → ℂ, ∃ P : Fin 4 → Fin 4 → ℂ, IsE4 (K4.muK m) ξ η P :=
  ⟨_, _, _, (G.d64lead hm hD).1⟩

/-- At a singular place with diagram `64`, for some symmetric pattern `ε` of cube roots of unity the forms `ℱ_ε` at
`μ = m_K` have a common zero `q ≠ 0`, or for some antisymmetric sign pattern `σ` the forms `𝒢_σ` have a common zero
`(ξ₂, ξ₃, ξ₄) ≠ 0` (Lemmas 7.2, 7.3 and 7.6; the first step of the proof of Theorem 7.12, `thm:d64`). -/
theorem d64_forms (hm : ∀ i, 0 < m i) (hD : G.HasDiagram Diagram.d64) :
    (∃ e : Fin 6 → ZMod 3, ∃ q : Fin 4 → ℂ, q ≠ 0 ∧ ∀ i, MvPolynomial.eval q (E4.Fforms (K4.muK m) e i) = 0) ∨
      ∃ s : Fin 6 → Bool, ∃ y : Fin 3 → ℂ, y ≠ 0 ∧ ∀ k, MvPolynomial.eval y (E4.Gforms (K4.muK m) s k) = 0 := by
  refine lem_E4 ?_ (G.d64lead hm hD).1
  simp only [K4.muK, mul_ne_zero_iff]
  exact ⟨⟨⟨K4.mass_ne_zero hm _, K4.mass_ne_zero hm _⟩, K4.mass_ne_zero hm _⟩, K4.mass_ne_zero hm _⟩

end Germ

end

end CC6Full

