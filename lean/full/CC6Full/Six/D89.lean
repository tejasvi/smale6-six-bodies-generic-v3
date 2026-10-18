import CC6Full.Germ.Diagram
import CC6Full.Six.Common

/-!
# Diagram 89 (Theorem 6.5, `thm:d89`)

Paper §6.2 (in §6, `sec:ak50`), Theorem 6.5 (`thm:d89`): no singular place has diagram `89` (Table 1,
`Diagram.d89`), stated and proved for germs as `Six.d89_excluded`. Diagram `89` has the `z`-strokes `45, 46, 56`
with the `z`-circles `5, 6`, the `w`-strokes `23, 24, 34` with the `w`-circles `2, 3`, and the free body `1` (no
stroke, no circle). In Lean body `k` of the paper is `k − 1`: the `z`-strokes are the pairs of `{3, 4, 5}`, the
`z`-circles are `4, 5`, the `w`-strokes are the pairs of `{1, 2, 3}`, the `w`-circles are `1, 2`, and the free body
is `0`.

The proof is the paper's, in three steps (the comments in the proof use the paper's numbering of the bodies):

* *the exponents*: (F1)–(F3) of Lemma 6.1 (`Six.F1_z`, …) and (O6) give `b_5, b_6, b_4 ≥ 2`, `a_2, a_3, a_4 ≥ 2`,
  and `a_1, b_1 ∈ (−2, 2)`, since otherwise `12` would be a `w`-stroke or `15` a `z`-stroke;
* *`a_1 + b_1 = 0`*: all pairs other than `14` have `x ≤ 0`, so if `a_1 + b_1 > 0` the term of `14` is the only
  term of negative exponent in `U = E` (`Germ.pot`); if `a_1 + b_1 < 0`, the term of `1` is the only one of negative
  exponent in `Σ_k m_k z_k w_k = E` (`Germ.virial`);
* *the torque of `S = {5, 6}`* (`Germ.torque`) at the exponent `1 + a_1/2 = 1 − b_1/2`: the pairs `(j, 1)` give
  `−m_1 (m_5 p̂_51 + m_6 p̂_61)` by (F4) (`Six.F4_z_term`), which is not zero by Lemma 6.3 (`Six.binary_z`); the pairs
  `(j, 2)`, `(j, 3)` have exponent at least `2`; and the pairs `(j, 4)` contribute `m_4 (w_4 B_z − z_4 B_w)` by
  Lemma 6.2 with `o = 4` (`Six.rewrite_sum`, `Six.rewrite_B`), where `e(B_z) ≥ a_1` and `B_w = w_4 − A_w` has
  exponent at least `2`, so that this contribution has exponent at least `2 + a_1`.
-/

namespace CC6Full

open Finset

noncomputable section

namespace Six

/-! ## Series -/

/-- A lower bound for the exponents of the terms is a lower bound for the exponent of the sum. -/
private theorem d89_le_sum {ι : Type*} (s : Finset ι) (f : ι → Ser) {e : WithTop ℚ}
    (h : ∀ i ∈ s, e ≤ (f i).orderTop) : e ≤ (∑ i ∈ s, f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi)))
      HahnSeries.min_orderTop_le_orderTop_add

/-- A constant factor does not lower the exponent. -/
private theorem d89_le_cS_mul (a : ℂ) (f : Ser) : f.orderTop ≤ (cS a * f).orderTop := by
  by_cases ha : a = 0
  · rw [ha, cS_zero, zero_mul, HahnSeries.orderTop_zero]
    exact le_top
  · rw [Ser.orderTop_cS_mul ha]

/-- `a + b ≤ e(fg)` for `a ≤ e(f)` and `b ≤ e(g)`. -/
private theorem d89_le_mul {f g : Ser} {a b : ℚ} (hf : (a : WithTop ℚ) ≤ f.orderTop)
    (hg : (b : WithTop ℚ) ≤ g.orderTop) : ((a + b : ℚ) : WithTop ℚ) ≤ (f * g).orderTop := by
  rw [HahnSeries.orderTop_mul, WithTop.coe_add]
  exact add_le_add hf hg

/-- A lower bound for the exponents of `f` and `g` is a lower bound for the exponent of `f − g`. -/
private theorem d89_le_sub {f g : Ser} {e : WithTop ℚ} (hf : e ≤ f.orderTop) (hg : e ≤ g.orderTop) :
    e ≤ (f - g).orderTop :=
  le_trans (le_min hf hg) HahnSeries.min_orderTop_le_orderTop_sub

/-- `e(f³) = 3 e(f)`. -/
private theorem d89_orderTop_pow_three {f : Ser} {e : ℚ} (h : f.orderTop = e) :
    (f ^ 3).orderTop = ((3 * e : ℚ) : WithTop ℚ) := by
  rw [pow_three', HahnSeries.orderTop_mul, HahnSeries.orderTop_mul, h, ← WithTop.coe_add,
    ← WithTop.coe_add]
  congr 1
  ring

/-- An exponent below a rational number is a rational number. -/
private theorem d89_coe_of_lt {u : WithTop ℚ} {c : ℚ} (h : u < c) : ∃ A : ℚ, u = A ∧ A < c := by
  induction u using WithTop.recTopCoe with
  | top => exact absurd h not_top_lt
  | coe A => exact ⟨A, rfl, WithTop.coe_lt_coe.mp h⟩

/-- Positive masses are nonzero. -/
private theorem d89_mass_ne_zero {n : ℕ} {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (i : Fin n) :
    (m i : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (hm i).ne'

/-! ## Germs -/

/-- `ζ_kl = a_k` if `a_k < a_l`. -/
private theorem d89_zeta_eq {n : ℕ} {m : Fin n → ℝ} (G : Germ n m) {k l : Fin n} {a : ℚ}
    (ha : (G.z k).orderTop = a) (hl : (a : WithTop ℚ) < (G.z l).orderTop) : G.zeta k l = a := by
  have hz : (G.z k).orderTop < (G.z l).orderTop := by
    rw [ha]
    exact hl
  have hkl : k ≠ l := by
    rintro rfl
    exact lt_irrefl _ hz
  have h1 := G.zeta_eq_min hkl hz.ne
  rw [min_eq_left hz.le, ha] at h1
  exact_mod_cast h1

/-- `ω_kl = b_k` if `b_k < b_l`. -/
private theorem d89_omega_eq {n : ℕ} {m : Fin n → ℝ} (G : Germ n m) {k l : Fin n} {b : ℚ}
    (hb : (G.w k).orderTop = b) (hl : (b : WithTop ℚ) < (G.w l).orderTop) : G.omega k l = b := by
  have hw : (G.w k).orderTop < (G.w l).orderTop := by
    rw [hb]
    exact hl
  have hkl : k ≠ l := by
    rintro rfl
    exact lt_irrefl _ hw
  have h1 := G.omega_eq_min hkl hw.ne
  rw [min_eq_left hw.le, hb] at h1
  exact_mod_cast h1

/-- In `U = E`, written as `Σ_{k ≠ l} m_k m_l p_kl = 2E` (`Germ.pot`): if `x_ab > 0` and `x_kl < x_ab` for every
other pair, the terms of `ab` and `ba` are the only ones of exponent `−x_ab < 0`, and their coefficient
`2 m_a m_b p̂_ab` does not vanish, while that of the constant `2E` does. -/
private theorem d89_pot {n : ℕ} {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (G : Germ n m) {a b : Fin n}
    (hab : a ≠ b) (hpos : 0 < G.x a b)
    (hlt : ∀ k l, k ≠ l → ¬ ((k = a ∧ l = b) ∨ (k = b ∧ l = a)) → G.x k l < G.x a b) : False := by
  have hF : ∀ k l, k ≠ l → ¬ ((k = a ∧ l = b) ∨ (k = b ∧ l = a)) →
      ((m k : ℂ) * (m l : ℂ)) * (G.p k l).coeff (-G.x a b) = 0 := by
    intro k l hkl h'
    have h1 : ((-G.x a b : ℚ) : WithTop ℚ) < (G.p k l).orderTop := by
      rw [G.orderTop_p hkl]
      exact WithTop.coe_lt_coe.mpr (by linarith [hlt k l hkl h'])
    rw [Ser.coeff_eq_zero_of_lt h1, mul_zero]
  have hcoef : ∑ k, ∑ l ∈ univ.erase k, ((m k : ℂ) * (m l : ℂ)) * (G.p k l).coeff (-G.x a b) = 0 := by
    have h0 := congrArg (fun f : Ser => f.coeff (-G.x a b)) G.pot
    simp only [HahnSeries.coeff_sum, Colour.coeff_cS_mul] at h0
    rw [h0, Colour.coeff_cS_of_ne _ (neg_ne_zero.mpr hpos.ne')]
  have hA : ∑ l ∈ univ.erase a, ((m a : ℂ) * (m l : ℂ)) * (G.p a l).coeff (-G.x a b) =
      ((m a : ℂ) * (m b : ℂ)) * (G.p a b).coeff (-G.x a b) := by
    refine Finset.sum_eq_single b (fun l hl hlb => hF a l (Finset.ne_of_mem_erase hl).symm ?_)
      (fun h => absurd (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩) h)
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hlb h
    · exact hab h
  have hB : ∑ l ∈ univ.erase b, ((m b : ℂ) * (m l : ℂ)) * (G.p b l).coeff (-G.x a b) =
      ((m b : ℂ) * (m a : ℂ)) * (G.p b a).coeff (-G.x a b) := by
    refine Finset.sum_eq_single a (fun l hl hla => hF b l (Finset.ne_of_mem_erase hl).symm ?_)
      (fun h => absurd (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩) h)
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hab.symm h
    · exact hla h
  have hO : ∀ c ∈ (univ : Finset (Fin n)), c ≠ a ∧ c ≠ b →
      ∑ l ∈ univ.erase c, ((m c : ℂ) * (m l : ℂ)) * (G.p c l).coeff (-G.x a b) = 0 := by
    intro c _ hc
    refine Finset.sum_eq_zero fun l hl => hF c l (Finset.ne_of_mem_erase hl).symm ?_
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hc.1 h
    · exact hc.2 h
  rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ a) (Finset.mem_univ b) hab hO, hA, hB,
    G.p_symm b a] at hcoef
  have h2 : (2 * ((m a : ℂ) * (m b : ℂ))) * (G.p a b).coeff (-G.x a b) = 0 := by
    linear_combination hcoef
  exact mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero (d89_mass_ne_zero hm a) (d89_mass_ne_zero hm b)))
    (HahnSeries.coeff_orderTop_ne (G.orderTop_p hab)) h2

/-- In the virial identity `Σ_k m_k z_k w_k = E` (`Germ.virial`): if `a_{k₀} + b_{k₀} = e < 0` and
`a_k + b_k ≥ 0` for every other body `k`, the term of `k₀` is the only one of exponent `e`, and its coefficient
`m_{k₀} ẑ_{k₀} ŵ_{k₀}` does not vanish, while that of the constant `E` does. -/
private theorem d89_virial {n : ℕ} {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (G : Germ n m) {k₀ : Fin n}
    {e : ℚ} (he : e < 0) (h0 : (G.z k₀ * G.w k₀).orderTop = e)
    (hk : ∀ k, k ≠ k₀ → (0 : WithTop ℚ) ≤ (G.z k * G.w k).orderTop) : False := by
  have hv := congrArg (fun f : Ser => f.coeff e) G.virial
  simp only [HahnSeries.coeff_sum, Colour.coeff_cS_mul] at hv
  rw [Colour.coeff_cS_of_ne _ he.ne, Finset.sum_eq_single k₀] at hv
  · exact mul_ne_zero (d89_mass_ne_zero hm k₀) (HahnSeries.coeff_orderTop_ne h0) hv
  · intro k _ hkk
    have hlt : (e : WithTop ℚ) < (G.z k * G.w k).orderTop :=
      lt_of_lt_of_le (by exact_mod_cast he) (hk k hkk)
    rw [Ser.coeff_eq_zero_of_lt hlt, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k₀) h

/-! ## The diagram -/

private theorem d89_zS (k l : Fin 6) : Diagram.d89.zS k l ↔ (k ≠ l ∧ 3 ≤ k.val ∧ 3 ≤ l.val) := by
  revert k l
  unfold Diagram.zS
  decide

private theorem d89_wS (k l : Fin 6) :
    Diagram.d89.wS k l ↔ (k ≠ l ∧ 1 ≤ k.val ∧ k.val ≤ 3 ∧ 1 ≤ l.val ∧ l.val ≤ 3) := by
  revert k l
  unfold Diagram.wS
  decide

private theorem d89_zC (k : Fin 6) : k ∈ Diagram.d89.zCircles ↔ 4 ≤ k.val := by
  revert k
  decide

private theorem d89_wC (k : Fin 6) : k ∈ Diagram.d89.wCircles ↔ (1 ≤ k.val ∧ k.val ≤ 2) := by
  revert k
  decide

/-- The diagram `89` read on the germ (Lean numbering): `z`-strokes on the pairs of `{3, 4, 5}`, `w`-strokes on the
pairs of `{1, 2, 3}`, the `z`-circles `4, 5` and the `w`-circles `1, 2`. -/
private theorem d89_facts {m : Fin 6 → ℝ} (G : Germ 6 m) (hD : G.HasDiagram Diagram.d89) :
    (∀ k l, G.zStroke k l ↔ (k ≠ l ∧ 3 ≤ k.val ∧ 3 ≤ l.val)) ∧
      (∀ k l, G.wStroke k l ↔ (k ≠ l ∧ 1 ≤ k.val ∧ k.val ≤ 3 ∧ 1 ≤ l.val ∧ l.val ≤ 3)) ∧
        (∀ k, G.zCircle k ↔ 4 ≤ k.val) ∧ (∀ k, G.wCircle k ↔ (1 ≤ k.val ∧ k.val ≤ 2)) :=
  ⟨fun k l => (hD.1 k l).trans (d89_zS k l), fun k l => (hD.2.1 k l).trans (d89_wS k l),
    fun k => (hD.2.2.1 k).trans (d89_zC k), fun k => (hD.2.2.2 k).trans (d89_wC k)⟩

/-- The term `m_k m_l p_kl³ (z_k w_l − z_l w_k)` of the pair `(k, l)` in a torque. -/
private def tq {m : Fin 6 → ℝ} (G : Germ 6 m) (k l : Fin 6) : Ser :=
  cS (m k) * cS (m l) * (G.p k l ^ 3 * (G.z k * G.w l - G.z l * G.w k))

/-! ## Theorem 6.5 -/

/-- **Theorem 6.5** (`thm:d89`): no germ of a singular place has diagram `89` (Table 1, `Diagram.d89`). In the
paper's numbering, where `A = {4, 5, 6}` carries the `z`-strokes, `W = {2, 3, 4}` the `w`-strokes and `1` is free:
the exponents satisfy `b_4, b_5, b_6 ≥ 2`, `a_2, a_3, a_4 ≥ 2` and `a_1, b_1 ∈ (−2, 2)`; `a_1 + b_1 = 0` since `U` is
constant and by the virial identity; and the coefficient of exponent `1 + a_1/2` in the torque of `{5, 6}` is
`−m_1 (m_5 p̂_51 + m_6 p̂_61) ≠ 0`, the pairs `(j, 4)` being handled by Lemma 6.2 (`rewrite_sum`) and the
nonvanishing by Lemma 6.3 (`binary_z`). -/
theorem d89_excluded {m : Fin 6 → ℝ} (hm : ∀ i, 0 < m i) (G : Germ 6 m) :
    ¬ G.HasDiagram Diagram.d89 := by
  intro hD
  obtain ⟨hzS, hwS, hzC, hwC⟩ := d89_facts G hD
  /- **The exponents.** The clusters `A = {4, 5, 6}` and `W = {2, 3, 4}` are `{3, 4, 5}` and `{1, 2, 3}` in
  Lean, and the free body `1` is `0`. -/
  have memA : ∀ k : Fin 6, k ∈ ({3, 4, 5} : Finset (Fin 6)) ↔ 3 ≤ k.val := by decide
  have memW : ∀ k : Fin 6, k ∈ ({1, 2, 3} : Finset (Fin 6)) ↔ (1 ≤ k.val ∧ k.val ≤ 3) := by decide
  have hzc4 : G.zCircle 4 := (hzC 4).mpr (by decide)
  have hzc5 : G.zCircle 5 := (hzC 5).mpr (by decide)
  have hz0 : ¬ G.zCircle 0 := fun h => absurd ((hzC 0).mp h) (by decide)
  have hw0 : ¬ G.wCircle 0 := fun h => absurd ((hwC 0).mp h) (by decide)
  have hzA : ∀ k ∈ ({3, 4, 5} : Finset (Fin 6)), ∀ l ∈ ({3, 4, 5} : Finset (Fin 6)), k ≠ l →
      G.zStroke k l := fun k hk l hl hkl => (hzS k l).mpr ⟨hkl, (memA k).mp hk, (memA l).mp hl⟩
  have hcA : ∀ k, G.zCircle k → k ∈ ({3, 4, 5} : Finset (Fin 6)) := fun k h =>
    (memA k).mpr (by have := (hzC k).mp h; omega)
  have hwW : ∀ k ∈ ({1, 2, 3} : Finset (Fin 6)), ∀ l ∈ ({1, 2, 3} : Finset (Fin 6)), k ≠ l →
      G.wStroke k l := fun k hk l hl hkl =>
    (hwS k l).mpr ⟨hkl, ((memW k).mp hk).1, ((memW k).mp hk).2, ((memW l).mp hl).1, ((memW l).mp hl).2⟩
  have hcW : ∀ k, G.wCircle k → k ∈ ({1, 2, 3} : Finset (Fin 6)) := fun k h =>
    (memW k).mpr (by have := (hwC k).mp h; omega)
  -- (F1): `ζ = −2`, `ω = 2`, `x = 0` on the pairs of `A`, and `ω = −2`, `ζ = 2`, `x = 0` on the pairs of `W`
  have hA : ∀ k l : Fin 6, 3 ≤ k.val → 3 ≤ l.val → k ≠ l →
      G.zeta k l = -2 ∧ G.omega k l = 2 ∧ G.x k l = 0 := fun k l hk hl hkl =>
    F1_z hm G hzA ⟨4, by decide, hzc4⟩ hcA ((memA k).mpr hk) ((memA l).mpr hl) hkl
  have hW : ∀ k l : Fin 6, 1 ≤ k.val → k.val ≤ 3 → 1 ≤ l.val → l.val ≤ 3 → k ≠ l →
      G.omega k l = -2 ∧ G.zeta k l = 2 ∧ G.x k l = 0 := fun k l hk1 hk3 hl1 hl3 hkl =>
    F1_w hm G hwW ⟨1, by decide, (hwC 1).mpr (by decide)⟩ hcW ((memW k).mpr ⟨hk1, hk3⟩)
      ((memW l).mpr ⟨hl1, hl3⟩) hkl
  -- (F2) and (F3): `b_5, b_6, b_4 ≥ 2` and `a_2, a_3, a_4 ≥ 2`
  have hb45 : ∀ k : Fin 6, 4 ≤ k.val → ((2 : ℚ) : WithTop ℚ) ≤ (G.w k).orderTop := fun k hk =>
    F2_z hm G hzA hcA ((hzC k).mpr hk)
  have ha12 : ∀ k : Fin 6, 1 ≤ k.val → k.val ≤ 2 → ((2 : ℚ) : WithTop ℚ) ≤ (G.z k).orderTop :=
    fun k hk1 hk2 => F2_w hm G hwW hcW ((hwC k).mpr ⟨hk1, hk2⟩)
  have hb3 : ((2 : ℚ) : WithTop ℚ) ≤ (G.w 3).orderTop :=
    le_trans (le_min (hb45 4 (by decide)) le_rfl)
      (F3_w G ((hzS 3 4).mpr ⟨by decide, by decide, by decide⟩)
        (hA 3 4 (by decide) (by decide) (by decide)).2.2)
  have ha3 : ((2 : ℚ) : WithTop ℚ) ≤ (G.z 3).orderTop :=
    le_trans (le_min (ha12 1 (by decide) (by decide)) le_rfl)
      (F3_z G ((hwS 3 1).mpr ⟨by decide, by decide, by decide, by decide, by decide⟩)
        (hW 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)).2.2)
  -- `a_1 < 2`, since otherwise `ζ_12 = 2` and `12` would be a `w`-stroke (O6)
  have ha0lt : (G.z 0).orderTop < ((2 : ℚ) : WithTop ℚ) := by
    by_contra hcon
    have h1 : ((2 : ℚ) : WithTop ℚ) ≤ (G.zeta 0 1 : WithTop ℚ) :=
      le_trans (le_min (not_lt.mp hcon) (ha12 1 (by decide) (by decide)))
        (G.min_le_zeta (by decide : (0 : Fin 6) ≠ 1))
    have h2 : G.zeta 0 1 = 2 :=
      le_antisymm (G.O1_le (by decide : (0 : Fin 6) ≠ 1)).1 (by exact_mod_cast h1)
    exact absurd ((hwS 0 1).mp (G.O6_z' h2).2).2.1 (by decide)
  -- `b_1 < 2`, since otherwise `ω_15 = 2` and `15` would be a `z`-stroke (O6)
  have hb0lt : (G.w 0).orderTop < ((2 : ℚ) : WithTop ℚ) := by
    by_contra hcon
    have h1 : ((2 : ℚ) : WithTop ℚ) ≤ (G.omega 0 4 : WithTop ℚ) :=
      le_trans (le_min (not_lt.mp hcon) (hb45 4 (by decide)))
        (G.min_le_omega (by decide : (0 : Fin 6) ≠ 4))
    have h2 : G.omega 0 4 = 2 :=
      le_antisymm (G.O1_le (by decide : (0 : Fin 6) ≠ 4)).2.1 (by exact_mod_cast h1)
    exact absurd ((hzS 0 4).mp (G.O6_w' h2).2).2.1 (by decide)
  -- `a_1, b_1 > −2`, since `1` is not circled
  have ha0gt : ((-2 : ℚ) : WithTop ℚ) < (G.z 0).orderTop :=
    lt_of_le_of_ne (G.low_z.1 0) (fun h => hz0 h.symm)
  have hb0gt : ((-2 : ℚ) : WithTop ℚ) < (G.w 0).orderTop :=
    lt_of_le_of_ne (G.low_w.1 0) (fun h => hw0 h.symm)
  obtain ⟨a0, ha0, ha0_2⟩ := d89_coe_of_lt ha0lt
  obtain ⟨b0, hb0, hb0_2⟩ := d89_coe_of_lt hb0lt
  have ha0_m2 : -2 < a0 := by
    have h := ha0gt
    rw [ha0] at h
    exact_mod_cast h
  have hb0_m2 : -2 < b0 := by
    have h := hb0gt
    rw [hb0] at h
    exact_mod_cast h
  -- `ζ_14 = a_1` and `ω_14 = b_1`
  have hζ03 : G.zeta 0 3 = a0 :=
    d89_zeta_eq G ha0 (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr ha0_2) ha3)
  have hω03 : G.omega 0 3 = b0 :=
    d89_omega_eq G hb0 (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hb0_2) hb3)
  /- **`a_1 + b_1 = 0`.** Every pair other than `14` has `x ≤ 0`: `ζ = −2` or `ω = −2` by (O6) if exactly one of
  its bodies is circled in some colour, and `x = 0` by (F1) on `56` and `23`. -/
  have hxle : ∀ k l : Fin 6, k ≠ l → ¬ ((k = 0 ∧ l = 3) ∨ (k = 3 ∧ l = 0)) → G.x k l ≤ 0 := by
    have rest : ∀ k l : Fin 6, k ≠ l → ¬ 4 ≤ k.val → ¬ (1 ≤ k.val ∧ k.val ≤ 2) → ¬ 4 ≤ l.val →
        ¬ (1 ≤ l.val ∧ l.val ≤ 2) → (k = 0 ∧ l = 3) ∨ (k = 3 ∧ l = 0) := by decide
    intro k l hkl hn
    have hb := G.O1_le hkl
    rw [G.x_eq hkl]
    by_cases hk : G.zCircle k <;> by_cases hl : G.zCircle l
    · obtain ⟨h1, h2, -⟩ := hA k l (by have := (hzC k).mp hk; omega)
        (by have := (hzC l).mp hl; omega) hkl
      linarith
    · have h1 := G.O6_z hk hl
      linarith [hb.2.1]
    · have h1 := G.O6_z hl hk
      rw [G.zeta_comm l k] at h1
      linarith [hb.2.1]
    · by_cases hk' : G.wCircle k <;> by_cases hl' : G.wCircle l
      · have h3 := (hwC k).mp hk'
        have h4 := (hwC l).mp hl'
        obtain ⟨h1, h2, -⟩ := hW k l h3.1 (by omega) h4.1 (by omega) hkl
        linarith
      · have h1 := G.O6_w hk' hl'
        linarith [hb.1]
      · have h1 := G.O6_w hl' hk'
        rw [G.omega_comm l k] at h1
        linarith [hb.1]
      · exact absurd (rest k l hkl (fun h => hk ((hzC k).mpr h)) (fun h => hk' ((hwC k).mpr h))
          (fun h => hl ((hzC l).mpr h)) (fun h => hl' ((hwC l).mpr h))) hn
  have hsum : a0 + b0 = 0 := by
    have cover : ∀ k : Fin 6, k ≠ 0 → (1 ≤ k.val ∧ k.val ≤ 2) ∨ k = 3 ∨ 4 ≤ k.val := by decide
    rcases lt_trichotomy (a0 + b0) 0 with hlt | heq | hgt
    · -- `a_1 + b_1 < 0`: in `Σ_k m_k z_k w_k = U`, `a_k + b_k ≥ 0` for `k ≠ 1`
      exfalso
      refine d89_virial hm G (k₀ := 0) hlt ?_ ?_
      · rw [HahnSeries.orderTop_mul, ha0, hb0, ← WithTop.coe_add]
      · intro k hk
        have h0 : ∀ {u v : ℚ}, u + v = 0 → (u : WithTop ℚ) ≤ (G.z k).orderTop →
            (v : WithTop ℚ) ≤ (G.w k).orderTop → (0 : WithTop ℚ) ≤ (G.z k * G.w k).orderTop := by
          intro u v huv hu hv
          have h := d89_le_mul hu hv
          rwa [huv, WithTop.coe_zero] at h
        rcases cover k hk with h | rfl | h
        · exact h0 (by norm_num) (ha12 k h.1 h.2) (G.low_w.1 k)
        · exact h0 (by norm_num) ha3 (G.low_w.1 3)
        · exact h0 (by norm_num) (G.low_z.1 k) (hb45 k h)
    · exact heq
    · -- `a_1 + b_1 > 0`: in `U = E` the term of `14` is the only one of negative exponent
      exfalso
      have hpos : 0 < G.x 0 3 := by
        rw [G.x_eq (by decide : (0 : Fin 6) ≠ 3), hζ03, hω03]
        linarith
      exact d89_pot hm G (by decide : (0 : Fin 6) ≠ 3) hpos fun k l hkl hn =>
        lt_of_le_of_lt (hxle k l hkl hn) hpos
  /- **The torque of `S = {5, 6}`** (Lean `{4, 5}`) at the exponent `e₀ = 1 − b_1/2 = 1 + a_1/2`. -/
  have hb0eq : b0 = -a0 := by linarith
  obtain ⟨e₀, he₀⟩ : ∃ e : ℚ, e = -((-2 + b0) / 2) := ⟨_, rfl⟩
  have he₀2 : e₀ < 2 := by
    rw [he₀]
    linarith
  have he₀R : e₀ < 2 + a0 := by
    rw [he₀]
    linarith
  -- the pairs `(j, 1)`, `j = 5, 6`, satisfy (F4): their terms have exponent `e₀` and coefficient
  -- `−m_j m_1 p̂_j1`
  have hF4 : ∀ j : Fin 6, 4 ≤ j.val →
      (tq G j 0).coeff e₀ = -((m j : ℂ) * (m 0 : ℂ) * (G.p j 0).leadingCoeff) := by
    intro j hj
    have hbj := hb45 j hj
    have hbj' : (b0 : WithTop ℚ) < (G.w j).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hb0_2) hbj
    have hs : ((-2 + b0 : ℚ) : WithTop ℚ) < (G.z 0).orderTop + (G.w j).orderTop := by
      rw [ha0]
      calc ((-2 + b0 : ℚ) : WithTop ℚ) < ((a0 + 2 : ℚ) : WithTop ℚ) :=
            WithTop.coe_lt_coe.mpr (by linarith)
        _ = (a0 : WithTop ℚ) + ((2 : ℚ) : WithTop ℚ) := by norm_cast
        _ ≤ (a0 : WithTop ℚ) + (G.w j).orderTop := add_le_add le_rfl hbj
    obtain ⟨h1, h2⟩ := F4_z_term hm G ((hzC j).mpr hj) hb0 ha0gt hbj' hs
    rw [← he₀] at h1
    exact (Ser.coeff_of_orderTop_eq h1).trans h2
  -- the pairs `(j, 2)`, `(j, 3)`: `ζ = ω = −2`, so `e(p_jl) = 2` and the term has exponent at least `2`
  have hfar : ∀ j l : Fin 6, 4 ≤ j.val → 1 ≤ l.val → l.val ≤ 2 → (tq G j l).coeff e₀ = 0 := by
    intro j l hj hl1 hl2
    have hjl : j ≠ l := by
      rintro rfl
      omega
    have hζ : G.zeta j l = -2 :=
      G.O6_z ((hzC j).mpr hj) (fun h => by have := (hzC l).mp h; omega)
    have hω : G.omega j l = -2 := by
      rw [G.omega_comm j l]
      exact G.O6_w ((hwC l).mpr ⟨hl1, hl2⟩) (fun h => by have := (hwC j).mp h; omega)
    have hp : (G.p j l).orderTop = ((2 : ℚ) : WithTop ℚ) := by
      rw [G.orderTop_p hjl, G.x_eq hjl, hζ, hω]
      norm_num
    have h2 : ((2 : ℚ) : WithTop ℚ) ≤ (tq G j l).orderTop := by
      unfold tq
      rw [mul_assoc]
      refine le_trans ?_ (d89_le_cS_mul _ _)
      refine le_trans ?_ (d89_le_cS_mul _ _)
      have h := d89_le_mul (d89_orderTop_pow_three hp).ge
        (d89_le_sub (d89_le_mul (G.low_z.1 j) (G.low_w.1 l)) (d89_le_mul (G.low_z.1 l) (G.low_w.1 j)))
      calc ((2 : ℚ) : WithTop ℚ) = ((3 * 2 + (-2 + -2) : ℚ) : WithTop ℚ) := by norm_num
        _ ≤ _ := h
    exact Ser.coeff_eq_zero_of_lt (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr he₀2) h2)
  -- the pairs `(j, 4)`, by Lemma 6.2 with `o = 4`: `e(B_z) ≥ a_1`, since `e(Z_41) = −(a_1 + 3b_1)/2 = a_1` and
  -- `e(Z_42) = e(Z_43) = 2`; and `e(A_w) ≥ 2`, since `e(W_45) = e(W_46) = 2`
  have h3 : (3 : Fin 6) ∉ ({4, 5} : Finset (Fin 6)) := by decide
  have hBz : (a0 : WithTop ℚ) ≤
      (∑ l ∈ (insert 3 {4, 5} : Finset (Fin 6))ᶜ, cS (m l) * termZ G.p G.z 3 l).orderTop := by
    have cov : ∀ l : Fin 6, l ∈ (insert 3 {4, 5} : Finset (Fin 6))ᶜ →
        l = 0 ∨ (1 ≤ l.val ∧ l.val ≤ 2) := by decide
    refine d89_le_sum _ _ fun l hl => le_trans ?_ (d89_le_cS_mul _ _)
    rcases cov l hl with rfl | ⟨hl1, hl2⟩
    · rw [G.orderTop_termZ_z (by decide : (3 : Fin 6) ≠ 0), G.zeta_comm 3 0, G.omega_comm 3 0, hζ03,
        hω03, hb0eq]
      exact WithTop.coe_le_coe.mpr (by linarith)
    · have h3l : (3 : Fin 6) ≠ l := by
        rintro rfl
        exact absurd hl2 (by decide)
      obtain ⟨hω, hζ, -⟩ := hW 3 l (by decide) (by decide) hl1 (by omega) h3l
      rw [G.orderTop_termZ_z h3l, hζ, hω]
      exact WithTop.coe_le_coe.mpr (by linarith)
  have hAw : ((2 : ℚ) : WithTop ℚ) ≤
      (∑ j ∈ ({4, 5} : Finset (Fin 6)), cS (m j) * termZ G.p G.w 3 j).orderTop := by
    have cov : ∀ j : Fin 6, j ∈ ({4, 5} : Finset (Fin 6)) → 4 ≤ j.val := by decide
    refine d89_le_sum _ _ fun j hj => le_trans ?_ (d89_le_cS_mul _ _)
    have hj4 := cov j hj
    have h3j : (3 : Fin 6) ≠ j := by
      rintro rfl
      exact absurd hj4 (by decide)
    obtain ⟨hζ, hω, -⟩ := hA 3 j (by decide) (by omega) h3j
    rw [G.orderTop_termZ_w h3j, hζ, hω]
    exact WithTop.coe_le_coe.mpr (by norm_num)
  -- so the contribution `m_4 (w_4 B_z − z_4 (w_4 − A_w))` has exponent at least `2 + a_1 > e₀`
  have hR : (cS (m 3) * (G.w 3 * (∑ l ∈ (insert 3 {4, 5} : Finset (Fin 6))ᶜ, cS (m l) * termZ G.p G.z 3 l) -
      G.z 3 * (G.w 3 - ∑ j ∈ ({4, 5} : Finset (Fin 6)), cS (m j) * termZ G.p G.w 3 j))).coeff e₀ = 0 := by
    refine Ser.coeff_eq_zero_of_lt (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr he₀R) ?_)
    refine le_trans ?_ (d89_le_cS_mul _ _)
    refine d89_le_sub (d89_le_mul hb3 hBz) (le_trans ?_ (d89_le_mul ha3 (d89_le_sub hb3 hAw)))
    exact WithTop.coe_le_coe.mpr (by linarith)
  -- the torque `T_S = 0`, with the pairs `(j, 4)` rewritten by Lemma 6.2
  have hT : tq G 4 0 + tq G 5 0 + (tq G 4 1 + tq G 4 2 + (tq G 5 1 + tq G 5 2)) +
      cS (m 3) * (G.w 3 * (∑ l ∈ (insert 3 {4, 5} : Finset (Fin 6))ᶜ, cS (m l) * termZ G.p G.z 3 l) -
        G.z 3 * (G.w 3 - ∑ j ∈ ({4, 5} : Finset (Fin 6)), cS (m j) * termZ G.p G.w 3 j)) = 0 := by
    have e4 : ∀ g : Fin 6 → Ser, ∑ l ∈ ({0, 1, 2, 3} : Finset (Fin 6)), g l = g 0 + g 1 + g 2 + g 3 := by
      intro g
      rw [Finset.sum_insert (show (0 : Fin 6) ∉ ({1, 2, 3} : Finset (Fin 6)) by decide),
        Finset.sum_insert (show (1 : Fin 6) ∉ ({2, 3} : Finset (Fin 6)) by decide),
        Finset.sum_pair (show (2 : Fin 6) ≠ 3 by decide)]
      ring
    have h45 : (4 : Fin 6) ≠ 5 := by decide
    have h : ∑ k ∈ ({4, 5} : Finset (Fin 6)), ∑ l ∈ ({4, 5} : Finset (Fin 6))ᶜ, tq G k l = 0 :=
      G.torque {4, 5}
    rw [show ({4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2, 3} by decide, Finset.sum_pair h45, e4, e4] at h
    have h1' : ∑ j ∈ ({4, 5} : Finset (Fin 6)), cS (m j) * cS (m 3) *
        (G.p j 3 ^ 3 * (G.z j * G.w 3 - G.z 3 * G.w j)) = tq G 4 3 + tq G 5 3 :=
      Finset.sum_pair h45
    obtain ⟨h1, h2⟩ := rewrite_sum G {4, 5} h3
    rw [← (rewrite_B G {4, 5} h3).2] at h2
    linear_combination h + h1' - h1 - h2
  -- the coefficient of `τ^{e₀}` in `T_S` is `−m_1 (m_5 p̂_51 + m_6 p̂_61)`, which is not zero by Lemma 6.3
  have c40 := hF4 4 (by decide)
  have c50 := hF4 5 (by decide)
  have c41 := hfar 4 1 (by decide) (by decide) (by decide)
  have c42 := hfar 4 2 (by decide) (by decide) (by decide)
  have c51 := hfar 5 1 (by decide) (by decide) (by decide)
  have c52 := hfar 5 2 (by decide) (by decide) (by decide)
  have hcT := congrArg (fun f : Ser => f.coeff e₀) hT
  simp only [Ser.coeff_add, HahnSeries.coeff_zero, c40, c50, c41, c42, c51, c52, hR] at hcT
  have honly : ∀ j, G.zCircle j → j = 4 ∨ j = 5 := by
    have key : ∀ j : Fin 6, 4 ≤ j.val → j = 4 ∨ j = 5 := by decide
    exact fun j h => key j ((hzC j).mp h)
  have hbk : (G.w 0).orderTop < min (G.w 4).orderTop (G.w 5).orderTop := by
    rw [hb0]
    exact lt_min (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hb0_2) (hb45 4 (by decide)))
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hb0_2) (hb45 5 (by decide)))
  have hbin := binary_z hm G (i := 4) (i' := 5) (k := 0) (by decide) hzc4 hzc5 honly ha0gt hbk
  have h5 : (m 0 : ℂ) * ((m 4 : ℂ) * (G.p 4 0).leadingCoeff + (m 5 : ℂ) * (G.p 5 0).leadingCoeff) = 0 := by
    linear_combination -hcT
  exact hbin ((mul_eq_zero.mp h5).resolve_left (d89_mass_ne_zero hm 0))

end Six

end

end CC6Full
