import L6CheckKSpec.N4.All
import L6CheckKSpec.KC.All
import L6CheckKSpec.KC.Counts
import L6SoundKSpec.Sweep
import L6SoundKSpec.Counts
import Lean6.Special.D88.Boxes.Counts

/-!
# Lemma 6.19(c), (d) with the standard axioms only

The statements of `Lean6.Special.D88.Boxes.lemma_6_19_c`, `lemma_6_19_d` and `sec_6_7_counts`, word for word (the
`example`s at the end check that the types coincide), proved from the kernel checks of `L6CheckKSpec` (every box of
`N4.allBoxes`, `KC.allBoxes` passes the tests of `n4BoxOK`, `kcBoxOK` after parsing; the boxes are pairwise separated
by the sweep; the classes of the KC boxes are counted by `kcCountsB`) and lean6_special's Box-level soundness
(`n4_box_soundB`, `kc_box_soundB`, `n4_len_of_test`, `kc_len_of_test`, `disjoint_of_pairwise`, `t123_sound`,
`small_sound`, `yBounds_sound`). No `native_decide` is used.
-/

namespace Lean6.Special.D88.BoxesK

open Lean6.Special.D88.Boxes Lean6.Special.Ball Lean6.Special.Kraw Metric Complex L6KSpec

/-- **Lemma 6.19(c).** -/
theorem lemma_6_19_c :
    ∃ (c : Fin 20316 → Fin 11 → ℂ) (r : Fin 20316 → ℝ),
      (∀ k, 0 < r k ∧ r k < 6 / 10 ^ 47) ∧
      Pairwise (fun k l => Disjoint (closedBall (c k) (r k)) (closedBall (c l) (r l))) ∧
      ∀ k, (∃ z ∈ closedBall (c k) (r k), N4.S11 z = 0 ∧ (∀ w ∈ closedBall (c k) (r k), N4.S11 w = 0 → w = z) ∧
          ∃ J : Matrix (Fin 11) (Fin 11) ℂ, IsUnit J.det ∧
            HasFDerivAt N4.S11 (Matrix.toLin' J).toContinuousLinearMap z) ∧
        ∀ w ∈ closedBall (c k) (r k), N4.X w 2 - N4.X w 3 ≠ 0 ∧ TTest4 (fun l => 1 / Real.sqrt ‖N4.X w l‖) ∧
          ∀ l, N4.X w l ≠ 0 := by
  set bs := L6CheckKSpec.N4.allBoxes
  have hbs : bs.length = 20316 := L6CheckKSpec.N4.length_eq
  have hok : ∀ b ∈ bs, (n4RadiusOK b && krawBox s11T b && n4Extra b) = true :=
    List.all_eq_true.mp L6CheckKSpec.N4.all_ok
  have hcs : ∀ b ∈ bs, b.cs ≠ [] := fun b hb h => by
    have := n4_len_of_test (hok b hb)
    rw [h] at this
    exact absurd this (by decide)
  have hpw : bs.Pairwise fun a b => sepBoxes a b = true := sweepOK_pairwise hcs L6CheckKSpec.N4.sweep
  refine ⟨fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).center 11, fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).radius,
    fun k => ?_, fun k l hkl => ?_, fun k => ?_⟩
  · obtain ⟨hr0, hr1, -⟩ := n4_box_soundB (hok _ (List.getElem_mem _))
    exact ⟨hr0, hr1⟩
  · exact disjoint_of_pairwise hpw (n := 11) (fun i hi => n4_len_of_test (hok _ (List.getElem_mem _)))
      (by rw [hbs]; exact k.2) (by rw [hbs]; exact l.2) (fun h => hkl (Fin.ext h))
  · obtain ⟨-, -, hz, hx⟩ := n4_box_soundB (hok _ (List.getElem_mem _))
    exact ⟨hz, hx⟩

/-- **Lemma 6.19(d).** -/
theorem lemma_6_19_d :
    ∃ (c : Fin 4788 → Fin 12 → ℂ) (r : Fin 4788 → ℝ),
      (∀ k, 0 < r k ∧ r k < 5 / 10 ^ 54) ∧
      Pairwise (fun k l => Disjoint (closedBall (c k) (r k)) (closedBall (c l) (r l))) ∧
      ∀ k, (∃ z ∈ closedBall (c k) (r k), KC.KC12 z = 0 ∧ (∀ w ∈ closedBall (c k) (r k), KC.KC12 w = 0 → w = z) ∧
          ∃ J : Matrix (Fin 12) (Fin 12) ℂ, IsUnit J.det ∧
            HasFDerivAt KC.KC12 (Matrix.toLin' J).toContinuousLinearMap z) ∧
        ∀ v ∈ closedBall (c k) (r k), KC.X v 2 ≠ 0 ∧
          (∀ w : Fin 3 → ℂ, (∀ l, w l ^ 2 = KC.X v l.castSucc) → ∀ ε s : Fin 3 → ℤ, (∀ l, IsSign (ε l)) →
            (∀ l, IsSign (s l)) → (147 / 100000000 : ℝ) * Real.sqrt (1 + rho ^ 2) * betaNorm w ≤ ‖kcSum w ε s‖) ∧
          ∀ l : Fin 3, KC.X v l.castSucc ≠ 0 := by
  set bs := L6CheckKSpec.KC.allBoxes
  have hbs : bs.length = 4788 := L6CheckKSpec.KC.length_eq
  have hok : ∀ b ∈ bs, (kcRadiusOK b && krawBox kc12T b && kcExtra b) = true :=
    List.all_eq_true.mp L6CheckKSpec.KC.all_ok
  have hcs : ∀ b ∈ bs, b.cs ≠ [] := fun b hb h => by
    have := kc_len_of_test (hok b hb)
    rw [h] at this
    exact absurd this (by decide)
  have hpw : bs.Pairwise fun a b => sepBoxes a b = true := sweepOK_pairwise hcs L6CheckKSpec.KC.sweep
  refine ⟨fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).center 12, fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).radius,
    fun k => ?_, fun k l hkl => ?_, fun k => ?_⟩
  · obtain ⟨hr0, hr1, -⟩ := kc_box_soundB (hok _ (List.getElem_mem _))
    exact ⟨hr0, hr1⟩
  · exact disjoint_of_pairwise hpw (n := 12) (fun i hi => kc_len_of_test (hok _ (List.getElem_mem _)))
      (by rw [hbs]; exact k.2) (by rw [hbs]; exact l.2) (fun h => hkl (Fin.ext h))
  · obtain ⟨-, -, hz, hx⟩ := kc_box_soundB (hok _ (List.getElem_mem _))
    exact ⟨hz, hx⟩

open Classical in
/-- **Sec. 6.7, last paragraph.** -/
theorem sec_6_7_counts :
    ∃ (c : Fin 4788 → Fin 12 → ℂ) (r : Fin 4788 → ℝ) (z : Fin 4788 → Fin 12 → ℂ),
      Pairwise (fun k l => Disjoint (closedBall (c k) (r k)) (closedBall (c l) (r l))) ∧
      (∀ k, z k ∈ closedBall (c k) (r k) ∧ KC.KC12 (z k) = 0 ∧
        ∀ w ∈ closedBall (c k) (r k), KC.KC12 w = 0 → w = z k) ∧
      (Finset.univ.filter fun k => T123Fail fun l => 1 / Real.sqrt ‖KC.X (z k) l.castSucc‖).card = 1092 ∧
      (Finset.univ.filter fun k => T123Pass fun l => 1 / Real.sqrt ‖KC.X (z k) l.castSucc‖).card = 3696 ∧
      (Finset.univ.filter fun k => SmallAt (z k)).card = 36 ∧
      ∀ k, SmallAt (z k) → 5000 < ‖KC.Y (z k) 3‖ ∧
        ∀ l : Fin 3, ‖KC.Y (z k) l.castSucc‖ < 3 / 100000 * ‖KC.Y (z k) 3‖ := by
  set bs := L6CheckKSpec.KC.allBoxes
  have hbs : bs.length = 4788 := L6CheckKSpec.KC.length_eq
  have hok : ∀ b ∈ bs, (kcRadiusOK b && krawBox kc12T b && kcExtra b) = true :=
    List.all_eq_true.mp L6CheckKSpec.KC.all_ok
  have hcs : ∀ b ∈ bs, b.cs ≠ [] := fun b hb h => by
    have := kc_len_of_test (hok b hb)
    rw [h] at this
    exact absurd this (by decide)
  have hpw : bs.Pairwise fun a b => sepBoxes a b = true := sweepOK_pairwise hcs L6CheckKSpec.KC.sweep
  obtain ⟨hcls, hf, hp, hm⟩ := kcCountsB_spec L6CheckKSpec.KC.counts_ok
  have hbk : ∀ k : Fin 4788, (bs[k.1]'(by rw [hbs]; exact k.2)) ∈ bs := fun k => List.getElem_mem _
  -- the zeros
  have hz : ∀ k : Fin 4788, ∃ z ∈ closedBall ((bs[k.1]'(by rw [hbs]; exact k.2)).center 12)
      (bs[k.1]'(by rw [hbs]; exact k.2)).radius, KC.KC12 z = 0 ∧
      ∀ w ∈ closedBall ((bs[k.1]'(by rw [hbs]; exact k.2)).center 12) (bs[k.1]'(by rw [hbs]; exact k.2)).radius,
        KC.KC12 w = 0 → w = z := by
    intro k
    obtain ⟨-, -, ⟨z, hzm, hz0, hzu, -⟩, -⟩ := kc_box_soundB (hok _ (hbk k))
    exact ⟨z, hzm, hz0, hzu⟩
  choose z hzm hz0 hzu using hz
  -- `ρ₀` is checked by every box
  have hrho : rho0OK = true := by
    have h1 := hok _ (hbk ⟨0, by norm_num⟩)
    simp only [Bool.and_eq_true] at h1
    have := h1.2
    unfold kcExtra at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1.2
  -- the classification of each zero
  have hclass : ∀ k : Fin 4788,
      (T123Fail (fun l => 1 / Real.sqrt ‖KC.X (z k) l.castSucc‖) ↔
        isFailB (bs[k.1]'(by rw [hbs]; exact k.2)) = true) ∧
      (T123Pass (fun l => 1 / Real.sqrt ‖KC.X (z k) l.castSucc‖) ↔
        isPassB (bs[k.1]'(by rw [hbs]; exact k.2)) = true) ∧
      (SmallAt (z k) ↔ isSmallB (bs[k.1]'(by rw [hbs]; exact k.2)) = true) ∧
      (SmallAt (z k) → yBounds (bs[k.1]'(by rw [hbs]; exact k.2)) = true) := by
    intro k
    obtain ⟨t, sm, hc⟩ := hcls _ (hbk k)
    obtain ⟨ht, hs, hy⟩ := kcClassB_spec hc
    have hT := t123_sound ht (hzm k)
    obtain ⟨w, hw⟩ := exists_sqrts (z k)
    have hsmall_iff : SmallAt (z k) ↔ sm = true := by
      constructor
      · intro hS
        by_contra hsm
        rw [Bool.not_eq_true] at hsm
        obtain ⟨ε, s, hε, hs', hlt⟩ := hS w hw
        have := (small_sound hs hrho (hzm k) hw).2 hsm ε s hε hs'
        linarith
      · intro hsm w' hw'
        exact (small_sound hs hrho (hzm k) hw').1 hsm
    refine ⟨?_, ?_, ?_, fun hS => hy (hsmall_iff.mp hS)⟩
    · simp only [isFailB, hc]
      cases t
      · simpa using hT.2 rfl
      · simp only [Bool.false_eq_true, iff_false]
        exact fun hF => pass_fail_exclusive _ ⟨hT.1 rfl, hF⟩
    · simp only [isPassB, hc]
      cases t
      · simp only [Bool.false_eq_true, iff_false]
        exact fun hP => pass_fail_exclusive _ ⟨hP, hT.2 rfl⟩
      · simpa using hT.1 rfl
    · rw [hsmall_iff]
      simp only [isSmallB, hc]
      cases sm <;> simp
  refine ⟨fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).center 12, fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).radius,
    z, fun k l hkl => ?_, fun k => ⟨hzm k, hz0 k, hzu k⟩, ?_, ?_, ?_, fun k hS => ?_⟩
  · exact disjoint_of_pairwise hpw (n := 12) (fun i hi => kc_len_of_test (hok _ (List.getElem_mem _)))
      (by rw [hbs]; exact k.2) (by rw [hbs]; exact l.2) (fun h => hkl (Fin.ext h))
  · have h1 := card_filter_countP' hbs isFailB
    have h2 := Finset.filter_congr (s := (Finset.univ : Finset (Fin 4788))) (fun k _ => (hclass k).1)
    exact (congrArg Finset.card h2).trans (h1.trans hf.symm)
  · have h1 := card_filter_countP' hbs isPassB
    have h2 := Finset.filter_congr (s := (Finset.univ : Finset (Fin 4788))) (fun k _ => (hclass k).2.1)
    exact (congrArg Finset.card h2).trans (h1.trans hp.symm)
  · have h1 := card_filter_countP' hbs isSmallB
    have h2 := Finset.filter_congr (s := (Finset.univ : Finset (Fin 4788))) (fun k _ => (hclass k).2.2.1)
    exact (congrArg Finset.card h2).trans (h1.trans hm.symm)
  · exact yBounds_sound ((hclass k).2.2.2 hS) (hzm k)

/-! The statements are those of lean6_special. -/

example : type_of% Lean6.Special.D88.Boxes.lemma_6_19_c := lemma_6_19_c
example : type_of% Lean6.Special.D88.Boxes.lemma_6_19_d := lemma_6_19_d
example : type_of% Lean6.Special.D88.Boxes.sec_6_7_counts := sec_6_7_counts

end Lean6.Special.D88.BoxesK
