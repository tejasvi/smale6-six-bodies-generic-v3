import Lean6.Special.D88.Boxes.Final
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Fintype.Fin

/-!
# Sec. 6.7, last paragraph: the counts on the solutions of KC

**`sec_6_7_counts`**: with the polydiscs and zeros `z_k` of Lemma 6.19(d), the T-test over the bodies 1, 2, 3 fails at
exactly 1092 zeros and holds at exactly 3696; at exactly 36 zeros the smallest of the 32 sums has relative margin
below `10⁻⁴` (`SmallAt`: for every choice of the square roots some sum has `‖Σ‖ < 10⁻⁴ (1 + ρ²)^{1/2} Σ_l |β_l|`), and
at these `|Y₄| > 5·10³` and `|Y_l| < 3·10⁻⁵ |Y₄|` for `l = 1, 2, 3`.
-/

namespace Lean6.Special.D88.Boxes

open Lean6.Special.Ball Lean6.Special.Kraw Metric Complex

/-- At the point `v`, for every choice of the square roots, some sum has relative margin below `10⁻⁴`. -/
def SmallAt (v : Fin 12 → ℂ) : Prop :=
  ∀ w : Fin 3 → ℂ, (∀ l, w l ^ 2 = KC.X v l.castSucc) → ∃ ε s : Fin 3 → ℤ, (∀ l, IsSign (ε l)) ∧
    (∀ l, IsSign (s l)) ∧ ‖kcSum w ε s‖ < (1 / 10000 : ℝ) * Real.sqrt (1 + rho ^ 2) * betaNorm w

/-- The classes of a box string. -/
def isFail (s : String) : Bool := match kcClass s with | some (false, _) => true | _ => false
def isPass (s : String) : Bool := match kcClass s with | some (true, _) => true | _ => false
def isSmall (s : String) : Bool := match kcClass s with | some (_, true) => true | _ => false

theorem kcCounts_spec : ∀ {l : List String} {f p m : ℕ}, kcCounts l = some (f, p, m) →
    (∀ s ∈ l, ∃ t sm, kcClass s = some (t, sm)) ∧ f = l.countP isFail ∧ p = l.countP isPass ∧ m = l.countP isSmall
  | [], f, p, m, h => by
    simp only [kcCounts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | s :: rest, f, p, m, h => by
    unfold kcCounts at h
    split at h
    · rename_i t sm f' p' m' hc hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hall, hf, hp, hm⟩ := kcCounts_spec hr
      refine ⟨fun x hx => ?_, ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨t, sm, hc⟩
        · exact hall x hx
      · rw [List.countP_cons, ← hf]
        cases t <;> simp [isFail, hc]
      · rw [List.countP_cons, ← hp]
        cases t <;> simp [isPass, hc]
      · rw [List.countP_cons, ← hm]
        cases sm <;> simp [isSmall, hc]
    · exact absurd h (by simp)

theorem card_filter_countP {α : Type} (p : α → Bool) :
    ∀ l : List α, (Finset.univ.filter fun k : Fin l.length => p l[k] = true).card = l.countP p
  | [] => by simp
  | a :: l => by
    have e : (Finset.univ.filter fun k : Fin (a :: l).length => p (a :: l)[k] = true).card =
        (Finset.univ.filter fun k : Fin (l.length + 1) => p ((a :: l)[k.1]'(by simp; omega)) = true).card := rfl
    rw [e, Fin.card_filter_univ_succ, List.countP_cons]
    have ih := card_filter_countP p l
    simp only [Fin.getElem_fin] at ih
    simp only [Function.comp_def, Fin.val_succ, List.getElem_cons_succ, Fin.val_zero, List.getElem_cons_zero]
    rw [ih]
    split_ifs with ha <;> simp [ha]

theorem card_filter_countP' {α : Type} {l : List α} {N : ℕ} (hN : l.length = N) (p : α → Bool) :
    (Finset.univ.filter fun k : Fin N => p (l[k.1]'(by rw [hN]; exact k.2)) = true).card = l.countP p := by
  subst hN
  exact card_filter_countP p l

theorem kcClass_spec {s : String} {t sm : Bool} (h : kcClass s = some (t, sm)) :
    ∃ b, parseBox s = some b ∧ t123Decide b = some t ∧ smallDecide b = some sm ∧ (sm = true → yBounds b = true) := by
  unfold kcClass at h
  split at h
  · rename_i b hb
    split at h
    · rename_i t' sm' ht hs
      split_ifs at h with hy
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨b, hb, ht, hs, fun hsm => ?_⟩
      subst hsm
      simpa using hy
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem pass_fail_exclusive (t : Fin 3 → ℝ) : ¬ (T123Pass t ∧ T123Fail t) := by
  rintro ⟨⟨k, hk⟩, hf⟩
  exact absurd (hf k) (not_lt.mpr hk.le)

theorem exists_sqrts (v : Fin 12 → ℂ) : ∃ w : Fin 3 → ℂ, ∀ l, w l ^ 2 = KC.X v l.castSucc :=
  ⟨fun l => KC.X v l.castSucc ^ ((2 : ℂ)⁻¹), fun l => by
    simpa using Complex.cpow_nat_inv_pow (KC.X v l.castSucc) (n := 2) two_ne_zero⟩

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
  obtain ⟨bs, hlen, hget, hpw⟩ := allSep_boxes KC.allSep_ok
  have hN : KC.allData.length = 4788 := KC.allData_length
  have hok0 := KC.all_ok
  unfold kcChunkOK at hok0
  have hok : ∀ s ∈ KC.allData, kcBoxOK s = true := List.all_eq_true.mp hok0
  have hbs : bs.length = 4788 := by rw [hlen, hN]
  obtain ⟨hcls, hf, hp, hm⟩ := kcCounts_spec KC.counts_ok
  -- per box: the string, its box, its classification
  have hbox : ∀ (k : Fin 4788), kcBoxOK (KC.allData[k.1]'(by rw [hN]; exact k.2)) = true ∧
      parseBox (KC.allData[k.1]'(by rw [hN]; exact k.2)) = some (bs[k.1]'(by rw [hbs]; exact k.2)) := fun k =>
    ⟨hok _ (List.getElem_mem _), hget k.1 (by rw [hN]; exact k.2) (by rw [hbs]; exact k.2)⟩
  -- the zeros
  have hz : ∀ k : Fin 4788, ∃ z ∈ closedBall ((bs[k.1]'(by rw [hbs]; exact k.2)).center 12)
      (bs[k.1]'(by rw [hbs]; exact k.2)).radius, KC.KC12 z = 0 ∧
      ∀ w ∈ closedBall ((bs[k.1]'(by rw [hbs]; exact k.2)).center 12) (bs[k.1]'(by rw [hbs]; exact k.2)).radius,
        KC.KC12 w = 0 → w = z := by
    intro k
    obtain ⟨h1, h2⟩ := hbox k
    obtain ⟨b, hb, -, -, ⟨z, hzm, hz0, hzu, -⟩, -⟩ := kc_box_sound h1
    rw [h2, Option.some.injEq] at hb
    subst hb
    exact ⟨z, hzm, hz0, hzu⟩
  choose z hzm hz0 hzu using hz
  -- `ρ₀` is checked by every box
  have hrho : rho0OK = true := by
    obtain ⟨h1, h2⟩ := hbox ⟨0, by norm_num⟩
    unfold kcBoxOK at h1
    rw [h2] at h1
    simp only [Bool.and_eq_true] at h1
    have := h1.2
    unfold kcExtra at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1.2
  -- the classification of each zero
  have hclass : ∀ k : Fin 4788,
      (T123Fail (fun l => 1 / Real.sqrt ‖KC.X (z k) l.castSucc‖) ↔
        isFail (KC.allData[k.1]'(by rw [hN]; exact k.2)) = true) ∧
      (T123Pass (fun l => 1 / Real.sqrt ‖KC.X (z k) l.castSucc‖) ↔
        isPass (KC.allData[k.1]'(by rw [hN]; exact k.2)) = true) ∧
      (SmallAt (z k) ↔ isSmall (KC.allData[k.1]'(by rw [hN]; exact k.2)) = true) ∧
      (SmallAt (z k) → yBounds (bs[k.1]'(by rw [hbs]; exact k.2)) = true) := by
    intro k
    obtain ⟨t, sm, hc⟩ := hcls _ (List.getElem_mem (by rw [hN]; exact k.2))
    obtain ⟨b, hb, ht, hs, hy⟩ := kcClass_spec hc
    rw [(hbox k).2, Option.some.injEq] at hb
    subst hb
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
    · simp only [isFail, hc]
      cases t
      · simpa using hT.2 rfl
      · simp only [Bool.false_eq_true, iff_false]
        exact fun hF => pass_fail_exclusive _ ⟨hT.1 rfl, hF⟩
    · simp only [isPass, hc]
      cases t
      · simp only [Bool.false_eq_true, iff_false]
        exact fun hP => pass_fail_exclusive _ ⟨hP, hT.2 rfl⟩
      · simpa using hT.1 rfl
    · rw [hsmall_iff]
      simp only [isSmall, hc]
      cases sm <;> simp
  refine ⟨fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).center 12, fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).radius,
    z, fun k l hkl => ?_, fun k => ⟨hzm k, hz0 k, hzu k⟩, ?_, ?_, ?_, fun k hS => ?_⟩
  · refine disjoint_of_pairwise hpw (n := 12) (fun i hi => ?_) (by rw [hbs]; exact k.2) (by rw [hbs]; exact l.2)
      (fun h => hkl (Fin.ext h))
    have hi' : i < 4788 := by rw [← hbs]; exact hi
    obtain ⟨h1, h2⟩ := hbox ⟨i, hi'⟩
    exact kc_len h1 h2
  · have h1 := card_filter_countP' hN isFail
    have h2 := Finset.filter_congr (s := (Finset.univ : Finset (Fin 4788))) (fun k _ => (hclass k).1)
    exact (congrArg Finset.card h2).trans (h1.trans hf.symm)
  · have h1 := card_filter_countP' hN isPass
    have h2 := Finset.filter_congr (s := (Finset.univ : Finset (Fin 4788))) (fun k _ => (hclass k).2.1)
    exact (congrArg Finset.card h2).trans (h1.trans hp.symm)
  · have h1 := card_filter_countP' hN isSmall
    have h2 := Finset.filter_congr (s := (Finset.univ : Finset (Fin 4788))) (fun k _ => (hclass k).2.2.1)
    exact (congrArg Finset.card h2).trans (h1.trans hm.symm)
  · exact yBounds_sound ((hclass k).2.2.2 hS) (hzm k)

end Lean6.Special.D88.Boxes
