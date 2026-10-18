import L6KSpec.Boxes

/-!
# The sweep proves pairwise separation

`sweepOK_pairwise`: if `sweepOK R l` holds and every box has a centre, the boxes of `l` are pairwise separated
(`sepBoxes`), as version 1's `pairwiseSep` states.
-/

namespace L6KSpec

open Lean6.Special.D88.Boxes

/-- A gap between the keys larger than the sum of the radii separates two boxes (in the first coordinate). -/
theorem sep_of_gap {b b' : Box} (hb : b.cs ≠ []) (hb' : b'.cs ≠ [])
    (h : boxKey b' - boxKey b > ((b.rho + b'.rho : Nat) : Int)) : sepBoxes b b' = true := by
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hb
  obtain ⟨c', cs', hc'⟩ := List.exists_cons_of_ne_nil hb'
  have k1 : boxKey b = c.1 := by simp [boxKey, Box.c, hc]
  have k2 : boxKey b' = c'.1 := by simp [boxKey, Box.c, hc']
  rw [k1, k2] at h
  unfold sepBoxes
  rw [hc, hc', List.zip_cons_cons, List.any_cons]
  have : b.rho + b'.rho < (c.1 - c'.1).natAbs := by omega
  simp [this]

/-- What `sweepFrom` gives, for boxes sorted by key with radii at most `R`. -/
theorem sweepFrom_spec {R : Nat} {b : Box} (hb : b.cs ≠ []) :
    ∀ (l : List Box), sweepFrom R b l = true → (∀ b' ∈ l, b'.cs ≠ [] ∧ b'.rho ≤ R) →
      l.Pairwise (fun x y => boxKey x ≤ boxKey y) → ∀ b' ∈ l, sepBoxes b b' = true
  | [], _, _, _ => by simp
  | b' :: rest, h, hl, hs => by
    intro x hx
    unfold sweepFrom at h
    rcases Bool.or_eq_true_iff.mp h with hg | h2
    · have hg' := of_decide_eq_true hg
      have hkx : boxKey b' ≤ boxKey x := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Int.le_refl _
        · exact List.rel_of_pairwise_cons hs hx
      obtain ⟨hcx, hrx⟩ := hl x hx
      refine sep_of_gap hb hcx ?_
      push_cast at hg' ⊢
      omega
    · rw [Bool.and_eq_true] at h2
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h2.1
      · exact sweepFrom_spec hb rest h2.2 (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hs.of_cons x hx

theorem sweepOK_cons {R : Nat} {b : Box} {rest : List Box} (h : sweepOK R (b :: rest) = true) :
    b.rho ≤ R ∧ (∀ c ∈ rest.head?, boxKey b ≤ boxKey c) ∧ sweepFrom R b rest = true ∧ sweepOK R rest = true := by
  unfold sweepOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun c hc => ?_, h3, h4⟩
  cases rest with
  | nil => simp at hc
  | cons d rest =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
    subst hc
    simpa using h2

theorem sweepOK_rho {R : Nat} : ∀ {l : List Box}, sweepOK R l = true → ∀ b ∈ l, b.rho ≤ R
  | [], _ => by simp
  | b :: rest, h => by
    obtain ⟨h1, -, -, h4⟩ := sweepOK_cons h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · exact sweepOK_rho h4 x hx

theorem sweepOK_sorted {R : Nat} : ∀ {l : List Box}, sweepOK R l = true →
    l.Pairwise (fun x y => boxKey x ≤ boxKey y)
  | [], _ => List.Pairwise.nil
  | b :: rest, h => by
    obtain ⟨-, h2, -, h4⟩ := sweepOK_cons h
    have ih := sweepOK_sorted h4
    refine List.Pairwise.cons (fun y hy => ?_) ih
    cases rest with
    | nil => simp at hy
    | cons c rest' =>
      have hbc : boxKey b ≤ boxKey c := h2 c (by simp)
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hbc
      · exact Int.le_trans hbc (List.rel_of_pairwise_cons ih hy)

/-- **The sweep gives pairwise separation.** -/
theorem sweepOK_pairwise {R : Nat} : ∀ {l : List Box}, (∀ b ∈ l, b.cs ≠ []) → sweepOK R l = true →
    l.Pairwise (fun x y => sepBoxes x y = true)
  | [], _, _ => List.Pairwise.nil
  | b :: rest, hcs, h => by
    obtain ⟨-, -, h3, h4⟩ := sweepOK_cons h
    have hcs' : ∀ y ∈ rest, y.cs ≠ [] := fun y hy => hcs y (List.mem_cons_of_mem _ hy)
    refine List.Pairwise.cons ?_ (sweepOK_pairwise hcs' h4)
    exact sweepFrom_spec (hcs b List.mem_cons_self) rest h3
      (fun y hy => ⟨hcs' y hy, sweepOK_rho h4 y hy⟩) (sweepOK_sorted h4)

end L6KSpec
