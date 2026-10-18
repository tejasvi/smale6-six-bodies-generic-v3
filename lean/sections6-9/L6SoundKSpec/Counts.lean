import L6KSpec.Counts
import Lean6.Special.D88.Boxes.Counts

/-!
# The counts of the KC boxes, from data

`kcCountsB_append`: the counts of a concatenation are the sums of the counts. `kcCountsB_spec`, `kcClassB_spec`: the
counts are the numbers of failing, passing and small boxes, and a classified box has the decisions behind its class
(as `kcCounts_spec`, `kcClass_spec` of lean6_special, without the parsing).
-/

namespace L6KSpec

open Lean6.Special.D88.Boxes

-- the classification is never unfolded by the elaborator here (it would start evaluating the closed parts of the
-- tests, such as the disc of `X₁`); the kernel checks of `L6CheckKSpec` evaluate it
attribute [local irreducible] kcClassB

/-- The classes of a box. -/
noncomputable def isFailB (b : Box) : Bool := match kcClassB b with | some (false, _) => true | _ => false
noncomputable def isPassB (b : Box) : Bool := match kcClassB b with | some (true, _) => true | _ => false
noncomputable def isSmallB (b : Box) : Bool := match kcClassB b with | some (_, true) => true | _ => false

theorem kcCountsB_append : ∀ (l l' : List Box), kcCountsB (l ++ l') = addCounts (kcCountsB l) (kcCountsB l')
  | [], l' => by
    show kcCountsB l' = addCounts (some (0, 0, 0)) (kcCountsB l')
    rcases kcCountsB l' with _ | ⟨f, p, k⟩
    · rfl
    · show some (f, p, k) = some (0 + f, 0 + p, 0 + k)
      rw [Nat.zero_add, Nat.zero_add, Nat.zero_add]
  | b :: l, l' => by
    show countStep (kcClassB b) (kcCountsB (l ++ l')) = addCounts (countStep (kcClassB b) (kcCountsB l)) (kcCountsB l')
    rw [kcCountsB_append l l']
    rcases kcClassB b with _ | ⟨t, sm⟩
    · rfl
    · rcases kcCountsB l with _ | ⟨f, p, k⟩
      · rfl
      · rcases kcCountsB l' with _ | ⟨f', p', k'⟩
        · rfl
        · show some _ = some _
          congr 1
          refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> split <;> omega

theorem kcCountsB_spec : ∀ {l : List Box} {f p m : ℕ}, kcCountsB l = some (f, p, m) →
    (∀ b ∈ l, ∃ t sm, kcClassB b = some (t, sm)) ∧ f = l.countP isFailB ∧ p = l.countP isPassB ∧ m = l.countP isSmallB
  | [], f, p, m, h => by
    have h' : (0, 0, 0) = (f, p, m) := Option.some.inj h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    simp
  | b :: rest, f, p, m, h => by
    change countStep (kcClassB b) (kcCountsB rest) = some (f, p, m) at h
    cases hc : kcClassB b with
    | none => rw [hc] at h; exact absurd h (by simp [countStep])
    | some tc =>
      obtain ⟨t, sm⟩ := tc
      cases hr : kcCountsB rest with
      | none => rw [hc, hr] at h; exact absurd h (by simp [countStep])
      | some c =>
        obtain ⟨f', p', m'⟩ := c
        rw [hc, hr] at h
        have h' := Option.some.inj h
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl, rfl⟩ := h'
        obtain ⟨hall, hf, hp, hm⟩ := kcCountsB_spec hr
        refine ⟨fun x hx => ?_, ?_, ?_, ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨t, sm, hc⟩
          · exact hall x hx
        · rw [List.countP_cons, ← hf]
          cases t <;> simp [isFailB, hc]
        · rw [List.countP_cons, ← hp]
          cases t <;> simp [isPassB, hc]
        · rw [List.countP_cons, ← hm]
          cases sm <;> simp [isSmallB, hc]

theorem kcClassB_spec {b : Box} {t sm : Bool} (h : kcClassB b = some (t, sm)) :
    t123Decide b = some t ∧ smallDecide b = some sm ∧ (sm = true → yBounds b = true) := by
  unfold kcClassB at h
  split at h
  · rename_i t' sm' ht hs
    split_ifs at h with hy
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨ht, hs, fun hsm => ?_⟩
    subst hsm
    simpa using hy
  · exact absurd h (by simp)

end L6KSpec
