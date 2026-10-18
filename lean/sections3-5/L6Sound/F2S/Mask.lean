import L6Sound.F2S.Defs

/-!
# Sets of points as bit masks

Membership, insertion, union, intersection, inclusion and the list of points of a mask (`L6F2S.Basic`).
-/

namespace L6.F2S

theorem mem_single (p q : Nat) : mem p (single q) = decide (q = p) := by
  unfold mem single
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem mem_ins (p q c : Nat) : mem p (ins q c) = (mem p c || decide (q = p)) := by
  unfold ins
  rw [show mem p (c ||| single q) = (c ||| single q).testBit p from rfl, Nat.testBit_or]
  rw [← mem_single p q]
  rfl

theorem mem_or (p c d : Nat) : mem p (c ||| d) = (mem p c || mem p d) := by
  unfold mem
  exact Nat.testBit_or c d p

theorem mem_and (p c d : Nat) : mem p (c &&& d) = (mem p c && mem p d) := by
  unfold mem
  exact Nat.testBit_and c d p

theorem mask_ext {c d : Nat} (h : ∀ p, mem p c = mem p d) : c = d :=
  Nat.eq_of_testBit_eq h

theorem subset_iff (c d : Nat) : subset c d = true ↔ ∀ p, mem p c = true → mem p d = true := by
  unfold subset
  rw [beq_iff_eq]
  constructor
  · intro h p hp
    have := congrArg (fun x => mem p x) h
    simp only [mem_and] at this
    rw [hp] at this
    simpa using this
  · intro h
    apply mask_ext
    intro p
    rw [mem_and]
    cases hp : mem p c
    · simp
    · simp [h p hp]

theorem ssubset_iff (c d : Nat) : ssubset c d = true ↔ subset c d = true ∧ c ≠ d := by
  unfold ssubset
  simp [bne_iff_ne]

theorem mem_toList (p c : Nat) : p ∈ toList c ↔ p < 7 ∧ mem p c = true := by
  unfold toList
  simp [List.mem_filter, List.mem_range]

theorem lt7_of_mem {c p : Nat} (hc : c < 128) (h : mem p c = true) : p < 7 := by
  by_contra hp'
  have hp : 7 ≤ p := by omega
  have hlt : c < 2 ^ p := lt_of_lt_of_le hc (by
    calc 128 = 2 ^ 7 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp)
  have := Nat.testBit_eq_false_of_lt hlt
  unfold mem at h
  rw [this] at h
  exact absurd h (by simp)

end L6.F2S
