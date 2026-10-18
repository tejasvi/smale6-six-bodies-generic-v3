import Mathlib.Tactic
import L6F1

/-!
# Basic lemmas on the codes of labelled diagrams

Digits of the edge codes, positions of pairs, kinds, and sorted lists of natural numbers.
-/

namespace L6F1

/-! ## Digits and kinds -/

theorem digit_lt (e i : ℕ) : digit e i < 4 := Nat.mod_lt _ (by norm_num)

/-- The digits below the position `J` are those of the residue modulo `4 ^ J`. -/
theorem digit_mod {e i J : ℕ} (h : i < J) : digit (e % 4 ^ J) i = digit e i := by
  unfold digit
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  have e1 : 4 ^ (i + k + 1) = 4 ^ i * 4 ^ (k + 1) := by rw [← pow_add]; ring_nf
  rw [e1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 4 (Nat.succ_ne_zero k))]

theorem mod_four_pow_succ (e j : ℕ) : e % 4 ^ (j + 1) = e % 4 ^ j + digit e j * 4 ^ j := by
  unfold digit
  rw [Nat.mod_pow_succ]
  ring

theorem ppos_comm (a b : ℕ) : ppos a b = ppos b a := by
  unfold ppos
  rcases lt_trichotomy a b with h | rfl | h
  · rw [ite_eq_left h, ite_eq_right (by omega)]
  · rfl
  · rw [ite_eq_right (by omega), ite_eq_left h]

theorem kind_comm (e a b : ℕ) : kind e a b = kind e b a := by
  unfold kind
  by_cases h : a = b
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), ppos_comm]

theorem kind_self (e a : ℕ) : kind e a a = 0 := by simp [kind]

theorem kind_lt (e a b : ℕ) : kind e a b < 4 := by
  unfold kind
  split_ifs
  · norm_num
  · exact digit_lt _ _

/-- The kind of a pair whose position is below `J` is the same in the residue of the edge code modulo `4 ^ J`. -/
theorem kind_mod {e J a b : ℕ} (h : ppos a b < J) : kind (e % 4 ^ J) a b = kind e a b := by
  unfold kind
  split_ifs
  · rfl
  · exact digit_mod h

/-! ## Sorted lists -/

theorem pairwise_of_strictSorted : ∀ {l : List ℕ}, strictSorted l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_strictSorted h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem nodup_of_strictSorted {l : List ℕ} (h : strictSorted l = true) : l.Nodup :=
  (pairwise_of_strictSorted h).imp ne_of_lt

theorem sortNat_perm (l : List ℕ) : (sortNat l).Perm l := List.mergeSort_perm _ _

theorem mem_sortNat {l : List ℕ} {x : ℕ} : x ∈ sortNat l ↔ x ∈ l := (sortNat_perm l).mem_iff

/-- A list whose sorted copy is strictly increasing has no repetitions. -/
theorem nodup_of_strictSorted_sortNat {l : List ℕ} (h : strictSorted (sortNat l) = true) : l.Nodup :=
  (sortNat_perm l).nodup_iff.mp (nodup_of_strictSorted h)

theorem mem_dedupSorted : ∀ {l : List ℕ} {x : ℕ}, x ∈ dedupSorted l ↔ x ∈ l
  | [], _ => Iff.rfl
  | [_], _ => Iff.rfl
  | a :: b :: l, x => by
    have ih := @mem_dedupSorted (b :: l) x
    unfold dedupSorted
    split_ifs with h
    · rw [ih, h]
      simp
    · rw [List.mem_cons, ih]
      simp

end L6F1
