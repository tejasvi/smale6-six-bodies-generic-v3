import L6Sound.F1.Basic
import L6K.F1.Sort
import Mathlib.Data.List.Sort
import Mathlib.Order.Basic

/-!
# The structural merge sort agrees with `sortNat`

`L6K.F1.msort` (structural recursion with fuel, evaluated by the kernel) returns a sorted permutation of its input
when the fuel `d` satisfies `length ≤ 2^d`; so does `L6F1.sortNat` (well-founded, compiled code). Sorted permutations
of the same list are equal, hence `msort d l = sortNat l`.
-/

namespace L6K.F1

open L6F1

theorem merge_perm : ∀ (f : ℕ) (a b : List ℕ), (merge f a b).Perm (a ++ b)
  | 0, a, b => by simp [merge]
  | f + 1, [], b => by simp [merge]
  | f + 1, x :: a, [] => by simp [merge]
  | f + 1, x :: a, y :: b => by
    unfold merge
    split_ifs with h
    · exact (merge_perm f a (y :: b)).cons x
    · have h1 := (merge_perm f (x :: a) b).cons y
      refine h1.trans ?_
      simpa using (List.perm_middle (a := y) (l₁ := x :: a) (l₂ := b)).symm

theorem merge_sorted : ∀ (f : ℕ) (a b : List ℕ), a.length + b.length ≤ f →
    a.Pairwise (· ≤ ·) → b.Pairwise (· ≤ ·) → (merge f a b).Pairwise (· ≤ ·)
  | 0, a, b, h, ha, hb => by
    have : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    have : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst_vars; simp [merge]
  | f + 1, [], b, _, _, hb => by simpa [merge] using hb
  | f + 1, x :: a, [], _, ha, _ => by simpa [merge] using ha
  | f + 1, x :: a, y :: b, h, ha, hb => by
    unfold merge
    split_ifs with hxy
    · have ih := merge_sorted f a (y :: b) (by simp at h ⊢; omega) ha.of_cons hb
      refine List.Pairwise.cons ?_ ih
      intro z hz
      rcases List.mem_append.mp ((merge_perm f a (y :: b)).subset hz) with hz | hz
      · exact List.rel_of_pairwise_cons ha hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · exact le_trans hxy (List.rel_of_pairwise_cons hb hz)
    · have hyx : y ≤ x := by omega
      have ih := merge_sorted f (x :: a) b (by simp at h ⊢; omega) ha hb.of_cons
      refine List.Pairwise.cons ?_ ih
      intro z hz
      rcases List.mem_append.mp ((merge_perm f (x :: a) b).subset hz) with hz | hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact hyx
        · exact le_trans hyx (List.rel_of_pairwise_cons ha hz)
      · exact List.rel_of_pairwise_cons hb hz

theorem msort_perm : ∀ (d : ℕ) (l : List ℕ), (msort d l).Perm l
  | 0, l => by simp [msort]
  | d + 1, [] => by simp [msort]
  | d + 1, [x] => by simp [msort]
  | d + 1, x :: y :: l => by
    unfold msort
    simp only
    refine (merge_perm _ _ _).trans ?_
    refine ((msort_perm d _).append (msort_perm d _)).trans ?_
    rw [List.take_append_drop]

theorem msort_sorted : ∀ (d : ℕ) (l : List ℕ), l.length ≤ 2 ^ d → (msort d l).Pairwise (· ≤ ·)
  | 0, [], _ => by simp [msort]
  | 0, [x], _ => by simp [msort]
  | 0, x :: y :: l, h => by simp at h
  | d + 1, [], _ => by simp [msort]
  | d + 1, [x], _ => by simp [msort]
  | d + 1, x :: y :: l, h => by
    unfold msort
    simp only
    have hlen : (x :: y :: l).length ≤ 2 ^ (d + 1) := h
    apply merge_sorted
    · rw [(msort_perm d _).length_eq, (msort_perm d _).length_eq, List.length_take, List.length_drop]
      omega
    · apply msort_sorted d
      rw [List.length_take]
      have : (x :: y :: l).length / 2 ≤ 2 ^ d := by rw [pow_succ] at hlen; omega
      omega
    · apply msort_sorted d
      rw [List.length_drop]
      have : (x :: y :: l).length - (x :: y :: l).length / 2 ≤ 2 ^ d := by rw [pow_succ] at hlen; omega
      exact this

theorem sortNat_sorted (l : List ℕ) : (sortNat l).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  unfold sortNat
  exact h.imp (fun hab => by simpa using hab)

/-- **The two sorts agree** when the fuel suffices. -/
theorem msort_eq_sortNat {d : ℕ} {l : List ℕ} (h : l.length ≤ 2 ^ d) : msort d l = sortNat l :=
  List.Perm.eq_of_pairwise' (msort_sorted d l h) (sortNat_sorted l) ((msort_perm d l).trans (sortNat_perm l).symm)

end L6K.F1
