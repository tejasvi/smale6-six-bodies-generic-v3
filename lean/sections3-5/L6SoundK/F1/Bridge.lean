import L6SoundK.F1.Sort
import L6Sound.F1.Classes
import L6K.F1.Shard

/-!
# The kernel versions of the class and permutation checks are the checks of `L6F1`

`orbitCodesK`, `checkClassK`, `isPermOfK`, `checkPermsK` are `orbitCodes`, `checkClass 6 false`, `isPermOf`,
`checkPerms` with `msort` in place of `sortNat`; by `msort_eq_sortNat` they are equal.
-/

namespace L6K.F1

open L6F1

theorem perms6_length : (perms 6).length = 720 := by decide +kernel

theorem orbitList_length (d : Diagram) : (orbitList 6 d).length = 1440 := by
  have h : ∀ l : List (List ℕ), (l.flatMap fun p => [act 6 p false d, act 6 p true d]).length = 2 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp only [List.length_cons, List.length_nil]
      omega
  unfold orbitList
  rw [h, perms6_length]

theorem orbitCodesK_eq (d : Diagram) : orbitCodesK d = orbitCodes 6 d := by
  have h : ((orbitList 6 d).map (dcode 6)).length ≤ 2 ^ 12 := by
    rw [List.length_map, orbitList_length]
    norm_num
  unfold orbitCodesK orbitCodes
  rw [msort_eq_sortNat h]

theorem checkClassK_eq (x : Diagram × ℕ) : checkClassK x = checkClass 6 false x := by
  unfold checkClassK checkClass
  simp only [orbitCodesK_eq, keyOf, Bool.false_eq_true, ite_false]

theorem perms6_mem_length : ∀ p ∈ perms 6, p.length = 6 := by decide +kernel

theorem checkPermsK_eq : checkPermsK 6 = checkPerms 6 := by
  unfold checkPermsK checkPerms
  have h1 : (perms 6).all (isPermOfK 6) = (perms 6).all (isPermOf 6) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun p hp => ?_
    have hl : p.length ≤ 2 ^ 10 := by
      rw [perms6_mem_length p hp]
      norm_num
    unfold isPermOfK isPermOf
    rw [msort_eq_sortNat hl]
  have h2 : ((perms 6).map (listCode 6)).length ≤ 2 ^ 12 := by
    rw [List.length_map, perms6_length]
    norm_num
  rw [h1, msort_eq_sortNat h2]

end L6K.F1
