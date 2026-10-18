import L6K.F1.SortR
import Mathlib.Data.List.Perm.Basic

/-! `msortR` permutes its input. -/

namespace L6K.F1

theorem mergeR_perm : ∀ (f : ℕ) (a b : List ℕ), (mergeR f a b).Perm (a ++ b)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, x :: a, [] => by
    show (x :: a).Perm ((x :: a) ++ [])
    rw [List.append_nil]
  | f + 1, x :: a, y :: b => by
    show (Bool.rec (motive := fun _ => List ℕ) (y :: mergeR f (x :: a) b) (x :: mergeR f a (y :: b)) (Nat.ble x y)).Perm _
    cases Nat.ble x y
    · exact ((mergeR_perm f (x :: a) b).cons y).trans List.perm_middle.symm
    · exact (mergeR_perm f a (y :: b)).cons x

theorem msortR_perm : ∀ (d : ℕ) (l : List ℕ), (msortR d l).Perm l
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => List.Perm.refl _
  | d + 1, x :: y :: l => by
    show (mergeR (x :: y :: l).length (msortR d ((x :: y :: l).take ((x :: y :: l).length / 2)))
      (msortR d ((x :: y :: l).drop ((x :: y :: l).length / 2)))).Perm _
    refine (mergeR_perm _ _ _).trans (((msortR_perm d _).append (msortR_perm d _)).trans ?_)
    rw [List.take_append_drop]

end L6K.F1
