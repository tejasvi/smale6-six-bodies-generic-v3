import L6KSpec.TropNorm
import Lean6.Special.Poly.Sem
import Mathlib.Data.List.Perm.Basic

/-!
# `normalizeK` has the value of its input

`msortM` permutes its input (`msortM_perm`), so `normalizeK` has the value of its input at every point of every
commutative ring, for every coefficient map (`eval_normalizeK`, as `Lean6.Special.Poly.eval_normalize`), and `isZeroK`
is a sound zero test (`isZeroK_sound`).
-/

namespace L6KSpec.Trop

open Lean6.Special Lean6.Special.Comp

variable {α : Type}

theorem mergeM_perm : ∀ (f : ℕ) (a b : Poly α), (mergeM f a b).Perm (a ++ b)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, x :: a, [] => by
    show (x :: a).Perm ((x :: a) ++ [])
    rw [List.append_nil]
  | f + 1, x :: a, y :: b => by
    show (Bool.rec (motive := fun _ => Poly α) (y :: mergeM f (x :: a) b) (x :: mergeM f a (y :: b))
      (leK x.2 y.2)).Perm _
    cases leK x.2 y.2
    · exact ((mergeM_perm f (x :: a) b).cons y).trans List.perm_middle.symm
    · exact (mergeM_perm f a (y :: b)).cons x

theorem msortM_perm : ∀ (d : ℕ) (l : Poly α), (msortM d l).Perm l
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => List.Perm.refl _
  | d + 1, x :: y :: l => by
    show (mergeM (x :: y :: l).length (msortM d ((x :: y :: l).take ((x :: y :: l).length / 2)))
      (msortM d ((x :: y :: l).drop ((x :: y :: l).length / 2)))).Perm _
    refine (mergeM_perm _ _ _).trans (((msortM_perm d _).append (msortM_perm d _)).trans ?_)
    rw [List.take_append_drop]

variable {C : Coeff α} {R : Type*} [CommRing R] (h : C.Hom R) (x : ℕ → R)

theorem eval_normalizeK (p : Poly α) : Poly.eval h x (normalizeK C p) = Poly.eval h x p := by
  unfold normalizeK
  rw [Poly.eval_filter_nonzero, Poly.eval_combine, Poly.eval_perm h x (msortM_perm 40 _), Poly.eval_trimAll]

/-- **The zero test `isZeroK` is sound.** -/
theorem isZeroK_sound {p : Poly α} (hp : isZeroK C p = true) : Poly.eval h x p = 0 := by
  rw [← eval_normalizeK h x p]
  unfold isZeroK at hp
  rw [List.isEmpty_iff.mp hp]
  rfl

end L6KSpec.Trop
