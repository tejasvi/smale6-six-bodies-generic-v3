import CC6Full.Statement
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite

/-!
# The statement is not vacuous

A nonzero `F ∈ ℤ[m₁, …, mₙ]` does not vanish at some positive mass vector (`exists_pos_aeval_ne_zero`): it does not
vanish identically on the box `(ℝ_{>0})ⁿ`, whose sides are infinite (`MvPolynomial.funext_set`). Hence the masses
covered by `GenericFiniteness n` form a nonempty (indeed dense open) subset of `(ℝ_{>0})ⁿ`.
-/

namespace CC6Full

open MvPolynomial

theorem exists_pos_aeval_ne_zero {n : ℕ} {F : MvPolynomial (Fin n) ℤ} (hF : F ≠ 0) :
    ∃ m : Fin n → ℝ, (∀ i, 0 < m i) ∧ aeval m F ≠ 0 := by
  have hF' : F.map (Int.castRingHom ℝ) ≠ 0 := fun h =>
    hF (map_injective _ (Int.castRingHom ℝ).injective_int (by rw [h, map_zero]))
  by_contra hall
  push Not at hall
  apply hF'
  refine funext_set (fun _ => Set.Ioi (0 : ℝ)) (fun _ => Set.Ioi_infinite 0) fun x hx => ?_
  rw [map_zero, eval_map]
  have hx' : ∀ i, 0 < x i := fun i => hx i (Set.mem_univ i)
  have := hall x hx'
  rwa [aeval_def] at this

end CC6Full
