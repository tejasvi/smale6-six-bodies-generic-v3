import Lean6.Special.Comp.D88.Boxes.Check
import Lean6.Special.Ball.KrawCheckSem
import Mathlib.Tactic

/-!
# The systems S11 and KC12 of Sec. 6.7 at `μ₀ = (1, 2, 3, 30)`, written from the definitions of the paper

`N4.S11`: the unknowns `v = (X₂, X₃, Y₁, Y₂, Y₃, p₁₂, p₁₃, p₁₄, p₂₃, p₂₄, p₃₄)`, the slice `X₁ = X₂ + 1`, `X₄` and `Y₄`
eliminated by the centre of mass, and the equations: the X-equations of bodies 1, 2, 3, the Y-equations of bodies 1, 2
and the six distance equations. `KC.KC12`: the unknowns `v = (X₂, X₃, Y₁, Y₂, Y₃, Y₄, p₁₂, …, p₃₄)`, `X₁ = 1`,
`X₄ = 0`, and the equations: the X-equations of bodies 1, 2, 3, the equation of the centre
`0 = Σ_{l ≤ 3} μ_l p_{4l}³ (X₄ − X_l)`, the Y-equations of bodies 1, 2 and the six distance equations.

**`N4.eval_s11T`**, **`KC.eval_kc12T`**: the generated term lists `s11T`, `kc12T` (the first taken from the msolve input
of S12) evaluate to these equations, up to the row factors `N4.scale` (`900` for the distances of `14, 24, 34`) and
`KC.scale` (`−1` for the equation of the centre).
-/

namespace Lean6.Special.D88.Boxes

open Lean6.Special.Kraw

/-- The values of the coefficient table `[1]`. -/
def κ1 : ℕ → ℂ := fun v => if v = 0 then 1 else 0

/-- The masses `μ₀ = (1, 2, 3, 30)`. -/
def μ0 : Fin 4 → ℂ := ![1, 2, 3, 30]

namespace N4

/-- The positions `X`: `X₁ = X₂ + 1`, `X₄ = −(μ₁X₁ + μ₂X₂ + μ₃X₃)/μ₄`. -/
noncomputable def X (v : Fin 11 → ℂ) : Fin 4 → ℂ :=
  ![v 0 + 1, v 0, v 1, -(μ0 0 * (v 0 + 1) + μ0 1 * v 0 + μ0 2 * v 1) / μ0 3]

/-- The positions `Y`: `Y₄ = −(μ₁Y₁ + μ₂Y₂ + μ₃Y₃)/μ₄`. -/
noncomputable def Y (v : Fin 11 → ℂ) : Fin 4 → ℂ :=
  ![v 2, v 3, v 4, -(μ0 0 * v 2 + μ0 1 * v 3 + μ0 2 * v 4) / μ0 3]

/-- The variables `p_kl` (symmetric, `0` on the diagonal). -/
def p (v : Fin 11 → ℂ) : Fin 4 → Fin 4 → ℂ :=
  ![![0, v 5, v 6, v 7], ![v 5, 0, v 8, v 9], ![v 6, v 8, 0, v 10], ![v 7, v 9, v 10, 0]]

/-- The X-equation of body `k`: `X_k − Σ_{l≠k} μ_l p_kl³ (X_k − X_l)`. -/
noncomputable def Xeq (v : Fin 11 → ℂ) (k : Fin 4) : ℂ :=
  X v k - ∑ l, if l = k then 0 else μ0 l * p v k l ^ 3 * (X v k - X v l)

/-- The Y-equation of body `k`. -/
noncomputable def Yeq (v : Fin 11 → ℂ) (k : Fin 4) : ℂ :=
  Y v k - ∑ l, if l = k then 0 else μ0 l * p v k l ^ 3 * (Y v k - Y v l)

/-- The distance equation of the pair `ab`: `p_ab² (X_a − X_b)(Y_a − Y_b) − 1`. -/
noncomputable def dist (v : Fin 11 → ℂ) (a b : Fin 4) : ℂ := p v a b ^ 2 * (X v a - X v b) * (Y v a - Y v b) - 1

/-- **The system S11.** -/
noncomputable def S11 (v : Fin 11 → ℂ) : Fin 11 → ℂ :=
  ![Xeq v 0, Xeq v 1, Xeq v 2, Yeq v 0, Yeq v 1, dist v 0 1, dist v 0 2, dist v 0 3, dist v 1 2, dist v 1 3,
    dist v 2 3]

/-- The row factors of `s11T`. -/
def scale : Fin 11 → ℂ := ![1, 1, 1, 1, 1, 1, 1, 900, 1, 900, 900]

theorem s11T_length : s11T.length = 11 := by decide

theorem scale_ne_zero (i : Fin 11) : scale i ≠ 0 := by
  fin_cases i <;> norm_num [scale]

/-- **The generated rows are the equations of S11**, up to the row factors. -/
theorem eval_s11T (v : Fin 11 → ℂ) (i : Fin 11) :
    (s11T.get (i.cast s11T_length.symm)).eval κ1 (extF v) = scale i * S11 v i := by
  fin_cases i <;>
    simp [s11T, TPoly.eval, TTerm.eval, κ1, extF, S11, Xeq, Yeq, dist, X, Y, p, μ0, scale, Fin.sum_univ_four] <;>
    ring

end N4

namespace KC

/-- The positions `X`: `X₁ = 1`, `X₄ = 0`. -/
def X (v : Fin 12 → ℂ) : Fin 4 → ℂ := ![1, v 0, v 1, 0]

/-- The positions `Y`. -/
def Y (v : Fin 12 → ℂ) : Fin 4 → ℂ := ![v 2, v 3, v 4, v 5]

/-- The variables `p_kl`. -/
def p (v : Fin 12 → ℂ) : Fin 4 → Fin 4 → ℂ :=
  ![![0, v 6, v 7, v 8], ![v 6, 0, v 9, v 10], ![v 7, v 9, 0, v 11], ![v 8, v 10, v 11, 0]]

/-- The X-equation of body `k`. -/
def Xeq (v : Fin 12 → ℂ) (k : Fin 4) : ℂ :=
  X v k - ∑ l, if l = k then 0 else μ0 l * p v k l ^ 3 * (X v k - X v l)

/-- The equation of the centre: `Σ_{l ≤ 3} μ_l p_{4l}³ (X₄ − X_l)`. -/
def Xc (v : Fin 12 → ℂ) : ℂ := ∑ l, if l = 3 then 0 else μ0 l * p v 3 l ^ 3 * (X v 3 - X v l)

/-- The Y-equation of body `k`. -/
def Yeq (v : Fin 12 → ℂ) (k : Fin 4) : ℂ :=
  Y v k - ∑ l, if l = k then 0 else μ0 l * p v k l ^ 3 * (Y v k - Y v l)

/-- The distance equation of the pair `ab`. -/
def dist (v : Fin 12 → ℂ) (a b : Fin 4) : ℂ := p v a b ^ 2 * (X v a - X v b) * (Y v a - Y v b) - 1

/-- **The system KC12.** -/
def KC12 (v : Fin 12 → ℂ) : Fin 12 → ℂ :=
  ![Xeq v 0, Xeq v 1, Xeq v 2, Xc v, Yeq v 0, Yeq v 1, dist v 0 1, dist v 0 2, dist v 0 3, dist v 1 2, dist v 1 3,
    dist v 2 3]

/-- The row factors of `kc12T`. -/
def scale : Fin 12 → ℂ := ![1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem kc12T_length : kc12T.length = 12 := by decide

theorem scale_ne_zero (i : Fin 12) : scale i ≠ 0 := by
  fin_cases i <;> norm_num [scale]

/-- **The generated rows are the equations of KC12**, up to the row factors. -/
theorem eval_kc12T (v : Fin 12 → ℂ) (i : Fin 12) :
    (kc12T.get (i.cast kc12T_length.symm)).eval κ1 (extF v) = scale i * KC12 v i := by
  fin_cases i <;>
    simp [kc12T, TPoly.eval, TTerm.eval, κ1, extF, KC12, Xeq, Xc, Yeq, dist, X, Y, p, μ0, scale,
      Fin.sum_univ_four] <;>
    ring

end KC

end Lean6.Special.D88.Boxes
