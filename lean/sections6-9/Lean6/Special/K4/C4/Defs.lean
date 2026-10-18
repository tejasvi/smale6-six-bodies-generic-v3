import Lean6.Special.Comp.K4.C4.Sys
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The equations of `Z(μ)` on the charts, as definitions

The definitions used in the statements of `Final.lean` (`lemma_7_9`, `sec_7_4`): the equations `eqsZ`, `eqsAt`, the
point `chartPt` of a chart and the properties `NoZero`, `UnitIdeal`, with `eqsAt_map`; kept apart from the checks so
that a module can state these results without importing a computation.
-/

namespace Lean6.Special.K4.C4

open Lean6.Special Lean6.Special.Comp Finset

section Equations

variable {R : Type*} [CommRing R]

/-- The positions `ξ = (μ₃ s, μ₃ t, −(μ₁ s + μ₂ t), 0)`. -/
def xiZ (μ : Fin 4 → R) (s t : R) : Fin 4 → R := ![μ 2 * s, μ 2 * t, -(μ 0 * s + μ 1 * t), 0]

/-- The index of `P_kl` among `P₁₂, P₁₃, P₁₄, P₂₃, P₂₄, P₃₄`. -/
def pairIdx : Fin 4 → Fin 4 → Fin 6
  | 0, 1 => 0 | 1, 0 => 0
  | 0, 2 => 1 | 2, 0 => 1
  | 0, 3 => 2 | 3, 0 => 2
  | 1, 2 => 3 | 2, 1 => 3
  | 1, 3 => 4 | 3, 1 => 4
  | 2, 3 => 5 | 3, 2 => 5
  | _, _ => 0

/-- The symmetric matrix of the `P_kl`. -/
def Pm (P : Fin 6 → R) (k l : Fin 4) : R := P (pairIdx k l)

/-- Equation (I) of body `k`. -/
def eqIZ (μ ξ : Fin 4 → R) (P : Fin 4 → Fin 4 → R) (k : Fin 4) : R :=
  ∑ l ∈ univ.filter (· ≠ k), μ l * P k l ^ 3 * (ξ k - ξ l)

/-- Equation (II) of body `k`. -/
def eqIIZ (μ ξ : Fin 4 → R) (P : Fin 4 → Fin 4 → R) (c : R) (k : Fin 4) : R :=
  ∑ l ∈ univ.filter (· ≠ k), μ l * P k l * ∏ j ∈ univ.filter (fun j => j ≠ k ∧ j ≠ l), (ξ k - ξ j) -
    c * ∏ l ∈ univ.filter (· ≠ k), (ξ k - ξ l)

/-- `a_kl = P_kl² (ξ_k − ξ_l)`. -/
def aZ (ξ : Fin 4 → R) (P : Fin 4 → Fin 4 → R) (k l : Fin 4) : R := P k l ^ 2 * (ξ k - ξ l)

/-- Equation (III) of the triangle `{k, l, n}`. -/
def eqIIIZ (ξ : Fin 4 → R) (P : Fin 4 → Fin 4 → R) (k l n : Fin 4) : R :=
  aZ ξ P l n * aZ ξ P n k + aZ ξ P k l * aZ ξ P n k + aZ ξ P k l * aZ ξ P l n

/-- **The eleven equations of `Z(μ)`** at the point `(s, t, P, c)`, in the order of the paper. -/
def eqsZ (μ : Fin 4 → R) (s t : R) (P : Fin 6 → R) (c : R) : List R :=
  [eqIZ μ (xiZ μ s t) (Pm P) 0, eqIZ μ (xiZ μ s t) (Pm P) 1, eqIZ μ (xiZ μ s t) (Pm P) 2,
   eqIZ μ (xiZ μ s t) (Pm P) 3,
   eqIIZ μ (xiZ μ s t) (Pm P) c 0, eqIIZ μ (xiZ μ s t) (Pm P) c 1, eqIIZ μ (xiZ μ s t) (Pm P) c 2,
   eqIIIZ (xiZ μ s t) (Pm P) 0 1 2, eqIIIZ (xiZ μ s t) (Pm P) 0 1 3, eqIIIZ (xiZ μ s t) (Pm P) 0 2 3,
   eqIIIZ (xiZ μ s t) (Pm P) 1 2 3]

/-- The equations at the point `x` (coordinates `s, t, P₁₂, …, P₃₄, c` = `x 0, …, x 8`). -/
def eqsAt (μ : Fin 4 → R) (x : ℕ → R) : List R := eqsZ μ (x 0) (x 1) (fun j => x (j + 2)) (x 8)

/-- Masses from a list of integers. -/
def muOf (μL : List ℤ) : Fin 4 → R := fun i => ((μL.getD i 0 : ℤ) : R)

end Equations

section Maps

variable {R : Type*} [CommRing R]

theorem eqsAt_map {S : Type*} [CommRing S] (φ : R →+* S) (μL : List ℤ) (x : ℕ → R) :
    eqsAt (muOf μL) (fun j => φ (x j)) = (eqsAt (muOf μL) x).map φ := by
  simp [eqsAt, eqsZ, eqIZ, eqIIZ, eqIIIZ, aZ, xiZ, Pm, muOf, map_sum, map_prod, Finset.sum_filter,
    Finset.prod_filter, Fin.sum_univ_four, Fin.prod_univ_four, pairIdx]

end Maps

/-- The point of the chart `ch` in the polynomial ring: the coordinates `ch.1`, `ch.2` are `1`, the others the
variables. -/
noncomputable def chartPt (p : ℕ) (ch : ℕ × ℕ) (j : ℕ) : MvPolynomial ℕ (ZMod p) :=
  if j = ch.1 ∨ j = ch.2 then 1 else MvPolynomial.X j

/-- No common zero on any chart, in any nontrivial commutative `ZMod p`-algebra. -/
def NoZero (μL : List ℤ) (p : ℕ) [NeZero p] : Prop :=
  ∀ (R : Type) [CommRing R] [Nontrivial R] [Algebra (ZMod p) R], ∀ ch ∈ C4.charts, ∀ x : ℕ → R,
    x ch.1 = 1 → x ch.2 = 1 → ¬ ∀ e ∈ eqsAt (muOf μL) x, e = 0

/-- The unit ideal on every chart, over `ZMod p`. -/
def UnitIdeal (μL : List ℤ) (p : ℕ) : Prop :=
  ∀ ch ∈ C4.charts, (1 : MvPolynomial ℕ (ZMod p)) ∈ Ideal.span {e | e ∈ eqsAt (muOf μL) (chartPt p ch)}

end Lean6.Special.K4.C4
