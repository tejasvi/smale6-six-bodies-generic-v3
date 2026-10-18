import Lean6.Special.Comp.Poly

/-!
# The equations of the compact model `Z(μ)` of `C₄` (Section 7.3), as integer polynomials (no Mathlib)

Variables (indices): `s = 0`, `t = 1`, `P₁₂ = 2`, `P₁₃ = 3`, `P₁₄ = 4`, `P₂₃ = 5`, `P₂₄ = 6`, `P₃₄ = 7`, `c = 8`.
Bodies `0, 1, 2, 3` (the paper's `1, 2, 3, 4`, body `4` the centre), masses `μ = (μ₁, μ₂, μ₃, μ₄)` and
`ξ = (μ₃ s, μ₃ t, −(μ₁ s + μ₂ t), 0)`. The eleven equations, in the order of the paper:

* (I) `Σ_{l ≠ k} μ_l P_kl³ (ξ_k − ξ_l)` for `k = 1, …, 4`;
* (II) `Σ_{l ≠ k} μ_l P_kl Π_{j ≠ k, l} (ξ_k − ξ_j) − c Π_{l ≠ k} (ξ_k − ξ_l)` for `k = 1, 2, 3`;
* (III) `a_ln a_nk + a_kl a_nk + a_kl a_ln` with `a_kl = P_kl² (ξ_k − ξ_l)`, for the triangles `{k, l, n}` =
  `123, 124, 134, 234`.

A chart sets one of `s, t` and one of `P₁₂, …, P₃₄, c` equal to `1` (`chartSub`); the fourteen charts are `charts`.
-/

namespace Lean6.Special.Comp.C4

open Lean6.Special.Comp

/-- The variable `i` as an integer polynomial. -/
def V (i : Nat) : Poly Int := Poly.var intC i

/-- The constant `a`. -/
def K (a : Int) : Poly Int := Poly.const a

/-- Product. -/
def mul (f g : Poly Int) : Poly Int := Poly.mul intC f g

/-- Difference. -/
def sub (f g : Poly Int) : Poly Int := Poly.sub intC f g

/-- The index of the variable `P_kl` (bodies `0, …, 3`, `k ≠ l`). -/
def pIdx (k l : Nat) : Nat :=
  match min k l, max k l with
  | 0, 1 => 2
  | 0, 2 => 3
  | 0, 3 => 4
  | 1, 2 => 5
  | 1, 3 => 6
  | _, _ => 7

/-- `P_kl`. -/
def P (k l : Nat) : Poly Int := V (pIdx k l)

/-- The position `ξ_k`. -/
def xi (μ₁ μ₂ μ₃ : Int) : Nat → Poly Int
  | 0 => mul (K μ₃) (V 0)
  | 1 => mul (K μ₃) (V 1)
  | 2 => sub (mul (K (-μ₁)) (V 0)) (mul (K μ₂) (V 1))
  | _ => []

/-- `ξ_k − ξ_l`. -/
def dxi (μ₁ μ₂ μ₃ : Int) (k l : Nat) : Poly Int := sub (xi μ₁ μ₂ μ₃ k) (xi μ₁ μ₂ μ₃ l)

/-- The other bodies. -/
def others (k : Nat) : List Nat := [0, 1, 2, 3].filter (· != k)

/-- Equation (I) of body `k`. -/
def eqI (μ : List Int) (k : Nat) : Poly Int :=
  Poly.sum ((others k).map fun l =>
    mul (K (μ.getD l 0)) (mul (mul (P k l) (mul (P k l) (P k l))) (dxi (μ.getD 0 0) (μ.getD 1 0) (μ.getD 2 0) k l)))

/-- The product of `ξ_k − ξ_j` over the bodies `j` of a list. -/
def prodD (μ : List Int) (k : Nat) (js : List Nat) : Poly Int :=
  js.foldr (fun j acc => mul (dxi (μ.getD 0 0) (μ.getD 1 0) (μ.getD 2 0) k j) acc) (K 1)

/-- Equation (II) of body `k`. -/
def eqII (μ : List Int) (k : Nat) : Poly Int :=
  sub (Poly.sum ((others k).map fun l => mul (K (μ.getD l 0)) (mul (P k l) (prodD μ k ((others k).filter (· != l))))))
    (mul (V 8) (prodD μ k (others k)))

/-- `a_kl = P_kl² (ξ_k − ξ_l)`. -/
def aa (μ : List Int) (k l : Nat) : Poly Int :=
  mul (mul (P k l) (P k l)) (dxi (μ.getD 0 0) (μ.getD 1 0) (μ.getD 2 0) k l)

/-- Equation (III) of the triangle `{k, l, n}`. -/
def eqIII (μ : List Int) (k l n : Nat) : Poly Int :=
  Poly.add (Poly.add (mul (aa μ l n) (aa μ n k)) (mul (aa μ k l) (aa μ n k))) (mul (aa μ k l) (aa μ l n))

/-- The eleven equations of `Z(μ)`, in the order of the paper. -/
def eqs (μ : List Int) : List (Poly Int) :=
  [eqI μ 0, eqI μ 1, eqI μ 2, eqI μ 3, eqII μ 0, eqII μ 1, eqII μ 2,
   eqIII μ 0 1 2, eqIII μ 0 1 3, eqIII μ 0 2 3, eqIII μ 1 2 3]

/-- The fourteen charts: one of `s, t` (variable `0` or `1`) and one of `P₁₂, …, P₃₄, c` (variables `2, …, 8`). -/
def charts : List (Nat × Nat) := [0, 1].flatMap fun a => [2, 3, 4, 5, 6, 7, 8].map fun b => (a, b)

/-- The substitution of a chart: its two variables become `1`. -/
def chartSub (ch : Nat × Nat) (i : Nat) : Poly Int := if i == ch.1 || i == ch.2 then K 1 else V i

/-- The equations on a chart. -/
def chartEqs (μ : List Int) (ch : Nat × Nat) : List (Poly Int) := (eqs μ).map (Poly.subst intC (chartSub ch))

/-- Integer coefficients reduced modulo `p`, as natural numbers. -/
def toMod (p : Nat) (f : Poly Int) : Poly Nat := Poly.mapC (fun a : Int => (a % (p : Int)).toNat) f

end Lean6.Special.Comp.C4
