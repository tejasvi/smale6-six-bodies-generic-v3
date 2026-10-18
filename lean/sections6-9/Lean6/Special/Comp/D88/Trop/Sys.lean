import Lean6.Special.Comp.D88.Trop.Check

/-!
# Lemma 6.19(a): the systems `S12` and `KC12`, the torus coordinates `ξ(v)` (no Mathlib)

Written from §6.7 of the paper, with the masses `μ₁, …, μ₄` as variables and `i_u` for the inverse of a mass.

* **N4** (the system `S12` of `N₄(μ)`): unknowns `v = (X₂, X₃, Y₁, Y₂, Y₃, p₁₂, p₁₃, p₁₄, p₂₃, p₂₄, p₃₄)` (variables
  `0, …, 10`), masses (`11, …, 14`), `i_u = 1/μ₄` (`15`); `X₁ = X₂ + 1` (the slice), `X₄ = −(μ₁X₁ + μ₂X₂ + μ₃X₃)/μ₄`,
  `Y₄ = −(μ₁Y₁ + μ₂Y₂ + μ₃Y₃)/μ₄` (the centre of mass). `S12` = the `X`- and `Y`-equations of the bodies `1, 2, 3` and the
  six distance equations. `ξ = (X₁₃, X₁₄, X₂₃, X₂₄, X₃₄, Y₁₂, Y₁₃, Y₁₄, Y₂₃, Y₂₄, Y₃₄, p₁₂, …, p₃₄)` with
  `X_kl = X_k − X_l`.
* **KC** (the system `KC12` of the centred system): unknowns `v = (X₂, X₃, Y₁, Y₂, Y₃, Y₄, p₁₂, …, p₃₄)` (`0, …, 11`),
  masses (`12, …, 15`), `i_u = 1/μ₃` (`16`); `X₁ = 1` (the slice), `X₄ = 0`. `KC12` = the four `X`-equations, the
  `Y`-equations of the bodies `1, 2` and the six distance equations. `ξ = (X₂, X₃, X₁₂, X₁₃, X₂₃, U₁, U₂, U₃, U₁₂,
  U₁₃, U₂₃, p₁₂, …, p₃₄)` with `U_k = Y_k − Y₄`, `U_kl = Y_k − Y_l`.

The equations: `Xeq_k = X_k − Σ_{l≠k} μ_l p_kl³ (X_k − X_l)`, `Yeq_k` likewise, `D_kl = p_kl² (X_k − X_l)(Y_k − Y_l) − 1`.
-/

namespace Lean6.Special.Comp.D88.Trop

open Lean6.Special.Comp

/-- A variable. -/
def V (i : Nat) : Poly Int := Poly.var intC i
/-- An integer constant. -/
def K (c : Int) : Poly Int := Poly.const c
/-- Sum. -/
def pa (a b : Poly Int) : Poly Int := Poly.normalize intC (Poly.add a b)
/-- Difference. -/
def ps (a b : Poly Int) : Poly Int := Poly.normalize intC (Poly.sub intC a b)
/-- Product. -/
def pm (a b : Poly Int) : Poly Int := Poly.normalize intC (Poly.mul intC a b)
/-- Sum of a list. -/
def psum (l : List (Poly Int)) : Poly Int := Poly.normalize intC (Poly.sum l)

/-- The index of the pair `{k, l}` in `12, 13, 14, 23, 24, 34`. -/
def pairIdx (k l : Nat) : Nat :=
  let a := min k l
  let b := max k l
  if a = 1 then b - 2 else if a = 2 then b + 0 else 5

/-- The six pairs. -/
def pairs : List (Nat × Nat) := [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- The equations of a four-body system, from the positions `X`, `Y`, the variable index of `p₁₂` and of `μ₁`. -/
structure Bodies where
  X : Nat → Poly Int
  Y : Nat → Poly Int
  p0 : Nat
  mu0 : Nat

namespace Bodies

/-- `p_kl`. -/
def P (B : Bodies) (k l : Nat) : Poly Int := V (B.p0 + pairIdx k l)
/-- `μ_k`. -/
def mu (B : Bodies) (k : Nat) : Poly Int := V (B.mu0 + k - 1)

/-- `Z_k − Σ_{l≠k} μ_l p_kl³ (Z_k − Z_l)`. -/
def eqn (B : Bodies) (Z : Nat → Poly Int) (k : Nat) : Poly Int :=
  ps (Z k) (psum (([1, 2, 3, 4].filter (· ≠ k)).map fun l =>
    pm (pm (B.mu l) (Poly.pow intC (B.P k l) 3)) (ps (Z k) (Z l))))

/-- `Xeq_k`. -/
def Xeq (B : Bodies) (k : Nat) : Poly Int := B.eqn B.X k
/-- `Yeq_k`. -/
def Yeq (B : Bodies) (k : Nat) : Poly Int := B.eqn B.Y k
/-- `D_kl`. -/
def D (B : Bodies) (k l : Nat) : Poly Int :=
  ps (pm (pm (Poly.pow intC (B.P k l) 2) (ps (B.X k) (B.X l))) (ps (B.Y k) (B.Y l))) (K 1)

end Bodies

/-! ## N4 -/

/-- The positions of `N4`. -/
def n4Bodies : Bodies where
  X := fun k => match k with
    | 1 => pa (V 0) (K 1)
    | 2 => V 0
    | 3 => V 1
    | _ => pm (K (-1)) (pm (psum [pm (V 11) (pa (V 0) (K 1)), pm (V 12) (V 0), pm (V 13) (V 1)]) (V 15))
  Y := fun k => match k with
    | 1 => V 2
    | 2 => V 3
    | 3 => V 4
    | _ => pm (K (-1)) (pm (psum [pm (V 11) (V 2), pm (V 12) (V 3), pm (V 13) (V 4)]) (V 15))
  p0 := 5
  mu0 := 11

/-- `S12`: the `X`- and `Y`-equations of the bodies `1, 2, 3` and the six distance equations. -/
def n4F : List (Poly Int) :=
  [n4Bodies.Xeq 1, n4Bodies.Xeq 2, n4Bodies.Xeq 3, n4Bodies.Yeq 1, n4Bodies.Yeq 2, n4Bodies.Yeq 3] ++
    pairs.map fun kl => n4Bodies.D kl.1 kl.2

/-- `ξ(v)` and the masses: the substitution for the variables of `flat g` (`ξ` = `0, …, 16`, `μ` = `17, …, 20`). -/
def n4σ (i : Nat) : Poly Int :=
  let X := n4Bodies.X
  let Y := n4Bodies.Y
  match i with
  | 0 => ps (X 1) (X 3)
  | 1 => ps (X 1) (X 4)
  | 2 => ps (X 2) (X 3)
  | 3 => ps (X 2) (X 4)
  | 4 => ps (X 3) (X 4)
  | 5 => ps (Y 1) (Y 2)
  | 6 => ps (Y 1) (Y 3)
  | 7 => ps (Y 1) (Y 4)
  | 8 => ps (Y 2) (Y 3)
  | 9 => ps (Y 2) (Y 4)
  | 10 => ps (Y 3) (Y 4)
  | i => if i < 17 then V (i - 6) else V (i - 6)

/-- `μ₄ · i_u − 1`. -/
def n4rel : Poly Int := ps (pm (V 14) (V 15)) (K 1)

/-! ## KC -/

/-- The positions of `KC`. -/
def kcBodies : Bodies where
  X := fun k => match k with
    | 1 => K 1
    | 2 => V 0
    | 3 => V 1
    | _ => K 0
  Y := fun k => match k with
    | 1 => V 2
    | 2 => V 3
    | 3 => V 4
    | _ => V 5
  p0 := 6
  mu0 := 12

/-- `KC12`: the four `X`-equations, the `Y`-equations of the bodies `1, 2` and the six distance equations. -/
def kcF : List (Poly Int) :=
  [kcBodies.Xeq 1, kcBodies.Xeq 2, kcBodies.Xeq 3, kcBodies.Xeq 4, kcBodies.Yeq 1, kcBodies.Yeq 2] ++
    pairs.map fun kl => kcBodies.D kl.1 kl.2

/-- `ξ(v)` and the masses for `KC` (`ξ` = `0, …, 16`, `μ` = `17, …, 20`). -/
def kcσ (i : Nat) : Poly Int :=
  let X := kcBodies.X
  let Y := kcBodies.Y
  match i with
  | 0 => V 0
  | 1 => V 1
  | 2 => ps (X 1) (X 2)
  | 3 => ps (X 1) (X 3)
  | 4 => ps (X 2) (X 3)
  | 5 => ps (Y 1) (Y 4)
  | 6 => ps (Y 2) (Y 4)
  | 7 => ps (Y 3) (Y 4)
  | 8 => ps (Y 1) (Y 2)
  | 9 => ps (Y 1) (Y 3)
  | 10 => ps (Y 2) (Y 3)
  | i => V (i - 5)

/-- `μ₃ · i_u − 1`. -/
def kcrel : Poly Int := ps (pm (V 14) (V 16)) (K 1)

end Lean6.Special.Comp.D88.Trop
