import Lean6.Special.Comp.Ball.Defs
import Lean6.Special.Comp.Ball.TPoly

/-!
# Uniqueness in a box by divided-difference slopes: the checker (no Mathlib)

For a square system `F = [F₀, …, F_{n-1}]` of polynomials in the variables `0, …, n-1` (`TPoly`, coefficient table
`tab`) and a box `bx` of `n` balls, `slopeMat` encloses the matrix of divided differences
`D_{ij}(u, v) = Σ_t c κ_k (∏_{v' ≠ j} w_{v'}^{e_{v'}}) h_{e_j - 1}(u_j, v_j)`, the sum over the terms `t` of `F_i` in which
the variable `j` occurs, where `w = (u₀, …, u_{j-1}, v_j, …, v_{n-1})` (the hybrid point) and
`h_d(a, b) = Σ_{i ≤ d} a^i b^{d-i}`, for all `u, v` in the box: since every coordinate of `w` lies in its ball, the
ball of `D_{ij}` is the product of the powers of the balls of the box with `h` replaced by `hBall`. Telescoping gives
`F_i(u) - F_i(v) = Σ_j (u_j - v_j) D_{ij}(u, v)` (`SlopeSem.lean`).

**`slopeOK`**: the terms are admissible (variables below `n`, positive exponents, distinct variables per monomial),
the box has `n` balls, and the approximate inverse `M` of the centers of the slope balls gives `‖1 - M S‖∞ < 1` with
small histories (the test of `liftCheck`). Then the slope matrix `S(u, v)` is invertible for all `u, v` in the box, so
two points of the box with the same values of `F` coincide (**`slope_unique`**, `SlopeSem.lean`).
-/

namespace Lean6.Special.Kraw

open Lean6.Special.Ball

section slope

variable (P : Nat)

/-- The ball of `h_d(a, b) = Σ_{i ≤ d} a^i b^{d-i}` for `a, b` in the ball `B`. -/
def hBall (B : CB) (d : Nat) : CB :=
  (List.range (Nat.succ d)).foldl (fun acc i => add P acc (mul P (tPow P B i) (tPow P B (Nat.sub d i)))) (zero P)

/-- The divided difference of a monomial in the variable `j`: the product of the powers of the balls of the box, with
the factor of `j` replaced by `hBall`. -/
def ddMono (bx : List CB) (j : Nat) : List (Nat × Nat) → CB
  | [] => one P
  | ve :: rest =>
    mul P (if ve.1 == j then hBall P (bx.getD j (zero P)) (Nat.sub ve.2 1) else tPow P (bx.getD ve.1 (zero P)) ve.2)
      (ddMono bx j rest)

/-- The divided difference of a term in the variable `j` (the zero ball if `j` does not occur). -/
def ddTerm (tab bx : List CB) (j : Nat) (t : TTerm) : CB :=
  if (t.mono.map Prod.fst).contains j then
    mul P (mul P (ofInt P t.c) (tab.getD t.k (zero P))) (ddMono P bx j t.mono)
  else zero P

/-- The divided difference of a polynomial in the variable `j`. -/
def ddPoly (tab bx : List CB) (j : Nat) : TPoly → CB
  | [] => zero P
  | t :: rest => add P (ddTerm P tab bx j t) (ddPoly tab bx j rest)

/-- The slope matrix: row `i` is `[D_{i,0}, …, D_{i,n-1}]`, `n = |F|`. -/
def slopeMat (tab : List CB) (F : List TPoly) (bx : List CB) : List (List CB) :=
  F.map fun Fi => (List.range F.length).map fun j => ddPoly P tab bx j Fi

end slope

/-- Distinct naturals. -/
def nodupS : List Nat → Bool
  | [] => true
  | a :: l => !(l.contains a) && nodupS l

/-- A term is admissible for `n` variables: indices below `n`, positive exponents, distinct variables. -/
def termOK (n : Nat) (t : TTerm) : Bool :=
  t.mono.all (fun ve => Nat.blt ve.1 n && Nat.blt 0 ve.2) && nodupS (t.mono.map Prod.fst)

/-- **The slope test**: admissible terms, `n` balls, and `‖1 - M S‖∞ < 1` with small histories. -/
def slopeOK (P : Nat) (tab : List CB) (F : List TPoly) (bx : List CB) : Bool :=
  let n := F.length
  let S := slopeMat P tab F bx
  let M := fixMat P n (approxInv P S)
  let qs := rowSumBound P (resMat P M (transpose P n S))
  Nat.beq bx.length n && F.all (fun Fi => Fi.all (termOK n)) && Nat.blt qs.1 (Nat.pow 2 P) && Nat.ble qs.2 (smax P)

end Lean6.Special.Kraw
