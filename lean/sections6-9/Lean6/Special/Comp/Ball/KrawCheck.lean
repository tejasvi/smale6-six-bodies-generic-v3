import Lean6.Special.Comp.Ball.Slope

/-!
# The Krawczyk test on a box of squares: the checker (no Mathlib)

For a square system `F` (`TPoly`, coefficient table `tab`), exact centers `cs` (balls of radius `0`) and a radius `rho`
(units `2^-P`): the slope balls `S` over the squares of half-side `rho` around the centers (`slopeMat`, which also
cover the discs of radius `rho`), `Y` the approximate inverse of their centers, `E = 1 - Y S` (`resMat`) and
`g = Y F(c)` with `F(c)` evaluated at the centers (`tEval`). **`krawOK`** asks, row by row, `s_i < 2^P` (contraction,
`s_i = Σ_j magB(E_ij)`) and `magB(g_i) 2^P + s_i rho < rho 2^P` (inclusion), with small histories: the hypotheses of
`Ball/Kraw.lean`'s `krawczyk` for the sup norm over the complex coordinates, `e_ij = magB(E_ij)/2^P`,
`b_i = magB(g_i)/2^P` (`KrawCheckSem.lean`).
-/

namespace Lean6.Special.Kraw

open Lean6.Special.Ball

/-- The squares of half-side `rho` around the centers `cs`. -/
def sqBox (cs : List CB) (rho : Nat) : List CB := cs.map fun c => ⟨c.re, c.im, rho, c.a, c.s⟩

/-- An exact valid center: `r = 0`, `|cv re| + |cv im| ≤ a ≤ s`. -/
def centerOK (P : Nat) (c : CB) : Bool :=
  Nat.beq c.r 0 && Nat.ble (Nat.add (absB P c.re) (absB P c.im)) c.a && Nat.ble c.a c.s

/-- The row test: contraction, inclusion, small histories. -/
def krawRowOK (P rho : Nat) (row : List CB) (g : CB) : Bool :=
  let s := row.foldl (fun t x => Nat.add t (magB P x)) 0
  Nat.blt s (Nat.pow 2 P) &&
    Nat.blt (Nat.add (Nat.mul (magB P g) (Nat.pow 2 P)) (Nat.mul s rho)) (Nat.mul rho (Nat.pow 2 P)) &&
    row.all (fun x => Nat.ble x.s (smax P)) && Nat.ble g.s (smax P)

/-- **The Krawczyk test** (existence of a zero of `F` in the discs of radius `rho` around the centers). -/
def krawOK (P : Nat) (tab : List CB) (F : List TPoly) (cs : List CB) (rho : Nat) : Bool :=
  let n := F.length
  let S := slopeMat P tab F (sqBox cs rho)
  let Y := fixMat P n (approxInv P S)
  let E := resMat P Y (transpose P n S)
  let g := matVec P Y (F.map fun Fi => tEval P tab cs Fi)
  Nat.beq cs.length n && F.all (fun Fi => Fi.all (termOK n)) && cs.all (centerOK P) &&
    (E.zip g).all (fun eg => krawRowOK P rho eg.1 eg.2)

end Lean6.Special.Kraw
