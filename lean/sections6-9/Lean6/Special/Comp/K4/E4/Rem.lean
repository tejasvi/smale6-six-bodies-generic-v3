import Lean6.Special.Comp.K4.E4.Run

/-!
# Remark 7.14 (no Mathlib)

At `μ = (1, 1, 1, 2), (5, 2, 11, 3), (1, 2, 3, 4), (2, 3, 5, 7)`: for each of the 64 sign patterns, either
* the construction of the remark applies (`consApplies`: distinct `i, j, k` with `μ_k = μ_i + μ_j`, `l` the fourth
  body, `σ_{li} = σ_{lj} = −σ_{lk}`): then its point (`consPoint`) is a common zero of `G_σ` (exact integer
  evaluation), and `d · D · ξ_i` lies in the span of the Macaulay rows of degree 7 for `i = 1, 2, 3`, with
  `D = ∏_{k < l} (ξ_k − ξ_l)` and `d ≠ 0` (cofactors found by exact rational elimination, untrusted; the identity
  is checked exactly), so every common zero has two coinciding points;
* or it does not, and the Macaulay check of degree 8 (`macCheck`) passes, so `G_σ` has no common zero.
The numbers of patterns of the first kind are 36, 16, 28, 28 (`rem714_*`).
-/

namespace Lean6.Special.Comp.E4

/-- The construction of Remark 7.14 applies to the sign pattern `w` at masses `μ`. -/
def consApplies (μ : List Int) (w : List Int) : Bool :=
  (List.range 4).any fun i => (List.range 4).any fun j => (List.range 4).any fun k =>
    i < j && i != k && j != k && μ.getD k 0 == μ.getD i 0 + μ.getD j 0 &&
      (sigmaOf w (6 - i - j - k) i == sigmaOf w (6 - i - j - k) j &&
        sigmaOf w (6 - i - j - k) i == -sigmaOf w (6 - i - j - k) k)

/-- The fourth body `l` of the first decomposition found (or `4` if none). -/
def consL (μ : List Int) (w : List Int) : Nat :=
  let ls := (List.range 4).flatMap fun i => (List.range 4).flatMap fun j => (List.range 4).filterMap fun k =>
    if i < j && i != k && j != k && μ.getD k 0 == μ.getD i 0 + μ.getD j 0 &&
      (sigmaOf w (6 - i - j - k) i == sigmaOf w (6 - i - j - k) j &&
        sigmaOf w (6 - i - j - k) i == -sigmaOf w (6 - i - j - k) k) then some (6 - i - j - k) else none
  ls.headD 4

/-- The point of the construction, `(ξ_1, ξ_2, ξ_3)` with `ξ_0 = 0`: three coinciding bodies, the fourth at
distance `1`. -/
def consPoint (μ : List Int) (w : List Int) : List Int :=
  let l := consL μ w
  if l == 0 then [-1, -1, -1] else (List.range 3).map fun t => if t + 1 == l then 1 else 0

/-- `x^m` at an integer point. -/
def monoEvalZ (x : List Int) : Mono → Nat → Int
  | [], _ => 1
  | e :: m, i => x.getD i 0 ^ e * monoEvalZ x m (i + 1)

/-- A polynomial over `ℤ[j]` at an integer point. -/
def evalZJ (x : List Int) (p : Poly ZJ) : ZJ := Poly.sumZJ ((p.map fun t => zjC.mul t.1 (monoEvalZ x t.2 0, 0)))
where
  /-- the sum of a list in `ℤ[j]` -/
  Poly.sumZJ : List ZJ → ZJ
    | [] => (0, 0)
    | a :: l => zjC.add a (Poly.sumZJ l)

/-- `D = ∏_{k < l} (ξ_k − ξ_l)`. -/
def Dpoly : Poly ZJ :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)].foldr
    (fun kl acc => Poly.normalize zjC (Poly.mul zjC (Poly.sub zjC (xiP kl.1) (xiP kl.2)) acc)) [(zjC.one, [])]

/-- Untrusted: a rational solution `c` of `Σ_r c_r A_r = t` (Gauss–Jordan on the transposed system). -/
def solveQ (A : List (List Int)) (t : List Int) : List Rat := Id.run do
  let nr := A.length
  let ncol := t.length
  -- equations: for each monomial index q: Σ_r c_r A_r[q] = t[q]
  let mut M : Array (Array Rat) := (Array.range ncol).map fun q =>
    ((Array.range nr).map fun r => ((A.getD r []).getD q 0 : Rat)).push (t.getD q 0 : Rat)
  let mut pivCols : Array Nat := #[]
  let mut row := 0
  for col in [0:nr] do
    if row < ncol then
      let mut piv := ncol
      for q in [row:ncol] do
        if piv == ncol && (M[q]!)[col]! != 0 then piv := q
      if piv < ncol then
        let rp := M[piv]!
        M := (M.set! piv (M[row]!)).set! row rp
        let inv := 1 / (M[row]!)[col]!
        let rr := (M[row]!).map (· * inv)
        M := M.set! row rr
        for q in [0:ncol] do
          if q != row then
            let c := (M[q]!)[col]!
            if c != 0 then
              let rq := M[q]!
              M := M.set! q ((Array.range (nr + 1)).map fun j => rq[j]! - c * rr[j]!)
        pivCols := pivCols.push col
        row := row + 1
  let mut sol : Array Rat := Array.replicate nr 0
  for i in [0:pivCols.size] do
    sol := sol.set! (pivCols[i]!) ((M[i]!)[nr]!)
  return sol.toList

/-- The integer form `(c′, d)` of a rational vector: `d` the lcm of the denominators, `c′ = d c`. -/
def scaleQ (c : List Rat) : List Int × Int :=
  let d : Nat := c.foldl (fun acc q => Nat.lcm acc q.den) 1
  (c.map fun q => (q * (d : Rat)).num, (d : Int))

/-- `Σ_r (c_r, 0) · row_r`. -/
def combo (rows : List (Poly ZJ)) (c : List Int) : Poly ZJ :=
  Poly.sum ((rows.zip c).map fun rc => Poly.mulTerm zjC (rc.2, 0) [] rc.1)

/-- The saturation check for the variable `i`: `combo rows c′ = d · D · ξ_i` with `d ≠ 0`. -/
def satCheck (μ : List Int) (w : List Int) (i : Nat) : Bool :=
  let rows := macRows 3 7 (formsG μ w)
  let ms := monos 3 7
  let target := Poly.normalize zjC (Poly.mul zjC Dpoly (Poly.var zjC i))
  let A := rows.map fun r => (coeffVec ms r).map Prod.fst
  let t := (coeffVec ms target).map Prod.fst
  let cd := scaleQ (solveQ A t)
  cd.2 != 0 && Poly.eqv zjC (combo rows cd.1) (Poly.mulTerm zjC (cd.2, 0) [] target)

/-- The check of Remark 7.14 at masses `μ`, with `n` patterns of the first kind. -/
def rem714 (μ : List Int) (n : Nat) : Bool :=
  (patsG.filter (consApplies μ)).length == n &&
    patsG.all fun w =>
      if consApplies μ w then
        consL μ w < 4 && (formsG μ w).all (fun f => evalZJ (consPoint μ w) f.1 == (0, 0)) &&
          (List.range 3).all (satCheck μ w)
      else macCheck 3 8 pE sE (formsG μ w)

theorem rem714_1112 : rem714 [1, 1, 1, 2] 36 = true := by native_decide

theorem rem714_5_2_11_3 : rem714 [5, 2, 11, 3] 16 = true := by native_decide

theorem rem714_1234 : rem714 [1, 2, 3, 4] 28 = true := by native_decide

theorem rem714_2357 : rem714 [2, 3, 5, 7] 28 = true := by native_decide

end Lean6.Special.Comp.E4
