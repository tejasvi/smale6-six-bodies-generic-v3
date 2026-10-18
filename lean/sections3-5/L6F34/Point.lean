import L6Common.LP

/-!
# F4: a floating-point interior point of a cell (proposer only)

The argmin set of a secondary identity on a cell is guessed at a point of the cell, as the engine does
(`tsec_exact.constant_argmin_exact`), and then certified by exact certificates; the point itself is not trusted.
At an optimal basis of the dual program of `L6.LP` (maximize `s`), the simplex multipliers `π = c_B B⁻¹` are an
optimal solution `(h, s)` of the primal program, so for an optimum `s > 0` they are a point of the relatively open
cell. They are recovered here from the final basis by Gaussian elimination with partial pivoting on `Bᵀ π = c_B`.
-/

namespace L6.F34

open L6.LP

/-- Solves the dense `m × m` float system `A x = b` (row-major `A`) by Gaussian elimination with partial pivoting. -/
def gaussSolve (m : Nat) (A0 : Array Float) (b0 : Array Float) : Option (Array Float) := Id.run do
  let mut A := A0
  let mut b := b0
  for k in [0:m] do
    let mut p := k
    let mut best := Float.abs A[k * m + k]!
    for i in [k+1:m] do
      let v := Float.abs A[i * m + k]!
      if v > best then p := i; best := v
    if best < 1e-12 then return none
    if p != k then
      for j in [0:m] do
        let t := A[k * m + j]!
        A := (A.set! (k * m + j) A[p * m + j]!).set! (p * m + j) t
      let t := b[k]!
      b := (b.set! k b[p]!).set! p t
    let piv := A[k * m + k]!
    for i in [k+1:m] do
      let f := A[i * m + k]! / piv
      if f != 0.0 then
        for j in [k:m] do
          A := A.set! (i * m + j) (A[i * m + j]! - f * A[k * m + j]!)
        b := b.set! i (b[i]! - f * b[k]!)
  let mut x := Array.replicate m 0.0
  let mut i := m
  while i > 0 do
    i := i - 1
    let mut s := b[i]!
    for j in [i+1:m] do
      s := s - A[i * m + j]! * x[j]!
    x := x.set! i (s / A[i * m + i]!)
  return some x

/-- A point `(h, s)` (length `n + 1`, `s` last) of the system with `s` maximal, if the maximum exceeds `1e-9`. -/
def interiorPoint (rows : Array Row) (n : Nat) : Option (Array Float) := Id.run do
  let cols := columns rows
  let K := cols.size
  let sol := solve rows n cols
  match sol.outcome with
  | .optimal v =>
    if v ≤ 1e-9 then return none
    let m := n + 1
    -- Bᵀ π = c_B: row k of Bᵀ is basic column k
    let mut A : Array Float := Array.replicate (m * m) 0.0
    let mut cb : Array Float := Array.replicate m 0.0
    for k in [0:m] do
      let bk := sol.basis[k]!
      for l in [0:m] do
        let e : Float := if bk < K then colEntry rows n cols[bk]! l else (if bk - K == l then 1.0 else 0.0)
        A := A.set! (k * m + l) e
      cb := cb.set! k (if bk < K then colCost rows cols[bk]! else 0.0)
    return gaussSolve m A cb
  | _ => return none

end L6.F34
