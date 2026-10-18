import L6Common.LP

/-!
# Exact points of the listed cells

For a system kept by the search, the floating-point optimal basis of the dual program also gives a point: the
prices `π = c_B B⁻¹` of that basis are the heights and the slack `s` (the program dual to the dual is "maximize `s`").
`exactPoint` computes `π` from the basis by fraction-free integer elimination, with a common positive denominator
`D`, and `pointOk` checks in integer arithmetic that `(H / D, S / D)` satisfies every row and that `S > 0`. Applied
to the rows of a listed cell (with the row `ℓ(x) ≤ 0`), an accepted point shows that the cell is not empty and meets
`ℓ(x) ≤ 0`: the floating-point verdict "feasible" of the search is then certified for every listed cell.
-/

namespace L6.F2

/-- The integer cost of a column of the dual program. -/
def colCostInt (rows : Array Row) (col : LP.Col) : Int :=
  match col.row with
  | some i => let r := rows[i]!; if col.sign == 1 then r.hi.getD 0 else -(r.lo.getD 0)
  | none => if col.sign == 1 then 1 else 0

/-- The prices of the floating-point optimal basis, exactly: `(D, x)` with `π = x / D`, `D > 0`; `none` if the
program is not optimal with a positive value or the basis matrix is singular. -/
def exactPoint (rows : Array Row) (nv : Nat) : Option (Int × Array Int) := Id.run do
  let cols := LP.columns rows
  let K := cols.size
  let sol := LP.solve rows nv cols
  match sol.outcome with
  | .optimal v =>
    if v ≤ 1e-9 then return none
    let m := nv + 1
    let mut mat : Array (Array Int) := #[]
    for k in [0:m] do
      let bk := sol.basis[k]!
      let mut row : Array Int := #[]
      for i in [0:m] do
        let e : Int := if bk < K then LP.colEntryInt rows nv cols[bk]! i else (if bk - K == i then 1 else 0)
        row := row.push e
      row := row.push (if bk < K then colCostInt rows cols[bk]! else 0)
      mat := mat.push row
    match LP.bareissSolve m mat with
    | none => return none
    | some (det, x) => if det < 0 then return some (-det, x.map (- ·)) else return some (det, x)
  | _ => return none

/-- `(x₀ / D, …, x_{nv−1} / D)` and `s = x_{nv} / D > 0` satisfy every row (`D > 0`). -/
def pointOk (rows : Array Row) (nv : Nat) (D : Int) (x : Array Int) : Bool :=
  let S := x[nv]!
  decide (0 < D) && decide (0 < S) && rows.all fun r =>
    let v := (List.range nv).foldl (fun acc j => acc + r.a[j]! * x[j]!) 0 + r.c * S
    (match r.lo with | some lo => decide (lo * D ≤ v) | none => true) &&
    (match r.hi with | some hi => decide (v ≤ hi * D) | none => true)

/-- The system has an exact point with `s > 0`, found from the floating-point basis. -/
def leafCertified (rows : Array Row) (nv : Nat) : Bool :=
  match exactPoint rows nv with
  | some (D, x) => pointOk rows nv D x
  | none => false

end L6.F2
