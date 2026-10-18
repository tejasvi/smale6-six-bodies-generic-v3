import L6F2S.SearchL
import L6F2.Check

/-! Pilot: the search with lists of rows and structured argmin sets against the specification search (development). -/

namespace L6.Pilot

open L6.F2S

/-- The decision on a linear program given as a list of rows. -/
def keepLPL (rows : List Row) (nv : Nat) : Bool := keepLP rows.toArray nv

/-- Compares `searchL` (rendered) with `search`, cell by cell, for class `k`. -/
def searchLClass (k : Nat) : IO Unit := do
  let D := L6.F2.diagOf k
  let t0 ← IO.monoMsNow
  let a := search keepLP D
  let t1 ← IO.monoMsNow
  let b := searchL keepLPL D (order D)
  let t2 ← IO.monoMsNow
  let render (c : SCellL) : String :=
    match idents D ⟨c.tz, c.tw⟩ with
    | some ids => renderIdx (ids.map fun id => (id.name, id.labels, id.forced)) c.argmin
    | none => "?"
  let same := a.length == b.length && (a.zip b).all fun (x, y) =>
    x.tz == y.tz && x.tw == y.tw && x.argmin == render y
  IO.println s!"class {k}: search {a.length} cells ({t1 - t0} ms), searchL {b.length} cells ({t2 - t1} ms), identical after rendering: {same}"

end L6.Pilot
