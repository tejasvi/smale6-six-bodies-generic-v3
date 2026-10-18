import L6F2S.Stored
import L6F2.Check

/-! Pilot: the specification search against the stored cells (counts, time). -/

namespace L6.Pilot

open L6.F2S

/-- Runs the specification search of class `k` and compares with the stored lines (both inclusions). -/
def specClass (k : Nat) : IO Unit := do
  let text ← IO.FS.readFile s!"data/cells/c{k}.jsonl"
  let D := L6.F2.diagOf k
  let t0 ← IO.monoMsNow
  let cells := search keepLP D
  let n := cells.length
  let t1 ← IO.monoMsNow
  match storedKeys text with
  | none => IO.println s!"class {k}: stored lines do not parse"
  | some ks =>
    let set : Std.HashSet _ := Std.HashSet.ofList ks
    let specKeys : Std.HashSet _ := Std.HashSet.ofList (cells.map (·.key))
    let miss := (cells.filter fun c => !set.contains c.key).length
    let extra := (ks.filter fun kk => !specKeys.contains kk).length
    IO.println s!"class {k}: spec cells {n}, stored {ks.length}, spec not stored {miss}, stored not spec {extra}, {t1 - t0} ms"

end L6.Pilot
