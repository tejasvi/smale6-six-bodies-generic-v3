import Lean6.Special.Cover.Comp
import Lean6.Special.Cover.Check.Links
import L6Check.F5.Data

/-! Development: `Templates.broadCounts` over all stored cells. -/

open Lean6.Special.Cover

#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  match allCells L6F5.Data.n6 L6F5.Data.files with
  | none => IO.println "read failed"
  | some cs =>
    IO.println (repr (Templates.broadCounts coreLinks cs))
    IO.println s!"{(← IO.monoMsNow) - t0} ms"
