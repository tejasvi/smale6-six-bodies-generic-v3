import Lean6.Special.Cover.Comp.Generic
import Lean6.Special.Cover.Comp.Driver
import L6Check.F5.Data

/-! Development: the witnesses of the generic lemmas in every cell, one JSON object per line (`dev_generic.jsonl`). -/

open Lean6.Special.Cover Lean6.Special.Cover.Generic L6.F34

/-- A list of numbers as JSON. -/
def jl (l : List Nat) : String := "[" ++ ",".intercalate (l.map toString) ++ "]"

/-- A colour as JSON. -/
def jc (c : Bool) : String := if c then "\"z\"" else "\"w\""

/-- A list of JSON values. -/
def ja (l : List String) : String := "[" ++ ",".intercalate l ++ "]"

#eval show IO Unit from do
  match allCells L6F5.Data.n6 L6F5.Data.files with
  | none => IO.println "read failed"
  | some cs =>
    let lines := cs.toList.map fun cc =>
      let x := cc.x
      let cen (w : List (Bool × List Nat × Nat)) : String :=
        ja (w.map fun (c, T, s) => "[" ++ jc c ++ "," ++ jl T ++ "," ++ toString s ++ "]")
      "{\"c\":" ++ toString cc.cls ++ ",\"i\":" ++ toString cc.idx ++
        ",\"E\":" ++ ja ((eWit cc.d).map jl) ++
        ",\"E1\":" ++ ja ((e1Wit x).map jl) ++
        ",\"Ra\":" ++ cen (raWit x) ++ ",\"Rb\":" ++ cen (rbWit x) ++ ",\"Rbp\":" ++ cen (rbProgWit x) ++
        ",\"R1p\":" ++ cen (r1ProgWit x) ++
        ",\"R6\":" ++ ja ((r6Wit x).map fun (c, T, s, a) =>
          "[" ++ jc c ++ "," ++ jl T ++ "," ++ toString s ++ "," ++ toString a ++ "]") ++
        ",\"Q\":" ++ ja ((qWit x).map fun (c, s, K) => "[" ++ jc c ++ "," ++ toString s ++ "," ++ jl K ++ "]") ++
        ",\"CL3\":" ++ ja ((clique3Wit x cc.d).map jl) ++ "}"
    IO.FS.writeFile "dev_generic.jsonl" (String.intercalate "\n" lines ++ "\n")
    IO.println s!"{cs.size} cells written"
    IO.println s!"counts E, E1, Ra, Rb, R6, Q, clique3, any: {genericCounts cs}"
    IO.println s!"E classes (of 191): {eClasses L6F5.Data.n6 191}"
    IO.println s!"E consistent: {eConsistent cs}"
