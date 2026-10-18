import Lean6.Special.Cover.Comp.Basic

/-!
# Proposition 9.23: all cells with their diagrams

`allCells n6 files` reads the classes of `n6.json` and the stored cells (`files[c]`: the text of the cell file of class
`c`, the cell `k` on the line `k`, counted from `0`), and returns each cell with its class, its index and the diagram
of its class; `none` if a file or a class is not read.
-/

namespace Lean6.Special.Cover

open L6.F34
open Lean (Json)

/-- A stored cell with its class `cls`, its line `idx` in the cell file of the class and the class representative. -/
structure CCell where
  cls : Nat
  idx : Nat
  x : Cell
  d : Diagram

/-- All stored cells, in the order of the classes and of the lines. -/
def allCells (n6 : String) (files : List String) : Option (Array CCell) := do
  let j ← (Json.parse n6).toOption
  let mut out := #[]
  let mut c := 0
  for f in files do
    let cs ← readCells f
    if cs.size > 0 then
      let d ← Diagram.ofN6 j c
      let mut k := 0
      for x in cs do
        out := out.push ⟨c, k, x, d⟩
        k := k + 1
    c := c + 1
  return out

end Lean6.Special.Cover
