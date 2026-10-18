import Lean6.Special.Cover.Comp
import Lean6.Special.Cover.Comp.Every
import L6Check.F5.Data

/-! Development: the lemmas 9.2–9.7 on every cell (`dev_every.txt`: `class cell names`, with `C5` for Lemma 9.4 with
`|J| ≤ 5`), for the comparison with the classifications of the supplement. -/

open Lean6.Special.Cover Lean6.Special.Cover.Every L6.F34

#eval show IO Unit from do
  match allCells L6F5.Data.n6 L6F5.Data.files with
  | none => IO.println "read failed"
  | some cs =>
    let lines := cs.toList.map fun c =>
      let names := everyNames c.x c.d ++ (if lemCProg c.x then ["C5"] else [])
      s!"{c.cls} {c.idx}" ++ String.join (names.map (" " ++ ·))
    IO.FS.writeFile "dev_every.txt" (String.intercalate "\n" lines ++ "\n")
    IO.println s!"{cs.size} cells"
