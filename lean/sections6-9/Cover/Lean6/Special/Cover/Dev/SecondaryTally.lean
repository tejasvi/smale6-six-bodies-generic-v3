import Lean6.Special.Cover.Comp
import Lean6.Special.Cover.Comp.Secondary
import L6Check.F5.Data

/-! Development: `secTally` over all stored cells, and Lemma 5.1 on torques in every cell outside Lemmas 9.2–9.7
(only to compare; writes `dev_td.txt`). -/

open Lean6.Special.Cover Lean6.Special.Cover.Secondary L6.F34

#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  match allCells L6F5.Data.n6 L6F5.Data.files with
  | none => IO.println "read failed"
  | some cs =>
    IO.println (repr (secTally cs))
    let t1 ← IO.monoMsNow
    IO.println s!"secTally {t1 - t0} ms"
    -- Lemma 5.1 on a torque in the cells without a test of Lemmas 9.2-9.7
    let rest := cs.toList.filter fun c => !((firstFlags c).take 6).any id
    let mut lines : Array String := #[]
    let mut n := 0
    for c in rest do
      match lpCtx c with
      | none => lines := lines.push s!"{c.cls} {c.idx} nolp"
      | some lp =>
        let td := tdWit lp
        if !td.isEmpty then
          n := n + 1
          lines := lines.push s!"{c.cls} {c.idx} {repr (td.map fun (J, l) => (J, reprStr l))}"
    IO.FS.writeFile "dev_td.txt" (String.intercalate "\n" lines.toList ++ "\n")
    let t2 ← IO.monoMsNow
    IO.println s!"cells without Lemmas 9.2-9.7: {rest.length}; with a torque with one least term: {n} ({t2 - t1} ms)"
