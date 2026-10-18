import Lean6.Special.Cover.Comp
import Lean6.Special.Cover.Comp.Secondary
import L6Check.F5.Data

/-! Development: Lemmas 9.11(c), 9.22 and Lemma 5.1 on a torque in the cells outside the first group of Proposition
9.23(b), and Lemma 5.1 on the torque of the cell 0 of class 15; writes `dev_secondary.txt`. -/

open Lean6.Special.Cover Lean6.Special.Cover.Secondary L6.F34

#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  match allCells L6F5.Data.n6 L6F5.Data.files with
  | none => IO.println "read failed"
  | some cs =>
    let out := outsideFirst cs
    let t1 ← IO.monoMsNow
    IO.println s!"outside the first group: {out.length} cells ({t1 - t0} ms); by class {classCounts out}"
    let mut lines : Array String := #[]
    let mut nrc := 0
    let mut nrcp := 0
    let mut ntq := 0
    let mut ntqp := 0
    let mut ntd := 0
    let mut nolp := 0
    for c in out do
      match lpCtx c with
      | none =>
        nolp := nolp + 1
        lines := lines.push s!"{c.cls} {c.idx} nolp"
      | some lp =>
        let rc := rcWit c lp
        let rcp := rcProgWit c lp
        let tq := tqWit c lp
        let tqp := tqProgWit c lp
        let td := tdWit lp
        if !rc.isEmpty then nrc := nrc + 1
        if !rcp.isEmpty then nrcp := nrcp + 1
        if !tq.isEmpty then ntq := ntq + 1
        if !tqp.isEmpty then ntqp := ntqp + 1
        if !td.isEmpty then ntd := ntd + 1
        lines := lines.push (s!"{c.cls} {c.idx} rc={repr rc} rcp={repr rcp} tq={repr tq} tqp={repr tqp} " ++
          s!"td={repr (td.map fun (J, l) => (J, reprStr l))}")
    let t2 ← IO.monoMsNow
    IO.FS.writeFile "dev_secondary.txt" (String.intercalate "\n" lines.toList ++ "\n")
    IO.println s!"rc {nrc}, rcProg {nrcp}, tq {ntq}, tqProg {ntqp}, td {ntd}, no LP context {nolp} ({t2 - t1} ms)"
    -- Lemma 5.1 on the torque T_{0,3,4} of the cell 0 of class 15 (the supplement's TD)
    for c in cs do
      if c.cls == 15 && c.idx == 0 then
        match lpCtx c with
        | none => IO.println "15/0: no LP context"
        | some lp =>
          IO.println s!"15/0: tdAt [0,3,4] T2 0 2 = {tdAt lp [0, 3, 4] (.T2 0 2)}; first flags {firstFlags c}"
          IO.println s!"15/0: tdWit {repr ((tdWit lp).map fun (J, l) => (J, reprStr l))}"
    let t3 ← IO.monoMsNow
    IO.println s!"total {t3 - t0} ms"
