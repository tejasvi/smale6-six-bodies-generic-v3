import Lean6.Special.Cover.Comp.Lines
import Lean6.Special.Cover.Comp.Driver
import L6Check.F5.Data

/-! Development: Lemmas 9.13 and 9.14 on all cells. `dev_lines.txt`: per cell the flags W3 (paper), W3 (notes),
W3 (broad Lemma 9.1 sets), EQ2 (paper, dimension at most 1), EQ2 (dimension 1), EQ2 (notes), EQ2 (broad);
`dev_lines_inst.txt`: every instance with the combinatorial hypotheses and its linear algebra. -/

open Lean6.Special.Cover Lean6.Special.Cover.Lines Lean6.Special.Cover.MP L6.F34

#eval show IO Unit from do
  match allCells L6F5.Data.n6 L6F5.Data.files with
  | none => IO.println "read failed"
  | some cs =>
    let mut flags : Array String := #[]
    let mut inst : Array String := #[]
    for cc in cs do
      let x := cc.x
      let w := w3Insts x
      let q := eq2Insts x
      let wb := w3InstsWith sSetsBroad x
      let qb := eq2InstsWith sSetsBroad x
      let f := [w.any (·.dimP == 1), w.any (·.notesOK), wb.any (·.dimP == 1), q.any (·.dimP ≤ 1), q.any (·.dimP == 1),
        q.any (·.notesOK), qb.any (·.dimP ≤ 1)]
      flags := flags.push (s!"{cc.cls} {cc.idx} " ++ String.intercalate " " (f.map fun b => if b then "1" else "0"))
      for i in w do
        inst := inst.push (s!"{cc.cls} {cc.idx} W3 {if i.c then "z" else "w"} {i.tri} v={i.v} bal={i.bal} " ++
          s!"nrel={i.nrel} dimP={i.dimP} notes={i.notesOK} e=[{String.intercalate ", " (i.e.map MPoly.toStr)}] " ++
          s!"g0={i.g.eval m0} hw0={hW0 i}")
      for i in q do
        inst := inst.push (s!"{cc.cls} {cc.idx} EQ2 {if i.c then "z" else "w"} s={i.s} a={i.a} b={i.b} v={i.v} " ++
          s!"nrel={i.nrel} dimP={i.dimP} notes={i.notesOK} MA={i.MA.toStr} MB={i.MB.toStr} g0={i.g.eval m0} " ++
          s!"val0={eq2Val0 i}")
    IO.FS.writeFile "dev_lines.txt" (String.intercalate "\n" flags.toList ++ "\n")
    IO.FS.writeFile "dev_lines_inst.txt" (String.intercalate "\n" inst.toList ++ "\n")
    IO.println s!"{cs.size} cells, {inst.size} instances"

/-! The counts of the paper's readings and their time (the predicates alone). -/

#eval show IO Unit from do
  match allCells L6F5.Data.n6 L6F5.Data.files with
  | none => IO.println "read failed"
  | some cs =>
    let t0 ← IO.monoMsNow
    let nW := (cs.filter fun cc => lemW3 cc.x).size
    let t1 ← IO.monoMsNow
    let nE := (cs.filter fun cc => lemEQ2 cc.x).size
    let t2 ← IO.monoMsNow
    let nWn := (cs.filter fun cc => lemW3Notes cc.x).size
    let nEl := (cs.filter fun cc => lemEQ2Line cc.x).size
    let nEn := (cs.filter fun cc => lemEQ2Notes cc.x).size
    IO.println s!"lemW3 {nW} cells ({t1 - t0} ms), lemEQ2 {nE} cells ({t2 - t1} ms); notes W3 {nWn}, EQ2 line {nEl}, EQ2 notes {nEn}"
    let zW := cs.filter fun cc => lemW3 cc.x && !w3NonzeroAtM0 cc.x
    let zE := cs.filter fun cc => lemEQ2 cc.x && !eq2NonzeroAtM0 cc.x
    IO.println s!"cells with W3 where some instance has g(m0) = 0 or H_W(m0) = 0: {zW.size} {(zW.toList.take 10).map fun cc => (cc.cls, cc.idx)}"
    IO.println s!"cells with EQ2 where some instance has g(m0) = 0 or value 0: {zE.size} {(zE.toList.take 10).map fun cc => (cc.cls, cc.idx)}"
