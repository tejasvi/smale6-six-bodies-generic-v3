import Lean6.Special.Cover.Comp
import Lean6.Special.Cover.Comp.Templates
import L6Check.F5.Data
import L6Check.F34.Data.C0
import L6Check.F34.Data.C3
import L6Check.F34.Data.C4
import L6Check.F34.Data.C8
import L6Check.F34.Data.C10
import L6Check.F34.Data.C12
import L6Check.F34.Data.C13
import L6Check.F34.Data.C14
import L6Check.F34.Data.C15
import L6Check.F34.Data.C16
import L6Check.F34.Data.C20
import L6Check.F34.Data.C22
import L6Check.F34.Data.C23
import L6Check.F34.Data.C24
import L6Check.F34.Data.C25
import L6Check.F34.Data.C28
import L6Check.F34.Data.C29
import L6Check.F34.Data.C30
import L6Check.F34.Data.C31
import L6Check.F34.Data.C34
import L6Check.F34.Data.C35
import L6Check.F34.Data.C40
import L6Check.F34.Data.C42
import L6Check.F34.Data.C44
import L6Check.F34.Data.C47
import L6Check.F34.Data.C53
import L6Check.F34.Data.C56
import L6Check.F34.Data.C57
import L6Check.F34.Data.C58
import L6Check.F34.Data.C62
import L6Check.F34.Data.C63
import L6Check.F34.Data.C64
import L6Check.F34.Data.C65
import L6Check.F34.Data.C66
import L6Check.F34.Data.C67
import L6Check.F34.Data.C69
import L6Check.F34.Data.C84
import L6Check.F34.Data.C110
import L6Check.F34.Data.C116
import L6Check.F34.Data.C117
import L6Check.F34.Data.C119
import L6Check.F34.Data.C120
import L6Check.F34.Data.C121
import L6Check.F34.Data.C122
import L6Check.F34.Data.C123
import L6Check.F34.Data.C124
import L6Check.F34.Data.C126
import L6Check.F34.Data.C128
import L6Check.F34.Data.C129
import L6Check.F34.Data.C130
import L6Check.F34.Data.C132
import L6Check.F34.Data.C133
import L6Check.F34.Data.C142
import L6Check.F34.Data.C143
import L6Check.F34.Data.C146
import L6Check.F34.Data.C147
import L6Check.F34.Data.C148
import L6Check.F34.Data.C149
import L6Check.F34.Data.C150
import L6Check.F34.Data.C167
import L6Check.F34.Data.C169
import L6Check.F34.Data.C170
import L6Check.F34.Data.C171
import L6Check.F34.Data.C172
import L6Check.F34.Data.C173
import L6Check.F34.Data.C183

/-! Development: the templates of Lemmas 9.20 and 9.21 on the cores (`dev_templates.txt`: the notes' cell-level tests
on every cell, and the template of every cell outside the first group or in the notes' domain), and their counts. -/

open Lean6.Special.Cover Lean6.Special.Cover.Templates Lean6.Special.Cover.MP L6.F34

/-- The link files of the classes with core cells. -/
def devLinks : List (Nat × String) := [(0, L6.F34.Data.links_0), (3, L6.F34.Data.links_3), (4, L6.F34.Data.links_4), (8, L6.F34.Data.links_8), (10, L6.F34.Data.links_10), (12, L6.F34.Data.links_12), (13, L6.F34.Data.links_13), (14, L6.F34.Data.links_14), (15, L6.F34.Data.links_15), (16, L6.F34.Data.links_16), (20, L6.F34.Data.links_20), (22, L6.F34.Data.links_22), (23, L6.F34.Data.links_23), (24, L6.F34.Data.links_24), (25, L6.F34.Data.links_25), (28, L6.F34.Data.links_28), (29, L6.F34.Data.links_29), (30, L6.F34.Data.links_30), (31, L6.F34.Data.links_31), (34, L6.F34.Data.links_34), (35, L6.F34.Data.links_35), (40, L6.F34.Data.links_40), (42, L6.F34.Data.links_42), (44, L6.F34.Data.links_44), (47, L6.F34.Data.links_47), (53, L6.F34.Data.links_53), (56, L6.F34.Data.links_56), (57, L6.F34.Data.links_57), (58, L6.F34.Data.links_58), (62, L6.F34.Data.links_62), (63, L6.F34.Data.links_63), (64, L6.F34.Data.links_64), (65, L6.F34.Data.links_65), (66, L6.F34.Data.links_66), (67, L6.F34.Data.links_67), (69, L6.F34.Data.links_69), (84, L6.F34.Data.links_84), (110, L6.F34.Data.links_110), (116, L6.F34.Data.links_116), (117, L6.F34.Data.links_117), (119, L6.F34.Data.links_119), (120, L6.F34.Data.links_120), (121, L6.F34.Data.links_121), (122, L6.F34.Data.links_122), (123, L6.F34.Data.links_123), (124, L6.F34.Data.links_124), (126, L6.F34.Data.links_126), (128, L6.F34.Data.links_128), (129, L6.F34.Data.links_129), (130, L6.F34.Data.links_130), (132, L6.F34.Data.links_132), (133, L6.F34.Data.links_133), (142, L6.F34.Data.links_142), (143, L6.F34.Data.links_143), (146, L6.F34.Data.links_146), (147, L6.F34.Data.links_147), (148, L6.F34.Data.links_148), (149, L6.F34.Data.links_149), (150, L6.F34.Data.links_150), (167, L6.F34.Data.links_167), (169, L6.F34.Data.links_169), (170, L6.F34.Data.links_170), (171, L6.F34.Data.links_171), (172, L6.F34.Data.links_172), (173, L6.F34.Data.links_173), (183, L6.F34.Data.links_183)]

def tmplStr : Option Tmpl → String
  | none => "uncert"
  | some .unmatched => "none"
  | some .B => "B"
  | some (.lin ms) => (if ms.any oneSign then "LIN-all " else "LIN-generic ") ++ String.intercalate " ; " (ms.map MPoly.toStr)
  | some (.p4 c s a b) => s!"P4 {if c then "z" else "w"} {s} {a} {b}"

#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  match allCells L6F5.Data.n6 L6F5.Data.files with
  | none => IO.println "read failed"
  | some cs =>
    let tbl := linkTable devLinks
    let mut out : Array String := #[]
    for c in cs do
      let fl := [Generic.lemE c.d, Every.lemT c.x, Every.lemP c.x c.d, Every.lemCProg c.x, Bn c.x c.d, E1n c.x, R1n c.x,
        R5n c.x, Generic.lemR6 c.x, Generic.lemQ c.x]
      out := out.push (s!"N {c.cls} {c.idx} " ++ String.intercalate " " (fl.map fun b => if b then "1" else "0"))
      let f := firstFlags c
      let outside := !(f.any id)
      let core := tbl.contains (c.cls, c.idx)
      let dom := core && !(fl.any id)
      if outside || dom then
        let b0kl := f.getD 3 false || f.getD 4 false || f.getD 5 false
        let tm := if core then tmplStr (cellTmpl tbl c) else "nolink"
        out := out.push s!"T {c.cls} {c.idx} {if outside then 1 else 0} {if dom then 1 else 0} {if b0kl then 1 else 0} {tm}"
    IO.FS.writeFile "dev_templates.txt" (String.intercalate "\n" out.toList ++ "\n")
    let t1 ← IO.monoMsNow
    IO.println s!"dump {t1 - t0} ms"
    IO.println (repr (ttally devLinks cs))
    IO.println s!"tally {(← IO.monoMsNow) - t1} ms"
