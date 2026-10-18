import Lean6.Special.Cover.Comp.Templates
import Lean6.Special.Cover.Comp.Secondary

/-!
# Proposition 9.23: all counts

`coverTally links cs` combines the tests of the first group of (b) (`firstFlags`), the templates of Lemmas 9.20 and
9.21 on the cores (`Templates`), Lemmas 9.11(c) and 9.22 (`Secondary.secondFlags`) and Lemma 5.1 on the torque
`T_{0,3,4}` in the cell 0 of class 15 (`Secondary.tdCell`), and counts:

* (a): the cells with one of Lemmas 9.2–9.7; those, among the cells where the notes' program classified the core and
  none of Lemmas 9.2–9.7 holds, whose core is `P4`, resp. `LIN` with a minor of one sign; the cell of Lemma 5.1 on a
  torque if none of Lemmas 9.2–9.7 holds there; and the number of cells in the union;
* (b): the cells of the first group; the cells outside it with Lemma 9.11(c), else Lemma 9.22, else a core `P4`, else
  a core `LIN` (the order of the paper's list), and their number; the remaining cells by class.
-/

namespace Lean6.Special.Cover

open L6.F34

/-- The counts of Proposition 9.23. -/
structure CoverTally where
  /-- the stored cells -/
  cells : Nat
  /-- (a): the cells excluded at every positive mass, the union of the next four sets -/
  aTotal : Nat
  /-- (a): the cells with one of Lemmas 9.2–9.7 -/
  aEvery : Nat
  /-- (a): the cells with a core `P4`, resp. `LIN` with a minor of one sign, as counted by the notes' program -/
  aP4 : Nat
  aLinAll : Nat
  /-- (a): the cell of Lemma 5.1 on a torque -/
  aTD : Nat
  /-- (b): the cells of the first group -/
  first : Nat
  /-- (b): the cells outside the first group with one of Lemmas 9.11(c), 9.22, 9.20, 9.21 -/
  second : Nat
  /-- (b): among them, by the first lemma of this list that holds -/
  secondRc : Nat
  secondTq : Nat
  secondP4 : Nat
  secondLin : Nat
  /-- (b): the remaining cells, by class -/
  remaining : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- **The counts of Proposition 9.23** over the cells `cs`, with the core links `links` (`(class, text)`). -/
def coverTally (links : List (Nat × String)) (cs : Array CCell) : CoverTally :=
  let tbl := Templates.linkTable links
  let rs := cs.toList.map fun c =>
    let f := firstFlags c
    let every := (f.take 6).any id
    let first := f.any id
    let b0kl := f.getD 3 false || f.getD 4 false || f.getD 5 false
    let dom := tbl.contains (c.cls, c.idx) && !Templates.notesLemma c
    let tm := if !first || dom then Templates.cellTmpl tbl c else none
    let p4 := match tm with | some (.p4 ..) => true | _ => false
    let lin := match tm with | some (.lin _) => true | _ => false
    let linAll := match tm with | some (.lin ms) => ms.any Templates.oneSign | _ => false
    let sf := if first then (false, false) else Secondary.secondFlags c
    let aP4 := dom && !b0kl && p4
    let aLinAll := dom && !b0kl && linAll
    let aTD := !every && c.cls == 15 && c.idx == 0 && Secondary.tdCell c [0, 3, 4] (.T2 0 2)
    let rc := !first && sf.1
    let tq := !first && !rc && sf.2
    let sp4 := !first && !rc && !tq && p4
    let slin := !first && !rc && !tq && !sp4 && lin
    (c.cls, [every, aP4, aLinAll, aTD, every || aP4 || aLinAll || aTD, first, rc, tq, sp4, slin,
      rc || tq || sp4 || slin, !first && !(rc || tq || sp4 || slin)])
  let cnt (i : Nat) : Nat := (rs.filter fun r => r.2.getD i false).length
  { cells := rs.length
    aTotal := cnt 4, aEvery := cnt 0, aP4 := cnt 1, aLinAll := cnt 2, aTD := cnt 3
    first := cnt 5, second := cnt 10, secondRc := cnt 6, secondTq := cnt 7, secondP4 := cnt 8, secondLin := cnt 9
    remaining := byClass ((rs.filter fun r => r.2.getD 11 false).map (·.1)) }

end Lean6.Special.Cover
