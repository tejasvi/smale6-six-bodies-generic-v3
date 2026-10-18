import Lean6.Special.Cover.Comp
import Lean6.Special.Cover.Check.Links
import L6Check.F5.Data

/-!
# Proposition 9.23: the counts

The stored cells and the classes embedded in the companion project `lean6` (`L6F5.Data`, digests checked there) and
its core links (`coreLinks`, from `L6Check.F34.Data`). `coverTally` (`Lean6.Special.Cover.Comp.Cover`) applies the
tests of all the lemmas of Proposition 9.23 to each cell.
-/

namespace Lean6.Special.Cover

/-- **Proposition 9.23.** Of the 91,273 stored cells:
(a) 70,406 are excluded at every positive mass: 70,233 by Lemmas 9.2–9.7, 171 by Lemma 9.20 and one by Lemma 9.21
(cores classified `P4`, resp. `LIN` with a minor of one sign, in the cells where the notes' program classified the core
and none of Lemmas 9.2–9.7 holds), and one by Lemma 5.1 applied to the torque `T_{0,3,4}` (the cell 0 of class 15);
(b) 90,943 satisfy the hypotheses of one of the first group (`prop_9_23_first`); 287 others satisfy those of Lemma
9.11(c) (1 cell), Lemma 9.22 (1), Lemma 9.20 (169) or Lemma 9.21 (116), counted by the first lemma of this list that
holds; and the remaining 43 cells are 1 of class 31, 10 of class 124, 9 of class 127, 2 of class 132, 1 of class 133,
11 of class 143 and 9 of class 147 (the diagrams 89, 64, 88, 93, 98, 66 and 94: `L6F5.F5_cc` in `lean6`). -/
theorem prop_9_23 :
    (allCells L6F5.Data.n6 L6F5.Data.files).map (coverTally coreLinks) = some
      { cells := 91273, aTotal := 70406, aEvery := 70233, aP4 := 171, aLinAll := 1, aTD := 1,
        first := 90943, second := 287, secondRc := 1, secondTq := 1, secondP4 := 169, secondLin := 116,
        remaining := [(31, 1), (124, 10), (127, 9), (132, 2), (133, 1), (143, 11), (147, 9)] } := by
  native_decide

/-- **The templates without the programs' order** (not part of Proposition 9.23). Over the 21,040 cells in which none
of Lemmas 9.2–9.7 holds (20,226 of them core cells), the templates of the cores give Lemma 9.20 in 401 cells, Lemma
9.21 with a minor of one sign in 2,742, Lemma 9.21 otherwise in 2,105, the binary template in none and no template in
14,978; every core identity's argmin set is certified. So Lemmas 9.20 and 9.21 exclude at every positive mass more
cells than the 172 that Proposition 9.23(a) counts, which are those that the notes' program reached. -/
theorem prop_9_23_broad :
    (allCells L6F5.Data.n6 L6F5.Data.files).map (Templates.broadCounts coreLinks) =
      some [21040, 20226, 401, 2742, 2105, 0, 14978, 0] := by
  native_decide

end Lean6.Special.Cover
