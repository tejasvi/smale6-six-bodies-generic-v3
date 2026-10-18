import Lean6.Special.Cover.Comp
import L6Check.F5.Data

/-!
# Proposition 9.23: the first group of (b)

The stored cells and the classes are those embedded in the companion project `lean6` (`L6F5.Data`: the files
`data/cells/c<N>.jsonl` and `data/f1/n6.json`, whose SHA-256 digests are checked there, `L6F5.cells_sha256` and
`L6F5.n6_sha256`). `tally` (`Lean6.Special.Cover.Comp.Tally`) applies the tests of the lemmas of the first group of
Proposition 9.23(b) to each cell.
-/

namespace Lean6.Special.Cover

/-- **Proposition 9.23, the first group of (b), and the cells of (a) excluded by Lemmas 9.2–9.7.** Of the 91,273
stored cells, 70,233 satisfy the hypotheses of one of Lemmas 9.2–9.7, and 90,943 those of one of the first group of
(b) (Lemmas 9.2–9.7, Corollary 9.10 with its class-level case, Lemma 9.11 (a), (b), Lemmas 9.12–9.15, Corollary 9.18
for a clique of three bodies); 90,919 without Corollary 9.18, which alone covers one cell of class 4, 22 of class 47
and one of class 53. Lemma 9.13 is the only test of the first group that holds in 16 cells and Lemma 9.14 in 58, and in
each of them the polynomial of the lemma (`H_W`, resp. `m_a² M_A⁴ − m_b² M_B⁴`) and its `g` are nonzero at
`m = (1, …, 6)`. The last field gives the number of cells for each test, in the order of `firstFlags`. -/
theorem prop_9_23_first :
    (allCells L6F5.Data.n6 L6F5.Data.files).map tally = some
      { cells := 91273, every := 70233, first := 90943, firstNoClique := 90919,
        cliqueOnly := [(4, 1), (47, 22), (53, 1)], w3Only := 16, eq2Only := 58,
        w3OnlyNonzero := true, eq2OnlyNonzero := true,
        perTest := [40084, 13293, 46289, 7722, 532, 2111, 50399, 86875, 77927, 79318, 54208, 2241, 2654, 2105,
          86842] } := by
  native_decide

end Lean6.Special.Cover
