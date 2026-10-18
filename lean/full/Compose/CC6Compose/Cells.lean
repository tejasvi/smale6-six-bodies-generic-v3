import CC6Compose.CellsConv
import L6Check.F2S.All

/-!
# Bridge: the cell of a germ is a stored cell of its class (Proposition 4.5)

For a germ for positive masses whose diagram is the labelled diagram `toDiagram x.1` of a representative `x` of
`L6F1.classes6` and with `ℓ(x) ≤ 0`, the cell of the germ (Definition 4.4: its trees and the argmin sets of the base
identities) is a cell stored by the certificate project for the class of `x`.

* `cond_of_germ` (`CellsConv.lean`): the converted trees with heights of the germ satisfy the conditions `Cond` of the
  specification search (Lemma 4.3 for the diagram and `ℓ ≤ 0`).
* `L6.F2S.Checks.f2s_cells_sound` (certificate project): for each of the 191 classes, every pair satisfying `Cond` has
  the key of a stored line of the class (the completeness of the specification search, `L6.F2S.search_complete`,
  and the 659 checks of the specification search against the stored cells, with the check of the insertion orders).
* `germ_cell_stored`: for all trees with heights realizing the exponents of the germ (Lemma 4.2), the key of the
  cell, `((toTS Tz).key, (toTS Tw).key, argminString (diagOf k) (toExp Tz htz) (toExp Tw htw))`, is the key of a
  stored line of class `k`, where `diagOf k = Diag.ofF1 x.1`. The trees of the line have the nodes `maskOf A` of the
  germ's trees (`nodes_of_key_eq`), the heights of the cell are those of the germ (`toExp_h_maskOf`), its exponents
  are those of the germ (`zExp_e_eq_order`, `wExp_e_eq_order`), and the exponents of the terms of the base
  identities of the specification are those of `Identity.base` at the germ (`bodyZ_filter_eq`, `bodyW_filter_eq`,
  `uExps_eq`, `potU_expos`, `iExps_eq`, `lagr_expos`).
* `germ_cell_stored_exists`: the same for the trees of Lemma 4.2 (`Germ.exists_tree_z`, `Germ.exists_tree_w`).

The checks behind `f2s_cells_sound` and `L6F1.F1_main` are evaluated by `native_decide` in the certificate project,
so these theorems depend on the auxiliary axioms of those evaluations in addition to `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace CC6Compose

open CC6Full

variable {m : Fin 6 → ℝ}

/-- **Proposition 4.5 for germs: the cell of a germ is stored.** For a germ for positive masses with diagram
`toDiagram x.1`, `x` a representative of `L6F1.classes6`, and `ℓ(x) ≤ 0`: the class `k` of `x` in the checks has the
diagram `Diag.ofF1 x.1`, and for all trees with heights realizing the exponents of the germ, the key of the cell of
the germ is the key of a stored line of class `k` (lines of `L6.F2.Checks.cellsOf k`, read by `L6.F2S.keyOfLine`). -/
theorem germ_cell_stored (hm : ∀ k, 0 < m k) (G : Germ 6 m) {x : L6F1.Diagram × ℕ} (hx : x ∈ L6F1.classes6)
    (hD : G.HasDiagram (toDiagram x.1)) (hell : G.ell ≤ 0) :
    ∃ k < 191, L6.F2.diagOf k = L6.F2.Diag.ofF1 x.1 ∧
      ∀ (Tz Tw : TreeShape 6) (htz htw : Finset (Pt 6) → ℚ), Tz.Realizes G.hz htz → Tw.Realizes G.hw htw →
        ∃ line ∈ ((L6.F2.Checks.cellsOf k).splitOn "\n").filter (· != ""),
          L6.F2S.keyOfLine line = some ((toTS Tz).key, (toTS Tw).key,
            L6.F2S.argminString (L6.F2.diagOf k) (toExp Tz htz) (toExp Tw htw)) :=
  germ_cell_stored_of L6.F2.Checks.cellsOf L6.F2S.Checks.f2s_cells_sound hm G hx hD hell

/-- **Proposition 4.5 for germs**, with the trees of Lemma 4.2: some trees with heights realizing the exponents of
the germ give the key of a stored line of the class of `x`, and the converted trees satisfy `Cond`. -/
theorem germ_cell_stored_exists (hm : ∀ k, 0 < m k) (G : Germ 6 m) {x : L6F1.Diagram × ℕ}
    (hx : x ∈ L6F1.classes6) (hD : G.HasDiagram (toDiagram x.1)) (hell : G.ell ≤ 0) :
    ∃ k < 191, L6.F2.diagOf k = L6.F2.Diag.ofF1 x.1 ∧
      ∃ (Tz Tw : TreeShape 6) (htz htw : Finset (Pt 6) → ℚ), Tz.Realizes G.hz htz ∧ Tw.Realizes G.hw htw ∧
        L6.F2S.Cond (L6.F2.diagOf k) (toExp Tz htz) (toExp Tw htw) ∧
        ∃ line ∈ ((L6.F2.Checks.cellsOf k).splitOn "\n").filter (· != ""),
          L6.F2S.keyOfLine line = some ((toTS Tz).key, (toTS Tw).key,
            L6.F2S.argminString (L6.F2.diagOf k) (toExp Tz htz) (toExp Tw htw)) := by
  obtain ⟨k, hk, hdiag, hall⟩ := germ_cell_stored hm G hx hD hell
  obtain ⟨Tz, htz, hRz⟩ := G.exists_tree_z (by norm_num)
  obtain ⟨Tw, htw, hRw⟩ := G.exists_tree_w (by norm_num)
  have hc := cond_of_germ hm G hD hell hRz hRw
  rw [← hdiag] at hc
  exact ⟨k, hk, hdiag, Tz, Tw, htz, htw, hRz, hRw, hc, hall Tz Tw htz htw hRz hRw⟩

end CC6Compose
