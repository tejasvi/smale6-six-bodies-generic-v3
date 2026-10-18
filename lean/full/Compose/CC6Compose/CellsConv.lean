import CC6Compose.CellsCore
import CC6Compose.Enum

/-!
# Bridge: the classes of the checks of Proposition 4.5

* `classes6_eq`, `diagOf_eq_ofF1`: the representatives of the checks of Proposition 4.5 are those of `L6F1.classes6`
  (proved from `L6F1.F1_main` by rewriting with the definition of `L6.F2.classes6`, without evaluating the reading of
  the class file); the diagram of class `k` is `Diag.ofF1` of the `k`-th representative.
* `germ_cell_stored_of`: with the conclusion of the checks of the specification search as a hypothesis, the key of
  the cell of the germ is the key of a stored line of its class.

The conversion of the trees of a germ and `cond_of_germ` are in `CellsCore.lean`.
-/

namespace CC6Compose

open CC6Full Finset

variable {m : Fin 6 → ℝ}

/-! ## The classes of the checks -/

set_option linter.auxLemma false in
/-- The reading of a class file as the array of the representatives of the checks of Proposition 4.5: the list
`L6.F2.classes6` is this function at `n6.json` (`classes6_eq_classesArray`). It is written with the matcher of the
definition of `L6.F2.classes6`, so that the equality is checked by unfolding both sides, without evaluating the
reading of the file. -/
def classesArray (s : String) : Array L6F1.Diagram :=
  L6.F2.classes6.match_1 (fun _ => Array L6F1.Diagram) (L6F1.parseFile s)
    (fun _ _ cls => (cls.map (·.1)).toArray) (fun _ => #[])

theorem classes6_eq_classesArray : L6.F2.classes6 = classesArray L6F1.n6json := rfl

theorem classesArray_of {s : String} {n t : ℕ} {cls : List (L6F1.Diagram × ℕ)}
    (h : L6F1.parseFile s = some (n, t, cls)) : classesArray s = (cls.map (·.1)).toArray := by
  unfold classesArray
  rw [h]

/-- **The representatives of the checks are those of `L6F1.classes6`.** -/
theorem classes6_eq : L6.F2.classes6 = (L6F1.classes6.map (·.1)).toArray :=
  classes6_eq_classesArray.trans (classesArray_of L6F1.F1_main.2.2.1)

theorem getElem!_map_fst (cls : List (L6F1.Diagram × ℕ)) {k : ℕ} (hk : k < cls.length) :
    (cls.map (·.1)).toArray[k]! = (cls[k]).1 := by
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp

/-- The diagram of class `k` of the checks of Proposition 4.5 is that of the `k`-th representative of
`L6F1.classes6`. -/
theorem diagOf_eq_ofF1 {k : ℕ} (hk : k < L6F1.classes6.length) :
    L6.F2.diagOf k = L6.F2.Diag.ofF1 (L6F1.classes6[k]).1 := by
  show L6.F2.Diag.ofF1 L6.F2.classes6[k]! = _
  rewrite [classes6_eq, getElem!_map_fst _ hk]
  rfl

/-- **The cell of a germ is stored** (Proposition 4.5), from the conclusion of the checks of the specification
search for all classes (`cells k`: the stored text of class `k`): for a germ with positive masses whose diagram is the
labelled diagram of a representative `x` of `L6F1.classes6` and with `ℓ(x) ≤ 0`, the class `k` of `x` has the diagram
`Diag.ofF1 x.1`, and for all trees with heights realizing the exponents of the germ, the key of the cell (the converted
trees and the argmin part of the line) is the key of a stored line of class `k`. -/
theorem germ_cell_stored_of (cells : ℕ → String)
    (hcells : ∀ k < 191, ∀ Xz Xw : L6.F2S.ExpTree, L6.F2S.Cond (L6.F2.diagOf k) Xz Xw →
      ∃ line ∈ ((cells k).splitOn "\n").filter (· != ""),
        L6.F2S.keyOfLine line = some (Xz.T.key, Xw.T.key, L6.F2S.argminString (L6.F2.diagOf k) Xz Xw))
    (hm : ∀ k, 0 < m k) (G : Germ 6 m) {x : L6F1.Diagram × ℕ} (hx : x ∈ L6F1.classes6)
    (hD : G.HasDiagram (toDiagram x.1)) (hell : G.ell ≤ 0) :
    ∃ k < 191, L6.F2.diagOf k = L6.F2.Diag.ofF1 x.1 ∧
      ∀ (Tz Tw : TreeShape 6) (htz htw : Finset (Pt 6) → ℚ), Tz.Realizes G.hz htz → Tw.Realizes G.hw htw →
        ∃ line ∈ ((cells k).splitOn "\n").filter (· != ""),
          L6.F2S.keyOfLine line = some ((toTS Tz).key, (toTS Tw).key,
            L6.F2S.argminString (L6.F2.diagOf k) (toExp Tz htz) (toExp Tw htw)) := by
  obtain ⟨-, -, -, -, hlen, -⟩ := L6F1.F1_main
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  have hk191 : k < 191 := hlen ▸ hk
  have hdiag := diagOf_eq_ofF1 hk
  refine ⟨k, hk191, hdiag, fun Tz Tw htz htw hRz hRw => ?_⟩
  have hc := cond_of_germ hm G hD hell hRz hRw
  rw [← hdiag] at hc
  exact hcells k hk191 _ _ hc

end CC6Compose
