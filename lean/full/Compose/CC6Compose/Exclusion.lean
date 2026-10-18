import CC6Compose.ExclusionClasses
import CC6Compose.ExclusionPoly

/-!
# Bridge: the exclusion of the classes without open cells (Proposition 5.3 for germs)

For a germ for positive masses whose diagram is `toDiagram x.1` for a representative `x` of class `k` of
`L6F1.classes6`, with `ℓ ≤ 0`, the cell of the germ is a stored cell of class `k` (Proposition 4.5,
`L6.F2S.Checks.f2s_cells_sound`, `cond_of_germ`), and the checks of Proposition 5.3 on the cells of the
specification search (`ClassClaim`, `classClaim`) give, unless the line is one of the 43 open cells:

* a single term (Lemma 5.1): impossible at the germ (`single_false`); or
* a core (Lemma 5.2) with a certificate of the class: its polynomial `certPoly c ∈ ℤ[m₀, …, m₅]`, nonzero, vanishes at
  the masses (`core_vanish`, `certPoly_vanish`, `certPoly_ne_zero`).

So every class without open cells is excluded at generic masses: **`diagExcluded_of_not_open`**,
`CC6Full.DiagExcluded (toDiagram (L6F1.classes6[k]).1)` for `k ∉ L6.F34S.openClasses` (the open cells lie in the
classes 31, 124, 127, 132, 133, 143, 147), with the finitely many polynomials `textPoly` of the certificate texts of
the class.

* `germ_line_index`: the stored line of the cell of the germ has an index `idx < ncells` in the file of its class;
  `germ_rows_strict`: the rows of the cell of the specification search with the argmin part of the germ hold strictly
  at the heights of the germ.
* `germ_claimIn`: `ClaimIn certs` at the converted trees with heights of the germ, for the certificate texts of the
  class.
* `germ_excluded`: some certificate text of the class has a polynomial vanishing at the masses.
* `diagExcluded_of_classClaim`, `diagExcluded_of_not_open`, `diagExcluded_of_mem`.

The checks used are evaluated by `native_decide` in the certificate project (the chunk theorems
`L6.F34S.Checks.F34S_c<k>_k<j>`, the certificate theorems behind `L6.F34.Checks.certsOK_c<k>_k<j>`,
`L6.F34S.Checks.lines_ok`, `L6.F34S.Checks.open_ok`, `L6.F2S.Checks.f2s_cells_sound`, `L6F1.F1_main`), so the
theorems of this file depend on their auxiliary axioms besides `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace CC6Compose

open CC6Full

variable {m : Fin 6 → ℝ}

/-! ## The stored cell of a germ -/

section germ

variable (hm : ∀ k, 0 < m k) (G : Germ 6 m) {k : ℕ} (hk : k < 191) {d : L6F1.Diagram}
  (hd : L6.F2.diagOf k = L6.F2.Diag.ofF1 d) (hD : G.HasDiagram (toDiagram d)) (hell : G.ell ≤ 0)
  {Tz Tw : TreeShape 6} {htz htw : Finset (Pt 6) → ℚ} (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw)

include hm hd hD hell hRz hRw in
theorem cond_of_germ' : L6.F2S.Cond (L6.F2.diagOf k) (toExp Tz htz) (toExp Tw htw) := by
  have hX := cond_of_germ hm G hD hell hRz hRw
  rwa [← hd] at hX

include hm hk hd hD hell hRz hRw in
/-- **The index of the stored line of the cell of a germ** in the file of its class (Proposition 4.5): its key is
that of the converted trees and of the argmin sets of the germ. -/
theorem germ_line_index : ∃ idx < L6.F34S.Checks.ncellsList.getD k 0,
    L6.F2S.keyOfLine (((L6.F2.Checks.cellsOf k).splitOn "\n").toArray.getD idx "") =
      some ((toTS Tz).key, (toTS Tw).key, L6.F2S.argminString (L6.F2.diagOf k) (toExp Tz htz) (toExp Tw htw)) := by
  have hX := cond_of_germ' hm G hd hD hell hRz hRw
  obtain ⟨line, hline, hkey⟩ := L6.F2S.Checks.f2s_cells_sound k hk _ _ hX
  have hl := List.all_eq_true.mp L6.F34S.Checks.lines_ok k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨idx, hidx, hget⟩ := L6.F34S.Checks.line_index hl.1 hl.2 hline
  exact ⟨idx, hidx, by rw [hget]; exact hkey⟩

include hm hd hD hell hRz hRw in
/-- **The rows of the cell of a germ hold strictly at its heights**: the specification search lists, below the pair
of the trees of the key of the germ, the cell with the argmin part of the germ, and its rows (the rows of the trees,
the forced argmin sets and the argmin choices of the base identities) hold strictly at the heights of the germ. -/
theorem germ_rows_strict :
    ∃ rows, (L6.F2S.argminString (L6.F2.diagOf k) (toExp Tz htz) (toExp Tw htw), rows) ∈
        L6.F34S.cellsBelowR L6.F2S.keepLP (L6.F2.diagOf k) (L6.F34S.pairOfKeys (toTS Tz).key (toTS Tw).key) ∧
      ∀ r ∈ rows, r.StrictHolds (L6.F34S.pairOfKeys (toTS Tz).key (toTS Tw).key).nv
        (L6.F2S.heightVec (toExp Tz htz) (toExp Tw htw) (L6.F34S.pairOfKeys (toTS Tz).key (toTS Tw).key)) := by
  have hX := cond_of_germ' hm G hd hD hell hRz hRw
  set P := L6.F34S.pairOfKeys (toExp Tz htz).T.key (toExp Tw htw).T.key with hP
  have hzn : P.tz.nodes.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr hX.gz.1.nodup
  have hwn : P.tw.nodes.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr hX.gw.1.nodup
  have hzE : P.tz.Equiv (toExp Tz htz).T := ⟨List.toFinset_eq_of_perm _ _ (List.mergeSort_perm _ _), rfl⟩
  have hwE : P.tw.Equiv (toExp Tw htw).T := ⟨List.toFinset_eq_of_perm _ _ (List.mergeSort_perm _ _), rfl⟩
  exact L6.F2S.cellsBelowR_complete L6.F2S.keepLP_sound hX P hzE hzn hwE hwn

include hm hk hd hD hell hRz hRw in
/-- **The claim of the cell of a germ**: for a class `k` without open cells and the certificate texts `certs` of its
chunks, `ClaimIn certs` holds at the converted trees with heights of the germ. -/
theorem germ_claimIn (hopen : k ∉ L6.F34S.openClasses) {certs : List (String × String)}
    (hc : ClassClaim k (L6.F34S.Checks.ncellsList.getD k 0) certs) :
    ClaimIn certs (toExp Tz htz) (toExp Tw htw) := by
  have hX := cond_of_germ' hm G hd hD hell hRz hRw
  obtain ⟨idx, hidx, hkey⟩ := germ_line_index hm G hk hd hD hell hRz hRw
  rcases hc.2 idx hidx with ho | hcl
  · exfalso
    have h2 := List.all_eq_true.mp L6.F34S.Checks.open_ok k (List.mem_range.mpr hk)
    simp only [Bool.or_eq_true, List.isEmpty_iff, List.contains_iff_mem] at h2
    rcases h2 with h2 | h2
    · rw [h2] at ho
      exact absurd ho (by simp)
    · exact hopen h2
  · exact hcl _ _ hX hkey

end germ

/-! ## The exclusion -/

/-- The polynomial of a certificate text (`1` if the text does not parse or if its polynomial is `0`). -/
noncomputable def textPoly (txt : String) : MvPolynomial (Fin 6) ℤ :=
  match L6.Poly.parseCert txt with
  | some c => if certPoly c = 0 then 1 else certPoly c
  | none => 1

theorem textPoly_ne_zero (txt : String) : textPoly txt ≠ 0 := by
  unfold textPoly
  split
  · split_ifs with h
    · exact one_ne_zero
    · exact h
  · exact one_ne_zero

/-- **A germ of a class without open cells makes one of the polynomials of the certificate texts of the class
vanish** at its masses. -/
theorem germ_excluded (hm : ∀ k, 0 < m k) (G : Germ 6 m) {k : ℕ} (hk : k < 191)
    (hopen : k ∉ L6.F34S.openClasses) {certs : List (String × String)}
    (hc : ClassClaim k (L6.F34S.Checks.ncellsList.getD k 0) certs) {d : L6F1.Diagram}
    (hd : L6.F2.diagOf k = L6.F2.Diag.ofF1 d) (hD : G.HasDiagram (toDiagram d)) (hell : G.ell ≤ 0) :
    ∃ p ∈ certs, MvPolynomial.aeval m (textPoly p.2) = 0 := by
  obtain ⟨Tz, htz, hRz⟩ := G.exists_tree_z (by norm_num)
  obtain ⟨Tw, htw, hRw⟩ := G.exists_tree_w (by norm_num)
  rcases germ_claimIn hm G hk hd hD hell hRz hRw hopen hc with
    ⟨I, hg, i, hi⟩ | ⟨c, vars, ⟨p, hp, hparse⟩, hmean, hF6, -, hgen⟩
  · exact (single_false hm hRz hRw hg hi).elim
  · refine ⟨p, hp, ?_⟩
    have h0 := core_vanish hm hRz hRw hmean hgen
    unfold textPoly
    rw [hparse]
    dsimp only
    rw [ite_eq_right (certPoly_ne_zero hmean hF6)]
    exact certPoly_vanish hm h0

/-- **Exclusion of a class from its claims**: if the stored cells of class `k` (with the diagram `Diag.ofF1 d`) are
not open and have the claims `ClassClaim` with the certificate texts `certs`, then the diagram `toDiagram d` is
excluded at generic masses, by the nonzero polynomials `textPoly` of the texts. -/
theorem diagExcluded_of_classClaim {k : ℕ} (hk : k < 191) (hopen : k ∉ L6.F34S.openClasses)
    {certs : List (String × String)} (hc : ClassClaim k (L6.F34S.Checks.ncellsList.getD k 0) certs)
    {d : L6F1.Diagram} (hd : L6.F2.diagOf k = L6.F2.Diag.ofF1 d) : DiagExcluded (toDiagram d) := by
  refine ⟨Fin certs.length, inferInstance, fun i => textPoly certs[i].2, fun i => textPoly_ne_zero _, ?_⟩
  intro m hm G hD hell
  obtain ⟨p, hp, h0⟩ := germ_excluded hm G hk hopen hc hd hD hell
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  refine ⟨⟨i, hi⟩, Equiv.refl _, ?_⟩
  simpa using h0

theorem classes6_length : L6F1.classes6.length = 191 := by
  obtain ⟨-, -, -, -, hlen, -⟩ := L6F1.F1_main
  exact hlen

/-- **Proposition 5.3 for germs: the classes without open cells are excluded.** For every class `k` of
`L6F1.classes6` that is not one of the seven classes of the 43 open cells (`L6.F34S.openClasses`: 31, 124, 127,
132, 133, 143, 147), the germs with the diagram of its representative and `ℓ ≤ 0` are excluded at generic masses. -/
theorem diagExcluded_of_not_open {k : ℕ} (hk : k < L6F1.classes6.length) (hopen : k ∉ L6.F34S.openClasses) :
    DiagExcluded (toDiagram (L6F1.classes6[k]).1) := by
  have hk191 : k < 191 := classes6_length ▸ hk
  obtain ⟨certs, hc⟩ := classClaim k hk191
  exact diagExcluded_of_classClaim hk191 hopen hc (diagOf_eq_ofF1 hk)

/-- **Proposition 5.3 for germs**, for a representative `x` of `L6F1.classes6` whose class (its position in the
list) is not one of the classes of the open cells. -/
theorem diagExcluded_of_mem {x : L6F1.Diagram × ℕ} (hx : x ∈ L6F1.classes6)
    (hopen : L6F1.classes6.idxOf x ∉ L6.F34S.openClasses) : DiagExcluded (toDiagram x.1) := by
  have hlt : L6F1.classes6.idxOf x < L6F1.classes6.length := List.idxOf_lt_length_iff.mpr hx
  have h := diagExcluded_of_not_open hlt hopen
  rwa [List.getElem_idxOf hlt] at h

end CC6Compose
