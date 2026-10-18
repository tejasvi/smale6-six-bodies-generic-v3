import CC6Compose.V3.Interface
import CC6Compose.ExclusionPoly

/-!
# The kernel-only composition: Theorem 1.1 from the string-free statements

`main_of_v3`: Theorem 1.1 from a class list `L` with `F1Cover L`, `FusedExclusion L` and `OpenCheck L`, and the
computations of Sections 6 and 7 (`SevenCerts'`). It uses no check of the certificate projects, so it depends only
on `propext`, `Classical.choice` and `Quot.sound`; the checks enter through its hypotheses.

* `repsL L`, `cover_of_f1`: the representatives cover the diagrams of all germs (Proposition 3.1 for germs).
* `diagExcluded_of_fused`: Proposition 5.3 for germs, with the nonzero polynomials `certPolyNZ` of the finitely many
  certificates of the class.
-/

namespace CC6Compose.V3

open CC6Full

/-! ## The classes -/

/-- The diagrams of the representatives of a class list. -/
def repsL (L : List (L6F1.Diagram × ℕ)) : Finset (Diagram 6) := (L.map fun x => toDiagram x.1).toFinset

theorem mem_repsL {L : List (L6F1.Diagram × ℕ)} {D : Diagram 6} :
    D ∈ repsL L ↔ ∃ x ∈ L, toDiagram x.1 = D := by
  simp only [repsL, List.mem_toFinset, List.mem_map]

theorem repsL_ordered (L : List (L6F1.Diagram × ℕ)) : ∀ D ∈ repsL L, D.Ordered := by
  intro D hD
  obtain ⟨x, -, rfl⟩ := mem_repsL.mp hD
  exact toDiagram_ordered x.1

/-- **Proposition 3.1 for germs** from `F1Cover`: the diagram of every germ for positive masses is the image of a
representative under a relabelling, followed by the exchange of the colours if `b`. -/
theorem cover_of_f1 {L : List (L6F1.Diagram × ℕ)} (hF1 : F1Cover L) :
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, ∃ D ∈ repsL L, ∃ σ : Equiv.Perm (Fin 6), ∃ b : Bool,
      G.HasDiagram (bif b then (D.relabel σ).swap else D.relabel σ) := by
  intro m hm G
  obtain ⟨x, hx, σ, s, hσ⟩ :=
    hF1.2 (germCode G) (L6F1.mem_allDiagrams.mpr (germCode_inRange G)) (okRules_germCode hm G)
  refine ⟨toDiagram x.1, mem_repsL.mpr ⟨x, hx, rfl⟩, σ.symm, s, ?_⟩
  have h := hasDiagram_germCode G
  rw [hσ, toDiagram_actP] at h
  exact h

/-! ## The exclusion -/

/-- The polynomial of a certificate (`1` if it is `0`). -/
noncomputable def certPolyNZ (c : L6.Poly.Cert) : MvPolynomial (Fin 6) ℤ :=
  if certPoly c = 0 then 1 else certPoly c

theorem certPolyNZ_ne_zero (c : L6.Poly.Cert) : certPolyNZ c ≠ 0 := by
  unfold certPolyNZ
  split_ifs with h
  · exact one_ne_zero
  · exact h

/-- **Proposition 5.3 for germs** from `FusedExclusion`: for a class `k` without open cells, the germs with the
diagram of its representative and `ℓ ≤ 0` make one of the polynomials of the certificates of the class vanish at
their masses. -/
theorem diagExcluded_of_fused {L : List (L6F1.Diagram × ℕ)} (hF : FusedExclusion L) {k : ℕ} (hk : k < 191)
    (hopen : k ∉ L6.F34S.openClasses) : DiagExcluded (toDiagram (L.getD k (default, 0)).1) := by
  obtain ⟨cs, hcs⟩ := hF k hk
  refine ⟨Fin cs.length, inferInstance, fun i => certPolyNZ cs[i], fun i => certPolyNZ_ne_zero _, ?_⟩
  intro m hm G hD hell
  obtain ⟨Tz, htz, hRz⟩ := G.exists_tree_z (by norm_num)
  obtain ⟨Tw, htw, hRw⟩ := G.exists_tree_w (by norm_num)
  rcases hcs _ _ (cond_of_germ hm G hD hell hRz hRw) with ho | ⟨I, hg, i, hi⟩ | ⟨c, hc, vars, hmean, hF6, -, hgen⟩
  · exact absurd ho hopen
  · exact (single_false hm hRz hRw hg hi).elim
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    refine ⟨⟨i, hi⟩, Equiv.refl _, ?_⟩
    have h0 := certPoly_vanish hm (core_vanish hm hRz hRw hmean hgen)
    simpa [certPolyNZ, certPoly_ne_zero hmean hF6] using h0

/-! ## Theorem 1.1 -/

/-- **Theorem 1.1 from the string-free statements**: a class list with `F1Cover`, `FusedExclusion` and
`OpenCheck`, and the computations of Sections 6 and 7. -/
theorem main_of_v3 (L : List (L6F1.Diagram × ℕ)) (hF1 : F1Cover L) (hF : FusedExclusion L) (hO : OpenCheck L)
    (h7 : SevenCerts') : MainTheorem := by
  refine main_of_classesExcluded ⟨repsL L, repsL_ordered L, cover_of_f1 hF1, fun D hD => ?_⟩
  by_cases hs : D ∈ specials
  · exact specials_excluded h7 D hs
  · obtain ⟨x, hx, rfl⟩ := mem_repsL.mp hD
    have hlt : L.idxOf x < L.length := List.idxOf_lt_length_iff.mpr hx
    have hget : L.getD (L.idxOf x) (default, 0) = x := by
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]
    have hopen : L.idxOf x ∉ L6.F34S.openClasses := by
      intro ho
      obtain ⟨E, hE, hb⟩ := hO _ ho
      rw [hget] at hb
      exact hs (eq_of_diagBEq hb ▸ hE)
    have h := diagExcluded_of_fused hF (hF1.1 ▸ hlt) hopen
    rwa [hget] at h

end CC6Compose.V3
