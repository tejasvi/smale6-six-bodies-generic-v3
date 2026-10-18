import CC6Compose.V3.Special
import CC6Compose.Exclusion
import CC6Compose.CellsConv

/-!
# The kernel-only composition: the string-free statements from the native checks

The hypotheses of `main_of_v3` for the literal class list `classes6Lit`, from the checks of the version-2
composition (`native_decide` in the certificate projects): `F1Cover` from `L6F1.F1_main`, `FusedExclusion` from the
chunk checks of Proposition 5.3 with the completeness of the cell search, `OpenCheck` by kernel evaluation. This
checks that the string-free statements say what the composition needs; `main_theorem_v3_native` is Theorem 1.1 assembled
through them. In the kernel-only version these instances are replaced by theorems of the certificate projects
checked by the kernel.
-/

namespace CC6Compose.V3

open CC6Full
open L6.F2S (ExpTree Cond)

/-- The class list read from `n6.json` is the literal `classes6Lit` (evaluated by `native_decide`). -/
theorem classes6_eq_lit : L6F1.classes6 = classes6Lit := by native_decide

theorem f1Cover_native : F1Cover classes6Lit := by
  obtain ⟨-, -, -, -, hlen, hcls, -⟩ := L6F1.F1_main
  rw [← classes6_eq_lit]
  exact ⟨hlen, fun d hd hok => (hcls d).mp ⟨hd, hok⟩⟩

theorem diagOfL_lit {k : ℕ} (hk : k < 191) : diagOfL classes6Lit k = L6.F2.diagOf k := by
  have hk' : k < L6F1.classes6.length := classes6_length ▸ hk
  rw [diagOf_eq_ofF1 hk', diagOfL, ← classes6_eq_lit, List.getD_eq_getElem _ _ hk']

/-- **The index of the stored line** of the cell of a pair satisfying `Cond` (Proposition 4.5). -/
theorem line_index_of_cond {k : ℕ} (hk : k < 191) {Xz Xw : ExpTree} (hX : Cond (L6.F2.diagOf k) Xz Xw) :
    ∃ idx < L6.F34S.Checks.ncellsList.getD k 0,
      L6.F2S.keyOfLine (((L6.F2.Checks.cellsOf k).splitOn "\n").toArray.getD idx "") =
        some (Xz.T.key, Xw.T.key, L6.F2S.argminString (L6.F2.diagOf k) Xz Xw) := by
  obtain ⟨line, hline, hkey⟩ := L6.F2S.Checks.f2s_cells_sound k hk _ _ hX
  have hl := List.all_eq_true.mp L6.F34S.Checks.lines_ok k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨idx, hidx, hget⟩ := L6.F34S.Checks.line_index hl.1 hl.2 hline
  exact ⟨idx, hidx, by rw [hget]; exact hkey⟩

/-- **The claim of a pair satisfying `Cond`** in a class without open cells, from the chunk checks. -/
theorem claimIn_of_cond {k : ℕ} (hk : k < 191) (hopen : k ∉ L6.F34S.openClasses) {certs : List (String × String)}
    (hc : ClassClaim k (L6.F34S.Checks.ncellsList.getD k 0) certs) {Xz Xw : ExpTree}
    (hX : Cond (L6.F2.diagOf k) Xz Xw) : ClaimIn certs Xz Xw := by
  obtain ⟨idx, hidx, hkey⟩ := line_index_of_cond hk hX
  rcases hc.2 idx hidx with ho | hcl
  · exfalso
    have h2 := List.all_eq_true.mp L6.F34S.Checks.open_ok k (List.mem_range.mpr hk)
    simp only [Bool.or_eq_true, List.isEmpty_iff, List.contains_iff_mem] at h2
    rcases h2 with h2 | h2
    · rw [h2] at ho
      exact absurd ho (by simp)
    · exact hopen h2
  · exact hcl _ _ hX hkey

theorem claimMeaningIn_of_claimIn {certs : List (String × String)} {Xz Xw : ExpTree} (h : ClaimIn certs Xz Xw) :
    ClaimMeaningIn (certs.filterMap fun p => L6.Poly.parseCert p.2) Xz Xw := by
  rcases h with hs | ⟨c, vars, ⟨p, hp, hparse⟩, rest⟩
  · exact Or.inl hs
  · exact Or.inr ⟨c, List.mem_filterMap.mpr ⟨p, hp, hparse⟩, vars, rest⟩

theorem fused_native : FusedExclusion classes6Lit := by
  intro k hk
  obtain ⟨certs, hc⟩ := classClaim k hk
  refine ⟨certs.filterMap fun p => L6.Poly.parseCert p.2, fun Xz Xw hX => ?_⟩
  by_cases ho : k ∈ L6.F34S.openClasses
  · exact Or.inl ho
  · rw [diagOfL_lit hk] at hX
    exact Or.inr (claimMeaningIn_of_claimIn (claimIn_of_cond hk ho hc hX))

/-- **Theorem 1.1**, assembled through the string-free statements, with their instances from the native checks. -/
theorem main_theorem_v3_native : MainTheorem :=
  main_of_facts classes6Lit f1Cover_native fused_native openCheck_lit specialFacts_native

end CC6Compose.V3
