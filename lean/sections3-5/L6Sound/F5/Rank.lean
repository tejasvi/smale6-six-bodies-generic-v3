import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.StdBasis

/-!
# The dimensions of the spaces `L^c` of Corollary 5.8

In Corollary 5.8, `L^c ⊆ ℚ^K` is spanned by vectors `e_t` for a set `F` of bodies of `K` and, possibly, by the vector
`𝟙`. With `k = |K|` and the bodies of `K` numbered `0, …, k - 1`:

* `finrank_units`: the span of the `e_t`, `t ∈ F`, has dimension `|F|`;
* `finrank_units_one`: if `F` is not everything, the span of the `e_t`, `t ∈ F`, and `𝟙` has dimension `|F| + 1`;
* `finrank_units_one_univ`: if `F` is everything, it has dimension `k`.

These are the values that `L6F5.rank` returns on these vectors for `k = 3, 4`, every `F` and both cases
(`L6F5.rank_unit_vectors`), so the census computes `dim L^z` and `dim L^w` exactly. The other conditions of
Corollary 5.8 are transcribed literally in `L6F5.cliqueOK` (`L6F5/Clique.lean`).
-/

open Module Submodule

namespace L6F5

/-- The vectors spanning the span of the `e_t`, `t ∈ F`, and `𝟙` in `ℚ^k`: `𝟙` at `none`, `e_t` at `some t`. -/
noncomputable def unitsOne {k : ℕ} (F : Finset (Fin k)) : Option F → (Fin k → ℚ) :=
  fun o => Option.casesOn' o (fun _ => 1) (fun t : F => Pi.single (t : Fin k) 1)

/-- The vectors `e_t`, `t ∈ F`, are linearly independent. -/
theorem linearIndependent_units {k : ℕ} (F : Finset (Fin k)) :
    LinearIndependent ℚ fun t : F => (Pi.single (t : Fin k) (1 : ℚ) : Fin k → ℚ) := by
  have h := (Pi.basisFun ℚ (Fin k)).linearIndependent.comp (Subtype.val : F → Fin k) Subtype.val_injective
  simpa [Function.comp_def, Pi.basisFun_apply] using h

/-- **The span of the `e_t`, `t ∈ F`, has dimension `|F|`.** -/
theorem finrank_units {k : ℕ} (F : Finset (Fin k)) :
    finrank ℚ (span ℚ (Set.range fun t : F => (Pi.single (t : Fin k) (1 : ℚ) : Fin k → ℚ))) = F.card := by
  rw [finrank_span_eq_card (linearIndependent_units F), Fintype.card_coe]

/-- **If `F` is not everything, the span of the `e_t`, `t ∈ F`, and `𝟙` has dimension `|F| + 1`.** -/
theorem finrank_units_one {k : ℕ} (F : Finset (Fin k)) (hF : F ≠ Finset.univ) :
    finrank ℚ (span ℚ (Set.range (unitsOne F))) = F.card + 1 := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ F := by
    by_contra h
    exact hF (Finset.eq_univ_iff_forall.mpr fun j => by
      by_contra hj
      exact h ⟨j, hj⟩)
  have hx : (fun _ => (1 : ℚ) : Fin k → ℚ) ∉
      span ℚ (Set.range fun t : F => (Pi.single (t : Fin k) (1 : ℚ) : Fin k → ℚ)) := by
    intro hmem
    have hle : span ℚ (Set.range fun t : F => (Pi.single (t : Fin k) (1 : ℚ) : Fin k → ℚ)) ≤
        LinearMap.ker (LinearMap.proj j : (Fin k → ℚ) →ₗ[ℚ] ℚ) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      have htj : j ≠ (t : Fin k) := fun h => hj (h ▸ t.2)
      simp [htj]
    have h1 := hle hmem
    simp at h1
  have hli : LinearIndependent ℚ (unitsOne F) := (linearIndependent_units F).option hx
  rw [finrank_span_eq_card hli, Fintype.card_option, Fintype.card_coe]

/-- **If `F` is everything, the span of the `e_t`, `t ∈ F`, and `𝟙` has dimension `k`.** -/
theorem finrank_units_one_univ (k : ℕ) :
    finrank ℚ (span ℚ (Set.range (unitsOne (Finset.univ : Finset (Fin k))))) = k := by
  have htop : span ℚ (Set.range (unitsOne (Finset.univ : Finset (Fin k)))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ (Fin k)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨some ⟨i, Finset.mem_univ i⟩, by simp [unitsOne, Pi.basisFun_apply]⟩
  rw [htop, finrank_top, Module.finrank_fin_fun]

end L6F5
