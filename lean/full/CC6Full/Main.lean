import CC6Full.Curve.GermOfPlace
import CC6Full.Germ.Symm
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Theorem 1.1 from the exclusion of germs (Section 8, `sec:proof`)

`GermExclusion` is the statement proved by Sections 3–7 of the paper: there are finitely many nonzero integer
polynomials in the six masses such that every germ of a singular place with `ℓ(x) ≤ 0`, for positive masses `m`,
makes one of them vanish at a permutation of `m`. `main_of_germExclusion` derives Theorem 1.1 (`MainTheorem`) from
it, as in Section 8: `F` is the product of all these polynomials evaluated at all permutations of the masses, `F ≠ 0`,
and if `F(m) ≠ 0` and `m` had infinitely many central configurations, Part I (`exists_germ`: Corollaries 2.4 and 2.7
and Lemma 2.5) would give a germ with `ℓ ≤ 0`.
-/

namespace CC6Full

open MvPolynomial

/-- The exclusion of germs with `ℓ ≤ 0` at generic masses (Sections 3–7). -/
def GermExclusion : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (P : ι → MvPolynomial (Fin 6) ℤ), (∀ i, P i ≠ 0) ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.ell ≤ 0 →
      ∃ i, ∃ σ : Equiv.Perm (Fin 6), aeval (m ∘ σ) (P i) = 0

/-- **Section 8**: Theorem 1.1 follows from the exclusion of germs. -/
theorem main_of_germExclusion (h : GermExclusion) : MainTheorem := by
  classical
  obtain ⟨ι, _, P, hP0, hP⟩ := h
  refine ⟨∏ i, ∏ σ : Equiv.Perm (Fin 6), rename σ (P i), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro σ _
    exact fun h0 => hP0 i (rename_injective σ σ.injective (by rw [h0, map_zero]))
  · intro m hm hF
    by_contra hfin
    obtain ⟨G, hG⟩ := exists_germ (n := 4) hm hfin
    obtain ⟨i, σ, hzero⟩ := hP m hm G hG
    apply hF
    rw [map_prod, Finset.prod_eq_zero_iff]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [map_prod, Finset.prod_eq_zero_iff]
    exact ⟨σ, Finset.mem_univ _, by rw [aeval_rename]; exact hzero⟩

end CC6Full
