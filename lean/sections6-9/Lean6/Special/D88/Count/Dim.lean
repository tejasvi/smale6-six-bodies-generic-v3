import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Dimension of a quotient by its standard monomials

For a monomial order `m` and a set `G` of nonzero polynomials in an ideal `I` of `K[σ]`, the standard monomials of
`G` (the exponents `c` with `m.degree g ≰ c` for all `g ∈ G`, `≤` the componentwise order) span `K[σ] ⧸ I`: this is
Mathlib's division algorithm `MonomialOrder.div_set` (`span_std`). A finite set `S` of exponents that contains `0`
and is closed under the border (for `s ∈ S` and every variable `i`, either `s + eᵢ ∈ S` or some leading exponent
`m.degree g` divides `s + eᵢ`) contains all standard monomials (`std_subset_of_border`). Hence
`dim_K K[σ] ⧸ I ≤ |S|` (`finrank_le_of_border`), the form in which Lemma 6.19(b) is checked: the checker verifies that
`S` contains `0` and is closed under the border with respect to the leading monomials of polynomials that lie in the
ideal by construction.
-/

namespace Lean6.Special.D88.Count

open MvPolynomial MonomialOrder Finsupp

variable {σ : Type*} {K : Type*} [Field K] (m : MonomialOrder σ)

/-- The standard monomials of a set of polynomials. -/
def Std (G : Set (MvPolynomial σ K)) : Set (σ →₀ ℕ) := {c | ∀ g ∈ G, ¬ m.degree g ≤ c}

/-- **Border closure**: a set of exponents that contains `0` and is closed under the border contains every standard
monomial. -/
theorem std_subset_of_border {G : Set (MvPolynomial σ K)} {S : Set (σ →₀ ℕ)} (h0 : 0 ∈ S)
    (hb : ∀ s ∈ S, ∀ i, s + single i 1 ∈ S ∨ ∃ g ∈ G, m.degree g ≤ s + single i 1) :
    Std m G ⊆ S := by
  suffices H : ∀ n : ℕ, ∀ c : σ →₀ ℕ, c.degree = n → c ∈ Std m G → c ∈ S from
    fun c hc => H _ c rfl hc
  intro n
  induction n with
  | zero =>
    intro c hc _
    rw [Finsupp.degree_eq_zero_iff] at hc
    rw [hc]
    exact h0
  | succ n ih =>
    intro c hc hstd
    have hne : c ≠ 0 := by
      rintro rfl
      simp at hc
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra! h
      exact hne (Finsupp.ext h)
    have hle : single i 1 ≤ c := by
      rw [Finsupp.single_le_iff]
      omega
    set c' := c - single i 1 with hc'def
    have hc' : c' + single i 1 = c := tsub_add_cancel_of_le hle
    have hdeg' : c'.degree = n := by
      have := map_add Finsupp.degree c' (single i 1)
      rw [hc', hc, Finsupp.degree_single] at this
      omega
    have hstd' : c' ∈ Std m G := by
      intro g hg hgc
      exact hstd g hg (hgc.trans (by rw [← hc']; exact le_self_add))
    rcases hb c' (ih c' hdeg' hstd') i with h | ⟨g, hg, hgc⟩
    · rwa [hc'] at h
    · rw [hc'] at hgc
      exact absurd hgc (hstd g hg)

/-- **The standard monomials span the quotient** (division algorithm). -/
theorem span_std (I : Ideal (MvPolynomial σ K)) (G : Set (MvPolynomial σ K)) (hGI : G ⊆ I)
    (hG0 : ∀ g ∈ G, g ≠ 0) (S : Set (σ →₀ ℕ)) (hS : Std m G ⊆ S) :
    Submodule.span K ((fun s => Ideal.Quotient.mk I (monomial s (1 : K))) '' S) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, r, hf, -, hr⟩ :=
    m.div_set (B := G) (fun b hb => (m.leadingCoeff_ne_zero_iff.mpr (hG0 b hb)).isUnit) f
  have hmem : f - r ∈ I := by
    rw [hf, add_sub_cancel_right, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun b _ => ?_
    show g b • (b : MvPolynomial σ K) ∈ I
    rw [smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (hGI b.2)
  have hq : Ideal.Quotient.mk I f = Ideal.Quotient.mk I r := Ideal.Quotient.eq.mpr hmem
  rw [hq, r.as_sum, map_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcS : c ∈ S := hS fun b hb => hr c hc b hb
  have e : Ideal.Quotient.mk I (monomial c (r.coeff c)) =
      r.coeff c • Ideal.Quotient.mk I (monomial c (1 : K)) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk K I, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, hcS, rfl⟩)

/-- **The dimension bound**: if `G ⊆ I` consists of nonzero polynomials and the finite set `S` of exponents contains
`0` and is closed under the border of the leading exponents of `G`, then `K[σ] ⧸ I` is finite-dimensional of
dimension at most `|S|`. -/
theorem finrank_le_of_border (I : Ideal (MvPolynomial σ K)) (G : Set (MvPolynomial σ K)) (hGI : G ⊆ I)
    (hG0 : ∀ g ∈ G, g ≠ 0) (S : Finset (σ →₀ ℕ)) (h0 : 0 ∈ S)
    (hb : ∀ s ∈ S, ∀ i, s + single i 1 ∈ S ∨ ∃ g ∈ G, m.degree g ≤ s + single i 1) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ∧ Module.finrank K (MvPolynomial σ K ⧸ I) ≤ S.card := by
  classical
  have hspan := span_std m I G hGI hG0 (S : Set (σ →₀ ℕ)) (std_subset_of_border m h0 hb)
  set T : Finset (MvPolynomial σ K ⧸ I) := S.image fun s => Ideal.Quotient.mk I (monomial s (1 : K)) with hT
  have hTspan : Submodule.span K (T : Set (MvPolynomial σ K ⧸ I)) = ⊤ := by
    rw [hT, Finset.coe_image]
    exact hspan
  have hfin : Module.Finite K (MvPolynomial σ K ⧸ I) := ⟨⟨T, hTspan⟩⟩
  refine ⟨hfin, ?_⟩
  have h1 := finrank_span_finset_le_card (R := K) T
  unfold Set.finrank at h1
  rw [hTspan, finrank_top] at h1
  exact h1.trans Finset.card_image_le

end Lean6.Special.D88.Count
