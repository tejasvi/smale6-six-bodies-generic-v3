import CC6Full.Six.D64Poly
import Mathlib.RingTheory.Nullstellensatz

/-!
# Diagram 64: the polynomial of Theorem 7.12 from the absence of common zeros at `μ₀`

`CC6Full.Six.d64_poly` takes as hypothesis the certificate fact `E4Cert` at `μ₀ = (3, 5, 7, 11)`: nonzero maximal
minors of the Macaulay matrices of the forms `ℱ_ε`, `𝒢_σ` of Lemma 7.6 in the fixed degrees `7` and `8`. Here the
hypothesis is the statement checked at `μ₀` after Proposition 7.8 (`prop:E4`): at `μ₀` none of these systems of forms
has a common zero other than `0`.

* `E4NoZero`: for every symmetric pattern `ε` (`e : Fin 6 → ZMod 3`, as in `CC6Full.Six.E4`) the seven cubic forms
  `E4.Fforms μ₀ e` have no common zero `q ≠ 0` in `ℂ⁴`, and for every antisymmetric sign pattern `σ`
  (`s : Fin 6 → Bool`) the four quartic forms `E4.Gforms μ₀ s` have no common zero `≠ 0` in `ℂ³`.
* `exists_macaulayMinor_ne_zero_of_noZero`: homogeneous forms over `ℂ` in at least one variable with only the
  trivial common zero have, in some degree `D`, a Macaulay matrix with a nonzero maximal minor.
* `E4P.prop_E4_poly_of_noZero`: **Proposition 7.8** in polynomial form, given `E4NoZero`.
* `d64_poly_of_noZero`: **Theorem 7.12**, the polynomial, given `E4NoZero`.

## The proof

By the Nullstellensatz (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`), forms with only the trivial common zero
have every variable `X_k` in the radical of the ideal `I` they generate: `X_k^{n_k} ∈ I`. With `N = Σ_k n_k`, every
monomial of degree `D = (number of variables) · N` has some exponent `≥ N`, so it lies in `I`
(`exists_degree_monomial_mem`). Taking the coefficients of the monomials of degree `D` (a linear map), an element
`Σ_i c_i f_i` of `I` goes to a combination of the rows of the Macaulay matrix in degree `D` (the products
`X^u f_i` of degree `D`; the other products `X^u f_i` are homogeneous of another degree and go to `0`); the monomials
of degree `D` go to the standard basis vectors. So the Macaulay matrix has full column rank
(`span_row_macaulayMatrix_eq_top`) and a nonzero maximal minor (`exists_submatrix_det_ne_zero`).

At `μ₀` this gives, for each pattern, a degree and a maximal minor of the Macaulay matrix of the forms with
coefficients in `ℤ[j][μ]` (`E4P.Fforms`, `E4P.Gforms`) that does not vanish at `μ₀`. The rest is the proof of
`d64_poly` with these degrees in place of `7` and `8`: the product of the minors and of `μ₁μ₂μ₃μ₄` vanishes on
`B_E` (the Macaulay transfer `eq_zero_of_map_macaulayMinor_ne_zero`), `E4P.exists_int_poly` gives integer
coefficients, and `Germ.d64_forms` puts the masses of the cluster `K = {3, 4, 5, 6}` in `B_E`.
-/

namespace CC6Full.Six

open MvPolynomial Finset

noncomputable section

/-- **The fact checked at `μ₀ = (3, 5, 7, 11)`** after Proposition 7.8 (`prop:E4`), with `μ₀ = E4P.μ₀`, the vector
`![3, 5, 7, 11]` of complex numbers: for each of the `3⁶` symmetric patterns `ε` (`e : Fin 6 → ZMod 3`) the seven
cubic forms `ℱ_ε` of Lemma 7.6 at `μ₀` (`E4.Fforms μ₀ e`) have no common zero `q ≠ 0` in `ℂ⁴`, and for each of the
`2⁶` antisymmetric sign patterns `σ` (`s : Fin 6 → Bool`) the four quartic forms `𝒢_σ` at `μ₀` (`E4.Gforms μ₀ s`)
have no common zero `(ξ₂, ξ₃, ξ₄) ≠ 0` in `ℂ³`. -/
def E4NoZero : Prop :=
  (∀ e : Fin 6 → ZMod 3, ∀ q : Fin 4 → ℂ, (∀ i, eval q (E4.Fforms E4P.μ₀ e i) = 0) → q = 0) ∧
    ∀ s : Fin 6 → Bool, ∀ y : Fin 3 → ℂ, (∀ k, eval y (E4.Gforms E4P.μ₀ s k) = 0) → y = 0

/-! ## From the trivial common zero to a nonzero maximal minor -/

section NoZero

variable {σ ι : Type*}

/-- The Nullstellensatz step: if polynomials over `ℂ` in finitely many variables have no common zero other than
`0`, every variable `X_k` vanishes on their common zeros, so it lies in the radical of the ideal they generate. -/
theorem exists_pow_X_mem_ideal [Finite σ] (f : ι → MvPolynomial σ ℂ)
    (h0 : ∀ q : σ → ℂ, (∀ i, eval q (f i) = 0) → q = 0) (k : σ) :
    ∃ n : ℕ, (X k : MvPolynomial σ ℂ) ^ n ∈ Ideal.span (Set.range f) := by
  have hmem : (X k : MvPolynomial σ ℂ) ∈ vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span (Set.range f))) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    have hx0 : x = 0 := h0 x fun i => by
      simpa using hx (f i) (Ideal.subset_span ⟨i, rfl⟩)
    rw [hx0, aeval_X, Pi.zero_apply]
  rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
  exact hmem

/-- If polynomials over `ℂ` in finitely many (and at least one) variables have no common zero other than `0`, then
for some degree `D` every monomial of degree `D` lies in the ideal they generate: with `X_k^{n_k}` in the ideal and
`N = Σ_k n_k`, a monomial of degree `D = (number of variables) · N` has some exponent `≥ N`. -/
theorem exists_degree_monomial_mem [Fintype σ] [Nonempty σ] (f : ι → MvPolynomial σ ℂ)
    (h0 : ∀ q : σ → ℂ, (∀ i, eval q (f i) = 0) → q = 0) :
    ∃ D : ℕ, ∀ v : σ →₀ ℕ, v.degree = D → monomial v (1 : ℂ) ∈ Ideal.span (Set.range f) := by
  choose n hn using exists_pow_X_mem_ideal f h0
  refine ⟨Fintype.card σ * ∑ k, n k, fun v hv => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, ∑ l, n l ≤ v k := by
    by_contra hcon
    push Not at hcon
    have hlt : ∑ k, v k < ∑ _k : σ, ∑ l, n l :=
      Finset.sum_lt_sum_of_nonempty univ_nonempty fun k _ => hcon k
    rw [sum_const, card_univ, smul_eq_mul, ← Finsupp.degree_eq_sum, hv] at hlt
    exact lt_irrefl _ hlt
  have hnk : n k ≤ ∑ l, n l := single_le_sum (fun l _ => Nat.zero_le (n l)) (mem_univ k)
  have hXN : (X k : MvPolynomial σ ℂ) ^ (∑ l, n l) ∈ Ideal.span (Set.range f) := by
    rw [← Nat.sub_add_cancel hnk, pow_add]
    exact Ideal.mul_mem_left _ _ (hn k)
  have hle : Finsupp.single k (∑ l, n l) ≤ v := Finsupp.single_le_iff.mpr hk
  have hmono : monomial v (1 : ℂ) = monomial (v - Finsupp.single k (∑ l, n l)) 1 * X k ^ (∑ l, n l) := by
    rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one, tsub_add_cancel_of_le hle]
  rw [hmono]
  exact Ideal.mul_mem_left _ _ hXN

variable [Fintype σ] [DecidableEq σ] [Fintype ι]

/-- Full column rank of the Macaulay matrix: if the forms `f i` (of degrees `d i`) over a field `K` have every
monomial of degree `D` in their ideal, the rows of the Macaulay matrix in degree `D` span the whole space. The
coefficients of the monomials of degree `D` form a linear map `L`; it sends `X^u f_i` to a row if
`deg u + d i = D` and to `0` otherwise (the product is homogeneous of degree `deg u + d i`), hence every element
`Σ_i c_i f_i` of the ideal into the span of the rows, and the monomials of degree `D` to the standard basis
vectors. -/
theorem span_row_macaulayMatrix_eq_top {K : Type*} [Field K] (f : ι → MvPolynomial σ K) {d : ι → ℕ}
    (hf : ∀ i, (f i).IsHomogeneous (d i)) {D : ℕ}
    (hD : ∀ v : σ →₀ ℕ, v.degree = D → monomial v (1 : K) ∈ Ideal.span (Set.range f)) :
    Submodule.span K (Set.range (macaulayMatrix f d D).row) = ⊤ := by
  obtain ⟨L, hL⟩ : ∃ L : MvPolynomial σ K →ₗ[K] (monomialsOfDegree σ D → K),
      ∀ p c, L p c = p.coeff (c : σ →₀ ℕ) :=
    ⟨LinearMap.pi fun c => lcoeff K (c : σ →₀ ℕ), fun _ _ => rfl⟩
  have hrow : ∀ (i : ι) (u : σ →₀ ℕ),
      L (macaulayRowPoly f (i, u)) ∈ Submodule.span K (Set.range (macaulayMatrix f d D).row) := by
    intro i u
    by_cases hiu : d i + u.degree = D
    · have hr : (i, u) ∈ macaulayRows σ d D := mem_macaulayRows.mpr hiu
      have h1 : L (macaulayRowPoly f (i, u)) = (macaulayMatrix f d D).row ⟨(i, u), hr⟩ := by
        funext c
        rw [hL]
        rfl
      rw [h1]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have h1 : L (macaulayRowPoly f (i, u)) = 0 := by
        funext c
        rw [hL, Pi.zero_apply]
        have hhom : (monomial u (1 : K) * f i).IsHomogeneous (u.degree + d i) :=
          (isHomogeneous_monomial (1 : K) rfl).mul (hf i)
        have hc : (c : σ →₀ ℕ).degree = D := mem_monomialsOfDegree.mp c.2
        exact hhom.coeff_eq_zero (by omega)
      rw [h1]
      exact Submodule.zero_mem _
  have hideal : ∀ p ∈ Ideal.span (Set.range f),
      L p ∈ Submodule.span K (Set.range (macaulayMatrix f d D).row) := by
    intro p hp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hci : c i * f i = ∑ u ∈ (c i).support, (c i).coeff u • macaulayRowPoly f (i, u) := by
      conv_lhs => rw [(c i).as_sum]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [macaulayRowPoly, smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one]
    rw [hci, map_sum]
    exact Submodule.sum_mem _ fun u _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hrow i u)
  refine Submodule.eq_top_iff'.mpr fun w => ?_
  have hw : L (∑ c : monomialsOfDegree σ D, w c • monomial (c : σ →₀ ℕ) (1 : K)) = w := by
    funext c'
    rw [hL, coeff_sum]
    simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single c']
    · simp
    · intro b _ hb
      exact ite_eq_right fun h => hb (Subtype.ext h)
    · intro h
      exact absurd (mem_univ c') h
  rw [← hw]
  exact hideal _ (Ideal.sum_mem _ fun c _ =>
    Submodule.smul_of_tower_mem _ _ (hD c (mem_monomialsOfDegree.mp c.2)))

/-- Homogeneous forms over `ℂ` in at least one variable that have no common zero other than `0` have, in some
degree `D`, a Macaulay matrix with a nonzero maximal minor: by `exists_degree_monomial_mem` and
`span_row_macaulayMatrix_eq_top` it has full column rank. -/
theorem exists_macaulayMinor_ne_zero_of_noZero [Nonempty σ] (f : ι → MvPolynomial σ ℂ) {d : ι → ℕ}
    (hf : ∀ i, (f i).IsHomogeneous (d i)) (h0 : ∀ q : σ → ℂ, (∀ i, eval q (f i) = 0) → q = 0) :
    ∃ D : ℕ, ∃ S : monomialsOfDegree σ D → macaulayRows σ d D, macaulayMinor f d D S ≠ 0 := by
  obtain ⟨D, hD⟩ := exists_degree_monomial_mem f h0
  exact ⟨D, exists_submatrix_det_ne_zero _ (span_row_macaulayMatrix_eq_top f hf hD)⟩

end NoZero

namespace E4P

/-! ## The forms of Lemma 7.6 in any degree -/

/-- The forms `ℱ_ε` of Lemma 7.6 at `μ` are cubic. -/
theorem E4Fforms_hom (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (i : Fin 7) : (E4.Fforms μ e i).IsHomogeneous 3 := by
  rw [← map_Fforms μ e i]
  exact (Fforms_hom e i).map _

/-- The forms `𝒢_σ` of Lemma 7.6 at `μ` are quartic. -/
theorem E4Gforms_hom (μ : Fin 4 → ℂ) (s : Fin 6 → Bool) (k : Fin 4) : (E4.Gforms μ s k).IsHomogeneous 4 := by
  rw [← map_Gforms μ s k]
  exact (Gforms_hom s k).map _

/-- In any degree `D`, the maximal minors of the Macaulay matrix of the forms `ℱ_ε` with coefficients in
`ℤ[j][μ]`, specialized at `μ`, are those of the forms `E4.Fforms μ e`. -/
theorem eval₂_macaulayMinorF (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3) (D : ℕ)
    (S : monomialsOfDegree (Fin 4) D → macaulayRows (Fin 4) (fun _ : Fin 7 => 3) D) :
    eval₂ ZJ.subtype μ (macaulayMinor (Fforms e) (fun _ => 3) D S) =
      macaulayMinor (E4.Fforms μ e) (fun _ => 3) D S := by
  have h := map_macaulayMinor (eval₂Hom ZJ.subtype μ) (Fforms e) (fun _ => 3) D S
  rw [coe_eval₂Hom, show (fun i => map (eval₂Hom ZJ.subtype μ) (Fforms e i)) = E4.Fforms μ e from
    funext (map_Fforms μ e)] at h
  exact h

/-- In any degree `D`, the maximal minors of the Macaulay matrix of the forms `𝒢_σ` with coefficients in
`ℤ[j][μ]`, specialized at `μ`, are those of the forms `E4.Gforms μ s`. -/
theorem eval₂_macaulayMinorG (μ : Fin 4 → ℂ) (s : Fin 6 → Bool) (D : ℕ)
    (S : monomialsOfDegree (Fin 3) D → macaulayRows (Fin 3) (fun _ : Fin 4 => 4) D) :
    eval₂ ZJ.subtype μ (macaulayMinor (Gforms s) (fun _ => 4) D S) =
      macaulayMinor (E4.Gforms μ s) (fun _ => 4) D S := by
  have h := map_macaulayMinor (eval₂Hom ZJ.subtype μ) (Gforms s) (fun _ => 4) D S
  rw [coe_eval₂Hom, show (fun i => map (eval₂Hom ZJ.subtype μ) (Gforms s i)) = E4.Gforms μ s from
    funext (map_Gforms μ s)] at h
  exact h

/-! ## Proposition 7.8 -/

/-- **Proposition 7.8** (`prop:E4`) in polynomial form, given `E4NoZero`: there is a nonzero
`P ∈ ℤ[μ₁, …, μ₄]` that vanishes on the set `B_E`, the union of `{μ₁μ₂μ₃μ₄ = 0}` and of the set of `μ ∈ ℂ⁴` for
which some `ℱ_ε` (`E4.Fforms μ e`) or some `𝒢_σ` (`E4.Gforms μ s`) has a common zero `≠ 0`. For each pattern,
`exists_macaulayMinor_ne_zero_of_noZero` gives a degree and a maximal minor that does not vanish at `μ₀`; the
polynomial is `h h̄` (`exists_int_poly`) for the product `h` of these minors and of `μ₁μ₂μ₃μ₄`. -/
theorem prop_E4_poly_of_noZero (hZ : E4NoZero) : ∃ P : MvPolynomial (Fin 4) ℤ, P ≠ 0 ∧ ∀ μ : Fin 4 → ℂ,
    ((∃ e : Fin 6 → ZMod 3, ∃ q : Fin 4 → ℂ, q ≠ 0 ∧ ∀ i, eval q (E4.Fforms μ e i) = 0) ∨
      (∃ s : Fin 6 → Bool, ∃ y : Fin 3 → ℂ, y ≠ 0 ∧ ∀ k, eval y (E4.Gforms μ s k) = 0) ∨
        μ 0 * μ 1 * μ 2 * μ 3 = 0) → aeval μ P = 0 := by
  obtain ⟨hF, hG⟩ := hZ
  have hF' : ∀ e : Fin 6 → ZMod 3, ∃ D : ℕ,
      ∃ S : monomialsOfDegree (Fin 4) D → macaulayRows (Fin 4) (fun _ : Fin 7 => 3) D,
        eval₂ ZJ.subtype μ₀ (macaulayMinor (Fforms e) (fun _ => 3) D S) ≠ 0 := by
    intro e
    obtain ⟨D, S, hS⟩ :=
      exists_macaulayMinor_ne_zero_of_noZero (E4.Fforms μ₀ e) (E4Fforms_hom μ₀ e) (hF e)
    exact ⟨D, S, by rwa [eval₂_macaulayMinorF]⟩
  have hG' : ∀ s : Fin 6 → Bool, ∃ D : ℕ,
      ∃ S : monomialsOfDegree (Fin 3) D → macaulayRows (Fin 3) (fun _ : Fin 4 => 4) D,
        eval₂ ZJ.subtype μ₀ (macaulayMinor (Gforms s) (fun _ => 4) D S) ≠ 0 := by
    intro s
    obtain ⟨D, S, hS⟩ :=
      exists_macaulayMinor_ne_zero_of_noZero (E4.Gforms μ₀ s) (E4Gforms_hom μ₀ s) (hG s)
    exact ⟨D, S, by rwa [eval₂_macaulayMinorG]⟩
  choose DF SF hSF using hF'
  choose DG SG hSG using hG'
  obtain ⟨h, hh⟩ : ∃ h : MvPolynomial (Fin 4) ZJ,
      h = (∏ e, macaulayMinor (Fforms e) (fun _ => 3) (DF e) (SF e)) *
        (∏ s, macaulayMinor (Gforms s) (fun _ => 4) (DG s) (SG s)) * (X 0 * X 1 * X 2 * X 3) := ⟨_, rfl⟩
  have hev : ∀ μ : Fin 4 → ℂ, eval₂ ZJ.subtype μ h =
      (∏ e, eval₂ ZJ.subtype μ (macaulayMinor (Fforms e) (fun _ => 3) (DF e) (SF e))) *
        (∏ s, eval₂ ZJ.subtype μ (macaulayMinor (Gforms s) (fun _ => 4) (DG s) (SG s))) *
          (μ 0 * μ 1 * μ 2 * μ 3) := by
    intro μ
    rw [hh, eval₂_mul, eval₂_mul, eval₂_prod, eval₂_prod]
    simp only [eval₂_mul, eval₂_X]
  have h0 : eval₂ ZJ.subtype μ₀ h ≠ 0 := by
    rw [hev]
    refine mul_ne_zero (mul_ne_zero (prod_ne_zero_iff.mpr fun e _ => hSF e)
      (prod_ne_zero_iff.mpr fun s _ => hSG s)) ?_
    norm_num [μ₀]
  obtain ⟨P, hP0, hP⟩ := exists_int_poly h fun h' => h0 (by rw [h', eval₂_zero])
  refine ⟨P, hP0, fun μ hμ => hP μ ?_⟩
  rw [hev]
  rcases hμ with ⟨e, q, hq0, hq⟩ | ⟨s, y, hy0, hy⟩ | hμ0
  · have hz : eval₂ ZJ.subtype μ (macaulayMinor (Fforms e) (fun _ => 3) (DF e) (SF e)) = 0 := by
      by_contra hne
      rw [← coe_eval₂Hom] at hne
      exact hq0 (eq_zero_of_map_macaulayMinor_ne_zero (eval₂Hom ZJ.subtype μ) (Fforms e) (Fforms_hom e)
        (SF e) hne q fun i => by rw [map_Fforms]; exact hq i)
    exact mul_eq_zero.mpr (Or.inl (mul_eq_zero.mpr (Or.inl (prod_eq_zero (mem_univ e) hz))))
  · have hz : eval₂ ZJ.subtype μ (macaulayMinor (Gforms s) (fun _ => 4) (DG s) (SG s)) = 0 := by
      by_contra hne
      rw [← coe_eval₂Hom] at hne
      exact hy0 (eq_zero_of_map_macaulayMinor_ne_zero (eval₂Hom ZJ.subtype μ) (Gforms s) (Gforms_hom s)
        (SG s) hne y fun k => by rw [map_Gforms]; exact hy k)
    exact mul_eq_zero.mpr (Or.inl (mul_eq_zero.mpr (Or.inr (prod_eq_zero (mem_univ s) hz))))
  · exact mul_eq_zero.mpr (Or.inr hμ0)

end E4P

/-! ## Theorem 7.12 -/

/-- **Theorem 7.12** (`thm:d64`), the polynomial, given the fact `E4NoZero` at `μ₀ = (3, 5, 7, 11)`: there is a
nonzero `P ∈ ℤ[m₁, …, m₆]` with `P(m) = 0` for all positive masses `m` that have a germ (a singular place) with
diagram `64` in the labelling of Table 1. `P` is the polynomial of Proposition 7.8 (`E4P.prop_E4_poly_of_noZero`)
in the masses `m_K = (m₃, m₄, m₅, m₆)` of the `z`-cluster `K = {3, 4, 5, 6}` (bodies `2, …, 5` in Lean): by Lemmas
7.2, 7.3 and 7.6 (`Germ.d64_forms`), some `ℱ_ε` or `𝒢_σ` at `μ = m_K` has a common zero `≠ 0`, so `m_K ∈ B_E`. -/
theorem d64_poly_of_noZero (h : E4NoZero) : ∃ P : MvPolynomial (Fin 6) ℤ, P ≠ 0 ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram Diagram.d64 →
      MvPolynomial.aeval m P = 0 := by
  obtain ⟨P, hP0, hP⟩ := E4P.prop_E4_poly_of_noZero h
  refine ⟨rename K4.emb P, fun h0 => hP0 ?_, fun m hm G hD => ?_⟩
  · have h1 : rename K4.emb P = rename K4.emb (0 : MvPolynomial (Fin 4) ℤ) := by
      rw [h0, map_zero]
    exact rename_injective _ E4P.emb_injective h1
  · rw [aeval_rename]
    refine E4P.aeval_eq_zero_of_ofReal (m := m ∘ K4.emb) (hP (K4.muK m) ?_)
    rcases G.d64_forms hm hD with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end

end CC6Full.Six
