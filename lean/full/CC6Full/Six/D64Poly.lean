import CC6Full.Six.D64
import CC6Full.Six.D64PolyForms
import CC6Full.Algebra.Macaulay

/-!
# Diagram 64: the polynomial of Theorem 7.12 (`thm:d64`)

Theorem 7.12 of the paper: at a singular place with diagram `64`, the masses `m_K` of the `z`-cluster
`K = {3, 4, 5, 6}` lie in the set `B_E` of Proposition 7.8 (`prop:E4`). Here `B_E` is replaced by the zero set of
one nonzero polynomial with integer coefficients, and the computation at the mass point `μ₀ = (3, 5, 7, 11)`
reported after Proposition 7.8 is taken as a hypothesis (`E4Cert`).

* `E4Cert`: for each of the `3⁶` patterns `ε` (resp. `2⁶` patterns `σ`), some square submatrix of rows of the
  Macaulay matrix in degree `7` of `ℱ_ε` (resp. in degree `8` of `𝒢_σ`), with entries in `ℤ[j][μ]`, has a nonzero
  determinant at `μ = μ₀`. (`E4Cert_iff`: equivalently, the Macaulay matrices of the forms `E4.Fforms μ₀ e` and
  `E4.Gforms μ₀ s` with complex coefficients have nonzero maximal minors.)
* `E4P.prop_E4_poly`: **Proposition 7.8** in polynomial form: there is a nonzero `P ∈ ℤ[μ₁, …, μ₄]` that vanishes
  on `B_E`, that is, at every `μ ∈ ℂ⁴` with `μ₁μ₂μ₃μ₄ = 0` or for which some `ℱ_ε` or `𝒢_σ` has a common zero
  `≠ 0`.
* `d64_poly`: **Theorem 7.12**, the polynomial: `P ≠ 0` in `ℤ[m₁, …, m₆]` and `P(m) = 0` for all positive masses
  that have a germ with diagram `64`.

## The proof

The choices of `E4Cert` give, for each pattern, a maximal minor `h_ε` (resp. `h_σ`) of the Macaulay matrix, a
polynomial in the masses with coefficients in `ℤ[j]`. Let `h = Π_ε h_ε · Π_σ h_σ · μ₁μ₂μ₃μ₄`; then `h(μ₀) ≠ 0`.
If `h_ε(μ) ≠ 0`, every monomial of degree `7` lies in the ideal of the specialized forms `ℱ_ε(μ)`, so they have no
common zero `q ≠ 0` (`eq_zero_of_map_macaulayMinor_ne_zero`, the Macaulay transfer); hence `h` vanishes on `B_E`.
For integer coefficients (`E4P.exists_int_poly`): with `H` the image of `h` in `ℂ[μ]` and `H̄` the polynomial with
the conjugate coefficients, `H H̄` has coefficients in `ℤ[j]` that are fixed by conjugation, hence integers since
`ℤ[j] ∩ ℝ = ℤ`; it is nonzero and vanishes wherever `H` does. Finally, `Germ.d64_forms` (Lemmas 7.2, 7.3 and 7.6)
puts `m_K` in `B_E`, and the masses `μ₁, …, μ₄` are renamed to the bodies `3, 4, 5, 6` (`K4.emb`).
-/

namespace CC6Full.Six

open MvPolynomial Finset ComplexConjugate

noncomputable section

namespace E4P

/-- The mass point `μ₀ = (3, 5, 7, 11)` of the computation reported after Proposition 7.8 (`prop:E4`). -/
def μ₀ : Fin 4 → ℂ := ![3, 5, 7, 11]

end E4P

/-- **The certificate fact at `μ₀ = (3, 5, 7, 11)`** (the computation reported after Proposition 7.8, `prop:E4`):
for each of the `3⁶` symmetric patterns `ε` (`e : Fin 6 → ZMod 3`), some square submatrix of rows (rows chosen by
`S`, all `120` columns) of the Macaulay matrix in degree `7` of the cubic forms `ℱ_ε` with coefficients in
`ℤ[j][μ₁, …, μ₄]` (`E4P.Fforms e`) has a determinant that does not vanish at `μ = μ₀`, and for each of the `2⁶`
antisymmetric sign patterns `σ` (`s : Fin 6 → Bool`), the same holds for the Macaulay matrix in degree `8` (`45`
columns) of the quartic forms `𝒢_σ` (`E4P.Gforms s`). The evaluation at `μ₀` is `eval₂ E4P.ZJ.subtype E4P.μ₀`. -/
def E4Cert : Prop :=
  (∀ e : Fin 6 → ZMod 3, ∃ S : monomialsOfDegree (Fin 4) 7 → macaulayRows (Fin 4) (fun _ : Fin 7 => 3) 7,
      eval₂ E4P.ZJ.subtype E4P.μ₀ ((macaulayMatrix (E4P.Fforms e) (fun _ => 3) 7).submatrix S id).det ≠ 0) ∧
    ∀ s : Fin 6 → Bool, ∃ S : monomialsOfDegree (Fin 3) 8 → macaulayRows (Fin 3) (fun _ : Fin 4 => 4) 8,
      eval₂ E4P.ZJ.subtype E4P.μ₀ ((macaulayMatrix (E4P.Gforms s) (fun _ => 4) 8).submatrix S id).det ≠ 0

namespace E4P

/-- The determinants of `E4Cert`, specialized at `μ`, are the maximal minors of the Macaulay matrices of the forms
`ℱ_ε` of Lemma 7.6 at `μ` (`E4.Fforms μ e`). -/
theorem eval₂_minorF (μ : Fin 4 → ℂ) (e : Fin 6 → ZMod 3)
    (S : monomialsOfDegree (Fin 4) 7 → macaulayRows (Fin 4) (fun _ : Fin 7 => 3) 7) :
    eval₂ ZJ.subtype μ ((macaulayMatrix (Fforms e) (fun _ => 3) 7).submatrix S id).det =
      ((macaulayMatrix (E4.Fforms μ e) (fun _ => 3) 7).submatrix S id).det := by
  have h := map_macaulayMinor (eval₂Hom ZJ.subtype μ) (Fforms e) (fun _ => 3) 7 S
  rw [coe_eval₂Hom, show (fun i => map (eval₂Hom ZJ.subtype μ) (Fforms e i)) = E4.Fforms μ e from
    funext (map_Fforms μ e)] at h
  exact h

/-- The determinants of `E4Cert`, specialized at `μ`, are the maximal minors of the Macaulay matrices of the forms
`𝒢_σ` of Lemma 7.6 at `μ` (`E4.Gforms μ s`). -/
theorem eval₂_minorG (μ : Fin 4 → ℂ) (s : Fin 6 → Bool)
    (S : monomialsOfDegree (Fin 3) 8 → macaulayRows (Fin 3) (fun _ : Fin 4 => 4) 8) :
    eval₂ ZJ.subtype μ ((macaulayMatrix (Gforms s) (fun _ => 4) 8).submatrix S id).det =
      ((macaulayMatrix (E4.Gforms μ s) (fun _ => 4) 8).submatrix S id).det := by
  have h := map_macaulayMinor (eval₂Hom ZJ.subtype μ) (Gforms s) (fun _ => 4) 8 S
  rw [coe_eval₂Hom, show (fun i => map (eval₂Hom ZJ.subtype μ) (Gforms s i)) = E4.Gforms μ s from
    funext (map_Gforms μ s)] at h
  exact h

end E4P

/-- `E4Cert` in terms of the forms of Lemma 7.6 at `μ₀` with complex coefficients: for every pattern, the Macaulay
matrix of `E4.Fforms μ₀ e` in degree `7` (resp. of `E4.Gforms μ₀ s` in degree `8`) has a nonzero maximal minor. -/
theorem E4Cert_iff : E4Cert ↔
    (∀ e : Fin 6 → ZMod 3, ∃ S : monomialsOfDegree (Fin 4) 7 → macaulayRows (Fin 4) (fun _ : Fin 7 => 3) 7,
        ((macaulayMatrix (E4.Fforms E4P.μ₀ e) (fun _ => 3) 7).submatrix S id).det ≠ 0) ∧
      ∀ s : Fin 6 → Bool, ∃ S : monomialsOfDegree (Fin 3) 8 → macaulayRows (Fin 3) (fun _ : Fin 4 => 4) 8,
        ((macaulayMatrix (E4.Gforms E4P.μ₀ s) (fun _ => 4) 8).submatrix S id).det ≠ 0 := by
  simp only [E4Cert, E4P.eval₂_minorF, E4P.eval₂_minorG]

namespace E4P

/-! ## Integer coefficients -/

/-- A nonzero polynomial `h` with coefficients in `ℤ[j]` gives a nonzero polynomial `P` with integer coefficients
that vanishes wherever `h` does: `P = h h̄`, where `h̄` has the conjugate coefficients. The coefficients of `h h̄`
lie in `ℤ[j]` and are fixed by complex conjugation, so they are integers (`eq_intCast_of_mem_ZJ`). -/
theorem exists_int_poly {σ : Type*} (h : MvPolynomial σ ZJ) (h0 : h ≠ 0) :
    ∃ P : MvPolynomial σ ℤ, P ≠ 0 ∧ ∀ μ : σ → ℂ, eval₂ ZJ.subtype μ h = 0 → aeval μ P = 0 := by
  classical
  obtain ⟨H, hH⟩ : ∃ H : MvPolynomial σ ℂ, H = map ZJ.subtype h := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial σ ℂ, Q = H * map (starRingEnd ℂ) H := ⟨_, rfl⟩
  have hHmem : ∀ v, H.coeff v ∈ ZJ := fun v => by
    rw [hH, coeff_map]
    exact (h.coeff v).2
  have hmem : ∀ v, Q.coeff v ∈ ZJ := by
    intro v
    rw [hQ, coeff_mul]
    exact sum_mem fun x _ => mul_mem (hHmem _) (by rw [coeff_map]; exact conj_mem_ZJ (hHmem _))
  have hconj : map (starRingEnd ℂ) Q = Q := by
    have hid : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ :=
      RingHom.ext fun x => starRingEnd_self_apply x
    rw [hQ, map_mul, MvPolynomial.map_map, hid, map_id, mul_comm]
  have hint : ∀ v, ∃ n : ℤ, Q.coeff v = n := by
    intro v
    refine eq_intCast_of_mem_ZJ (hmem v) ?_
    have h1 : (map (starRingEnd ℂ) Q).coeff v = Q.coeff v := by rw [hconj]
    rwa [coeff_map] at h1
  obtain ⟨P, hP⟩ : Q ∈ Set.range (map (Int.castRingHom ℂ)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨v, -, rfl⟩ := mem_coeffs_iff.mp (Finset.mem_coe.mp hc)
    obtain ⟨n, hn⟩ := hint v
    exact ⟨n, by rw [hn, eq_intCast]⟩
  have hHne : H ≠ 0 := by
    rw [hH]
    intro h1
    exact h0 (map_injective _ (fun a b hab => Subtype.ext hab) (by rw [h1, map_zero]))
  have hHcne : map (starRingEnd ℂ) H ≠ 0 := by
    intro h1
    exact hHne (map_injective _ (starRingEnd ℂ).injective (by rw [h1, map_zero]))
  refine ⟨P, ?_, fun μ hμ => ?_⟩
  · rintro rfl
    rw [map_zero, hQ] at hP
    exact mul_ne_zero hHne hHcne hP.symm
  · rw [aeval_def, algebraMap_int_eq, ← eval_map, hP, hQ, eval_mul, hH, eval_map, hμ, zero_mul]

/-! ## Proposition 7.8 -/

/-- **Proposition 7.8** (`prop:E4`) in polynomial form, given the certificate fact `E4Cert` at
`μ₀ = (3, 5, 7, 11)`: there is a nonzero `P ∈ ℤ[μ₁, …, μ₄]` that vanishes on the set `B_E`, the union of
`{μ₁μ₂μ₃μ₄ = 0}` and of the set of `μ ∈ ℂ⁴` for which some `ℱ_ε` (`E4.Fforms μ e`) or some `𝒢_σ`
(`E4.Gforms μ s`) has a common zero `≠ 0`. The polynomial is `h h̄` (`exists_int_poly`) for the product `h` of
`μ₁μ₂μ₃μ₄` and of the maximal minors chosen by `E4Cert`, which is nonzero at `μ₀`. -/
theorem prop_E4_poly (hC : E4Cert) : ∃ P : MvPolynomial (Fin 4) ℤ, P ≠ 0 ∧ ∀ μ : Fin 4 → ℂ,
    ((∃ e : Fin 6 → ZMod 3, ∃ q : Fin 4 → ℂ, q ≠ 0 ∧ ∀ i, eval q (E4.Fforms μ e i) = 0) ∨
      (∃ s : Fin 6 → Bool, ∃ y : Fin 3 → ℂ, y ≠ 0 ∧ ∀ k, eval y (E4.Gforms μ s k) = 0) ∨
        μ 0 * μ 1 * μ 2 * μ 3 = 0) → aeval μ P = 0 := by
  obtain ⟨hF, hG⟩ := hC
  choose SF hSF using hF
  choose SG hSG using hG
  obtain ⟨h, hh⟩ : ∃ h : MvPolynomial (Fin 4) ZJ,
      h = (∏ e, macaulayMinor (Fforms e) (fun _ => 3) 7 (SF e)) *
        (∏ s, macaulayMinor (Gforms s) (fun _ => 4) 8 (SG s)) * (X 0 * X 1 * X 2 * X 3) := ⟨_, rfl⟩
  have hev : ∀ μ : Fin 4 → ℂ, eval₂ ZJ.subtype μ h =
      (∏ e, eval₂ ZJ.subtype μ (macaulayMinor (Fforms e) (fun _ => 3) 7 (SF e))) *
        (∏ s, eval₂ ZJ.subtype μ (macaulayMinor (Gforms s) (fun _ => 4) 8 (SG s))) *
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
  · have hz : eval₂ ZJ.subtype μ (macaulayMinor (Fforms e) (fun _ => 3) 7 (SF e)) = 0 := by
      by_contra hne
      rw [← coe_eval₂Hom] at hne
      exact hq0 (eq_zero_of_map_macaulayMinor_ne_zero (eval₂Hom ZJ.subtype μ) (Fforms e) (Fforms_hom e)
        (SF e) hne q fun i => by rw [map_Fforms]; exact hq i)
    exact mul_eq_zero.mpr (Or.inl (mul_eq_zero.mpr (Or.inl (prod_eq_zero (mem_univ e) hz))))
  · have hz : eval₂ ZJ.subtype μ (macaulayMinor (Gforms s) (fun _ => 4) 8 (SG s)) = 0 := by
      by_contra hne
      rw [← coe_eval₂Hom] at hne
      exact hy0 (eq_zero_of_map_macaulayMinor_ne_zero (eval₂Hom ZJ.subtype μ) (Gforms s) (Gforms_hom s)
        (SG s) hne y fun k => by rw [map_Gforms]; exact hy k)
    exact mul_eq_zero.mpr (Or.inl (mul_eq_zero.mpr (Or.inr (prod_eq_zero (mem_univ s) hz))))
  · exact mul_eq_zero.mpr (Or.inr hμ0)

/-! ## Theorem 7.12 -/

/-- The renumbering `K4.emb` of the bodies of `K = {3, 4, 5, 6}` is injective. -/
theorem emb_injective : Function.Injective K4.emb := fun a b h => by
  by_contra hab
  exact K4.emb_ne hab h

/-- A polynomial with integer coefficients that vanishes at the complex point `m` (real) vanishes at `m`. -/
theorem aeval_eq_zero_of_ofReal {ι : Type*} {m : ι → ℝ} {P : MvPolynomial ι ℤ}
    (h : aeval (fun k => (m k : ℂ)) P = 0) : aeval m P = 0 := by
  have h' := aeval_algebraMap_apply ℂ m P
  rw [Complex.coe_algebraMap] at h'
  exact Complex.ofReal_eq_zero.mp (h'.symm.trans h)

end E4P

/-- **Theorem 7.12** (`thm:d64`), the polynomial, given the certificate fact `E4Cert` at `μ₀ = (3, 5, 7, 11)`:
there is a nonzero `P ∈ ℤ[m₁, …, m₆]` with `P(m) = 0` for all positive masses `m` that have a germ (a singular
place) with diagram `64` in the labelling of Table 1. `P` is the polynomial of Proposition 7.8 (`E4P.prop_E4_poly`)
in the masses `m_K = (m₃, m₄, m₅, m₆)` of the `z`-cluster `K = {3, 4, 5, 6}` (bodies `2, …, 5` in Lean): by Lemmas
7.2, 7.3 and 7.6 (`Germ.d64_forms`), some `ℱ_ε` or `𝒢_σ` at `μ = m_K` has a common zero `≠ 0`, so `m_K ∈ B_E`. -/
theorem d64_poly (hC : E4Cert) : ∃ P : MvPolynomial (Fin 6) ℤ, P ≠ 0 ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram Diagram.d64 →
      MvPolynomial.aeval m P = 0 := by
  obtain ⟨P, hP0, hP⟩ := E4P.prop_E4_poly hC
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
