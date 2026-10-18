import CC6Full.Six.ThreeDefs
import CC6Full.Algebra.Elim

/-!
# Integral elimination for the leading systems of Theorems 6.12 and 6.15

Theorems 6.12 (`thm:d98`) and 6.15 (`thm:d93`) of the paper end with a nonzero polynomial in the masses that
vanishes whenever a polynomial system in auxiliary unknowns (the shapes of the triangles and the normalized cross
coefficients) has a complex solution. The paper takes resultants (two in Theorem 6.12, one in Theorem 6.15).
Here the polynomial comes from the integral elimination lemma `CC6Full.elim_integral_int`
(`CC6Full/Algebra/Elim.lean`): it suffices that every unknown is integral over `ℚ[μ][1/g]` modulo the system, and
that the system has no complex solution at one rational parameter point where `g` does not vanish.

`elim_integral_int` takes the integrality equations with coefficients in `ℚ[μ]`. A shape is a root of `S_μ`, whose
leading coefficient `(μ₁ + μ₂)⁴` lies in `ℚ[μ]`, but a cross coefficient `c` only satisfies `c² = Y` with `Y` a
polynomial in the parameters and the shapes, so its integrality is transitive. This file supplies the transitivity
in the form needed:

* `gInt φ g`: for `φ : A →+* Q` and `g : A`, the subring of the `y ∈ Q` such that `φ(g)^a y` is integral over `A`
  for some `a` (the elements integral over `A[1/g]`);
* `mem_gInt_of_sq`: `gInt φ g` is closed under square roots (`IsIntegral.of_pow`);
* `eval₂_mem_gInt`: it contains `p(y)` for `p ∈ A[t]` and `y ∈ gInt φ g`;
* `mem_gInt_of_Sμ`: it contains the roots of `S_μ` (entries of `μ` in `A`) if `(μ₁ + μ₂)⁴ ≠ 0` and `g^a` is a
  multiple of it (`RingHom.isIntegralElem_leadingCoeff_mul`);
* `hint_of_mem_gInt`: an unknown whose class modulo the system lies in `gInt` satisfies an equation of the form
  required by `elim_integral_int`;
* `elim_gInt`: `elim_integral_int` with the integrality hypothesis in this form.

It also contains the evaluation of `S_μ` and `Λ_k` under ring homomorphisms (`hom_eval₂_Sμ`, `hom_eval₂_LamP`), the
identity `ℓ_k Λ_k = ℓ₁ ℓ₂ ℓ₃` (`ellP_mul_LamP`), and two facts used by both theorems (`Mμ_mass_ne_zero`,
`aeval_real_eq_zero`).
-/

namespace CC6Full.Six

open MvPolynomial

noncomputable section

/-! ## Elements integral over `A[1/g]` -/

section GInt

variable {A Q : Type*} [CommRing A] [CommRing Q] (φ : A →+* Q) (g : A)

/-- The elements `y ∈ Q` integral over `A[1/g]` (through `φ : A →+* Q`): `φ(g)^a y` is integral over `A` for some
`a`. They form a subring of `Q`. -/
def gInt : Subring Q where
  carrier := {y | ∃ a : ℕ, φ.IsIntegralElem (φ g ^ a * y)}
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [show φ g ^ (a + b) * (x * y) = (φ g ^ a * x) * (φ g ^ b * y) by ring]
    exact ha.mul φ hb
  one_mem' := ⟨0, by rw [pow_zero, one_mul]; exact φ.isIntegralElem_one⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [show φ g ^ (a + b) * (x + y) = φ (g ^ b) * (φ g ^ a * x) + φ (g ^ a) * (φ g ^ b * y) by
      rw [map_pow, map_pow]; ring]
    exact (φ.isIntegralElem_map.mul φ ha).add φ (φ.isIntegralElem_map.mul φ hb)
  zero_mem' := ⟨0, by rw [mul_zero]; exact φ.isIntegralElem_zero⟩
  neg_mem' := by
    rintro x ⟨a, ha⟩
    exact ⟨a, by rw [mul_neg]; exact ha.neg φ⟩

theorem mem_gInt {y : Q} : y ∈ gInt φ g ↔ ∃ a : ℕ, φ.IsIntegralElem (φ g ^ a * y) := Iff.rfl

/-- The image of `A` lies in `gInt φ g`. -/
theorem map_mem_gInt (x : A) : φ x ∈ gInt φ g :=
  (mem_gInt φ g).mpr ⟨0, by rw [pow_zero, one_mul]; exact φ.isIntegralElem_map⟩

/-- `gInt φ g` is closed under square roots: if `φ(g)^a y²` is integral over `A`, so is
`(φ(g)^a y)² = φ(g^a) · φ(g)^a y²`, and then `φ(g)^a y` (`IsIntegral.of_pow`). -/
theorem mem_gInt_of_sq {y : Q} (h : y ^ 2 ∈ gInt φ g) : y ∈ gInt φ g := by
  obtain ⟨a, ha⟩ := (mem_gInt φ g).mp h
  refine (mem_gInt φ g).mpr ⟨a, ?_⟩
  let _ : Algebra A Q := φ.toAlgebra
  have h2 : IsIntegral A ((φ g ^ a * y) ^ 2) := by
    show φ.IsIntegralElem _
    rw [show (φ g ^ a * y) ^ 2 = φ (g ^ a) * (φ g ^ a * y ^ 2) by rw [map_pow]; ring]
    exact φ.isIntegralElem_map.mul φ ha
  exact IsIntegral.of_pow two_pos h2

/-- `p(y) ∈ gInt φ g` for `p ∈ A[t]` and `y ∈ gInt φ g`. -/
theorem eval₂_mem_gInt {y : Q} (hy : y ∈ gInt φ g) (p : Polynomial A) : p.eval₂ φ y ∈ gInt φ g := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (map_mem_gInt φ g _) (pow_mem hy _)

/-- The leading coefficient of `S_μ` is `(μ₁ + μ₂)⁴` when this is nonzero (§6.4). -/
theorem leadingCoeff_Sμ {R : Type*} [CommRing R] (μ : Fin 3 → R) (h : (μ 0 + μ 1) ^ 4 ≠ 0) :
    (Sμ μ).leadingCoeff = (μ 0 + μ 1) ^ 4 := by
  have h34 : (Sμ μ).natDegree = 34 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (natDegree_Sμ_le μ) (by rw [coeff_Sμ_34]; exact h)
  rw [Polynomial.leadingCoeff, h34, coeff_Sμ_34]

/-- A root `y` of `S_μ` (through `φ`, with `μ` in `A`) lies in `gInt φ g` if `(μ₁ + μ₂)⁴ ≠ 0` and
`g^a = u (μ₁ + μ₂)⁴`: then `φ(g)^a y = φ(u) · φ((μ₁ + μ₂)⁴) y`, and the second factor is integral over `A`, since
`(μ₁ + μ₂)⁴` is the leading coefficient of `S_μ` (`RingHom.isIntegralElem_leadingCoeff_mul`). -/
theorem mem_gInt_of_Sμ (μ : Fin 3 → A) (hlc : (μ 0 + μ 1) ^ 4 ≠ 0) {a : ℕ} {u : A}
    (hg : g ^ a = u * (μ 0 + μ 1) ^ 4) {y : Q} (hy : (Sμ μ).eval₂ φ y = 0) : y ∈ gInt φ g := by
  refine (mem_gInt φ g).mpr ⟨a, ?_⟩
  have h := φ.isIntegralElem_leadingCoeff_mul (Sμ μ) y hy
  rw [leadingCoeff_Sμ μ hlc] at h
  rw [← map_pow, hg, map_mul, mul_assoc]
  exact φ.isIntegralElem_map.mul φ h

end GInt

/-! ## Integral elimination with integrality in `gInt` -/

/-- **The integrality equation of an unknown in `gInt`.** Let `φ : ℚ[μ] → ℚ[μ, x]/(S)`. If the class of the unknown
`x_i` lies in `gInt φ g`, then `g^a x_i^d + Σ_{j<d} c_j x_i^j ∈ (S)` for some `a`, `d` and `c_j ∈ ℚ[μ]`, the form of
the hypothesis of `elim_integral_int`: if `p` is monic of degree `d` with `p(φ(g)^a x_i) = 0`, then
`g^{ad} x_i^d + Σ_{j<d} p_j g^{aj} x_i^j` maps to `p(φ(g)^a x_i) = 0`. -/
theorem hint_of_mem_gInt {ι κ : Type*} {S : Set (MvPolynomial (ι ⊕ κ) ℚ)} {g : MvPolynomial ι ℚ} {i : κ}
    (h : Ideal.Quotient.mk (Ideal.span S) (X (Sum.inr i)) ∈
      gInt ((Ideal.Quotient.mk (Ideal.span S)).comp (rename Sum.inl).toRingHom) g) :
    ∃ (a d : ℕ) (c : Fin d → MvPolynomial ι ℚ),
      rename Sum.inl (g ^ a) * X (Sum.inr i) ^ d +
        ∑ j : Fin d, rename Sum.inl (c j) * X (Sum.inr i) ^ (j : ℕ) ∈ Ideal.span S := by
  obtain ⟨a, p, hp, hev⟩ := (mem_gInt _ g).mp h
  refine ⟨a * p.natDegree, p.natDegree, fun j => p.coeff j * g ^ (a * j), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine Eq.trans ?_ hev
  conv_rhs => rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul,
    Finset.sum_range, add_comm]
  simp only [map_add, map_mul, map_pow, map_sum, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by ring

/-- **Integral elimination, with integrality in `gInt`.** `elim_integral_int` with the hypothesis that the class of
every unknown in `ℚ[μ, x]/(S)` lies in `gInt φ g`, `φ : ℚ[μ] → ℚ[μ, x]/(S)`: then there is `P ∈ ℤ[μ]` with
`P(μ₀) ≠ 0` and `P(μ) = 0` at every `μ ∈ ℂ^ι` for which `S` has a complex solution. -/
theorem elim_gInt {ι κ : Type*} (S : Set (MvPolynomial (ι ⊕ κ) ℚ)) (g : MvPolynomial ι ℚ)
    (hint : ∀ i : κ, Ideal.Quotient.mk (Ideal.span S) (X (Sum.inr i)) ∈
      gInt ((Ideal.Quotient.mk (Ideal.span S)).comp (rename Sum.inl).toRingHom) g)
    (μ₀ : ι → ℚ) (hg : eval μ₀ g ≠ 0)
    (hnone : ∀ x : κ → ℂ, ∃ f ∈ S, aeval (Sum.elim (fun k => (μ₀ k : ℂ)) x) f ≠ 0) :
    ∃ P : MvPolynomial ι ℤ, aeval μ₀ P ≠ 0 ∧
      ∀ μ : ι → ℂ, (∃ x : κ → ℂ, ∀ f ∈ S, aeval (Sum.elim μ x) f = 0) → aeval μ P = 0 :=
  elim_integral_int S g (fun i => hint_of_mem_gInt (hint i)) μ₀ hg hnone

/-- `(X_a + X_b)^n ≠ 0` in `ℚ[σ]` (it takes the value `2^n` at `(1, …, 1)`). -/
theorem X_add_X_pow_ne_zero {σ : Type*} (a b : σ) (n : ℕ) : (X a + X b : MvPolynomial σ ℚ) ^ n ≠ 0 := by
  refine pow_ne_zero n fun h => ?_
  have h1 := congrArg (eval fun _ => (1 : ℚ)) h
  norm_num at h1

/-! ## `S_μ` and `Λ_k` under ring homomorphisms -/

section Hom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem map_ellP (f : R →+* S) (μ : Fin 3 → R) (k : Fin 3) : (ellP μ k).map f = ellP (f ∘ μ) k := by
  rcases fin3_cases k with rfl | rfl | rfl <;> simp [ellP, Mμ]

theorem map_LamP (f : R →+* S) (μ : Fin 3 → R) (k : Fin 3) : (LamP μ k).map f = LamP (f ∘ μ) k := by
  simp only [LamP, Polynomial.map_prod, map_ellP]

/-- `F(S_μ(x)) = S_{F ∘ f ∘ μ}(F(x))` for `S_μ` evaluated through `f`. -/
theorem hom_eval₂_Sμ (F : S →+* T) (f : R →+* S) (μ : Fin 3 → R) (x : S) :
    F ((Sμ μ).eval₂ f x) = (Sμ fun k => F (f (μ k))).eval (F x) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_eq_eval_map (F.comp f)]
  exact congrArg (Polynomial.eval (F x)) (map_Sμ (F.comp f) μ)

/-- `F(Λ_k(x; μ)) = Λ_k(F(x); F ∘ f ∘ μ)` for `Λ_k` evaluated through `f`. -/
theorem hom_eval₂_LamP (F : S →+* T) (f : R →+* S) (μ : Fin 3 → R) (k : Fin 3) (x : S) :
    F ((LamP μ k).eval₂ f x) = (LamP (fun k => F (f (μ k))) k).eval (F x) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_eq_eval_map (F.comp f)]
  exact congrArg (Polynomial.eval (F x)) (map_LamP (F.comp f) μ k)

/-- `ℓ_k Λ_k = ℓ₁ ℓ₂ ℓ₃` (§6.4). -/
theorem ellP_mul_LamP (μ : Fin 3 → R) (t : R) (k : Fin 3) :
    (ellP μ k).eval t * (LamP μ k).eval t = (ellP μ 0).eval t * (ellP μ 1).eval t * (ellP μ 2).eval t := by
  rcases fin3_cases k with rfl | rfl | rfl
  · rw [LamP_zero, Polynomial.eval_mul]; ring
  · rw [LamP_one, Polynomial.eval_mul]; ring
  · rw [LamP_two, Polynomial.eval_mul]; ring

end Hom

/-! ## Masses -/

/-- The total mass `M_μ` of three positive masses `μ_j = m_{e(j)}` is nonzero. -/
theorem Mμ_mass_ne_zero {m : Fin 6 → ℝ} (hm : ∀ i, 0 < m i) (e : Fin 3 → Fin 6) :
    Mμ (fun j => (m (e j) : ℂ)) ≠ 0 := by
  have h : Mμ (fun j => (m (e j) : ℂ)) = ((m (e 0) + m (e 1) + m (e 2) : ℝ) : ℂ) := by
    simp only [Mμ, Complex.ofReal_add]
  rw [h, Complex.ofReal_ne_zero]
  exact (show (0 : ℝ) < m (e 0) + m (e 1) + m (e 2) by linarith [hm (e 0), hm (e 1), hm (e 2)]).ne'

/-- A polynomial with integer coefficients that vanishes at the complex point `m` (real) vanishes at `m`. -/
theorem aeval_real_eq_zero {ι : Type*} {m : ι → ℝ} {P : MvPolynomial ι ℤ}
    (h : aeval (fun k => (m k : ℂ)) P = 0) : aeval m P = 0 := by
  have h' := aeval_algebraMap_apply ℂ m P
  rw [Complex.coe_algebraMap] at h'
  exact Complex.ofReal_eq_zero.mp (h'.symm.trans h)

end

end CC6Full.Six
