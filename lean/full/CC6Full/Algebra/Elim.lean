import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Integral elimination

Theorems 6.12, 6.15 and 6.20 of the paper (`thm:d98`, `thm:d93`, `thm:d88`) need a nonzero
polynomial in the masses that vanishes at every mass vector for which a polynomial system in
auxiliary unknowns has a complex solution. The paper obtains it from resultants (Theorems 6.12
and 6.15) and from constructible sets (Theorem 6.20). Here that step is replaced by one lemma of
commutative algebra, proved from lying over for integral extensions.

Let `μ = (μ_k)_{k ∈ ι}` be parameters and `x = (x_i)_{i ∈ κ}` unknowns (in the paper `ι = Fin r`
and `κ = Fin N`), let `S ⊆ ℚ[μ, x]` be a set of polynomials, `I = (S)` the ideal it generates,
and `g ∈ ℚ[μ]`. Assume that every unknown is integral over `ℚ[μ][1/g]` modulo `I`: for every `i`
there are `a, d ∈ ℕ` and `c_j ∈ ℚ[μ]` (`j < d`) with `g^a x_i^d + ∑_{j<d} c_j x_i^j ∈ I`. Let
`μ₀ ∈ ℚ^ι` be a parameter point with `g(μ₀) ≠ 0` at which `S` has no complex solution.

* `elim_integral_mem`: the elimination ideal `I ∩ ℚ[μ]` contains some `h` with `h(μ₀) ≠ 0`.
* `elim_integral`: there is `h ∈ ℚ[μ]` with `h(μ₀) ≠ 0` and `h(μ) = 0` (so also `g(μ) h(μ) = 0`)
  at every complex common zero `(μ, x)` of `S`.
* `elim_integral_int`: there is `P ∈ ℤ[μ]` (a positive integer multiple of `h`) with
  `P(μ₀) ≠ 0` and `P(μ) = 0` at every `μ ∈ ℂ^ι` for which `S` has a complex solution.

The set `S` need not be finite. For a `Finset` `S`, pass
`(S : Set (MvPolynomial (Fin r ⊕ Fin N) ℚ))` with the full type, or name the arguments
`(ι := Fin r) (κ := Fin N) (S := ↑S)`.

## Proof

Let `R = ℚ[μ][1/g]` and `B = (ℚ[μ, x]/I)[1/g]`; then `B` is integral over `R`. Let `𝔪 ⊆ R` be
the kernel of the evaluation at `μ₀`, a maximal ideal with residue field `ℚ`. Suppose that the
kernel of `R → B` is contained in `𝔪`. Lying over (`Ideal.exists_ideal_over_maximal_of_isIntegral`)
gives a maximal ideal `𝔫` of `B` over `𝔪`; the field `B/𝔫` is integral over `R/𝔪 = ℚ`, hence
embeds in `ℂ` (`IsAlgClosed.lift`), and the images of the `x_i` are a complex solution at `μ₀`
(`exists_ringHom_complex_of_isIntegral`, `exists_ringHom_complex_of_integral_away`). So some
element `a/g^b` of the kernel is not in `𝔪`: then `a(μ₀) ≠ 0` and `g^c a ∈ I` for some `c`, and
`h = g^c a` lies in `I ∩ ℚ[μ]` with `h(μ₀) ≠ 0`. Every element of `I` vanishes at every common
zero of `S`. For `elim_integral_int` the denominators of `h` are cleared
(`exists_map_int_eq_natCast_mul`).

## Main statements

* `exists_ringHom_complex_of_isIntegral`: a rational point of `R` that kills the kernel of an
  integral extension `R → B` extends to a ring homomorphism `B →+* ℂ`.
* `exists_ringHom_complex_of_integral_away`: the same for `A → Q` when `Q` is generated over `A`
  by elements integral over `A[1/g]` and the point does not vanish at `g`.
* `elim_integral_mem`, `elim_integral`, `elim_integral_int`: integral elimination, as above.
-/

namespace CC6Full

open MvPolynomial

noncomputable section

/-! ### Complex points of integral extensions -/

/-- **Lying over at a rational point.** Let `B` be an integral algebra over a `ℚ`-algebra `R`, and
let `ev : R →+* ℚ` be a rational point of `R` that vanishes on the kernel of `R → B`. Then `ev`
extends to a ring homomorphism `B →+* ℂ`. -/
theorem exists_ringHom_complex_of_isIntegral {R B : Type*} [CommRing R] [CommRing B]
    [Algebra ℚ R] [Algebra R B] [Algebra.IsIntegral R B] (ev : R →+* ℚ)
    (hker : RingHom.ker (algebraMap R B) ≤ RingHom.ker ev) :
    ∃ σ : B →+* ℂ, ∀ z : R, σ (algebraMap R B z) = (ev z : ℂ) := by
  have hev : ∀ q : ℚ, ev (algebraMap ℚ R q) = q := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (ev.comp (algebraMap ℚ R)) (RingHom.id ℚ)) q
  have : (RingHom.ker ev).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective ev fun q => ⟨algebraMap ℚ R q, hev q⟩
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) (RingHom.ker ev) hker
  have := h𝔫max
  let : Field (B ⧸ 𝔫) := Ideal.Quotient.field 𝔫
  let : Algebra ℚ (B ⧸ 𝔫) :=
    ((Ideal.Quotient.mk 𝔫).comp ((algebraMap R B).comp (algebraMap ℚ R))).toAlgebra
  -- the map `R → B ⧸ 𝔫` factors through `ev`
  have hcomp : (algebraMap ℚ (B ⧸ 𝔫)).comp ev = (Ideal.Quotient.mk 𝔫).comp (algebraMap R B) := by
    refine RingHom.ext fun z => ?_
    have hz : z - algebraMap ℚ R (ev z) ∈ 𝔫.under R := by
      rw [h𝔫, RingHom.mem_ker, map_sub, hev, sub_self]
    have hz' : algebraMap R B z - algebraMap R B (algebraMap ℚ R (ev z)) ∈ 𝔫 := by
      rw [← map_sub]
      exact Ideal.mem_comap.mp hz
    exact (Ideal.Quotient.eq.mpr hz').symm
  have : Algebra.IsIntegral ℚ (B ⧸ 𝔫) := ⟨fun y => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact IsIntegral.map_of_comp_eq ev (Ideal.Quotient.mk 𝔫) hcomp
      (Algebra.IsIntegral.isIntegral b)⟩
  let τ : (B ⧸ 𝔫) →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine ⟨τ.toRingHom.comp (Ideal.Quotient.mk 𝔫), fun z => ?_⟩
  have h1 : Ideal.Quotient.mk 𝔫 (algebraMap R B z) = algebraMap ℚ (B ⧸ 𝔫) (ev z) :=
    (RingHom.congr_fun hcomp z).symm
  show τ (Ideal.Quotient.mk 𝔫 (algebraMap R B z)) = _
  rw [h1, AlgHom.commutes, eq_ratCast]

/-- The statement of `exists_ringHom_complex_of_integral_away` for arbitrary localizations `R` of
`A` and `B` of `Q` away from `g`. The proof shows that `B` is integral over `R` and applies
`exists_ringHom_complex_of_isIntegral` to the point of `R` induced by `ev₀`. -/
theorem exists_ringHom_complex_of_away {A Q : Type*} [CommRing A] [CommRing Q] [Algebra ℚ A]
    (R B : Type*) [CommRing R] [CommRing B] [Algebra A R] [Algebra Q B] (φ : A →+* Q) (g : A)
    [IsLocalization.Away g R] [IsLocalization.Away (φ g) B] (ev₀ : A →+* ℚ) (hg : ev₀ g ≠ 0)
    (hgen : ∀ q : Q, q ∈ Subring.closure (Set.range φ ∪ {y | ∃ (a d : ℕ) (c : Fin d → A),
      φ (g ^ a) * y ^ d + ∑ j : Fin d, φ (c j) * y ^ (j : ℕ) = 0}))
    (hker : ∀ (a : A) (c : ℕ), φ (g ^ c * a) = 0 → ev₀ a = 0) :
    ∃ σ : Q →+* ℂ, ∀ a : A, σ (φ a) = (ev₀ a : ℂ) := by
  have hu : IsUnit (((algebraMap Q B).comp φ) g) :=
    IsLocalization.Away.algebraMap_isUnit (S := B) (φ g)
  let : Algebra R B := (IsLocalization.Away.lift (S := R) g hu).toAlgebra
  have key : ∀ a : A, algebraMap R B (algebraMap A R a) = algebraMap Q B (φ a) :=
    IsLocalization.Away.lift_eq (S := R) g hu
  -- the generators of `Q` are integral over `R`
  have hgenI : ∀ y : Q, (∃ (a d : ℕ) (c : Fin d → A),
      φ (g ^ a) * y ^ d + ∑ j : Fin d, φ (c j) * y ^ (j : ℕ) = 0) →
      IsIntegral R (algebraMap Q B y) := by
    rintro y ⟨a, d, c, hy⟩
    have hvg : algebraMap A R g * IsLocalization.Away.invSelf (S := R) g = 1 :=
      IsLocalization.Away.mul_invSelf (S := R) g
    refine ⟨Polynomial.X ^ d + ∑ j : Fin d,
        Polynomial.C (IsLocalization.Away.invSelf (S := R) g ^ a * algebraMap A R (c j)) *
          Polynomial.X ^ (j : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
    have hy' : algebraMap R B (algebraMap A R g) ^ a * algebraMap Q B y ^ d +
        ∑ j : Fin d, algebraMap R B (algebraMap A R (c j)) * algebraMap Q B y ^ (j : ℕ) = 0 := by
      have := congrArg (algebraMap Q B) hy
      simpa only [map_add, map_mul, map_sum, map_pow, map_zero, key] using this
    have hvg' : algebraMap R B (IsLocalization.Away.invSelf (S := R) g) ^ a *
        algebraMap R B (algebraMap A R g) ^ a = 1 := by
      rw [← mul_pow, ← map_mul, mul_comm, hvg, map_one, one_pow]
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow,
      map_mul, map_pow]
    calc algebraMap Q B y ^ d + ∑ j : Fin d,
          algebraMap R B (IsLocalization.Away.invSelf (S := R) g) ^ a *
            algebraMap R B (algebraMap A R (c j)) * algebraMap Q B y ^ (j : ℕ)
        = algebraMap R B (IsLocalization.Away.invSelf (S := R) g) ^ a *
            (algebraMap R B (algebraMap A R g) ^ a * algebraMap Q B y ^ d +
              ∑ j : Fin d, algebraMap R B (algebraMap A R (c j)) * algebraMap Q B y ^ (j : ℕ)) := by
          rw [mul_add, ← mul_assoc, hvg', one_mul, Finset.mul_sum]
          simp only [mul_assoc]
      _ = 0 := by rw [hy', mul_zero]
  -- every element of `Q` is integral over `R`
  have hQ : ∀ q : Q, IsIntegral R (algebraMap Q B q) := by
    have hle : Subring.closure (Set.range φ ∪ {y | ∃ (a d : ℕ) (c : Fin d → A),
        φ (g ^ a) * y ^ d + ∑ j : Fin d, φ (c j) * y ^ (j : ℕ) = 0}) ≤
        (integralClosure R B).toSubring.comap (algebraMap Q B) := by
      rw [Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · rw [SetLike.mem_coe, Subring.mem_comap, Subalgebra.mem_toSubring, mem_integralClosure_iff,
          ← key]
        exact isIntegral_algebraMap
      · rw [SetLike.mem_coe, Subring.mem_comap, Subalgebra.mem_toSubring, mem_integralClosure_iff]
        exact hgenI y hy
    intro q
    have := hle (hgen q)
    rwa [Subring.mem_comap, Subalgebra.mem_toSubring, mem_integralClosure_iff] at this
  -- `B` is integral over `R`
  have : Algebra.IsIntegral R B := ⟨fun b => by
    obtain ⟨⟨q, s⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (φ g)) b
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    dsimp only at hb
    have hs : algebraMap Q B (s : Q) *
        algebraMap R B (IsLocalization.Away.invSelf (S := R) g ^ n) = 1 := by
      rw [← hn, ← map_pow φ, ← key, ← map_mul, map_pow (algebraMap A R), ← mul_pow,
        IsLocalization.Away.mul_invSelf, one_pow, map_one]
    have hb' : b = algebraMap Q B q *
        algebraMap R B (IsLocalization.Away.invSelf (S := R) g ^ n) := by
      rw [← hb, mul_assoc, hs, mul_one]
    rw [hb']
    exact (hQ q).mul isIntegral_algebraMap⟩
  -- the rational point of `R`
  let ev : R →+* ℚ := IsLocalization.Away.lift (S := R) g hg.isUnit
  have hev : ∀ a : A, ev (algebraMap A R a) = ev₀ a := IsLocalization.Away.lift_eq (S := R) g _
  have hker' : RingHom.ker (algebraMap R B) ≤ RingHom.ker ev := by
    intro z hz
    rw [RingHom.mem_ker] at hz ⊢
    obtain ⟨⟨a, s⟩, hzs⟩ := IsLocalization.surj (Submonoid.powers g) z
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    dsimp only at hzs
    have h1 : algebraMap Q B (φ a) = 0 := by
      rw [← key, ← hzs, map_mul, hz, zero_mul]
    obtain ⟨⟨m, hm⟩, hm0⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ g)) B (φ a)).mp h1
    obtain ⟨c, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hm
    have h2 : ev₀ a = 0 := hker a c (by rw [map_mul, map_pow]; exact hm0)
    have h3 := congrArg ev hzs
    rw [map_mul, hev, hev, h2, ← hn, map_pow] at h3
    exact (mul_eq_zero.mp h3).resolve_right (pow_ne_zero _ hg)
  let : Algebra ℚ R := ((algebraMap A R).comp (algebraMap ℚ A)).toAlgebra
  obtain ⟨σ, hσ⟩ := exists_ringHom_complex_of_isIntegral ev hker'
  refine ⟨σ.comp (algebraMap Q B), fun a => ?_⟩
  rw [RingHom.comp_apply, ← key, hσ, hev]

/-- **Lying over at a rational point**, for an `A`-algebra `Q` (through `φ : A →+* Q`) generated
by `φ(A)` and by elements `y` integral over `A[1/g]`, in the form
`φ(g)^a y^d + ∑_{j<d} φ(c_j) y^j = 0`. If `ev₀ : A →+* ℚ` satisfies `ev₀ g ≠ 0` and vanishes at
every `a` with `φ (g ^ c * a) = 0` for some `c`, then `ev₀` extends to a ring homomorphism
`Q →+* ℂ`. -/
theorem exists_ringHom_complex_of_integral_away {A Q : Type*} [CommRing A] [CommRing Q]
    [Algebra ℚ A] (φ : A →+* Q) (g : A) (ev₀ : A →+* ℚ) (hg : ev₀ g ≠ 0)
    (hgen : ∀ q : Q, q ∈ Subring.closure (Set.range φ ∪ {y | ∃ (a d : ℕ) (c : Fin d → A),
      φ (g ^ a) * y ^ d + ∑ j : Fin d, φ (c j) * y ^ (j : ℕ) = 0}))
    (hker : ∀ (a : A) (c : ℕ), φ (g ^ c * a) = 0 → ev₀ a = 0) :
    ∃ σ : Q →+* ℂ, ∀ a : A, σ (φ a) = (ev₀ a : ℂ) :=
  exists_ringHom_complex_of_away (Localization.Away g) (Localization.Away (φ g)) φ g ev₀ hg hgen
    hker

/-! ### Integral elimination -/

/-- Every polynomial in the ideal generated by `S` vanishes at the common complex zeros of `S`. -/
theorem aeval_eq_zero_of_mem_span {σ : Type*} {S : Set (MvPolynomial σ ℚ)}
    {f : MvPolynomial σ ℚ} (hf : f ∈ Ideal.span S) {y : σ → ℂ} (hy : ∀ s ∈ S, aeval y s = 0) :
    aeval y f = 0 := by
  have hle : Ideal.span S ≤ RingHom.ker (aeval y : MvPolynomial σ ℚ →ₐ[ℚ] ℂ) :=
    Ideal.span_le.mpr fun s hs => RingHom.mem_ker.mpr (hy s hs)
  exact RingHom.mem_ker.mp (hle hf)

variable {ι κ : Type*}

/-- **Integral elimination**, algebraic form. Let `S` be a set of polynomials in parameters
`μ = (μ_k)_{k ∈ ι}` and unknowns `x = (x_i)_{i ∈ κ}` over `ℚ`, and `g ∈ ℚ[μ]`. Assume that every
unknown is integral over `ℚ[μ][1/g]` modulo the ideal `(S)`: `g^a x_i^d + ∑_{j<d} c_j x_i^j ∈ (S)`
with `c_j ∈ ℚ[μ]`. Let `μ₀ ∈ ℚ^ι` with `g(μ₀) ≠ 0` be a parameter point at which `S` has no
complex solution. Then the elimination ideal `(S) ∩ ℚ[μ]` contains some `h` with `h(μ₀) ≠ 0`. -/
theorem elim_integral_mem (S : Set (MvPolynomial (ι ⊕ κ) ℚ)) (g : MvPolynomial ι ℚ)
    (hint : ∀ i : κ, ∃ (a d : ℕ) (c : Fin d → MvPolynomial ι ℚ),
      rename Sum.inl (g ^ a) * X (Sum.inr i) ^ d +
        ∑ j : Fin d, rename Sum.inl (c j) * X (Sum.inr i) ^ (j : ℕ) ∈ Ideal.span S)
    (μ₀ : ι → ℚ) (hg : eval μ₀ g ≠ 0)
    (hnone : ∀ x : κ → ℂ, ∃ f ∈ S, aeval (Sum.elim (fun k => (μ₀ k : ℂ)) x) f ≠ 0) :
    ∃ h : MvPolynomial ι ℚ, eval μ₀ h ≠ 0 ∧ rename Sum.inl h ∈ Ideal.span S := by
  classical
  by_contra hcon
  push Not at hcon
  -- every `a` with `g ^ c * a ∈ (S)` vanishes at `μ₀`
  have hK : ∀ (a : MvPolynomial ι ℚ) (c : ℕ),
      rename Sum.inl (g ^ c * a) ∈ Ideal.span S → eval μ₀ a = 0 := by
    intro a c hmem
    by_contra ha
    refine hcon (g ^ c * a) ?_ hmem
    rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hg) ha
  -- a complex solution at `μ₀`, from lying over
  have hpt := exists_ringHom_complex_of_integral_away
    ((Ideal.Quotient.mk (Ideal.span S)).comp (rename Sum.inl).toRingHom) g (eval μ₀) hg ?_ ?_
  · obtain ⟨σ, hσ⟩ := hpt
    let x : κ → ℂ := fun i => σ (Ideal.Quotient.mk (Ideal.span S) (X (Sum.inr i)))
    have hΨ : σ.comp (Ideal.Quotient.mk (Ideal.span S)) =
        (aeval (Sum.elim (fun k => (μ₀ k : ℂ)) x)).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun q => ?_) (fun v => ?_)
      · exact RingHom.congr_fun (RingHom.ext_rat ((σ.comp (Ideal.Quotient.mk _)).comp C)
          ((aeval (Sum.elim (fun k => (μ₀ k : ℂ)) x)).toRingHom.comp C)) q
      · cases v with
        | inl k =>
          have h1 := hσ (X k)
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
            eval_X] at h1
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
            Sum.elim_inl, h1]
        | inr i =>
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
            Sum.elim_inr, x]
    obtain ⟨f, hfS, hf⟩ := hnone x
    apply hf
    have h0 : (σ.comp (Ideal.Quotient.mk (Ideal.span S))) f = 0 := by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hfS), map_zero]
    rw [hΨ] at h0
    exact h0
  · -- `ℚ[μ, x] ⧸ (S)` is generated by `ℚ[μ]` and the integral unknowns
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    induction p using MvPolynomial.induction_on with
    | C c =>
      exact Subring.subset_closure (Set.mem_union_left _ ⟨C c, by simp⟩)
    | add p q hp hq =>
      rw [map_add]
      exact Subring.add_mem _ hp hq
    | mul_X p v hp =>
      rw [map_mul]
      refine Subring.mul_mem _ hp (Subring.subset_closure ?_)
      cases v with
      | inl k => exact Set.mem_union_left _ ⟨X k, by simp⟩
      | inr i =>
        obtain ⟨a, d, c, hrel⟩ := hint i
        refine Set.mem_union_right _ ⟨a, d, c, ?_⟩
        have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hrel
        simpa only [map_add, map_mul, map_sum, map_pow, RingHom.comp_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h0
  · -- the kernel condition
    intro a c h0
    exact hK a c (Ideal.Quotient.eq_zero_iff_mem.mp h0)

/-- **Integral elimination.** Under the hypotheses of `elim_integral_mem` (every unknown integral
over `ℚ[μ][1/g]` modulo `(S)`, `g(μ₀) ≠ 0`, no complex solution at `μ₀`), there is `h ∈ ℚ[μ]` with
`h(μ₀) ≠ 0` and `h(μ) = 0` at every complex common zero `(μ, x)` of `S`; in particular
`g(μ) h(μ) = 0` there. -/
theorem elim_integral (S : Set (MvPolynomial (ι ⊕ κ) ℚ)) (g : MvPolynomial ι ℚ)
    (hint : ∀ i : κ, ∃ (a d : ℕ) (c : Fin d → MvPolynomial ι ℚ),
      rename Sum.inl (g ^ a) * X (Sum.inr i) ^ d +
        ∑ j : Fin d, rename Sum.inl (c j) * X (Sum.inr i) ^ (j : ℕ) ∈ Ideal.span S)
    (μ₀ : ι → ℚ) (hg : eval μ₀ g ≠ 0)
    (hnone : ∀ x : κ → ℂ, ∃ f ∈ S, aeval (Sum.elim (fun k => (μ₀ k : ℂ)) x) f ≠ 0) :
    ∃ h : MvPolynomial ι ℚ, eval μ₀ h ≠ 0 ∧
      ∀ (μ : ι → ℂ) (x : κ → ℂ), (∀ f ∈ S, aeval (Sum.elim μ x) f = 0) → aeval μ h = 0 := by
  obtain ⟨h, hh, hmem⟩ := elim_integral_mem S g hint μ₀ hg hnone
  refine ⟨h, hh, fun μ x hsol => ?_⟩
  have h0 := aeval_eq_zero_of_mem_span hmem hsol
  rwa [aeval_rename, Sum.elim_comp_inl] at h0

/-- Clearing denominators: a positive integer multiple of a polynomial with rational coefficients
has integer coefficients. -/
theorem exists_map_int_eq_natCast_mul {σ : Type*} (p : MvPolynomial σ ℚ) :
    ∃ (D : ℕ) (P : MvPolynomial σ ℤ), 0 < D ∧ map (algebraMap ℤ ℚ) P = C (D : ℚ) * p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u q =>
    refine ⟨q.den, monomial u q.num, q.den_pos, ?_⟩
    rw [map_monomial, C_mul_monomial, eq_intCast, Rat.den_mul_eq_num]
  | add p q hp hq =>
    obtain ⟨D₁, P₁, hD₁, h₁⟩ := hp
    obtain ⟨D₂, P₂, hD₂, h₂⟩ := hq
    refine ⟨D₁ * D₂, C (D₂ : ℤ) * P₁ + C (D₁ : ℤ) * P₂, Nat.mul_pos hD₁ hD₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_C, map_C, h₁, h₂, Nat.cast_mul, C_mul]
    simp only [eq_intCast, Int.cast_natCast]
    ring

/-- **Integral elimination, integer form.** Under the hypotheses of `elim_integral_mem` there is
`P ∈ ℤ[μ]` with `P(μ₀) ≠ 0` and `P(μ) = 0` at every `μ ∈ ℂ^ι` for which `S` has a complex
solution. -/
theorem elim_integral_int (S : Set (MvPolynomial (ι ⊕ κ) ℚ)) (g : MvPolynomial ι ℚ)
    (hint : ∀ i : κ, ∃ (a d : ℕ) (c : Fin d → MvPolynomial ι ℚ),
      rename Sum.inl (g ^ a) * X (Sum.inr i) ^ d +
        ∑ j : Fin d, rename Sum.inl (c j) * X (Sum.inr i) ^ (j : ℕ) ∈ Ideal.span S)
    (μ₀ : ι → ℚ) (hg : eval μ₀ g ≠ 0)
    (hnone : ∀ x : κ → ℂ, ∃ f ∈ S, aeval (Sum.elim (fun k => (μ₀ k : ℂ)) x) f ≠ 0) :
    ∃ P : MvPolynomial ι ℤ, aeval μ₀ P ≠ 0 ∧
      ∀ μ : ι → ℂ, (∃ x : κ → ℂ, ∀ f ∈ S, aeval (Sum.elim μ x) f = 0) → aeval μ P = 0 := by
  obtain ⟨h, hh, hvan⟩ := elim_integral S g hint μ₀ hg hnone
  obtain ⟨D, P, hD, hP⟩ := exists_map_int_eq_natCast_mul h
  refine ⟨P, ?_, ?_⟩
  · rw [← aeval_map_algebraMap ℚ, hP, map_mul]
    refine mul_ne_zero ?_ hh
    rw [aeval_C]
    simpa using hD.ne'
  · rintro μ ⟨x, hx⟩
    rw [← aeval_map_algebraMap ℚ, hP, map_mul, hvan μ x hx, mul_zero]
end

end CC6Full
