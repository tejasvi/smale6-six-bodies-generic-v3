import CC6Full.Curve.ACurve
import CC6Full.Curve.Algebra
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# The coordinate ring of a curve is integral over a polynomial ring in one variable

* `ringKrullDim_le_of_isIntegral`: along an injective integral extension of domains the Krull dimension does not
  decrease (lying over and going up lift every chain of primes).
* `curve_noether`: for an irreducible curve `C ⊆ ℂ^σ` (`σ` finite; a prime of dimension one), some `t₀ ∈ ℂ[C]` is
  transcendental (`ℂ[X] → ℂ[C]`, `X ↦ t₀` injective) and `ℂ[C]` is integral over `ℂ[t₀]` (Noether normalization;
  the number of parameters is `1`, since it is at most the dimension and the ring is not a field).

Ported from the five-body formalization (`CC5Full/Theory/FunctionField/Dim.lean`), with the curves `C ⊆ Y_m`
replaced by the affine curves `ACurve σ`.
-/

namespace CC6Full

variable {σ : Type*}

/-- **Krull dimension along an injective integral extension of a domain**: `dim R ≤ dim S`. -/
theorem ringKrullDim_le_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) : ringKrullDim R ≤ ringKrullDim S := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  have hker : RingHom.ker (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]; exact Ideal.zero_mem _
  obtain ⟨Q, hQ, hQl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S)
    (RelSeries.head l).asIdeal hker
  have : Q.LiesOver (RelSeries.head l).asIdeal := ⟨hQl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
  rw [← hL]
  exact le_iSup (fun p : LTSeries (PrimeSpectrum S) => (p.length : WithBot ℕ∞)) L

/-- **Noether normalization of a curve**: `ℂ[C]` is integral over `ℂ[t₀]` for a transcendental `t₀`. -/
theorem curve_noether [Finite σ] (C : ACurve σ) :
    ∃ t₀ : C.Ring, Function.Injective (Polynomial.aeval (R := ℂ) t₀) ∧
      ∀ a : C.Ring, (Polynomial.aeval (R := ℂ) t₀).toRingHom.IsIntegralElem a := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ C.Ring
  have hs1 : s = 1 := by
    let _ : Algebra (MvPolynomial (Fin s) ℂ) C.Ring := g.toRingHom.toAlgebra
    have _ : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) C.Ring := ⟨fun x => hint x⟩
    have hle := ringKrullDim_le_of_isIntegral (R := MvPolynomial (Fin s) ℂ) (S := C.Ring) hinj
    rw [C.dim_one] at hle
    have hs := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (R := ℂ) (Fin s)
    rw [ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin] at hs
    have h1 : (s : WithBot ℕ∞) ≤ 1 := hs.trans hle
    have hs_le : s ≤ 1 := by exact_mod_cast h1
    have hs_ne : s ≠ 0 := by
      rintro rfl
      have hB : IsField (MvPolynomial (Fin 0) ℂ) :=
        (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).toMulEquiv.isField (Field.toIsField ℂ)
      have hF : IsField C.Ring := isField_of_isIntegral_of_isField' hB
      have := C.dim_one
      rw [ringKrullDim_eq_zero_of_isField hF] at this
      exact zero_ne_one this
    omega
  subst hs1
  set t₀ := g (MvPolynomial.X 0)
  -- `ℂ[X] → MvPolynomial (Fin 1) ℂ`, `X ↦ X 0`, and back
  set toMv : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ := Polynomial.aeval (MvPolynomial.X 0)
  set toPoly : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] Polynomial ℂ := MvPolynomial.aeval fun _ => Polynomial.X
  have hgt : (Polynomial.aeval (R := ℂ) t₀) = g.comp toMv := by
    refine Polynomial.algHom_ext ?_
    simp [toMv, t₀]
  have hpg : (Polynomial.aeval (R := ℂ) t₀).comp toPoly = g := by
    refine MvPolynomial.algHom_ext fun i => ?_
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp [toPoly, t₀]
  have htoMv : Function.Injective toMv := by
    have hleft : ∀ p, toPoly (toMv p) = p := by
      intro p
      have : toPoly.comp toMv = AlgHom.id ℂ (Polynomial ℂ) := Polynomial.algHom_ext (by simp [toPoly, toMv])
      exact congrArg (fun F => F p) this
    exact Function.LeftInverse.injective hleft
  refine ⟨t₀, ?_, fun a => ?_⟩
  · rw [hgt]
    exact hinj.comp htoMv
  · obtain ⟨p, hpm, hp⟩ := hint a
    refine ⟨p.map toPoly.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hp using 2
    rw [← hpg]
    rfl

end CC6Full
