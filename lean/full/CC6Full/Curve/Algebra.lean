import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Curves inside an algebraic set (the commutative algebra of `cor:curve`)

Three general facts, for polynomials over `ℂ` in a finite set `σ` of variables (ported from the five-body
formalization, `CC5Full/Theory/CorU/Algebra.lean`, which is already stated for any `σ`):

* `exists_prime_of_infinite`: an infinite set `T` of zeros of an ideal `I` on which `g` does not vanish lies in no
  finite union of points, so some minimal prime `P` of the vanishing ideal of `T` contains `I`, misses `g`, and is
  not maximal (a maximal ideal has at most one zero, `zeroLocus_subsingleton_of_isMaximal`).
* `exists_prime_not_mem_ringKrullDim_eq_one`: in a domain `A`, finitely generated over an infinite field and not a
  field, every `f ≠ 0` lies outside some prime `Q` with `dim A/Q = 1` (Noether normalization, a line on which the
  constant term of a monic relation of `f` does not vanish, lying over, and `Ring.DimensionLEOne` of integral
  extensions of `k[X]`); `exists_curve_ideal` is its form for `ℂ[σ]/P`: a non-maximal prime `P` and `f ∉ P` give
  a prime `Q ⊇ P` of dimension one with `f ∉ Q`, i.e. an irreducible curve inside the zero set of `P` on which `f`
  is not identically zero.
* `zeroLocus_infinite_of_ringKrullDim_eq_one`: a prime of dimension one has infinitely many zeros (Nullstellensatz
  for prime ideals).
-/

namespace CC6Full

open Polynomial

/-- An element of a domain that is integral (through `g`) and nonzero satisfies a monic relation whose constant
coefficient is nonzero. -/
theorem exists_monic_eval₂_eq_zero_coeff_zero_ne {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (g : R →+* S) {f : S} (hf : f ≠ 0) (hint : g.IsIntegralElem f) :
    ∃ p : R[X], p.Monic ∧ p.eval₂ g f = 0 ∧ p.coeff 0 ≠ 0 := by
  obtain ⟨p, hpm, hp⟩ := hint
  induction hn : p.natDegree generalizing p with
  | zero =>
    rw [Polynomial.Monic.natDegree_eq_zero hpm] at hn
    subst hn
    simp at hp
  | succ n ih =>
    by_cases h0 : p.coeff 0 = 0
    · have hX := Polynomial.X_mul_divX_add p
      rw [h0, map_zero, add_zero] at hX
      have hdeg : (p.divX).natDegree = n := by
        rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hn]; rfl
      have hmon : (p.divX).Monic := by
        rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, Polynomial.coeff_divX, ← hn]
        exact hpm
      have hev : (p.divX).eval₂ g f = 0 := by
        rw [← hX, Polynomial.eval₂_mul, Polynomial.eval₂_X] at hp
        exact (mul_eq_zero.mp hp).resolve_left hf
      exact ih p.divX hmon hev hdeg
    · exact ⟨p, hpm, hp, h0⟩

/-- An element of `WithBot ℕ∞` that is at most `1` and not at most `0` is `1`. -/
theorem withBot_enat_eq_one {x : WithBot ℕ∞} (h1 : x ≤ 1) (h0 : ¬ x ≤ 0) : x = 1 := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd bot_le h0
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd h1 (by decide)
    | coe k =>
      have h1' : k ≤ 1 := by exact_mod_cast h1
      have h0' : ¬ k ≤ 0 := fun h => h0 (by exact_mod_cast h)
      have : k = 1 := by omega
      subst this; rfl

/-- **A curve through a nonvanishing function.** Let `A` be a domain, finitely generated over an infinite field
`k`, that is not a field, and `f ≠ 0` in `A`. Then some prime `Q` of `A` with `f ∉ Q` has `dim A/Q = 1`.
(Noether normalization `k[t₁, …, tₛ] ⊆ A`, `s ≥ 1`; a monic relation of `f` with constant term `b₀ ≠ 0`; a line
`t_i = a_i` (`i ≥ 1`) on which `b₀` does not vanish; a prime of `A` over it, by lying over.) -/
theorem exists_prime_not_mem_ringKrullDim_eq_one {k A : Type*} [Field k] [Infinite k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (hA : ¬ IsField A) {f : A} (hf : f ≠ 0) :
    ∃ Q : Ideal A, Q.IsPrime ∧ f ∉ Q ∧ ringKrullDim (A ⧸ Q) = 1 := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hint x⟩
  -- `s ≥ 1`
  have hs : s ≠ 0 := by
    rintro rfl
    have hB : IsField (MvPolynomial (Fin 0) k) :=
      (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toMulEquiv.isField (Field.toIsField k)
    exact hA (isField_of_isIntegral_of_isField' hB)
  set i₀ : Fin s := ⟨0, Nat.pos_of_ne_zero hs⟩
  -- a monic relation with nonzero constant term
  obtain ⟨p, hpm, hp, hp0⟩ := exists_monic_eval₂_eq_zero_coeff_zero_ne g.toRingHom hf (hint f)
  -- a point where the constant term does not vanish
  obtain ⟨a, ha⟩ : ∃ a : Fin s → k, MvPolynomial.eval a (p.coeff 0) ≠ 0 := by
    by_contra! h
    exact hp0 (MvPolynomial.funext fun x => by simpa using h x)
  -- the line `t_i = a_i`, `i ≠ i₀`
  set φ : MvPolynomial (Fin s) k →ₐ[k] k[X] :=
    MvPolynomial.aeval fun i => if i = i₀ then Polynomial.X else Polynomial.C (a i)
  have hφX : φ (MvPolynomial.X i₀) = Polynomial.X := by simp [φ]
  have hφsurj : Function.Surjective φ := by
    intro q
    refine ⟨Polynomial.aeval (MvPolynomial.X i₀) q, ?_⟩
    rw [← Polynomial.aeval_algHom_apply, hφX, Polynomial.aeval_X_left_apply]
  have hφeval : ∀ b, (φ b).eval (a i₀) = MvPolynomial.eval a b := by
    intro b
    have : (Polynomial.aeval (a i₀)).comp φ = MvPolynomial.aeval a := by
      refine MvPolynomial.algHom_ext fun i => ?_
      by_cases hi : i = i₀
      · subst hi; simp [φ]
      · simp [φ, hi]
    have h := congrArg (fun F => F b) this
    simpa using h
  have hb₀ : p.coeff 0 ∉ RingHom.ker φ.toRingHom := by
    intro h
    rw [RingHom.mem_ker] at h
    apply ha
    rw [← hφeval]
    change (φ.toRingHom (p.coeff 0)).eval (a i₀) = 0
    rw [h, Polynomial.eval_zero]
  have _ : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
  -- lying over
  obtain ⟨Q, hQ, hQunder⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := A) (RingHom.ker φ.toRingHom) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have : x = 0 := hinj (by rw [map_zero]; exact hx)
      rw [this]; exact Ideal.zero_mem _)
  refine ⟨Q, hQ, ?_, ?_⟩
  · -- `f ∉ Q`
    intro hfQ
    apply hb₀
    rw [← hQunder, Ideal.under, Ideal.mem_comap]
    have hX := Polynomial.X_mul_divX_add p
    have h2 : p.eval₂ g.toRingHom f = f * (p.divX).eval₂ g.toRingHom f + g.toRingHom (p.coeff 0) := by
      conv_lhs => rw [← hX]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [hp] at h2
    have h3 : algebraMap (MvPolynomial (Fin s) k) A (p.coeff 0) =
        -(f * (p.divX).eval₂ g.toRingHom f) := by
      change g.toRingHom (p.coeff 0) = _
      linear_combination h2.symm
    rw [h3]
    exact Q.neg_mem_iff.mpr (Q.mul_mem_right _ hfQ)
  · -- `dim A/Q = 1`
    set R' := MvPolynomial (Fin s) k ⧸ Q.comap (algebraMap (MvPolynomial (Fin s) k) A)
    have e : R' ≃+* k[X] :=
      (Ideal.quotEquivOfEq hQunder).trans (RingHom.quotientKerEquivOfSurjective (f := φ.toRingHom) hφsurj)
    have _ : Ring.DimensionLEOne R' := Ring.DimensionLEOne.of_ringEquiv e
    have _ : Nontrivial R' := e.toEquiv.nontrivial
    have _ : Ring.DimensionLEOne (A ⧸ Q) := Ring.DimensionLEOne.of_isIntegral R' (A ⧸ Q)
    have hle : ringKrullDim (A ⧸ Q) ≤ 1 := by
      have : Ring.KrullDimLE 1 (A ⧸ Q) := inferInstance
      exact_mod_cast Ring.krullDimLE_iff.mp this
    have hnf : ¬ IsField (A ⧸ Q) := by
      intro hF
      have hR' : IsField R' := isField_of_isIntegral_of_isField Ideal.algebraMap_quotient_injective hF
      exact Polynomial.not_isField k (e.symm.toMulEquiv.isField hR')
    have hnle : ¬ ringKrullDim (A ⧸ Q) ≤ 0 := by
      intro h0
      have : Ring.KrullDimLE 0 (A ⧸ Q) := Ring.krullDimLE_iff.mpr (by exact_mod_cast h0)
      exact hnf Ring.KrullDimLE.isField_of_isDomain
    exact withBot_enat_eq_one hle hnle

section poly

variable {σ : Type*} [Finite σ]

omit [Finite σ] in
/-- `aeval` and `eval` agree for polynomials over `ℂ` at complex points. -/
theorem aeval_eq_eval_complex (x : σ → ℂ) (p : MvPolynomial σ ℂ) : MvPolynomial.aeval x p = MvPolynomial.eval x p :=
  rfl

/-- **Curves in the zero set of a prime**: a non-maximal prime `P` and `f ∉ P` give a prime `Q ⊇ P` with `f ∉ Q`
and `dim ℂ[σ]/Q = 1`. -/
theorem exists_curve_ideal {P : Ideal (MvPolynomial σ ℂ)} [hP : P.IsPrime] (hmax : ¬ P.IsMaximal)
    {f : MvPolynomial σ ℂ} (hf : f ∉ P) :
    ∃ Q : Ideal (MvPolynomial σ ℂ), Q.IsPrime ∧ P ≤ Q ∧ f ∉ Q ∧ ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = 1 := by
  have hA : ¬ IsField (MvPolynomial σ ℂ ⧸ P) := fun h =>
    hmax ((Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr h)
  have hf' : Ideal.Quotient.mk P f ≠ 0 := fun h => hf (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨Q', hQ', hfQ', hdim⟩ := exists_prime_not_mem_ringKrullDim_eq_one (k := ℂ) hA hf'
  refine ⟨Q'.comap (Ideal.Quotient.mk P), Ideal.comap_isPrime _ _, ?_, ?_, ?_⟩
  · intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Q'.zero_mem
  · exact hfQ'
  · have hle : P ≤ Q'.comap (Ideal.Quotient.mk P) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact Q'.zero_mem
    have hmap : (Q'.comap (Ideal.Quotient.mk P)).map (Ideal.Quotient.mk P) = Q' :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q'
    rw [← ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle), hmap, hdim]

/-- A prime of dimension one is not maximal. -/
theorem not_isMaximal_of_ringKrullDim_eq_one {R : Type*} [CommRing R] {Q : Ideal R}
    (hdim : ringKrullDim (R ⧸ Q) = 1) : ¬ Q.IsMaximal := by
  intro hQ
  have hF : IsField (R ⧸ Q) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hQ
  rw [ringKrullDim_eq_zero_of_isField hF] at hdim
  exact zero_ne_one hdim

/-- **A curve has infinitely many points**: a prime of `ℂ[σ]` of dimension one has infinitely many zeros. -/
theorem zeroLocus_infinite_of_ringKrullDim_eq_one {Q : Ideal (MvPolynomial σ ℂ)} [hQ : Q.IsPrime]
    (hdim : ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = 1) :
    {y : σ → ℂ | ∀ f ∈ Q, MvPolynomial.eval y f = 0}.Infinite := by
  intro hfin
  set Z := {y : σ → ℂ | ∀ f ∈ Q, MvPolynomial.eval y f = 0}
  have hZ : MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ Q) = Q :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus Q
  have hZeq : MvPolynomial.zeroLocus ℂ Q = Z := rfl
  rw [hZeq] at hZ
  have hnmax := not_isMaximal_of_ringKrullDim_eq_one hdim
  -- for each zero `y`, a polynomial vanishing at `y` and not in `Q`
  have hsep : ∀ y ∈ Z, ∃ g, MvPolynomial.eval y g = 0 ∧ g ∉ Q := by
    intro y hy
    by_contra! h
    have hle : MvPolynomial.vanishingIdeal ℂ {y} ≤ Q := fun g hg =>
      h g ((MvPolynomial.mem_vanishingIdeal_singleton_iff y g).mp hg)
    have hge : Q ≤ MvPolynomial.vanishingIdeal ℂ {y} := fun g hg =>
      (MvPolynomial.mem_vanishingIdeal_singleton_iff y g).mpr (hy g hg)
    exact hnmax (le_antisymm hge hle ▸ inferInstance)
  choose! g hg using hsep
  set F := hfin.toFinset
  have hmem : ∏ y ∈ F, g y ∈ Q := by
    rw [← hZ]
    intro x hx
    rw [aeval_eq_eval_complex, map_prod]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.mpr hx) (hg x hx).1
  obtain ⟨y, hyF, hyQ⟩ := (Ideal.IsPrime.prod_mem_iff).mp hmem
  exact (hg y (hfin.mem_toFinset.mp hyF)).2 hyQ

omit [Finite σ] in
/-- A maximal ideal of `ℂ[σ]` has at most one zero. -/
theorem zeroLocus_subsingleton_of_isMaximal {P : Ideal (MvPolynomial σ ℂ)} (hP : P.IsMaximal) :
    {y : σ → ℂ | ∀ f ∈ P, MvPolynomial.eval y f = 0}.Subsingleton := by
  intro y hy y' hy'
  have h1 : P = MvPolynomial.vanishingIdeal ℂ {y} :=
    hP.eq_of_le Ideal.IsPrime.ne_top' fun g hg => (MvPolynomial.mem_vanishingIdeal_singleton_iff y g).mpr (hy g hg)
  have h2 : P = MvPolynomial.vanishingIdeal ℂ {y'} :=
    hP.eq_of_le Ideal.IsPrime.ne_top' fun g hg =>
      (MvPolynomial.mem_vanishingIdeal_singleton_iff y' g).mpr (hy' g hg)
  funext c
  have hc : MvPolynomial.X c - MvPolynomial.C (y c) ∈ MvPolynomial.vanishingIdeal ℂ {y'} := by
    rw [← h2, h1, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp [aeval_eq_eval_complex]
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, aeval_eq_eval_complex] at hc
  simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at hc
  exact (sub_eq_zero.mp hc).symm

/-- **Infinitely many zeros give a non-maximal prime**: if `g` vanishes nowhere on an infinite set `T` of zeros of
`I`, some non-maximal prime `P ⊇ I` misses `g`. -/
theorem exists_prime_of_infinite {I : Ideal (MvPolynomial σ ℂ)} {g : MvPolynomial σ ℂ} {T : Set (σ → ℂ)}
    (hT : ∀ y ∈ T, ∀ f ∈ I, MvPolynomial.eval y f = 0) (hinf : T.Infinite)
    (hg : ∀ y ∈ T, MvPolynomial.eval y g ≠ 0) :
    ∃ P : Ideal (MvPolynomial σ ℂ), P.IsPrime ∧ I ≤ P ∧ g ∉ P ∧ ¬ P.IsMaximal := by
  set J : Ideal (MvPolynomial σ ℂ) := MvPolynomial.vanishingIdeal ℂ T
  have hIJ : I ≤ J := fun f hf x hx => by rw [aeval_eq_eval_complex]; exact hT x hx f hf
  have hfinM : J.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ J
  -- every point of `T` is a zero of some minimal prime
  have hcover : ∀ y ∈ T, ∃ P ∈ J.minimalPrimes, ∀ f ∈ P, MvPolynomial.eval y f = 0 := by
    intro y hy
    by_contra! h
    choose! f hfP hfy using h
    set F := hfinM.toFinset
    have hprod : ∏ P ∈ F, f P ∈ J.radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      exact Ideal.prod_mem _ (hfinM.mem_toFinset.mpr hP) (hfP P hP)
    obtain ⟨n, hn⟩ := hprod
    have := hn y hy
    rw [aeval_eq_eval_complex, map_pow, map_prod] at this
    obtain ⟨P, hPF, hP0⟩ := Finset.prod_eq_zero_iff.mp (pow_eq_zero_iff'.mp this).1
    exact hfy P (hfinM.mem_toFinset.mp hPF) hP0
  -- one of them carries infinitely many points of `T`
  have hunion : T ⊆ ⋃ P ∈ J.minimalPrimes, T ∩ {y | ∀ f ∈ P, MvPolynomial.eval y f = 0} := by
    intro y hy
    obtain ⟨P, hP, hyP⟩ := hcover y hy
    exact Set.mem_biUnion hP ⟨hy, hyP⟩
  obtain ⟨P, hPmin, hPinf⟩ : ∃ P ∈ J.minimalPrimes,
      (T ∩ {y | ∀ f ∈ P, MvPolynomial.eval y f = 0}).Infinite := by
    by_contra! h
    exact hinf ((hfinM.biUnion fun P hP => h P hP).subset hunion)
  have hPprime : P.IsPrime := hPmin.1.1
  refine ⟨P, hPprime, hIJ.trans hPmin.1.2, ?_, ?_⟩
  · intro hgP
    obtain ⟨y, hyT, hyP⟩ := hPinf.nonempty
    exact hg y hyT (hyP g hgP)
  · intro hmax
    exact hPinf ((zeroLocus_subsingleton_of_isMaximal hmax).anti Set.inter_subset_right).finite

end poly

end CC6Full
