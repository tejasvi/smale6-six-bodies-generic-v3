import CC6Full.Curve.FunctionField.Expansion
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Every curve has a place centred on it

`exists_place_centred`: for an irreducible curve `C ⊆ ℂ^σ` (`σ` finite) there is a place `P` (a normalized discrete
valuation of `ℂ(C)`, trivial on `ℂ`) with `ord_P f ≥ 0` for every `f ∈ ℂ[C]`. Construction: `ℂ(C)` is finite over
`ℂ(t₀)` (`curve_noether`); the integral closure `B` of `ℂ[t₀]` in `ℂ(C)` is a Dedekind domain containing `ℂ[C]`; a
maximal ideal of `B` gives the adic valuation `Valuation ℂ(C) Zm0` of Mathlib, turned into an
`AddValuation ℂ(C) (WithTop ℤ)` by `ordOfVal`.

Ported from the five-body formalization (`CC5Full/Theory/FunctionField/Places.lean`), with the curves `C ⊆ Y_m`
replaced by the affine curves `ACurve σ`.
-/

namespace CC6Full

noncomputable section

/-- The value monoid of the adic valuations. -/
local notation "Zm0" => WithZero (Multiplicative ℤ)

section conv

variable {K : Type*} [Field K] (val : Valuation K Zm0)

/-- The additive form `x ↦ −log v(x)` of a valuation with values in `Zm0`. -/
def ordFun (x : K) : WithTop ℤ := by
  classical
  exact if h : val x = 0 then ⊤ else ((-(Multiplicative.toAdd (WithZero.unzero h)) : ℤ) : WithTop ℤ)

theorem ordFun_of_ne {x : K} (h : val x ≠ 0) :
    ordFun val x = ((-(Multiplicative.toAdd (WithZero.unzero h)) : ℤ) : WithTop ℤ) := by
  classical
  unfold ordFun; simp only [h, ↓reduceDIte]

theorem ordFun_eq_coe {x : K} {n : ℤ} (h : val x = ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : Zm0)) :
    ordFun val x = n := by
  have h0 : val x ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  rw [ordFun_of_ne val h0]
  have : WithZero.unzero h0 = Multiplicative.ofAdd (-n) := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, h]
  rw [this, toAdd_ofAdd, neg_neg]

theorem ordFun_mul (x y : K) : ordFun val (x * y) = ordFun val x + ordFun val y := by
  by_cases hx : val x = 0
  · have : val (x * y) = 0 := by rw [map_mul, hx, zero_mul]
    unfold ordFun; simp [hx, this]
  by_cases hy : val y = 0
  · have : val (x * y) = 0 := by rw [map_mul, hy, mul_zero]
    unfold ordFun; simp [hy, this]
  have hxy : val (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hx hy
  rw [ordFun_of_ne val hx, ordFun_of_ne val hy, ordFun_of_ne val hxy, ← WithTop.coe_add]
  congr 1
  have : WithZero.unzero hxy = WithZero.unzero hx * WithZero.unzero hy := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]
  ring

theorem ordFun_add (x y : K) : min (ordFun val x) (ordFun val y) ≤ ordFun val (x + y) := by
  by_cases hxy : val (x + y) = 0
  · unfold ordFun; simp [hxy]
  have hle := val.map_add x y
  by_cases hx : val x = 0
  · rw [hx, max_eq_right zero_le] at hle
    have hy : val y ≠ 0 := fun h => hxy (le_antisymm (h ▸ hle) zero_le)
    refine min_le_of_right_le ?_
    rw [ordFun_of_ne val hy, ordFun_of_ne val hxy]
    have : WithZero.unzero hxy ≤ WithZero.unzero hy := by
      rw [← WithZero.coe_le_coe, WithZero.coe_unzero, WithZero.coe_unzero]; exact hle
    have := Multiplicative.toAdd_le.mpr this
    exact_mod_cast neg_le_neg this
  by_cases hy : val y = 0
  · rw [hy, max_eq_left zero_le] at hle
    refine min_le_of_left_le ?_
    rw [ordFun_of_ne val hx, ordFun_of_ne val hxy]
    have : WithZero.unzero hxy ≤ WithZero.unzero hx := by
      rw [← WithZero.coe_le_coe, WithZero.coe_unzero, WithZero.coe_unzero]; exact hle
    have := Multiplicative.toAdd_le.mpr this
    exact_mod_cast neg_le_neg this
  rw [ordFun_of_ne val hx, ordFun_of_ne val hy, ordFun_of_ne val hxy]
  rcases le_total (val x) (val y) with h | h
  · rw [max_eq_right h] at hle
    refine min_le_of_right_le ?_
    have : WithZero.unzero hxy ≤ WithZero.unzero hy := by
      rw [← WithZero.coe_le_coe, WithZero.coe_unzero, WithZero.coe_unzero]; exact hle
    have := Multiplicative.toAdd_le.mpr this
    exact_mod_cast neg_le_neg this
  · rw [max_eq_left h] at hle
    refine min_le_of_left_le ?_
    have : WithZero.unzero hxy ≤ WithZero.unzero hx := by
      rw [← WithZero.coe_le_coe, WithZero.coe_unzero, WithZero.coe_unzero]; exact hle
    have := Multiplicative.toAdd_le.mpr this
    exact_mod_cast neg_le_neg this

/-- The additive valuation `−log v`. -/
def ordOfVal : AddValuation K (WithTop ℤ) :=
  AddValuation.of (ordFun val) (by unfold ordFun; simp) (by
    have h1 : val 1 = ((Multiplicative.ofAdd (-(0 : ℤ)) : Multiplicative ℤ) : Zm0) := by
      rw [map_one, neg_zero, ofAdd_zero]; rfl
    rw [ordFun_eq_coe val h1]; rfl) (ordFun_add val) (ordFun_mul val)

theorem ordOfVal_apply (x : K) : ordOfVal val x = ordFun val x := rfl

/-- `−log v ≥ 0` where `v ≤ 1`. -/
theorem ordOfVal_nonneg {x : K} (h : val x ≤ 1) : 0 ≤ ordOfVal val x := by
  rw [ordOfVal_apply]
  by_cases hx : val x = 0
  · unfold ordFun; simp [hx]
  rw [ordFun_of_ne val hx]
  have : WithZero.unzero hx ≤ 1 := by
    rw [← WithZero.coe_le_coe, WithZero.coe_unzero]; exact h
  have h2 : Multiplicative.toAdd (WithZero.unzero hx) ≤ 0 := by
    have := Multiplicative.toAdd_le.mpr this; simpa using this
  exact_mod_cast neg_nonneg.mpr h2

end conv

section curve

variable {σ : Type*} {C : ACurve σ}

/-- Every function on a curve is `a / c` with `a ∈ ℂ[C]` and `c ∈ ℂ[t₀] ∖ 0`. -/
theorem exists_num_den {t₀ : C.Ring} (_hinj : Function.Injective (Polynomial.aeval (R := ℂ) t₀))
    (hint : ∀ a : C.Ring, (Polynomial.aeval (R := ℂ) t₀).toRingHom.IsIntegralElem a) (f : C.FunctionField) :
    ∃ (a : C.Ring) (p : Polynomial ℂ), p ≠ 0 ∧
      f * algebraMap C.Ring C.FunctionField (Polynomial.aeval t₀ p) = algebraMap C.Ring C.FunctionField a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C.Ring) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set φ := (Polynomial.aeval (R := ℂ) t₀).toRingHom
  set ι := algebraMap C.Ring C.FunctionField
  have hι : Function.Injective ι := IsFractionRing.injective C.Ring C.FunctionField
  obtain ⟨p, -, hp, hp0⟩ := exists_monic_eval₂_eq_zero_coeff_zero_ne φ hb0 (hint b)
  set e := (p.divX).eval₂ φ b
  have hbe : b * e = -φ (p.coeff 0) := by
    have hX := Polynomial.X_mul_divX_add p
    have h2 : p.eval₂ φ b = b * e + φ (p.coeff 0) := by
      conv_lhs => rw [← hX]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [hp] at h2
    linear_combination -h2
  refine ⟨-(a * e), p.coeff 0, hp0, ?_⟩
  have hιb : ι b ≠ 0 := fun h => hb0 (hι (by rw [h, map_zero]))
  have := congrArg ι hbe
  simp only [map_mul, map_neg] at this
  show ι a / ι b * ι (φ (p.coeff 0)) = ι (-(a * e))
  rw [show ι (φ (p.coeff 0)) = -(ι b * ι e) by linear_combination this, map_neg, map_mul]
  field_simp

/-- **Every curve has a place centred on it**: a place `P` with `ord_P f ≥ 0` for all `f ∈ ℂ[C]`. -/
theorem exists_place_centred [Finite σ] (C : ACurve σ) : ∃ P : Place C, ∀ f : MvPolynomial σ ℂ, 0 ≤ P.v f := by
  classical
  obtain ⟨t₀, hinj, hint⟩ := curve_noether C
  have hφ : Function.Injective ((algebraMap C.Ring C.FunctionField).comp (Polynomial.aeval (R := ℂ) t₀).toRingHom) :=
    (IsFractionRing.injective C.Ring C.FunctionField).comp hinj
  let _ : Algebra (Polynomial ℂ) C.FunctionField :=
    ((algebraMap C.Ring C.FunctionField).comp (Polynomial.aeval (R := ℂ) t₀).toRingHom).toAlgebra
  have hφeq : ∀ p, algebraMap (Polynomial ℂ) C.FunctionField p =
      algebraMap C.Ring C.FunctionField (Polynomial.aeval t₀ p) := fun p => rfl
  let _ : Algebra (FractionRing (Polynomial ℂ)) C.FunctionField := (IsFractionRing.lift hφ).toAlgebra
  have _ : IsScalarTower (Polynomial ℂ) (FractionRing (Polynomial ℂ)) C.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hφ x).symm
  -- `ℂ[C]` is a finite `ℂ[t₀]`-module
  let _ : Algebra (Polynomial ℂ) C.Ring := (Polynomial.aeval (R := ℂ) t₀).toRingHom.toAlgebra
  have _ : Algebra.IsIntegral (Polynomial ℂ) C.Ring := ⟨fun a => hint a⟩
  have _ : IsScalarTower ℂ (Polynomial ℂ) C.Ring := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap ℂ C.Ring c = Polynomial.aeval t₀ (Polynomial.C c)
    rw [Polynomial.aeval_C]
  have _ : Algebra.FiniteType (Polynomial ℂ) C.Ring :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ C.Ring
  have _ : Module.Finite (Polynomial ℂ) C.Ring := Algebra.IsIntegral.finite
  obtain ⟨gens, hgens⟩ := (Module.Finite.fg_top : (⊤ : Submodule (Polynomial ℂ) C.Ring).FG)
  -- `ℂ(C)` is finite over `ℂ(t₀)`
  have _ : FiniteDimensional (FractionRing (Polynomial ℂ)) C.FunctionField := by
    refine Module.finite_def.mpr ⟨gens.image (algebraMap C.Ring C.FunctionField), ?_⟩
    rw [eq_top_iff]
    intro f _
    obtain ⟨a, p, hp, hfa⟩ := exists_num_den hinj hint f
    have ha : a ∈ Submodule.span (Polynomial ℂ) (gens : Set C.Ring) := by rw [hgens]; trivial
    obtain ⟨c, -, hc⟩ := (Submodule.mem_span_finset).mp ha
    have hφp : algebraMap (Polynomial ℂ) C.FunctionField p ≠ 0 := fun h => hp (hφ (h.trans (map_zero _).symm))
    have hfeq : f = ∑ g ∈ gens, (algebraMap (FractionRing (Polynomial ℂ)) C.FunctionField
        (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) (c g) /
          algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) p)) * algebraMap C.Ring C.FunctionField g := by
      have h1 : f = algebraMap C.Ring C.FunctionField a / algebraMap (Polynomial ℂ) C.FunctionField p := by
        rw [eq_div_iff hφp, hφeq]; exact hfa
      rw [h1, ← hc, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hφeq, hφeq]
      rw [Algebra.smul_def, map_mul]
      field_simp
      rw [mul_comm]
      rfl
    rw [hfeq]
    refine Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hg)
  -- the integral closure is a Dedekind domain with fraction field `ℂ(C)`
  have _ : IsDedekindDomain (integralClosure (Polynomial ℂ) C.FunctionField) :=
    integralClosure.isDedekindDomain (Polynomial ℂ) (FractionRing (Polynomial ℂ)) C.FunctionField
  have _ : IsFractionRing (integralClosure (Polynomial ℂ) C.FunctionField) C.FunctionField :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing (Polynomial ℂ)) C.FunctionField
  set B := integralClosure (Polynomial ℂ) C.FunctionField
  -- `B` is not a field
  have hinjB : Function.Injective (algebraMap (Polynomial ℂ) B) := by
    intro x y hxy
    apply hφ
    have := congrArg (algebraMap B C.FunctionField) hxy
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  have hBnf : ¬ IsField B := fun hF => Polynomial.not_isField ℂ (isField_of_isIntegral_of_isField hinjB hF)
  obtain ⟨𝔓, h𝔓⟩ := Ideal.exists_maximal B
  have h𝔓0 : 𝔓 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔓 hBnf
  let v : IsDedekindDomain.HeightOneSpectrum B := ⟨𝔓, h𝔓.isPrime, h𝔓0⟩
  set val := v.valuation C.FunctionField
  -- elements of `ℂ[C]` are integral over `ℂ[t₀]`, so lie in `B`
  have hmemB : ∀ a : C.Ring, IsIntegral (Polynomial ℂ) (algebraMap C.Ring C.FunctionField a) := by
    intro a
    obtain ⟨q, hqm, hq⟩ := hint a
    refine ⟨q, hqm, ?_⟩
    have := congrArg (algebraMap C.Ring C.FunctionField) hq
    rw [map_zero, Polynomial.hom_eval₂] at this
    exact this
  -- constants are units of `B`
  have hconstB : ∀ c : ℂ, algebraMap ℂ C.FunctionField c =
      algebraMap B C.FunctionField (algebraMap (Polynomial ℂ) B (Polynomial.C c)) := by
    intro c
    rw [← IsScalarTower.algebraMap_apply, hφeq, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
  have hconst : ∀ c : ℂ, c ≠ 0 → val (algebraMap ℂ C.FunctionField c) = 1 := by
    intro c hc
    rw [hconstB, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hmem
    have hu : IsUnit (algebraMap (Polynomial ℂ) B (Polynomial.C c)) :=
      (Polynomial.isUnit_C.mpr (Ne.isUnit hc)).map _
    exact h𝔓.ne_top ((Ideal.eq_top_of_isUnit_mem _ hmem hu))
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer (K := C.FunctionField) v
  refine ⟨⟨ordOfVal val, fun c hc => ?_, ⟨π, ?_⟩⟩, fun f => ?_⟩
  · rw [fn_C_eq_algebraMap]
    have h1 : val (algebraMap ℂ C.FunctionField c) =
        ((Multiplicative.ofAdd (-(0 : ℤ)) : Multiplicative ℤ) : Zm0) := by
      rw [hconst c hc, neg_zero, ofAdd_zero]; rfl
    rw [ordOfVal_apply, ordFun_eq_coe val h1]; rfl
  · rw [ordOfVal_apply, ordFun_eq_coe val (n := 1) hπ]; rfl
  · show 0 ≤ ordOfVal val (C.fn f)
    apply ordOfVal_nonneg
    have : C.fn f = algebraMap B C.FunctionField ⟨_, hmemB (Ideal.Quotient.mk C.ideal f)⟩ := rfl
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v _

end curve

end

end CC6Full
