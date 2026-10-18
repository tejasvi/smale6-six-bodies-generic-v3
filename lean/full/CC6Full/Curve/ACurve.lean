import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Affine curves over `ℂ`, their function fields, places and expansions

Paper §2.2 (`ss:places`), in the form of the five-body formalization (`CC5Full/Places.lean`,
`CC5Full/Expansion.lean`), for curves in an affine space `𝔸^σ` with any finite set of coordinates `σ`.

* `ACurve σ`: an irreducible curve, i.e. a prime ideal `𝔭` of `ℂ[σ]` with `dim ℂ[σ]/𝔭 = 1`. By the
  Nullstellensatz these are the irreducible closed curves of `ℂ^σ`.
* `ACurve.FunctionField`: `ℂ(C) = Frac(ℂ[σ]/𝔭)`; `ACurve.fn f` is the function of a polynomial.
* `Place C`: a normalized discrete valuation of `ℂ(C)` trivial on `ℂ*`, i.e. an additive valuation with values in
  `WithTop ℤ` that vanishes on the nonzero constants and takes the value `1`. There is no smooth projective model:
  the places of `C̄` are exactly these valuations.
* `Place.Expansion P`: a ring embedding `ℂ(C) → ℂ((t))` that is the identity on `ℂ` and turns `ord_P` into the
  `t`-adic order (the completion at `P` with a uniformizer `t`).
-/

namespace CC6Full

open MvPolynomial

noncomputable section

/-- An irreducible affine curve in `ℂ^σ`: a prime ideal of `ℂ[σ]` whose quotient has Krull dimension one. -/
structure ACurve (σ : Type*) where
  /-- the prime ideal of the curve -/
  ideal : Ideal (MvPolynomial σ ℂ)
  isPrime : ideal.IsPrime
  dim_one : ringKrullDim (MvPolynomial σ ℂ ⧸ ideal) = 1

variable {σ : Type*}

instance ACurve.instIsPrime (C : ACurve σ) : C.ideal.IsPrime := C.isPrime

/-- The coordinate ring `ℂ[C]`. -/
abbrev ACurve.Ring (C : ACurve σ) : Type _ := MvPolynomial σ ℂ ⧸ C.ideal

/-- The function field `ℂ(C)`. -/
abbrev ACurve.FunctionField (C : ACurve σ) : Type _ := FractionRing C.Ring

/-- The function on `C` of a polynomial. -/
def ACurve.fn (C : ACurve σ) (f : MvPolynomial σ ℂ) : C.FunctionField :=
  algebraMap C.Ring C.FunctionField (Ideal.Quotient.mk C.ideal f)

/-- `f` is constant on the curve. -/
def ACurve.IsConst (C : ACurve σ) (f : MvPolynomial σ ℂ) : Prop := ∃ c : ℂ, f - MvPolynomial.C c ∈ C.ideal

/-- A place of the function field of `C`: a normalized discrete valuation trivial on the constants. -/
structure Place (C : ACurve σ) where
  /-- the order of a function at the place -/
  ord : AddValuation C.FunctionField (WithTop ℤ)
  ord_const : ∀ c : ℂ, c ≠ 0 → ord (C.fn (MvPolynomial.C c)) = 0
  exists_ord_eq_one : ∃ f : C.FunctionField, ord f = 1

/-- The order at `P` of the function of a polynomial. -/
def Place.v {C : ACurve σ} (P : Place C) (f : MvPolynomial σ ℂ) : WithTop ℤ := P.ord (C.fn f)

/-- A formal expansion at the place `P`: a ring embedding of `ℂ(C)` into `ℂ((t))`, the identity on `ℂ`, with
`ord_P f` the order of the Laurent series of `f`. -/
structure Place.Expansion {C : ACurve σ} (P : Place C) where
  /-- the Laurent series of a function -/
  ι : C.FunctionField →+* LaurentSeries ℂ
  map_const : ∀ c : ℂ, ι (C.fn (MvPolynomial.C c)) = HahnSeries.C c
  orderTop_eq : ∀ f : C.FunctionField, (ι f).orderTop = P.ord f

end

end CC6Full
