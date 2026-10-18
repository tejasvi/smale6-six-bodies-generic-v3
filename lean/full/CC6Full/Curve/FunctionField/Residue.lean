import CC6Full.Curve.FunctionField.AlgRel

/-!
# The residue field of every place of a curve is `ℂ`

`exists_residue_place`: for a place `P` of an irreducible curve `C ⊆ ℂ^σ` (`σ` finite) and `f ∈ ℂ(C)` with
`ord_P f ≥ 0`, some `c ∈ ℂ` has `ord_P (f − c) > 0`.

Proof. `ℂ[C]` is integral over `ℂ[t₀]` (`curve_noether`), so every `f ∈ ℂ(C)` is algebraic over `ℂ[t₀]`
(`algRel_of_curve`: write `f = a/b`, clear `b` by the constant term of a monic relation of `b`, and use a monic
relation of the numerator). Some `x ∈ {t₀, t₀⁻¹, t₀ − c}` has `ord_P x > 0`: if `ord_P t₀ = 0` and every
`ord_P (t₀ − c) = 0`, then `ord_P` vanishes on `ℂ[t₀] ∖ 0` (`val_aeval_eq_sum_roots`), hence on `ℂ(C)^*`
(`val_eq_zero_of_algRel`), against the element of order `1`. Then `exists_residue` applies.

Ported from the five-body formalization (`CC5Full/Theory/FunctionField/Residue.lean`), with the curves `C ⊆ Y_m`
replaced by the affine curves `ACurve σ`.
-/

namespace CC6Full

open Polynomial

noncomputable section

variable {σ : Type*} {C : ACurve σ}

/-- Every function on a curve is algebraic over `ℂ[t₀]`. -/
theorem algRel_of_curve {t₀ : C.Ring} (hinj : Function.Injective (Polynomial.aeval (R := ℂ) t₀))
    (hint : ∀ a : C.Ring, (Polynomial.aeval (R := ℂ) t₀).toRingHom.IsIntegralElem a) (f : C.FunctionField) :
    AlgRel (algebraMap C.Ring C.FunctionField t₀) f := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C.Ring) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set φ := (Polynomial.aeval (R := ℂ) t₀).toRingHom
  set ι := algebraMap C.Ring C.FunctionField
  have hι : Function.Injective ι := IsFractionRing.injective C.Ring C.FunctionField
  -- `1/b` has denominator in `ℂ[t₀]`
  obtain ⟨p, -, hp, hp0⟩ := exists_monic_eval₂_eq_zero_coeff_zero_ne φ hb0 (hint b)
  set e := (p.divX).eval₂ φ b
  have hbe : b * e = -φ (p.coeff 0) := by
    have hX := Polynomial.X_mul_divX_add p
    have h2 : p.eval₂ φ b = b * e + φ (p.coeff 0) := by
      conv_lhs => rw [← hX]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [hp] at h2
    linear_combination -h2
  have hc0 : φ (p.coeff 0) ≠ 0 := fun h => hp0 (hinj (h.trans (map_zero _).symm))
  -- `f = a'' / c` with `c = φ(p₀)`
  set a'' := -(a * e)
  have hf : ι a / ι b = ι a'' / ι (φ (p.coeff 0)) := by
    have hιb : ι b ≠ 0 := fun h => hb0 (hι (by rw [h, map_zero]))
    have hιc : ι (φ (p.coeff 0)) ≠ 0 := fun h => hc0 (hι (by rw [h, map_zero]))
    rw [div_eq_div_iff hιb hιc]
    have := congrArg ι hbe
    simp only [map_mul, map_neg] at this
    simp only [a'', map_neg, map_mul]
    linear_combination (ι a) * this
  -- a monic relation of `a''`
  obtain ⟨q, hqm, hq⟩ := hint a''
  refine ⟨q.comp (Polynomial.C (p.coeff 0) * Polynomial.X), ?_, ?_⟩
  · intro h0
    rw [Polynomial.comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨-, h0⟩
    · exact hqm.ne_zero h0
    · have := congrArg (fun r => Polynomial.coeff r 1) h0
      simp at this
      exact hp0 this
  · have hψ : (Polynomial.aeval (R := ℂ) (ι t₀)).toRingHom = ι.comp φ := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · simp only [φ, ι, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C, RingHom.comp_apply]
        exact IsScalarTower.algebraMap_apply ℂ C.Ring C.FunctionField c
      · simp [φ, ι]
    rw [Polynomial.eval₂_comp, hψ]
    have hlin : (Polynomial.C (p.coeff 0) * Polynomial.X).eval₂ (ι.comp φ) (ι a / ι b) = ι a'' := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, hf, RingHom.comp_apply]
      have hιc : ι (φ (p.coeff 0)) ≠ 0 := fun h => hc0 (hι (by rw [h, map_zero]))
      field_simp
    rw [hlin, ← Polynomial.hom_eval₂, hq, map_zero]

/-- The function of a constant polynomial is the constant. -/
theorem fn_C_eq_algebraMap (c : ℂ) : C.fn (MvPolynomial.C c) = algebraMap ℂ C.FunctionField c := by
  rw [ACurve.fn, IsScalarTower.algebraMap_apply ℂ C.Ring C.FunctionField]
  rfl

/-- The nonzero constants have order `0` at every place. -/
theorem ord_algebraMap (P : Place C) (c : ℂ) (hc : c ≠ 0) : P.ord (algebraMap ℂ C.FunctionField c) = 0 := by
  have h := P.ord_const c hc
  rwa [fn_C_eq_algebraMap] at h

/-- **The residue field of every place of a curve is `ℂ`.** -/
theorem exists_residue_place [Finite σ] (P : Place C) {f : C.FunctionField} (hf : 0 ≤ P.ord f) :
    ∃ c : ℂ, 0 < P.ord (f - algebraMap ℂ C.FunctionField c) := by
  obtain ⟨t₀, hinj, hint⟩ := curve_noether C
  set x₀ := algebraMap C.Ring C.FunctionField t₀
  have hrel : ∀ g, AlgRel x₀ g := algRel_of_curve hinj hint
  have hconst : ∀ c : ℂ, c ≠ 0 → P.ord (algebraMap ℂ C.FunctionField c) = 0 := ord_algebraMap P
  -- `x₀` is not a constant
  have hx₀c : ∀ c : ℂ, x₀ - algebraMap ℂ C.FunctionField c ≠ 0 := by
    intro c h
    have h1 : Polynomial.aeval t₀ (Polynomial.X - Polynomial.C c) = 0 := by
      apply IsFractionRing.injective C.Ring C.FunctionField
      rw [map_zero, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_sub,
        ← IsScalarTower.algebraMap_apply]
      exact h
    have := hinj (h1.trans (map_zero _).symm)
    exact Polynomial.X_sub_C_ne_zero c this
  have hx₀ : x₀ ≠ 0 := by simpa using hx₀c 0
  -- an element of positive order algebraic relations go through
  obtain ⟨x, hx0, hxpos, hxrel⟩ : ∃ x : C.FunctionField, x ≠ 0 ∧ 0 < P.ord x ∧ AlgRel x f := by
    rcases lt_trichotomy (P.ord x₀) 0 with hneg | hzero | hpos
    · refine ⟨x₀⁻¹, inv_ne_zero hx₀, ?_, algRel_inv hx₀ (hrel f)⟩
      have h1 : P.ord x₀⁻¹ + P.ord x₀ = 0 := by
        rw [← AddValuation.map_mul, inv_mul_cancel₀ hx₀, AddValuation.map_one]
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hneg)
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff P.ord).mpr (inv_ne_zero hx₀))
      rw [← hn] at hneg h1
      rw [← hk] at h1 ⊢
      have hn' : n < 0 := by exact_mod_cast hneg
      have h1' : k + n = 0 := by exact_mod_cast h1
      exact_mod_cast (show (0 : ℤ) < k by omega)
    · -- some `x₀ − c` has positive order
      obtain ⟨c, hc⟩ : ∃ c : ℂ, 0 < P.ord (x₀ - algebraMap ℂ C.FunctionField c) := by
        by_contra hall
        push Not at hall
        have hzero' : ∀ c : ℂ, P.ord (x₀ - algebraMap ℂ C.FunctionField c) = 0 := fun c =>
          le_antisymm (hall c) (le_trans (le_min hzero.ge (hconst_nonneg P.ord hconst c)) (AddValuation.map_sub _ _ _))
        have htriv : ∀ q : Polynomial ℂ, q ≠ 0 → P.ord (Polynomial.aeval x₀ q) = 0 := by
          intro q hq
          rw [val_aeval_eq_sum_roots P.ord hconst hq x₀, Multiset.map_congr rfl fun c _ => hzero' c,
            Multiset.map_const', Multiset.sum_replicate, nsmul_zero]
        obtain ⟨u, hu⟩ := P.exists_ord_eq_one
        have hu0 : u ≠ 0 := by
          rintro rfl
          rw [AddValuation.map_zero] at hu
          exact WithTop.top_ne_coe hu
        have := val_eq_zero_of_algRel P.ord hu0 (hrel u) htriv
        rw [hu] at this
        exact one_ne_zero (WithTop.coe_injective this)
      exact ⟨x₀ - algebraMap ℂ C.FunctionField c, hx₀c c, hc, algRel_shift (hrel f) c⟩
    · exact ⟨x₀, hx₀, hpos, hrel f⟩
  exact exists_residue P.ord hconst hx0 hxpos hf hxrel

end

end CC6Full
