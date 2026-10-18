import CC6Full.Six.D88
import CC6Full.Six.D94
import Lean6.Special.D88.Count.Main

/-!
# Bridge: the dimension bounds of Lemma 6.19(b) from the certificate project

`d88Dim : D88Dim` and `d94Dim : D94Dim` from `count_S12` and `count_KC` of the certificate project
(`Lean6.Special.D88.Count`), which bound the dimension over `ZMod 65521` of `(ZMod 65521)[v] ⧸ ⟨S12(μ₀)⟩` by `20316`
and of `(ZMod 65521)[v′] ⧸ ⟨KC′(μ₀)⟩` by `4788`, with the equations of §6.7 written there.

* `S12`: our rows (`D88.rows12`, the denominator `μ₄` cleared) at `μ₀ = (1, 2, 3, 30)` are those of the certificate
  project times the units `1` and `900 = μ₄²` (`rows12_eq_s12`), so its ideal is contained in ours and our quotient is a
  quotient of its quotient.
* `KC`: our system `KC` lives in the twelve unknowns `X₂, X₃, Y₁, …, Y₄, p_kl`; the certificate project's `KC′` in the
  eleven unknowns `X₂, X₃, U_k = Y_k − Y₄, p_kl`, with `Y₄` eliminated by the `Y`-equation of body `1`. The algebra map
  `U_k ↦ Y_k − Y₄` sends the equations of `KC′` into the ideal of `KC` (`kcSys_wOf`: the `Y`-equations of `KC′` are
  differences of those of `KC`) and is onto modulo that ideal (`Y₄` is the image of the eliminated expression
  `kcY4`), so our quotient is again a quotient of the certificate project's.
-/

namespace CC6Compose

open CC6Full CC6Full.Six MvPolynomial

/-- A surjective linear map does not increase the dimension. -/
theorem finrank_le_of_surjective {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] [Module.Finite K M] (f : M →ₗ[K] N) (hf : Function.Surjective f) :
    Module.finrank K N ≤ Module.finrank K M := by
  have h := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.mpr hf, finrank_top] at h

/-! ## S12 -/

/-- **Our rows of `S12` at `μ₀` are the certificate project's rows times `1` or `900`**, at every point of every
commutative ring in which `30 · i₄ = 1`. -/
theorem rows12_eq_s12 {R : Type*} [CommRing R] (i4 : R) (h4 : 30 * i4 = 1) (v : Fin 11 → R) (j : Fin 12) :
    D88.rows12 (Lean6.Special.D88.Count.μ0 : Fin 4 → R) v j =
      Lean6.Special.D88.Count.s12U j * Lean6.Special.D88.Count.s12Sys Lean6.Special.D88.Count.μ0 i4 v j := by
  fin_cases j
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      first
      | linear_combination (v 7 ^ 3 * (3 * v 0 + 3 * v 1 + 1)) * h4
      | linear_combination (-(v 7 ^ 3 * (3 * v 0 + 3 * v 1 + 1))) * h4
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      first
      | linear_combination (v 9 ^ 3 * (3 * v 0 + 3 * v 1 + 1)) * h4
      | linear_combination (-(v 9 ^ 3 * (3 * v 0 + 3 * v 1 + 1))) * h4
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      first
      | linear_combination (v 10 ^ 3 * (3 * v 0 + 3 * v 1 + 1)) * h4
      | linear_combination (-(v 10 ^ 3 * (3 * v 0 + 3 * v 1 + 1))) * h4
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      first
      | linear_combination (v 7 ^ 3 * (v 2 + 2 * v 3 + 3 * v 4)) * h4
      | linear_combination (-(v 7 ^ 3 * (v 2 + 2 * v 3 + 3 * v 4))) * h4
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      first
      | linear_combination (v 9 ^ 3 * (v 2 + 2 * v 3 + 3 * v 4)) * h4
      | linear_combination (-(v 9 ^ 3 * (v 2 + 2 * v 3 + 3 * v 4))) * h4
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      first
      | linear_combination (v 10 ^ 3 * (v 2 + 2 * v 3 + 3 * v 4)) * h4
      | linear_combination (-(v 10 ^ 3 * (v 2 + 2 * v 3 + 3 * v 4))) * h4
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      ring
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      ring
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      first
      | linear_combination (v 7 ^ 2 * (30 * ((3 * v 0 + 3 * v 1 + 1) * v 2 + (v 2 + 2 * v 3 + 3 * v 4) * (v 0 + 1)) + (1 + 30 * i4) * (3 * v 0 + 3 * v 1 + 1) * (v 2 + 2 * v 3 + 3 * v 4))) * h4
      | linear_combination (-(v 7 ^ 2 * (30 * ((3 * v 0 + 3 * v 1 + 1) * v 2 + (v 2 + 2 * v 3 + 3 * v 4) * (v 0 + 1)) + (1 + 30 * i4) * (3 * v 0 + 3 * v 1 + 1) * (v 2 + 2 * v 3 + 3 * v 4)))) * h4
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      ring
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      first
      | linear_combination (v 9 ^ 2 * (30 * ((3 * v 0 + 3 * v 1 + 1) * v 3 + (v 2 + 2 * v 3 + 3 * v 4) * v 0) + (1 + 30 * i4) * (3 * v 0 + 3 * v 1 + 1) * (v 2 + 2 * v 3 + 3 * v 4))) * h4
      | linear_combination (-(v 9 ^ 2 * (30 * ((3 * v 0 + 3 * v 1 + 1) * v 3 + (v 2 + 2 * v 3 + 3 * v 4) * v 0) + (1 + 30 * i4) * (3 * v 0 + 3 * v 1 + 1) * (v 2 + 2 * v 3 + 3 * v 4)))) * h4
  · simp [D88.rows12, D88.rowX, D88.rowY, D88.rowD, D88.rowD4, D88.gX, D88.gY, D88.gmX, D88.gmY, D88.gp,
        Lean6.Special.D88.Count.s12Sys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.distEq,
        Lean6.Special.D88.Count.s12X, Lean6.Special.D88.Count.s12Y, Lean6.Special.D88.Count.pm,
        Lean6.Special.D88.Count.μ0, Lean6.Special.D88.Count.s12U, Fin.sum_univ_four] <;>
      first
      | linear_combination (v 10 ^ 2 * (30 * ((3 * v 0 + 3 * v 1 + 1) * v 4 + (v 2 + 2 * v 3 + 3 * v 4) * v 1) + (1 + 30 * i4) * (3 * v 0 + 3 * v 1 + 1) * (v 2 + 2 * v 3 + 3 * v 4))) * h4
      | linear_combination (-(v 10 ^ 2 * (30 * ((3 * v 0 + 3 * v 1 + 1) * v 4 + (v 2 + 2 * v 3 + 3 * v 4) * v 1) + (1 + 30 * i4) * (3 * v 0 + 3 * v 1 + 1) * (v 2 + 2 * v 3 + 3 * v 4)))) * h4

/-- The masses `μ₀` reduced modulo `p` are the numerals `1, 2, 3, 30`. -/
theorem C_redPt_X_eq {σ : Type*} (k : Fin 4) :
    (C (redPt 65521 μ0Z (X k)) : MvPolynomial σ (ZMod 65521)) = Lean6.Special.D88.Count.μ0 k := by
  fin_cases k <;> simp [redPt, μ0Z, Lean6.Special.D88.Count.μ0] <;> exact map_ofNat C _

/-- Our `S12` at `μ₀`, reduced modulo `p`, as the rows `rows12` over `ZMod 65521`. -/
theorem map_S12P_eq (j : Fin 12) :
    map (redPt 65521 μ0Z) (D88.S12P j) =
      D88.rows12 (Lean6.Special.D88.Count.μ0 : Fin 4 → MvPolynomial (Fin 11) (ZMod 65521)) X j := by
  have h1 : (fun k => map (redPt 65521 μ0Z) (C (X k) : MvPolynomial (Fin 11) (MvPolynomial (Fin 4) ℤ))) =
      (Lean6.Special.D88.Count.μ0 : Fin 4 → MvPolynomial (Fin 11) (ZMod 65521)) := by
    funext k
    rw [map_C, C_redPt_X_eq]
  have h2 : (fun j => map (redPt 65521 μ0Z) (X j : MvPolynomial (Fin 11) (MvPolynomial (Fin 4) ℤ))) = X := by
    funext j
    rw [map_X]
  rw [D88.S12P, D88.map_rows12 (map (redPt 65521 μ0Z)), h1, h2]

/-- Our ideal of `S12` at `μ₀` modulo `p`. -/
noncomputable abbrev I88 : Ideal (MvPolynomial (Fin 11) (ZMod 65521)) :=
  Ideal.span (Set.range fun i => map (redPt 65521 μ0Z) (D88.S12P i))

theorem s12U_isUnit (j : Fin 12) :
    IsUnit (Lean6.Special.D88.Count.s12U j : MvPolynomial (Fin 11) (ZMod 65521)) := by
  have h900 : IsUnit (900 : MvPolynomial (Fin 11) (ZMod 65521)) := by
    rw [show (900 : MvPolynomial (Fin 11) (ZMod 65521)) = C 900 from (map_ofNat C 900).symm]
    exact (isUnit_iff_ne_zero.mpr (by decide : (900 : ZMod 65521) ≠ 0)).map C
  fin_cases j <;> simp [Lean6.Special.D88.Count.s12U, h900]

/-- **The ideal of the certificate project's `S12` lies in ours.** -/
theorem span_S12eqs_le : Ideal.span (Set.range Lean6.Special.D88.Count.S12eqs) ≤ I88 := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  have hrow : map (redPt 65521 μ0Z) (D88.S12P j) =
      Lean6.Special.D88.Count.s12U j * Lean6.Special.D88.Count.S12eqs j := by
    rw [map_S12P_eq]
    exact rows12_eq_s12 _ Lean6.Special.D88.Count.thirty_mul_inv X j
  obtain ⟨u, hu⟩ := s12U_isUnit j
  have : Lean6.Special.D88.Count.S12eqs j = ↑u⁻¹ * map (redPt 65521 μ0Z) (D88.S12P j) := by
    rw [hrow, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- **Lemma 6.19(b) for diagram 88** (`D88Dim`), from `count_S12`. -/
theorem d88Dim_of (h : type_of% @Lean6.Special.D88.Count.count_S12) : D88Dim := by
  obtain ⟨hfin, hle⟩ := h
  have := hfin
  exact (finrank_le_of_surjective (Ideal.Quotient.factorₐ (ZMod 65521) span_S12eqs_le).toLinearMap
    (Ideal.Quotient.factor_surjective span_S12eqs_le)).trans hle

theorem d88Dim : D88Dim := d88Dim_of Lean6.Special.D88.Count.count_S12

/-! ## KC -/

/-- The point of `KC′` of a point of `KC`: `(X₂, X₃, Y₁ − Y₄, Y₂ − Y₄, Y₃ − Y₄, p₁₂, …, p₃₄)`. -/
def wOf {R : Type*} [CommRing R] (v : Fin 12 → R) : Fin 11 → R :=
  ![v 0, v 1, v 2 - v 5, v 3 - v 5, v 4 - v 5, v 6, v 7, v 8, v 9, v 10, v 11]

/-- The combination of the equations of `KC` that gives the equations of `KC′`: the `X`-equations, the equation of
the centre and the distances unchanged, and the `Y`-equations of bodies `2` and `3` minus that of body `1`. -/
def kcComb {R : Type*} [CommRing R] (r : Fin 13 → R) : Fin 12 → R :=
  ![r 0, r 1, r 2, r 3, r 5 - r 4, r 12 - r 4, r 6, r 7, r 8, r 9, r 10, r 11]

/-- **The equations of `KC′` at the point `wOf v` are combinations of those of `KC` at `v`.** -/
theorem kcSys_wOf {R : Type*} [CommRing R] (v : Fin 12 → R) (j : Fin 12) :
    Lean6.Special.D88.Count.kcSys Lean6.Special.D88.Count.μ0 (wOf v) j =
      kcComb (D94.KC Lean6.Special.D88.Count.μ0 v) j := by
  fin_cases j <;>
    simp [Lean6.Special.D88.Count.kcSys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.kcCentre,
      Lean6.Special.D88.Count.kcYeq, Lean6.Special.D88.Count.kcY4, Lean6.Special.D88.Count.distEq,
      Lean6.Special.D88.Count.kcX, Lean6.Special.D88.Count.kcU, Lean6.Special.D88.Count.pm, kcComb, D94.KC,
      D94.Xeq, D94.Xc, D94.Yeq, D94.dist, D94.X, D94.Y, D94.p, wOf, Fin.sum_univ_four] <;>
    ring

theorem kcComb_mem {A : Type*} [CommRing A] {I : Ideal A} {r : Fin 13 → A} (h : ∀ i, r i ∈ I) (j : Fin 12) :
    kcComb r j ∈ I := by
  fin_cases j <;> simp only [kcComb] <;> simp <;>
    first
    | exact h _
    | exact I.sub_mem (h _) (h _)

/-- The eliminated `Y₄` of `KC′` at `wOf v` is `Y₄` minus the `Y`-equation of body `1` of `KC`. -/
theorem kcY4_wOf {R : Type*} [CommRing R] (v : Fin 12 → R) :
    Lean6.Special.D88.Count.kcY4 Lean6.Special.D88.Count.μ0 (wOf v) =
      v 5 - D94.KC Lean6.Special.D88.Count.μ0 v 4 := by
  simp [Lean6.Special.D88.Count.kcY4, Lean6.Special.D88.Count.kcU, Lean6.Special.D88.Count.pm, D94.KC, D94.Yeq,
    D94.Y, D94.p, wOf, Fin.sum_univ_four]
  ring

/-- `kcSys` commutes with ring maps. -/
theorem map_kcSys {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (μ : Fin 4 → A) (v : Fin 11 → A)
    (j : Fin 12) :
    f (Lean6.Special.D88.Count.kcSys μ v j) =
      Lean6.Special.D88.Count.kcSys (fun k => f (μ k)) (fun i => f (v i)) j := by
  fin_cases j <;>
    simp [Lean6.Special.D88.Count.kcSys, Lean6.Special.D88.Count.bodyEq, Lean6.Special.D88.Count.kcCentre,
      Lean6.Special.D88.Count.kcYeq, Lean6.Special.D88.Count.kcY4, Lean6.Special.D88.Count.distEq,
      Lean6.Special.D88.Count.kcX, Lean6.Special.D88.Count.kcU, Lean6.Special.D88.Count.pm, Fin.sum_univ_four]

/-- `kcY4` commutes with ring maps. -/
theorem map_kcY4 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (μ : Fin 4 → A) (v : Fin 11 → A) :
    f (Lean6.Special.D88.Count.kcY4 μ v) = Lean6.Special.D88.Count.kcY4 (fun k => f (μ k)) (fun i => f (v i)) := by
  simp [Lean6.Special.D88.Count.kcY4, Lean6.Special.D88.Count.kcU, Lean6.Special.D88.Count.pm, Fin.sum_univ_four]

/-- Our ideal of `KC` at `μ₀` modulo `p`. -/
noncomputable abbrev I94 : Ideal (MvPolynomial (Fin 12) (ZMod 65521)) :=
  Ideal.span (Set.range fun i => map (redPt 65521 μ0Z) (D94.KCP i))

/-- Our `KC` at `μ₀`, reduced modulo `p`. -/
theorem map_KCP_eq (i : Fin 13) :
    map (redPt 65521 μ0Z) (D94.KCP i) =
      D94.KC (Lean6.Special.D88.Count.μ0 : Fin 4 → MvPolynomial (Fin 12) (ZMod 65521)) X i := by
  rw [D94.KCP, D94.map_KC (map (redPt 65521 μ0Z))]
  congr 1
  · funext k
    rw [map_C, C_redPt_X_eq]
  · funext j
    rw [map_X]

theorem KC_mem_I94 (i : Fin 13) :
    D94.KC (Lean6.Special.D88.Count.μ0 : Fin 4 → MvPolynomial (Fin 12) (ZMod 65521)) X i ∈ I94 := by
  rw [← map_KCP_eq]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The algebra map `U_k ↦ Y_k − Y₄` from the polynomial ring of `KC′` to our quotient. -/
noncomputable def phi94 : MvPolynomial (Fin 11) (ZMod 65521) →ₐ[ZMod 65521] MvPolynomial (Fin 12) (ZMod 65521) ⧸ I94 :=
  (Ideal.Quotient.mkₐ (ZMod 65521) I94).comp (aeval (wOf X))

theorem μ0_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    (fun k => f ((Lean6.Special.D88.Count.μ0 : Fin 4 → A) k)) = (Lean6.Special.D88.Count.μ0 : Fin 4 → B) := by
  funext k
  fin_cases k <;> simp [Lean6.Special.D88.Count.μ0] <;> exact map_ofNat f _

theorem aeval_kcSys (j : Fin 12) :
    aeval (wOf (X : Fin 12 → MvPolynomial (Fin 12) (ZMod 65521))) (Lean6.Special.D88.Count.KCprimeEqs j) =
      Lean6.Special.D88.Count.kcSys Lean6.Special.D88.Count.μ0 (wOf X) j := by
  have h := map_kcSys (aeval (R := ZMod 65521) (wOf (X : Fin 12 → MvPolynomial (Fin 12) (ZMod 65521)))).toRingHom
    Lean6.Special.D88.Count.μ0 X j
  rw [μ0_map] at h
  simpa [Lean6.Special.D88.Count.KCprimeEqs] using h

theorem kcSys_wOf_mem (j : Fin 12) :
    Lean6.Special.D88.Count.kcSys Lean6.Special.D88.Count.μ0
      (wOf (X : Fin 12 → MvPolynomial (Fin 12) (ZMod 65521))) j ∈ I94 := by
  rw [kcSys_wOf]
  exact kcComb_mem KC_mem_I94 j

theorem span_KCprime_le_ker : Ideal.span (Set.range Lean6.Special.D88.Count.KCprimeEqs) ≤ RingHom.ker phi94 := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  show Ideal.Quotient.mk I94 (aeval (wOf X) (Lean6.Special.D88.Count.KCprimeEqs j)) = 0
  rw [aeval_kcSys, Ideal.Quotient.eq_zero_iff_mem]
  exact kcSys_wOf_mem j

/-- The induced map from the certificate project's quotient to ours. -/
noncomputable def psi94 : Lean6.Special.D88.Count.AqKC →ₐ[ZMod 65521] MvPolynomial (Fin 12) (ZMod 65521) ⧸ I94 :=
  Ideal.Quotient.liftₐ _ phi94 fun _ ha => (RingHom.mem_ker).mp (span_KCprime_le_ker ha)

theorem phi94_surjective : Function.Surjective phi94 := by
  have hY4 : phi94 (Lean6.Special.D88.Count.kcY4 Lean6.Special.D88.Count.μ0 (X : Fin 11 → MvPolynomial (Fin 11) (ZMod 65521))) = Ideal.Quotient.mk I94 (X 5) := by
    have h := map_kcY4 (aeval (R := ZMod 65521) (wOf (X : Fin 12 → MvPolynomial (Fin 12) (ZMod 65521)))).toRingHom
      Lean6.Special.D88.Count.μ0 X
    rw [μ0_map] at h
    have h' : aeval (wOf (X : Fin 12 → MvPolynomial (Fin 12) (ZMod 65521)))
        (Lean6.Special.D88.Count.kcY4 Lean6.Special.D88.Count.μ0
          (X : Fin 11 → MvPolynomial (Fin 11) (ZMod 65521))) =
          Lean6.Special.D88.Count.kcY4 Lean6.Special.D88.Count.μ0 (wOf X) := by simpa using h
    show Ideal.Quotient.mk I94 (aeval (wOf X) _) = _
    rw [h', kcY4_wOf, Ideal.Quotient.eq]
    simpa using KC_mem_I94 4
  have hX : ∀ i : Fin 11, phi94 (X i) = Ideal.Quotient.mk I94 (wOf X i) := fun i => by
    simp [phi94]
  have hgen : ∀ i : Fin 12, Ideal.Quotient.mk I94 (X i) ∈ phi94.range := by
    intro i
    fin_cases i
    · exact (AlgHom.mem_range _).mpr ⟨X 0, by rw [hX]; rfl⟩
    · exact (AlgHom.mem_range _).mpr ⟨X 1, by rw [hX]; rfl⟩
    · refine (AlgHom.mem_range _).mpr ⟨X 2 + Lean6.Special.D88.Count.kcY4 Lean6.Special.D88.Count.μ0 X, ?_⟩
      rw [map_add, hY4, hX, ← map_add]
      simp [wOf]
    · refine (AlgHom.mem_range _).mpr ⟨X 3 + Lean6.Special.D88.Count.kcY4 Lean6.Special.D88.Count.μ0 X, ?_⟩
      rw [map_add, hY4, hX, ← map_add]
      simp [wOf]
    · refine (AlgHom.mem_range _).mpr ⟨X 4 + Lean6.Special.D88.Count.kcY4 Lean6.Special.D88.Count.μ0 X, ?_⟩
      rw [map_add, hY4, hX, ← map_add]
      simp [wOf]
    · exact (AlgHom.mem_range _).mpr ⟨_, hY4⟩
    · exact (AlgHom.mem_range _).mpr ⟨X 5, by rw [hX]; rfl⟩
    · exact (AlgHom.mem_range _).mpr ⟨X 6, by rw [hX]; rfl⟩
    · exact (AlgHom.mem_range _).mpr ⟨X 7, by rw [hX]; rfl⟩
    · exact (AlgHom.mem_range _).mpr ⟨X 8, by rw [hX]; rfl⟩
    · exact (AlgHom.mem_range _).mpr ⟨X 9, by rw [hX]; rfl⟩
    · exact (AlgHom.mem_range _).mpr ⟨X 10, by rw [hX]; rfl⟩
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmem : Ideal.Quotient.mk I94 f ∈ phi94.range := by
    induction f using MvPolynomial.induction_on with
    | C a =>
      refine (AlgHom.mem_range _).mpr ⟨C a, ?_⟩
      show Ideal.Quotient.mk I94 (aeval (wOf X) (C a)) = Ideal.Quotient.mk I94 (C a)
      rw [aeval_C, MvPolynomial.algebraMap_eq]
    | add f g hf hg => rw [map_add]; exact phi94.range.add_mem hf hg
    | mul_X f i hf => rw [map_mul]; exact phi94.range.mul_mem hf (hgen i)
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).mp hmem
  exact ⟨x, hx⟩

/-- **Lemma 6.19(b) for diagram 94** (`D94Dim`), from `count_KC`. -/
theorem d94Dim_of (h : type_of% @Lean6.Special.D88.Count.count_KC) : D94Dim := by
  obtain ⟨hfin, hle⟩ := h
  have := hfin
  have hsurj : Function.Surjective psi94 := by
    intro y
    obtain ⟨x, hx⟩ := phi94_surjective y
    exact ⟨Ideal.Quotient.mk _ x, hx⟩
  exact (finrank_le_of_surjective psi94.toLinearMap hsurj).trans hle

theorem d94Dim : D94Dim := d94Dim_of Lean6.Special.D88.Count.count_KC

end CC6Compose
