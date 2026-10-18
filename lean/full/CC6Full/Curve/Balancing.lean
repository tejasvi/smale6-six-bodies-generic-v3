import CC6Full.Curve.Places6

/-!
# Balancing (Lemma 2.6, `lem:balance`) and Corollary 2.7 (`cor:sum`)

Lemma 2.6 (`lem:balance`):

> Let `C` be a nontrivial curve. Then `C` has at least one singular place, and `Σ_{P singular} d_P x(P) = 0`.

Corollary 2.7 (`cor:sum`):

> Let `C` be a nontrivial curve. Some singular place `P` of `C` has `ℓ(x(P)) ≤ 0`.

Here `ℓ(x) = Σ_{k<l} x_kl`. The proof is that of the paper (and of the five-body formalization,
`CC5Full/Theory/FunctionField/Divisor.lean`):

* the singular places form a finite set: a singular place is a pole of some coordinate function
  (`Place.exists_neg_of_singular`), and a coordinate function has finitely many poles (`ACurve.exists_finset_poles`,
  from `degree_zero`);
* for each pair `e`, `Σ_P ν_P(p_e) = 0` over any finite set of places containing those where `ν(p_e) ≠ 0`
  (`ACurve.sum_ordZ_eq_zero`, from `degree_zero`, or `p_e` is constant), and `ν(p_e) = 0` off the singular places
  (`Curve.v_pP_eq_zero_of_not_singular`); so `Σ_{P singular} d_P x_e(P) = −2 Σ_P ν_P(p_e) = 0`;
* some `r²_kl` is not constant, so it has a pole `P` (`exists_pole`); since `p_kl² r²_kl = 1`, `ν_P(p_kl) ≠ 0`, and
  `P` is singular.
-/

namespace CC6Full

open Finset MvPolynomial Curve

noncomputable section

section general

variable {σ : Type*} {C : ACurve σ}

/-- A polynomial whose function is a constant is constant on the curve. -/
theorem ACurve.isConst_of_fn_eq {f : MvPolynomial σ ℂ} {c : ℂ} (h : C.fn f = algebraMap ℂ C.FunctionField c) :
    C.IsConst f :=
  ⟨c, by rw [← ACurve.fn_eq_zero_iff, ← ACurve.fnHom_apply, map_sub, ACurve.fnHom_apply, ACurve.fnHom_apply, h,
    fn_C_eq_algebraMap, sub_self]⟩

/-- The function of a polynomial has finitely many poles. -/
theorem ACurve.exists_finset_poles [Finite σ] (C : ACurve σ) (f : MvPolynomial σ ℂ) :
    ∃ S : Finset (Place C), ∀ P : Place C, P.v f < 0 → P ∈ S := by
  rcases const_or_transcendental (C.fn f) with ⟨a, ha⟩ | htr
  · refine ⟨∅, fun P hP => absurd hP ?_⟩
    rw [Place.v, ha]
    by_cases ha0 : a = 0
    · rw [ha0, map_zero, AddValuation.map_zero]
      exact not_lt.mpr le_top
    · rw [ord_algebraMap P a ha0]
      exact lt_irrefl _
  · obtain ⟨S, hS, -⟩ := degree_zero htr
    exact ⟨S, fun P hP => (hS P).mpr (ne_of_lt hP)⟩

/-- **Degree zero**: the orders of a function sum to zero over every finite set of places containing those where its
order is not zero. -/
theorem ACurve.sum_ordZ_eq_zero [Finite σ] (g : C.FunctionField) (S : Finset (Place C))
    (hS : ∀ P : Place C, P.ord g ≠ 0 → P ∈ S) : ∑ P ∈ S, ordZ P.ord g = 0 := by
  classical
  rcases const_or_transcendental g with ⟨a, ha⟩ | htr
  · refine Finset.sum_eq_zero fun P _ => ?_
    rw [ha]
    by_cases ha0 : a = 0
    · rw [ha0, map_zero, ordZ, AddValuation.map_zero]
      rfl
    · rw [ordZ, ord_algebraMap P a ha0]
      rfl
  · obtain ⟨T, hT, hsum⟩ := degree_zero htr
    rw [← hsum]
    symm
    apply Finset.sum_subset
    · intro P hP
      exact hS P ((hT P).mp hP)
    · intro P _ hPT
      have h0 : P.ord g = 0 := by
        by_contra h
        exact hPT ((hT P).mpr h)
      rw [ordZ, h0]
      rfl

end general

variable {n : ℕ} {m : Fin (n + 2) → ℝ}

/-- **Lemma 2.6** (`lem:balance`): on a nontrivial curve `C` the singular places form a finite nonempty set `S`,
`d_P > 0` for `P ∈ S`, and `Σ_{P ∈ S} d_P x(P) = 0` (equation (2.3), `eq:balx`). -/
theorem Curve.balancing {C : Curve n m} (hC : C.Nontrivial) :
    ∃ S : Finset (Place C.toACurve), (∀ P, P ∈ S ↔ P.Singular) ∧ S.Nonempty ∧ (∀ P ∈ S, 0 < P.dd) ∧
      ∑ P ∈ S, P.dd • P.type = 0 := by
  classical
  choose Sc hSc using fun c : Coord (n + 2) => C.toACurve.exists_finset_poles (X c)
  set S : Finset (Place C.toACurve) := (Finset.univ.biUnion Sc).filter (fun P => P.Singular) with hS_def
  have hS : ∀ P, P ∈ S ↔ P.Singular := by
    intro P
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      obtain ⟨c, hc⟩ := P.exists_neg_of_singular h
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hSc c P hc⟩, h⟩
  refine ⟨S, hS, ?_, fun P hP => P.dd_pos ((hS P).mp hP), ?_⟩
  · -- a pole of a nonconstant `r²_kl` is singular
    obtain ⟨-, k, l, hkl⟩ := hC
    have hne : k ≠ l := by
      rintro rfl
      exact hkl ⟨0, by simp [r2P]⟩
    have htr : Transcendental ℂ (C.fn (r2P k l)) := by
      rcases const_or_transcendental (C.fn (r2P k l)) with ⟨a, ha⟩ | h
      · exact absurd (ACurve.isConst_of_fn_eq ha) hkl
      · exact h
    obtain ⟨P, hP⟩ := exists_pole htr
    refine ⟨P, (hS P).mpr ?_⟩
    by_contra hns
    have h0 := C.v_pP_eq_zero_of_not_singular hns hne
    have hD := C.ordZ_dist P hne
    have ha : ordZ P.ord (C.fn (pP k l)) = 0 := by
      rw [ordZ, show P.ord (C.fn (pP k l)) = P.v (pP k l) from rfl, h0]
      rfl
    have hbc : ordZ P.ord (C.fn (zP k - zP l)) + ordZ P.ord (C.fn (wP k - wP l)) = 0 := by
      rw [ha] at hD
      linarith
    have hr : P.v (r2P k l) = 0 := by
      rw [r2P, P.v_mul, P.v_eq_ordZ (C.fn_zsub_ne_zero hne), P.v_eq_ordZ (C.fn_wsub_ne_zero hne),
        ← WithTop.coe_add, hbc]
      rfl
    have hP' : P.v (r2P k l) < 0 := hP
    rw [hr] at hP'
    exact lt_irrefl _ hP'
  · funext e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hterm : ∀ P ∈ S, P.dd * P.type e = -2 * (ordZ P.ord (C.fn (X (pc e))) : ℚ) := by
      intro P hP
      have hd := (P.dd_pos ((hS P).mp hP)).ne'
      simp only [Place.type]
      field_simp
    have hsing : ∀ P : Place C.toACurve, P.ord (C.fn (X (pc e))) ≠ 0 → P ∈ S := by
      intro P hP
      rw [hS]
      by_contra hns
      apply hP
      have := C.v_pP_eq_zero_of_not_singular hns (ne_of_lt e.2)
      rwa [pP_pair] at this
    have hsum : ∑ P ∈ S, ordZ P.ord (C.fn (X (pc e))) = 0 := ACurve.sum_ordZ_eq_zero _ S hsing
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Int.cast_sum, hsum, Int.cast_zero, mul_zero]

/-- `ℓ(x(P)) = Σ_{k<l} x_kl(P)`. -/
def Place.ell {N : ℕ} {C : ACurve (Coord N)} (P : Place C) : ℚ := ∑ e, P.type e

/-- **Corollary 2.7** (`cor:sum`): some singular place `P` of a nontrivial curve has `ℓ(x(P)) ≤ 0`. -/
theorem Curve.exists_singular_place_ell_nonpos {C : Curve n m} (hC : C.Nontrivial) :
    ∃ P : Place C.toACurve, P.Singular ∧ P.ell ≤ 0 := by
  obtain ⟨S, hS, hne, hd, hsum⟩ := Curve.balancing hC
  by_contra hcon
  have hpos : ∀ P ∈ S, 0 < P.dd * P.ell := fun P hP =>
    mul_pos (hd P hP) (lt_of_not_ge fun hle => hcon ⟨P, (hS P).mp hP, hle⟩)
  have h1 : ∑ P ∈ S, P.dd * P.ell = 0 := by
    have := congrArg (fun x : Pair (n + 2) → ℚ => ∑ e, x e) hsum
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.sum_const_zero] at this
    rw [Finset.sum_comm] at this
    simpa only [Place.ell, Finset.mul_sum] using this
  have h2 := Finset.sum_pos hpos hne
  linarith

end

end CC6Full
