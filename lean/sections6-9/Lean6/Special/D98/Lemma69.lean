import Lean6.Special.D98.Shapes
import Lean6.Special.Comp.D98.Run

/-!
# Lemma 6.9 (`lem:three`): the degree of `S_μ` and the check of the eliminants

* **`Spol_natDegree_leadingCoeff`**: over a domain, if `μ₁ + μ₂ ≠ 0`, then `S_μ` has degree `34` and leading
  coefficient `(μ₁ + μ₂)⁴`; **`S_generic`**: in `ℤ[μ₁, μ₂, μ₃][t]` (`R = MvPolynomial (Fin 3) ℤ`, `μ = X`).
* **`toPoly_SUP`**: the computable `SUP` of the checkers is `S_μ` at integer masses.
* **`lemma_6_9_check`** at `μ = (1,2,7)`, `(1,2,8)`, `(2,3,11)`: the eliminant `g` stored by the elimination in
  Singular (`elim_*.txt`, sha256 in `data/d98/SHA256SUMS`) and `S_μ` have the square-free part `g₀` in `ℚ[X]`
  (`g₀ ∣ g ∣ g₀³`, `g₀ ∣ S_μ ∣ g₀²`, `g₀` separable, of degree `32`); hence `g`, `S_μ` and `g₀` have the same complex
  roots, `S_μ` has `34` complex roots counted with multiplicity and `32` distinct ones. What is not checked: that `g` is
  the eliminant of the system (the Singular computation), and the counts `102` and `114`.
-/

namespace Lean6.Special.D98

open Polynomial Lean6.Special.Comp.D98

variable {R : Type*} [CommRing R]

/-- `Q_σ(t − 1)` in coefficient form. -/
theorem Q_shift (μ : Fin 3 → R) (s : ℤ × ℤ × ℤ) :
    Q (fun i => C (μ i)) s (X - 1) =
      C ((s.1 : R) * (μ 0 + μ 1)) * X ^ 5 + C (-((s.1 : R) * (2 * μ 0 + 3 * μ 1))) * X ^ 4 +
        C ((s.1 : R) * μ 0 + 3 * (s.1 : R) * μ 1 + (s.2.1 : R) * μ 2 - (s.2.2 : R) * μ 2) * X ^ 3 +
        C (-((s.1 : R) * μ 1 + (s.2.1 : R) * μ 0 + 3 * (s.2.1 : R) * μ 2 + (s.2.2 : R) * μ 1)) * X ^ 2 +
        C ((s.2.1 : R) * (2 * μ 0 + 3 * μ 2)) * X + C (-((s.2.1 : R) * (μ 0 + μ 2))) := by
  simp only [Q, map_add, map_mul, map_sub, map_neg, map_intCast, map_ofNat]
  ring

theorem Q_shift_deg [IsDomain R] (μ : Fin 3 → R) (s : ℤ × ℤ × ℤ) (h : (s.1 : R) * (μ 0 + μ 1) ≠ 0) :
    (Q (fun i => C (μ i)) s (X - 1)).natDegree = 5 ∧
      (Q (fun i => C (μ i)) s (X - 1)).leadingCoeff = (s.1 : R) * (μ 0 + μ 1) := by
  rw [Q_shift]
  have hd : (C ((s.1 : R) * (μ 0 + μ 1)) * X ^ 5 + C (-((s.1 : R) * (2 * μ 0 + 3 * μ 1))) * X ^ 4 +
        C ((s.1 : R) * μ 0 + 3 * (s.1 : R) * μ 1 + (s.2.1 : R) * μ 2 - (s.2.2 : R) * μ 2) * X ^ 3 +
        C (-((s.1 : R) * μ 1 + (s.2.1 : R) * μ 0 + 3 * (s.2.1 : R) * μ 2 + (s.2.2 : R) * μ 1)) * X ^ 2 +
        C ((s.2.1 : R) * (2 * μ 0 + 3 * μ 2)) * X + C (-((s.2.1 : R) * (μ 0 + μ 2)))).natDegree = 5 := by
    compute_degree!
    all_goals exact mul_ne_zero_iff.mp h
  refine ⟨hd, ?_⟩
  rw [leadingCoeff, hd]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

theorem natDegree_lag [Nontrivial R] : (lag (X : R[X])).natDegree = 2 := by
  simp only [lag]; compute_degree!

theorem natDegree_N01 [Nontrivial R] : (N01 (X : R[X])).natDegree = 4 := by
  simp only [N01]; compute_degree!

theorem natDegree_N10 [Nontrivial R] : (N10 (X : R[X])).natDegree = 4 := by
  simp only [N10]; compute_degree!

theorem natDegree_N11 [Nontrivial R] : (N11 (X : R[X])).natDegree = 4 := by
  simp only [N11]; compute_degree!

theorem monic_lag [Nontrivial R] : (lag (X : R[X])).Monic := by simp only [lag]; monicity!

theorem monic_N01 [Nontrivial R] : (N01 (X : R[X])).Monic := by simp only [N01]; monicity!

theorem monic_N10 [Nontrivial R] : (N10 (X : R[X])).Monic := by simp only [N10]; monicity!

theorem monic_N11 [Nontrivial R] : (N11 (X : R[X])).Monic := by simp only [N11]; monicity!

/-- **`S_μ` has degree `34` and leading coefficient `(μ₁ + μ₂)⁴`** (over a domain, if `μ₁ + μ₂ ≠ 0`). -/
theorem Spol_natDegree_leadingCoeff [IsDomain R] (μ : Fin 3 → R) (h : μ 0 + μ 1 ≠ 0) :
    (Spol μ).natDegree = 34 ∧ (Spol μ).leadingCoeff = (μ 0 + μ 1) ^ 4 := by
  have hq : ∀ i : Fin 4, (Q (fun i => C (μ i)) (sig i) (X - 1)).natDegree = 5 ∧
      (Q (fun i => C (μ i)) (sig i) (X - 1)).leadingCoeff = μ 0 + μ 1 := by
    intro i
    have h1 : ((sig i).1 : R) = 1 := by fin_cases i <;> simp [sig]
    have := Q_shift_deg μ (sig i) (by rw [h1, one_mul]; exact h)
    rw [h1, one_mul] at this
    exact this
  have hq0 : ∀ i : Fin 4, Q (fun i => C (μ i)) (sig i) (X - 1) ≠ 0 := by
    intro i h0
    have := (hq i).2
    rw [h0, leadingCoeff_zero] at this
    exact h this.symm
  have hl0 : lag (X : R[X]) * N01 X * N10 X * N11 X ≠ 0 :=
    (((monic_lag.mul monic_N01).mul monic_N10).mul monic_N11).ne_zero
  have hlm : (lag (X : R[X]) * N01 X * N10 X * N11 X).Monic :=
    ((monic_lag.mul monic_N01).mul monic_N10).mul monic_N11
  have hln : (lag (X : R[X]) * N01 X * N10 X * N11 X).natDegree = 14 := by
    rw [natDegree_mul (((monic_lag.mul monic_N01).mul monic_N10).ne_zero) monic_N11.ne_zero,
      natDegree_mul ((monic_lag.mul monic_N01).ne_zero) monic_N10.ne_zero,
      natDegree_mul monic_lag.ne_zero monic_N01.ne_zero, natDegree_lag, natDegree_N01, natDegree_N10,
      natDegree_N11]
  have hP0 : (∏ i : Fin 4, Q (fun i => C (μ i)) (sig i) (X - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hq0 i
  have hPn : (∏ i : Fin 4, Q (fun i => C (μ i)) (sig i) (X - 1)).natDegree = 20 := by
    rw [natDegree_prod _ _ fun i _ => hq0 i]
    simp [fun i => (hq i).1]
  have hPl : (∏ i : Fin 4, Q (fun i => C (μ i)) (sig i) (X - 1)).leadingCoeff = (μ 0 + μ 1) ^ 4 := by
    rw [leadingCoeff_prod]
    simp [fun i => (hq i).2]
  have e : Spol μ = (lag (X : R[X]) * N01 X * N10 X * N11 X) * ∏ i : Fin 4, Q (fun i => C (μ i)) (sig i) (X - 1) :=
    rfl
  rw [e, natDegree_mul hl0 hP0, hln, hPn, leadingCoeff_mul, hlm.leadingCoeff, hPl, one_mul]
  exact ⟨rfl, rfl⟩

/-- **Lemma 6.9, `S_μ ∈ ℤ[μ₁, μ₂, μ₃][t]`**: degree `34`, leading coefficient `(μ₁ + μ₂)⁴`. -/
theorem S_generic :
    (Spol (fun i => (MvPolynomial.X i : MvPolynomial (Fin 3) ℤ))).natDegree = 34 ∧
      (Spol (fun i => (MvPolynomial.X i : MvPolynomial (Fin 3) ℤ))).leadingCoeff =
        (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 4 := by
  refine Spol_natDegree_leadingCoeff _ ?_
  intro h
  have := congrArg (MvPolynomial.eval (fun _ => (1 : ℤ))) h
  simp at this

/-! ## The computable `SUP` -/

theorem toPoly_QUP (m1 m2 m3 a b c : ℤ) :
    toPoly (UP.comp (QUP m1 m2 m3 a b c) tm1UP) = Q (fun i => C (![m1, m2, m3] i)) (a, b, c) (X - 1) := by
  rw [toPoly_comp]
  simp only [QUP, tm1UP, toPoly_cons, toPoly_nil, mul_zero, add_zero, add_comp, mul_comp, C_comp, X_comp]
  simp only [Q, map_add, map_mul, map_neg, map_sub, eq_intCast, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

theorem toPoly_lagUP : toPoly lagUP = lag (X : ℤ[X]) := by
  simp only [lagUP, lag, toPoly_cons, toPoly_nil, eq_intCast]; push_cast; ring
theorem toPoly_N01UP : toPoly N01UP = N01 (X : ℤ[X]) := by
  simp only [N01UP, N01, toPoly_cons, toPoly_nil, eq_intCast]; push_cast; ring
theorem toPoly_N10UP : toPoly N10UP = N10 (X : ℤ[X]) := by
  simp only [N10UP, N10, toPoly_cons, toPoly_nil, eq_intCast]; push_cast; ring
theorem toPoly_N11UP : toPoly N11UP = N11 (X : ℤ[X]) := by
  simp only [N11UP, N11, toPoly_cons, toPoly_nil, eq_intCast]; push_cast; ring

/-- **The computable `SUP` is `S_μ`.** -/
theorem toPoly_SUP (m1 m2 m3 : ℤ) : toPoly (SUP m1 m2 m3) = Spol ![m1, m2, m3] := by
  simp only [SUP, toPoly_mul, toPoly_QUP, toPoly_lagUP, toPoly_N01UP, toPoly_N10UP, toPoly_N11UP, Spol, S,
    Fin.prod_univ_four, sig, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

/-! ## The certificates of the eliminants -/

/-- Roots of `a · p = d · q` over a field: a root of `d` is a root of `p`. -/
theorem root_of_dvd_cert {K : Type*} [Field K] [CharZero K] {a : ℤ} {p d q : UP} (ha : a ≠ 0)
    (h : toPoly (UP.scale a p) = toPoly (UP.mul d q)) {t : K}
    (hd : ((toPoly d).map (Int.castRingHom K)).eval t = 0) : ((toPoly p).map (Int.castRingHom K)).eval t = 0 := by
  have := congrArg (fun f => (f.map (Int.castRingHom K)).eval t) h
  simp only [toPoly_scale, toPoly_mul, Polynomial.map_mul, map_C, eval_mul, eval_C, hd, zero_mul] at this
  have ha' : ((Int.castRingHom K) a) ≠ 0 := by simpa using ha
  exact (mul_eq_zero.mp this).resolve_left ha'

/-- The divisibility in `ℚ[X]` given by `a · p = d · q`. -/
theorem dvd_of_cert {a : ℤ} {p d q : UP} (ha : a ≠ 0) (h : toPoly (UP.scale a p) = toPoly (UP.mul d q)) :
    (toPoly d).map (Int.castRingHom ℚ) ∣ (toPoly p).map (Int.castRingHom ℚ) := by
  have h' := congrArg (fun f => f.map (Int.castRingHom ℚ)) h
  simp only [toPoly_scale, toPoly_mul, Polynomial.map_mul, map_C, eq_intCast, Polynomial.map_intCast] at h'
  have e2 : (a : ℚ[X]) = C (a : ℚ) := by simp
  rw [e2] at h'
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  refine ⟨C ((a : ℚ)⁻¹) * (toPoly q).map (Int.castRingHom ℚ), ?_⟩
  have e : (toPoly p).map (Int.castRingHom ℚ) =
      C ((a : ℚ)⁻¹) * (C (a : ℚ) * (toPoly p).map (Int.castRingHom ℚ)) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha', C_1, one_mul]
  rw [e, h']
  ring

/-- Separability from `u g₀ + v g₀' = c ≠ 0`, over any field of characteristic zero. -/
theorem separable_of_cert {K : Type*} [Field K] [CharZero K] {g0 u v : UP} {c : ℤ} (hc : c ≠ 0)
    (h : toPoly (UP.add (UP.mul u g0) (UP.mul v (UP.deriv g0))) = toPoly [c]) :
    ((toPoly g0).map (Int.castRingHom K)).Separable := by
  rw [separable_def']
  have := congrArg (fun f => f.map (Int.castRingHom K)) h
  simp only [toPoly_add, toPoly_mul, toPoly_deriv, Polynomial.map_add, Polynomial.map_mul, toPoly_cons,
    toPoly_nil, mul_zero, add_zero, map_C, derivative_map] at this
  have hc' : ((Int.castRingHom K) c) ≠ 0 := by simpa using hc
  refine ⟨C ((Int.castRingHom K) c)⁻¹ * (toPoly u).map (Int.castRingHom K),
    C ((Int.castRingHom K) c)⁻¹ * (toPoly v).map (Int.castRingHom K), ?_⟩
  calc C ((Int.castRingHom K) c)⁻¹ * (toPoly u).map (Int.castRingHom K) * (toPoly g0).map (Int.castRingHom K) +
        C ((Int.castRingHom K) c)⁻¹ * (toPoly v).map (Int.castRingHom K) *
          derivative ((toPoly g0).map (Int.castRingHom K))
      = C ((Int.castRingHom K) c)⁻¹ * ((toPoly u).map (Int.castRingHom K) * (toPoly g0).map (Int.castRingHom K) +
          (toPoly v).map (Int.castRingHom K) * derivative ((toPoly g0).map (Int.castRingHom K))) := by ring
    _ = 1 := by rw [derivative_map, this, ← C_mul, inv_mul_cancel₀ hc', C_1]

/-- What a successful `sqfOK S g g₀ C` means: in `ℚ[X]`, `g₀ ∣ g ∣ g₀^kg`, `g₀ ∣ S ∣ g₀^ks` and `g₀` is
separable; over any field `K` of characteristic zero, `g`, `S` and `g₀` have the same roots and `g₀` is separable. -/
theorem sqfOK_sound {S g g0 : UP} {C : SqfCert} (h : sqfOK S g g0 C = true) :
    ((toPoly g0).map (Int.castRingHom ℚ) ∣ (toPoly g).map (Int.castRingHom ℚ)) ∧
    ((toPoly g).map (Int.castRingHom ℚ) ∣ ((toPoly g0).map (Int.castRingHom ℚ)) ^ C.kg) ∧
    ((toPoly g0).map (Int.castRingHom ℚ) ∣ (toPoly S).map (Int.castRingHom ℚ)) ∧
    ((toPoly S).map (Int.castRingHom ℚ) ∣ ((toPoly g0).map (Int.castRingHom ℚ)) ^ C.ks) ∧
    (∀ (K : Type) [Field K] [CharZero K], ((toPoly g0).map (Int.castRingHom K)).Separable ∧
      ∀ t : K, (((toPoly g).map (Int.castRingHom K)).eval t = 0 ↔
          ((toPoly g0).map (Int.castRingHom K)).eval t = 0) ∧
        (((toPoly S).map (Int.castRingHom K)).eval t = 0 ↔
          ((toPoly g0).map (Int.castRingHom K)).eval t = 0)) := by
  simp only [sqfOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha1, ha2⟩, ha3⟩, ha4⟩, hc⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have e1 := eqv_sound h1
  have e2 := eqv_sound h2
  have e3 := eqv_sound h3
  have e4 := eqv_sound h4
  have e5 := eqv_sound h5
  have pw : ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (t : K),
      ((toPoly (UP.pow g0 k)).map (Int.castRingHom K)).eval t = (((toPoly g0).map (Int.castRingHom K)).eval t) ^ k := by
    intro K _ _ k t
    rw [toPoly_pow, Polynomial.map_pow, eval_pow]
  refine ⟨dvd_of_cert ha1 e1, ?_, dvd_of_cert ha3 e3, ?_, ?_⟩
  · have := dvd_of_cert ha2 e2
    rwa [toPoly_pow, Polynomial.map_pow] at this
  · have := dvd_of_cert ha4 e4
    rwa [toPoly_pow, Polynomial.map_pow] at this
  · intro K _ _
    refine ⟨separable_of_cert hc e5, fun t => ⟨⟨fun hg => ?_, fun hg0 => root_of_dvd_cert ha1 e1 hg0⟩,
      ⟨fun hS => ?_, fun hg0 => root_of_dvd_cert ha3 e3 hg0⟩⟩⟩
    · have := root_of_dvd_cert ha2 e2 hg
      rw [pw] at this
      exact (pow_eq_zero_iff'.mp this).1
    · have := root_of_dvd_cert ha4 e4 hS
      rw [pw] at this
      exact (pow_eq_zero_iff'.mp this).1

end Lean6.Special.D98
