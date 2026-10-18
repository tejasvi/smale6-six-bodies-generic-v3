import Lean6.Special.D98.Lemma69Check

/-!
# Theorem 6.15: `P₉₃(1, 2, 7) ≠ 0`

`Φ₃(t; μ) = Y₁² + Y₂² + Y₃² − 2(Y₁Y₂ + Y₂Y₃ + Y₃Y₁)` with `Y_l = μ_l² Λ_l(t; μ)`, and
`P₉₃ = Res_t(S_μ(t), Φ₃(t; μ)) ∈ ℤ[μ₁, μ₂, μ₃]` (Mathlib's `Polynomial.resultant`, the determinant of the Sylvester
matrix, with the formal degrees `34` and `4`).

* **`no_common_root_1_2_7`**: `S_μ` and `Φ₃` have no common complex root at `μ = (1, 2, 7)`;
* **`P93_eval_1_2_7_ne_zero`**: `P₉₃(1, 2, 7) ≠ 0`.

Both from the Bezout identity `U S_μ + V Φ₃ = c`, `c ≠ 0` (`bez93`, checked by `native_decide`). The factorization
of `P₉₃` into the polynomials of [AK12, §8.2.1] is not checked here.
-/

namespace Lean6.Special.D98

open Polynomial Lean6.Special.Comp.D98

variable {R : Type*} [CommRing R]

/-- `Φ₃(t; μ)`. -/
def Phi3 (μ : Fin 3 → R) (t : R) : R :=
  (μ 0 ^ 2 * Lam μ t 0) ^ 2 + (μ 1 ^ 2 * Lam μ t 1) ^ 2 + (μ 2 ^ 2 * Lam μ t 2) ^ 2 -
    2 * (μ 0 ^ 2 * Lam μ t 0 * (μ 1 ^ 2 * Lam μ t 1) + μ 1 ^ 2 * Lam μ t 1 * (μ 2 ^ 2 * Lam μ t 2) +
      μ 2 ^ 2 * Lam μ t 2 * (μ 0 ^ 2 * Lam μ t 0))

theorem map_Phi3 {R' : Type*} [CommRing R'] (f : R →+* R') (μ : Fin 3 → R) (t : R) :
    f (Phi3 μ t) = Phi3 (fun i => f (μ i)) (f t) := by
  simp [Phi3, Lam, ell1, ell2, ell3, Mtot, map_ofNat]

/-- `Φ₃` as a polynomial over `R`. -/
noncomputable def Phi3pol (μ : Fin 3 → R) : R[X] := Phi3 (fun i => C (μ i)) X

theorem eval_Phi3pol (μ : Fin 3 → R) (t : R) : (Phi3pol μ).eval t = Phi3 μ t := by
  have := map_Phi3 (evalRingHom t) (fun i => C (μ i)) X
  simpa [Phi3pol] using this

theorem map_Phi3pol {R' : Type*} [CommRing R'] (f : R →+* R') (μ : Fin 3 → R) :
    (Phi3pol μ).map f = Phi3pol (fun i => f (μ i)) := by
  have := map_Phi3 (mapRingHom f) (fun i => C (μ i)) X
  simpa [Phi3pol] using this

theorem toPoly_Phi3UP (m1 m2 m3 : ℤ) : toPoly (Phi3UP m1 m2 m3) = Phi3pol ![m1, m2, m3] := by
  simp only [Phi3UP, toPoly_sub, toPoly_add, toPoly_mul, toPoly_scale, toPoly_cons, toPoly_nil, Phi3pol, Phi3,
    Lam, ell1, ell2, ell3, Mtot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_mul, map_sub, map_ofNat]
  ring

theorem natDegree_Phi3pol_le (μ : Fin 3 → R) : (Phi3pol μ).natDegree ≤ 4 := by
  simp only [Phi3pol, Phi3, Lam, ell1, ell2, ell3, Mtot, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  compute_degree

/-- `P₉₃ = Res_t(S_μ, Φ₃) ∈ ℤ[μ₁, μ₂, μ₃]`. -/
noncomputable def P93 : MvPolynomial (Fin 3) ℤ :=
  resultant (Spol fun i => MvPolynomial.X i) (Phi3pol fun i => MvPolynomial.X i)

theorem bez93_identity :
    toPoly bez93_U * Spol ![(1 : ℤ), 2, 7] + toPoly bez93_V * Phi3pol ![(1 : ℤ), 2, 7] = C bez93_c := by
  have h1 := bez93.1
  simp only [bezOK, Bool.and_eq_true] at h1
  have h := eqv_sound h1.2
  rw [toPoly_add, toPoly_mul, toPoly_mul, toPoly_SUP, toPoly_Phi3UP] at h
  simpa using h

theorem bez93_c_ne_zero : bez93_c ≠ 0 := by
  have h1 := bez93.1
  simp only [bezOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
  exact h1.1

/-- **`S_μ` and `Φ₃` have no common complex root at `μ = (1, 2, 7)`.** -/
theorem no_common_root_1_2_7 (t : ℂ) (hS : S ![(1 : ℂ), 2, 7] t = 0) : Phi3 ![(1 : ℂ), 2, 7] t ≠ 0 := by
  intro hP
  have h := congrArg (fun f => (f.map (Int.castRingHom ℂ)).eval t) bez93_identity
  simp only [Polynomial.map_add, Polynomial.map_mul, map_Spol, map_Phi3pol, eval_add, eval_mul, eval_Spol,
    eval_Phi3pol, map_C, eval_C] at h
  have e1 : (fun i => (Int.castRingHom ℂ) (![(1 : ℤ), 2, 7] i)) = ![(1 : ℂ), 2, 7] := by
    funext i; fin_cases i <;> simp
  rw [e1, hS, hP] at h
  have h2 : ((bez93_c : ℤ) : ℂ) = 0 := by simpa [eq_comm] using h
  exact bez93_c_ne_zero (by exact_mod_cast h2)

/-- **`P₉₃(1, 2, 7) ≠ 0`** (Theorem 6.15). -/
theorem P93_eval_1_2_7_ne_zero : MvPolynomial.eval ![(1 : ℤ), 2, 7] P93 ≠ 0 := by
  set φ := MvPolynomial.eval ![(1 : ℤ), 2, 7]
  have hφμ : (fun i => φ (MvPolynomial.X i)) = ![(1 : ℤ), 2, 7] := by
    funext i; simp [φ]
  have hS127 : (Spol ![(1 : ℤ), 2, 7]).natDegree = 34 := by
    rw [← toPoly_SUP]; exact (degLead_sound deg_1_2_7.1).1
  have hP127 : (Phi3pol ![(1 : ℤ), 2, 7]).natDegree = 4 := by
    rw [← toPoly_Phi3UP]; exact (degLead_sound bez93.2).1
  have hSg : (Spol fun i => (MvPolynomial.X i : MvPolynomial (Fin 3) ℤ)).natDegree = 34 := S_generic.1
  have hPg : (Phi3pol fun i => (MvPolynomial.X i : MvPolynomial (Fin 3) ℤ)).natDegree = 4 := by
    refine le_antisymm (natDegree_Phi3pol_le _) ?_
    have := natDegree_map_le (f := φ) (p := Phi3pol fun i => (MvPolynomial.X i : MvPolynomial (Fin 3) ℤ))
    rw [map_Phi3pol, hφμ, hP127] at this
    exact this
  have key : φ P93 = resultant (Spol ![(1 : ℤ), 2, 7]) (Phi3pol ![(1 : ℤ), 2, 7]) := by
    rw [P93, hSg, hPg, ← resultant_map_map, map_Spol, map_Phi3pol, hφμ, hS127, hP127]
  rw [key]
  -- nonzero over ℚ by coprimality
  intro h0
  set ψ := Int.castRingHom ℚ
  have hinj : Function.Injective ψ := ψ.injective_int
  have hSq : ((Spol ![(1 : ℤ), 2, 7]).map ψ).natDegree = 34 := by rw [natDegree_map_eq_of_injective hinj, hS127]
  have hPq : ((Phi3pol ![(1 : ℤ), 2, 7]).map ψ).natDegree = 4 := by
    rw [natDegree_map_eq_of_injective hinj, hP127]
  have hcop : IsCoprime ((Spol ![(1 : ℤ), 2, 7]).map ψ) ((Phi3pol ![(1 : ℤ), 2, 7]).map ψ) := by
    have h := congrArg (fun f => f.map ψ) bez93_identity
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C] at h
    have hc : ψ bez93_c ≠ 0 := by simpa [ψ] using bez93_c_ne_zero
    refine ⟨C (ψ bez93_c)⁻¹ * (toPoly bez93_U).map ψ, C (ψ bez93_c)⁻¹ * (toPoly bez93_V).map ψ, ?_⟩
    calc C (ψ bez93_c)⁻¹ * (toPoly bez93_U).map ψ * (Spol ![(1 : ℤ), 2, 7]).map ψ +
          C (ψ bez93_c)⁻¹ * (toPoly bez93_V).map ψ * (Phi3pol ![(1 : ℤ), 2, 7]).map ψ
        = C (ψ bez93_c)⁻¹ * ((toPoly bez93_U).map ψ * (Spol ![(1 : ℤ), 2, 7]).map ψ +
          (toPoly bez93_V).map ψ * (Phi3pol ![(1 : ℤ), 2, 7]).map ψ) := by ring
      _ = 1 := by rw [h, ← C_mul, inv_mul_cancel₀ hc, C_1]
  have hne := resultant_ne_zero _ _ hcop
  have e1 : resultant ((Spol ![(1 : ℤ), 2, 7]).map ψ) ((Phi3pol ![(1 : ℤ), 2, 7]).map ψ) =
      ψ (resultant (Spol ![(1 : ℤ), 2, 7]) (Phi3pol ![(1 : ℤ), 2, 7])) := by
    rw [hSq, hPq, resultant_map_map, hS127, hP127]
  apply hne
  rw [e1, h0, map_zero]

end Lean6.Special.D98
