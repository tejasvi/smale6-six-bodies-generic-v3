import Lean6.Special.D98.Check127
import Lean6.Special.Comp.D98.RootsFacts

/-!
# The check of Lemma 6.13 at `(1, 2, 7)`: the statements

See `Lean6.Special.D98.Check127` for the method.
-/

namespace Lean6.Special.D98

open Polynomial Lean6.Special.Comp.D98

theorem rootsOK_get {m1 m2 m3 : ℤ} {θ : ℚ} {Fs : List FacDisks} (h : rootsOK m1 m2 m3 θ Fs = true) (k : ℕ)
    (hk : k < 8) : facOK m1 m2 m3 θ ((factorsUP m1 m2 m3).getD k []) (Fs.getD k ⟨0, []⟩) = true := by
  simp only [rootsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hk1 : k < (factorsUP m1 m2 m3).length := by simp [factorsUP]; omega
  have hk2 : k < Fs.length := by omega
  have hmem : ((factorsUP m1 m2 m3)[k], Fs[k]) ∈ (factorsUP m1 m2 m3).zip Fs := by
    have hz : k < ((factorsUP m1 m2 m3).zip Fs).length := by simp [List.length_zip]; omega
    have := List.getElem_mem hz
    rwa [List.getElem_zip] at this
  have := hall _ hmem
  rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2]
  exact this

/-- `S_μ` is the product of the values of its eight factors. -/
theorem S_eq_prod (m1 m2 m3 : ℤ) (t : ℂ) :
    S ![(m1 : ℂ), m2, m3] t = ((factorsUP m1 m2 m3).map fun f => ((toPoly f).map (Int.castRingHom ℂ)).eval t).prod := by
  rw [← eval_Spol, ← map_toPoly_SUP]
  simp only [SUP, factorsUP, toPoly_mul, Polynomial.map_mul, eval_mul, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  ring

/-- **What `rootsOK` means**: at every root of `S_μ`, `ℓ₁ℓ₂ℓ₃ ≠ 0` and `ρ ≥ θ`. -/
theorem rootsOK_sound {m1 m2 m3 : ℤ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) {θ : ℚ} {Fs : List FacDisks}
    (h : rootsOK m1 m2 m3 θ Fs = true) (t : ℂ) (ht : S ![(m1 : ℂ), m2, m3] t = 0) :
    ell1 (fun i => ((![(m1 : ℝ), m2, m3] i : ℝ) : ℂ)) t * ell2 (fun i => ((![(m1 : ℝ), m2, m3] i : ℝ) : ℂ)) t *
        ell3 (fun i => ((![(m1 : ℝ), m2, m3] i : ℝ) : ℂ)) t ≠ 0 ∧
      (θ : ℝ) ≤ rhoG ![(m1 : ℝ), m2, m3] t := by
  rw [S_eq_prod, List.prod_eq_zero_iff] at ht
  obtain ⟨f, hf, hf0⟩ := List.mem_map.mp ht
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hf
  have hk8 : k < 8 := by simpa [factorsUP] using hk
  have hfac := rootsOK_get h k hk8
  rw [List.getD_eq_getElem _ _ hk] at hfac
  obtain ⟨D, -, hD, hdisk⟩ := (facOK_sound hfac).1 t hf0
  exact diskOK_sound hm1 hm2 hm3 hdisk hD

theorem inv_sqrt_two_lt {θ : ℝ} (h0 : 0 < θ) (h : 1 / 2 < θ ^ 2) : 1 / Real.sqrt 2 < θ := by
  rw [one_div, ← Real.sqrt_inv, Real.sqrt_lt' h0]
  norm_num
  linarith

/-- **The check at `(1, 2, 7)`**: at every root `t` of `S_μ`, `ℓ₁ℓ₂ℓ₃(t) ≠ 0` and
`ρ(t) ≥ 0.7641079385 > 1/√2`. -/
theorem check_1_2_7 (t : ℂ) (ht : S ![(1 : ℂ), 2, 7] t = 0) :
    ell1 (fun i => ((![(1 : ℝ), 2, 7] i : ℝ) : ℂ)) t * ell2 (fun i => ((![(1 : ℝ), 2, 7] i : ℝ) : ℂ)) t *
        ell3 (fun i => ((![(1 : ℝ), 2, 7] i : ℝ) : ℂ)) t ≠ 0 ∧
      (7641079385 / 10000000000 : ℝ) ≤ rhoG ![1, 2, 7] t ∧ 1 / Real.sqrt 2 < rhoG ![1, 2, 7] t := by
  have h := rootsOK_sound (m1 := 1) (m2 := 2) (m3 := 7) (by norm_num) (by norm_num) (by norm_num) roots_1_2_7 t
    (by simpa using ht)
  have e : ![((1 : ℤ) : ℝ), ((2 : ℤ) : ℝ), ((7 : ℤ) : ℝ)] = ![(1 : ℝ), 2, 7] := by norm_num
  rw [e] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : (7641079385 / 10000000000 : ℝ) ≤ rhoG ![1, 2, 7] t := by
    have : (((7641079385 / 10000000000 : ℚ)) : ℝ) = 7641079385 / 10000000000 := by norm_num
    rw [← this]; exact h2
  exact ⟨h1, h2', lt_of_lt_of_le (inv_sqrt_two_lt (by norm_num) (by norm_num)) h2'⟩

/-- **The check at `(1, 2, 8)`**: at every root `t` of `S_μ`, `ρ(t) ≥ 0.7990358445`. -/
theorem check_1_2_8 (t : ℂ) (ht : S ![(1 : ℂ), 2, 8] t = 0) :
    ell1 (fun i => ((![(1 : ℝ), 2, 8] i : ℝ) : ℂ)) t * ell2 (fun i => ((![(1 : ℝ), 2, 8] i : ℝ) : ℂ)) t *
        ell3 (fun i => ((![(1 : ℝ), 2, 8] i : ℝ) : ℂ)) t ≠ 0 ∧
      (7990358445 / 10000000000 : ℝ) ≤ rhoG ![1, 2, 8] t := by
  have h := rootsOK_sound (m1 := 1) (m2 := 2) (m3 := 8) (by norm_num) (by norm_num) (by norm_num) roots_1_2_8 t
    (by simpa using ht)
  have e : ![((1 : ℤ) : ℝ), ((2 : ℤ) : ℝ), ((8 : ℤ) : ℝ)] = ![(1 : ℝ), 2, 8] := by norm_num
  rw [e] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  have : (((7990358445 / 10000000000 : ℚ)) : ℝ) = 7990358445 / 10000000000 := by norm_num
  rw [← this]; exact h2

/-- **`ρρ' > 1/2`** for roots `t` of `S_μ` at `(1, 2, 7)` and `t'` at `(1, 2, 8)`. -/
theorem check_rho_product (t t' : ℂ) (ht : S ![(1 : ℂ), 2, 7] t = 0) (ht' : S ![(1 : ℂ), 2, 8] t' = 0) :
    1 / 2 < rhoG ![1, 2, 7] t * rhoG ![1, 2, 8] t' := by
  have h1 := (check_1_2_7 t ht).2.1
  have h2 := (check_1_2_8 t' ht').2
  have := mul_le_mul h1 h2 (by norm_num) (le_trans (by norm_num) h1)
  linarith

/-- **The minimum at `(1, 2, 7)`**: a root `t` of `N₁₁` (hence of `S_μ`) has `ρ(t) ≤ 0.7641079386`. -/
theorem check_1_2_7_min : ∃ t : ℂ, S ![(1 : ℂ), 2, 7] t = 0 ∧ N11 t = 0 ∧ rhoG ![1, 2, 7] t ≤ 7641079386 / 10000000000 := by
  obtain ⟨hmf, hmd, hlen, hy1, hy2⟩ := minFac_eq
  have hfac := rootsOK_get roots_1_2_7 3 (by norm_num)
  set F := disks_1_2_7.getD 3 ⟨0, []⟩
  have hfac' : facOK 1 2 7 (7641079385 / 10000000000) N11UP F = true := hfac
  have hD : F.disks.getD 0 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ ∈ F.disks := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨⟨t, ht0, htr⟩, hdisk⟩ := (facOK_sound hfac').2 _ hD
  have hup := upper_1_2_7
  rw [hmf, hmd] at hup
  have hρ := upperOK_sound (m1 := 1) (m2 := 2) (m3 := 7) (by norm_num) (by norm_num) (by norm_num) hdisk hup htr
  have e : ![((1 : ℤ) : ℝ), ((2 : ℤ) : ℝ), ((7 : ℤ) : ℝ)] = ![(1 : ℝ), 2, 7] := by norm_num
  rw [e] at hρ
  have hN : N11 t = 0 := by
    have := ht0
    rw [toPoly_N11UP] at this
    simpa [N11, map_ofNat] using this
  refine ⟨t, ?_, hN, ?_⟩
  · simp only [S, hN, mul_zero, zero_mul]
  · have : (((7641079386 / 10000000000 : ℚ)) : ℝ) = 7641079386 / 10000000000 := by norm_num
    rw [← this]; exact hρ

end Lean6.Special.D98
