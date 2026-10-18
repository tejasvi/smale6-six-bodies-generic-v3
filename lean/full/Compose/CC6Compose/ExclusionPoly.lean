import CC6Compose.ExclusionCore

/-!
# Bridge: the polynomial of a certificate as a polynomial in the six masses

A certificate of the checks (`L6.Poly.Cert`) has a polynomial `h` in the masses (packed exponents, variables
`0, …, 5`) that is nonzero at the point `hPoint` (with `m_F = 1` when the mass `F` is fixed), and by Lemma 5.2 it
vanishes at the masses `m` of a germ of the cell (no fixed mass) or at `m / m_F` (`core_vanish`). This file writes it
as a nonzero `MvPolynomial (Fin 6) ℤ` vanishing at `m`: `h` itself, or its homogenization `m_F^d h(m / m_F)` with
respect to the fixed mass, of the largest degree `d` of its terms.

* `monoMv`, `degK`, `maxDeg`, `massPoly`, `homogMv`, `certPoly`.
* `aeval_massPoly`, `aeval_homogMv`, `aeval_homogMv_one`: their values.
* `certPoly_vanish`: `certPoly c` vanishes at `m` if `h` vanishes at the masses of `massPt m c.fixed`.
* `certPoly_ne_zero`: `certPoly c ≠ 0` for a certificate with `CertMeaning` (it is nonzero at `hPoint`).
-/

namespace CC6Compose

open MvPolynomial

/-! ## Polynomials in the masses from packed polynomials -/

/-- The monomial of a key in the six masses. -/
noncomputable def monoMv (key : ℕ) : MvPolynomial (Fin 6) ℤ := ∏ i : Fin 6, X i ^ L6.Poly.keyExp key i.val

/-- The total degree of a key in the six masses. -/
def degK (key : ℕ) : ℕ := ∑ i : Fin 6, L6.Poly.keyExp key i.val

/-- The largest degree of the terms of a packed polynomial. -/
def maxDeg (h : L6.Poly.Poly) : ℕ := (h.map fun t => degK t.1).foldr max 0

theorem degK_le_maxDeg {h : L6.Poly.Poly} {t : ℕ × ℤ} (ht : t ∈ h) : degK t.1 ≤ maxDeg h := by
  unfold maxDeg
  induction h with
  | nil => exact absurd ht List.not_mem_nil
  | cons a h ih =>
    rw [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

/-- A packed polynomial in the masses as a polynomial of `ℤ[m₀, …, m₅]`. -/
noncomputable def massPoly (h : L6.Poly.Poly) : MvPolynomial (Fin 6) ℤ := (h.map fun t => C t.2 * monoMv t.1).sum

/-- The homogenization `m_F^d h(m / m_F)` of a packed polynomial with respect to the mass `F`, for the largest degree
`d` of its terms. -/
noncomputable def homogMv (h : L6.Poly.Poly) (F : Fin 6) : MvPolynomial (Fin 6) ℤ :=
  (h.map fun t => C t.2 * X F ^ (maxDeg h - degK t.1) * monoMv t.1).sum

/-- The polynomial of a certificate: `h` if no mass is fixed, else its homogenization with respect to the fixed
mass. -/
noncomputable def certPoly (c : L6.Poly.Cert) : MvPolynomial (Fin 6) ℤ :=
  if 0 ≤ c.fixed then homogMv c.h (fin6 c.fixed.toNat) else massPoly c.h

/-! ## Values -/

section values

variable {R : Type*} [CommRing R]

theorem monoEval_six (φ : ℕ → R) (key : ℕ) :
    L6.Poly.monoEval 6 φ key = ∏ i : Fin 6, φ i.val ^ L6.Poly.keyExp key i.val := by
  unfold L6.Poly.monoEval
  rw [Fin.prod_univ_eq_prod_range (fun i => φ i ^ L6.Poly.keyExp key i) 6]

theorem aeval_monoMv (x : Fin 6 → R) (key : ℕ) :
    aeval x (monoMv key) = ∏ i : Fin 6, x i ^ L6.Poly.keyExp key i.val := by
  simp [monoMv, map_prod]

theorem aeval_massPoly (x : Fin 6 → R) (h : L6.Poly.Poly) :
    aeval x (massPoly h) = L6.Poly.eval 6 (fun i => x (fin6 i)) h := by
  unfold massPoly L6.Poly.eval
  rw [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, map_mul, eq_intCast, map_intCast, aeval_monoMv, monoEval_six, fin6_val]

theorem aeval_homogMv_one (x : Fin 6 → R) (h : L6.Poly.Poly) {F : Fin 6} (hF : x F = 1) :
    aeval x (homogMv h F) = L6.Poly.eval 6 (fun i => x (fin6 i)) h := by
  unfold homogMv L6.Poly.eval
  rw [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, map_mul, map_pow, eq_intCast, map_intCast, aeval_X, hF, one_pow, mul_one,
    aeval_monoMv, monoEval_six, fin6_val]

theorem eval_map_ringHom {S : Type*} [CommRing S] (f : R →+* S) (φ : ℕ → R) (h : L6.Poly.Poly) :
    f (L6.Poly.eval 6 φ h) = L6.Poly.eval 6 (fun i => f (φ i)) h := by
  unfold L6.Poly.eval
  rw [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, map_mul, map_intCast, monoEval_six, map_prod, map_pow]

end values

theorem aeval_homogMv {K : Type*} [Field K] (x : Fin 6 → K) (h : L6.Poly.Poly) {F : Fin 6} (hF : x F ≠ 0) :
    aeval x (homogMv h F) = x F ^ maxDeg h * L6.Poly.eval 6 (fun i => x (fin6 i) / x F) h := by
  unfold homogMv L6.Poly.eval
  rw [map_list_sum, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  have hle := degK_le_maxDeg ht
  simp only [Function.comp_apply, map_mul, map_pow, eq_intCast, map_intCast, aeval_X, aeval_monoMv, monoEval_six,
    fin6_val, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hdeg : (∑ i : Fin 6, L6.Poly.keyExp t.1 i.val) = degK t.1 := rfl
  rw [hdeg, pow_sub₀ _ hF hle]
  field_simp

/-! ## The polynomial of a certificate -/

/-- **`certPoly c` vanishes at the masses** of a germ whose core has the certificate `c` (`core_vanish`). -/
theorem certPoly_vanish {m : Fin 6 → ℝ} (hm : ∀ k, 0 < m k) {c : L6.Poly.Cert}
    (h0 : L6.Poly.eval 6 (ptM (massPt m c.fixed)) c.h = 0) : aeval m (certPoly c) = 0 := by
  have hreal : L6.Poly.eval 6 (fun i => massPt m c.fixed (fin6 i)) c.h = 0 := by
    have := eval_map_ringHom Complex.ofRealHom (fun i => massPt m c.fixed (fin6 i)) c.h
    rw [show (fun i => Complex.ofRealHom (massPt m c.fixed (fin6 i))) = ptM (massPt m c.fixed) from rfl, h0] at this
    exact Complex.ofReal_eq_zero.mp this
  unfold certPoly
  split_ifs with hF
  · have hmF : m (fin6 c.fixed.toNat) ≠ 0 := (hm _).ne'
    rw [aeval_homogMv m c.h hmF]
    have e : (fun i => m (fin6 i) / m (fin6 c.fixed.toNat)) = fun i => massPt m c.fixed (fin6 i) := by
      funext i
      simp only [massPt, ite_eq_left hF, Pi.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
    rw [e, hreal, mul_zero]
  · rw [aeval_massPoly]
    have e : (fun i => m (fin6 i)) = fun i => massPt m c.fixed (fin6 i) := by
      funext i
      simp only [massPt, ite_eq_right hF]
    rw [e, hreal]

theorem hPoint_fixed {F : ℕ} (hF : F < 6) : (#[(3 : ℤ), 5, 7, 11, 13, 17].set! F 1).getD F 0 = 1 := by
  interval_cases F <;> rfl

/-- **`certPoly c` is not zero** for a certificate with `CertMeaning`: it is nonzero at `hPoint`. -/
theorem certPoly_ne_zero {c : L6.Poly.Cert} (hmean : L6.Poly.CertMeaning c) (hF6 : c.fixed < 6) :
    certPoly c ≠ 0 := by
  intro h0
  have hne := hmean.2
  set y : Fin 6 → ℤ := fun i => (L6.Poly.hPoint c.fixed).getD i.val 0 with hy
  have hev : L6.Poly.eval 6 (fun i => y (fin6 i)) c.h = 0 := by
    unfold certPoly at h0
    split_ifs at h0 with hF
    · have hyF : y (fin6 c.fixed.toNat) = 1 := by
        have hlt : c.fixed.toNat < 6 := by omega
        simp only [hy, fin6_val_of_lt hlt, L6.Poly.hPoint, show (0 ≤ c.fixed && c.fixed < 6) = true by simp [hF, hF6],
          ite_true]
        exact hPoint_fixed hlt
      rw [← aeval_homogMv_one y c.h hyF, h0, map_zero]
    · rw [← aeval_massPoly, h0, map_zero]
  apply hne
  refine (eval_congr (fun i hi => ?_) c.h).trans hev
  simp only [hy, fin6_val_of_lt hi]

end CC6Compose
