import CC6Full.Curve.System
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field

/-!
# From a central configuration to a point of the slice

The first step of the proof of Corollary 2.4 (`cor:curve`): every central configuration with positive masses is
represented, up to similarity, by a point of the slice `Y_m` at which `U ≠ 0`. This combines [Tom26, Lemma 2.1]
(a central configuration is similar to a real normalized central configuration with positive `p_kl`) with the
rotation of Lemma 2.1 (`lem:slice`) (a), in the coordinates `z, w, p` of `CC6Full.Curve.System`. Bodies `1, 2` of
the paper are `0, 1`.

* `sum_sum_mul_sub_of_symm`: an antisymmetric double sum vanishes, `Σ_i Σ_j b_ij (x_i − x_j) = 0` for a symmetric
  kernel `b` (over any commutative ring); `two_mul_sum_sum_mul_conj` is the symmetrization
  `2 Σ_i Σ_j b_ij (q_i − q_j) conj (q_i − c) = Σ_i Σ_j b_ij |q_i − q_j|²` for a symmetric real kernel.
* `lam_pos_of_isCC` ([Tom26, Lemma 2.1]): the multiplier `λ` of a central configuration `q` with centre `c` and
  positive masses is positive. Multiplying the equation of body `i` by `conj (q_i − c)` and summing gives
  `2 λ Σ_i m_i |q_i − c|² = Σ_{i ≠ j} m_i m_j / r_ij > 0`.
* `exists_slice_point`: with `a = λ^{1/3} > 0`, the configuration `Z = a (q − c)` solves the equations of the bodies
  `Z_k = Σ_{l ≠ k} m_l |Z_k − Z_l|⁻³ (Z_k − Z_l)`, so `(z, w, p) = (Z, conj Z, 1/|Z_k − Z_l|)` is a point of `X_m`, at
  which `U = Σ_{k<l} m_k m_l p_kl > 0`. The rotation `(z, w) ↦ (s z, s⁻¹ w)` with `s = 1/(Z₁ − Z₂)` moves it into the
  slice and changes neither `p` nor `U`. The resulting point (`ccPoint q c (q 0 - q 1) a`) has
  `z_k = (q_k − c)/(q₁ − q₂)`, `w_k = a² (q₁ − q₂) conj (q_k − c)`, `p_kl = 1/(a r_kl)`, and `q` is the image of its
  configuration `(z_k)_k` under the similarity `z ↦ (q₁ − q₂) z + c`.
* `finitelyManyCC_of_finite`: if `Y_m ∩ {U ≠ 0}` is finite, the masses have finitely many central configurations
  up to similarity.
-/

namespace CC6Full

open Finset MvPolynomial ComplexConjugate

section sums

variable {ι : Type*} [Fintype ι]

/-- An antisymmetric double sum vanishes: `Σ_i Σ_j b_ij (x_i − x_j) = 0` for a symmetric kernel `b`. -/
theorem sum_sum_mul_sub_of_symm {R : Type*} [CommRing R] {b : ι → ι → R} (hb : ∀ i j, b i j = b j i)
    (x : ι → R) : ∑ i, ∑ j, b i j * (x i - x j) = 0 := by
  have h : ∑ i, ∑ j, b i j * x j = ∑ i, ∑ j, b i j * x i := by
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hb]
  simp only [mul_sub, Finset.sum_sub_distrib, h, sub_self]

/-- Symmetrization: for a symmetric real kernel `b`,
`2 Σ_i Σ_j b_ij (q_i − q_j) conj (q_i − c) = Σ_i Σ_j b_ij |q_i − q_j|²`. -/
theorem two_mul_sum_sum_mul_conj {b : ι → ι → ℝ} (hb : ∀ i j, b i j = b j i) (q : ι → ℂ) (c : ℂ) :
    2 * ∑ i, ∑ j, (b i j : ℂ) * (q i - q j) * conj (q i - c) =
      ∑ i, ∑ j, ((b i j * Complex.normSq (q i - q j) : ℝ) : ℂ) := by
  have h1 : ∑ i, ∑ j, (b i j : ℂ) * (q i - q j) * conj (q j - c) =
      -∑ i, ∑ j, (b i j : ℂ) * (q i - q j) * conj (q i - c) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb j i]; ring
  have h2 : ∑ i, ∑ j, ((b i j * Complex.normSq (q i - q j) : ℝ) : ℂ) =
      ∑ i, ∑ j, (b i j : ℂ) * (q i - q j) * conj (q i - c) -
        ∑ i, ∑ j, (b i j : ℂ) * (q i - q j) * conj (q j - c) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_mul, ← Complex.mul_conj]
    simp only [map_sub]
    ring
  rw [h2, h1]; ring

end sums

variable {n : ℕ}

/-- **The multiplier of a central configuration with positive masses is positive** ([Tom26, Lemma 2.1]):
`2 λ Σ_i m_i |q_i − c|² = Σ_{i ≠ j} m_i m_j / |q_i − q_j| > 0`. -/
theorem lam_pos_of_isCC {m : Fin (n + 2) → ℝ} (hm : ∀ i, 0 < m i) {q : Conf (n + 2)} (hcf : CollisionFree q)
    {lam : ℝ} {c : ℂ} (h : ∀ i, ((lam * m i : ℝ) : ℂ) * (q i - c) =
      ∑ j ∈ univ.erase i, ((m i * m j / ‖q i - q j‖ ^ 3 : ℝ) : ℂ) * (q i - q j)) : 0 < lam := by
  set b : Fin (n + 2) → Fin (n + 2) → ℝ := fun i j => m i * m j / ‖q i - q j‖ ^ 3 with hb_def
  have hb : ∀ i j, b i j = b j i := fun i j => by
    simp only [hb_def]; rw [norm_sub_rev, mul_comm (m i)]
  have hE : ∀ i, ∑ j, (b i j : ℂ) * (q i - q j) = ((lam * m i : ℝ) : ℂ) * (q i - c) := by
    intro i
    rw [h i]
    exact (Finset.sum_erase univ (f := fun j => (b i j : ℂ) * (q i - q j)) (a := i) (by simp)).symm
  -- `Σ_i conj (q_i − c) E_i` computed with the equations of the bodies
  have h1 : ∑ i, ∑ j, (b i j : ℂ) * (q i - q j) * conj (q i - c) =
      ((lam * ∑ i, m i * Complex.normSq (q i - c) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hE i, Complex.normSq_eq_conj_mul_self]
    push_cast; ring
  have h3 := two_mul_sum_sum_mul_conj hb q c
  rw [h1] at h3
  simp only [← Complex.ofReal_sum] at h3
  have h3' : 2 * (lam * ∑ i, m i * Complex.normSq (q i - c)) =
      ∑ i, ∑ j, b i j * Complex.normSq (q i - q j) := by
    exact_mod_cast h3
  have hnn : ∀ i j, 0 ≤ b i j * Complex.normSq (q i - q j) := fun i j =>
    mul_nonneg (div_nonneg (mul_nonneg (hm i).le (hm j).le) (by positivity)) (Complex.normSq_nonneg _)
  have hq01 : q 0 - q 1 ≠ 0 := sub_ne_zero.mpr (hcf 0 1 Fin.zero_lt_one.ne)
  have hpos01 : 0 < b 0 1 * Complex.normSq (q 0 - q 1) :=
    mul_pos (div_pos (mul_pos (hm 0) (hm 1)) (pow_pos (norm_pos_iff.mpr hq01) 3))
      (Complex.normSq_pos.mpr hq01)
  have hRpos : 0 < ∑ i, ∑ j, b i j * Complex.normSq (q i - q j) := by
    calc (0 : ℝ) < b 0 1 * Complex.normSq (q 0 - q 1) := hpos01
      _ ≤ ∑ j, b 0 j * Complex.normSq (q 0 - q j) :=
          Finset.single_le_sum (fun j _ => hnn 0 j) (Finset.mem_univ 1)
      _ ≤ ∑ i, ∑ j, b i j * Complex.normSq (q i - q j) :=
          Finset.single_le_sum (f := fun i => ∑ j, b i j * Complex.normSq (q i - q j))
            (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) (Finset.mem_univ 0)
  have hInn : 0 ≤ ∑ i, m i * Complex.normSq (q i - c) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (Complex.normSq_nonneg _)
  by_contra hle
  have hle' : lam ≤ 0 := not_lt.mp hle
  nlinarith

section point

variable {N : ℕ}

/-- The point of `ℂ^{Coord}` of a configuration `q` with centre `c`, for `a > 0` and a scale `d`:
`z_k = (q_k − c)/d`, `w_k = a² d conj (q_k − c)`, `p_kl = 1/(a |q_k − q_l|)`. For a central configuration with
centre `c`, multiplier `a³` and `d = q 0 - q 1` it is a point of `Y_m` (`exists_slice_point`). -/
noncomputable def ccPoint (q : Conf N) (c d : ℂ) (a : ℝ) : Coord N → ℂ
  | Sum.inl k => (q k - c) / d
  | Sum.inr (Sum.inl k) => (a : ℂ) ^ 2 * d * conj (q k - c)
  | Sum.inr (Sum.inr e) => ((1 / (a * ‖q e.1.1 - q e.1.2‖) : ℝ) : ℂ)

@[simp] theorem ccPoint_zc (q : Conf N) (c d : ℂ) (a : ℝ) (k : Fin N) :
    ccPoint q c d a (zc k) = (q k - c) / d := rfl

@[simp] theorem ccPoint_wc (q : Conf N) (c d : ℂ) (a : ℝ) (k : Fin N) :
    ccPoint q c d a (wc k) = (a : ℂ) ^ 2 * d * conj (q k - c) := rfl

@[simp] theorem ccPoint_pc (q : Conf N) (c d : ℂ) (a : ℝ) (e : Pair N) :
    ccPoint q c d a (pc e) = ((1 / (a * ‖q e.1.1 - q e.1.2‖) : ℝ) : ℂ) := rfl

theorem eval_pP_ccPoint (q : Conf N) (c d : ℂ) (a : ℝ) {k l : Fin N} (hkl : k ≠ l) :
    eval (ccPoint q c d a) (pP k l) = ((1 / (a * ‖q k - q l‖) : ℝ) : ℂ) :=
  eval_pP_eq (f := fun k l => ((1 / (a * ‖q k - q l‖) : ℝ) : ℂ)) (fun _ => rfl)
    (fun k l => by simp only [norm_sub_rev]) hkl

end point

/-- **From a central configuration to the slice** (Lemma 2.1 (`lem:slice`) (a) and [Tom26, Lemma 2.1]). For
positive masses every central configuration `q` is similar to the configuration `(z_k)_k` of a point of `Y_m` at
which `U ≠ 0`. -/
theorem exists_slice_point {m : Fin (n + 2) → ℝ} (hm : ∀ i, 0 < m i) {q : Conf (n + 2)} (hq : IsCC m q) :
    ∃ y ∈ Ym m, eval y (Upoly m) ≠ 0 ∧ Similar (zConf y) q := by
  obtain ⟨hcf, lam, c, h⟩ := hq
  have hlam : 0 < lam := lam_pos_of_isCC hm hcf h
  obtain ⟨a, ha, ha3⟩ : ∃ a : ℝ, 0 < a ∧ a ^ 3 = lam :=
    ⟨lam ^ ((3 : ℕ) : ℝ)⁻¹, Real.rpow_pos_of_pos hlam _, Real.rpow_inv_natCast_pow hlam.le (by norm_num)⟩
  have hd : q 0 - q 1 ≠ 0 := sub_ne_zero.mpr (hcf 0 1 Fin.zero_lt_one.ne)
  have hr : ∀ k l, k ≠ l → 0 < ‖q k - q l‖ := fun k l hkl =>
    norm_pos_iff.mpr (sub_ne_zero.mpr (hcf k l hkl))
  -- the equation of body `k`, divided by `m_k λ = m_k a³`
  have hsum : ∀ k, ∑ l ∈ univ.erase k, (m l : ℂ) * ((1 / (a * ‖q k - q l‖) : ℝ) : ℂ) ^ 3 * (q k - q l) =
      q k - c := by
    intro k
    have hmk : ((m k * lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos (hm k) hlam).ne'
    apply mul_left_cancel₀ hmk
    rw [Finset.mul_sum, show ((m k * lam : ℝ) : ℂ) * (q k - c) = ((lam * m k : ℝ) : ℂ) * (q k - c) by
      rw [mul_comm (m k)], h k]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hrl := hr k l (Ne.symm (Finset.ne_of_mem_erase hl))
    have ha0 := ha.ne'
    have hrl0 := hrl.ne'
    have e : m k * lam * (m l * (1 / (a * ‖q k - q l‖)) ^ 3) = m k * m l / ‖q k - q l‖ ^ 3 := by
      rw [← ha3]; field_simp
    rw [← e]; push_cast; ring
  have hsumc : ∀ k, ∑ l ∈ univ.erase k, (m l : ℂ) * ((1 / (a * ‖q k - q l‖) : ℝ) : ℂ) ^ 3 * conj (q k - q l) =
      conj (q k - c) := fun k => by
    simpa only [map_sum, map_mul, map_pow, Complex.conj_ofReal] using congrArg conj (hsum k)
  refine ⟨ccPoint q c (q 0 - q 1) a, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- the rows vanish
    rintro f ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨e, rfl⟩)
    · rw [eval_rowZ, sub_eq_zero]
      calc ccPoint q c (q 0 - q 1) a (zc k)
          = (∑ l ∈ univ.erase k, (m l : ℂ) * ((1 / (a * ‖q k - q l‖) : ℝ) : ℂ) ^ 3 * (q k - q l)) /
              (q 0 - q 1) := by rw [hsum k, ccPoint_zc]
        _ = ∑ l ∈ univ.erase k, (m l : ℂ) * ((1 / (a * ‖q k - q l‖) : ℝ) : ℂ) ^ 3 * (q k - q l) /
              (q 0 - q 1) := by rw [Finset.sum_div]
        _ = _ := Finset.sum_congr rfl fun l hl => by
            rw [eval_pP_ccPoint q c _ a (Ne.symm (Finset.ne_of_mem_erase hl))]
            simp only [ccPoint_zc]
            ring
    · rw [eval_rowW, sub_eq_zero]
      calc ccPoint q c (q 0 - q 1) a (wc k)
          = (a : ℂ) ^ 2 * (q 0 - q 1) * ∑ l ∈ univ.erase k,
              (m l : ℂ) * ((1 / (a * ‖q k - q l‖) : ℝ) : ℂ) ^ 3 * conj (q k - q l) := by
            rw [hsumc k, ccPoint_wc]
        _ = ∑ l ∈ univ.erase k, (a : ℂ) ^ 2 * (q 0 - q 1) *
              ((m l : ℂ) * ((1 / (a * ‖q k - q l‖) : ℝ) : ℂ) ^ 3 * conj (q k - q l)) := by
            rw [Finset.mul_sum]
        _ = _ := Finset.sum_congr rfl fun l hl => by
            rw [eval_pP_ccPoint q c _ a (Ne.symm (Finset.ne_of_mem_erase hl))]
            simp only [ccPoint_wc, map_sub]
            ring
    · have hr0 := hr _ _ e.2.ne
      have ha0 := ha.ne'
      have hr00 := hr0.ne'
      rw [eval_rowD, sub_eq_zero]
      simp only [ccPoint_zc, ccPoint_wc, ccPoint_pc]
      have hn : (q e.1.1 - q e.1.2) * conj (q e.1.1 - q e.1.2) = ((‖q e.1.1 - q e.1.2‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hreal : (1 / (a * ‖q e.1.1 - q e.1.2‖)) ^ 2 * a ^ 2 * ‖q e.1.1 - q e.1.2‖ ^ 2 = 1 := by
        field_simp
      have hdd : (q 0 - q 1)⁻¹ * (q 0 - q 1) = 1 := inv_mul_cancel₀ hd
      calc _ = ((1 / (a * ‖q e.1.1 - q e.1.2‖) : ℝ) : ℂ) ^ 2 * (a : ℂ) ^ 2 *
            ((q e.1.1 - q e.1.2) * conj (q e.1.1 - q e.1.2)) * ((q 0 - q 1)⁻¹ * (q 0 - q 1)) := by
            simp only [map_sub]; ring
        _ = 1 := by rw [hdd, mul_one, hn]; exact_mod_cast hreal
  · -- the slice
    rw [eval_sliceP, ccPoint_zc, ccPoint_zc, div_sub_div_same,
      show q 0 - c - (q 1 - c) = q 0 - q 1 by ring, div_self hd, sub_self]
  · -- `U > 0`
    have hU : eval (ccPoint q c (q 0 - q 1) a) (Upoly m) =
        ((∑ e : Pair (n + 2), m e.1.1 * m e.1.2 * (1 / (a * ‖q e.1.1 - q e.1.2‖)) : ℝ) : ℂ) := by
      simp only [Upoly, map_sum, map_mul, eval_C, eval_X, ccPoint_pc]
      push_cast
      rfl
    rw [hU]
    have hpos : 0 < ∑ e : Pair (n + 2), m e.1.1 * m e.1.2 * (1 / (a * ‖q e.1.1 - q e.1.2‖)) :=
      Finset.sum_pos (fun e _ => mul_pos (mul_pos (hm _) (hm _)) (one_div_pos.mpr (mul_pos ha (hr _ _ e.2.ne))))
        ⟨⟨(0, 1), Fin.zero_lt_one⟩, Finset.mem_univ _⟩
    exact_mod_cast hpos.ne'
  · -- the similarity `z ↦ (q₁ − q₂) z + c`
    refine ⟨q 0 - q 1, c, hd, Or.inl fun i => ?_⟩
    show q i = (q 0 - q 1) * ((q i - c) / (q 0 - q 1)) + c
    rw [mul_div_cancel₀ _ hd]
    ring

/-- **Finiteness from the slice**: if `Y_m ∩ {U ≠ 0}` is finite, the masses have finitely many central
configurations up to similarity. -/
theorem finitelyManyCC_of_finite {m : Fin (n + 2) → ℝ} (hm : ∀ i, 0 < m i)
    (h : {y : Coord (n + 2) → ℂ | y ∈ Ym m ∧ eval y (Upoly m) ≠ 0}.Finite) : FinitelyManyCC m := by
  refine ⟨(h.image zConf).toFinset, fun q hq => ?_⟩
  obtain ⟨y, hy, hU, hsim⟩ := exists_slice_point hm hq
  exact ⟨zConf y, (h.image zConf).mem_toFinset.mpr ⟨y, ⟨hy, hU⟩, rfl⟩, hsim⟩

end CC6Full
