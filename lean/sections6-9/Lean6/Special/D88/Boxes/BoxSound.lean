import Lean6.Special.D88.Boxes.Disc
import Lean6.Special.D88.Boxes.Systems
import Lean6.Special.Ball.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# What a passing box means

For a box `b` (radius `b.radius = rho/2^P`, centers `b.center n`), with `closedBall` the polydisc in the sup norm:

* **`n4_box_sound`** (Lemma 6.19(c)): if `n4BoxOK s` and `parseBox s = some b`, the polydisc contains exactly one zero
  `z` of S11, S11 has an invertible Jacobian matrix at `z`, and at every point of the polydisc `X₃ − X₄ ≠ 0` and the
  T-test holds with margin `0.1756`.
* **`kc_box_sound`** (Lemma 6.19(d)): the same for KC12, with `X₃ ≠ 0` and the 32 sums of Lemma 6.17(b) at
  `(m₅, m₆) = (1, 2)` bounded below by `1.47·10⁻⁶ (1 + ρ²)^{1/2} Σ_l |β_l|`, for every choice of the square roots.
* **`t123_sound`**, **`small_sound`**, **`yBounds_sound`**: the decisions of Sec. 6.7, last paragraph.
-/

namespace Lean6.Special.D88.Boxes

open Lean6.Special.Ball Lean6.Special.Kraw Metric Complex

/-- The center of the polydisc of a box in `ℂⁿ`. -/
noncomputable def Box.center (b : Box) (n : ℕ) : Fin n → ℂ :=
  fun j => ⟨((b.c j).1 : ℝ) / 2 ^ P, ((b.c j).2 : ℝ) / 2 ^ P⟩

/-- The radius of the polydisc of a box. -/
noncomputable def Box.radius (b : Box) : ℝ := (b.rho : ℝ) / 2 ^ P

theorem S_cast : ((S : ℕ) : ℝ) = (2 : ℝ) ^ P := by simp [S]

theorem cv_biased {x : ℤ} (hx : x.natAbs < bias P) : cv P (biased x) = x := by
  unfold cv biased
  have h : 0 ≤ x + (bias P : ℤ) := by omega
  rw [Int.toNat_of_nonneg h]
  ring

theorem center_mkCenter {x : ℤ × ℤ} (h1 : x.1.natAbs < bias P) (h2 : x.2.natAbs < bias P) :
    centerC P (mkCenter x) = ⟨(x.1 : ℝ) / 2 ^ P, (x.2 : ℝ) / 2 ^ P⟩ := by
  simp only [centerC, mkCenter, cv_biased h1, cv_biased h2]

/-- The centers of the Krawczyk test are the centers of the box. -/
theorem kraw_center_eq {b : Box} (hs : centersSmall b = true) {n : ℕ} (hn : b.cs.length = n) (j : Fin n) :
    centerC P ((b.cs.map mkCenter).getD j.1 (zero P)) = b.center n j := by
  have hj : j.1 < b.cs.length := by omega
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  unfold centersSmall at hs
  rw [List.all_eq_true] at hs
  have := hs _ (List.getElem_mem hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rw [center_mkCenter this.1 this.2]
  simp only [Box.center, Box.c, List.getD_eq_getElem _ _ hj]

/-- `ListMemF` for the table `[1]`. -/
theorem listMemF_tab1 : ListMemF P κ1 tab1 := by
  intro v
  rcases v with _ | v
  · simpa [tab1, κ1] using (mem_one (P := P))
  · simp only [tab1, κ1]
    rw [List.getD_eq_default _ _ (by simp)]
    simpa using (mem_zero (P := P))

/-- A point of the polydisc is in the coordinate discs. -/
theorem coord_mem {b : Box} {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ closedBall (b.center n) b.radius) (j : Fin n) :
    (coordDisc b j).Mem (z j) := by
  have h := (norm_le_pi_norm (z - b.center n) j).trans (mem_closedBall_iff_norm.mp hz)
  rw [Pi.sub_apply] at h
  unfold IDisc.Mem
  have hc : (coordDisc b j).center = b.center n j := by
    simp [coordDisc, IDisc.center, Box.center, S_cast]
  have hr : ((coordDisc b j).R : ℝ) / ((coordDisc b j).T : ℝ) = b.radius := by
    simp [coordDisc, Box.radius, S_cast]
  rw [hc, hr]
  exact h

/-- **Affine images of two coordinates.** -/
theorem affine_mem {a0 b0 a1 b1 : ℤ} {ρ : ℕ} {z0 z1 : ℂ} (h0 : (⟨a0, b0, ρ, S⟩ : IDisc).Mem z0)
    (h1 : (⟨a1, b1, ρ, S⟩ : IDisc).Mem z1) (α β γ : ℤ) (D : ℕ) (hD : 0 < D) {A B : ℤ} {R T : ℕ}
    (hA : A = α * a0 + β * a1 + γ * S) (hB : B = α * b0 + β * b1) (hT : T = D * S)
    (hR : (α.natAbs + β.natAbs) * ρ ≤ R) :
    (⟨A, B, R, T⟩ : IDisc).Mem (((α : ℂ) * z0 + β * z1 + γ) / D) := by
  unfold IDisc.Mem at h0 h1 ⊢
  simp only [IDisc.center] at h0 h1 ⊢
  have hS : (0 : ℝ) < (S : ℝ) := by rw [S_cast]; positivity
  have hD' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have e : ((α : ℂ) * z0 + β * z1 + γ) / D - ⟨(A : ℝ) / (T : ℝ), (B : ℝ) / (T : ℝ)⟩ =
      ((α : ℂ) * (z0 - ⟨(a0 : ℝ) / S, (b0 : ℝ) / S⟩) + β * (z1 - ⟨(a1 : ℝ) / S, (b1 : ℝ) / S⟩)) / D := by
    subst hA hB hT
    apply Complex.ext
    · simp [Complex.div_re, Complex.normSq]
      field_simp
      try ring
    · simp [Complex.div_im, Complex.normSq]
      field_simp
      try ring
  rw [e, norm_div, Complex.norm_natCast]
  have hN : ‖(α : ℂ) * (z0 - ⟨(a0 : ℝ) / S, (b0 : ℝ) / S⟩) + β * (z1 - ⟨(a1 : ℝ) / S, (b1 : ℝ) / S⟩)‖ ≤
      (R : ℝ) / S := by
    calc ‖(α : ℂ) * (z0 - ⟨(a0 : ℝ) / S, (b0 : ℝ) / S⟩) + β * (z1 - ⟨(a1 : ℝ) / S, (b1 : ℝ) / S⟩)‖
        ≤ ‖(α : ℂ)‖ * ‖z0 - ⟨(a0 : ℝ) / S, (b0 : ℝ) / S⟩‖ + ‖(β : ℂ)‖ * ‖z1 - ⟨(a1 : ℝ) / S, (b1 : ℝ) / S⟩‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ (α.natAbs : ℝ) * ((ρ : ℝ) / S) + (β.natAbs : ℝ) * ((ρ : ℝ) / S) := by
          rw [Complex.norm_intCast, Complex.norm_intCast, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs,
            Int.cast_abs]
          gcongr
      _ = (((α.natAbs + β.natAbs) * ρ : ℕ) : ℝ) / S := by push_cast; ring
      _ ≤ (R : ℝ) / S := by
          gcongr
  rw [hT, Nat.cast_mul, div_le_div_iff₀ hD' (by positivity)]
  rw [le_div_iff₀ hS] at hN
  nlinarith

/-! ## Lemma 6.19(c) -/

theorem n4_X_mem {b : Box} {z : Fin 11 → ℂ} (hz : z ∈ closedBall (b.center 11) b.radius) :
    (n4D1 b).Mem (N4.X z 0) ∧ (n4D2 b).Mem (N4.X z 1) ∧ (n4D3 b).Mem (N4.X z 2) ∧ (n4D4 b).Mem (N4.X z 3) ∧
      (n4X34Disc b).Mem (N4.X z 2 - N4.X z 3) := by
  have h0 := coord_mem hz 0
  have h1 := coord_mem hz 1
  rw [show ((0 : Fin 11) : ℕ) = 0 from rfl] at h0
  rw [show ((1 : Fin 11) : ℕ) = 1 from rfl] at h1
  simp only [coordDisc] at h0 h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hp : N4.X z 0 = (((1 : ℤ) : ℂ) * z 0 + ((0 : ℤ) : ℂ) * z 1 + ((1 : ℤ) : ℂ)) / ((1 : ℕ) : ℂ) := by
      simp [N4.X]
    rw [hp]
    exact affine_mem h0 h1 1 0 1 1 one_pos (by simp [n4D1]) (by simp [n4D1]) (by simp [n4D1]) (by simp [n4D1])
  · have hp : N4.X z 1 = (((1 : ℤ) : ℂ) * z 0 + ((0 : ℤ) : ℂ) * z 1 + ((0 : ℤ) : ℂ)) / ((1 : ℕ) : ℂ) := by
      simp [N4.X]
    rw [hp]
    exact affine_mem h0 h1 1 0 0 1 one_pos (by simp [n4D2]) (by simp [n4D2]) (by simp [n4D2]) (by simp [n4D2])
  · have hp : N4.X z 2 = (((0 : ℤ) : ℂ) * z 0 + ((1 : ℤ) : ℂ) * z 1 + ((0 : ℤ) : ℂ)) / ((1 : ℕ) : ℂ) := by
      simp [N4.X]
    rw [hp]
    exact affine_mem h0 h1 0 1 0 1 one_pos (by simp [n4D3]) (by simp [n4D3]) (by simp [n4D3]) (by simp [n4D3])
  · have hp : N4.X z 3 = (((-3 : ℤ) : ℂ) * z 0 + ((-3 : ℤ) : ℂ) * z 1 + ((-1 : ℤ) : ℂ)) / ((30 : ℕ) : ℂ) := by
      simp [N4.X, μ0]
      ring
    rw [hp]
    exact affine_mem h0 h1 (-3) (-3) (-1) 30 (by norm_num) (by simp [n4D4]; try ring) (by simp [n4D4]; try ring)
      (by simp [n4D4]; try ring) (by simp [n4D4]; try omega)
  · have hp : N4.X z 2 - N4.X z 3 =
        (((3 : ℤ) : ℂ) * z 0 + ((33 : ℤ) : ℂ) * z 1 + ((1 : ℤ) : ℂ)) / ((30 : ℕ) : ℂ) := by
      simp [N4.X, μ0]
      ring
    rw [hp]
    exact affine_mem h0 h1 3 33 1 30 (by norm_num) (by simp [n4X34Disc]; try ring) (by simp [n4X34Disc]; try ring)
      (by simp [n4X34Disc]; try ring) (by simp [n4X34Disc]; try omega)

/-- The T-test with margin `0.1756` at some body, as a statement about the reals `t_l = ‖X_l‖^{-1/2}`. -/
def TTest4 (t : Fin 4 → ℝ) : Prop :=
  ∃ k : Fin 4, (1756 / 10000 : ℝ) * (∑ l, (μ0 l).re * t l) ≤
    (μ0 k).re * t k - ∑ l, if l = k then 0 else (μ0 l).re * t l

theorem tTestN4_sound {l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (h : tTestN4 l1 u1 l2 u2 l3 u3 l4 u4 = true) {t : Fin 4 → ℝ}
    (h1 : (l1 : ℝ) / 2 ^ Q ≤ t 0 ∧ t 0 ≤ (u1 : ℝ) / 2 ^ Q) (h2 : (l2 : ℝ) / 2 ^ Q ≤ t 1 ∧ t 1 ≤ (u2 : ℝ) / 2 ^ Q)
    (h3 : (l3 : ℝ) / 2 ^ Q ≤ t 2 ∧ t 2 ≤ (u3 : ℝ) / 2 ^ Q) (h4 : (l4 : ℝ) / 2 ^ Q ≤ t 3 ∧ t 3 ≤ (u4 : ℝ) / 2 ^ Q) :
    TTest4 t := by
  unfold tTestN4 at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  have hq : (0 : ℝ) < 2 ^ Q := by positivity
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  obtain ⟨a3, b3⟩ := h3
  obtain ⟨a4, b4⟩ := h4
  rw [div_le_iff₀ hq] at a1 a2 a3 a4
  rw [le_div_iff₀ hq] at b1 b2 b3 b4
  unfold TTest4
  simp only [Fin.sum_univ_four, μ0]
  rcases h with ((h | h) | h) | h
  · refine ⟨0, ?_⟩
    have h' : (11756 : ℝ) * (2 * u2 + 3 * u3 + 30 * u4) ≤ 8244 * l1 := by exact_mod_cast h
    norm_num
    nlinarith
  · refine ⟨1, ?_⟩
    have h' : (11756 : ℝ) * (u1 + 3 * u3 + 30 * u4) ≤ 8244 * (2 * l2) := by exact_mod_cast h
    norm_num
    nlinarith
  · refine ⟨2, ?_⟩
    have h' : (11756 : ℝ) * (u1 + 2 * u2 + 30 * u4) ≤ 8244 * (3 * l3) := by exact_mod_cast h
    norm_num
    nlinarith
  · refine ⟨3, ?_⟩
    have h' : (11756 : ℝ) * (u1 + 2 * u2 + 3 * u3) ≤ 8244 * (30 * l4) := by exact_mod_cast h
    norm_num
    nlinarith

theorem s11T_termOK : ∀ Fi ∈ s11T, ∀ t ∈ Fi, termOK 11 t = true := by
  have : s11T.all (fun Fi => Fi.all (termOK 11)) = true := by decide
  simp only [List.all_eq_true] at this
  exact this

/-- `S11` is the row-scaled generated map. -/
theorem S11_eq (z : Fin 11 → ℂ) (i : Fin 11) :
    N4.S11 z i = (N4.scale i)⁻¹ * (s11T.getD i []).eval κ1 (extF z) := by
  have : s11T.getD i [] = s11T.get (i.cast N4.s11T_length.symm) := by
    rw [List.getD_eq_getElem _ _ (by rw [N4.s11T_length]; exact i.2)]; rfl
  rw [this, N4.eval_s11T, ← mul_assoc, inv_mul_cancel₀ (N4.scale_ne_zero i), one_mul]

/-- **Zeros and Jacobian from a Krawczyk box**, for a system `G` that is a row scaling of the generated rows `F`. -/
theorem zero_jac_of_kraw {F : List TPoly} {n : ℕ} (hn : F.length = n) (hn0 : 0 < n)
    (hF : ∀ Fi ∈ F, ∀ t ∈ Fi, termOK n t = true) {G : (Fin n → ℂ) → Fin n → ℂ} {sc : Fin n → ℂ}
    (hsc : ∀ i, sc i ≠ 0) (hG : ∀ z i, G z i = (sc i)⁻¹ * (F.getD i []).eval κ1 (extF z)) {b : Box}
    (hsmall : centersSmall b = true) (hlen : b.cs.length = n) (hk : krawOK P tab1 F (b.cs.map mkCenter) b.rho = true) :
    ∃ z ∈ closedBall (b.center n) b.radius, G z = 0 ∧ (∀ w ∈ closedBall (b.center n) b.radius, G w = 0 → w = z) ∧
      ∃ J : Matrix (Fin n) (Fin n) ℂ, IsUnit J.det ∧ HasFDerivAt G (Matrix.toLin' J).toContinuousLinearMap z := by
  obtain ⟨z, hz, hFz, hdet, huniq⟩ := kraw_unique_n hn hk listMemF_tab1 hn0
  have hcen : (fun j : Fin n => centerC P ((b.cs.map mkCenter).getD j.1 (zero P))) = b.center n := by
    funext j
    exact kraw_center_eq hsmall hlen j
  rw [hcen] at hz huniq
  have hzero : ∀ w, G w = 0 ↔ ∀ i : Fin n, (F.getD i []).eval κ1 (extF w) = 0 := by
    intro w
    constructor
    · intro h0 i
      have := hG w i
      rw [h0] at this
      simp only [Pi.zero_apply] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (inv_ne_zero (hsc i))
    · intro h0
      funext i
      rw [hG w i, h0 i, mul_zero]
      rfl
  refine ⟨z, hz, (hzero z).mpr hFz, fun w hw hw0 => huniq w hw ((hzero w).mp hw0), ?_⟩
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (sc i)⁻¹
  let Jm := slopeMatrixN κ1 (extF z) (extF z) F n
  refine ⟨D * Jm, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ hdet
    rw [Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (hsc i)).isUnit
  · have hd := hasFDerivAt_tpoly_n hn κ1 hF z
    let Dl : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := (Matrix.toLin' D).toContinuousLinearMap
    have hfun : G = fun w => Dl (fun i : Fin n => (F.getD i []).eval κ1 (extF w)) := by
      funext w i
      rw [hG w i]
      simp only [Dl, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, D, Matrix.mulVec_diagonal]
    have hcomp := HasFDerivAt.comp z Dl.hasFDerivAt hd
    rw [hfun]
    have hL : (Matrix.toLin' (D * Jm)).toContinuousLinearMap =
        Dl.comp (Matrix.toLin' (slopeMatrixN κ1 (extF z) (extF z) F n)).toContinuousLinearMap := by
      ext w i
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, LinearMap.coe_toContinuousLinearMap',
        Matrix.toLin'_apply, Dl, Matrix.mulVec_mulVec, Jm]
    rw [hL]
    exact hcomp

/-- **A box of Lemma 6.19(c), as a `Box` value** (the test after parsing): its polydisc has radius in
`(0, 6·10⁻⁴⁷)`, contains exactly one zero of S11, at which the Jacobian is invertible, and at every point of it
`X₃ − X₄ ≠ 0`, the T-test holds and every `X_l ≠ 0`. -/
theorem n4_box_soundB {b : Box} (h : (n4RadiusOK b && krawBox s11T b && n4Extra b) = true) :
    0 < b.radius ∧ b.radius < 6 / 10 ^ 47 ∧
      (∃ z ∈ closedBall (b.center 11) b.radius, N4.S11 z = 0 ∧
        (∀ w ∈ closedBall (b.center 11) b.radius, N4.S11 w = 0 → w = z) ∧
        ∃ J : Matrix (Fin 11) (Fin 11) ℂ, IsUnit J.det ∧ HasFDerivAt N4.S11 (Matrix.toLin' J).toContinuousLinearMap z) ∧
      ∀ w ∈ closedBall (b.center 11) b.radius,
        N4.X w 2 - N4.X w 3 ≠ 0 ∧ TTest4 (fun l => 1 / Real.sqrt ‖N4.X w l‖) ∧ ∀ l, N4.X w l ≠ 0 := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hrad, hkraw⟩, hext⟩ := h
  unfold n4RadiusOK at hrad
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrad
  unfold krawBox at hkraw
  simp only [Bool.and_eq_true] at hkraw
  obtain ⟨hsmall, hk⟩ := hkraw
  unfold n4Extra at hext
  simp only [Bool.and_eq_true, beq_iff_eq] at hext
  obtain ⟨⟨hlen, hnz⟩, htt⟩ := hext
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Box.radius
    have : (0 : ℝ) < b.rho := by exact_mod_cast hrad.1
    positivity
  · unfold Box.radius
    have h6 : (b.rho : ℝ) * 10 ^ 47 < 6 * 2 ^ P := by
      have := hrad.2
      rw [← S_cast]
      exact_mod_cast this
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  · exact zero_jac_of_kraw N4.s11T_length (by norm_num) s11T_termOK N4.scale_ne_zero S11_eq hsmall hlen hk
  · intro w hw
    obtain ⟨m1, m2, m3, m4, m34⟩ := n4_X_mem hw
    refine ⟨discNonzero_sound hnz (by simp [n4X34Disc, S]) m34, ?_⟩
    split at htt
    · rename_i l1 u1 l2 u2 l3 u3 l4 u4 e1 e2 e3 e4
      refine ⟨tTestN4_sound htt
        (discInvSqrt_sound e1 (by simp [n4D1, S]) m1) (discInvSqrt_sound e2 (by simp [n4D2, S]) m2)
        (discInvSqrt_sound e3 (by simp [n4D3, S]) m3) (discInvSqrt_sound e4 (by simp [n4D4, S]) m4), ?_⟩
      intro l
      fin_cases l
      · exact discInvSqrt_ne_zero e1 (by simp [n4D1, S]) m1
      · exact discInvSqrt_ne_zero e2 (by simp [n4D2, S]) m2
      · exact discInvSqrt_ne_zero e3 (by simp [n4D3, S]) m3
      · exact discInvSqrt_ne_zero e4 (by simp [n4D4, S]) m4
    · exact absurd htt (by simp)

/-- The test of a box of Lemma 6.19(c) fixes the number of centres: `11`. -/
theorem n4_len_of_test {b : Box} (h : (n4RadiusOK b && krawBox s11T b && n4Extra b) = true) : b.cs.length = 11 := by
  simp only [Bool.and_eq_true] at h
  have := h.2
  unfold n4Extra at this
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1

/-- **A box of Lemma 6.19(c)**, as a string of the certificate file: `n4_box_soundB` after parsing. -/
theorem n4_box_sound {s : String} (h : n4BoxOK s = true) :
    ∃ b, parseBox s = some b ∧ 0 < b.radius ∧ b.radius < 6 / 10 ^ 47 ∧
      (∃ z ∈ closedBall (b.center 11) b.radius, N4.S11 z = 0 ∧
        (∀ w ∈ closedBall (b.center 11) b.radius, N4.S11 w = 0 → w = z) ∧
        ∃ J : Matrix (Fin 11) (Fin 11) ℂ, IsUnit J.det ∧ HasFDerivAt N4.S11 (Matrix.toLin' J).toContinuousLinearMap z) ∧
      ∀ w ∈ closedBall (b.center 11) b.radius,
        N4.X w 2 - N4.X w 3 ≠ 0 ∧ TTest4 (fun l => 1 / Real.sqrt ‖N4.X w l‖) ∧ ∀ l, N4.X w l ≠ 0 := by
  unfold n4BoxOK at h
  split at h
  · rename_i b hb
    exact ⟨b, hb, n4_box_soundB h⟩
  · exact absurd h (by simp)

end Lean6.Special.D88.Boxes
