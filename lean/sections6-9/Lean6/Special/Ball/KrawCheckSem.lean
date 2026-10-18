import Lean6.Special.Comp.Ball.KrawCheck
import Lean6.Special.Ball.SlopeSem
import Lean6.Special.Ball.Kraw

/-!
# The Krawczyk test on a box of squares: soundness

**`kraw_exists`**: if `krawOK P tab F cs rho` and the table balls contain `κ`, the system `F` has a zero `x` with
`‖x_j - c_j‖ ≤ rho/2^P` for every `j < n` (`c_j` the center of `cs_j`). The proof builds the hypotheses
`KrawczykHyp` of `Ball/Kraw.lean` for `F` on `Fin n → ℂ` (sup norm), the closed ball of radius `rho/2^P` around the
centers: the slopes are the divided-difference matrices `slopeMatrix` (`TPoly.eval_sub_eq`), which lie in the balls of
`slopeMat` over the squares (a point of the disc lies in the square, `mem_sqBox`); `e_ij = magB(E_ij)/2^P` bounds
`‖(1 - Y S)_ij‖` (`matMem_resMat`, `norm_le_magB`), `b_i = magB(g_i)/2^P` bounds `‖(Y F(c))_i‖`; the row tests give the
inclusion and the contraction.
-/

namespace Lean6.Special.Kraw

open Lean6.Special.Ball Matrix Metric

variable {P : ℕ}

/-- The extension of a point with `Fin n` coordinates by `0`. -/
def extF {n : ℕ} (u : Fin n → ℂ) : ℕ → ℂ := fun j => if h : j < n then u ⟨j, h⟩ else 0

theorem extF_lt {n : ℕ} (u : Fin n → ℂ) {j : ℕ} (h : j < n) : extF u j = u ⟨j, h⟩ := by simp [extF, h]

/-- An exact valid center contains its center. -/
theorem mem_centerC_exact {x : CB} (h : centerOK P x = true) : x.Mem P (centerC P x) := by
  simp only [centerOK, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨hr, ha⟩, hs⟩ := h
  intro _
  have hp : (2 : ℝ) ^ P ≠ 0 := by positivity
  refine ⟨⟨?_, hs⟩, ?_, ?_⟩
  · have e1 := absB_eq (P := P) x.re
    have e2 := absB_eq (P := P) x.im
    have h1 : ((Nat.add (absB P x.re) (absB P x.im) : ℕ) : ℤ) ≤ x.a := by exact_mod_cast ha
    simp only [Nat.add_eq] at h1
    push_cast at h1
    linarith
  · simp only [centerC, hr, Nat.cast_zero]
    rw [div_mul_cancel₀ _ hp, sub_self, abs_zero]
  · simp only [centerC, hr, Nat.cast_zero]
    rw [div_mul_cancel₀ _ hp, sub_self, abs_zero]

/-- A point within `rho/2^P` of the center (complex norm) lies in the square of half-side `rho`. -/
theorem mem_sq_of_norm {x : CB} (h : centerOK P x = true) {rho : ℕ} {z : ℂ}
    (hz : ‖z - centerC P x‖ ≤ (rho : ℝ) / 2 ^ P) : (⟨x.re, x.im, rho, x.a, x.s⟩ : CB).Mem P z := by
  have hx := mem_centerC_exact h
  intro hs
  obtain ⟨hv, -, -⟩ := hx hs
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have hre : |(z - centerC P x).re| ≤ (rho : ℝ) / 2 ^ P := (Complex.abs_re_le_norm _).trans hz
  have him : |(z - centerC P x).im| ≤ (rho : ℝ) / 2 ^ P := (Complex.abs_im_le_norm _).trans hz
  refine ⟨⟨hv.mag, hv.hist⟩, ?_, ?_⟩
  · simp only [Complex.sub_re, centerC] at hre
    have e : z.re * 2 ^ P - (cv P x.re : ℝ) = (z.re - (cv P x.re : ℝ) / 2 ^ P) * 2 ^ P := by field_simp
    rw [e, abs_mul, abs_of_pos hp]
    calc |z.re - (cv P x.re : ℝ) / 2 ^ P| * 2 ^ P ≤ (rho : ℝ) / 2 ^ P * 2 ^ P :=
          mul_le_mul_of_nonneg_right hre hp.le
      _ = rho := div_mul_cancel₀ _ hp.ne'
  · simp only [Complex.sub_im, centerC] at him
    have e : z.im * 2 ^ P - (cv P x.im : ℝ) = (z.im - (cv P x.im : ℝ) / 2 ^ P) * 2 ^ P := by field_simp
    rw [e, abs_mul, abs_of_pos hp]
    calc |z.im - (cv P x.im : ℝ) / 2 ^ P| * 2 ^ P ≤ (rho : ℝ) / 2 ^ P * 2 ^ P :=
          mul_le_mul_of_nonneg_right him hp.le
      _ = rho := div_mul_cancel₀ _ hp.ne'

theorem getD_sqBox {cs : List CB} {rho j : ℕ} (hj : j < cs.length) :
    (sqBox cs rho).getD j (zero P) =
      ⟨(cs.getD j (zero P)).re, (cs.getD j (zero P)).im, rho, (cs.getD j (zero P)).a, (cs.getD j (zero P)).s⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa [sqBox] using hj), List.getD_eq_getElem _ _ hj]
  simp [sqBox]

/-- A row of a zipped `all`. -/
theorem all_zip_get {α β : Type*} {E : List α} {g : List β} {f : α × β → Bool} (h : ∀ eg ∈ E.zip g, f eg = true)
    {i : ℕ} (hE : i < E.length) (hg : i < g.length) : f (E[i], g[i]) = true := by
  have hz : i < (E.zip g).length := by simp [hE, hg]
  have := h _ (List.getElem_mem hz)
  simpa [List.getElem_zip] using this

/-- **The Krawczyk test gives the hypotheses of `krawczyk`** on the polydisc of radius `rho/2^P` around the centers. -/
theorem kraw_hyp {tab : List CB} {F : List TPoly} {cs : List CB} {rho : ℕ}
    (h : krawOK P tab F cs rho = true) {κ : ℕ → ℂ} (hκ : ListMemF P κ tab) (hn : 0 < F.length) :
    ∃ (Y : Matrix (Fin F.length) (Fin F.length) ℂ) (e : Fin F.length → Fin F.length → ℝ) (b : Fin F.length → ℝ),
      KrawczykHyp (fun u i => (F.get i).eval κ (extF u)) (fun j => centerC P (cs.getD j.1 (zero P)))
        ((rho : ℝ) / 2 ^ P) Y (fun u v => slopeMatrix κ (extF u) (extF v) F) e b := by
  unfold krawOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hlen, hwf⟩, hcs⟩, hrows⟩ := h
  have : NeZero F.length := ⟨by omega⟩
  have hok : ∀ Fi ∈ F, ∀ t ∈ Fi, (∀ ve ∈ t.mono, ve.1 < F.length ∧ 0 < ve.2) ∧ (t.mono.map Prod.fst).Nodup :=
    fun Fi hFi t ht => termOK_spec (hwf Fi hFi t ht)
  have hcsj : ∀ j < F.length, centerOK P (cs.getD j (zero P)) = true := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hcs _ (List.getElem_mem _)
  generalize hSb : slopeMat P tab F (sqBox cs rho) = Sb at hrows
  generalize hYb : fixMat P F.length (approxInv P Sb) = Yb at hrows
  generalize hEb : resMat P Yb (transpose P F.length Sb) = Eb at hrows
  generalize hfb : F.map (fun Fi => tEval P tab cs Fi) = fb at hrows
  generalize hgb : matVec P Yb fb = gb at hrows
  obtain ⟨c0, hc0⟩ : ∃ c0 : Fin F.length → ℂ, c0 = fun j => centerC P (cs.getD j.1 (zero P)) := ⟨_, rfl⟩
  have hc0j : ∀ (j : ℕ) (hj : j < F.length), c0 ⟨j, hj⟩ = centerC P (cs.getD j (zero P)) := by
    intro j hj; rw [hc0]
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = (rho : ℝ) / 2 ^ P := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin F.length) (Fin F.length) ℂ, Y = centerMat P F.length Yb := ⟨_, rfl⟩
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have hρ0 : 0 ≤ ρ' := by rw [hρ']; positivity
  -- points of the ball lie in the squares
  have hsq : ∀ u ∈ closedBall c0 ρ', ∀ j < F.length, ((sqBox cs rho).getD j (zero P)).Mem P (extF u j) := by
    intro u hu j hj
    rw [getD_sqBox (by omega), extF_lt u hj]
    refine mem_sq_of_norm (hcsj j hj) ?_
    have h1 : ‖u - c0‖ ≤ ρ' := mem_closedBall_iff_norm.mp hu
    have h2 := (norm_le_pi_norm (u - c0) ⟨j, hj⟩).trans h1
    rw [Pi.sub_apply, hc0j j hj, hρ'] at h2
    exact h2
  have hM : MatMem P Y Yb := by rw [hY, ← hYb]; exact matMem_fixMat _ _
  have hSm : ∀ u ∈ closedBall c0 ρ', ∀ v ∈ closedBall c0 ρ', MatMem P (slopeMatrix κ (extF u) (extF v) F) Sb := by
    intro u hu v hv
    rw [← hSb]
    exact matMem_slopeMat hκ (fun i hi => ⟨hsq u hu i hi, hsq v hv i hi⟩)
      fun Fi hFi t ht ve hve => ((hok Fi hFi t ht).1 ve hve).1
  have hc0mem : c0 ∈ closedBall c0 ρ' := mem_closedBall_self hρ0
  have hEm : ∀ u ∈ closedBall c0 ρ', ∀ v ∈ closedBall c0 ρ',
      MatMem P (resTrue Y (slopeMatrix κ (extF u) (extF v) F)) Eb := by
    intro u hu v hv
    rw [← hEb]
    exact matMem_resMat hM (hSm u hu v hv)
  -- the values at the center
  have hcpt : ListMemF P (extF c0) cs := by
    intro j
    by_cases hj : j < F.length
    · rw [extF_lt c0 hj, hc0j j hj]
      exact mem_centerC_exact (hcsj j hj)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp only [extF, dif_neg hj]
      exact mem_zero
  have hfv : VecMem P (fun i : Fin F.length => (F.get i).eval κ (extF c0)) fb := by
    refine vecMem_of_get (by rw [← hfb, List.length_map]) fun i => ?_
    simp only [← hfb, List.get_eq_getElem, List.getElem_map]
    exact mem_tEval hκ hcpt _
  have hgv : VecMem P (Y *ᵥ fun i : Fin F.length => (F.get i).eval κ (extF c0)) gb := by
    rw [← hgb]; exact vecMem_matVec hM hfv
  -- lengths and rows
  obtain ⟨hEl, hErow⟩ := forall₂_ofFn_iff.mp (hEm c0 hc0mem c0 hc0mem)
  have hgl : gb.length = F.length := hgv.length
  have hrow : ∀ i : Fin F.length, krawRowOK P rho (Eb[i.1]'(by omega)) (gb[i.1]'(by omega)) = true :=
    fun i => all_zip_get hrows (by omega) (by omega)
  have hrowl : ∀ i : Fin F.length, (Eb[i.1]'(by omega)).length = F.length := fun i => by
    obtain ⟨hl, -⟩ := forall₂_ofFn_iff.mp (hErow i)
    simpa using hl
  -- the bounds `e`, `b`
  let e : Fin F.length → Fin F.length → ℝ := fun i j => (magB P ((Eb[i.1]'(by omega))[j.1]'(by rw [hrowl i]; exact j.2)) : ℝ) / 2 ^ P
  let b : Fin F.length → ℝ := fun i => (magB P (gb[i.1]'(by omega)) : ℝ) / 2 ^ P
  have hrowfacts : ∀ i : Fin F.length,
      (∑ j : Fin F.length, (magB P ((Eb[i.1]'(by omega))[j.1]'(by rw [hrowl i]; exact j.2)) : ℕ)) < 2 ^ P ∧
      magB P (gb[i.1]'(by omega)) * 2 ^ P +
          (∑ j : Fin F.length, (magB P ((Eb[i.1]'(by omega))[j.1]'(by rw [hrowl i]; exact j.2)) : ℕ)) * rho < rho * 2 ^ P ∧
      (∀ x ∈ Eb[i.1]'(by omega), x.s ≤ smax P) ∧ (gb[i.1]'(by omega)).s ≤ smax P := by
    intro i
    have h := hrow i
    simp only [krawRowOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.pow_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hsum : (Eb[i.1]'(by omega)).foldl (fun t x => Nat.add t (magB P x)) 0 =
        ∑ j : Fin F.length, (magB P ((Eb[i.1]'(by omega))[j.1]'(by rw [hrowl i]; exact j.2)) : ℕ) := by
      rw [foldl_add_eq, zero_add, sum_magB_eq _ (hrowl i)]
      rfl
    rw [hsum] at h1 h2
    simp only [Nat.add_eq, Nat.mul_eq] at h2
    exact ⟨h1, h2, h3, h4⟩
  have hK : KrawczykHyp (fun u i => (F.get i).eval κ (extF u)) c0 ρ' Y
      (fun u v => slopeMatrix κ (extF u) (extF v) F) e b := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- slopes
      intro u _ v _
      funext i
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, slopeMatrix]
      rw [TPoly.eval_sub_eq κ (extF u) (extF v) F.length (F.get i) (hok _ (List.get_mem _ _)),
        ← Fin.sum_univ_eq_sum_range (fun j => (extF u j - extF v j) * (F.get i).dd κ (extF u) (extF v) j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [extF_lt u j.2, extF_lt v j.2, mul_comm]
    · -- the bounds of `1 - Y S`
      intro u hu v hv i j
      have hr := (forall₂_ofFn_iff.mp (hEm u hu v hv)).2
      have hr' := (forall₂_ofFn_iff.mp (hr i)).2
      have hm := hr' j
      simp only [List.get_eq_getElem] at hm
      have hs : ((Eb[i.1]'(by omega))[j.1]'(by rw [hrowl i]; exact j.2)).s ≤ smax P :=
        (hrowfacts i).2.2.1 _ (List.getElem_mem _)
      have := norm_le_magB hm hs
      rw [norm_resTrue] at this
      show ‖((1 : Matrix (Fin F.length) (Fin F.length) ℂ) - Y * slopeMatrix κ (extF u) (extF v) F) i j‖ ≤ e i j
      rw [le_div_iff₀ hp]
      exact this
    · -- the bounds of `Y F(c)`
      intro i
      have hm := hgv.get i
      simp only [List.get_eq_getElem] at hm
      have := norm_le_magB hm (hrowfacts i).2.2.2
      show ‖(Y *ᵥ fun i : Fin F.length => (F.get i).eval κ (extF c0)) i‖ ≤ b i
      rw [le_div_iff₀ hp]
      exact this
    · -- inclusion
      intro i
      have h2 := (hrowfacts i).2.1
      have h2' : ((magB P (gb[i.1]'(by omega)) : ℕ) : ℝ) * 2 ^ P +
          ((∑ j : Fin F.length, (magB P ((Eb[i.1]'(by omega))[j.1]'(by rw [hrowl i]; exact j.2)) : ℕ) : ℕ) : ℝ) * rho <
          (rho : ℝ) * 2 ^ P := by exact_mod_cast h2
      simp only [b, e, hρ']
      rw [← Finset.sum_div]
      push_cast at h2' ⊢
      have hp2 : (0 : ℝ) < 2 ^ P * 2 ^ P := by positivity
      have e1 : ∀ t S : ℝ, t / 2 ^ P + S / 2 ^ P * ((rho : ℝ) / 2 ^ P) = (t * 2 ^ P + S * rho) / (2 ^ P * 2 ^ P) := by
        intro t S; field_simp
      have e2 : (rho : ℝ) / 2 ^ P = (rho * 2 ^ P) / (2 ^ P * 2 ^ P) := by field_simp
      rw [e1, e2]
      exact div_lt_div_of_pos_right h2' hp2
    · -- contraction
      intro i
      have h1 := (hrowfacts i).1
      have h1' : ((∑ j : Fin F.length, (magB P ((Eb[i.1]'(by omega))[j.1]'(by rw [hrowl i]; exact j.2)) : ℕ) : ℕ) : ℝ) <
          2 ^ P := by exact_mod_cast h1
      simp only [e]
      rw [← Finset.sum_div, div_lt_one hp]
      push_cast at h1'
      exact h1'
  subst hc0 hρ' hY
  exact ⟨_, e, b, hK⟩

/-- **The Krawczyk test gives a zero.** -/
theorem kraw_exists {tab : List CB} {F : List TPoly} {cs : List CB} {rho : ℕ}
    (h : krawOK P tab F cs rho = true) {κ : ℕ → ℂ} (hκ : ListMemF P κ tab) (hn : 0 < F.length) :
    ∃ x : ℕ → ℂ, (∀ j < F.length, ‖x j - centerC P (cs.getD j (zero P))‖ ≤ (rho : ℝ) / 2 ^ P) ∧
      ∀ i < F.length, (F.getD i []).eval κ x = 0 := by
  obtain ⟨Y, e, b, hK⟩ := kraw_hyp h hκ hn
  have : NeZero F.length := ⟨by omega⟩
  obtain ⟨u, ⟨hu, hFu⟩, -⟩ := krawczyk hK
  refine ⟨extF u, fun j hj => ?_, fun i hi => ?_⟩
  · rw [extF_lt u hj]
    have h1 := mem_closedBall_iff_norm.mp hu
    have h2 := (norm_le_pi_norm _ ⟨j, hj⟩).trans h1
    simpa using h2
  · have := congrFun hFu ⟨i, hi⟩
    rw [List.getD_eq_getElem _ _ hi]
    simpa using this

/-- **The Krawczyk test gives exactly one zero in the polydisc, and the slope matrix at it is invertible.** -/
theorem kraw_unique {tab : List CB} {F : List TPoly} {cs : List CB} {rho : ℕ}
    (h : krawOK P tab F cs rho = true) {κ : ℕ → ℂ} (hκ : ListMemF P κ tab) (hn : 0 < F.length) :
    ∃ z : Fin F.length → ℂ,
      z ∈ closedBall (fun j : Fin F.length => centerC P (cs.getD j.1 (zero P))) ((rho : ℝ) / 2 ^ P) ∧
      (∀ i, (F.get i).eval κ (extF z) = 0) ∧ IsUnit (slopeMatrix κ (extF z) (extF z) F).det ∧
      ∀ w ∈ closedBall (fun j : Fin F.length => centerC P (cs.getD j.1 (zero P))) ((rho : ℝ) / 2 ^ P),
        (∀ i, (F.get i).eval κ (extF w) = 0) → w = z := by
  obtain ⟨Y, e, b, hK⟩ := kraw_hyp h hκ hn
  have : NeZero F.length := ⟨by omega⟩
  obtain ⟨z, hz, hFz, hdet, huniq⟩ := krawczyk_jacobian hK
  exact ⟨z, hz, fun i => congrFun hFz i, hdet, fun w hw hFw => huniq w hw (funext hFw)⟩

end Lean6.Special.Kraw
