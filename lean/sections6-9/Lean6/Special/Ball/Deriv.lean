import Lean6.Special.Ball.KrawCheckSem
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The slope matrix at a point is the derivative

For a square system `F` of admissible polynomials (`TPoly`), the divided-difference slope matrix `S(u, v)` of
`SlopeSem.lean` satisfies `F(u) − F(z) = S(u, z)(u − z)` and is continuous in `u`, so
**`hasFDerivAt_tpoly`**: the map `u ↦ F(u)` has the derivative `S(z, z)` at `z`. With `kraw_unique` this makes the
zero of a Krawczyk box a zero with an invertible Jacobian.
-/

namespace Lean6.Special.Kraw

open Lean6.Special.Ball Matrix Filter Topology Asymptotics

/-- `‖A v‖ ≤ (Σᵢ Σⱼ ‖Aᵢⱼ‖) ‖v‖` in the sup norm. -/
theorem norm_mulVec_le_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ‖A *ᵥ v‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  refine (norm_mulVec_apply_le A v i).trans ?_
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖) (fun i _ => by positivity) (Finset.mem_univ i)) (norm_nonneg _)

/-- **Differentiability from a continuous slope**: `f(u) − f(z) = S(u)(u − z)` with `S` continuous at `z` gives the
derivative `S(z)` at `z`. -/
theorem hasFDerivAt_of_slope {n : ℕ} {f : (Fin n → ℂ) → (Fin n → ℂ)} {S : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ}
    {z : Fin n → ℂ} (hslope : ∀ u, f u - f z = S u *ᵥ (u - z)) (hcont : ∀ i j, ContinuousAt (fun u => S u i j) z) :
    HasFDerivAt f (Matrix.toLin' (S z)).toContinuousLinearMap z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hg : Tendsto (fun h : Fin n → ℂ => ∑ i, ∑ j, ‖S (z + h) i j - S z i j‖) (𝓝 0) (𝓝 0) := by
    have hij : ∀ i j, Tendsto (fun h : Fin n → ℂ => ‖S (z + h) i j - S z i j‖) (𝓝 0) (𝓝 0) := by
      intro i j
      have h1 : Tendsto (fun h : Fin n → ℂ => z + h) (𝓝 0) (𝓝 z) := by
        have := (tendsto_const_nhds : Tendsto (fun _ : Fin n → ℂ => z) (𝓝 0) (𝓝 z)).add
          (tendsto_id : Tendsto (fun h : Fin n → ℂ => h) (𝓝 0) (𝓝 0))
        simpa using this
      have h2 := (hcont i j).tendsto.comp h1
      have h3 : Tendsto (fun h : Fin n → ℂ => S (z + h) i j - S z i j) (𝓝 0) (𝓝 0) := by
        have := h2.sub_const (S z i j)
        simpa using this
      have := h3.norm
      simpa using this
    have := tendsto_finset_sum (Finset.univ : Finset (Fin n))
      fun i _ => tendsto_finset_sum (Finset.univ : Finset (Fin n)) fun j _ => hij i j
    simpa using this
  filter_upwards [hg.eventually (Iio_mem_nhds hc)] with h hh
  have eq : f (z + h) - f z - (Matrix.toLin' (S z)).toContinuousLinearMap h = (S (z + h) - S z) *ᵥ h := by
    rw [hslope (z + h)]
    simp [Matrix.sub_mulVec]
  rw [eq]
  refine (norm_mulVec_le_sum _ _).trans ?_
  have : ∑ i, ∑ j, ‖(S (z + h) - S z) i j‖ ≤ c := by
    simp only [Matrix.sub_apply]
    exact (Set.mem_Iio.mp hh).le
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

theorem continuous_extF_apply {n : ℕ} (j : ℕ) : Continuous fun u : Fin n → ℂ => extF u j := by
  unfold extF
  by_cases h : j < n
  · simp only [h, dif_pos]
    exact continuous_apply _
  · simp only [h, dif_neg, not_false_eq_true]
    exact continuous_const

/-- The divided differences are continuous in the first point. -/
theorem continuous_dd {n : ℕ} (κ : ℕ → ℂ) (z : Fin n → ℂ) (j : ℕ) (p : TPoly) :
    Continuous fun u : Fin n → ℂ => p.dd κ (extF u) (extF z) j := by
  unfold TPoly.dd
  apply continuous_list_sum
  intro t _
  unfold TTerm.dd
  by_cases hj : j ∈ t.mono.map Prod.fst
  · simp only [hj, if_true]
    apply Continuous.mul continuous_const
    unfold ddProd
    apply continuous_list_prod
    intro ve _
    by_cases hv : ve.1 = j
    · simp only [hv, if_true]
      unfold hsum
      apply continuous_finset_sum
      intro i _
      exact ((continuous_extF_apply j).pow i).mul continuous_const
    · simp only [hv, if_false]
      unfold hyb
      by_cases hlt : ve.1 < j
      · simp only [hlt, if_true]
        exact (continuous_extF_apply _).pow _
      · simp only [hlt, if_false]
        exact continuous_const
  · simp only [hj, if_false]
    exact continuous_const

/-- **The derivative of a polynomial system is the slope matrix at the point.** -/
theorem hasFDerivAt_tpoly {F : List TPoly} (κ : ℕ → ℂ) (hF : ∀ Fi ∈ F, ∀ t ∈ Fi, termOK F.length t = true)
    (z : Fin F.length → ℂ) :
    HasFDerivAt (fun u : Fin F.length → ℂ => fun i => (F.get i).eval κ (extF u))
      (Matrix.toLin' (slopeMatrix κ (extF z) (extF z) F)).toContinuousLinearMap z := by
  have hok : ∀ Fi ∈ F, ∀ t ∈ Fi, (∀ ve ∈ t.mono, ve.1 < F.length ∧ 0 < ve.2) ∧ (t.mono.map Prod.fst).Nodup :=
    fun Fi hFi t ht => termOK_spec (hF Fi hFi t ht)
  refine hasFDerivAt_of_slope (S := fun u => slopeMatrix κ (extF u) (extF z) F) ?_ ?_
  · intro u
    funext i
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, slopeMatrix]
    rw [TPoly.eval_sub_eq κ (extF u) (extF z) F.length (F.get i) (hok _ (List.get_mem _ _)),
      ← Fin.sum_univ_eq_sum_range (fun j => (extF u j - extF z j) * (F.get i).dd κ (extF u) (extF z) j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [extF_lt u j.2, extF_lt z j.2, mul_comm]
  · intro i j
    exact (continuous_dd κ z j (F.get i)).continuousAt

end Lean6.Special.Kraw

namespace Lean6.Special.Kraw

open Lean6.Special.Ball Matrix Metric

/-- The slope matrix on `Fin n`, read with `getD`. -/
def slopeMatrixN (κ u v : ℕ → ℂ) (F : List TPoly) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (F.getD i []).dd κ u v j

/-- **`kraw_unique` on `Fin n`** for a system with `n` equations. -/
theorem kraw_unique_n {P : ℕ} {tab : List CB} {F : List TPoly} {cs : List CB} {rho n : ℕ} (hn : F.length = n)
    (h : krawOK P tab F cs rho = true) {κ : ℕ → ℂ} (hκ : ListMemF P κ tab) (hn0 : 0 < n) :
    ∃ z : Fin n → ℂ, z ∈ closedBall (fun j : Fin n => centerC P (cs.getD j.1 (zero P))) ((rho : ℝ) / 2 ^ P) ∧
      (∀ i : Fin n, (F.getD i []).eval κ (extF z) = 0) ∧ IsUnit (slopeMatrixN κ (extF z) (extF z) F n).det ∧
      ∀ w ∈ closedBall (fun j : Fin n => centerC P (cs.getD j.1 (zero P))) ((rho : ℝ) / 2 ^ P),
        (∀ i : Fin n, (F.getD i []).eval κ (extF w) = 0) → w = z := by
  subst hn
  obtain ⟨z, hz, hFz, hdet, huniq⟩ := kraw_unique h hκ hn0
  have hget : ∀ i : Fin F.length, F.getD i [] = F.get i := fun i => by
    rw [List.getD_eq_getElem _ _ i.2]; rfl
  refine ⟨z, hz, fun i => by rw [hget]; exact hFz i, ?_, fun w hw hFw => huniq w hw fun i => by
    rw [← hget]; exact hFw i⟩
  have : slopeMatrixN κ (extF z) (extF z) F F.length = slopeMatrix κ (extF z) (extF z) F := by
    funext i j
    simp only [slopeMatrixN, slopeMatrix, hget]
  rw [this]
  exact hdet

/-- **`hasFDerivAt_tpoly` on `Fin n`.** -/
theorem hasFDerivAt_tpoly_n {F : List TPoly} {n : ℕ} (hn : F.length = n) (κ : ℕ → ℂ)
    (hF : ∀ Fi ∈ F, ∀ t ∈ Fi, termOK n t = true) (z : Fin n → ℂ) :
    HasFDerivAt (fun u : Fin n → ℂ => fun i : Fin n => (F.getD i []).eval κ (extF u))
      (Matrix.toLin' (slopeMatrixN κ (extF z) (extF z) F n)).toContinuousLinearMap z := by
  subst hn
  have hget : ∀ i : Fin F.length, F.getD i [] = F.get i := fun i => by
    rw [List.getD_eq_getElem _ _ i.2]; rfl
  have h1 : (fun u : Fin F.length → ℂ => fun i : Fin F.length => (F.getD i []).eval κ (extF u)) =
      fun u i => (F.get i).eval κ (extF u) := by
    funext u i
    rw [hget]
  have h2 : slopeMatrixN κ (extF z) (extF z) F F.length = slopeMatrix κ (extF z) (extF z) F := by
    funext i j
    simp only [slopeMatrixN, slopeMatrix, hget]
  rw [h1, h2]
  exact hasFDerivAt_tpoly κ hF z

end Lean6.Special.Kraw
