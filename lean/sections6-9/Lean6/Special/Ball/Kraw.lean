import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# The Krawczyk test in `𝕜ⁿ` (contraction form)

**`krawczyk`**: let `𝕜` be `ℝ` or `ℂ` (any `RCLike` field), `F : 𝕜ⁿ → 𝕜ⁿ` (`𝕜ⁿ = Fin n → 𝕜` with Mathlib's sup norm),
a box `B = closedBall c ρ`, a matrix `Y` and *slopes* `S u v` with `F u - F v = S u v (u - v)` for `u, v ∈ B`. If, for
every row `i`, `‖(1 - Y S u v)ᵢⱼ‖ ≤ eᵢⱼ` for `u, v ∈ B`, `‖(Y F c)ᵢ‖ ≤ bᵢ`, `bᵢ + (Σⱼ eᵢⱼ) ρ < ρ` (inclusion) and
`Σⱼ eᵢⱼ < 1` (contraction) (the hypotheses `KrawczykHyp`), then `F` has exactly one zero in `B`.
**`KrawczykHyp.isUnit_det_Y`**, **`KrawczykHyp.isUnit_det_S`**: `Y` and every slope `S u v` (`u, v ∈ B`) are
invertible. **`krawczyk_jacobian`**: the zero `z` is nonsingular, `det (S z z) ≠ 0` (`S z z` is the Jacobian of `F` at
`z` when the slopes are chosen with `S u u = DF(u)`).

The map `T u = u - Y F u` (`kmap`) satisfies `T u - T v = (1 - Y S u v)(u - v)` on `B` (`KrawczykHyp.kmap_sub`), by the
slope identity alone (no derivative and no mean value theorem). The row sums of `‖1 - Y S u v‖` are at most
`q = max (0, maxᵢ Σⱼ eᵢⱼ) < 1` (`qc`), so `‖(1 - Y S u v) w‖ ≤ q ‖w‖` (`norm_mulVec_le_qc`); in Mathlib's `ℓ^∞`
operator norm, `‖1 - Y S u v‖ ≤ q < 1` (`KrawczykHyp.linfty_opNorm_le`, `KrawczykHyp.linfty_opNorm_lt_one`). Hence `T`
is a `q`-contraction of `B`, and it maps `B` into itself by the inclusion; Banach's fixed point theorem
(`ContractingWith.exists_fixedPoint`, on the complete subtype `B`) gives a fixed point. A vector `w` with
`Y S u v w = 0` satisfies `w = (1 - Y S u v) w`, so `‖w‖ ≤ q ‖w‖` and `w = 0`: `det Y · det (S u v) ≠ 0`
(`KrawczykHyp.det_mul_ne_zero`). So the fixed points of `T` are exactly the zeros of `F`
(`KrawczykHyp.kmap_eq_self_iff`), and the contraction makes the zero unique.

**Dimension.** `krawczyk` and `krawczyk_jacobian` assume `[NeZero n]`, i.e. `0 < n`: for `n ≥ 1` the hypotheses force
`0 < ρ` (`KrawczykHyp.rho_pos`), while for `n = 0` they are vacuous and allow `ρ < 0`, an empty box.
`krawczyk_of_mem` assumes `c ∈ B` instead and holds for every `n`, as do the invertibility statements.

**Provenance.** A port of the 2×2 theorem `CC50.TM.krawczyk2` of the author's earlier Lean development (file `CC50/TM/Krawczyk.lean`) from `ℝ²` to
`Fin n → 𝕜`: the same hypotheses (`|·|` becomes `‖·‖`, the two-term row sums become `Σⱼ`) and the same proof. The
invertibility of `Y`, there a 2×2 determinant computation (`det (Y S c c) = det (1 - E) > 0`), is here the injectivity
argument above, which also gives the invertibility of the slopes. The statements are over `RCLike 𝕜`, so they apply to
`ℂⁿ` directly, with no passage to `ℝ^{2n}`.
-/

namespace Lean6.Special.Ball

open Metric

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ## Row sums and the sup norm -/

/-- A component of `A w` is at most the row sum of `‖Aᵢⱼ‖` times `‖w‖`. -/
theorem norm_mulVec_apply_le (A : Matrix (Fin n) (Fin n) 𝕜) (w : Fin n → 𝕜) (i : Fin n) :
    ‖A.mulVec w i‖ ≤ (∑ j, ‖A i j‖) * ‖w‖ := by
  show ‖∑ j, A i j * w j‖ ≤ _
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w j) (norm_nonneg _)

/-- The same with entrywise bounds `‖Aᵢⱼ‖ ≤ eᵢⱼ`. -/
theorem norm_mulVec_apply_le_of_le {A : Matrix (Fin n) (Fin n) 𝕜} {e : Fin n → Fin n → ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ e i j) (w : Fin n → 𝕜) (i : Fin n) :
    ‖A.mulVec w i‖ ≤ (∑ j, e i j) * ‖w‖ :=
  (norm_mulVec_apply_le A w i).trans
    (mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => hA i j) (norm_nonneg w))

/-- The contraction constant `q = max (0, maxᵢ Σⱼ eᵢⱼ)` (`0` for `n = 0`). -/
noncomputable def qc (e : Fin n → Fin n → ℝ) : NNReal :=
  Finset.univ.sup fun i => (∑ j, e i j).toNNReal

theorem row_le_qc (e : Fin n → Fin n → ℝ) (i : Fin n) : ∑ j, e i j ≤ qc e :=
  (Real.le_coe_toNNReal _).trans <| NNReal.coe_le_coe.mpr <|
    Finset.le_sup (f := fun i => (∑ j, e i j).toNNReal) (Finset.mem_univ i)

theorem qc_lt_one {e : Fin n → Fin n → ℝ} (h : ∀ i, ∑ j, e i j < 1) : qc e < 1 :=
  (Finset.sup_lt_iff (by simp)).mpr fun i _ => Real.toNNReal_lt_one.mpr (h i)

/-- **The operator norm bound**: with entrywise bounds `‖Aᵢⱼ‖ ≤ eᵢⱼ`, `‖A w‖ ≤ q ‖w‖`. -/
theorem norm_mulVec_le_qc {A : Matrix (Fin n) (Fin n) 𝕜} {e : Fin n → Fin n → ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ e i j) (w : Fin n → 𝕜) : ‖A.mulVec w‖ ≤ qc e * ‖w‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i =>
    (norm_mulVec_apply_le_of_le hA w i).trans (mul_le_mul_of_nonneg_right (row_le_qc e i) (norm_nonneg w))

theorem eq_zero_of_le_mul_of_lt_one {q : NNReal} {x : ℝ} (hq : q < 1) (hx : 0 ≤ x) (h : x ≤ q * x) :
    x = 0 := by
  have : (q : ℝ) < 1 := by exact_mod_cast hq
  exact le_antisymm (by nlinarith) hx

/-! ## The hypotheses and the Krawczyk map -/

/-- The hypotheses of the Krawczyk test on the box `closedBall c ρ` (sup norm): the slope identity, the entrywise bounds
`e` of `1 - Y S u v`, the bounds `b` of `Y F c`, the inclusion and the contraction (row by row). -/
structure KrawczykHyp (F : (Fin n → 𝕜) → Fin n → 𝕜) (c : Fin n → 𝕜) (ρ : ℝ) (Y : Matrix (Fin n) (Fin n) 𝕜)
    (S : (Fin n → 𝕜) → (Fin n → 𝕜) → Matrix (Fin n) (Fin n) 𝕜) (e : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    Prop where
  /-- slopes: `F u - F v = S u v (u - v)` on the box -/
  slope : ∀ u ∈ closedBall c ρ, ∀ v ∈ closedBall c ρ, F u - F v = (S u v).mulVec (u - v)
  /-- entrywise bounds of `1 - Y S u v` on the box -/
  hE : ∀ u ∈ closedBall c ρ, ∀ v ∈ closedBall c ρ, ∀ i j,
    ‖((1 : Matrix (Fin n) (Fin n) 𝕜) - Y * S u v) i j‖ ≤ e i j
  /-- bounds of `Y F c` -/
  hb : ∀ i, ‖(Y.mulVec (F c)) i‖ ≤ b i
  /-- inclusion -/
  incl : ∀ i, b i + (∑ j, e i j) * ρ < ρ
  /-- contraction -/
  contr : ∀ i, ∑ j, e i j < 1

/-- The Krawczyk map `T u = u - Y F u`. -/
def kmap (Y : Matrix (Fin n) (Fin n) 𝕜) (F : (Fin n → 𝕜) → Fin n → 𝕜) (u : Fin n → 𝕜) : Fin n → 𝕜 :=
  u - Y.mulVec (F u)

variable {F : (Fin n → 𝕜) → Fin n → 𝕜} {c : Fin n → 𝕜} {ρ : ℝ} {Y : Matrix (Fin n) (Fin n) 𝕜}
  {S : (Fin n → 𝕜) → (Fin n → 𝕜) → Matrix (Fin n) (Fin n) 𝕜} {e : Fin n → Fin n → ℝ} {b : Fin n → ℝ}
  {u v : Fin n → 𝕜}

namespace KrawczykHyp

/-- `T u - T v = (1 - Y S u v)(u - v)` on the box. -/
theorem kmap_sub (h : KrawczykHyp F c ρ Y S e b) (hu : u ∈ closedBall c ρ) (hv : v ∈ closedBall c ρ) :
    kmap Y F u - kmap Y F v = ((1 : Matrix (Fin n) (Fin n) 𝕜) - Y * S u v).mulVec (u - v) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← h.slope u hu v hv, Matrix.mulVec_sub]
  simp only [kmap]
  abel

/-- `T u - c = (1 - Y S u c)(u - c) - Y F c` on the box. -/
theorem kmap_sub_center (h : KrawczykHyp F c ρ Y S e b) (hu : u ∈ closedBall c ρ) (hc : c ∈ closedBall c ρ) :
    kmap Y F u - c = ((1 : Matrix (Fin n) (Fin n) 𝕜) - Y * S u c).mulVec (u - c) - Y.mulVec (F c) := by
  rw [← h.kmap_sub hu hc]
  simp only [kmap]
  abel

theorem e_nonneg (h : KrawczykHyp F c ρ Y S e b) (hu : u ∈ closedBall c ρ) (i j : Fin n) : 0 ≤ e i j :=
  (norm_nonneg _).trans (h.hE u hu u hu i j)

/-- `‖(1 - Y S u v) w‖ ≤ q ‖w‖` on the box. -/
theorem norm_mulVec_le (h : KrawczykHyp F c ρ Y S e b) (hu : u ∈ closedBall c ρ) (hv : v ∈ closedBall c ρ)
    (w : Fin n → 𝕜) : ‖((1 : Matrix (Fin n) (Fin n) 𝕜) - Y * S u v).mulVec w‖ ≤ qc e * ‖w‖ :=
  norm_mulVec_le_qc (h.hE u hu v hv) w

open scoped Matrix.Norms.Operator in
/-- In Mathlib's `ℓ^∞` operator norm (the maximal row sum), `‖1 - Y S u v‖ ≤ q` on the box. -/
theorem linfty_opNorm_le (h : KrawczykHyp F c ρ Y S e b) (hu : u ∈ closedBall c ρ) (hv : v ∈ closedBall c ρ) :
    ‖(1 : Matrix (Fin n) (Fin n) 𝕜) - Y * S u v‖ ≤ qc e := by
  rw [Matrix.linfty_opNorm_def, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_sum]
  simp only [coe_nnnorm]
  exact (Finset.sum_le_sum fun j _ => h.hE u hu v hv i j).trans (row_le_qc e i)

open scoped Matrix.Norms.Operator in
/-- In Mathlib's `ℓ^∞` operator norm, `‖1 - Y S u v‖ < 1` on the box. -/
theorem linfty_opNorm_lt_one (h : KrawczykHyp F c ρ Y S e b) (hu : u ∈ closedBall c ρ)
    (hv : v ∈ closedBall c ρ) : ‖(1 : Matrix (Fin n) (Fin n) 𝕜) - Y * S u v‖ < 1 :=
  (h.linfty_opNorm_le hu hv).trans_lt (by exact_mod_cast qc_lt_one h.contr)

/-- `Y S u v` is invertible on the box: a kernel vector `w` satisfies `w = (1 - Y S u v) w`, so `‖w‖ ≤ q ‖w‖`. -/
theorem det_mul_ne_zero (h : KrawczykHyp F c ρ Y S e b) (hu : u ∈ closedBall c ρ) (hv : v ∈ closedBall c ρ) :
    (Y * S u v).det ≠ 0 := by
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : ((1 : Matrix (Fin n) (Fin n) 𝕜) - Y * S u v).mulVec w = w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hw, sub_zero]
  have h2 := h.norm_mulVec_le hu hv w
  rw [h1] at h2
  exact hw0 (norm_eq_zero.mp (eq_zero_of_le_mul_of_lt_one (qc_lt_one h.contr) (norm_nonneg w) h2))

/-- **The slopes are invertible** on the box. -/
theorem isUnit_det_S (h : KrawczykHyp F c ρ Y S e b) (hu : u ∈ closedBall c ρ) (hv : v ∈ closedBall c ρ) :
    IsUnit (S u v).det := by
  have := h.det_mul_ne_zero hu hv
  rw [Matrix.det_mul] at this
  exact (right_ne_zero_of_mul this).isUnit

theorem det_Y_ne_zero (h : KrawczykHyp F c ρ Y S e b) (hc : c ∈ closedBall c ρ) : Y.det ≠ 0 := by
  have := h.det_mul_ne_zero hc hc
  rw [Matrix.det_mul] at this
  exact left_ne_zero_of_mul this

/-- For `n ≥ 1` the hypotheses force `0 < ρ`. -/
theorem rho_pos [NeZero n] (h : KrawczykHyp F c ρ Y S e b) : 0 < ρ := by
  have h1 := h.incl 0
  have h2 := (norm_nonneg _).trans (h.hb 0)
  have h3 := h.contr 0
  nlinarith

theorem center_mem [NeZero n] (h : KrawczykHyp F c ρ Y S e b) : c ∈ closedBall c ρ :=
  mem_closedBall_self h.rho_pos.le

/-- **`Y` is invertible** (for every `n`; for `n = 0` trivially). -/
theorem isUnit_det_Y (h : KrawczykHyp F c ρ Y S e b) : IsUnit Y.det := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Matrix.det_isEmpty]
    exact isUnit_one
  · have : NeZero n := ⟨hn.ne'⟩
    exact (h.det_Y_ne_zero h.center_mem).isUnit

/-- The fixed points of `T` are the zeros of `F`. -/
theorem kmap_eq_self_iff (h : KrawczykHyp F c ρ Y S e b) (hc : c ∈ closedBall c ρ) (w : Fin n → 𝕜) :
    kmap Y F w = w ↔ F w = 0 := by
  rw [kmap, sub_eq_self]
  refine ⟨fun hw => ?_, fun hw => by rw [hw, Matrix.mulVec_zero]⟩
  by_contra hne
  exact h.det_Y_ne_zero hc (Matrix.exists_mulVec_eq_zero_iff.mp ⟨F w, hne, hw⟩)

end KrawczykHyp

/-! ## The test -/

/-- **The Krawczyk test**, given that the center lies in the box (automatic for `n ≥ 1`): `F` has exactly one zero in
the box. -/
theorem krawczyk_of_mem (h : KrawczykHyp F c ρ Y S e b) (hc : c ∈ closedBall c ρ) :
    ∃! u, u ∈ closedBall c ρ ∧ F u = 0 := by
  have hρ : 0 ≤ ρ := dist_nonneg.trans (mem_closedBall.mp hc)
  have hq := qc_lt_one h.contr
  have hT : ∀ u ∈ closedBall c ρ, ∀ v ∈ closedBall c ρ,
      dist (kmap Y F u) (kmap Y F v) ≤ qc e * dist u v := by
    intro u hu v hv
    rw [dist_eq_norm, dist_eq_norm, h.kmap_sub hu hv]
    exact h.norm_mulVec_le hu hv (u - v)
  have hmaps : ∀ u ∈ closedBall c ρ, kmap Y F u ∈ closedBall c ρ := by
    intro u hu
    have hu' : ‖u - c‖ ≤ ρ := mem_closedBall_iff_norm.mp hu
    rw [mem_closedBall_iff_norm, h.kmap_sub_center hu hc]
    refine (pi_norm_le_iff_of_nonneg hρ).mpr fun i => ?_
    rw [Pi.sub_apply]
    have hs : 0 ≤ ∑ j, e i j := Finset.sum_nonneg fun j _ => h.e_nonneg hc i j
    calc ‖((1 : Matrix (Fin n) (Fin n) 𝕜) - Y * S u c).mulVec (u - c) i - Y.mulVec (F c) i‖
        ≤ ‖((1 : Matrix (Fin n) (Fin n) 𝕜) - Y * S u c).mulVec (u - c) i‖ + ‖Y.mulVec (F c) i‖ :=
          norm_sub_le _ _
      _ ≤ (∑ j, e i j) * ‖u - c‖ + b i :=
          add_le_add (norm_mulVec_apply_le_of_le (h.hE u hu c hc) _ i) (h.hb i)
      _ ≤ ρ := by linarith [mul_le_mul_of_nonneg_left hu' hs, h.incl i]
  have : CompleteSpace (closedBall c ρ) := isClosed_closedBall.isComplete.completeSpace_coe
  let Tb : closedBall c ρ → closedBall c ρ := fun u => ⟨kmap Y F u, hmaps u u.2⟩
  have hK : ContractingWith (qc e) Tb := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq]
    exact hT u u.2 v v.2
  obtain ⟨u, hu, -⟩ := hK.exists_fixedPoint ⟨c, hc⟩ (edist_ne_top _ _)
  have hfix : kmap Y F u = u := congrArg Subtype.val hu
  refine ⟨u, ⟨u.2, (h.kmap_eq_self_iff hc u).mp hfix⟩, ?_⟩
  rintro v ⟨hv, hFv⟩
  have hd := hT v hv u u.2
  rw [(h.kmap_eq_self_iff hc v).mpr hFv, hfix] at hd
  exact dist_eq_zero.mp (eq_zero_of_le_mul_of_lt_one hq dist_nonneg hd)

/-- **The Krawczyk test** (`n ≥ 1`): `F` has exactly one zero in the box `closedBall c ρ`. -/
theorem krawczyk [NeZero n] (h : KrawczykHyp F c ρ Y S e b) : ∃! u, u ∈ Metric.closedBall c ρ ∧ F u = 0 :=
  krawczyk_of_mem h h.center_mem

/-- **The zero is nonsingular** (`n ≥ 1`): the zero `z` of `F` in the box has an invertible `S z z` (the Jacobian of `F`
at `z` when `S u u = DF(u)`), and it is the only zero in the box. -/
theorem krawczyk_jacobian [NeZero n] (h : KrawczykHyp F c ρ Y S e b) :
    ∃ z ∈ closedBall c ρ, F z = 0 ∧ IsUnit (S z z).det ∧ ∀ w ∈ closedBall c ρ, F w = 0 → w = z := by
  obtain ⟨z, ⟨hz, hFz⟩, huniq⟩ := krawczyk h
  exact ⟨z, hz, hFz, h.isUnit_det_S hz hz, fun w hw hFw => huniq w ⟨hw, hFw⟩⟩

end Lean6.Special.Ball
