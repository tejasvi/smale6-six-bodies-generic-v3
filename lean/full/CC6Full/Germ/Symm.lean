import CC6Full.Germ.Initial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Symmetries of germs

Paper Lemma 2.1 (b) (`lem:slice`), Lemma 2.2 (`lem:exchange`) and Lemma 2.9 (`lem:symm`), for germs.

* `Germ.relabel σ G : Germ n (m ∘ σ)`: body `k` of the new germ is body `σ k` of `G`, that is `z' k = z (σ k)`,
  `w' k = w (σ k)`, `p' k l = p (σ k) (σ l)`, with the same `E`. Its exponents `ζ`, `ω`, `x`, its strokes and its
  circles at `k, l` are those of `G` at `σ k, σ l`, and `ℓ` is unchanged (Lemma 2.9 (a)).
* `Germ.swap G : Germ n m` exchanges the colours: `z' = w`, `w' = z`, with the same `p` and `E`. It exchanges `ζ`
  and `ω`, the `z`- and `w`-strokes and the `z`- and `w`-circles; `x` and `ℓ` are unchanged (Lemma 2.9 (b)). On
  germs the rotation by `v_1` of Lemma 2.2 is not needed.
* `Germ.scale G t ht : Germ n (t • m)` for `t > 0`: `z' = c z`, `w' = c w`, `p' = c⁻¹ p` with `c = t^{1/3}` the real
  cube root (`Germ.cubeRoot t`), and `E' = c⁵ E = t^{5/3} E` (Lemma 2.1 (b)). It is `Germ.scaleBy` for this `c`;
  `Germ.scaleBy` works for any complex `c ≠ 0` with `c³ = t`. A nonzero constant factor does not change orders, so
  `ζ`, `ω`, `x`, `ℓ`, the strokes and the circles are those of `G`.
-/

namespace CC6Full

open Finset

noncomputable section

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ}

/-! ## Relabelling (Lemma 2.1 (b), Lemma 2.9 (a)) -/

/-- Reindexing a sum over `univ.erase k` by a permutation. -/
theorem sum_erase_perm {M : Type*} [AddCommMonoid M] (σ : Equiv.Perm (Fin n)) (k : Fin n)
    (f : Fin n → M) : ∑ l ∈ univ.erase k, f (σ l) = ∑ l ∈ univ.erase (σ k), f l :=
  Finset.sum_equiv σ (fun l => by simp) (fun _ _ => rfl)

/-- Reindexing a sum over the ordered pairs `k ≠ l` by a permutation. -/
theorem sum_sum_erase_perm {M : Type*} [AddCommMonoid M] (σ : Equiv.Perm (Fin n))
    (F : Fin n → Fin n → M) :
    ∑ k, ∑ l ∈ univ.erase k, F (σ k) (σ l) = ∑ k, ∑ l ∈ univ.erase k, F k l := by
  rw [← Equiv.sum_comp σ (fun k => ∑ l ∈ univ.erase k, F k l)]
  exact Finset.sum_congr rfl fun k _ => sum_erase_perm σ k (F (σ k))

theorem lowAt_relabel {p : Fin n → Fin n → Ser} {h : Fin n → Ser} (σ : Equiv.Perm (Fin n))
    (H : LowAt p h) : LowAt (fun k l => p (σ k) (σ l)) (fun k => h (σ k)) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨fun k => h1 (σ k), fun k l hkl => h2 (σ k) (σ l) (σ.injective.ne hkl), ?_⟩
  rcases h3 with ⟨k, hk⟩ | ⟨k, l, hkl, hk⟩
  · refine Or.inl ⟨σ.symm k, ?_⟩
    show (h (σ (σ.symm k))).orderTop = _
    rw [Equiv.apply_symm_apply]
    exact hk
  · refine Or.inr ⟨σ.symm k, σ.symm l, fun he => hkl (by simpa using congrArg σ he), ?_⟩
    show (termZ p h (σ (σ.symm k)) (σ (σ.symm l))).orderTop = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hk

/-- The germ of the relabelled place (Lemma 2.1 (b), Lemma 2.9 (a)), for the masses `m ∘ σ`: body `k` of the new
germ is body `σ k` of `G`. -/
def relabel (σ : Equiv.Perm (Fin n)) (G : Germ n m) : Germ n (m ∘ σ) where
  z k := G.z (σ k)
  w k := G.w (σ k)
  p k l := G.p (σ k) (σ l)
  p_symm k l := G.p_symm (σ k) (σ l)
  body_z k := by
    show G.z (σ k) = _
    rw [G.body_z (σ k), ← sum_erase_perm σ k]
    rfl
  body_w k := by
    show G.w (σ k) = _
    rw [G.body_w (σ k), ← sum_erase_perm σ k]
    rfl
  dist k l h := G.dist (σ k) (σ l) (σ.injective.ne h)
  E := G.E
  E_ne := G.E_ne
  pot := by
    rw [← G.pot]
    exact sum_sum_erase_perm σ (fun k l => cS (m k * m l) * G.p k l)
  low_z := lowAt_relabel σ G.low_z
  low_w := lowAt_relabel σ G.low_w

section relabel

variable (G : Germ n m) (σ : Equiv.Perm (Fin n))

@[simp] theorem relabel_z (k : Fin n) : (G.relabel σ).z k = G.z (σ k) := rfl

@[simp] theorem relabel_w (k : Fin n) : (G.relabel σ).w k = G.w (σ k) := rfl

@[simp] theorem relabel_p (k l : Fin n) : (G.relabel σ).p k l = G.p (σ k) (σ l) := rfl

@[simp] theorem relabel_E : (G.relabel σ).E = G.E := rfl

theorem relabel_termZ_z (k l : Fin n) :
    termZ (G.relabel σ).p (G.relabel σ).z k l = termZ G.p G.z (σ k) (σ l) := rfl

theorem relabel_termZ_w (k l : Fin n) :
    termZ (G.relabel σ).p (G.relabel σ).w k l = termZ G.p G.w (σ k) (σ l) := rfl

@[simp] theorem relabel_zeta (k l : Fin n) : (G.relabel σ).zeta k l = G.zeta (σ k) (σ l) := rfl

@[simp] theorem relabel_omega (k l : Fin n) : (G.relabel σ).omega k l = G.omega (σ k) (σ l) := rfl

@[simp] theorem relabel_x (k l : Fin n) : (G.relabel σ).x k l = G.x (σ k) (σ l) := rfl

@[simp] theorem relabel_ell : (G.relabel σ).ell = G.ell := by
  unfold Germ.ell
  congr 1
  exact sum_sum_erase_perm σ G.x

theorem relabel_zStroke (k l : Fin n) : (G.relabel σ).zStroke k l ↔ G.zStroke (σ k) (σ l) :=
  and_congr σ.injective.ne_iff.symm Iff.rfl

theorem relabel_wStroke (k l : Fin n) : (G.relabel σ).wStroke k l ↔ G.wStroke (σ k) (σ l) :=
  and_congr σ.injective.ne_iff.symm Iff.rfl

theorem relabel_zCircle (k : Fin n) : (G.relabel σ).zCircle k ↔ G.zCircle (σ k) := Iff.rfl

theorem relabel_wCircle (k : Fin n) : (G.relabel σ).wCircle k ↔ G.wCircle (σ k) := Iff.rfl

end relabel

/-! ## Exchange of the colours (Lemma 2.2, Lemma 2.9 (b)) -/

/-- The germ of the image of the place under the involution `ι` of Lemma 2.2: the colours are exchanged. -/
def swap (G : Germ n m) : Germ n m where
  z := G.w
  w := G.z
  p := G.p
  p_symm := G.p_symm
  body_z := G.body_w
  body_w := G.body_z
  dist k l h := by
    rw [mul_right_comm]
    exact G.dist k l h
  E := G.E
  E_ne := G.E_ne
  pot := G.pot
  low_z := G.low_w
  low_w := G.low_z

section swap

variable (G : Germ n m)

@[simp] theorem swap_z (k : Fin n) : G.swap.z k = G.w k := rfl

@[simp] theorem swap_w (k : Fin n) : G.swap.w k = G.z k := rfl

@[simp] theorem swap_p (k l : Fin n) : G.swap.p k l = G.p k l := rfl

@[simp] theorem swap_E : G.swap.E = G.E := rfl

@[simp] theorem swap_swap : G.swap.swap = G := rfl

theorem swap_termZ_z (k l : Fin n) : termZ G.swap.p G.swap.z k l = termZ G.p G.w k l := rfl

theorem swap_termZ_w (k l : Fin n) : termZ G.swap.p G.swap.w k l = termZ G.p G.z k l := rfl

@[simp] theorem swap_zeta (k l : Fin n) : G.swap.zeta k l = G.omega k l := rfl

@[simp] theorem swap_omega (k l : Fin n) : G.swap.omega k l = G.zeta k l := rfl

@[simp] theorem swap_x (k l : Fin n) : G.swap.x k l = G.x k l := rfl

@[simp] theorem swap_ell : G.swap.ell = G.ell := rfl

theorem swap_zStroke (k l : Fin n) : G.swap.zStroke k l ↔ G.wStroke k l := Iff.rfl

theorem swap_wStroke (k l : Fin n) : G.swap.wStroke k l ↔ G.zStroke k l := Iff.rfl

theorem swap_zCircle (k : Fin n) : G.swap.zCircle k ↔ G.wCircle k := Iff.rfl

theorem swap_wCircle (k : Fin n) : G.swap.wCircle k ↔ G.zCircle k := Iff.rfl

end swap

/-! ## Scaling of the masses (Lemma 2.1 (b)) -/

/-- The real cube root `t^{1/3}` of `t`, as a complex number. -/
def cubeRoot (t : ℝ) : ℂ := ((t ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ)

theorem cubeRoot_pow_three {t : ℝ} (ht : 0 ≤ t) : cubeRoot t ^ 3 = t := by
  rw [cubeRoot, ← Complex.ofReal_pow]
  congr 1
  simpa using Real.rpow_inv_natCast_pow ht (n := 3) (by norm_num)

theorem cubeRoot_ne_zero {t : ℝ} (ht : 0 < t) : cubeRoot t ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne'

/-- `c⁵ = t^{5/3}` for `c = t^{1/3}`. -/
theorem cubeRoot_pow_five {t : ℝ} (ht : 0 ≤ t) : cubeRoot t ^ 5 = ((t ^ ((5 : ℝ) / 3) : ℝ) : ℂ) := by
  rw [cubeRoot, ← Complex.ofReal_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

/-- `Z_kl` of the scaled series: `(c⁻¹ p)³ (c h_k − c h_l) = c⁻³ c Z_kl`. -/
theorem termZ_scale (c : ℂ) (p : Fin n → Fin n → Ser) (h : Fin n → Ser) (k l : Fin n) :
    termZ (fun k l => cS c⁻¹ * p k l) (fun k => cS c * h k) k l = cS (c⁻¹ ^ 3 * c) * termZ p h k l := by
  simp only [termZ, cS_mul, cS_pow]
  ring

theorem scale_body {c : ℂ} (hc : c ≠ 0) {t : ℝ} (hct : c ^ 3 = t) {p : Fin n → Fin n → Ser}
    {h : Fin n → Ser} (hb : ∀ k, h k = ∑ l ∈ univ.erase k, cS (m l) * termZ p h k l) (k : Fin n) :
    cS c * h k = ∑ l ∈ univ.erase k,
      cS ((t • m) l) * termZ (fun k l => cS c⁻¹ * p k l) (fun k => cS c * h k) k l := by
  have h2 := cS_inv_mul_cancel hc
  have key : ∀ l, cS ((t • m) l) * termZ (fun k l => cS c⁻¹ * p k l) (fun k => cS c * h k) k l =
      cS c * (cS (m l) * termZ p h k l) := by
    intro l
    have h3 : cS ((t • m) l) = cS c ^ 3 * cS (m l) := by
      rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, cS_mul, ← hct, cS_pow]
    rw [h3]
    simp only [termZ]
    linear_combination (cS c * cS (m l) * p k l ^ 3 * (h k - h l) *
      ((cS c⁻¹ * cS c) ^ 2 + cS c⁻¹ * cS c + 1)) * h2
  rw [Finset.sum_congr rfl fun l _ => key l, ← Finset.mul_sum, ← hb k]

theorem lowAt_scale {c : ℂ} (hc : c ≠ 0) {p : Fin n → Fin n → Ser} {h : Fin n → Ser}
    (H : LowAt p h) : LowAt (fun k l => cS c⁻¹ * p k l) (fun k => cS c * h k) := by
  have hc' : c⁻¹ ^ 3 * c ≠ 0 := mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) hc
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨fun k => ?_, fun k l hkl => ?_, ?_⟩
  · show _ ≤ (cS c * h k).orderTop
    rw [Ser.orderTop_cS_mul hc]
    exact h1 k
  · rw [termZ_scale, Ser.orderTop_cS_mul hc']
    exact h2 k l hkl
  · rcases h3 with ⟨k, hk⟩ | ⟨k, l, hkl, hk⟩
    · refine Or.inl ⟨k, ?_⟩
      show (cS c * h k).orderTop = _
      rw [Ser.orderTop_cS_mul hc]
      exact hk
    · refine Or.inr ⟨k, l, hkl, ?_⟩
      rw [termZ_scale, Ser.orderTop_cS_mul hc']
      exact hk

/-- The germ for the masses `t • m`, for any `c ≠ 0` with `c³ = t`: `z' = c z`, `w' = c w`, `p' = c⁻¹ p`,
`E' = c⁵ E`. -/
def scaleBy (G : Germ n m) (c : ℂ) (hc : c ≠ 0) (t : ℝ) (hct : c ^ 3 = t) : Germ n (t • m) where
  z k := cS c * G.z k
  w k := cS c * G.w k
  p k l := cS c⁻¹ * G.p k l
  p_symm k l := by rw [G.p_symm]
  body_z := scale_body hc hct G.body_z
  body_w := scale_body hc hct G.body_w
  dist k l hkl := by
    have h2 := cS_inv_mul_cancel hc
    have hd := G.dist k l hkl
    show (cS c⁻¹ * G.p k l) ^ 2 * (cS c * G.z k - cS c * G.z l) * (cS c * G.w k - cS c * G.w l) = 1
    linear_combination (cS c⁻¹ * cS c) ^ 2 * hd + (cS c⁻¹ * cS c + 1) * h2
  E := c ^ 5 * G.E
  E_ne := mul_ne_zero (pow_ne_zero _ hc) G.E_ne
  pot := by
    have h2 := cS_inv_mul_cancel hc
    have ht3 : cS (t : ℂ) = cS c ^ 3 := by rw [← cS_pow, hct]
    have key : ∀ k l, cS ((t • m) k * (t • m) l) * (cS c⁻¹ * G.p k l) =
        cS (c ^ 5) * (cS (m k * m l) * G.p k l) := by
      intro k l
      simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, cS_mul, cS_pow, ht3]
      linear_combination cS c ^ 5 * cS (m k) * cS (m l) * G.p k l * h2
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => key k l]
    simp_rw [← Finset.mul_sum]
    rw [G.pot, ← cS_mul]
    congr 1
    ring
  low_z := lowAt_scale hc G.low_z
  low_w := lowAt_scale hc G.low_w

/-- The germ for the masses `t • m`, `t > 0` (Lemma 2.1 (b)): `z' = c z`, `w' = c w`, `p' = c⁻¹ p` with the real
cube root `c = t^{1/3}`, and `E' = c⁵ E = t^{5/3} E` (`cubeRoot_pow_five`). -/
def scale (G : Germ n m) (t : ℝ) (ht : 0 < t) : Germ n (t • m) :=
  G.scaleBy (cubeRoot t) (cubeRoot_ne_zero ht) t (cubeRoot_pow_three ht.le)

section scale

variable (G : Germ n m) (c : ℂ) (hc : c ≠ 0) (t : ℝ) (hct : c ^ 3 = t)

@[simp] theorem scaleBy_z (k : Fin n) : (G.scaleBy c hc t hct).z k = cS c * G.z k := rfl

@[simp] theorem scaleBy_w (k : Fin n) : (G.scaleBy c hc t hct).w k = cS c * G.w k := rfl

@[simp] theorem scaleBy_p (k l : Fin n) : (G.scaleBy c hc t hct).p k l = cS c⁻¹ * G.p k l := rfl

@[simp] theorem scaleBy_E : (G.scaleBy c hc t hct).E = c ^ 5 * G.E := rfl

theorem scaleBy_termZ_z (k l : Fin n) :
    termZ (G.scaleBy c hc t hct).p (G.scaleBy c hc t hct).z k l = cS (c⁻¹ ^ 3 * c) * termZ G.p G.z k l :=
  termZ_scale c G.p G.z k l

theorem scaleBy_termZ_w (k l : Fin n) :
    termZ (G.scaleBy c hc t hct).p (G.scaleBy c hc t hct).w k l = cS (c⁻¹ ^ 3 * c) * termZ G.p G.w k l :=
  termZ_scale c G.p G.w k l

@[simp] theorem scaleBy_zeta (k l : Fin n) : (G.scaleBy c hc t hct).zeta k l = G.zeta k l := by
  show (cS c * G.z k - cS c * G.z l).order = (G.z k - G.z l).order
  rw [← mul_sub, Ser.order_cS_mul hc]

@[simp] theorem scaleBy_omega (k l : Fin n) : (G.scaleBy c hc t hct).omega k l = G.omega k l := by
  show (cS c * G.w k - cS c * G.w l).order = (G.w k - G.w l).order
  rw [← mul_sub, Ser.order_cS_mul hc]

@[simp] theorem scaleBy_x (k l : Fin n) : (G.scaleBy c hc t hct).x k l = G.x k l := by
  show -(cS c⁻¹ * G.p k l).order = -(G.p k l).order
  rw [Ser.order_cS_mul (inv_ne_zero hc)]

@[simp] theorem scaleBy_ell : (G.scaleBy c hc t hct).ell = G.ell := by
  unfold Germ.ell
  simp only [scaleBy_x]

theorem scaleBy_zStroke (k l : Fin n) : (G.scaleBy c hc t hct).zStroke k l ↔ G.zStroke k l := by
  unfold Germ.zStroke
  rw [scaleBy_termZ_z, Ser.orderTop_cS_mul (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) hc)]

theorem scaleBy_wStroke (k l : Fin n) : (G.scaleBy c hc t hct).wStroke k l ↔ G.wStroke k l := by
  unfold Germ.wStroke
  rw [scaleBy_termZ_w, Ser.orderTop_cS_mul (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) hc)]

theorem scaleBy_zCircle (k : Fin n) : (G.scaleBy c hc t hct).zCircle k ↔ G.zCircle k := by
  unfold Germ.zCircle
  rw [scaleBy_z, Ser.orderTop_cS_mul hc]

theorem scaleBy_wCircle (k : Fin n) : (G.scaleBy c hc t hct).wCircle k ↔ G.wCircle k := by
  unfold Germ.wCircle
  rw [scaleBy_w, Ser.orderTop_cS_mul hc]

end scale

section scale

variable (G : Germ n m) (t : ℝ) (ht : 0 < t)

@[simp] theorem scale_z (k : Fin n) : (G.scale t ht).z k = cS (cubeRoot t) * G.z k := rfl

@[simp] theorem scale_w (k : Fin n) : (G.scale t ht).w k = cS (cubeRoot t) * G.w k := rfl

@[simp] theorem scale_p (k l : Fin n) : (G.scale t ht).p k l = cS (cubeRoot t)⁻¹ * G.p k l := rfl

@[simp] theorem scale_E : (G.scale t ht).E = cubeRoot t ^ 5 * G.E := rfl

theorem scale_E' : (G.scale t ht).E = ((t ^ ((5 : ℝ) / 3) : ℝ) : ℂ) * G.E := by
  rw [scale_E, cubeRoot_pow_five ht.le]

@[simp] theorem scale_zeta (k l : Fin n) : (G.scale t ht).zeta k l = G.zeta k l := scaleBy_zeta _ _ _ _ _ k l

@[simp] theorem scale_omega (k l : Fin n) : (G.scale t ht).omega k l = G.omega k l :=
  scaleBy_omega _ _ _ _ _ k l

@[simp] theorem scale_x (k l : Fin n) : (G.scale t ht).x k l = G.x k l := scaleBy_x _ _ _ _ _ k l

@[simp] theorem scale_ell : (G.scale t ht).ell = G.ell := scaleBy_ell _ _ _ _ _

theorem scale_zStroke (k l : Fin n) : (G.scale t ht).zStroke k l ↔ G.zStroke k l :=
  scaleBy_zStroke _ _ _ _ _ k l

theorem scale_wStroke (k l : Fin n) : (G.scale t ht).wStroke k l ↔ G.wStroke k l :=
  scaleBy_wStroke _ _ _ _ _ k l

theorem scale_zCircle (k : Fin n) : (G.scale t ht).zCircle k ↔ G.zCircle k := scaleBy_zCircle _ _ _ _ _ k

theorem scale_wCircle (k : Fin n) : (G.scale t ht).wCircle k ↔ G.wCircle k := scaleBy_wCircle _ _ _ _ _ k

end scale

end Germ

end

end CC6Full
