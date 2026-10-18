import Mathlib

/-!
# Computations inside the hand proofs of Section 2

For any finite set `ι` of bodies (the paper has six) and any commutative ring, with `Z_kl = p_kl³ (z_k − z_l)` (`Zf`)
and symmetric `p`:

* §2.1: `body_eq_of_rows`: the rows `F_k(u) = F_o(u)` with `z_k = u_k − F_o(u)` give the equations of the bodies (2.2)
  and `z_k − z_l = u_k − u_l`.
* §2.3, the identities on `X_m`: `subset_sum` (subset sums), `torque_zero` (`T_J = 0`), `partial_virial` (partial virials,
  doubled, in any characteristic; `partial_virial_half`: as printed, with the sum over `k < l`, when `2` is invertible),
  `difference` (differences), `mass_sum_zero` (`Σ_k m_k z_k = 0`), `U_eq_sum` (`U = Σ_k m_k z_k w_k`), `sep_sum_algebra`
  and `sep_sum` (`Σ_{k<l} m_k m_l z_kl w_kl = M U`).
* Lemma 2.3(a) (`lem:U`): `lemma_2_3_a`.
* Lemmas 2.2 and 2.9(b): `rows_swap_D`, `rows_swap_Z`, `F_smul`, `rows_rotate`, `iota_slice`, `iota_invol`, `iota_rows`,
  `z_iota`, `w_iota`.
* Lemma 2.8 (the consequences printed in (O1), (O3)) and the exponent arithmetic of the proof of Lemma 2.11: `O1_bounds`,
  `O3_zstroke`, `edgeF`, `edgeF_strictAnti`, `omega_eq_edgeF`, `zstroke_kind`, `wstroke_kind`, `zwedge_kind`,
  `edgeF_gt_one_iff`, `edgeF_lt_one_iff`, `E2_arith`, `E3_arith`, `E6_arith`, `C2_arith`, `C4_arith`.
* Corollary 2.4 (the remark after it): `fibre_bound`.
-/

namespace Lean6.Special.Hand

open Finset

section Antisymm

variable {ι R : Type*} [CommRing R]

/-- A double sum over `J × J` of a function that is antisymmetric with zero diagonal vanishes (in any
characteristic). -/
theorem sum_sum_antisymm (J : Finset ι) (f : ι → ι → R) (hf : ∀ k l, f l k = -f k l) (hd : ∀ k, f k k = 0) :
    ∑ k ∈ J, ∑ l ∈ J, f k l = 0 := by
  rw [← Finset.sum_product' J J f]
  refine Finset.sum_involution (fun a _ => (a.2, a.1)) ?_ ?_ ?_ ?_
  · intro a _
    show f a.1 a.2 + f a.2 a.1 = 0
    rw [hf a.1 a.2, add_neg_cancel]
  · intro a _ hne heq
    apply hne
    have h1 : a.2 = a.1 := congrArg Prod.fst heq
    rw [h1]
    exact hd a.1
  · intro a ha
    simp only [Finset.mem_product] at ha ⊢
    exact ⟨ha.2, ha.1⟩
  · intro a _
    rfl

/-- Ordered pairs of distinct elements against pairs `k < l`. -/
theorem sum_erase_eq_sum_lt [DecidableEq ι] [LinearOrder ι] (J : Finset ι) (f : ι → ι → R) :
    ∑ k ∈ J, ∑ l ∈ J.erase k, f k l = ∑ k ∈ J, ∑ l ∈ J.filter (k < ·), (f k l + f l k) := by
  have h1 : ∀ k ∈ J, ∑ l ∈ J.erase k, f k l =
      ∑ l ∈ J.filter (· < k), f k l + ∑ l ∈ J.filter (k < ·), f k l := by
    intro k _
    rw [← Finset.sum_filter_add_sum_filter_not (J.erase k) (· < k)]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext l
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hl⟩, hlt⟩
        exact ⟨hl, hlt⟩
      · rintro ⟨hl, hlt⟩
        exact ⟨⟨ne_of_lt hlt, hl⟩, hlt⟩
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext l
      simp only [Finset.mem_filter, Finset.mem_erase, not_lt]
      constructor
      · rintro ⟨⟨hne, hl⟩, hle⟩
        exact ⟨hl, lt_of_le_of_ne hle (Ne.symm hne)⟩
      · rintro ⟨hl, hlt⟩
        exact ⟨⟨ne_of_gt hlt, hl⟩, le_of_lt hlt⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have h2 : ∑ k ∈ J, ∑ l ∈ J.filter (· < k), f k l = ∑ l ∈ J, ∑ k ∈ J.filter (l < ·), f k l :=
    Finset.sum_comm' (fun k l => by simp only [Finset.mem_filter]; tauto)
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Antisymm

section Bodies

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- `Z_kl = p_kl³ (z_k − z_l)` (and `W_kl` with `w`). -/
def Zf (p : ι → ι → R) (z : ι → R) (k l : ι) : R := p k l ^ 3 * (z k - z l)

/-- The equations of the bodies (2.2) in one colour: `z_k = Σ_{l ≠ k} m_l Z_kl`. -/
def BodyEqs (m : ι → R) (p : ι → ι → R) (z : ι → R) : Prop :=
  ∀ k, z k = ∑ l ∈ univ.erase k, m l * Zf p z k l

/-- The distance equations `p_kl² z_kl w_kl = 1` for `k ≠ l`. -/
def DistEqs (p : ι → ι → R) (z w : ι → R) : Prop :=
  ∀ k l, k ≠ l → p k l ^ 2 * (z k - z l) * (w k - w l) = 1

/-- `F_k(h) = h_k − Σ_{l ≠ k} m_l p_kl³ (h_k − h_l)` (§2.1). -/
def Fk (m : ι → R) (p : ι → ι → R) (h : ι → R) (k : ι) : R := h k - ∑ l ∈ univ.erase k, m l * Zf p h k l

omit [Fintype ι] [DecidableEq ι] in
theorem Zf_self (p : ι → ι → R) (z : ι → R) (k : ι) : Zf p z k k = 0 := by simp [Zf]

omit [Fintype ι] [DecidableEq ι] in
theorem Zf_antisymm (p : ι → ι → R) (hp : ∀ k l, p k l = p l k) (z : ι → R) (k l : ι) :
    Zf p z l k = -Zf p z k l := by
  unfold Zf
  rw [hp l k]
  ring

theorem body_univ {m : ι → R} {p : ι → ι → R} {z : ι → R} (hz : BodyEqs m p z) (k : ι) :
    z k = ∑ l, m l * Zf p z k l := by
  rw [hz k]
  exact Finset.sum_erase univ (by rw [Zf_self, mul_zero])

/-- **§2.1**: the rows `Z_k = F_k(u) − F_o(u) = 0` and `z_k = u_k − F_o(u)` give `z_k − z_l = u_k − u_l` and the
equations of the bodies (2.2). -/
theorem body_eq_of_rows (m : ι → R) (p : ι → ι → R) (u : ι → R) (o : ι) (hrows : ∀ k, Fk m p u k = Fk m p u o) :
    (∀ k l, (u k - Fk m p u o) - (u l - Fk m p u o) = u k - u l) ∧ BodyEqs m p (fun k => u k - Fk m p u o) := by
  refine ⟨fun k l => by ring, fun k => ?_⟩
  have hZ : ∀ l, Zf p (fun k => u k - Fk m p u o) k l = Zf p u k l := fun l => by unfold Zf; ring
  simp only [hZ]
  have := hrows k
  unfold Fk at this ⊢
  linear_combination this

variable (m : ι → R) (p : ι → ι → R) (hp : ∀ k l, p k l = p l k) (z w : ι → R)
include hp

/-- **Subset sums** (§2.3): `Σ_{k∈J} m_k z_k = Σ_{k∈J, l∉J} m_k m_l Z_kl`. -/
theorem subset_sum (hz : BodyEqs m p z) (J : Finset ι) :
    ∑ k ∈ J, m k * z k = ∑ k ∈ J, ∑ l ∈ univ \ J, m k * m l * Zf p z k l := by
  have h1 : ∀ k, m k * z k = ∑ l, m k * m l * Zf p z k l := by
    intro k
    rw [body_univ hz k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  calc ∑ k ∈ J, m k * z k = ∑ k ∈ J, ∑ l, m k * m l * Zf p z k l := Finset.sum_congr rfl fun k _ => h1 k
    _ = ∑ k ∈ J, (∑ l ∈ univ \ J, m k * m l * Zf p z k l + ∑ l ∈ J, m k * m l * Zf p z k l) :=
        Finset.sum_congr rfl fun k _ => (Finset.sum_sdiff (Finset.subset_univ J)).symm
    _ = ∑ k ∈ J, ∑ l ∈ univ \ J, m k * m l * Zf p z k l + ∑ k ∈ J, ∑ l ∈ J, m k * m l * Zf p z k l :=
        Finset.sum_add_distrib
    _ = ∑ k ∈ J, ∑ l ∈ univ \ J, m k * m l * Zf p z k l := by
        rw [sum_sum_antisymm J _ (fun k l => by rw [Zf_antisymm p hp z k l]; ring)
          (fun k => by rw [Zf_self, mul_zero]), add_zero]

/-- `Σ_k m_k z_k = 0` (§2.1, the subset sum of all bodies). -/
theorem mass_sum_zero (hz : BodyEqs m p z) : ∑ k, m k * z k = 0 := by
  rw [subset_sum m p hp z hz univ]
  simp

/-- **Torques** (§2.3): `T_J = Σ_{k∈J, l∉J} m_k m_l p_kl³ (z_k w_l − z_l w_k) = 0`. -/
theorem torque_zero (hz : BodyEqs m p z) (hw : BodyEqs m p w) (J : Finset ι) :
    ∑ k ∈ J, ∑ l ∈ univ \ J, m k * m l * p k l ^ 3 * (z k * w l - z l * w k) = 0 := by
  set f : ι → ι → R := fun k l => m k * m l * p k l ^ 3 * (z k * w l - z l * w k) with hf
  -- `w_k` times the `z`-equation of `k` minus `z_k` times its `w`-equation
  have hk : ∀ k, ∑ l, f k l = 0 := by
    intro k
    have e1 := body_univ hz k
    have e2 := body_univ hw k
    have : ∑ l, f k l = m k * (w k * (∑ l, m l * Zf p z k l) - z k * (∑ l, m l * Zf p w k l)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by simp only [hf, Zf]; ring
    rw [this, ← e1, ← e2]
    ring
  have hJ : ∑ k ∈ J, ∑ l, f k l = 0 := Finset.sum_eq_zero fun k _ => hk k
  have hsplit : ∑ k ∈ J, ∑ l, f k l = ∑ k ∈ J, ∑ l ∈ univ \ J, f k l + ∑ k ∈ J, ∑ l ∈ J, f k l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (Finset.sum_sdiff (Finset.subset_univ J)).symm
  have hanti : ∑ k ∈ J, ∑ l ∈ J, f k l = 0 :=
    sum_sum_antisymm J f (fun k l => by simp only [hf]; rw [hp l k]; ring) (fun k => by simp [hf])
  rw [hsplit, hanti, add_zero] at hJ
  exact hJ

/-- **Partial virials** (§2.3), doubled (any characteristic):
`2 Σ_{k∈J} m_k z_k w_k = Σ_{k∈J} Σ_{l∈J, l≠k} m_k m_l p_kl + Σ_{k∈J, l∉J} m_k m_l p_kl³ (w_k z_kl + z_k w_kl)`. -/
theorem partial_virial (hz : BodyEqs m p z) (hw : BodyEqs m p w) (hd : DistEqs p z w) (J : Finset ι) :
    2 * ∑ k ∈ J, m k * z k * w k =
      ∑ k ∈ J, ∑ l ∈ J.erase k, m k * m l * p k l +
        ∑ k ∈ J, ∑ l ∈ univ \ J, m k * m l * p k l ^ 3 * (w k * (z k - z l) + z k * (w k - w l)) := by
  set g : ι → ι → R := fun k l => m k * m l * p k l ^ 3 * (w k * (z k - z l) + z k * (w k - w l)) with hg
  have hk : ∀ k, 2 * (m k * z k * w k) = ∑ l, g k l := by
    intro k
    have e1 := body_univ hz k
    have e2 := body_univ hw k
    have : ∑ l, g k l = m k * (w k * (∑ l, m l * Zf p z k l) + z k * (∑ l, m l * Zf p w k l)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by simp only [hg, Zf]; ring
    rw [this, ← e1, ← e2]
    ring
  -- the pairs inside `J`
  set h : ι → ι → R := fun k l => m k * m l * p k l ^ 3 * (z k * w k - z l * w l) with hh
  have hgh : ∀ k l, g k l = m k * m l * p k l ^ 3 * ((z k - z l) * (w k - w l)) + h k l := by
    intro k l
    simp only [hg, hh]
    ring
  have hin : ∑ k ∈ J, ∑ l ∈ J, g k l = ∑ k ∈ J, ∑ l ∈ J.erase k, m k * m l * p k l := by
    have hanti : ∑ k ∈ J, ∑ l ∈ J, h k l = 0 :=
      sum_sum_antisymm J h (fun k l => by simp only [hh]; rw [hp l k]; ring) (fun k => by simp [hh])
    have e : ∑ k ∈ J, ∑ l ∈ J, g k l =
        ∑ k ∈ J, ∑ l ∈ J, m k * m l * p k l ^ 3 * ((z k - z l) * (w k - w l)) + ∑ k ∈ J, ∑ l ∈ J, h k l := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => hgh k l
    rw [e, hanti, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.sum_erase_add J _ hk]
    simp only [sub_self, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hne : k ≠ l := (Finset.ne_of_mem_erase hl).symm
    have := hd k l hne
    calc m k * m l * p k l ^ 3 * ((z k - z l) * (w k - w l))
        = m k * m l * p k l * (p k l ^ 2 * (z k - z l) * (w k - w l)) := by ring
      _ = m k * m l * p k l := by rw [this, mul_one]
  calc 2 * ∑ k ∈ J, m k * z k * w k = ∑ k ∈ J, ∑ l, g k l := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hk k
    _ = ∑ k ∈ J, ∑ l ∈ J, g k l + ∑ k ∈ J, ∑ l ∈ univ \ J, g k l := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [add_comm]
        exact (Finset.sum_sdiff (Finset.subset_univ J)).symm
    _ = _ := by rw [hin]

omit hp in
/-- **Differences** (§2.3): `z_kl = Σ_{j≠k} m_j Z_kj − Σ_{j≠l} m_j Z_lj`. -/
theorem difference (hz : BodyEqs m p z) (k l : ι) :
    z k - z l = ∑ j ∈ univ.erase k, m j * Zf p z k j - ∑ j ∈ univ.erase l, m j * Zf p z l j := by
  rw [← hz k, ← hz l]

/-- `U = Σ_{k<l} m_k m_l p_kl` equals `Σ_k m_k z_k w_k` (Lemma 2.3(a), first part; only the `z`-equations and the
distance equations are used, in any characteristic). -/
theorem U_eq_sum [LinearOrder ι] (hz : BodyEqs m p z) (hd : DistEqs p z w) :
    ∑ k, m k * z k * w k = ∑ k, ∑ l ∈ univ.filter (k < ·), m k * m l * p k l := by
  have h1 : ∑ k, m k * z k * w k = ∑ k, ∑ l ∈ univ.erase k, m k * m l * p k l ^ 3 * (z k - z l) * w k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [hz k]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by simp only [Zf]; ring
  rw [h1, sum_erase_eq_sum_lt]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l hl => ?_
  have hkl : k < l := (Finset.mem_filter.mp hl).2
  have := hd k l (ne_of_lt hkl)
  rw [hp l k]
  calc m k * m l * p k l ^ 3 * (z k - z l) * w k + m l * m k * p k l ^ 3 * (z l - z k) * w l
      = m k * m l * p k l * (p k l ^ 2 * (z k - z l) * (w k - w l)) := by ring
    _ = m k * m l * p k l := by rw [this, mul_one]

omit hp in
/-- The algebra behind `Σ_{k<l} m_k m_l z_kl w_kl = M U`: for all `m, z, w`,
`Σ_{k<l} m_k m_l (z_k − z_l)(w_k − w_l) = (Σ m_k) (Σ m_k z_k w_k) − (Σ m_k z_k)(Σ m_k w_k)`. -/
theorem sep_sum_algebra [LinearOrder ι] :
    ∑ k, ∑ l ∈ univ.filter (k < ·), m k * m l * ((z k - z l) * (w k - w l)) =
      (∑ k, m k) * (∑ k, m k * z k * w k) - (∑ k, m k * z k) * (∑ k, m k * w k) := by
  have h1 : ∑ k, ∑ l ∈ univ.filter (k < ·), m k * m l * ((z k - z l) * (w k - w l)) =
      ∑ k, ∑ l ∈ univ.erase k, m k * m l * (z k * w k - z k * w l) := by
    rw [sum_erase_eq_sum_lt]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have h2 : ∀ k, ∑ l ∈ univ.erase k, m k * m l * (z k * w k - z k * w l) =
      ∑ l, m k * m l * (z k * w k - z k * w l) := fun k =>
    Finset.sum_erase univ (by ring)
  rw [h1, Finset.sum_congr rfl fun k _ => h2 k]
  have e1 : (∑ k, m k) * (∑ k, m k * z k * w k) = ∑ k, ∑ l, m k * m l * (z k * w k) := by
    rw [mul_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e2 : (∑ k, m k * z k) * (∑ k, m k * w k) = ∑ k, ∑ l, m k * m l * (z k * w l) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `Σ_{k<l} m_k m_l z_kl w_kl = M U` on `X_m` (§2.3, last line). -/
theorem sep_sum [LinearOrder ι] (hz : BodyEqs m p z) (hd : DistEqs p z w) :
    ∑ k, ∑ l ∈ univ.filter (k < ·), m k * m l * ((z k - z l) * (w k - w l)) =
      (∑ k, m k) * ∑ k, ∑ l ∈ univ.filter (k < ·), m k * m l * p k l := by
  rw [sep_sum_algebra, mass_sum_zero m p hp z hz, zero_mul, sub_zero, U_eq_sum m p hp z w hz hd]

end Bodies

/-- **Lemma 2.3(a)** (`lem:U`): on `X_m`, `U = Σ_k m_k z_k w_k`, and `U = I` if `M ≠ 0`, where
`I = M⁻¹ Σ_{k<l} m_k m_l u_kl v_kl` and `u_kl = z_kl`, `v_kl = w_kl`. -/
theorem lemma_2_3_a {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (m : ι → K) (p : ι → ι → K) (hp : ∀ k l, p k l = p l k) (z w : ι → K)
    (hz : BodyEqs m p z) (hd : DistEqs p z w) :
    (∑ k, ∑ l ∈ univ.filter (k < ·), m k * m l * p k l) = ∑ k, m k * z k * w k ∧
      ((∑ k, m k) ≠ 0 → (∑ k, ∑ l ∈ univ.filter (k < ·), m k * m l * p k l) =
        (∑ k, m k)⁻¹ * ∑ k, ∑ l ∈ univ.filter (k < ·), m k * m l * ((z k - z l) * (w k - w l))) := by
  refine ⟨(U_eq_sum m p hp z w hz hd).symm, fun hM => ?_⟩
  rw [sep_sum m p hp z w hz hd, ← mul_assoc, inv_mul_cancel₀ hM, one_mul]

/-- **Partial virials** as printed (§2.3), when `2` is invertible: `Σ_{k∈J} m_k z_k w_k − Σ_{k<l∈J} m_k m_l p_kl −
½ Σ_{k∈J, l∉J} m_k m_l p_kl³ (w_k z_kl + z_k w_kl) = 0`. -/
theorem partial_virial_half {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (h2 : (2 : K) ≠ 0) (m : ι → K) (p : ι → ι → K) (hp : ∀ k l, p k l = p l k) (z w : ι → K)
    (hz : BodyEqs m p z) (hw : BodyEqs m p w) (hd : DistEqs p z w) (J : Finset ι) :
    ∑ k ∈ J, m k * z k * w k - ∑ k ∈ J, ∑ l ∈ J.filter (k < ·), m k * m l * p k l -
      (1 / 2) * ∑ k ∈ J, ∑ l ∈ univ \ J, m k * m l * p k l ^ 3 * (w k * (z k - z l) + z k * (w k - w l)) = 0 := by
  have hv := partial_virial m p hp z w hz hw hd J
  have hlt : ∑ k ∈ J, ∑ l ∈ J.erase k, m k * m l * p k l = 2 * ∑ k ∈ J, ∑ l ∈ J.filter (k < ·), m k * m l * p k l := by
    rw [sum_erase_eq_sum_lt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hp l k]; ring
  rw [hlt] at hv
  set A := ∑ k ∈ J, m k * z k * w k
  set B := ∑ k ∈ J, ∑ l ∈ J.filter (k < ·), m k * m l * p k l
  set C := ∑ k ∈ J, ∑ l ∈ univ \ J, m k * m l * p k l ^ 3 * (w k * (z k - z l) + z k * (w k - w l))
  have h2' : (2 : K) * (1 / 2) = 1 := mul_one_div_cancel h2
  have key : (2 : K) * (A - B - 1 / 2 * C) = 0 := by linear_combination hv - C * h2'
  exact (mul_eq_zero.mp key).resolve_left h2



/-! ## Lemmas 2.2 and 2.9(b): the exchange of the colours -/

section Exchange

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] (m : ι → K) (p : ι → ι → K)

/-- `F_k` is linear: `F_k(s h) = s F_k(h)`. -/
theorem F_smul (s : K) (h : ι → K) (k : ι) : Fk m p (fun i => s * h i) k = s * Fk m p h k := by
  simp only [Fk, Zf]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

omit [Fintype ι] [DecidableEq ι] in
/-- The row `D_kl = p_kl² u_kl v_kl − 1` is symmetric in `(u, v)`. -/
theorem rows_swap_D (u v : ι → K) (k l : ι) :
    p k l ^ 2 * (v k - v l) * (u k - u l) - 1 = p k l ^ 2 * (u k - u l) * (v k - v l) - 1 := by ring

/-- The rows `Z_k = F_k(u) − F_o(u)` and `W_k = F_k(v) − F_o(v)` are exchanged by `(u, v) ↦ (v, u)` (they are the same
function of `u`, resp. `v`). -/
theorem rows_swap_Z (u v : ι → K) (o k : ι) :
    (fun a _ : ι → K => Fk m p a k - Fk m p a o) v u = (fun _ b : ι → K => Fk m p b k - Fk m p b o) u v := rfl

/-- The rotation `(u, v) ↦ (s u, s⁻¹ v)` multiplies the rows `Z_k` by `s`, the rows `W_k` by `s⁻¹`, and fixes `D_kl`. -/
theorem rows_rotate (s : K) (hs : s ≠ 0) (u v : ι → K) (o k l : ι) :
    Fk m p (fun i => s * u i) k - Fk m p (fun i => s * u i) o = s * (Fk m p u k - Fk m p u o) ∧
      Fk m p (fun i => s⁻¹ * v i) k - Fk m p (fun i => s⁻¹ * v i) o = s⁻¹ * (Fk m p v k - Fk m p v o) ∧
      p k l ^ 2 * (s * u k - s * u l) * (s⁻¹ * v k - s⁻¹ * v l) - 1 = p k l ^ 2 * (u k - u l) * (v k - v l) - 1 := by
  refine ⟨by rw [F_smul, F_smul, mul_sub], by rw [F_smul, F_smul, mul_sub], ?_⟩
  linear_combination (p k l ^ 2 * (u k - u l) * (v k - v l)) * (mul_inv_cancel₀ hs)

/-- `ι(u, v, p) = (v / v₁, v₁ u, p)`, with body `i1` in the role of body 1. -/
def iotaUV (i1 : ι) (u v : ι → K) : (ι → K) × (ι → K) := (fun i => v i / v i1, fun i => v i1 * u i)

omit [Fintype ι] [DecidableEq ι] in
/-- **Lemma 2.2**: `ι` lands in the slice `u₁ = 1`. -/
theorem iota_slice (i1 : ι) (u v : ι → K) (hv : v i1 ≠ 0) : (iotaUV i1 u v).1 i1 = 1 := by
  simp [iotaUV, hv]

omit [Fintype ι] [DecidableEq ι] in
/-- **Lemma 2.2**: `ι` is an involution of the slice `u₁ = 1`. -/
theorem iota_invol (i1 : ι) (u v : ι → K) (hu : u i1 = 1) (hv : v i1 ≠ 0) :
    iotaUV i1 (iotaUV i1 u v).1 (iotaUV i1 u v).2 = (u, v) := by
  ext i
  · simp only [iotaUV, hu, mul_one]
    field_simp
  · simp only [iotaUV, hu, mul_one]
    field_simp

/-- **Lemma 2.2**: the rows at `ι(u, v)` are the rows at `(u, v)`, exchanged and rotated: `Z_k(ι) = W_k / v₁`,
`W_k(ι) = v₁ Z_k`, `D_kl(ι) = D_kl`. So `ι` maps `X_m` to itself. -/
theorem iota_rows (i1 o : ι) (u v : ι → K) (hv : v i1 ≠ 0) (k l : ι) :
    Fk m p (iotaUV i1 u v).1 k - Fk m p (iotaUV i1 u v).1 o = (Fk m p v k - Fk m p v o) / v i1 ∧
      Fk m p (iotaUV i1 u v).2 k - Fk m p (iotaUV i1 u v).2 o = v i1 * (Fk m p u k - Fk m p u o) ∧
      p k l ^ 2 * ((iotaUV i1 u v).1 k - (iotaUV i1 u v).1 l) * ((iotaUV i1 u v).2 k - (iotaUV i1 u v).2 l) - 1 =
        p k l ^ 2 * (u k - u l) * (v k - v l) - 1 := by
  have e1 : (iotaUV i1 u v).1 = fun i => (v i1)⁻¹ * v i := funext fun i => by simp [iotaUV, div_eq_inv_mul]
  have e2 : (iotaUV i1 u v).2 = fun i => v i1 * u i := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, F_smul, F_smul, ← mul_sub, div_eq_inv_mul]
  · rw [e2, F_smul, F_smul, ← mul_sub]
  · simp only [e1, e2]
    linear_combination (p k l ^ 2 * (u k - u l) * (v k - v l)) * (inv_mul_cancel₀ hv)

/-- **Lemma 2.9(b)**: with `z_k = u_k − F_o(u)` and `w_k = v_k − F_o(v)`, `z_k ∘ ι = w_k / v₁` and `w_k ∘ ι = v₁ z_k`. -/
theorem z_iota (i1 o : ι) (u v : ι → K) (k : ι) :
    (iotaUV i1 u v).1 k - Fk m p (iotaUV i1 u v).1 o = (v k - Fk m p v o) / v i1 := by
  have e1 : (iotaUV i1 u v).1 = fun i => (v i1)⁻¹ * v i := funext fun i => by simp [iotaUV, div_eq_inv_mul]
  rw [e1, F_smul, div_eq_inv_mul, mul_sub]

theorem w_iota (i1 o : ι) (u v : ι → K) (k : ι) :
    (iotaUV i1 u v).2 k - Fk m p (iotaUV i1 u v).2 o = v i1 * (u k - Fk m p u o) := by
  have e2 : (iotaUV i1 u v).2 = fun i => v i1 * u i := rfl
  rw [e2, F_smul, mul_sub]

end Exchange

/-! ## Lemma 2.8 and the exponent arithmetic of the proof of Lemma 2.11 -/

section Orders

/-- **(O1), consequences**: from `ζ, ω ≥ −2`, `ζ + 3ω ≤ 4` and `3ζ + ω ≤ 4`: `ζ, ω ≤ 2` and `−2 ≤ x ≤ 1`, with
`x = (ζ + ω)/2`. -/
theorem O1_bounds (ζ ω : ℚ) (hz : -2 ≤ ζ) (hw : -2 ≤ ω) (h1 : ζ + 3 * ω ≤ 4) (h2 : 3 * ζ + ω ≤ 4) :
    ζ ≤ 2 ∧ ω ≤ 2 ∧ -2 ≤ (ζ + ω) / 2 ∧ (ζ + ω) / 2 ≤ 1 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **(O3)**: on a `z`-stroke (`ζ + 3ω = 4`), `ζ = 3x − 2` and `ω = 2 − x`; with (O1), `0 ≤ x ≤ 1`. -/
theorem O3_zstroke (ζ ω : ℚ) (hz : -2 ≤ ζ) (h1 : ζ + 3 * ω = 4) (h2 : 3 * ζ + ω ≤ 4) :
    ζ = 3 * ((ζ + ω) / 2) - 2 ∧ ω = 2 - (ζ + ω) / 2 ∧ 0 ≤ (ζ + ω) / 2 ∧ (ζ + ω) / 2 ≤ 1 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The function `f` of the proof of Lemma 2.11: `f(ζ) = (4 − ζ)/3` for `ζ ≤ 1`, `4 − 3ζ` for `ζ ≥ 1`. -/
def edgeF (ζ : ℚ) : ℚ := if ζ ≤ 1 then (4 - ζ) / 3 else 4 - 3 * ζ

theorem edgeF_strictAnti : StrictAnti edgeF := by
  intro a b hab
  unfold edgeF
  split_ifs <;> linarith

/-- On an edge (a stroke of some colour), `ω = f(ζ)`. -/
theorem omega_eq_edgeF (ζ ω : ℚ) (h1 : ζ + 3 * ω ≤ 4) (h2 : 3 * ζ + ω ≤ 4)
    (he : ζ + 3 * ω = 4 ∨ 3 * ζ + ω = 4) : ω = edgeF ζ := by
  unfold edgeF
  rcases he with he | he
  · have : ζ ≤ 1 := by linarith
    rw [if_pos this]
    linarith
  · by_cases h : ζ ≤ 1
    · rw [if_pos h]
      have : ζ = 1 := by linarith
      subst this
      linarith
    · rw [if_neg h]
      linarith

/-- A `z`-stroke that is not a `zw`-edge has `ζ < 1 < ω`. -/
theorem zstroke_kind (ζ ω : ℚ) (h1 : ζ + 3 * ω = 4) (h2 : 3 * ζ + ω < 4) : ζ < 1 ∧ 1 < ω := by
  constructor <;> linarith

/-- A `w`-stroke that is not a `zw`-edge has `ω < 1 < ζ`. -/
theorem wstroke_kind (ζ ω : ℚ) (h1 : 3 * ζ + ω = 4) (h2 : ζ + 3 * ω < 4) : ω < 1 ∧ 1 < ζ := by
  constructor <;> linarith

/-- On a `zw`-edge, `ζ = ω = 1`. -/
theorem zwedge_kind (ζ ω : ℚ) (h1 : ζ + 3 * ω = 4) (h2 : 3 * ζ + ω = 4) : ζ = 1 ∧ ω = 1 := by
  constructor <;> linarith

theorem edgeF_gt_one_iff (ζ : ℚ) : 1 < edgeF ζ ↔ ζ < 1 := by
  unfold edgeF
  split_ifs with h <;> constructor <;> intro h' <;> linarith

theorem edgeF_lt_one_iff (ζ : ℚ) : edgeF ζ < 1 ↔ 1 < ζ := by
  unfold edgeF
  split_ifs with h <;> constructor <;> intro h' <;> linarith

/-- **(E2)**: if `ζ, ω ≥ 1` (by (O5) in a triangle with two `zw`-edges) and `ζ + 3ω ≤ 4`, then `ζ = ω = 1`, so
`x = 1`. -/
theorem E2_arith (ζ ω : ℚ) (hz : 1 ≤ ζ) (hw : 1 ≤ ω) (h1 : ζ + 3 * ω ≤ 4) : ζ = 1 ∧ ω = 1 := by
  constructor <;> linarith

/-- **(E3)**, last step: `ζ₁ ≤ ζ₃` and `f(ζ₃) ≥ f(ζ₁)` (the minimum of `ω` attained twice) give `ζ₃ = ζ₁`. -/
theorem E3_arith (ζ1 ζ3 : ℚ) (h13 : ζ1 ≤ ζ3) (hω : edgeF ζ1 ≤ edgeF ζ3) : ζ3 = ζ1 := by
  rcases h13.lt_or_eq with h | h
  · exact absurd (edgeF_strictAnti h) (not_lt.mpr hω)
  · exact h.symm

/-- **(E6)**: with `α < β`, `ζ_ac ≥ β` and `ω_ac ≥ f(α)`: if `α < 1` then `ζ_ac + 3ω_ac > 4`, and if `α ≥ 1` then
`3ζ_ac + ω_ac > 4`, against (O1). -/
theorem E6_arith (α β ζ ω : ℚ) (hab : α < β) (hz : β ≤ ζ) (hw : edgeF α ≤ ω) :
    (α < 1 → 4 < ζ + 3 * ω) ∧ (1 ≤ α → 4 < 3 * ζ + ω) := by
  unfold edgeF at hw
  constructor
  · intro h
    rw [if_pos h.le] at hw
    linarith
  · intro h
    by_cases h' : α ≤ 1
    · rw [if_pos h'] at hw
      have : α = 1 := le_antisymm h' h
      subst this
      linarith
    · rw [if_neg h'] at hw
      linarith

/-- **(C2)**: on a `w`-stroke, `ζ ≥ 1 > −2`. -/
theorem C2_arith (ζ ω : ℚ) (h1 : 3 * ζ + ω = 4) (h2 : ζ + 3 * ω ≤ 4) : 1 ≤ ζ ∧ -2 < ζ := by
  constructor <;> linarith

/-- **(C4)**: `ω_kj ≥ 2` (by (O5)) with (O1) gives `ω_kj = 2`, `ζ_kj = −2` and `ζ_kj + 3ω_kj = 4`, so `kj` is a
`z`-stroke by (O2). -/
theorem C4_arith (ζ ω : ℚ) (hz : -2 ≤ ζ) (h1 : ζ + 3 * ω ≤ 4) (h2 : 3 * ζ + ω ≤ 4) (hw : 2 ≤ ω) :
    ω = 2 ∧ ζ = -2 ∧ ζ + 3 * ω = 4 := by
  refine ⟨by linarith, by linarith, by linarith⟩

end Orders

/-- **Corollary 2.4** (the remark after it): on a fibre of `(u, v, p) ↦ (r_kl²)` the coordinates `u₂, …, u₅` are roots
of quadratics and the fifteen `p_kl` are determined up to sign: `2⁴ · 2¹⁵ = 2¹⁹` (and `2³ · 2¹⁰ = 2¹³` for five
bodies). -/
theorem fibre_bound : (2 : ℕ) ^ (6 - 2) * 2 ^ (6 * 5 / 2) = 2 ^ 19 ∧ (2 : ℕ) ^ (5 - 2) * 2 ^ (5 * 4 / 2) = 2 ^ 13 := by
  norm_num

end Lean6.Special.Hand
