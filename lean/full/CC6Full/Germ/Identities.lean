import CC6Full.Germ.Initial

/-!
# The identities of §2.3 (`ss:identities`)

For every germ `G : Germ n m`, as equalities in `Ser` with the masses as constants `cS (m k)`; `J` is a set of
bodies, `Jᶜ` its complement, `M = Σ_k m_k`, `Z_kl = termZ G.p G.z k l = p_kl³ z_kl`, `W_kl = termZ G.p G.w k l`,
`z_kl = z_k − z_l`, `w_kl = w_k − w_l`. The paper's names:

* centre of mass: `Σ_k m_k z_k = 0`, `Σ_k m_k w_k = 0` (`com_z`, `com_w`);
* *subset sums*: `Σ_{k∈J} m_k z_k = Σ_{k∈J, l∈Jᶜ} m_k m_l Z_kl`, and the same in `w` (`subsetSum_z`,
  `subsetSum_w`); for `J = {k}` this is the equation of the body `k`;
* *torques*: `T_J = Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ (z_k w_l − z_l w_k) = 0` (`torque`; `torque_body` for one body
  and all `l`);
* *partial virials*:
  `Σ_{k∈J} m_k z_k w_k − Σ_{k<l ∈ J} m_k m_l p_kl − ½ Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ (w_k z_kl + z_k w_kl) = 0`
  (`partialVirial`; `partialVirial_two` is twice it, with the sum over the ordered pairs `k ≠ l` of `J`);
* *differences*: `z_kl = Σ_{j≠k} m_j Z_kj − Σ_{j≠l} m_j Z_lj`, and the same in `w` (`difference_z`,
  `difference_w`);
* `U = Σ_k m_k z_k w_k` (`U_eq_virial`), where `U = Σ_{k<l} m_k m_l p_kl = E` (`U_eq`, from `pot`), so
  `Σ_k m_k z_k w_k = E` (`virial`); `Σ_{k<l} m_k m_l z_kl w_kl = M E` (`lagrange`, Lagrange's identity with the
  centre of mass, `M U` in the paper; `lagrange_ordered` over ordered pairs); `p_kl³ z_kl w_kl = p_kl`
  (`p_cube_mul`) and `p_kl² z_kl w_kl = 1` (the field `dist`).

The proofs are those of the paper: ring manipulations of the equations of the bodies, `dist` and `pot`, in which the
terms of the pairs inside `J` cancel because they are antisymmetric (`sum_sum_sub_swap`,
`sum_sum_mul_sub_of_symm'`). Sums over `k < l` are converted to sums over ordered pairs by
`sum_sum_erase_eq_two_mul`.
-/

namespace CC6Full

open Finset

noncomputable section

/-! ## Double sums -/

section sums

variable {ι R : Type*}

/-- An antisymmetric double sum vanishes: `Σ_{i,j ∈ s} (F i j − F j i) = 0`. -/
theorem sum_sum_sub_swap [AddCommGroup R] (s : Finset ι) (F : ι → ι → R) :
    ∑ i ∈ s, ∑ j ∈ s, (F i j - F j i) = 0 := by
  have h : ∑ i ∈ s, ∑ j ∈ s, F j i = ∑ i ∈ s, ∑ j ∈ s, F i j := Finset.sum_comm
  simp only [Finset.sum_sub_distrib, h, sub_self]

/-- `Σ_{i,j ∈ s} b_ij (x_i − x_j) = 0` for a symmetric kernel `b`. -/
theorem sum_sum_mul_sub_of_symm' [CommRing R] (s : Finset ι) {b : ι → ι → R}
    (hb : ∀ i j, b i j = b j i) (x : ι → R) : ∑ i ∈ s, ∑ j ∈ s, b i j * (x i - x j) = 0 := by
  refine Eq.trans ?_ (sum_sum_sub_swap s fun i j => b i j * x i)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hb j i]
  ring

/-- Splitting the inner sum over all `l` into `l ∈ J` and `l ∈ Jᶜ`. -/
theorem sum_univ_split [Fintype ι] [DecidableEq ι] [AddCommMonoid R] (J : Finset ι) (T : ι → ι → R) :
    ∑ k ∈ J, ∑ l, T k l = ∑ k ∈ J, ∑ l ∈ J, T k l + ∑ k ∈ J, ∑ l ∈ Jᶜ, T k l := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => (Finset.sum_add_sum_compl J _).symm

/-- For a symmetric `S`, the sum over the ordered pairs `i ≠ j` of `J` is twice the sum over the pairs `i < j`. -/
theorem sum_sum_erase_eq_two_mul [LinearOrder ι] [CommRing R] (J : Finset ι) {S : ι → ι → R}
    (hS : ∀ i j, S i j = S j i) :
    ∑ i ∈ J, ∑ j ∈ J.erase i, S i j = 2 * ∑ i ∈ J, ∑ j ∈ J with i < j, S i j := by
  have h1 : ∀ i ∈ J, ∑ j ∈ J.erase i, S i j =
      ∑ j ∈ J with j < i, S i j + ∑ j ∈ J with i < j, S i j := by
    intro i hi
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_erase_add _ _ hi]
    simp only [lt_self_iff_false, ite_false, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    rcases lt_trichotomy j i with h | h | h
    · simp [h, lt_asymm h]
    · exact absurd h (Finset.ne_of_mem_erase hj)
    · simp [h, lt_asymm h]
  have h2 : ∑ i ∈ J, ∑ j ∈ J with j < i, S i j = ∑ i ∈ J, ∑ j ∈ J with i < j, S i j := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hS]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2, two_mul]

end sums

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ}

/-! ## One colour -/

section colour

variable {p : Fin n → Fin n → Ser} {h : Fin n → Ser}

theorem termZ_self (p : Fin n → Fin n → Ser) (h : Fin n → Ser) (k : Fin n) : termZ p h k k = 0 := by
  simp [termZ]

theorem termZ_antisymm (hp : ∀ k l, p k l = p l k) (k l : Fin n) : termZ p h l k = -termZ p h k l := by
  simp only [termZ, hp l k]
  ring

/-- The equation of a body, summed over all `l` (the term `l = k` vanishes). -/
theorem body_univ (hb : ∀ k, h k = ∑ l ∈ univ.erase k, cS (m l) * termZ p h k l) (k : Fin n) :
    h k = ∑ l, cS (m l) * termZ p h k l :=
  (hb k).trans (Finset.sum_erase _ (by simp [termZ]))

theorem subsetSum_aux (hp : ∀ k l, p k l = p l k)
    (hb : ∀ k, h k = ∑ l ∈ univ.erase k, cS (m l) * termZ p h k l) (J : Finset (Fin n)) :
    ∑ k ∈ J, cS (m k) * h k = ∑ k ∈ J, ∑ l ∈ Jᶜ, cS (m k) * cS (m l) * termZ p h k l := by
  have h1 : ∑ k ∈ J, cS (m k) * h k = ∑ k ∈ J, ∑ l, cS (m k) * cS (m l) * termZ p h k l := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [body_univ hb k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have h2 : ∑ k ∈ J, ∑ l ∈ J, cS (m k) * cS (m l) * termZ p h k l = 0 := by
    refine Eq.trans ?_ (sum_sum_mul_sub_of_symm' J (b := fun k l => cS (m k) * cS (m l) * p k l ^ 3)
      (fun k l => by simp only [hp k l]; ring) h)
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [termZ]
    ring
  rw [h1, sum_univ_split, h2, zero_add]

theorem com_aux (hp : ∀ k l, p k l = p l k)
    (hb : ∀ k, h k = ∑ l ∈ univ.erase k, cS (m l) * termZ p h k l) : ∑ k, cS (m k) * h k = 0 := by
  have h1 := subsetSum_aux hp hb univ
  rw [Finset.compl_univ] at h1
  simp only [Finset.sum_empty, Finset.sum_const_zero] at h1
  exact h1

theorem difference_aux (hb : ∀ k, h k = ∑ l ∈ univ.erase k, cS (m l) * termZ p h k l) (k l : Fin n) :
    h k - h l = ∑ j ∈ univ.erase k, cS (m j) * termZ p h k j - ∑ j ∈ univ.erase l, cS (m j) * termZ p h l j := by
  rw [← hb k, ← hb l]

end colour

variable (G : Germ n m)

/-! ## Centre of mass, subset sums, differences -/

/-- The centre of mass: `Σ_k m_k z_k = 0`. -/
theorem com_z : ∑ k, cS (m k) * G.z k = 0 := com_aux G.p_symm G.body_z

/-- The centre of mass: `Σ_k m_k w_k = 0`. -/
theorem com_w : ∑ k, cS (m k) * G.w k = 0 := com_aux G.p_symm G.body_w

/-- Subset sums: `Σ_{k∈J} m_k z_k = Σ_{k∈J, l∈Jᶜ} m_k m_l Z_kl`. -/
theorem subsetSum_z (J : Finset (Fin n)) :
    ∑ k ∈ J, cS (m k) * G.z k = ∑ k ∈ J, ∑ l ∈ Jᶜ, cS (m k) * cS (m l) * termZ G.p G.z k l :=
  subsetSum_aux G.p_symm G.body_z J

/-- Subset sums: `Σ_{k∈J} m_k w_k = Σ_{k∈J, l∈Jᶜ} m_k m_l W_kl`. -/
theorem subsetSum_w (J : Finset (Fin n)) :
    ∑ k ∈ J, cS (m k) * G.w k = ∑ k ∈ J, ∑ l ∈ Jᶜ, cS (m k) * cS (m l) * termZ G.p G.w k l :=
  subsetSum_aux G.p_symm G.body_w J

/-- Differences: `z_kl = Σ_{j≠k} m_j Z_kj − Σ_{j≠l} m_j Z_lj`. -/
theorem difference_z (k l : Fin n) :
    G.z k - G.z l = ∑ j ∈ univ.erase k, cS (m j) * termZ G.p G.z k j -
      ∑ j ∈ univ.erase l, cS (m j) * termZ G.p G.z l j :=
  difference_aux G.body_z k l

/-- Differences: `w_kl = Σ_{j≠k} m_j W_kj − Σ_{j≠l} m_j W_lj`. -/
theorem difference_w (k l : Fin n) :
    G.w k - G.w l = ∑ j ∈ univ.erase k, cS (m j) * termZ G.p G.w k j -
      ∑ j ∈ univ.erase l, cS (m j) * termZ G.p G.w l j :=
  difference_aux G.body_w k l

/-! ## Torques -/

/-- The torque of one body: `Σ_l m_l p_kl³ (z_k w_l − z_l w_k) = 0` (`w_k` times the `z`-equation of `k` minus
`z_k` times its `w`-equation). -/
theorem torque_body (k : Fin n) :
    ∑ l, cS (m l) * (G.p k l ^ 3 * (G.z k * G.w l - G.z l * G.w k)) = 0 := by
  have hz := body_univ G.body_z k
  have hw := body_univ G.body_w k
  have e : ∑ l, cS (m l) * (G.p k l ^ 3 * (G.z k * G.w l - G.z l * G.w k)) =
      G.w k * ∑ l, cS (m l) * termZ G.p G.z k l - G.z k * ∑ l, cS (m l) * termZ G.p G.w k l := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [termZ]
    ring
  rw [e, ← hz, ← hw]
  ring

/-- Torques: `T_J = Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ (z_k w_l − z_l w_k) = 0`. -/
theorem torque (J : Finset (Fin n)) :
    ∑ k ∈ J, ∑ l ∈ Jᶜ, cS (m k) * cS (m l) * (G.p k l ^ 3 * (G.z k * G.w l - G.z l * G.w k)) = 0 := by
  have h1 : ∑ k ∈ J, ∑ l, cS (m k) * cS (m l) * (G.p k l ^ 3 * (G.z k * G.w l - G.z l * G.w k)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← mul_zero (cS (m k)), ← G.torque_body k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have h2 : ∑ k ∈ J, ∑ l ∈ J, cS (m k) * cS (m l) * (G.p k l ^ 3 * (G.z k * G.w l - G.z l * G.w k)) = 0 := by
    refine Eq.trans ?_ (sum_sum_sub_swap J fun k l => cS (m k) * cS (m l) * G.p k l ^ 3 * (G.z k * G.w l))
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [G.p_symm l k]
    ring
  rw [sum_univ_split, h2, zero_add] at h1
  exact h1

/-! ## Partial virials, `U` and Lagrange's identity -/

/-- `p_kl³ z_kl w_kl = p_kl`, from the distance equation `p_kl² z_kl w_kl = 1`. -/
theorem p_cube_mul {k l : Fin n} (h : k ≠ l) :
    G.p k l ^ 3 * ((G.z k - G.z l) * (G.w k - G.w l)) = G.p k l := by
  linear_combination G.p k l * G.dist k l h

/-- `pot` with the product of the masses written as a product of constants:
`Σ_{k ≠ l} m_k m_l p_kl = 2E`. -/
theorem pot' : ∑ k, ∑ l ∈ univ.erase k, cS (m k) * cS (m l) * G.p k l = cS (2 * G.E) := by
  rw [← G.pot]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [cS_mul]

/-- The virial of one body: `2 m_k z_k w_k = Σ_l m_k m_l p_kl³ (w_k z_kl + z_k w_kl)`. -/
theorem virial_body (k : Fin n) :
    2 * (cS (m k) * (G.z k * G.w k)) =
      ∑ l, cS (m k) * cS (m l) * (G.p k l ^ 3 * (G.w k * (G.z k - G.z l) + G.z k * (G.w k - G.w l))) := by
  have hz := body_univ G.body_z k
  have hw := body_univ G.body_w k
  have e : ∑ l, cS (m k) * cS (m l) * (G.p k l ^ 3 * (G.w k * (G.z k - G.z l) + G.z k * (G.w k - G.w l))) =
      cS (m k) * (G.w k * ∑ l, cS (m l) * termZ G.p G.z k l + G.z k * ∑ l, cS (m l) * termZ G.p G.w k l) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [termZ]
    ring
  rw [e, ← hz, ← hw]
  ring

/-- Partial virials, multiplied by `2`, with the ordered pairs `k ≠ l` of `J`:
`2 Σ_{k∈J} m_k z_k w_k = Σ_{k∈J} Σ_{l∈J, l≠k} m_k m_l p_kl + Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ (w_k z_kl + z_k w_kl)`. -/
theorem partialVirial_two (J : Finset (Fin n)) :
    2 * ∑ k ∈ J, cS (m k) * (G.z k * G.w k) =
      ∑ k ∈ J, ∑ l ∈ J.erase k, cS (m k) * cS (m l) * G.p k l +
        ∑ k ∈ J, ∑ l ∈ Jᶜ, cS (m k) * cS (m l) *
          (G.p k l ^ 3 * (G.w k * (G.z k - G.z l) + G.z k * (G.w k - G.w l))) := by
  rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => G.virial_body k, sum_univ_split]
  congr 1
  have hsym := sum_sum_mul_sub_of_symm' J (b := fun k l => cS (m k) * cS (m l) * G.p k l ^ 3)
    (fun k l => by simp only [G.p_symm k l]; ring) (fun k => G.z k * G.w k)
  beta_reduce at hsym
  calc ∑ k ∈ J, ∑ l ∈ J, cS (m k) * cS (m l) *
          (G.p k l ^ 3 * (G.w k * (G.z k - G.z l) + G.z k * (G.w k - G.w l)))
      = ∑ k ∈ J, ∑ l ∈ J, cS (m k) * cS (m l) * (G.p k l ^ 3 * ((G.z k - G.z l) * (G.w k - G.w l))) +
          ∑ k ∈ J, ∑ l ∈ J, cS (m k) * cS (m l) * G.p k l ^ 3 * (G.z k * G.w k - G.z l * G.w l) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = ∑ k ∈ J, ∑ l ∈ J.erase k, cS (m k) * cS (m l) * G.p k l := by
        rw [hsym, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        calc ∑ l ∈ J, cS (m k) * cS (m l) * (G.p k l ^ 3 * ((G.z k - G.z l) * (G.w k - G.w l)))
            = ∑ l ∈ J.erase k, cS (m k) * cS (m l) * (G.p k l ^ 3 * ((G.z k - G.z l) * (G.w k - G.w l))) :=
              (Finset.sum_erase J (by simp)).symm
          _ = _ := Finset.sum_congr rfl fun l hl => by
              rw [G.p_cube_mul (Finset.ne_of_mem_erase hl).symm]

/-- Partial virials:
`Σ_{k∈J} m_k z_k w_k − Σ_{k<l ∈ J} m_k m_l p_kl − ½ Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ (w_k z_kl + z_k w_kl) = 0`. -/
theorem partialVirial (J : Finset (Fin n)) :
    ∑ k ∈ J, cS (m k) * (G.z k * G.w k) - ∑ k ∈ J, ∑ l ∈ J with k < l, cS (m k) * cS (m l) * G.p k l -
      cS (1 / 2) * ∑ k ∈ J, ∑ l ∈ Jᶜ, cS (m k) * cS (m l) *
        (G.p k l ^ 3 * (G.w k * (G.z k - G.z l) + G.z k * (G.w k - G.w l))) = 0 := by
  have h := G.partialVirial_two J
  rw [sum_sum_erase_eq_two_mul J (S := fun k l => cS (m k) * cS (m l) * G.p k l)
    (fun k l => by simp only [G.p_symm k l]; ring)] at h
  have h2 : cS (1 / 2) * 2 = 1 := by
    rw [← cS_two, ← cS_mul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, cS_one]
  set X := ∑ k ∈ J, cS (m k) * (G.z k * G.w k)
  set Y := ∑ k ∈ J, ∑ l ∈ J with k < l, cS (m k) * cS (m l) * G.p k l
  linear_combination cS (1 / 2) * h - (X - Y) * h2

/-- `U = E`: `Σ_{k<l} m_k m_l p_kl = E`. -/
theorem U_eq : ∑ k, ∑ l ∈ Ioi k, cS (m k) * cS (m l) * G.p k l = cS G.E := by
  have h := G.pot'
  rw [sum_sum_erase_eq_two_mul univ (S := fun k l => cS (m k) * cS (m l) * G.p k l)
    (fun k l => by simp only [G.p_symm k l]; ring)] at h
  simp only [Finset.filter_lt_eq_Ioi] at h
  rw [cS_mul, cS_two] at h
  exact mul_left_cancel₀ two_ne_zero_ser h

/-- The virial identity `Σ_k m_k z_k w_k = E` (the partial virial for `J = {1, …, n}` and `U = E`). -/
theorem virial : ∑ k, cS (m k) * (G.z k * G.w k) = cS G.E := by
  have h := G.partialVirial_two univ
  rw [Finset.compl_univ] at h
  simp only [Finset.sum_empty, Finset.sum_const_zero, add_zero] at h
  rw [G.pot', cS_mul, cS_two] at h
  exact mul_left_cancel₀ two_ne_zero_ser h

/-- `U = Σ_k m_k z_k w_k` (Lemma 2.3 (a)). -/
theorem U_eq_virial : ∑ k, ∑ l ∈ Ioi k, cS (m k) * cS (m l) * G.p k l = ∑ k, cS (m k) * (G.z k * G.w k) :=
  G.U_eq.trans G.virial.symm

/-- Lagrange's identity over the ordered pairs: `Σ_{k,l} m_k m_l z_kl w_kl = 2 M E`. -/
theorem lagrange_ordered :
    ∑ k, ∑ l, cS (m k) * cS (m l) * ((G.z k - G.z l) * (G.w k - G.w l)) =
      2 * (cS ((∑ k, m k : ℝ) : ℂ) * cS G.E) := by
  have hA : cS ((∑ k, m k : ℝ) : ℂ) = ∑ k, cS (m k) := by rw [Complex.ofReal_sum, cS_sum]
  have e : ∀ k l, cS (m k) * cS (m l) * ((G.z k - G.z l) * (G.w k - G.w l)) =
      cS (m k) * (G.z k * G.w k) * cS (m l) + cS (m k) * (cS (m l) * (G.z l * G.w l)) -
        cS (m k) * G.z k * (cS (m l) * G.w l) - cS (m k) * G.w k * (cS (m l) * G.z l) := by
    intro k l
    ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum, G.virial,
    G.com_z, G.com_w, hA]
  ring

/-- Lagrange's identity with the centre of mass: `Σ_{k<l} m_k m_l z_kl w_kl = M E` (`M U` in the paper). -/
theorem lagrange :
    ∑ k, ∑ l ∈ Ioi k, cS (m k) * cS (m l) * ((G.z k - G.z l) * (G.w k - G.w l)) =
      cS ((∑ k, m k : ℝ) : ℂ) * cS G.E := by
  have h := G.lagrange_ordered
  have hdiag : ∀ k, ∑ l, cS (m k) * cS (m l) * ((G.z k - G.z l) * (G.w k - G.w l)) =
      ∑ l ∈ univ.erase k, cS (m k) * cS (m l) * ((G.z k - G.z l) * (G.w k - G.w l)) :=
    fun k => (Finset.sum_erase _ (by simp)).symm
  rw [Finset.sum_congr rfl fun k _ => hdiag k,
    sum_sum_erase_eq_two_mul univ (S := fun k l => cS (m k) * cS (m l) * ((G.z k - G.z l) * (G.w k - G.w l)))
      (fun k l => by ring)] at h
  simp only [Finset.filter_lt_eq_Ioi] at h
  exact mul_left_cancel₀ two_ne_zero_ser h

end Germ

end

end CC6Full
