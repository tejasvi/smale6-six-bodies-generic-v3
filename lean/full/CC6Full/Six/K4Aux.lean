import CC6Full.Germ.Diagram
import CC6Full.Germ.Rules
import CC6Full.Germ.Identities
import CC6Full.Six.Systems

/-!
# Tools for the diagrams with a cluster of four bodies without circles (§7)

Shared by `D64.lean` (Lemmas 7.1–7.3) and `D66.lean` (Lemmas 7.4, 7.5). Everything is stated for a germ
`G : Germ n m`, or for `n = 6` with the cluster `K = {3, 4, 5, 6}` of the paper, which is `{2, 3, 4, 5}` in Lean.

* Series: lower bounds for the exponents of sums, products and powers, and the coefficient of a product at the sum
  of lower bounds of the exponents of its factors (`K4.coeff_mul3`, `K4.coeff_termZ`).
* Germs: the coefficient of the distance equation at exponent `0` (`K4.coeff_dist`), (F4) of Lemma 6.1
  (`lem:common`), proved here for the pair `(k, j)` with `a_k < a_j`, `b_j < b_k` (`K4.f4`, `K4.f4_term`), and
  small facts about circles, the centre of mass and the equations of the bodies.
* The cluster `K`: `K4.emb : Fin 4 → Fin 6`, `k ↦ k + 2`, renumbers `K` as `0, 1, 2, 3` in increasing order; the
  leading data `K4.xiK`, `K4.etaK`, `K4.PK`, `K4.muK`; part (a) of Lemma 7.1 (`K4.pairsK`), and the distance
  equations and the equations `Φ^ξ_k = 0` of the leading data (`K4.lead_dist`, `K4.lead_force_xi`), and
  `Φ^η_k = [w_k]_{2−4x}` (`K4.lead_force_eta`), which are common to Lemmas 7.3 and 7.5.
-/

namespace CC6Full

open Finset

noncomputable section

namespace K4

/-! ## Series -/

/-- A lower bound for the exponents of the terms is a lower bound for the exponent of the sum. -/
theorem le_orderTop_sum {ι : Type*} (s : Finset ι) (f : ι → Ser) {e : WithTop ℚ}
    (h : ∀ i ∈ s, e ≤ (f i).orderTop) : e ≤ (∑ i ∈ s, f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi)))
      HahnSeries.min_orderTop_le_orderTop_add

/-- A constant factor does not lower the exponent. -/
theorem le_orderTop_cS_mul (a : ℂ) (f : Ser) : f.orderTop ≤ (cS a * f).orderTop := by
  by_cases ha : a = 0
  · rw [ha, cS_zero, zero_mul, HahnSeries.orderTop_zero]
    exact le_top
  · rw [Ser.orderTop_cS_mul ha]

/-- `k e ≤ e(f^k)` for `e ≤ e(f)`. -/
theorem le_orderTop_pow {f : Ser} {e : ℚ} (h : (e : WithTop ℚ) ≤ f.orderTop) (k : ℕ) :
    ((k * e : ℚ) : WithTop ℚ) ≤ (f ^ k).orderTop := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, HahnSeries.orderTop_mul, show ((k + 1 : ℕ) * e : ℚ) = k * e + e by push_cast; ring,
      WithTop.coe_add]
    exact add_le_add ih h

/-- `x + y < u + v` for `x ≤ u`, `y < v` with `x, y` finite. -/
theorem coe_add_lt {x y : ℚ} {u v : WithTop ℚ} (hu : (x : WithTop ℚ) ≤ u) (hv : (y : WithTop ℚ) < v) :
    ((x + y : ℚ) : WithTop ℚ) < u + v := by
  induction u using WithTop.recTopCoe with
  | top => rw [WithTop.top_add]; exact WithTop.coe_lt_top _
  | coe u =>
    induction v using WithTop.recTopCoe with
    | top => rw [WithTop.add_top]; exact WithTop.coe_lt_top _
    | coe v =>
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]
      rw [WithTop.coe_le_coe] at hu
      rw [WithTop.coe_lt_coe] at hv
      linarith

/-- `[fgh]_{a+b+c} = [f]_a [g]_b [h]_c` for lower bounds `a, b, c` of the exponents. -/
theorem coeff_mul3 {f g h : Ser} {a b c : ℚ} (hf : (a : WithTop ℚ) ≤ f.orderTop)
    (hg : (b : WithTop ℚ) ≤ g.orderTop) (hh : (c : WithTop ℚ) ≤ h.orderTop) :
    (f * g * h).coeff (a + b + c) = f.coeff a * g.coeff b * h.coeff c := by
  have hfg : ((a + b : ℚ) : WithTop ℚ) ≤ (f * g).orderTop := by
    rw [HahnSeries.orderTop_mul, WithTop.coe_add]
    exact add_le_add hf hg
  rw [Ser.coeff_mul_of_le hfg hh, Ser.coeff_mul_of_le hf hg]

/-- `[f^k]_{k e} = [f]_e^k` for `e ≤ e(f)` (`Ser.coeff_pow_of_le`). -/
theorem coeff_pow' {f : Ser} {e : ℚ} (h : (e : WithTop ℚ) ≤ f.orderTop) (k : ℕ) :
    (f ^ k).coeff (k * e) = f.coeff e ^ k :=
  Ser.coeff_pow_of_le h k

/-- `[p_kl³ h_kl]_{3a+b} = [p_kl]_a³ [h_kl]_b` for lower bounds `a`, `b` of the exponents. -/
theorem coeff_termZ {n : ℕ} {p : Fin n → Fin n → Ser} {h : Fin n → Ser} {k l : Fin n} {a b : ℚ}
    (hp : (a : WithTop ℚ) ≤ (p k l).orderTop) (hh : (b : WithTop ℚ) ≤ (h k - h l).orderTop) :
    (termZ p h k l).coeff (3 * a + b) = (p k l).coeff a ^ 3 * (h k - h l).coeff b := by
  unfold termZ
  have h3 := le_orderTop_pow hp 3
  have c3 := coeff_pow' hp 3
  push_cast at h3 c3
  rw [Ser.coeff_mul_of_le h3 hh, c3]

/-! ## Germs -/

variable {n : ℕ} {m : Fin n → ℝ}

/-- A body that is not `z`-circled has `[z_k]_{−2} = 0`. -/
theorem coeff_z_neg_two (G : Germ n m) {k : Fin n} (hk : ¬ G.zCircle k) : (G.z k).coeff (-2) = 0 := by
  by_contra h
  exact hk ((G.colZ.circle_iff_coeff k).mpr h)

/-- A body that is not `w`-circled has `[w_k]_{−2} = 0`. -/
theorem coeff_w_neg_two (G : Germ n m) {k : Fin n} (hk : ¬ G.wCircle k) : (G.w k).coeff (-2) = 0 := by
  by_contra h
  exact hk ((G.colW.circle_iff_coeff k).mpr h)

/-- The centre of mass at exponent `e`: `Σ_k m_k [z_k]_e = 0`. -/
theorem com_z_coeff (G : Germ n m) (e : ℚ) : ∑ k, (m k : ℂ) * (G.z k).coeff e = 0 :=
  initial_coeff G.com_z e

/-- The centre of mass at exponent `e`: `Σ_k m_k [w_k]_e = 0`. -/
theorem com_w_coeff (G : Germ n m) (e : ℚ) : ∑ k, (m k : ℂ) * (G.w k).coeff e = 0 :=
  initial_coeff G.com_w e

/-- Below `ζ_ab` the bodies `a` and `b` have the same coefficients. -/
theorem coeff_z_eq_of_lt (G : Germ n m) {a b : Fin n} (hab : a ≠ b) {e : ℚ} (he : e < G.zeta a b) :
    (G.z a).coeff e = (G.z b).coeff e := by
  have h0 : (G.z a - G.z b).coeff e = 0 :=
    Ser.coeff_eq_zero_of_lt (by rw [G.orderTop_z_sub hab]; exact_mod_cast he)
  rwa [Ser.coeff_sub, sub_eq_zero] at h0

/-- Below `ω_ab` the bodies `a` and `b` have the same coefficients. -/
theorem coeff_w_eq_of_lt (G : Germ n m) {a b : Fin n} (hab : a ≠ b) {e : ℚ} (he : e < G.omega a b) :
    (G.w a).coeff e = (G.w b).coeff e := by
  have h0 : (G.w a - G.w b).coeff e = 0 :=
    Ser.coeff_eq_zero_of_lt (by rw [G.orderTop_w_sub hab]; exact_mod_cast he)
  rwa [Ser.coeff_sub, sub_eq_zero] at h0

/-- Positive masses are nonzero. -/
theorem mass_ne_zero (hm : ∀ i, 0 < m i) (i : Fin n) : (m i : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (hm i).ne'

/-- A nonempty partial sum of positive masses is nonzero. -/
theorem sum_mass_ne_zero (hm : ∀ i, 0 < m i) {K : Finset (Fin n)} (hK : K.Nonempty) :
    ∑ i ∈ K, (m i : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_sum]
  exact Complex.ofReal_ne_zero.mpr (Finset.sum_pos (fun i _ => hm i) hK).ne'

/-- If `ζ_kl = −2`, one of `k`, `l` is `z`-circled. -/
theorem zCircle_of_zeta (G : Germ n m) {k l : Fin n} (hkl : k ≠ l) (h : G.zeta k l = -2) :
    G.zCircle k ∨ G.zCircle l := by
  have h1 := G.min_le_zeta hkl
  rw [h] at h1
  rcases min_le_iff.mp h1 with h2 | h2
  · exact Or.inl (le_antisymm h2 (G.low_z.1 k))
  · exact Or.inr (le_antisymm h2 (G.low_z.1 l))

/-- If `ω_jl = −2` for all `l ≠ j`, then `a_j ≥ 2`: every term `Z_jl` of the `z`-equation of `j` has exponent
`(6 − ζ_jl)/2 ≥ 2`. -/
theorem two_le_orderTop_z (G : Germ n m) {j : Fin n} (h : ∀ l, l ≠ j → G.omega j l = -2) :
    ((2 : ℚ) : WithTop ℚ) ≤ (G.z j).orderTop := by
  rw [G.body_z j]
  refine le_orderTop_sum _ _ fun l hl => le_trans ?_ (le_orderTop_cS_mul _ _)
  have hlj : l ≠ j := Finset.ne_of_mem_erase hl
  rw [G.orderTop_termZ_z hlj.symm, h l hlj]
  have h2 := (G.O1_le hlj.symm).1
  exact_mod_cast (show (2 : ℚ) ≤ -(G.zeta j l + 3 * -2) / 2 by linarith)

/-- If `a_j ≥ 2` and `ζ_jk < 2`, then `a_k = ζ_jk < a_j`. -/
theorem orderTop_z_eq_zeta (G : Germ n m) {j k : Fin n} (hjk : j ≠ k)
    (hj : ((2 : ℚ) : WithTop ℚ) ≤ (G.z j).orderTop) (hz : G.zeta j k < 2) :
    (G.z k).orderTop = (G.zeta j k : WithTop ℚ) ∧ (G.z k).orderTop < (G.z j).orderTop := by
  have h1 := G.min_le_zeta hjk
  have hlt : (G.z k).orderTop < (G.z j).orderTop := by
    by_contra hcon
    rw [min_eq_left (not_lt.mp hcon)] at h1
    have h3 : (2 : ℚ) ≤ G.zeta j k := by exact_mod_cast le_trans hj h1
    linarith
  have h2 := G.zeta_eq_min hjk hlt.ne'
  rw [min_eq_right hlt.le] at h2
  exact ⟨h2.symm, hlt⟩

/-- The centre of mass at the exponent `A` of a body `k ∈ K`, when `A` is below `ζ_kl` for `l ∈ K` and below the
exponents of the bodies outside `K`, gives `[z_k]_A Σ_{l∈K} m_l = 0`, which is impossible. -/
theorem com_contra (G : Germ n m) (hm : ∀ i, 0 < m i) (K : Finset (Fin n)) {k : Fin n} (hk : k ∈ K) {A : ℚ}
    (hkA : (G.z k).orderTop = A) (hK : ∀ l ∈ K, l ≠ k → A < G.zeta k l)
    (hout : ∀ j ∉ K, (A : WithTop ℚ) < (G.z j).orderTop) : False := by
  have hc := com_z_coeff G A
  rw [← Finset.sum_add_sum_compl K] at hc
  have h2 : ∑ i ∈ Kᶜ, (m i : ℂ) * (G.z i).coeff A = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Ser.coeff_eq_zero_of_lt (hout i (Finset.mem_compl.mp hi)), mul_zero]
  have h1 : ∑ i ∈ K, (m i : ℂ) * (G.z i).coeff A = (∑ i ∈ K, (m i : ℂ)) * (G.z k).coeff A := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hik : i = k
    · rw [hik]
    · rw [← coeff_z_eq_of_lt G (Ne.symm hik) (hK i hi hik)]
  rw [h1, h2, add_zero] at hc
  have h0 : (G.z k).coeff A = 0 := (mul_eq_zero.mp hc).resolve_left (sum_mass_ne_zero hm ⟨k, hk⟩)
  exact HahnSeries.coeff_orderTop_ne hkA h0

/-- The distance equation at exponent `0`: `[p_kl]_a² [z_kl]_b [w_kl]_c = 1` for lower bounds `a, b, c` of the
exponents with `2a + b + c = 0`. -/
theorem coeff_dist (G : Germ n m) {k l : Fin n} (hkl : k ≠ l) {a b c : ℚ}
    (hp : (a : WithTop ℚ) ≤ (G.p k l).orderTop) (hz : (b : WithTop ℚ) ≤ (G.z k - G.z l).orderTop)
    (hw : (c : WithTop ℚ) ≤ (G.w k - G.w l).orderTop) (habc : 2 * a + b + c = 0) :
    (G.p k l).coeff a ^ 2 * (G.z k - G.z l).coeff b * (G.w k - G.w l).coeff c = 1 := by
  have h2 := le_orderTop_pow hp 2
  have c2 := coeff_pow' hp 2
  push_cast at h2 c2
  have e := congrArg (fun f : Ser => f.coeff (2 * a + b + c)) (G.dist k l hkl)
  rw [coeff_mul3 h2 hz hw, c2, habc, HahnSeries.coeff_one, ite_eq_left rfl] at e
  exact e

/-- **(F4)** of Lemma 6.1 (`lem:common`), for the pair `(k, j)`: if `a_k < a_j` and `b_j < b_k`, then
`ζ_kj = a_k`, `ω_kj = b_j`, `x_kj = (a_k + b_j)/2`, and `[p_kj]² ẑ_k ŵ_j = −1` with `[p_kj]` the coefficient at
`e(p_kj) = −(a_k + b_j)/2`. -/
theorem f4 (G : Germ n m) {k j : Fin n} (hkj : k ≠ j) {a b : ℚ}
    (ha : (G.z k).orderTop = a) (hb : (G.w j).orderTop = b)
    (haj : (a : WithTop ℚ) < (G.z j).orderTop) (hbk : (b : WithTop ℚ) < (G.w k).orderTop) :
    G.zeta k j = a ∧ G.omega k j = b ∧ G.x k j = (a + b) / 2 ∧
      (G.p k j).coeff (-((a + b) / 2)) ^ 2 * (G.z k).coeff a * (G.w j).coeff b = -1 := by
  have hz : G.zeta k j = a := by
    have h1 := G.zeta_eq_min hkj (by rw [ha]; exact haj.ne)
    rw [ha, min_eq_left haj.le] at h1
    exact_mod_cast h1
  have hw : G.omega k j = b := by
    have h1 := G.omega_eq_min hkj (by rw [hb]; exact hbk.ne')
    rw [hb, min_eq_right hbk.le] at h1
    exact_mod_cast h1
  have hx : G.x k j = (a + b) / 2 := by rw [G.x_eq hkj, hz, hw]
  refine ⟨hz, hw, hx, ?_⟩
  have hp : (G.p k j).orderTop = ((-((a + b) / 2) : ℚ) : WithTop ℚ) := by rw [G.orderTop_p hkj, hx]
  have hzk : (G.z k - G.z j).orderTop = (a : WithTop ℚ) := by rw [G.orderTop_z_sub hkj, hz]
  have hwk : (G.w k - G.w j).orderTop = (b : WithTop ℚ) := by rw [G.orderTop_w_sub hkj, hw]
  have e := coeff_dist G hkj hp.ge hzk.ge hwk.ge (by ring)
  rw [Ser.coeff_sub, Ser.coeff_sub, Ser.coeff_eq_zero_of_lt haj, Ser.coeff_eq_zero_of_lt hbk] at e
  linear_combination -e

/-- **(F4)** of Lemma 6.1 (`lem:common`), second part, for the pair `(k, j)`: if moreover `a_j + b_k > a_k + b_j`,
the term `p_kj³ (z_k w_j − z_j w_k)` has exponent at least `−(a_k + b_j)/2`, with coefficient `−[p_kj]` there. -/
theorem f4_term (G : Germ n m) {k j : Fin n} (hkj : k ≠ j) {a b : ℚ}
    (ha : (G.z k).orderTop = a) (hb : (G.w j).orderTop = b)
    (haj : (a : WithTop ℚ) < (G.z j).orderTop) (hbk : (b : WithTop ℚ) < (G.w k).orderTop)
    (hsum : ((a + b : ℚ) : WithTop ℚ) < (G.z j).orderTop + (G.w k).orderTop) :
    ((-((a + b) / 2) : ℚ) : WithTop ℚ) ≤ (G.p k j ^ 3 * (G.z k * G.w j - G.z j * G.w k)).orderTop ∧
      (G.p k j ^ 3 * (G.z k * G.w j - G.z j * G.w k)).coeff (-((a + b) / 2)) =
        -(G.p k j).coeff (-((a + b) / 2)) := by
  obtain ⟨-, -, hx, hcoef⟩ := f4 G hkj ha hb haj hbk
  obtain ⟨E, hE⟩ : ∃ E : ℚ, E = -((a + b) / 2) := ⟨_, rfl⟩
  rw [← hE] at hcoef ⊢
  have hp : (G.p k j).orderTop = (E : WithTop ℚ) := by rw [G.orderTop_p hkj, hx, hE]
  have hp3 : ((3 * E : ℚ) : WithTop ℚ) ≤ (G.p k j ^ 3).orderTop := by
    have h3 := le_orderTop_pow hp.ge 3
    push_cast at h3
    exact h3
  have c3 := coeff_pow' hp.ge 3
  push_cast at c3
  have hzw : ((a + b : ℚ) : WithTop ℚ) ≤ (G.z k * G.w j).orderTop := by
    rw [HahnSeries.orderTop_mul, ha, hb, WithTop.coe_add]
  have hE3 : 3 * E + (a + b) = E := by rw [hE]; ring
  have hT1 : (G.p k j ^ 3 * (G.z k * G.w j)).coeff E =
      (G.p k j).coeff E ^ 3 * ((G.z k).coeff a * (G.w j).coeff b) := by
    have h1 := Ser.coeff_mul_of_le hp3 hzw
    rw [hE3, c3, Ser.coeff_mul_of_le ha.ge hb.ge] at h1
    exact h1
  have hT1o : (E : WithTop ℚ) ≤ (G.p k j ^ 3 * (G.z k * G.w j)).orderTop := by
    rw [HahnSeries.orderTop_mul, ← hE3, WithTop.coe_add]
    exact add_le_add hp3 hzw
  have hT2o : (E : WithTop ℚ) < (G.p k j ^ 3 * (G.z j * G.w k)).orderTop := by
    rw [HahnSeries.orderTop_mul, HahnSeries.orderTop_mul, ← hE3]
    exact coe_add_lt hp3 hsum
  rw [mul_sub]
  refine ⟨le_trans (le_min hT1o hT2o.le) HahnSeries.min_orderTop_le_orderTop_sub, ?_⟩
  rw [Ser.coeff_sub, hT1, Ser.coeff_eq_zero_of_lt hT2o]
  linear_combination (G.p k j).coeff E * hcoef

/-! ## The cluster `K = {3, 4, 5, 6}` of the paper -/

variable {m : Fin 6 → ℝ}

/-- The cluster `K = {3, 4, 5, 6}` of the paper (`{2, 3, 4, 5}` in Lean). -/
def Kset : Finset (Fin 6) := {2, 3, 4, 5}

/-- `k ∈ K` iff `k ≥ 2` in Lean's numbering. -/
theorem mem_Kset (k : Fin 6) : k ∈ Kset ↔ 2 ≤ k.val := by
  revert k
  decide

/-- `K` is the complement of the binary `{1, 2}` of the paper (`{0, 1}` in Lean). -/
theorem compl_Kset : Kset = ({0, 1} : Finset (Fin 6))ᶜ := by decide

/-- The bodies of `K`, renumbered `0, 1, 2, 3` in increasing order: `k ↦ k + 2`. -/
def emb (k : Fin 4) : Fin 6 := ⟨k.val + 2, by omega⟩

theorem emb_val (k : Fin 4) : (emb k).val = k.val + 2 := rfl

theorem two_le_emb (k : Fin 4) : 2 ≤ (emb k).val := by
  rw [emb_val]
  omega

theorem emb_ne {k l : Fin 4} (h : k ≠ l) : emb k ≠ emb l := by
  intro h'
  apply h
  have := congrArg Fin.val h'
  rw [emb_val, emb_val] at this
  exact Fin.ext (by omega)

theorem emb_zero : emb 0 = 2 := rfl
theorem emb_one : emb 1 = 3 := rfl
theorem emb_two : emb 2 = 4 := rfl
theorem emb_three : emb 3 = 5 := rfl

/-- A sum over the six bodies, with the bodies `0, 1` and those of `K` separated. -/
theorem sum_fin6 {M : Type*} [AddCommMonoid M] (f : Fin 6 → M) :
    ∑ l, f l = f 0 + f 1 + ∑ l : Fin 4, f (emb l) := by
  rw [Fin.sum_univ_six, Fin.sum_univ_four, emb_zero, emb_one, emb_two, emb_three]
  simp only [add_assoc]

/-- The force as a sum over all bodies (the term `l = k` vanishes). -/
theorem force_eq_sum {N : ℕ} (μ : Fin N → ℂ) (P : Fin N → Fin N → ℂ) (h : Fin N → ℂ) (k : Fin N) :
    force μ P h k = ∑ l, μ l * P k l ^ 3 * (h k - h l) :=
  Finset.sum_erase _ (by simp)

/-- The coefficient form of the equation of a body `emb k` of `K`, with the terms of the bodies `0, 1` and those of
`K` separated. -/
theorem body_coeff_split (G : Germ 6 m) {h h' : Fin 6 → Ser} (H : Colour.Pair m G.p h h') (k : Fin 4)
    (e : ℚ) : (h (emb k)).coeff e = (m 0 : ℂ) * (termZ G.p h (emb k) 0).coeff e +
      (m 1 : ℂ) * (termZ G.p h (emb k) 1).coeff e +
        ∑ l : Fin 4, (m (emb l) : ℂ) * (termZ G.p h (emb k) (emb l)).coeff e := by
  rw [H.coeff_body (emb k) e, Finset.sum_erase _ (by simp [Germ.termZ_self]), sum_fin6]

/-! ## The leading data -/

/-- The masses `m_K` of the bodies of `K`, renumbered. -/
def muK (m : Fin 6 → ℝ) (k : Fin 4) : ℂ := (m (emb k) : ℂ)

/-- `ξ_k = [z_k]_{3x−2}` for the bodies of `K`. -/
def xiK (G : Germ 6 m) (x : ℚ) (k : Fin 4) : ℂ := (G.z (emb k)).coeff (3 * x - 2)

/-- `η_k = [w_k]_{2−x}` for the bodies of `K`, so that `η_k − η_l = [w_kl]_{2−x}`. -/
def etaK (G : Germ 6 m) (x : ℚ) (k : Fin 4) : ℂ := (G.w (emb k)).coeff (2 - x)

/-- `P_kl = [p_kl]_{−x}` for the bodies of `K`. -/
def PK (G : Germ 6 m) (x : ℚ) (k l : Fin 4) : ℂ := (G.p (emb k) (emb l)).coeff (-x)

/-- `ξ_k − ξ_l = [z_kl]_{3x−2}`. -/
theorem xiK_sub (G : Germ 6 m) (x : ℚ) (k l : Fin 4) :
    xiK G x k - xiK G x l = (G.z (emb k) - G.z (emb l)).coeff (3 * x - 2) :=
  (Ser.coeff_sub _ _ _).symm

/-- `η_k − η_l = [w_kl]_{2−x}`: the `η_kl` of Lemmas 7.3 and 7.5 are differences. -/
theorem etaK_sub (G : Germ 6 m) (x : ℚ) (k l : Fin 4) :
    etaK G x k - etaK G x l = (G.w (emb k) - G.w (emb l)).coeff (2 - x) :=
  (Ser.coeff_sub _ _ _).symm

/-- `P` is symmetric. -/
theorem PK_symm (G : Germ 6 m) (x : ℚ) : IsSymm (PK G x) := by
  intro k l
  simp only [PK, G.p_symm (emb k) (emb l)]

/-- The hypothesis on the pairs of `K` given by part (a) of Lemma 7.1: `ζ = 3x − 2`, `ω = 2 − x` and `x_kl = x`. -/
def PairsK (G : Germ 6 m) (x : ℚ) : Prop :=
  ∀ k l : Fin 6, 2 ≤ k.val → 2 ≤ l.val → k ≠ l → G.zeta k l = 3 * x - 2 ∧ G.omega k l = 2 - x ∧ G.x k l = x

/-- **Lemma 7.1 (a)** (`lem:d64type`), and (a) of Lemma 7.4 (`lem:d66type`): if the six pairs of `K` are
`z`-strokes, the pair `{3, 4}` of the paper is not a `w`-stroke and `3`, `4` are not `z`-circled, then on the six
pairs of `K`, `ζ = 3x − 2` and `ω = 2 − x` with one common `x`, `0 < x < 1`. -/
theorem pairsK (G : Germ 6 m) (hz : ∀ k l : Fin 6, 2 ≤ k.val → 2 ≤ l.val → k ≠ l → G.zStroke k l)
    (hw : ¬ G.wStroke 2 3) (hc2 : ¬ G.zCircle 2) (hc3 : ¬ G.zCircle 3) :
    0 < G.x 2 3 ∧ G.x 2 3 < 1 ∧ PairsK G (G.x 2 3) := by
  have hS : ∀ k ∈ Kset, ∀ l ∈ Kset, k ≠ l → G.edge k l := fun k hk l hl hkl =>
    Or.inl (hz k l ((mem_Kset k).mp hk) ((mem_Kset l).mp hl) hkl)
  obtain ⟨hζ23, hω23, hx0, hx1⟩ := G.O3_z (hz 2 3 (by decide) (by decide) (by decide))
  refine ⟨?_, ?_, ?_⟩
  · rcases hx0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hζ : G.zeta 2 3 = -2 := by rw [hζ23, ← h]; ring
      rcases zCircle_of_zeta G (by decide) hζ with h2 | h3
      · exact hc2 h2
      · exact hc3 h3
  · rcases hx1.lt_or_eq with h | h
    · exact h
    · exact absurd ((G.O4 (by decide)).mp h).2 hw
  · intro k l hk hl hkl
    have h23 : (2 : Fin 6) ≠ 3 := by decide
    obtain ⟨hζ, hω, -⟩ := G.edges_clique hS ((mem_Kset k).mpr hk) ((mem_Kset l).mpr hl)
      ((mem_Kset 2).mpr (by decide)) ((mem_Kset 3).mpr (by decide)) hkl h23
    refine ⟨by rw [hζ, hζ23], by rw [hω, hω23], ?_⟩
    rw [G.x_eq hkl, G.x_eq h23, hζ, hω]

/-- The distance equations of the leading data (Lemma 7.3, and (i) of Lemma 7.5): at exponent `0`,
`P_kl² (ξ_k − ξ_l)(η_k − η_l) = 1`. -/
theorem lead_dist (G : Germ 6 m) {x : ℚ} (hK : PairsK G x) : DistEqs (PK G x) (xiK G x) (etaK G x) := by
  intro k l hkl
  have hkl' := emb_ne hkl
  obtain ⟨hζ, hω, hx⟩ := hK _ _ (two_le_emb k) (two_le_emb l) hkl'
  have hp : (G.p (emb k) (emb l)).orderTop = ((-x : ℚ) : WithTop ℚ) := by rw [G.orderTop_p hkl', hx]
  have hz : (G.z (emb k) - G.z (emb l)).orderTop = ((3 * x - 2 : ℚ) : WithTop ℚ) := by
    rw [G.orderTop_z_sub hkl', hζ]
  have hw : (G.w (emb k) - G.w (emb l)).orderTop = ((2 - x : ℚ) : WithTop ℚ) := by
    rw [G.orderTop_w_sub hkl', hω]
  have e := coeff_dist G hkl' hp.ge hz.ge hw.ge (by ring)
  rw [Ser.coeff_sub, Ser.coeff_sub] at e
  exact e

/-- `Φ^ξ_k = 0` for the bodies of `K` (Lemma 7.3, and (ii) of Lemma 7.5): the `z`-equation of `k ∈ K` at
exponent `−2`, where the terms `Z_kl`, `l ∈ K`, have coefficient `P_kl³ (ξ_k − ξ_l)`, the pairs `kj`, `j = 1, 2`,
are not `z`-strokes, and `k` is not `z`-circled. -/
theorem lead_force_xi (G : Germ 6 m) {x : ℚ} (hK : PairsK G x)
    (hns : ∀ k j : Fin 6, 2 ≤ k.val → j.val < 2 → ¬ G.zStroke k j)
    (hc : ∀ k : Fin 6, 2 ≤ k.val → ¬ G.zCircle k) (k : Fin 4) :
    force (muK m) (PK G x) (xiK G x) k = 0 := by
  have hb := body_coeff_split G G.colZ k (-2)
  rw [coeff_z_neg_two G (hc _ (two_le_emb k)),
    G.colZ.coeff_termZ_eq_zero (Fin.ne_of_val_ne (by rw [emb_val]; simp)) (hns _ 0 (two_le_emb k) (by simp)),
    G.colZ.coeff_termZ_eq_zero (Fin.ne_of_val_ne (by rw [emb_val]; simp)) (hns _ 1 (two_le_emb k) (by simp)),
    mul_zero, mul_zero, zero_add, zero_add] at hb
  rw [force_eq_sum, hb]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k = l
  · subst hkl
    simp [Germ.termZ_self]
  · have hkl' := emb_ne hkl
    obtain ⟨hζ, -, hx⟩ := hK _ _ (two_le_emb k) (two_le_emb l) hkl'
    have hp : ((-x : ℚ) : WithTop ℚ) ≤ (G.p (emb k) (emb l)).orderTop := by rw [G.orderTop_p hkl', hx]
    have hz : ((3 * x - 2 : ℚ) : WithTop ℚ) ≤ (G.z (emb k) - G.z (emb l)).orderTop := by
      rw [G.orderTop_z_sub hkl', hζ]
    have e := coeff_termZ hp hz
    rw [show 3 * -x + (3 * x - 2) = -2 by ring, Ser.coeff_sub] at e
    simp only [muK, PK, xiK]
    rw [e]
    ring

/-- `Φ^η_k = [w_k]_{2−4x}` for a body `k ∈ K` whose terms `W_kj`, `j = 1, 2`, vanish at exponent `2 − 4x`
(Lemma 7.3, and (iii) of Lemma 7.5): the `w`-equation of `k` at exponent `2 − 4x`, where the terms `W_kl`,
`l ∈ K`, have coefficient `P_kl³ (η_k − η_l)`. -/
theorem lead_force_eta (G : Germ 6 m) {x : ℚ} (hK : PairsK G x) (k : Fin 4)
    (h0 : (termZ G.p G.w (emb k) 0).coeff (2 - 4 * x) = 0)
    (h1 : (termZ G.p G.w (emb k) 1).coeff (2 - 4 * x) = 0) :
    force (muK m) (PK G x) (etaK G x) k = (G.w (emb k)).coeff (2 - 4 * x) := by
  have hb := body_coeff_split G G.colW k (2 - 4 * x)
  rw [h0, h1, mul_zero, mul_zero, zero_add, zero_add] at hb
  rw [force_eq_sum, hb]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k = l
  · subst hkl
    simp [Germ.termZ_self]
  · have hkl' := emb_ne hkl
    obtain ⟨-, hω, hx⟩ := hK _ _ (two_le_emb k) (two_le_emb l) hkl'
    have hp : ((-x : ℚ) : WithTop ℚ) ≤ (G.p (emb k) (emb l)).orderTop := by rw [G.orderTop_p hkl', hx]
    have hw : ((2 - x : ℚ) : WithTop ℚ) ≤ (G.w (emb k) - G.w (emb l)).orderTop := by
      rw [G.orderTop_w_sub hkl', hω]
    have e := coeff_termZ hp hw
    rw [show 3 * -x + (2 - x) = 2 - 4 * x by ring, Ser.coeff_sub] at e
    simp only [muK, PK, etaK]
    rw [e]
    ring

/-- The term `W_kj` vanishes at exponent `2 − 4x` when `ζ_kj = 3x − 2`, `ω_kj = −2` and `x < 4`: its exponent is
`(2 − 4x) + (2 − x/2)`. -/
theorem coeff_W_cross (G : Germ 6 m) {k j : Fin 6} (hkj : k ≠ j) {x : ℚ} (hζ : G.zeta k j = 3 * x - 2)
    (hω : G.omega k j = -2) (hx : x < 4) : (termZ G.p G.w k j).coeff (2 - 4 * x) = 0 := by
  apply Ser.coeff_eq_zero_of_lt
  rw [G.orderTop_termZ_w hkj, hζ, hω]
  exact_mod_cast (show 2 - 4 * x < -(3 * (3 * x - 2) + -2) / 2 by linarith)

end K4

end

end CC6Full
