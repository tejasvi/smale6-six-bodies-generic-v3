import CC6Full.Germ.Symm
import CC6Full.Germ.Identities
import CC6Full.Germ.Rules

/-!
# Common facts for the diagrams with a circled cluster of each colour (§6.1)

Paper §6.1 (`ss:common`): Lemma 6.1 (`lem:common`, (F1)–(F4)), Lemma 6.2 (`lem:rewrite`) and Lemma 6.3
(`lem:binary`), for a germ `G : Germ n m`. As in the paper, `a_k = e(z_k)` and `b_k = e(w_k)` are exponents
(`orderTop`), `ẑ_k`, `ŵ_k` and `p̂_kl` are the leading coefficients of `z_k`, `w_k` and `p_kl` (`leadingCoeff`), and
`Z_kl = p_kl³ z_kl`, `W_kl = p_kl³ w_kl` are `termZ G.p G.z k l` and `termZ G.p G.w k l`.

* (F1)–(F3): `Six.F1_z`, `Six.F2_z`, `Six.F3_z`, and `Six.F1_w`, `Six.F2_w`, `Six.F3_w` with the colours exchanged.
* (F4): `Six.F4_z` (the exponents of `z_jl`, `w_jl`, `p_jl` and their leading coefficients) and `Six.F4_z_term`
  (the term of the pair `jl` in a torque), and `Six.F4_w`, `Six.F4_w_term` with the colours exchanged.
* Lemma 6.2: `Six.rewrite_B` (`B_z = z_o − A_z` and `B_w = w_o − A_w` by the equations of the body `o`) and
  `Six.rewrite_sum`, identities of series valid for every germ.
* Lemma 6.3: `Six.binary_com_z` (the relation `m_i ẑ_i + m_{i'} ẑ_{i'} = 0`) and `Six.binary_z`, for any two distinct
  bodies `i`, `i'` in place of `5`, `6`, and `Six.binary_com_w`, `Six.binary_w` with the colours exchanged.

The statements for the colour `w` are those for `z` applied to `G.swap` (Lemma 2.9 (b), `lem:symm`). The positive
masses `hm : ∀ i, 0 < m i` are assumed where they are used: in (F1) and (F2) through `Σ_{k∈A} m_k ≠ 0`, in the second
part of (F4) through `m_j m_l ≠ 0`, and in Lemma 6.3 through `m_i³ + m_{i'}³ ≠ 0`. (F3), the first part of (F4),
Lemma 6.2 and the relation of Lemma 6.3 hold for all masses.

In (F1) the paper also assumes that `A` has two, three or four bodies and that no pair of `A` is a `zw`-edge. The
proof uses neither (it does not use `x < 1`), so `Six.F1_z` and `Six.F2_z` are stated without these hypotheses.
-/

namespace CC6Full

open Finset

noncomputable section

namespace Six

variable {n : ℕ} {m : Fin n → ℝ}

/-! ## Series -/

/-- A lower bound for the exponents of the terms is a lower bound for the exponent of the sum. -/
private theorem le_orderTop_sum {ι : Type*} (s : Finset ι) (f : ι → Ser) {e : WithTop ℚ}
    (h : ∀ i ∈ s, e ≤ (f i).orderTop) : e ≤ (∑ i ∈ s, f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi)))
      HahnSeries.min_orderTop_le_orderTop_add

/-- A constant factor does not lower the exponent. -/
private theorem le_orderTop_cS_mul (a : ℂ) (f : Ser) : f.orderTop ≤ (cS a * f).orderTop := by
  by_cases ha : a = 0
  · rw [ha, cS_zero, zero_mul, HahnSeries.orderTop_zero]
    exact le_top
  · rw [Ser.orderTop_cS_mul ha]

/-- `x + y < u + v` for `x ≤ u` and `y < v` with `x`, `y` finite. -/
private theorem coe_add_lt {x y : ℚ} {u v : WithTop ℚ} (hu : (x : WithTop ℚ) ≤ u)
    (hv : (y : WithTop ℚ) < v) : ((x + y : ℚ) : WithTop ℚ) < u + v := by
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

/-- `e(f³) = 3 e(f)`. -/
private theorem orderTop_pow_three {f : Ser} {e : ℚ} (h : f.orderTop = e) :
    (f ^ 3).orderTop = ((3 * e : ℚ) : WithTop ℚ) := by
  rw [pow_three', HahnSeries.orderTop_mul, HahnSeries.orderTop_mul, h, ← WithTop.coe_add,
    ← WithTop.coe_add]
  congr 1
  ring

/-- Positive masses are nonzero. -/
private theorem mass_ne_zero (hm : ∀ i, 0 < m i) (i : Fin n) : (m i : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (hm i).ne'

/-- A body that is not `z`-circled has `[z_k]_{−2} = 0`. -/
private theorem coeff_z_neg_two {G : Germ n m} {k : Fin n} (hk : ¬ G.zCircle k) :
    (G.z k).coeff (-2) = 0 := by
  by_contra h
  exact hk ((G.colZ.circle_iff_coeff k).mpr h)

/-- If `ζ_kl = −2` for all `l ≠ k`, then `b_k ≥ 2`: every term `W_kl` of the `w`-equation of `k` has exponent
`−(3ζ_kl + ω_kl)/2 = 3 − ω_kl/2 ≥ 2` by (O1). -/
private theorem two_le_orderTop_w (G : Germ n m) {k : Fin n} (h : ∀ l, l ≠ k → G.zeta k l = -2) :
    ((2 : ℚ) : WithTop ℚ) ≤ (G.w k).orderTop := by
  rw [G.body_w k]
  refine le_orderTop_sum _ _ fun l hl => le_trans ?_ (le_orderTop_cS_mul _ _)
  have hlk : l ≠ k := Finset.ne_of_mem_erase hl
  rw [G.orderTop_termZ_w hlk.symm, h l hlk]
  have h2 := (G.O1_le hlk.symm).2.1
  exact_mod_cast (show (2 : ℚ) ≤ -(3 * -2 + G.omega k l) / 2 by linarith)

/-- The equation of a body `o ∉ S` in a colour `h`, split along `S ∪ {o}` and its complement:
`h_o − Σ_{j∈S} m_j H_oj = Σ_{l∉S∪{o}} m_l H_ol`. -/
private theorem body_split {p : Fin n → Fin n → Ser} {h : Fin n → Ser}
    (hb : ∀ k, h k = ∑ l ∈ univ.erase k, cS (m l) * termZ p h k l) (S : Finset (Fin n)) {o : Fin n}
    (ho : o ∉ S) :
    h o - ∑ j ∈ S, cS (m j) * termZ p h o j = ∑ l ∈ (insert o S)ᶜ, cS (m l) * termZ p h o l := by
  rw [Germ.body_univ hb o, ← Finset.sum_add_sum_compl (insert o S), Finset.sum_insert ho,
    Germ.termZ_self, mul_zero, zero_add]
  ring

/-! ## Lemma 6.1 (`lem:common`) -/

/-- **Lemma 6.1 (F1)** (`lem:common`), colour `z`: let `A` be a set of bodies whose pairs are all `z`-strokes, such
that `A` contains a `z`-circled body and every `z`-circled body lies in `A`. Then `ζ_kl = −2`, `ω_kl = 2` and
`x_kl = 0` for all pairs `kl` in `A`. (The paper also assumes that `A` has two, three or four bodies and that no pair
of `A` is a `zw`-edge; the proof uses neither.) -/
theorem F1_z (hm : ∀ i, 0 < m i) (G : Germ n m) {A : Finset (Fin n)}
    (hz : ∀ k ∈ A, ∀ l ∈ A, k ≠ l → G.zStroke k l) (hc : ∃ k ∈ A, G.zCircle k)
    (hcA : ∀ k, G.zCircle k → k ∈ A) {k l : Fin n} (hk : k ∈ A) (hl : l ∈ A) (hkl : k ≠ l) :
    G.zeta k l = -2 ∧ G.omega k l = 2 ∧ G.x k l = 0 := by
  -- (O3): `ζ = 3x − 2`, `ω = 2 − x` and `x ≥ 0` on the `z`-stroke `kl`
  obtain ⟨hζ, hω, hx0, -⟩ := G.O3_z (hz k hk l hl hkl)
  suffices hx : G.x k l = 0 from ⟨by linarith, by linarith, hx⟩
  obtain ⟨c, hcA', hcc⟩ := hc
  have hS : ∀ k ∈ A, ∀ l ∈ A, k ≠ l → G.edge k l := fun k hk l hl hkl => Or.inl (hz k hk l hl hkl)
  by_contra hx
  -- if `x > 0`, then `ζ > −2` on the pairs of `A`, which have one `ζ` by (E3)
  have hlt : -2 < G.zeta k l := by
    have : 0 < G.x k l := lt_of_le_of_ne hx0 (Ne.symm hx)
    linarith
  -- so all bodies of `A` have the coefficient `[z_c]_{−2} ≠ 0` at exponent `−2`
  have hsame : ∀ j ∈ A, (G.z j).coeff (-2) = (G.z c).coeff (-2) := by
    intro j hj
    by_cases hjc : j = c
    · rw [hjc]
    · have h1 : -2 < G.zeta j c := by
        rw [(G.edges_clique hS hj hcA' hk hl hjc hkl).1]
        exact hlt
      have h0 : (G.z j - G.z c).coeff (-2) = 0 :=
        Ser.coeff_eq_zero_of_lt (by rw [G.orderTop_z_sub hjc]; exact_mod_cast h1)
      rwa [Ser.coeff_sub, sub_eq_zero] at h0
  -- the bodies outside `A` are not circled
  have hzero : ∀ j ∉ A, (G.z j).coeff (-2) = 0 := fun j hj => coeff_z_neg_two fun h => hj (hcA j h)
  -- the centre of mass at exponent `−2` gives `(Σ_{j∈A} m_j) [z_c]_{−2} = 0`
  have hcom := initial_coeff G.com_z (-2)
  rw [← Finset.sum_add_sum_compl A] at hcom
  have h2 : ∑ i ∈ Aᶜ, (m i : ℂ) * (G.z i).coeff (-2) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hzero i (Finset.mem_compl.mp hi), mul_zero]
  have h1 : ∑ i ∈ A, (m i : ℂ) * (G.z i).coeff (-2) = (∑ i ∈ A, (m i : ℂ)) * (G.z c).coeff (-2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [hsame i hi]
  rw [h1, h2, add_zero] at hcom
  have hne : ∑ i ∈ A, (m i : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_ne_zero.mpr (Finset.sum_pos (fun i _ => hm i) ⟨c, hcA'⟩).ne'
  exact mul_ne_zero hne ((G.colZ.circle_iff_coeff c).mp hcc) hcom

/-- **Lemma 6.1 (F1)** (`lem:common`), colour `w`: let `A` be a set of bodies whose pairs are all `w`-strokes, such
that `A` contains a `w`-circled body and every `w`-circled body lies in `A`. Then `ω_kl = −2`, `ζ_kl = 2` and
`x_kl = 0` for all pairs `kl` in `A`. -/
theorem F1_w (hm : ∀ i, 0 < m i) (G : Germ n m) {A : Finset (Fin n)}
    (hw : ∀ k ∈ A, ∀ l ∈ A, k ≠ l → G.wStroke k l) (hc : ∃ k ∈ A, G.wCircle k)
    (hcA : ∀ k, G.wCircle k → k ∈ A) {k l : Fin n} (hk : k ∈ A) (hl : l ∈ A) (hkl : k ≠ l) :
    G.omega k l = -2 ∧ G.zeta k l = 2 ∧ G.x k l = 0 :=
  F1_z hm G.swap hw hc hcA hk hl hkl

/-- **Lemma 6.1 (F2)** (`lem:common`), colour `z`: in the situation of (F1), every `z`-circled body `k` has
`b_k ≥ 2`. -/
theorem F2_z (hm : ∀ i, 0 < m i) (G : Germ n m) {A : Finset (Fin n)}
    (hz : ∀ k ∈ A, ∀ l ∈ A, k ≠ l → G.zStroke k l) (hcA : ∀ k, G.zCircle k → k ∈ A) {k : Fin n}
    (hk : G.zCircle k) : ((2 : ℚ) : WithTop ℚ) ≤ (G.w k).orderTop := by
  -- `ζ_kl = −2` for all `l ≠ k`: by (F1) for `l ∈ A`, by (O6) for `l ∉ A`
  refine two_le_orderTop_w G fun l hlk => ?_
  by_cases hl : l ∈ A
  · exact (F1_z hm G hz ⟨k, hcA k hk, hk⟩ hcA (hcA k hk) hl (Ne.symm hlk)).1
  · exact G.O6_z hk fun h => hl (hcA l h)

/-- **Lemma 6.1 (F2)** (`lem:common`), colour `w`: in the situation of (F1) for the colour `w`, every `w`-circled
body `k` has `a_k ≥ 2`. -/
theorem F2_w (hm : ∀ i, 0 < m i) (G : Germ n m) {A : Finset (Fin n)}
    (hw : ∀ k ∈ A, ∀ l ∈ A, k ≠ l → G.wStroke k l) (hcA : ∀ k, G.wCircle k → k ∈ A) {k : Fin n}
    (hk : G.wCircle k) : ((2 : ℚ) : WithTop ℚ) ≤ (G.z k).orderTop :=
  F2_z hm G.swap hw hcA hk

/-- **Lemma 6.1 (F3)** (`lem:common`), colour `z`: if `kl` is a `w`-stroke with `x_kl = 0`, then
`a_k ≥ min(a_l, 2)`, since `z_k = z_l + z_kl` and `ζ_kl = 2` by (O3). -/
theorem F3_z (G : Germ n m) {k l : Fin n} (hs : G.wStroke k l) (hx : G.x k l = 0) :
    min (G.z l).orderTop ((2 : ℚ) : WithTop ℚ) ≤ (G.z k).orderTop := by
  have hζ : G.zeta k l = 2 := by
    have h := (G.O3_w hs).2.1
    linarith
  calc min (G.z l).orderTop ((2 : ℚ) : WithTop ℚ) = min (G.z l).orderTop (G.z k - G.z l).orderTop := by
        rw [G.orderTop_z_sub hs.1, hζ]
    _ ≤ (G.z l + (G.z k - G.z l)).orderTop := HahnSeries.min_orderTop_le_orderTop_add
    _ = (G.z k).orderTop := by
        congr 1
        ring

/-- **Lemma 6.1 (F3)** (`lem:common`), colour `w`: if `kl` is a `z`-stroke with `x_kl = 0`, then
`b_k ≥ min(b_l, 2)`. -/
theorem F3_w (G : Germ n m) {k l : Fin n} (hs : G.zStroke k l) (hx : G.x k l = 0) :
    min (G.w l).orderTop ((2 : ℚ) : WithTop ℚ) ≤ (G.w k).orderTop :=
  F3_z G.swap hs hx

/-- **Lemma 6.1 (F4)** (`lem:common`), colour `z`, first part: if `a_j < a_l` and `b_l < b_j`, then `ζ_jl = a_j`,
`ω_jl = b_l`, `lc(z_jl) = ẑ_j`, `lc(w_jl) = −ŵ_l`, `e(p_jl) = −(a_j + b_l)/2` and `p̂_jl² ẑ_j ŵ_l = −1`. The exponents
`a = a_j` and `b = b_l` are finite since `a_j < a_l` and `b_l < b_j`. -/
theorem F4_z (G : Germ n m) {j l : Fin n} {a b : ℚ} (ha : (G.z j).orderTop = a)
    (hb : (G.w l).orderTop = b) (hal : (a : WithTop ℚ) < (G.z l).orderTop)
    (hbj : (b : WithTop ℚ) < (G.w j).orderTop) :
    G.zeta j l = a ∧ G.omega j l = b ∧ (G.z j - G.z l).leadingCoeff = (G.z j).leadingCoeff ∧
      (G.w j - G.w l).leadingCoeff = -(G.w l).leadingCoeff ∧
      (G.p j l).orderTop = ((-((a + b) / 2) : ℚ) : WithTop ℚ) ∧
      (G.p j l).leadingCoeff ^ 2 * (G.z j).leadingCoeff * (G.w l).leadingCoeff = -1 := by
  have hz : (G.z j).orderTop < (G.z l).orderTop := by rw [ha]; exact hal
  have hw : (G.w l).orderTop < (G.w j).orderTop := by rw [hb]; exact hbj
  have hjl : j ≠ l := by
    rintro rfl
    exact lt_irrefl _ hz
  have hζ : G.zeta j l = a := by
    have h1 := G.zeta_eq_min hjl hz.ne
    rw [min_eq_left hz.le, ha] at h1
    exact_mod_cast h1
  have hω : G.omega j l = b := by
    have h1 := G.omega_eq_min hjl hw.ne'
    rw [min_eq_right hw.le, hb] at h1
    exact_mod_cast h1
  have hlz : (G.z j - G.z l).leadingCoeff = (G.z j).leadingCoeff := HahnSeries.leadingCoeff_sub hz
  have hlw : (G.w j - G.w l).leadingCoeff = -(G.w l).leadingCoeff := by
    rw [← neg_sub, HahnSeries.leadingCoeff_neg, HahnSeries.leadingCoeff_sub hw]
  refine ⟨hζ, hω, hlz, hlw, by rw [G.orderTop_p hjl, G.x_eq hjl, hζ, hω], ?_⟩
  -- the distance equation `p_jl² z_jl w_jl = 1` at its leading coefficient
  have hd := congrArg HahnSeries.leadingCoeff (G.dist j l hjl)
  rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_mul, Ser.leadingCoeff_pow, hlz, hlw,
    HahnSeries.leadingCoeff_one] at hd
  linear_combination -hd

/-- **Lemma 6.1 (F4)** (`lem:common`), colour `z`, second part: if `a_j < a_l`, `b_l < b_j` and moreover
`a_l + b_j > a_j + b_l`, the term `m_j m_l p_jl³ (z_j w_l − z_l w_j)` of the pair `jl` in a torque has exponent
`−(a_j + b_l)/2` and leading coefficient `−m_j m_l p̂_jl`. -/
theorem F4_z_term (hm : ∀ i, 0 < m i) (G : Germ n m) {j l : Fin n} {a b : ℚ}
    (ha : (G.z j).orderTop = a) (hb : (G.w l).orderTop = b) (hal : (a : WithTop ℚ) < (G.z l).orderTop)
    (hbj : (b : WithTop ℚ) < (G.w j).orderTop)
    (hs : ((a + b : ℚ) : WithTop ℚ) < (G.z l).orderTop + (G.w j).orderTop) :
    (cS (m j) * cS (m l) * (G.p j l ^ 3 * (G.z j * G.w l - G.z l * G.w j))).orderTop =
        ((-((a + b) / 2) : ℚ) : WithTop ℚ) ∧
      (cS (m j) * cS (m l) * (G.p j l ^ 3 * (G.z j * G.w l - G.z l * G.w j))).leadingCoeff =
        -((m j : ℂ) * (m l : ℂ) * (G.p j l).leadingCoeff) := by
  obtain ⟨-, -, -, -, hp, hc⟩ := F4_z G ha hb hal hbj
  have hp3 := orderTop_pow_three hp
  -- the term `p_jl³ z_j w_l` has exponent `3 e(p_jl) + a_j + b_l = −(a_j + b_l)/2` and coefficient
  -- `p̂_jl³ ẑ_j ŵ_l = −p̂_jl`
  have h1o : (G.p j l ^ 3 * (G.z j * G.w l)).orderTop = ((-((a + b) / 2) : ℚ) : WithTop ℚ) := by
    rw [HahnSeries.orderTop_mul, HahnSeries.orderTop_mul, hp3, ha, hb, ← WithTop.coe_add,
      ← WithTop.coe_add]
    congr 1
    ring
  have h1c : (G.p j l ^ 3 * (G.z j * G.w l)).leadingCoeff = -(G.p j l).leadingCoeff := by
    rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_mul, Ser.leadingCoeff_pow]
    linear_combination (G.p j l).leadingCoeff * hc
  -- the term `p_jl³ z_l w_j` has the larger exponent `3 e(p_jl) + a_l + b_j`
  have h2o : (G.p j l ^ 3 * (G.z j * G.w l)).orderTop < (G.p j l ^ 3 * (G.z l * G.w j)).orderTop := by
    rw [h1o, HahnSeries.orderTop_mul, HahnSeries.orderTop_mul,
      show (-((a + b) / 2) : ℚ) = 3 * -((a + b) / 2) + (a + b) by ring]
    exact coe_add_lt hp3.ge hs
  have hmm : (m j : ℂ) * (m l : ℂ) ≠ 0 := mul_ne_zero (mass_ne_zero hm j) (mass_ne_zero hm l)
  rw [mul_sub, ← cS_mul]
  refine ⟨?_, ?_⟩
  · rw [Ser.orderTop_cS_mul hmm, HahnSeries.orderTop_sub h2o, h1o]
  · rw [Ser.leadingCoeff_cS_mul, HahnSeries.leadingCoeff_sub h2o, h1c]
    ring

/-- **Lemma 6.1 (F4)** (`lem:common`), colour `w`, first part: if `b_j < b_l` and `a_l < a_j`, then `ω_jl = b_j`,
`ζ_jl = a_l`, `lc(w_jl) = ŵ_j`, `lc(z_jl) = −ẑ_l`, `e(p_jl) = −(b_j + a_l)/2` and `p̂_jl² ŵ_j ẑ_l = −1`. -/
theorem F4_w (G : Germ n m) {j l : Fin n} {b a : ℚ} (hb : (G.w j).orderTop = b)
    (ha : (G.z l).orderTop = a) (hbl : (b : WithTop ℚ) < (G.w l).orderTop)
    (haj : (a : WithTop ℚ) < (G.z j).orderTop) :
    G.omega j l = b ∧ G.zeta j l = a ∧ (G.w j - G.w l).leadingCoeff = (G.w j).leadingCoeff ∧
      (G.z j - G.z l).leadingCoeff = -(G.z l).leadingCoeff ∧
      (G.p j l).orderTop = ((-((b + a) / 2) : ℚ) : WithTop ℚ) ∧
      (G.p j l).leadingCoeff ^ 2 * (G.w j).leadingCoeff * (G.z l).leadingCoeff = -1 :=
  F4_z G.swap hb ha hbl haj

/-- **Lemma 6.1 (F4)** (`lem:common`), colour `w`, second part: if `b_j < b_l`, `a_l < a_j` and moreover
`b_l + a_j > b_j + a_l`, the term `m_j m_l p_jl³ (w_j z_l − w_l z_j)` has exponent `−(b_j + a_l)/2` and leading
coefficient `−m_j m_l p̂_jl`. -/
theorem F4_w_term (hm : ∀ i, 0 < m i) (G : Germ n m) {j l : Fin n} {b a : ℚ}
    (hb : (G.w j).orderTop = b) (ha : (G.z l).orderTop = a) (hbl : (b : WithTop ℚ) < (G.w l).orderTop)
    (haj : (a : WithTop ℚ) < (G.z j).orderTop)
    (hs : ((b + a : ℚ) : WithTop ℚ) < (G.w l).orderTop + (G.z j).orderTop) :
    (cS (m j) * cS (m l) * (G.p j l ^ 3 * (G.w j * G.z l - G.w l * G.z j))).orderTop =
        ((-((b + a) / 2) : ℚ) : WithTop ℚ) ∧
      (cS (m j) * cS (m l) * (G.p j l ^ 3 * (G.w j * G.z l - G.w l * G.z j))).leadingCoeff =
        -((m j : ℂ) * (m l : ℂ) * (G.p j l).leadingCoeff) :=
  F4_z_term hm G.swap hb ha hbl haj hs

/-! ## Lemma 6.2 (`lem:rewrite`) -/

/-- **Lemma 6.2** (`lem:rewrite`), the sums `B_z` and `B_w`: for a set `S` of bodies and a body `o ∉ S`, with
`A_z = Σ_{j∈S} m_j Z_oj` and `A_w = Σ_{j∈S} m_j W_oj`, the equations of the body `o` give
`B_z = z_o − A_z = Σ_{l∉S∪{o}} m_l Z_ol` and `B_w = w_o − A_w = Σ_{l∉S∪{o}} m_l W_ol`. -/
theorem rewrite_B (G : Germ n m) (S : Finset (Fin n)) {o : Fin n} (ho : o ∉ S) :
    G.z o - ∑ j ∈ S, cS (m j) * termZ G.p G.z o j = ∑ l ∈ (insert o S)ᶜ, cS (m l) * termZ G.p G.z o l ∧
      G.w o - ∑ j ∈ S, cS (m j) * termZ G.p G.w o j = ∑ l ∈ (insert o S)ᶜ, cS (m l) * termZ G.p G.w o l :=
  ⟨body_split G.body_z S ho, body_split G.body_w S ho⟩

/-- **Lemma 6.2** (`lem:rewrite`): for a set `S` of bodies and a body `o ∉ S`, with `A_z = Σ_{j∈S} m_j Z_oj`,
`A_w = Σ_{j∈S} m_j W_oj`, `B_z = Σ_{l∉S∪{o}} m_l Z_ol` and `B_w = Σ_{l∉S∪{o}} m_l W_ol` (so that `B_z = z_o − A_z`
and `B_w = w_o − A_w` by the equations of the body `o`, `rewrite_B`),
`Σ_{j∈S} m_j m_o p_jo³ (z_j w_o − z_o w_j) = m_o (z_o A_w − w_o A_z) = m_o (w_o B_z − z_o B_w)`. -/
theorem rewrite_sum (G : Germ n m) (S : Finset (Fin n)) {o : Fin n} (ho : o ∉ S) :
    ∑ j ∈ S, cS (m j) * cS (m o) * (G.p j o ^ 3 * (G.z j * G.w o - G.z o * G.w j)) =
        cS (m o) * (G.z o * ∑ j ∈ S, cS (m j) * termZ G.p G.w o j -
          G.w o * ∑ j ∈ S, cS (m j) * termZ G.p G.z o j) ∧
      cS (m o) * (G.z o * ∑ j ∈ S, cS (m j) * termZ G.p G.w o j -
          G.w o * ∑ j ∈ S, cS (m j) * termZ G.p G.z o j) =
        cS (m o) * (G.w o * ∑ l ∈ (insert o S)ᶜ, cS (m l) * termZ G.p G.z o l -
          G.z o * ∑ l ∈ (insert o S)ᶜ, cS (m l) * termZ G.p G.w o l) := by
  obtain ⟨hBz, hBw⟩ := rewrite_B G S ho
  refine ⟨?_, ?_⟩
  · -- `p_jo³ z_j = p_jo³ z_o − Z_oj` and `p_jo³ w_j = p_jo³ w_o − W_oj`; the terms `p_jo³ z_o w_o` cancel
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [termZ, G.p_symm o j]
    ring
  · -- `A_z = z_o − B_z` and `A_w = w_o − B_w`
    rw [← hBz, ← hBw]
    ring

/-! ## Lemma 6.3 (`lem:binary`) -/

/-- **Lemma 6.3** (`lem:binary`), colour `z`, the relation `m_i ẑ_i + m_{i'} ẑ_{i'} = 0` when `i` and `i'` are the
only `z`-circled bodies: it is the coefficient of exponent `−2` in `Σ_j m_j z_j = 0`. -/
theorem binary_com_z (G : Germ n m) {i i' : Fin n} (hii' : i ≠ i') (hi : G.zCircle i)
    (hi' : G.zCircle i') (honly : ∀ j, G.zCircle j → j = i ∨ j = i') :
    (m i : ℂ) * (G.z i).leadingCoeff + (m i' : ℂ) * (G.z i').leadingCoeff = 0 := by
  have hcom := initial_coeff G.com_z (-2)
  have h0 : ∀ j ∈ (univ : Finset (Fin n)), j ≠ i ∧ j ≠ i' → (m j : ℂ) * (G.z j).coeff (-2) = 0 := by
    intro j _ hj
    rw [coeff_z_neg_two fun h => (honly j h).elim hj.1 hj.2, mul_zero]
  rw [Finset.sum_eq_add_of_mem i i' (Finset.mem_univ i) (Finset.mem_univ i') hii' h0,
    Ser.coeff_of_orderTop_eq hi, Ser.coeff_of_orderTop_eq hi'] at hcom
  exact hcom

/-- **Lemma 6.3** (`lem:binary`), colour `w`, the relation `m_i ŵ_i + m_{i'} ŵ_{i'} = 0` when `i` and `i'` are the
only `w`-circled bodies. -/
theorem binary_com_w (G : Germ n m) {i i' : Fin n} (hii' : i ≠ i') (hi : G.wCircle i)
    (hi' : G.wCircle i') (honly : ∀ j, G.wCircle j → j = i ∨ j = i') :
    (m i : ℂ) * (G.w i).leadingCoeff + (m i' : ℂ) * (G.w i').leadingCoeff = 0 :=
  binary_com_z G.swap hii' hi hi' honly

/-- **Lemma 6.3** (`lem:binary`), colour `z`, for any two distinct bodies `i`, `i'` in place of `5`, `6`: if `i` and
`i'` are the only `z`-circled bodies and a body `k` satisfies `a_k > −2` and `b_k < min(b_i, b_{i'})`, then
`m_i p̂_ik + m_{i'} p̂_{i'k} ≠ 0`. -/
theorem binary_z (hm : ∀ i, 0 < m i) (G : Germ n m) {i i' k : Fin n} (hii' : i ≠ i') (hi : G.zCircle i)
    (hi' : G.zCircle i') (honly : ∀ j, G.zCircle j → j = i ∨ j = i')
    (hak : ((-2 : ℚ) : WithTop ℚ) < (G.z k).orderTop)
    (hbk : (G.w k).orderTop < min (G.w i).orderTop (G.w i').orderTop) :
    (m i : ℂ) * (G.p i k).leadingCoeff + (m i' : ℂ) * (G.p i' k).leadingCoeff ≠ 0 := by
  have hb : (G.w k).orderTop = ((G.w k).order : WithTop ℚ) :=
    Ser.orderTop_eq_order (HahnSeries.orderTop_ne_top.1 hbk.ne_top)
  -- (F4) for the pairs `(j, k)`, `j = i, i'`: `p̂_jk² ẑ_j ŵ_k = −1`
  have hF : ∀ j, G.zCircle j → (G.w k).orderTop < (G.w j).orderTop →
      (G.p j k).leadingCoeff ^ 2 * (G.z j).leadingCoeff * (G.w k).leadingCoeff = -1 := by
    intro j hj hbj
    exact (F4_z G hj hb hak (by rw [← hb]; exact hbj)).2.2.2.2.2
  have h1 := hF i hi (lt_of_lt_of_le hbk (min_le_left _ _))
  have h2 := hF i' hi' (lt_of_lt_of_le hbk (min_le_right _ _))
  have h3 := binary_com_z G hii' hi hi' honly
  have hX : (G.z i).leadingCoeff ≠ 0 :=
    HahnSeries.leadingCoeff_ne_zero.mpr (Ser.ne_zero_of_orderTop_eq hi)
  have hM : (m i : ℂ) ^ 3 + (m i' : ℂ) ^ 3 ≠ 0 := by
    have h : ((m i ^ 3 + m i' ^ 3 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (add_pos (pow_pos (hm i) 3) (pow_pos (hm i') 3)).ne'
    push_cast at h
    exact h
  -- if `m_i p̂_ik = −m_{i'} p̂_{i'k}`, squaring gives `m_i² / ẑ_i = m_{i'}² / ẑ_{i'}`, and with
  -- `m_{i'} ẑ_{i'} = −m_i ẑ_i` this gives `(m_i³ + m_{i'}³) ẑ_i = 0`
  intro h4
  apply mul_ne_zero hM hX
  linear_combination (m i : ℂ) ^ 2 * h3 + (m i' : ℂ) * ((m i : ℂ) * (G.p i k).leadingCoeff -
      (m i' : ℂ) * (G.p i' k).leadingCoeff) * (G.z i).leadingCoeff * (G.z i').leadingCoeff *
      (G.w k).leadingCoeff * h4 - (m i : ℂ) ^ 2 * (m i' : ℂ) * (G.z i').leadingCoeff * h1 +
      (m i' : ℂ) ^ 3 * (G.z i).leadingCoeff * h2

/-- **Lemma 6.3** (`lem:binary`), colour `w`, for any two distinct bodies `i`, `i'`: if `i` and `i'` are the only
`w`-circled bodies and a body `k` satisfies `b_k > −2` and `a_k < min(a_i, a_{i'})`, then
`m_i p̂_ik + m_{i'} p̂_{i'k} ≠ 0`. -/
theorem binary_w (hm : ∀ i, 0 < m i) (G : Germ n m) {i i' k : Fin n} (hii' : i ≠ i') (hi : G.wCircle i)
    (hi' : G.wCircle i') (honly : ∀ j, G.wCircle j → j = i ∨ j = i')
    (hbk : ((-2 : ℚ) : WithTop ℚ) < (G.w k).orderTop)
    (hak : (G.z k).orderTop < min (G.z i).orderTop (G.z i').orderTop) :
    (m i : ℂ) * (G.p i k).leadingCoeff + (m i' : ℂ) * (G.p i' k).leadingCoeff ≠ 0 :=
  binary_z hm G.swap hii' hi hi' honly hbk hak

end Six

end

end CC6Full
