import CC6Full.Germ.Basic

/-!
# Coefficients and initial forms (Lemma 2.10, `lem:initial`)

Paper §2.2 and §2.3. For a series `f : Ser` the exponent `e(f)` of the paper is `f.orderTop` (or `f.order` for
`f ≠ 0`), the coefficient `[f]_e` of `τ^e` is `f.coeff e`, and the leading coefficient `[f]_{e(f)}` is
`f.leadingCoeff`.

## Coefficients (§2.2)

* `Ser.coeff_eq_zero_of_lt`, `Ser.coeff_eq_zero_of_lt_order`: `[f]_e = 0` for `e < e(f)`.
* `Ser.coeff_of_orderTop_eq`: `[f]_{e(f)}` is the leading coefficient.
* `Ser.coeff_add`, `Ser.coeff_sub`, `Ser.coeff_sum`, `Ser.coeff_cS_mul`: `[f + g]_e = [f]_e + [g]_e`, and the
  coefficients are `ℂ`-linear.
* `Ser.coeff_mul_of_le`: `[fg]_{e+e'} = [f]_e [g]_{e'}` for `e ≤ e(f)`, `e' ≤ e(g)`; `Ser.coeff_prod_of_le` and
  `Ser.coeff_pow_of_le` for products of several factors, with `Ser.orderTop_prod`, `Ser.leadingCoeff_prod`,
  `Ser.orderTop_pow`, `Ser.leadingCoeff_pow`: the exponent of a product is the sum of the exponents of its factors,
  and its leading coefficient is the product of their leading coefficients.
* `Ser.orderTop_cS_mul`, `Ser.order_cS_mul`, `Ser.leadingCoeff_cS_mul`: a nonzero constant factor does not change
  the order.

## Lemma 2.10 (`lem:initial`)

An identity `Σ_{i ∈ s} c_i g_i = 0` in `Ser` with complex coefficients `c_i` (written `cS (c i) * g i`):

* `initial_coeff`: `Σ_i c_i [g_i]_e = 0` for every `e`.
* `initial_sum_filter`: if `e ≤ e(g_i)` for all `i`, then `Σ_{e(g_i) = e} c_i lc(g_i) = 0`.
* `initial_not_unique_min`: there is no index `i₀` with `c_{i₀} ≠ 0`, `g_{i₀} ≠ 0` whose exponent is smaller than
  the exponents of all other terms.
* `initial` (with `order`) and `initial_orderTop` (with `orderTop`): if `s` is nonempty and all `c_i`, `g_i` are
  nonzero, the least exponent `e₀` of the terms is attained by at least two terms, and the initial form
  `Σ_{e(g_i) = e₀} c_i lc(g_i)` vanishes.
-/

namespace CC6Full

open Finset

noncomputable section

/-! ## Constants -/

theorem cS_mul (a b : ℂ) : cS (a * b) = cS a * cS b := map_mul HahnSeries.C a b

theorem cS_add (a b : ℂ) : cS (a + b) = cS a + cS b := map_add HahnSeries.C a b

theorem cS_sub (a b : ℂ) : cS (a - b) = cS a - cS b := map_sub HahnSeries.C a b

theorem cS_neg (a : ℂ) : cS (-a) = -cS a := map_neg HahnSeries.C a

theorem cS_pow (a : ℂ) (k : ℕ) : cS (a ^ k) = cS a ^ k := map_pow HahnSeries.C a k

theorem cS_one : cS 1 = 1 := map_one HahnSeries.C

theorem cS_zero : cS 0 = 0 := map_zero HahnSeries.C

theorem cS_two : cS 2 = 2 := map_ofNat HahnSeries.C 2

theorem cS_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) : cS (∑ i ∈ s, a i) = ∑ i ∈ s, cS (a i) :=
  map_sum HahnSeries.C a s

theorem cS_ne_zero {a : ℂ} (ha : a ≠ 0) : cS a ≠ 0 := HahnSeries.C_ne_zero ha

theorem cS_inv_mul_cancel {a : ℂ} (ha : a ≠ 0) : cS a⁻¹ * cS a = 1 := by
  rw [← cS_mul, inv_mul_cancel₀ ha, cS_one]

theorem two_ne_zero_ser : (2 : Ser) ≠ 0 := by
  rw [← cS_two]
  exact cS_ne_zero two_ne_zero

namespace Ser

/-! ## Coefficients -/

/-- `[f]_e = 0` below the exponent. -/
theorem coeff_eq_zero_of_lt {f : Ser} {e : ℚ} (h : (e : WithTop ℚ) < f.orderTop) : f.coeff e = 0 :=
  HahnSeries.coeff_eq_zero_of_lt_orderTop h

theorem coeff_eq_zero_of_lt_order {f : Ser} {e : ℚ} (h : e < f.order) : f.coeff e = 0 :=
  HahnSeries.coeff_eq_zero_of_lt_order h

theorem orderTop_eq_order {f : Ser} (hf : f ≠ 0) : f.orderTop = (f.order : WithTop ℚ) :=
  (HahnSeries.order_eq_orderTop_of_ne_zero hf).symm

theorem ne_zero_of_orderTop_eq {f : Ser} {e : ℚ} (h : f.orderTop = e) : f ≠ 0 := by
  rintro rfl
  simp at h

theorem order_eq_of_orderTop_eq {f : Ser} {e : ℚ} (h : f.orderTop = e) : f.order = e := by
  have h' := orderTop_eq_order (ne_zero_of_orderTop_eq h)
  rw [h] at h'
  exact (WithTop.coe_inj.mp h').symm

/-- `[f]_{e(f)}` is the leading coefficient. -/
theorem coeff_of_orderTop_eq {f : Ser} {e : ℚ} (h : f.orderTop = e) : f.coeff e = f.leadingCoeff := by
  rw [HahnSeries.leadingCoeff_eq, order_eq_of_orderTop_eq h]

/-- At a lower bound `e` of the exponent, `[f]_e` is the leading coefficient if `e(f) = e` and `0` otherwise. -/
theorem coeff_eq_ite_of_le {f : Ser} {e : ℚ} (he : (e : WithTop ℚ) ≤ f.orderTop) :
    f.coeff e = if f.orderTop = e then f.leadingCoeff else 0 := by
  split_ifs with h
  · exact coeff_of_orderTop_eq h
  · exact coeff_eq_zero_of_lt (lt_of_le_of_ne he (Ne.symm h))

theorem coeff_add (f g : Ser) (e : ℚ) : (f + g).coeff e = f.coeff e + g.coeff e :=
  HahnSeries.coeff_add

theorem coeff_sub (f g : Ser) (e : ℚ) : (f - g).coeff e = f.coeff e - g.coeff e :=
  HahnSeries.coeff_sub

theorem coeff_neg (f : Ser) (e : ℚ) : (-f).coeff e = -f.coeff e :=
  HahnSeries.coeff_neg

theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Ser) (e : ℚ) :
    (∑ i ∈ s, f i).coeff e = ∑ i ∈ s, (f i).coeff e :=
  HahnSeries.coeff_sum e

theorem coeff_cS_mul (a : ℂ) (f : Ser) (e : ℚ) : (cS a * f).coeff e = a * f.coeff e := by
  show (HahnSeries.C a * f).coeff e = a * f.coeff e
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem coeff_cS (a : ℂ) (e : ℚ) : (cS a).coeff e = if e = 0 then a else 0 := by
  show (HahnSeries.C a).coeff e = _
  rw [HahnSeries.C_apply]
  split_ifs with h
  · rw [h, HahnSeries.coeff_single_same]
  · exact HahnSeries.coeff_single_of_ne h

/-- The coefficients of a linear combination with constant coefficients. -/
theorem coeff_sum_cS_mul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → Ser) (e : ℚ) :
    (∑ i ∈ s, cS (c i) * g i).coeff e = ∑ i ∈ s, c i * (g i).coeff e := by
  rw [coeff_sum]
  exact Finset.sum_congr rfl fun i _ => coeff_cS_mul _ _ _

theorem orderTop_cS {a : ℂ} (ha : a ≠ 0) : (cS a).orderTop = 0 := by
  show (HahnSeries.C a).orderTop = 0
  rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha, WithTop.coe_zero]

theorem order_cS (a : ℂ) : (cS a).order = 0 := HahnSeries.order_C

theorem leadingCoeff_cS (a : ℂ) : (cS a).leadingCoeff = a := by
  show (HahnSeries.C a).leadingCoeff = a
  rw [HahnSeries.C_apply, HahnSeries.leadingCoeff_of_single]

/-- A nonzero constant factor does not change the exponent. -/
theorem orderTop_cS_mul {a : ℂ} (ha : a ≠ 0) (f : Ser) : (cS a * f).orderTop = f.orderTop := by
  rw [HahnSeries.orderTop_mul, orderTop_cS ha, zero_add]

theorem order_cS_mul {a : ℂ} (ha : a ≠ 0) (f : Ser) : (cS a * f).order = f.order := by
  by_cases hf : f = 0
  · rw [hf, mul_zero]
  rw [HahnSeries.order_mul (cS_ne_zero ha) hf, order_cS, zero_add]

theorem leadingCoeff_cS_mul (a : ℂ) (f : Ser) : (cS a * f).leadingCoeff = a * f.leadingCoeff := by
  rw [HahnSeries.leadingCoeff_mul, leadingCoeff_cS]

/-- `[fg]_{e+e'} = [f]_e [g]_{e'}` for `e ≤ e(f)` and `e' ≤ e(g)`. -/
theorem coeff_mul_of_le {f g : Ser} {e e' : ℚ} (hf : (e : WithTop ℚ) ≤ f.orderTop)
    (hg : (e' : WithTop ℚ) ≤ g.orderTop) : (f * g).coeff (e + e') = f.coeff e * g.coeff e' := by
  by_cases hf0 : f = 0
  · simp [hf0]
  by_cases hg0 : g = 0
  · simp [hg0]
  have hfo := orderTop_eq_order hf0
  have hgo := orderTop_eq_order hg0
  have hfg : (f * g).orderTop = ((f.order + g.order : ℚ) : WithTop ℚ) := by
    rw [HahnSeries.orderTop_mul, hfo, hgo, WithTop.coe_add]
  rw [hfo, WithTop.coe_le_coe] at hf
  rw [hgo, WithTop.coe_le_coe] at hg
  rcases hf.lt_or_eq with hf' | rfl
  · rw [coeff_eq_zero_of_lt_order hf', zero_mul]
    apply coeff_eq_zero_of_lt
    rw [hfg, WithTop.coe_lt_coe]
    linarith
  rcases hg.lt_or_eq with hg' | rfl
  · rw [coeff_eq_zero_of_lt_order hg', mul_zero]
    apply coeff_eq_zero_of_lt
    rw [hfg, WithTop.coe_lt_coe]
    linarith
  rw [HahnSeries.coeff_mul_order_add_order, HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq]

/-- The exponent of a product is the sum of the exponents of the factors. -/
theorem orderTop_prod {ι : Type*} (s : Finset ι) (f : ι → Ser) :
    (∏ i ∈ s, f i).orderTop = ∑ i ∈ s, (f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, HahnSeries.orderTop_mul, ih]

/-- The leading coefficient of a product is the product of the leading coefficients of the factors. -/
theorem leadingCoeff_prod {ι : Type*} (s : Finset ι) (f : ι → Ser) :
    (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, HahnSeries.leadingCoeff_mul, ih]

/-- `[Π f_i]_{Σ e_i} = Π [f_i]_{e_i}` for `e_i ≤ e(f_i)`. -/
theorem coeff_prod_of_le {ι : Type*} (s : Finset ι) (f : ι → Ser) (e : ι → ℚ)
    (h : ∀ i ∈ s, (e i : WithTop ℚ) ≤ (f i).orderTop) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (f i).coeff (e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, (e i : WithTop ℚ) ≤ (f i).orderTop := fun i hi => h i (mem_insert_of_mem hi)
    have hle : ((∑ i ∈ s, e i : ℚ) : WithTop ℚ) ≤ (∏ i ∈ s, f i).orderTop := by
      rw [orderTop_prod, WithTop.coe_sum]
      exact Finset.sum_le_sum hs
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
      coeff_mul_of_le (h a (mem_insert_self a s)) hle, ih hs]

theorem orderTop_pow (f : Ser) (k : ℕ) : (f ^ k).orderTop = k • f.orderTop := by
  rw [← Finset.card_range k, ← Finset.prod_const, ← Finset.sum_const, orderTop_prod]

theorem leadingCoeff_pow (f : Ser) (k : ℕ) : (f ^ k).leadingCoeff = f.leadingCoeff ^ k := by
  rw [← Finset.card_range k, ← Finset.prod_const, ← Finset.prod_const, leadingCoeff_prod]

/-- `[f^k]_{k e} = [f]_e^k` for `e ≤ e(f)`. -/
theorem coeff_pow_of_le {f : Ser} {e : ℚ} (h : (e : WithTop ℚ) ≤ f.orderTop) (k : ℕ) :
    (f ^ k).coeff (k * e) = f.coeff e ^ k := by
  have := coeff_prod_of_le (Finset.range k) (fun _ => f) (fun _ => e) (fun _ _ => h)
  rw [Finset.prod_const, Finset.sum_const, Finset.card_range, Finset.prod_const, Finset.card_range,
    nsmul_eq_mul] at this
  exact this

end Ser

/-! ## Lemma 2.10 (`lem:initial`) -/

section initial

variable {ι : Type*} {s : Finset ι} {c : ι → ℂ} {g : ι → Ser}

/-- An identity `Σ_i c_i g_i = 0` gives `Σ_i c_i [g_i]_e = 0` for every `e`. -/
theorem initial_coeff (hsum : ∑ i ∈ s, cS (c i) * g i = 0) (e : ℚ) :
    ∑ i ∈ s, c i * (g i).coeff e = 0 := by
  rw [← Ser.coeff_sum_cS_mul, hsum, HahnSeries.coeff_zero]

/-- If all exponents are at least `e`, the terms of exponent `e` have a vanishing initial form:
`Σ_{e(g_i) = e} c_i lc(g_i) = 0`. -/
theorem initial_sum_filter (hsum : ∑ i ∈ s, cS (c i) * g i = 0) {e : ℚ}
    (he : ∀ i ∈ s, (e : WithTop ℚ) ≤ (g i).orderTop) :
    ∑ i ∈ s with (g i).orderTop = e, c i * (g i).leadingCoeff = 0 := by
  refine Eq.trans ?_ (initial_coeff hsum e)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Ser.coeff_eq_ite_of_le (he i hi)]
  split_ifs <;> simp

/-- A single term of least exponent is impossible: if `c_{i₀} ≠ 0`, `g_{i₀} ≠ 0` and every other term has a
larger exponent, the identity `Σ_i c_i g_i = 0` fails. -/
theorem initial_not_unique_min (hsum : ∑ i ∈ s, cS (c i) * g i = 0) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hc : c i₀ ≠ 0) (hg : g i₀ ≠ 0) (hmin : ∀ j ∈ s, j ≠ i₀ → (g i₀).orderTop < (g j).orderTop) : False := by
  have h0 := initial_coeff hsum (g i₀).order
  rw [Finset.sum_eq_single_of_mem i₀ hi₀, ← HahnSeries.leadingCoeff_eq] at h0
  · exact mul_ne_zero hc (HahnSeries.leadingCoeff_ne_zero.mpr hg) h0
  · intro j hj hji
    have h1 := hmin j hj hji
    rw [Ser.orderTop_eq_order hg] at h1
    rw [Ser.coeff_eq_zero_of_lt h1, mul_zero]

/-- **Lemma 2.10** (`lem:initial`), with exponents `orderTop`: if all `c_i` and `g_i` are nonzero, the least
exponent `e₀` of the terms is attained by at least two terms, and `Σ_{e(g_i) = e₀} c_i lc(g_i) = 0`. -/
theorem initial_orderTop (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hg : ∀ i ∈ s, g i ≠ 0)
    (hsum : ∑ i ∈ s, cS (c i) * g i = 0) :
    (∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ (g i).orderTop = s.inf' hs (fun i => (g i).orderTop) ∧
        (g j).orderTop = s.inf' hs (fun i => (g i).orderTop)) ∧
      ∑ i ∈ s with (g i).orderTop = s.inf' hs (fun i => (g i).orderTop), c i * (g i).leadingCoeff = 0 := by
  obtain ⟨i₀, hi₀s, hi₀⟩ := Finset.exists_mem_eq_inf' hs (fun i => (g i).orderTop)
  have hi₀' : s.inf' hs (fun i => (g i).orderTop) = (g i₀).orderTop := hi₀
  have hle : ∀ i ∈ s, s.inf' hs (fun i => (g i).orderTop) ≤ (g i).orderTop :=
    fun i hi => Finset.inf'_le _ hi
  refine ⟨?_, ?_⟩
  · by_contra H
    push Not at H
    refine initial_not_unique_min hsum hi₀s (hc i₀ hi₀s) (hg i₀ hi₀s) fun j hj hji => ?_
    rw [← hi₀']
    exact lt_of_le_of_ne (hle j hj) fun h => H i₀ hi₀s j hj (Ne.symm hji) hi₀'.symm h.symm
  · rw [hi₀', Ser.orderTop_eq_order (hg i₀ hi₀s)]
    refine initial_sum_filter hsum fun i hi => ?_
    rw [← Ser.orderTop_eq_order (hg i₀ hi₀s), ← hi₀']
    exact hle i hi

/-- **Lemma 2.10** (`lem:initial`): if all `c_i` and `g_i` are nonzero, the least order `e₀` of the terms is
attained by at least two terms, and `Σ_{ord g_i = e₀} c_i lc(g_i) = 0`. -/
theorem initial (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hg : ∀ i ∈ s, g i ≠ 0)
    (hsum : ∑ i ∈ s, cS (c i) * g i = 0) :
    (∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ (g i).order = s.inf' hs (fun i => (g i).order) ∧
        (g j).order = s.inf' hs (fun i => (g i).order)) ∧
      ∑ i ∈ s with (g i).order = s.inf' hs (fun i => (g i).order), c i * (g i).leadingCoeff = 0 := by
  obtain ⟨i₀, hi₀s, hi₀⟩ := Finset.exists_mem_eq_inf' hs (fun i => (g i).order)
  have hi₀' : s.inf' hs (fun i => (g i).order) = (g i₀).order := hi₀
  have hle : ∀ i ∈ s, s.inf' hs (fun i => (g i).order) ≤ (g i).order :=
    fun i hi => Finset.inf'_le _ hi
  have hot : ∀ i ∈ s, (g i).orderTop = ((g i).order : WithTop ℚ) :=
    fun i hi => Ser.orderTop_eq_order (hg i hi)
  refine ⟨?_, ?_⟩
  · by_contra H
    push Not at H
    refine initial_not_unique_min hsum hi₀s (hc i₀ hi₀s) (hg i₀ hi₀s) fun j hj hji => ?_
    rw [hot i₀ hi₀s, hot j hj, WithTop.coe_lt_coe, ← hi₀']
    exact lt_of_le_of_ne (hle j hj) fun h => H i₀ hi₀s j hj (Ne.symm hji) hi₀'.symm h.symm
  · rw [hi₀']
    have hfilter : ∑ i ∈ s with (g i).order = (g i₀).order, c i * (g i).leadingCoeff =
        ∑ i ∈ s with (g i).orderTop = ((g i₀).order : WithTop ℚ), c i * (g i).leadingCoeff := by
      refine Finset.sum_congr (Finset.filter_congr fun i hi => ?_) fun _ _ => rfl
      rw [hot i hi, WithTop.coe_inj]
    rw [hfilter]
    refine initial_sum_filter hsum fun i hi => ?_
    rw [hot i hi, WithTop.coe_le_coe, ← hi₀']
    exact hle i hi

end initial

end

end CC6Full
