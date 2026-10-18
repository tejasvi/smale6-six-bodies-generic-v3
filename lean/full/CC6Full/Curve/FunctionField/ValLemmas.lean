import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Two facts about discrete valuations

* `addVal_eq_of_nonneg_imp`: two `ℤ`-valued valuations of a field, both taking the value `1`, with the valuation ring
  of the second contained in that of the first, are equal (a discrete valuation ring is a maximal proper valuation
  subring). Proof: with `w₂(π) = 1`, every `x ≠ 0` is `π^n u` with `w₂(u) = 0`, so `w₁(u) = 0`, `w₁(x) = n w₁(π)`,
  and `w₁(π) = 1` because `w₁` takes the value `1`.
* `addVal_nonneg_of_isIntegral`: valuation rings are integrally closed.

Ported unchanged from the five-body formalization (`CC5Full/Theory/FunctionField/ValLemmas.lean`).
-/

namespace CC6Full

noncomputable section

section addval

variable {K : Type*} [Field K]

/-- The integer order of an element (`0` for `x = 0`). -/
def ordZ (w : AddValuation K (WithTop ℤ)) (x : K) : ℤ := WithTop.untopD 0 (w x)

theorem ordZ_spec (w : AddValuation K (WithTop ℤ)) {x : K} (hx : x ≠ 0) : w x = (ordZ w x : WithTop ℤ) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff w).mpr hx)
  rw [ordZ, ← hr, WithTop.untopD_coe]

theorem ordZ_one (w : AddValuation K (WithTop ℤ)) : ordZ w 1 = 0 := by
  have h := ordZ_spec w one_ne_zero
  rw [AddValuation.map_one] at h
  exact_mod_cast h.symm

theorem ordZ_mul (w : AddValuation K (WithTop ℤ)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordZ w (x * y) = ordZ w x + ordZ w y := by
  have h := w.map_mul x y
  rw [ordZ_spec w hx, ordZ_spec w hy, ordZ_spec w (mul_ne_zero hx hy)] at h
  exact_mod_cast h

theorem ordZ_inv (w : AddValuation K (WithTop ℤ)) {x : K} (hx : x ≠ 0) : ordZ w x⁻¹ = -ordZ w x := by
  have h := ordZ_mul w hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ordZ_one] at h
  linarith

theorem ordZ_pow (w : AddValuation K (WithTop ℤ)) {x : K} (hx : x ≠ 0) (n : ℕ) :
    ordZ w (x ^ n) = n * ordZ w x := by
  induction n with
  | zero => simp [ordZ_one]
  | succ n ih => rw [pow_succ, ordZ_mul w (pow_ne_zero n hx) hx, ih]; push_cast; ring

theorem ordZ_zpow (w : AddValuation K (WithTop ℤ)) {x : K} (hx : x ≠ 0) (n : ℤ) :
    ordZ w (x ^ n) = n * ordZ w x := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, ordZ_pow w hx]
  · rw [zpow_neg, zpow_natCast, ordZ_inv w (pow_ne_zero k hx), ordZ_pow w hx]; ring

/-- **Uniqueness of discrete valuations**: if `w₁` and `w₂` take the value `1` and `w₂ ≥ 0` implies `w₁ ≥ 0`, then
`w₁ = w₂`. -/
theorem addVal_eq_of_nonneg_imp (w1 w2 : AddValuation K (WithTop ℤ)) (h1 : ∃ f, w1 f = 1) (h2 : ∃ π, w2 π = 1)
    (h : ∀ x, 0 ≤ w2 x → 0 ≤ w1 x) : w1 = w2 := by
  obtain ⟨π, hπ⟩ := h2
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have hπ2 : ordZ w2 π = 1 := by
    have h3 := ordZ_spec w2 hπ0
    rw [hπ] at h3
    exact_mod_cast h3.symm
  have hc0 : 0 ≤ ordZ w1 π := by
    have h3 := h π (by rw [hπ]; exact zero_le_one)
    rw [ordZ_spec w1 hπ0] at h3
    exact_mod_cast h3
  have hzero : ∀ y : K, y ≠ 0 → ordZ w2 y = 0 → ordZ w1 y = 0 := by
    intro y hy h0
    have a := h y (by rw [ordZ_spec w2 hy, h0]; rfl)
    have b := h y⁻¹ (by rw [ordZ_spec w2 (inv_ne_zero hy), ordZ_inv w2 hy, h0, neg_zero]; rfl)
    rw [ordZ_spec w1 hy] at a
    rw [ordZ_spec w1 (inv_ne_zero hy), ordZ_inv w1 hy] at b
    have a' : 0 ≤ ordZ w1 y := by exact_mod_cast a
    have b' : 0 ≤ -ordZ w1 y := by exact_mod_cast b
    omega
  have key : ∀ x : K, x ≠ 0 → ordZ w1 x = ordZ w2 x * ordZ w1 π := by
    intro x hx
    have hπn : π ^ (-ordZ w2 x) ≠ 0 := zpow_ne_zero _ hπ0
    have hy : x * π ^ (-ordZ w2 x) ≠ 0 := mul_ne_zero hx hπn
    have h2y : ordZ w2 (x * π ^ (-ordZ w2 x)) = 0 := by
      rw [ordZ_mul w2 hx hπn, ordZ_zpow w2 hπ0, hπ2]; ring
    have h1y := hzero _ hy h2y
    rw [ordZ_mul w1 hx hπn, ordZ_zpow w1 hπ0] at h1y
    linarith
  obtain ⟨f, hf⟩ := h1
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hf1 : ordZ w1 f = 1 := by
    have h3 := ordZ_spec w1 hf0
    rw [hf] at h3
    exact_mod_cast h3.symm
  have hc1 : ordZ w1 π = 1 := by
    have h3 := key f hf0
    rw [hf1] at h3
    exact Int.eq_one_of_mul_eq_one_left hc0 h3.symm
  refine AddValuation.ext fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  · rw [ordZ_spec w1 hx, ordZ_spec w2 hx, key x hx, hc1, mul_one]

/-- **Valuation rings are integrally closed**: an element integral over a ring of elements of nonnegative
valuation has nonnegative valuation. -/
theorem addVal_nonneg_of_isIntegral {R : Type*} [CommRing R] [Algebra R K] (w : AddValuation K (WithTop ℤ))
    (hR : ∀ r : R, 0 ≤ w (algebraMap R K r)) {y : K} (hy : IsIntegral R y) : 0 ≤ w y := by
  obtain ⟨p, hpm, hp⟩ := hy
  by_contra hneg
  push Not at hneg
  have hy0 : y ≠ 0 := by rintro rfl; simp at hneg
  have ha : ordZ w y < 0 := by
    rw [ordZ_spec w hy0] at hneg
    exact_mod_cast hneg
  set n := p.natDegree
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hp
  have hsum : ((n * ordZ w y + 1 : ℤ) : WithTop ℤ) ≤
      w (∑ i ∈ Finset.range n, algebraMap R K (p.coeff i) * y ^ i) := by
    apply AddValuation.map_le_sum
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rw [AddValuation.map_mul, AddValuation.map_pow, ordZ_spec w hy0]
    by_cases hc : algebraMap R K (p.coeff i) = 0
    · rw [hc, AddValuation.map_zero, top_add]; exact le_top
    · have hcn := hR (p.coeff i)
      rw [ordZ_spec w hc] at hcn ⊢
      have hcn' : 0 ≤ ordZ w (algebraMap R K (p.coeff i)) := by exact_mod_cast hcn
      have hle : n * ordZ w y + 1 ≤ ordZ w (algebraMap R K (p.coeff i)) + i * ordZ w y := by
        have h3 : (n : ℤ) * ordZ w y + 1 ≤ i * ordZ w y := by
          have h4 : ((i : ℤ) + 1) ≤ n := by exact_mod_cast hin
          nlinarith
        linarith
      rw [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
      exact_mod_cast hle
  have hyn : y ^ n = -∑ i ∈ Finset.range n, algebraMap R K (p.coeff i) * y ^ i := by
    linear_combination hp
  have hval : w (y ^ n) = ((n * ordZ w y : ℤ) : WithTop ℤ) := by
    rw [ordZ_spec w (pow_ne_zero n hy0), ordZ_pow w hy0]
  rw [hyn, AddValuation.map_neg] at hval
  rw [hval] at hsum
  have : n * ordZ w y + 1 ≤ n * ordZ w y := by exact_mod_cast hsum
  omega

end addval

end

end CC6Full
