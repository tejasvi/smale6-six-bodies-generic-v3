import Lean6.Special.Comp.Ball.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Complex balls: the meaning of a ball and the soundness of the operations

A biased natural `X` stands for the integer `cv P X = X − bias P`. A ball `x` **contains** `z : ℂ` (`x.Mem P z`) if,
provided its history is small (`x.s ≤ smax P`), it is valid (`|cv re| + |cv im| ≤ a ≤ s`) and `z · 2^P` lies within `r`
of the center `cv re + cv im · i` in the real and in the imaginary part. Every operation maps balls containing `z, w` to a
ball containing the result (`mem_add`, `mem_sub`, `mem_neg`, `mem_mul`, `mem_dot`, …): its history dominates those of
its inputs, so the hypothesis "history small" passes to the inputs, and then every truncated subtraction of `Defs.lean`
is exact (`bias = 2 · smax`). `excl0_ne_zero`: a ball that passes `excl0` does not contain `0`.
-/

namespace Lean6.Special.Ball

open Complex

/-! ## The bias -/

theorem bias_eq (P : ℕ) : bias P = 2 ^ (3 * P + 1) := by simp [bias, Nat.pow_eq]

theorem smax_eq (P : ℕ) : smax P = 2 ^ (3 * P) := by simp [smax, Nat.pow_eq]

theorem bias_eq_two_smax (P : ℕ) : bias P = 2 * smax P := by
  rw [bias_eq, smax_eq, pow_succ]; ring

theorem smax_pos (P : ℕ) : 0 < smax P := by rw [smax_eq]; positivity

theorem one_le_smax (P : ℕ) : 1 ≤ smax P := smax_pos P

/-- `smax · 2^P ≤ bias · 2^P`, in the form used by the exactness of the rounding. -/
theorem smax_le_bias (P : ℕ) : smax P ≤ bias P := by rw [bias_eq_two_smax]; omega

/-- `Nat.shiftLeft` as a product. -/
theorem shiftLeft_eq' (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

/-- `Nat.shiftRight` as a quotient. -/
theorem shiftRight_eq' (a b : ℕ) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b

/-- `Nat.div` as a quotient. -/
theorem div_eq' (a b : ℕ) : Nat.div a b = a / b := rfl

/-! ## Meaning -/

/-- The integer of a biased natural. -/
def cv (P X : ℕ) : ℤ := (X : ℤ) - (bias P : ℤ)

/-- A ball is valid: `a` bounds the center, `s` bounds `a`. -/
structure CB.Valid (P : ℕ) (x : CB) : Prop where
  mag : |cv P x.re| + |cv P x.im| ≤ (x.a : ℤ)
  hist : x.a ≤ x.s

/-- **The ball `x` contains `z`** (provided its history is small). -/
def CB.Mem (P : ℕ) (z : ℂ) (x : CB) : Prop :=
  x.s ≤ smax P → x.Valid P ∧ |z.re * 2 ^ P - (cv P x.re : ℝ)| ≤ x.r ∧ |z.im * 2 ^ P - (cv P x.im : ℝ)| ≤ x.r

variable {P : ℕ}

theorem CB.Valid.cv_re_le {x : CB} (h : x.Valid P) (hs : x.s ≤ smax P) : |cv P x.re| ≤ smax P := by
  have := h.mag; have := h.hist; have := abs_nonneg (cv P x.im); omega

theorem CB.Valid.cv_im_le {x : CB} (h : x.Valid P) (hs : x.s ≤ smax P) : |cv P x.im| ≤ smax P := by
  have := h.mag; have := h.hist; have := abs_nonneg (cv P x.re); omega

/-- The biased natural of a small center lies in `[smax, 3 smax]`. -/
theorem re_range {x : CB} (h : x.Valid P) (hs : x.s ≤ smax P) :
    smax P ≤ x.re ∧ x.re ≤ 3 * smax P ∧ smax P ≤ x.im ∧ x.im ≤ 3 * smax P := by
  have h1 := abs_le.mp (h.cv_re_le hs)
  have h2 := abs_le.mp (h.cv_im_le hs)
  have hb := bias_eq_two_smax P
  unfold cv at h1 h2
  omega

/-! ## Real-number helpers -/

theorem abs_le_of_sub {u c r : ℝ} (h : |u - c| ≤ r) : |u| ≤ |c| + r := by
  have := abs_sub_abs_le_abs_sub u c; linarith

/-- The error of a product of perturbed complex numbers (real part). -/
theorem prod_err_re {a b c d e1 e2 f1 f2 rx ry ax ay : ℝ} (he1 : |e1| ≤ rx) (he2 : |e2| ≤ rx)
    (hf1 : |f1| ≤ ry) (hf2 : |f2| ≤ ry) (ha : |a| + |b| ≤ ax) (hc : |c| + |d| ≤ ay) :
    |(a + e1) * (c + f1) - (b + e2) * (d + f2) - (a * c - b * d)| ≤ ax * ry + rx * ay + 2 * rx * ry := by
  have hrx : 0 ≤ rx := (abs_nonneg _).trans he1
  have hry : 0 ≤ ry := (abs_nonneg _).trans hf1
  have e : (a + e1) * (c + f1) - (b + e2) * (d + f2) - (a * c - b * d) =
      a * f1 + e1 * c + e1 * f1 - b * f2 - e2 * d - e2 * f2 := by ring
  rw [e]
  have t1 : |a * f1| ≤ |a| * ry := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf1 (abs_nonneg _)
  have t2 : |e1 * c| ≤ rx * |c| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right he1 (abs_nonneg _)
  have t3 : |e1 * f1| ≤ rx * ry := by rw [abs_mul]; exact mul_le_mul he1 hf1 (abs_nonneg _) hrx
  have t4 : |b * f2| ≤ |b| * ry := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf2 (abs_nonneg _)
  have t5 : |e2 * d| ≤ rx * |d| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right he2 (abs_nonneg _)
  have t6 : |e2 * f2| ≤ rx * ry := by rw [abs_mul]; exact mul_le_mul he2 hf2 (abs_nonneg _) hrx
  have s1 := abs_add_le (a * f1 + e1 * c + e1 * f1 - b * f2 - e2 * d) (-(e2 * f2))
  have s2 := abs_add_le (a * f1 + e1 * c + e1 * f1 - b * f2) (-(e2 * d))
  have s3 := abs_add_le (a * f1 + e1 * c + e1 * f1) (-(b * f2))
  have s4 := abs_add_le (a * f1 + e1 * c) (e1 * f1)
  have s5 := abs_add_le (a * f1) (e1 * c)
  simp only [abs_neg, ← sub_eq_add_neg] at s1 s2 s3
  have m1 : (|a| + |b|) * ry ≤ ax * ry := mul_le_mul_of_nonneg_right ha hry
  have m2 : rx * (|c| + |d|) ≤ rx * ay := mul_le_mul_of_nonneg_left hc hrx
  nlinarith

/-- The error of a product of perturbed complex numbers (imaginary part). -/
theorem prod_err_im {a b c d e1 e2 f1 f2 rx ry ax ay : ℝ} (he1 : |e1| ≤ rx) (he2 : |e2| ≤ rx)
    (hf1 : |f1| ≤ ry) (hf2 : |f2| ≤ ry) (ha : |a| + |b| ≤ ax) (hc : |c| + |d| ≤ ay) :
    |(a + e1) * (d + f2) + (b + e2) * (c + f1) - (a * d + b * c)| ≤ ax * ry + rx * ay + 2 * rx * ry := by
  have h := prod_err_re (a := a) (b := -b) (c := d) (d := c) (e1 := e1) (e2 := -e2) (f1 := f2) (f2 := f1)
    (ax := ax) (ay := ay) he1 (by rwa [abs_neg]) hf2 hf1 (by rwa [abs_neg]) (by rw [add_comm (|d|)]; exact hc)
  have e : (a + e1) * (d + f2) - (-b + -e2) * (c + f1) - (a * d - -b * c) =
      (a + e1) * (d + f2) + (b + e2) * (c + f1) - (a * d + b * c) := by ring
  rwa [e] at h

/-- The magnitude of a product of integers. -/
theorem prod_mag {a b c d : ℤ} : |a * c - b * d| + |a * d + b * c| ≤ (|a| + |b|) * (|c| + |d|) := by
  have h1 : |a * c - b * d| ≤ |a| * |c| + |b| * |d| := by
    rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
  have h2 : |a * d + b * c| ≤ |a| * |d| + |b| * |c| := by
    rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
  nlinarith

/-! ## Rounding -/

/-- Exactness of the rounding of a scaled sum: the integer `R` (with `|R| < bias · 2^P`) as naturals `pr, nr` with
`pr − nr = R` is rounded to `⌊R / 2^P⌋`, biased. -/
theorem round_cv {pr nr : ℕ} {R : ℤ} (hR : (pr : ℤ) - nr = R) (hlt : |R| < (bias P : ℤ) * 2 ^ P) :
    cv P (rnd P pr nr) = R / 2 ^ P := by
  have hle : nr ≤ pr + bias P * 2 ^ P := by
    have := (abs_lt.mp hlt).1
    zify; linarith
  simp only [rnd, Nat.add_eq, Nat.sub_eq, shiftLeft_eq', shiftRight_eq']
  unfold cv
  rw [Int.natCast_ediv, Nat.cast_sub hle]
  push_cast
  have h2 : (2 : ℤ) ^ P ≠ 0 := by positivity
  have : (pr : ℤ) + bias P * 2 ^ P - nr = R + bias P * 2 ^ P := by linarith
  rw [this, Int.add_mul_ediv_right _ _ h2]
  ring

/-- `⌊R / 2^P⌋ · 2^P` is within `[R − 2^P, R]`. -/
theorem ediv_bounds (R : ℤ) : 0 ≤ R - 2 ^ P * (R / 2 ^ P) ∧ R - 2 ^ P * (R / 2 ^ P) < 2 ^ P := by
  have hp : (0 : ℤ) < 2 ^ P := by positivity
  rw [← Int.emod_def]
  exact ⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩

/-- The real error of the rounding: `|u · 2^P − ⌊R/2^P⌋| ≤ |u · 2^{2P} − R| / 2^P + 1`. -/
theorem round_err (u : ℝ) (R : ℤ) {r : ℝ} (h : |u * 2 ^ (2 * P) - R| ≤ r) :
    |u * 2 ^ P - ((R / 2 ^ P : ℤ) : ℝ)| < r / 2 ^ P + 1 := by
  obtain ⟨h1, h2⟩ := ediv_bounds (P := P) R
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  set q := R / 2 ^ P
  have h1' : (0 : ℝ) ≤ R - 2 ^ P * q := by exact_mod_cast h1
  have h2' : (R : ℝ) - 2 ^ P * q < 2 ^ P := by exact_mod_cast h2
  have e : u * 2 ^ P - q = (u * 2 ^ (2 * P) - R) / 2 ^ P + (R - 2 ^ P * q) / 2 ^ P := by
    field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans_lt ?_
  rw [abs_div, abs_of_pos hp, abs_of_nonneg (div_nonneg h1' hp.le)]
  have : (R - 2 ^ P * q : ℝ) / 2 ^ P < 1 := by rw [div_lt_one hp]; exact h2'
  have : |u * 2 ^ (2 * P) - R| / 2 ^ P ≤ r / 2 ^ P := div_le_div_of_nonneg_right h hp.le
  linarith

/-- `|⌊R / 2^P⌋| < |R| / 2^P + 1`. -/
theorem round_mag (R : ℤ) : (((|R / 2 ^ P| : ℤ)) : ℝ) < |(R : ℝ)| / 2 ^ P + 1 := by
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have h := round_err (P := P) ((R : ℝ) / 2 ^ (2 * P)) R (r := 0) (by
    have hp2 : (0 : ℝ) < 2 ^ (2 * P) := by positivity
    rw [div_mul_cancel₀ _ hp2.ne', sub_self, abs_zero])
  have e : (R : ℝ) / 2 ^ (2 * P) * 2 ^ P = R / 2 ^ P := by
    rw [two_mul, pow_add]; field_simp
  rw [e, zero_div, zero_add] at h
  have h3 := abs_sub_abs_le_abs_sub (((R / 2 ^ P : ℤ)) : ℝ) ((R : ℝ) / 2 ^ P)
  rw [abs_sub_comm] at h3
  rw [abs_div, abs_of_pos hp] at h3
  push_cast
  linarith

/-- `n / 2^P < (n >> P) + 1`. -/
theorem lt_shiftRight_succ (n : ℕ) : (n : ℝ) / 2 ^ P < (Nat.shiftRight n P : ℕ) + 1 := by
  rw [shiftRight_eq']
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  rw [div_lt_iff₀ hp]
  have h := Nat.lt_div_mul_add (a := n) (b := 2 ^ P) (by positivity)
  have h' : (n : ℝ) < ((n / 2 ^ P : ℕ) : ℝ) * 2 ^ P + 2 ^ P := by exact_mod_cast h
  linarith

/-- Two radius bounds add. -/
theorem abs_add_sub_le {u1 u2 c1 c2 r1 r2 : ℝ} (h1 : |u1 - c1| ≤ r1) (h2 : |u2 - c2| ≤ r2) :
    |(u1 + u2) - (c1 + c2)| ≤ r1 + r2 := by
  have e : (u1 + u2) - (c1 + c2) = (u1 - c1) + (u2 - c2) := by ring
  rw [e]; exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Two radius bounds subtract. -/
theorem abs_sub_sub_le {u1 u2 c1 c2 r1 r2 : ℝ} (h1 : |u1 - c1| ≤ r1) (h2 : |u2 - c2| ≤ r2) :
    |(u1 - u2) - (c1 - c2)| ≤ r1 + r2 := by
  have e : (u1 - u2) - (c1 - c2) = (u1 - c1) - (u2 - c2) := by ring
  rw [e]; exact (abs_sub _ _).trans (add_le_add h1 h2)

/-! ## Exact balls -/

theorem mem_zero : (zero P).Mem P 0 := by
  intro _
  refine ⟨⟨by simp [zero, cv], by simp [zero]⟩, by simp [zero, cv], by simp [zero, cv]⟩

theorem mem_ofInt (c : ℤ) : (ofInt P c).Mem P (c : ℂ) := by
  intro hs
  have hb := bias_eq_two_smax P
  cases c with
  | ofNat n =>
    simp only [ofInt, Nat.add_eq, shiftLeft_eq'] at hs ⊢
    have e : cv P (bias P + n * 2 ^ P) = n * 2 ^ P := by unfold cv; push_cast; ring
    refine ⟨⟨?_, le_rfl⟩, ?_, ?_⟩
    · rw [e]; simp [cv, abs_of_nonneg]
    · rw [e]; simp
    · simp [cv]
  | negSucc n =>
    simp only [ofInt, Nat.sub_eq, shiftLeft_eq'] at hs ⊢
    have hle : (n.succ) * 2 ^ P ≤ bias P := by omega
    have e : cv P (bias P - n.succ * 2 ^ P) = -((n.succ : ℤ) * 2 ^ P) := by
      unfold cv; rw [Nat.cast_sub hle]; push_cast; ring
    refine ⟨⟨?_, le_rfl⟩, ?_, ?_⟩
    · rw [e]; simp [cv, abs_of_nonneg]
    · rw [e]; simp [Int.negSucc_eq]; ring_nf
    · simp [cv]

theorem mem_one : (one P).Mem P 1 := by
  have := mem_ofInt (P := P) 1; simpa [one] using this

/-! ## Sum, difference, negation -/

theorem mem_add {z w : ℂ} {x y : CB} (hx : x.Mem P z) (hy : y.Mem P w) : (add P x y).Mem P (z + w) := by
  intro hs
  simp only [add, Nat.add_eq, Nat.sub_eq] at hs ⊢
  obtain ⟨hxv, hxr, hxi⟩ := hx (by omega)
  obtain ⟨hyv, hyr, hyi⟩ := hy (by omega)
  have rx := re_range hxv (by omega)
  have ry := re_range hyv (by omega)
  have hb := bias_eq_two_smax P
  have e1 : cv P (x.re + y.re - bias P) = cv P x.re + cv P y.re := by
    unfold cv; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : cv P (x.im + y.im - bias P) = cv P x.im + cv P y.im := by
    unfold cv; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have ha := hxv.mag
  have hb' := hyv.mag
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [e1, e2]; push_cast
    have := abs_add_le (cv P x.re) (cv P y.re)
    have := abs_add_le (cv P x.im) (cv P y.im)
    linarith
  · show x.a + y.a ≤ x.s + y.s
    have := hxv.hist; have := hyv.hist; omega
  · rw [e1]; push_cast; rw [Complex.add_re, add_mul]; exact abs_add_sub_le hxr hyr
  · rw [e2]; push_cast; rw [Complex.add_im, add_mul]; exact abs_add_sub_le hxi hyi

theorem mem_sub {z w : ℂ} {x y : CB} (hx : x.Mem P z) (hy : y.Mem P w) : (sub P x y).Mem P (z - w) := by
  intro hs
  simp only [sub, Nat.add_eq, Nat.sub_eq] at hs ⊢
  obtain ⟨hxv, hxr, hxi⟩ := hx (by omega)
  obtain ⟨hyv, hyr, hyi⟩ := hy (by omega)
  have rx := re_range hxv (by omega)
  have ry := re_range hyv (by omega)
  have hb := bias_eq_two_smax P
  have e1 : cv P (x.re + bias P - y.re) = cv P x.re - cv P y.re := by
    unfold cv; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : cv P (x.im + bias P - y.im) = cv P x.im - cv P y.im := by
    unfold cv; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have ha := hxv.mag
  have hb' := hyv.mag
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [e1, e2]; push_cast
    have := abs_sub (cv P x.re) (cv P y.re)
    have := abs_sub (cv P x.im) (cv P y.im)
    linarith
  · show x.a + y.a ≤ x.s + y.s
    have := hxv.hist; have := hyv.hist; omega
  · rw [e1]; push_cast; rw [Complex.sub_re, sub_mul]; exact abs_sub_sub_le hxr hyr
  · rw [e2]; push_cast; rw [Complex.sub_im, sub_mul]; exact abs_sub_sub_le hxi hyi

theorem mem_neg {z : ℂ} {x : CB} (hx : x.Mem P z) : (neg P x).Mem P (-z) := by
  intro hs
  simp only [neg, Nat.mul_eq, Nat.sub_eq] at hs ⊢
  obtain ⟨hxv, hxr, hxi⟩ := hx hs
  have rx := re_range hxv hs
  have hb := bias_eq_two_smax P
  have e1 : cv P (2 * bias P - x.re) = -cv P x.re := by
    unfold cv; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : cv P (2 * bias P - x.im) = -cv P x.im := by
    unfold cv; rw [Nat.cast_sub (by omega)]; push_cast; ring
  refine ⟨⟨?_, hxv.hist⟩, ?_, ?_⟩
  · rw [e1, e2, abs_neg, abs_neg]; exact hxv.mag
  · rw [e1]; push_cast; rw [Complex.neg_re, neg_mul, ← neg_add', abs_neg]; exact hxr
  · rw [e2]; push_cast; rw [Complex.neg_im, neg_mul, ← neg_add', abs_neg]; exact hxi

/-! ## Fused sums of products -/

/-- The meaning of an accumulator holding the true sum `z`: `pr − nr`, `pi − ni` are the scaled center of the sum. -/
def Acc.Inv (P : ℕ) (z : ℂ) (c : Acc) : Prop :=
  c.s ≤ smax P →
    |(c.pr : ℤ) - c.nr| + |(c.pi : ℤ) - c.ni| ≤ (c.a : ℤ) ∧
    |z.re * 2 ^ (2 * P) - (((c.pr : ℤ) - c.nr : ℤ) : ℝ)| ≤ c.r ∧
    |z.im * 2 ^ (2 * P) - (((c.pi : ℤ) - c.ni : ℤ) : ℝ)| ≤ c.r

theorem inv_zero : Acc.zero.Inv P 0 := by
  intro _; simp [Acc.zero]

theorem inv_mac {c : Acc} {x y : CB} {z zx zy : ℂ} (hc : c.Inv P z) (hx : x.Mem P zx) (hy : y.Mem P zy) :
    (Acc.mac P c x y).Inv P (z + zx * zy) := by
  intro hs
  simp only [Acc.mac, Nat.add_eq, Nat.mul_eq] at hs ⊢
  obtain ⟨hcm, hcr, hci⟩ := hc (by omega)
  obtain ⟨hxv, hxr, hxi⟩ := hx (by omega)
  obtain ⟨hyv, hyr, hyi⟩ := hy (by omega)
  set a := cv P x.re
  set b := cv P x.im
  set cc := cv P y.re
  set d := cv P y.im
  have eR : ((c.pr + (x.re * y.re + bias P * (x.im + y.im)) : ℕ) : ℤ) -
      ((c.nr + (x.im * y.im + bias P * (x.re + y.re)) : ℕ) : ℤ) = ((c.pr : ℤ) - c.nr) + (a * cc - b * d) := by
    simp only [a, b, cc, d, cv]; push_cast; ring
  have eI : ((c.pi + (x.re * y.im + x.im * y.re + 2 * bias P * bias P) : ℕ) : ℤ) -
      ((c.ni + bias P * (x.re + y.im + (x.im + y.re)) : ℕ) : ℤ) = ((c.pi : ℤ) - c.ni) + (a * d + b * cc) := by
    simp only [a, b, cc, d, cv]; push_cast; ring
  have hxa : |a| + |b| ≤ (x.a : ℤ) := hxv.mag
  have hya : |cc| + |d| ≤ (y.a : ℤ) := hyv.mag
  have hxa' : |(a : ℝ)| + |(b : ℝ)| ≤ x.a := by exact_mod_cast hxa
  have hya' : |(cc : ℝ)| + |(d : ℝ)| ≤ y.a := by exact_mod_cast hya
  have hp2 : (2 : ℝ) ^ (2 * P) = 2 ^ P * 2 ^ P := by rw [two_mul, pow_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [eR, eI]
    have hm := prod_mag (a := a) (b := b) (c := cc) (d := d)
    have : (|a| + |b|) * (|cc| + |d|) ≤ (x.a : ℤ) * y.a :=
      mul_le_mul hxa hya (by positivity) (by positivity)
    have := abs_add_le ((c.pr : ℤ) - c.nr) (a * cc - b * d)
    have := abs_add_le ((c.pi : ℤ) - c.ni) (a * d + b * cc)
    push_cast; linarith
  · rw [eR]; push_cast
    have h := prod_err_re (a := (a : ℝ)) (b := (b : ℝ)) (c := (cc : ℝ)) (d := (d : ℝ))
      (e1 := zx.re * 2 ^ P - a) (e2 := zx.im * 2 ^ P - b) (f1 := zy.re * 2 ^ P - cc) (f2 := zy.im * 2 ^ P - d)
      (ax := x.a) (ay := y.a) hxr hxi hyr hyi hxa' hya'
    have e : (z + zx * zy).re * 2 ^ (2 * P) - ((c.pr : ℝ) - c.nr + (a * cc - b * d)) =
        (z.re * 2 ^ (2 * P) - ((c.pr : ℝ) - c.nr)) +
        ((a + (zx.re * 2 ^ P - a)) * (cc + (zy.re * 2 ^ P - cc)) - (b + (zx.im * 2 ^ P - b)) *
          (d + (zy.im * 2 ^ P - d)) - (a * cc - b * d)) := by
      rw [Complex.add_re, Complex.mul_re, hp2]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have hcr' : |z.re * 2 ^ (2 * P) - ((c.pr : ℝ) - c.nr)| ≤ c.r := by exact_mod_cast hcr
    linarith
  · rw [eI]; push_cast
    have h := prod_err_im (a := (a : ℝ)) (b := (b : ℝ)) (c := (cc : ℝ)) (d := (d : ℝ))
      (e1 := zx.re * 2 ^ P - a) (e2 := zx.im * 2 ^ P - b) (f1 := zy.re * 2 ^ P - cc) (f2 := zy.im * 2 ^ P - d)
      (ax := x.a) (ay := y.a) hxr hxi hyr hyi hxa' hya'
    have e : (z + zx * zy).im * 2 ^ (2 * P) - ((c.pi : ℝ) - c.ni + (a * d + b * cc)) =
        (z.im * 2 ^ (2 * P) - ((c.pi : ℝ) - c.ni)) +
        ((a + (zx.re * 2 ^ P - a)) * (d + (zy.im * 2 ^ P - d)) + (b + (zx.im * 2 ^ P - b)) *
          (cc + (zy.re * 2 ^ P - cc)) - (a * d + b * cc)) := by
      rw [Complex.add_im, Complex.mul_im, hp2]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have hci' : |z.im * 2 ^ (2 * P) - ((c.pi : ℝ) - c.ni)| ≤ c.r := by exact_mod_cast hci
    linarith

theorem inv_addB {c : Acc} {x : CB} {z zx : ℂ} (hc : c.Inv P z) (hx : x.Mem P zx) :
    (Acc.addB P c x).Inv P (z + zx) := by
  intro hs
  simp only [Acc.addB, Nat.add_eq, shiftLeft_eq'] at hs ⊢
  obtain ⟨hcm, hcr, hci⟩ := hc (by omega)
  obtain ⟨hxv, hxr, hxi⟩ := hx (by omega)
  have eR : ((c.pr + x.re * 2 ^ P : ℕ) : ℤ) - ((c.nr + bias P * 2 ^ P : ℕ) : ℤ) =
      ((c.pr : ℤ) - c.nr) + cv P x.re * 2 ^ P := by unfold cv; push_cast; ring
  have eI : ((c.pi + x.im * 2 ^ P : ℕ) : ℤ) - ((c.ni + bias P * 2 ^ P : ℕ) : ℤ) =
      ((c.pi : ℤ) - c.ni) + cv P x.im * 2 ^ P := by unfold cv; push_cast; ring
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have hp2 : (2 : ℝ) ^ (2 * P) = 2 ^ P * 2 ^ P := by rw [two_mul, pow_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [eR, eI]
    have hm := hxv.mag
    have hp' : (0 : ℤ) < 2 ^ P := by positivity
    have h1 := abs_add_le ((c.pr : ℤ) - c.nr) (cv P x.re * 2 ^ P)
    have h2 := abs_add_le ((c.pi : ℤ) - c.ni) (cv P x.im * 2 ^ P)
    rw [abs_mul, abs_of_pos hp'] at h1 h2
    have h3 : (|cv P x.re| + |cv P x.im|) * 2 ^ P ≤ (x.a : ℤ) * 2 ^ P := mul_le_mul_of_nonneg_right hm hp'.le
    push_cast; linarith
  · rw [eR]; push_cast
    have e : (z + zx).re * 2 ^ (2 * P) - ((c.pr : ℝ) - c.nr + cv P x.re * 2 ^ P) =
        (z.re * 2 ^ (2 * P) - ((c.pr : ℝ) - c.nr)) + (zx.re * 2 ^ P - cv P x.re) * 2 ^ P := by
      rw [Complex.add_re, hp2]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hp]
    have hcr' : |z.re * 2 ^ (2 * P) - ((c.pr : ℝ) - c.nr)| ≤ c.r := by exact_mod_cast hcr
    have := mul_le_mul_of_nonneg_right hxr hp.le
    linarith
  · rw [eI]; push_cast
    have e : (z + zx).im * 2 ^ (2 * P) - ((c.pi : ℝ) - c.ni + cv P x.im * 2 ^ P) =
        (z.im * 2 ^ (2 * P) - ((c.pi : ℝ) - c.ni)) + (zx.im * 2 ^ P - cv P x.im) * 2 ^ P := by
      rw [Complex.add_im, hp2]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hp]
    have hci' : |z.im * 2 ^ (2 * P) - ((c.pi : ℝ) - c.ni)| ≤ c.r := by exact_mod_cast hci
    have := mul_le_mul_of_nonneg_right hxi hp.le
    linarith

theorem mem_fin {c : Acc} {z : ℂ} (hc : c.Inv P z) : (Acc.fin P c).Mem P z := by
  intro hs
  simp only [Acc.fin] at hs ⊢
  simp only [Nat.add_eq] at hs
  obtain ⟨hcm, hcr, hci⟩ := hc (by omega)
  have hb := bias_eq_two_smax P
  -- the magnitude is below `bias · 2^P`
  have ha : (c.a : ℝ) / 2 ^ P < (Nat.shiftRight c.a P : ℕ) + 1 := lt_shiftRight_succ c.a
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have hsa : Nat.shiftRight c.a P + 1 ≤ smax P := by omega
  have hA : (c.a : ℤ) < (bias P : ℤ) * 2 ^ P := by
    have h1 : (c.a : ℝ) < ((Nat.shiftRight c.a P : ℕ) + 1) * 2 ^ P := by rwa [div_lt_iff₀ hp] at ha
    have h2 : ((Nat.shiftRight c.a P : ℕ) + 1 : ℝ) ≤ bias P := by
      have : (Nat.shiftRight c.a P + 1 : ℕ) ≤ bias P := by omega
      exact_mod_cast this
    have : (c.a : ℝ) < bias P * 2 ^ P := h1.trans_le (mul_le_mul_of_nonneg_right h2 hp.le)
    exact_mod_cast this
  have hR : |(c.pr : ℤ) - c.nr| < (bias P : ℤ) * 2 ^ P := by
    have := abs_nonneg ((c.pi : ℤ) - c.ni); linarith
  have hI : |(c.pi : ℤ) - c.ni| < (bias P : ℤ) * 2 ^ P := by
    have := abs_nonneg ((c.pr : ℤ) - c.nr); linarith
  have eR := round_cv (P := P) (pr := c.pr) (nr := c.nr) rfl hR
  have eI := round_cv (P := P) (pr := c.pi) (nr := c.ni) rfl hI
  have er := round_err (P := P) z.re _ hcr
  have ei := round_err (P := P) z.im _ hci
  have hr : (c.r : ℝ) / 2 ^ P < (Nat.shiftRight c.r P : ℕ) + 1 := lt_shiftRight_succ c.r
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- the magnitude
    set R : ℤ := (c.pr : ℤ) - c.nr
    set I : ℤ := (c.pi : ℤ) - c.ni
    have m1 := round_mag (P := P) R
    have m2 := round_mag (P := P) I
    have hcm' : |(R : ℝ)| + |(I : ℝ)| ≤ c.a := by exact_mod_cast hcm
    have h4 : |(R : ℝ)| / 2 ^ P + |(I : ℝ)| / 2 ^ P ≤ (c.a : ℝ) / 2 ^ P := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hcm' hp.le
    rw [Int.cast_abs] at m1 m2
    have h5 : (((|R / 2 ^ P| + |I / 2 ^ P| : ℤ)) : ℝ) < ((Nat.shiftRight c.a P : ℕ) : ℝ) + 3 := by
      push_cast; linarith
    have h3 : |R / 2 ^ P| + |I / 2 ^ P| < (Nat.shiftRight c.a P : ℤ) + 3 := by exact_mod_cast h5
    show |cv P (rnd P c.pr c.nr)| + |cv P (rnd P c.pi c.ni)| ≤ ((Nat.add (Nat.shiftRight c.a P) 2 : ℕ) : ℤ)
    rw [eR, eI]; simp only [Nat.add_eq]; push_cast; omega
  · show Nat.add (Nat.shiftRight c.a P) 2 ≤ Nat.add c.s (Nat.add (Nat.shiftRight c.a P) 2)
    simp only [Nat.add_eq]; omega
  · show |z.re * 2 ^ P - (cv P (rnd P c.pr c.nr) : ℝ)| ≤ ((Nat.add (Nat.shiftRight c.r P) 2 : ℕ) : ℝ)
    rw [eR]; simp only [Nat.add_eq]; push_cast at er ⊢; linarith
  · show |z.im * 2 ^ P - (cv P (rnd P c.pi c.ni) : ℝ)| ≤ ((Nat.add (Nat.shiftRight c.r P) 2 : ℕ) : ℝ)
    rw [eI]; simp only [Nat.add_eq]; push_cast at ei ⊢; linarith

theorem mem_mul {x y : CB} {z w : ℂ} (hx : x.Mem P z) (hy : y.Mem P w) : (mul P x y).Mem P (z * w) := by
  have h := mem_fin (inv_mac (inv_zero (P := P)) hx hy)
  rwa [zero_add] at h

/-- The fused sum over two lists of balls. -/
theorem inv_dot : ∀ {c : Acc} {z : ℂ} {xs ys : List CB} {zs ws : List ℂ}, c.Inv P z →
    List.Forall₂ (fun u x => CB.Mem P u x) zs xs → List.Forall₂ (fun u x => CB.Mem P u x) ws ys →
    (Acc.dot P c xs ys).Inv P (z + (List.zipWith (· * ·) zs ws).sum)
  | c, z, [], ys, zs, ws, hc, hx, _ => by
    cases hx; simp only [Acc.dot, List.zipWith_nil_left, List.sum_nil, add_zero]; exact hc
  | c, z, _ :: _, [], zs, ws, hc, hx, hy => by
    cases hy; simp only [Acc.dot, List.zipWith_nil_right, List.sum_nil, add_zero]; exact hc
  | c, z, x :: xs, y :: ys, zs, ws, hc, hx, hy => by
    cases hx with
    | cons hx1 hx2 =>
      cases hy with
      | cons hy1 hy2 =>
        simp only [Acc.dot, List.zipWith_cons_cons, List.sum_cons]
        have := inv_dot (inv_mac hc hx1 hy1) hx2 hy2
        rwa [add_assoc] at this

theorem mem_dot {xs ys : List CB} {zs ws : List ℂ} (hx : List.Forall₂ (fun u x => CB.Mem P u x) zs xs)
    (hy : List.Forall₂ (fun u x => CB.Mem P u x) ws ys) :
    (dot P xs ys).Mem P (List.zipWith (· * ·) zs ws).sum := by
  have h := mem_fin (inv_dot (inv_zero (P := P)) hx hy)
  rwa [zero_add] at h

/-! ## Magnitudes and the exclusion of `0` -/

theorem absB_eq (X : ℕ) : (absB P X : ℤ) = |cv P X| := by
  unfold absB cv
  split_ifs with h
  · have h' : bias P ≤ X := by simpa [Nat.ble_eq] using h
    rw [Nat.sub_eq, Nat.cast_sub h', abs_of_nonneg (by omega)]
  · have h' : X < bias P := by simpa [Nat.ble_eq] using h
    rw [Nat.sub_eq, Nat.cast_sub h'.le, abs_of_neg (by omega)]; ring

theorem mem_tight {x : CB} {z : ℂ} (hx : x.Mem P z) : (tight P x).Mem P z := by
  intro hs
  simp only [tight, Nat.add_eq] at hs ⊢
  obtain ⟨hxv, hxr, hxi⟩ := hx (by omega)
  refine ⟨⟨?_, ?_⟩, hxr, hxi⟩
  · push_cast; rw [absB_eq, absB_eq]
  · show absB P x.re + absB P x.im ≤ x.s + (absB P x.re + absB P x.im); omega

/-- The center of a ball as a complex number. -/
noncomputable def centerC (P : ℕ) (x : CB) : ℂ := ⟨(cv P x.re : ℝ) / 2 ^ P, (cv P x.im : ℝ) / 2 ^ P⟩

theorem mem_center (x : CB) : (center P x).Mem P (centerC P x) := by
  intro hs
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  refine ⟨⟨?_, by simp [center]⟩, ?_, ?_⟩
  · simp only [center, Nat.add_eq]; push_cast; rw [absB_eq, absB_eq]
  · simp [center, centerC, div_mul_cancel₀ _ hp.ne']
  · simp [center, centerC, div_mul_cancel₀ _ hp.ne']

theorem norm_le_magB {x : CB} {z : ℂ} (hx : x.Mem P z) (hs : x.s ≤ smax P) : ‖z‖ * 2 ^ P ≤ magB P x := by
  obtain ⟨hxv, hxr, hxi⟩ := hx hs
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have h1 := abs_le_of_sub hxr
  have h2 := abs_le_of_sub hxi
  rw [abs_mul, abs_of_pos hp] at h1 h2
  have hn := Complex.norm_le_abs_re_add_abs_im z
  have e1 : ((absB P x.re : ℕ) : ℝ) = |(cv P x.re : ℝ)| := by exact_mod_cast absB_eq x.re
  have e2 : ((absB P x.im : ℕ) : ℝ) = |(cv P x.im : ℝ)| := by exact_mod_cast absB_eq x.im
  simp only [magB, Nat.add_eq, Nat.mul_eq]; push_cast; rw [e1, e2]
  nlinarith

theorem excl0_ne_zero {x : CB} {z : ℂ} (hx : x.Mem P z) (he : excl0 P x = true) : z ≠ 0 := by
  simp only [excl0, okS, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at he
  obtain ⟨hs, hre⟩ := he
  obtain ⟨_, hxr, hxi⟩ := hx hs
  intro hz
  subst hz
  simp only [Complex.zero_re, Complex.zero_im, zero_mul, zero_sub, abs_neg] at hxr hxi
  rcases hre with h | h
  · have : (x.r : ℤ) < |cv P x.re| := by rw [← absB_eq]; exact_mod_cast h
    have : (x.r : ℝ) < |(cv P x.re : ℝ)| := by exact_mod_cast this
    linarith
  · have : (x.r : ℤ) < |cv P x.im| := by rw [← absB_eq]; exact_mod_cast h
    have : (x.r : ℝ) < |(cv P x.im : ℝ)| := by exact_mod_cast this
    linarith

end Lean6.Special.Ball
