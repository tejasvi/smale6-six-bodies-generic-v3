import Lean6.Special.Comp.D88.Boxes.Check
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic

/-!
# Discs: the soundness of the integer and rational disc arithmetic of `Comp/D88/Boxes/Check.lean`

* `IDisc.Mem d z`: `‖z − (a + b i)/T‖ ≤ R/T`. **`modBounds_sound`**: `L ≤ T‖z‖ ≤ U`; **`invSqrtBounds_sound`**:
  `λ/2^Q ≤ 1/√‖z‖ ≤ υ/2^Q`; **`discNonzero_sound`**: `z ≠ 0`.
* `QDisc.Mem d z`: `‖z − c‖ ≤ r` with a rational center and radius; sums, products, real multiples
  (`qadd_mem`, `qmul_mem`, `qsmul_mem`); `normLo_sound`, `normHi_sound`, `discLo_sound`, `discUp_sound`.
* **`betaDisc_sound`**: if `w² = X` with `X` in the disc `d`, then `±μ/w` lies in `betaDisc μ d` (the square root
  covering `‖w − s₀‖ ‖w + s₀‖ = ‖w² − s₀²‖ ≤ δ`, `‖w − s₀‖ + ‖w + s₀‖ ≥ 2‖s₀‖`, and the reciprocal).
* **`sumDisc3_mem`**: the sums of Lemma 6.17(b) lie in `sumDisc3`, with `ρ = 2√2` (`rho_mem`).
-/

namespace Lean6.Special.D88.Boxes

open Complex

/-! ## Integer discs -/

/-- The center `(a + b i)/T` of an integer disc. -/
noncomputable def IDisc.center (d : IDisc) : ℂ := ⟨(d.a : ℝ) / (d.T : ℝ), (d.b : ℝ) / (d.T : ℝ)⟩

/-- Membership in an integer disc. -/
def IDisc.Mem (d : IDisc) (z : ℂ) : Prop := ‖z - d.center‖ ≤ (d.R : ℝ) / (d.T : ℝ)

theorem natAbs_mul_self_cast (a : ℤ) : ((a.natAbs * a.natAbs : ℕ) : ℝ) = (a : ℝ) * (a : ℝ) := by
  simp only [Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs, abs_mul_abs_self]

/-- `T‖c‖ = √(a² + b²)`. -/
theorem IDisc.T_mul_norm_center (d : IDisc) (hT : 0 < d.T) :
    (d.T : ℝ) * ‖d.center‖ = Real.sqrt (((d.a.natAbs * d.a.natAbs + d.b.natAbs * d.b.natAbs : ℕ) : ℝ)) := by
  have hT' : (0 : ℝ) < d.T := by exact_mod_cast hT
  rw [Nat.cast_add, natAbs_mul_self_cast, natAbs_mul_self_cast, Complex.norm_def, Complex.normSq_apply]
  simp only [IDisc.center]
  have e : (d.a : ℝ) / d.T * ((d.a : ℝ) / d.T) + (d.b : ℝ) / d.T * ((d.b : ℝ) / d.T) =
      ((d.a : ℝ) * d.a + (d.b : ℝ) * d.b) / ((d.T : ℝ) * d.T) := by field_simp
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_mul_self hT'.le]
  field_simp

/-- **Moduli on an integer disc.** -/
theorem modBounds_sound {d : IDisc} {L U : ℕ} (h : modBounds d = some (L, U)) (hT : 0 < d.T) {z : ℂ}
    (hz : d.Mem z) : (L : ℝ) ≤ d.T * ‖z‖ ∧ (d.T : ℝ) * ‖z‖ ≤ U := by
  unfold modBounds at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  · rename_i hc
    obtain ⟨hm1, hm2⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    set n := d.a.natAbs * d.a.natAbs + d.b.natAbs * d.b.natAbs with hn
    set m := isqrt n
    have hT' : (0 : ℝ) < d.T := by exact_mod_cast hT
    have hc := d.T_mul_norm_center hT
    rw [← hn] at hc
    have hsq_lo : (m : ℝ) ≤ Real.sqrt n := by
      rw [show (m : ℝ) = Real.sqrt ((m : ℝ) * m) from (Real.sqrt_mul_self (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hm1)
    have hsq_hi : Real.sqrt n < (m : ℝ) + 1 := by
      rw [show (m : ℝ) + 1 = Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 1)) from
        (Real.sqrt_mul_self (by positivity)).symm]
      exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hm2)
    have hzc : (d.T : ℝ) * ‖z - d.center‖ ≤ d.R := by
      have := mul_le_mul_of_nonneg_left hz hT'.le
      rwa [mul_div_cancel₀ _ hT'.ne'] at this
    have h1 : ‖d.center‖ - ‖z - d.center‖ ≤ ‖z‖ := by
      have := norm_sub_norm_le d.center (d.center - z)
      rw [sub_sub_cancel, norm_sub_rev] at this
      linarith
    have h2 : ‖z‖ ≤ ‖d.center‖ + ‖z - d.center‖ := by
      have := norm_add_le (z - d.center) d.center
      rw [sub_add_cancel] at this
      linarith
    constructor
    · by_cases hmR : d.R ≤ m
      · rw [Nat.cast_sub hmR]
        nlinarith [mul_le_mul_of_nonneg_left h1 hT'.le]
      · rw [show m - d.R = 0 by omega, Nat.cast_zero]
        positivity
    · push_cast
      nlinarith [mul_le_mul_of_nonneg_left h2 hT'.le]
  · exact absurd h (by simp)

/-- **Inverse square roots** from `L ≤ T x ≤ U`. -/
theorem invSqrtBounds_sound {L U T lam ups : ℕ} (h : invSqrtBounds L U T = some (lam, ups)) {x : ℝ} (hT : 0 < T)
    (hL : (L : ℝ) ≤ T * x) (hU : (T : ℝ) * x ≤ U) :
    (lam : ℝ) / 2 ^ Q ≤ 1 / Real.sqrt x ∧ 1 / Real.sqrt x ≤ (ups : ℝ) / 2 ^ Q := by
  unfold invSqrtBounds at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  · rename_i hc
    obtain ⟨⟨⟨hL0, hU0⟩, hlam⟩, hups⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    set lam' := isqrt (4 ^ Q * T / U)
    set ups' := isqrt (4 ^ Q * T / L) + 1
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL0
    have hU' : (0 : ℝ) < U := by exact_mod_cast hU0
    have hx : 0 < x := by nlinarith
    have h4 : (4 : ℝ) ^ Q = (2 ^ Q) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hlam' : (lam' : ℝ) * lam' * U ≤ 4 ^ Q * T := by exact_mod_cast hlam
    have hups' : (4 : ℝ) ^ Q * T ≤ ups' * ups' * L := by exact_mod_cast hups
    have h2Q : (0 : ℝ) < 2 ^ Q := by positivity
    have A : (lam' : ℝ) ^ 2 * x ≤ (4 : ℝ) ^ Q := by
      have h1 : (lam' : ℝ) ^ 2 * ((T : ℝ) * x) ≤ (lam' : ℝ) ^ 2 * (U : ℝ) :=
        mul_le_mul_of_nonneg_left hU (by positivity)
      have h2 : (lam' : ℝ) ^ 2 * (U : ℝ) ≤ (4 : ℝ) ^ Q * (T : ℝ) := by rw [sq]; exact hlam'
      have h3 : (T : ℝ) * ((lam' : ℝ) ^ 2 * x) ≤ (T : ℝ) * (4 : ℝ) ^ Q := by nlinarith
      exact le_of_mul_le_mul_left h3 hT'
    have B : (4 : ℝ) ^ Q ≤ (ups' : ℝ) ^ 2 * x := by
      have h1 : (ups' : ℝ) ^ 2 * (L : ℝ) ≤ (ups' : ℝ) ^ 2 * ((T : ℝ) * x) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      have h2 : (4 : ℝ) ^ Q * (T : ℝ) ≤ (ups' : ℝ) ^ 2 * (L : ℝ) := by rw [sq]; exact hups'
      have h3 : (T : ℝ) * (4 : ℝ) ^ Q ≤ (T : ℝ) * ((ups' : ℝ) ^ 2 * x) := by nlinarith
      exact le_of_mul_le_mul_left h3 hT'
    rw [one_div, ← Real.sqrt_inv]
    constructor
    · rw [Real.le_sqrt (by positivity) (by positivity), div_pow, ← h4, div_le_iff₀ (by positivity),
        inv_mul_eq_div, le_div_iff₀ hx]
      exact A
    · rw [Real.sqrt_le_left (by positivity), div_pow, ← h4, le_div_iff₀ (by positivity),
        inv_mul_eq_div, div_le_iff₀ hx]
      exact B
  · exact absurd h (by simp)

/-- **The inverse square roots of an integer disc.** -/
theorem discInvSqrt_sound {d : IDisc} {lam ups : ℕ} (h : discInvSqrt d = some (lam, ups)) (hT : 0 < d.T) {z : ℂ}
    (hz : d.Mem z) : (lam : ℝ) / 2 ^ Q ≤ 1 / Real.sqrt ‖z‖ ∧ 1 / Real.sqrt ‖z‖ ≤ (ups : ℝ) / 2 ^ Q := by
  unfold discInvSqrt at h
  split at h
  · rename_i L U hm
    obtain ⟨h1, h2⟩ := modBounds_sound hm hT hz
    exact invSqrtBounds_sound h hT h1 h2
  · exact absurd h (by simp)

/-- **A disc that excludes `0`.** -/
theorem discNonzero_sound {d : IDisc} (h : discNonzero d = true) (hT : 0 < d.T) {z : ℂ} (hz : d.Mem z) : z ≠ 0 := by
  intro hz0
  subst hz0
  unfold IDisc.Mem at hz
  rw [zero_sub, norm_neg] at hz
  have hT' : (0 : ℝ) < d.T := by exact_mod_cast hT
  have hre := Complex.abs_re_le_norm d.center
  have him := Complex.abs_im_le_norm d.center
  simp only [IDisc.center, abs_div, Nat.abs_cast] at hre him
  unfold discNonzero at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  have ha : (d.a.natAbs : ℝ) = |(d.a : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hb : (d.b.natAbs : ℝ) = |(d.b : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rcases h with h | h
  · have h' : (d.R : ℝ) < d.a.natAbs := by exact_mod_cast h
    rw [ha] at h'
    have : |(d.a : ℝ)| / d.T ≤ d.R / d.T := hre.trans hz
    rw [div_le_div_iff_of_pos_right hT'] at this
    linarith
  · have h' : (d.R : ℝ) < d.b.natAbs := by exact_mod_cast h
    rw [hb] at h'
    have : |(d.b : ℝ)| / d.T ≤ d.R / d.T := him.trans hz
    rw [div_le_div_iff_of_pos_right hT'] at this
    linarith

/-! ## Rational discs -/

/-- A complex rational as a complex number. -/
def toC (z : CQ) : ℂ := ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

/-- Membership in a rational disc. -/
def QDisc.Mem (d : QDisc) (z : ℂ) : Prop := ‖z - toC d.c‖ ≤ (d.r : ℝ)

theorem qabs_cast (x : ℚ) : ((qabs x : ℚ) : ℝ) = |(x : ℝ)| := by
  unfold qabs
  split_ifs with h
  · have : (x : ℝ) < 0 := by exact_mod_cast h
    rw [Rat.cast_neg, abs_of_neg this]
  · have : (0 : ℝ) ≤ x := by exact_mod_cast not_lt.mp h
    rw [abs_of_nonneg this]

theorem norm_le_cabsUp (z : CQ) : ‖toC z‖ ≤ (cabsUp z : ℝ) := by
  unfold cabsUp
  rw [Rat.cast_add, qabs_cast, qabs_cast]
  exact Complex.norm_le_abs_re_add_abs_im _

theorem toC_cadd (z w : CQ) : toC (cadd z w) = toC z + toC w := by
  apply Complex.ext <;> simp [toC, cadd]

theorem toC_cmul (z w : CQ) : toC (cmul z w) = toC z * toC w := by
  apply Complex.ext <;> simp [toC, cmul]

theorem toC_csmul (c : ℚ) (z : CQ) : toC (csmul c z) = ((c : ℝ) : ℂ) * toC z := by
  apply Complex.ext <;> simp [toC, csmul]

theorem normSq_toC (z : CQ) : Complex.normSq (toC z) = ((cnormSq z : ℚ) : ℝ) := by
  simp [toC, cnormSq, Complex.normSq_apply]

theorem QDisc.Mem.r_nonneg {d : QDisc} {z : ℂ} (h : d.Mem z) : (0 : ℝ) ≤ d.r := (norm_nonneg _).trans h

theorem qadd_mem {d e : QDisc} {z w : ℂ} (hz : d.Mem z) (hw : e.Mem w) : (qadd d e).Mem (z + w) := by
  unfold QDisc.Mem qadd
  simp only [toC_cadd, Rat.cast_add]
  calc ‖z + w - (toC d.c + toC e.c)‖ = ‖(z - toC d.c) + (w - toC e.c)‖ := by ring_nf
    _ ≤ ‖z - toC d.c‖ + ‖w - toC e.c‖ := norm_add_le _ _
    _ ≤ d.r + e.r := add_le_add hz hw

theorem qmul_mem {d e : QDisc} {z w : ℂ} (hz : d.Mem z) (hw : e.Mem w) : (qmul d e).Mem (z * w) := by
  unfold QDisc.Mem qmul
  simp only [toC_cmul, Rat.cast_add, Rat.cast_mul]
  have hd := hz.r_nonneg
  have he := hw.r_nonneg
  have e1 : z * w - toC d.c * toC e.c =
      toC d.c * (w - toC e.c) + toC e.c * (z - toC d.c) + (z - toC d.c) * (w - toC e.c) := by ring
  rw [e1]
  have t1 : ‖toC d.c * (w - toC e.c) + toC e.c * (z - toC d.c) + (z - toC d.c) * (w - toC e.c)‖
      ≤ ‖toC d.c‖ * ‖w - toC e.c‖ + ‖toC e.c‖ * ‖z - toC d.c‖ + ‖z - toC d.c‖ * ‖w - toC e.c‖ := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
      rw [norm_mul]
  have n1 : ‖toC d.c‖ * ‖w - toC e.c‖ ≤ (cabsUp d.c : ℝ) * e.r :=
    mul_le_mul (norm_le_cabsUp _) hw (norm_nonneg _) ((norm_nonneg _).trans (norm_le_cabsUp _))
  have n2 : ‖toC e.c‖ * ‖z - toC d.c‖ ≤ (cabsUp e.c : ℝ) * d.r :=
    mul_le_mul (norm_le_cabsUp _) hz (norm_nonneg _) ((norm_nonneg _).trans (norm_le_cabsUp _))
  have n3 : ‖z - toC d.c‖ * ‖w - toC e.c‖ ≤ d.r * e.r := mul_le_mul hz hw (norm_nonneg _) hd
  linarith

theorem qsmul_mem (s : ℚ) {d : QDisc} {z : ℂ} (hz : d.Mem z) : (qsmul s d).Mem (((s : ℝ) : ℂ) * z) := by
  unfold QDisc.Mem qsmul
  simp only [toC_csmul, Rat.cast_mul, qabs_cast]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)

theorem normLo_sound {z : CQ} {lo : ℚ} (h : normLo z = some lo) : (lo : ℝ) ≤ ‖toC z‖ := by
  unfold normLo at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨h0, h1⟩ := hc
    rw [Complex.norm_def, normSq_toC]
    apply Real.le_sqrt_of_sq_le
    rw [sq]
    exact_mod_cast h1
  · exact absurd h (by simp)

theorem normHi_sound {z : CQ} {hi : ℚ} (h : normHi z = some hi) : ‖toC z‖ ≤ (hi : ℝ) := by
  unfold normHi at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨h0, h1⟩ := hc
    rw [Complex.norm_def, normSq_toC, Real.sqrt_le_left (by exact_mod_cast h0), sq]
    exact_mod_cast h1
  · exact absurd h (by simp)

theorem discUp_sound {d : QDisc} {u : ℚ} (h : discUp d = some u) {z : ℂ} (hz : d.Mem z) : ‖z‖ ≤ (u : ℝ) := by
  unfold discUp at h
  cases hh : normHi d.c with
  | none => rw [hh] at h; exact absurd h (by simp)
  | some hi =>
    rw [hh] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have := normHi_sound hh
    have h2 : ‖z‖ ≤ ‖toC d.c‖ + ‖z - toC d.c‖ := by
      have := norm_add_le (z - toC d.c) (toC d.c)
      rw [sub_add_cancel] at this
      linarith
    unfold QDisc.Mem at hz
    push_cast
    linarith

theorem discLo_sound {d : QDisc} {l : ℚ} (h : discLo d = some l) {z : ℂ} (hz : d.Mem z) : (l : ℝ) ≤ ‖z‖ := by
  unfold discLo at h
  cases hh : normLo d.c with
  | none => rw [hh] at h; exact absurd h (by simp)
  | some lo =>
    rw [hh] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have := normLo_sound hh
    have h1 : ‖toC d.c‖ - ‖z - toC d.c‖ ≤ ‖z‖ := by
      have := norm_sub_norm_le (toC d.c) (toC d.c - z)
      rw [sub_sub_cancel, norm_sub_rev] at this
      linarith
    unfold QDisc.Mem at hz
    push_cast
    linarith

/-- A lower bound of the modulus on a disc from `normLo` of the center. -/
theorem norm_ge_of_normLo {d : QDisc} {lo : ℚ} (h : normLo d.c = some lo) {z : ℂ} (hz : d.Mem z) :
    (lo : ℝ) - d.r ≤ ‖z‖ := by
  have := normLo_sound h
  have h1 : ‖toC d.c‖ - ‖z - toC d.c‖ ≤ ‖z‖ := by
    have := norm_sub_norm_le (toC d.c) (toC d.c - z)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  unfold QDisc.Mem at hz
  linarith

/-- An upper bound of the modulus on a disc from `normHi` of the center. -/
theorem norm_le_of_normHi {d : QDisc} {hi : ℚ} (h : normHi d.c = some hi) {z : ℂ} (hz : d.Mem z) :
    ‖z‖ ≤ (hi : ℝ) + d.r := by
  have := normHi_sound h
  have h2 : ‖z‖ ≤ ‖toC d.c‖ + ‖z - toC d.c‖ := by
    have := norm_add_le (z - toC d.c) (toC d.c)
    rw [sub_add_cancel] at this
    linarith
  unfold QDisc.Mem at hz
  linarith

/-! ## Square roots and reciprocals: `betaDisc` -/

theorem H_sq : ((H : ℕ) : ℝ) * (H : ℝ) = (S : ℝ) := by
  simp only [H, S, P]
  push_cast
  norm_num

/-- **The square-root covering**: `‖w − s₀‖ ‖w + s₀‖ ≤ δ` and `‖s₀‖ ≥ L > 0` give `‖σ w − s₀‖ ≤ δ/L` for a sign `σ`. -/
theorem sqrt_cover {w s0 : ℂ} {δ L : ℝ} (hδ : ‖w ^ 2 - s0 ^ 2‖ ≤ δ) (hL : 0 < L) (hLs : L ≤ ‖s0‖) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ ‖σ * w - s0‖ ≤ δ / L := by
  have hprod : ‖w - s0‖ * ‖w + s0‖ ≤ δ := by
    rw [← norm_mul, show (w - s0) * (w + s0) = w ^ 2 - s0 ^ 2 by ring]
    exact hδ
  have hsum : 2 * ‖s0‖ ≤ ‖w - s0‖ + ‖w + s0‖ := by
    have := norm_sub_le (w + s0) (w - s0)
    rw [show w + s0 - (w - s0) = 2 * s0 by ring, norm_mul, Complex.norm_two] at this
    linarith
  rcases le_total ‖w - s0‖ ‖w + s0‖ with hle | hle
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_mul, le_div_iff₀ hL]
    have hv : L ≤ ‖w + s0‖ := by linarith
    nlinarith [norm_nonneg (w - s0)]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [show -1 * w - s0 = -(w + s0) by ring, norm_neg, le_div_iff₀ hL]
    have hu : L ≤ ‖w - s0‖ := by linarith
    nlinarith [norm_nonneg (w + s0)]

/-- **The reciprocal on a disc**: `‖v − s₀‖ ≤ e < L ≤ ‖s₀‖` gives `‖μ/v − μ/s₀‖ ≤ μ e/(L (L − e))`. -/
theorem recip_bound {v s0 : ℂ} {e L μ : ℝ} (hμ : 0 ≤ μ) (he : ‖v - s0‖ ≤ e) (heL : e < L) (hLs : L ≤ ‖s0‖)
    (he0 : 0 ≤ e) : ‖(μ : ℂ) / v - μ / s0‖ ≤ μ * e / (L * (L - e)) := by
  have hL : 0 < L := lt_of_le_of_lt he0 heL
  have hs0 : s0 ≠ 0 := by intro h; rw [h, norm_zero] at hLs; linarith
  have hv_ge : L - e ≤ ‖v‖ := by
    have := norm_sub_norm_le s0 (s0 - v)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  have hv : v ≠ 0 := by intro h; rw [h, norm_zero] at hv_ge; linarith
  have eq : (μ : ℂ) / v - μ / s0 = μ * (s0 - v) / (v * s0) := by field_simp
  rw [eq, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ, norm_sub_rev]
  have hden : L * (L - e) ≤ ‖v‖ * ‖s0‖ := by
    have h1 : 0 ≤ L - e := by linarith
    calc L * (L - e) = (L - e) * L := by ring
      _ ≤ ‖v‖ * ‖s0‖ := mul_le_mul hv_ge hLs hL.le (norm_nonneg _)
  have hpos : 0 < L * (L - e) := mul_pos hL (by linarith)
  rw [div_le_div_iff₀ (mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hs0)) hpos]
  calc μ * ‖v - s0‖ * (L * (L - e)) ≤ μ * e * (L * (L - e)) := by gcongr
    _ ≤ μ * e * (‖v‖ * ‖s0‖) := by gcongr

/-- `‖s₀² − c‖ ≤ (|p² − q² − a| + |2pq − b|)/S` for `s₀ = (p + q i)/H`, `c = (a + b i)/S`, `H² = S`. -/
theorem gsq_bound (p q a b : ℤ) {Hr Sr : ℝ} (hH : 0 < Hr) (hHS : Hr * Hr = Sr) :
    ‖(⟨(p : ℝ) / Hr, (q : ℝ) / Hr⟩ : ℂ) ^ 2 - ⟨(a : ℝ) / Sr, (b : ℝ) / Sr⟩‖ ≤
      (|((p * p - q * q - a : ℤ) : ℝ)| + |((2 * p * q - b : ℤ) : ℝ)|) / Sr := by
  have hS : 0 < Sr := by rw [← hHS]; positivity
  have e1 : (⟨(p : ℝ) / Hr, (q : ℝ) / Hr⟩ : ℂ) ^ 2 - ⟨(a : ℝ) / Sr, (b : ℝ) / Sr⟩ =
      ⟨((p * p - q * q - a : ℤ) : ℝ) / Sr, ((2 * p * q - b : ℤ) : ℝ) / Sr⟩ := by
    apply Complex.ext
    · simp only [sq, Complex.sub_re, Complex.mul_re]
      rw [← hHS]
      push_cast
      field_simp
    · simp only [sq, Complex.sub_im, Complex.mul_im]
      rw [← hHS]
      push_cast
      field_simp
      ring
  rw [e1]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [abs_div, abs_of_pos hS]
  rw [← add_div]

/-- `max(|p|, |q|)/H ≤ ‖(p + q i)/H‖`. -/
theorem max_le_norm (p q : ℤ) {Hr : ℝ} (hH : 0 < Hr) :
    ((max p.natAbs q.natAbs : ℕ) : ℝ) / Hr ≤ ‖(⟨(p : ℝ) / Hr, (q : ℝ) / Hr⟩ : ℂ)‖ := by
  have hre := Complex.abs_re_le_norm (⟨(p : ℝ) / Hr, (q : ℝ) / Hr⟩ : ℂ)
  have him := Complex.abs_im_le_norm (⟨(p : ℝ) / Hr, (q : ℝ) / Hr⟩ : ℂ)
  simp only [abs_div, abs_of_pos hH] at hre him
  rcases le_total p.natAbs q.natAbs with hpq | hpq
  · rw [max_eq_right hpq, Nat.cast_natAbs, Int.cast_abs]
    exact him
  · rw [max_eq_left hpq, Nat.cast_natAbs, Int.cast_abs]
    exact hre

/-- The center `μ/s₀` of a β-disc. -/
theorem toC_recip (μ : ℕ) (s : CQ) :
    toC ((μ : ℚ) * s.1 / cnormSq s, -((μ : ℚ) * s.2) / cnormSq s) = ((μ : ℝ) : ℂ) / toC s := by
  apply Complex.ext
  · rw [Complex.div_re, normSq_toC]
    simp [toC]
  · rw [Complex.div_im, normSq_toC]
    simp [toC]
    ring

/-- **The β-disc**: if `w² = X` and `X` lies in the disc `d`, then `σ μ/w` lies in `betaDisc μ d` for a sign `σ`. -/
theorem betaDisc_sound {mu : ℕ} {d : IDisc} {B : QDisc} (h : betaDisc mu d = some B) {X w : ℂ} (hX : d.Mem X)
    (hw : w ^ 2 = X) : ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ B.Mem (σ * ((mu : ℂ) / w)) := by
  unfold betaDisc at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  · rename_i hc
    obtain ⟨⟨hT, hL⟩, heL⟩ := hc
    simp only [Option.some.injEq] at h
    subst h
    generalize hpq : gsqrt d.a d.b = pq at *
    obtain ⟨p, q⟩ := pq
    simp only at hL heL ⊢
    have hH : (0 : ℝ) < (H : ℝ) := by simp only [H]; positivity
    have hS : (0 : ℝ) < (S : ℝ) := by simp only [S]; positivity
    have hs0 : toC ((p : ℚ) / (H : ℚ), (q : ℚ) / (H : ℚ)) = ⟨(p : ℝ) / (H : ℝ), (q : ℝ) / (H : ℝ)⟩ := by
      simp [toC]
    -- `‖w² − s₀²‖ ≤ δ`
    set δr : ℝ := ((((((p * p - q * q - d.a).natAbs + (2 * p * q - d.b).natAbs : ℕ) : ℚ) + (d.R : ℚ)) / (S : ℚ) : ℚ) : ℝ)
      with hδr
    have hδ : ‖w ^ 2 - (toC ((p : ℚ) / (H : ℚ), (q : ℚ) / (H : ℚ))) ^ 2‖ ≤ δr := by
      rw [hw, hs0]
      have hc := gsq_bound p q d.a d.b hH H_sq
      have hXc : ‖X - d.center‖ ≤ (d.R : ℝ) / S := by
        have := hX
        unfold IDisc.Mem at this
        rwa [hT] at this
      have hcen : d.center = ⟨(d.a : ℝ) / (S : ℝ), (d.b : ℝ) / (S : ℝ)⟩ := by simp [IDisc.center, hT]
      rw [hcen] at hXc
      have tri : ‖X - (⟨(p : ℝ) / (H : ℝ), (q : ℝ) / (H : ℝ)⟩ : ℂ) ^ 2‖ ≤
          ‖X - ⟨(d.a : ℝ) / (S : ℝ), (d.b : ℝ) / (S : ℝ)⟩‖ +
            ‖(⟨(p : ℝ) / (H : ℝ), (q : ℝ) / (H : ℝ)⟩ : ℂ) ^ 2 - ⟨(d.a : ℝ) / (S : ℝ), (d.b : ℝ) / (S : ℝ)⟩‖ := by
        rw [← norm_neg ((⟨(p : ℝ) / (H : ℝ), (q : ℝ) / (H : ℝ)⟩ : ℂ) ^ 2 - _)]
        refine (norm_add_le _ _).trans_eq' ?_
        ring_nf
      refine tri.trans ?_
      rw [hδr]
      push_cast
      rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
      push_cast at hc ⊢
      rw [add_div, add_div]
      rw [add_div] at hc
      linarith
    -- `L ≤ ‖s₀‖`
    set Lr : ℝ := ((((max p.natAbs q.natAbs : ℕ) : ℚ) / (H : ℚ) : ℚ) : ℝ) with hLr
    have hLs : Lr ≤ ‖toC ((p : ℚ) / (H : ℚ), (q : ℚ) / (H : ℚ))‖ := by
      rw [hs0, hLr]
      have := max_le_norm p q hH
      push_cast at this ⊢
      exact this
    have hL' : (0 : ℝ) < Lr := by rw [hLr]; exact_mod_cast hL
    obtain ⟨σ, hσ, hcov⟩ := sqrt_cover hδ hL' hLs
    refine ⟨σ, hσ, ?_⟩
    have hδ0 : (0 : ℝ) ≤ δr := (norm_nonneg _).trans hδ
    have he0 : (0 : ℝ) ≤ δr / Lr := div_nonneg hδ0 hL'.le
    have heL' : δr / Lr < Lr := by
      rw [hδr, hLr]
      exact_mod_cast heL
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hval : σ * ((mu : ℂ) / w) = ((mu : ℝ) : ℂ) / (σ * w) := by
      push_cast
      field_simp
      rw [sq, hσ2, one_mul]
    unfold QDisc.Mem
    dsimp only
    have hcen := toC_recip mu ((p : ℚ) / (H : ℚ), (q : ℚ) / (H : ℚ))
    dsimp only at hcen
    rw [hval, hcen]
    have key := recip_bound (μ := (mu : ℝ)) (by positivity) hcov heL' hLs he0
    convert key using 2
    rw [hδr, hLr]
    push_cast
    ring
  · exact absurd h (by simp)

/-- **A disc with inverse square-root bounds excludes `0`**: the lower bound `L > 0` of `T‖z‖` is checked. -/
theorem discInvSqrt_ne_zero {d : IDisc} {lam ups : ℕ} (h : discInvSqrt d = some (lam, ups)) (hT : 0 < d.T) {z : ℂ}
    (hz : d.Mem z) : z ≠ 0 := by
  unfold discInvSqrt at h
  split at h
  · rename_i L U hm
    obtain ⟨h1, -⟩ := modBounds_sound hm hT hz
    unfold invSqrtBounds at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    split at h
    · rename_i hc
      have hL0 : (0 : ℝ) < L := by exact_mod_cast hc.1.1.1
      intro hz0
      rw [hz0, norm_zero, mul_zero] at h1
      linarith
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **A disc with a β-disc excludes `0`**: `‖X − s₀²‖ ≤ δ < L² ≤ ‖s₀‖²` on the disc. -/
theorem betaDisc_X_ne_zero {mu : ℕ} {d : IDisc} {B : QDisc} (h : betaDisc mu d = some B) {X : ℂ} (hX : d.Mem X) :
    X ≠ 0 := by
  unfold betaDisc at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  split at h
  · rename_i hc
    obtain ⟨⟨hT, hL⟩, heL⟩ := hc
    generalize hpq : gsqrt d.a d.b = pq at *
    obtain ⟨p, q⟩ := pq
    simp only at hL heL
    have hH : (0 : ℝ) < (H : ℝ) := by simp only [H]; positivity
    have hS : (0 : ℝ) < (S : ℝ) := by simp only [S]; positivity
    set s0 : ℂ := ⟨(p : ℝ) / (H : ℝ), (q : ℝ) / (H : ℝ)⟩ with hs0
    set δr : ℝ := ((((((p * p - q * q - d.a).natAbs + (2 * p * q - d.b).natAbs : ℕ) : ℚ) + (d.R : ℚ)) / (S : ℚ) : ℚ) : ℝ)
      with hδr
    have hδ : ‖X - s0 ^ 2‖ ≤ δr := by
      have hc := gsq_bound p q d.a d.b hH H_sq
      have hXc : ‖X - d.center‖ ≤ (d.R : ℝ) / S := by
        have := hX
        unfold IDisc.Mem at this
        rwa [hT] at this
      have hcen : d.center = ⟨(d.a : ℝ) / (S : ℝ), (d.b : ℝ) / (S : ℝ)⟩ := by simp [IDisc.center, hT]
      rw [hcen] at hXc
      have tri : ‖X - s0 ^ 2‖ ≤ ‖X - ⟨(d.a : ℝ) / (S : ℝ), (d.b : ℝ) / (S : ℝ)⟩‖ +
            ‖s0 ^ 2 - ⟨(d.a : ℝ) / (S : ℝ), (d.b : ℝ) / (S : ℝ)⟩‖ := by
        rw [← norm_neg (s0 ^ 2 - _)]
        refine (norm_add_le _ _).trans_eq' ?_
        ring_nf
      refine tri.trans ?_
      rw [hδr]
      push_cast
      rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
      push_cast at hc ⊢
      rw [add_div, add_div]
      rw [add_div] at hc
      linarith
    set Lr : ℝ := ((((max p.natAbs q.natAbs : ℕ) : ℚ) / (H : ℚ) : ℚ) : ℝ) with hLr
    have hLs : Lr ≤ ‖s0‖ := by
      rw [hs0, hLr]
      have := max_le_norm p q hH
      push_cast at this ⊢
      exact this
    have hL' : (0 : ℝ) < Lr := by rw [hLr]; exact_mod_cast hL
    have heL' : δr / Lr < Lr := by
      rw [hδr, hLr]
      exact_mod_cast heL
    have hδL : δr < Lr * Lr := by rwa [div_lt_iff₀ hL'] at heL'
    intro hX0
    rw [hX0, zero_sub, norm_neg, norm_pow] at hδ
    nlinarith [norm_nonneg s0]
  · exact absurd h (by simp)

/-! ## The sums of Lemma 6.17(b) -/

/-- `ρ = (m₆/m₅)^{3/2} = 2√2` at `(m₅, m₆) = (1, 2)`. -/
noncomputable def rho : ℝ := 2 * Real.sqrt 2

theorem rho_sq : rho ^ 2 = 8 := by
  unfold rho
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem sqrt_one_add_rho_sq : Real.sqrt (1 + rho ^ 2) = 3 := by
  rw [rho_sq, show (1 : ℝ) + 8 = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `ρ₀ ≤ ρ ≤ ρ₀ + 2^-Q`. -/
theorem rho_mem (h : rho0OK = true) : |rho - (rho0 : ℝ)| ≤ (eta : ℝ) := by
  unfold rho0OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have h0' : (0 : ℝ) ≤ rho0 := by exact_mod_cast h0
  have h1' : (rho0 : ℝ) * rho0 ≤ 8 := by exact_mod_cast h1
  have h2' : (8 : ℝ) ≤ ((rho0 : ℝ) + eta) * ((rho0 : ℝ) + eta) := by exact_mod_cast h2
  have heta : (0 : ℝ) ≤ eta := by simp only [eta]; push_cast; positivity
  have hr : 0 ≤ rho := by unfold rho; positivity
  have hr2 : rho * rho = 8 := by rw [← sq]; exact rho_sq
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The factor `1 + i s ρ` lies in `factorDisc s` for `s = ±1`. -/
theorem factorDisc_mem (h : rho0OK = true) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (factorDisc s).Mem (1 + Complex.I * ((s : ℂ) * (rho : ℂ))) := by
  unfold QDisc.Mem factorDisc
  have e : 1 + Complex.I * ((s : ℂ) * (rho : ℂ)) - toC (1, (s : ℚ) * rho0) =
      Complex.I * ((((s : ℝ) * (rho - rho0)) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [toC]; ring
  rw [e, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hs' : |(s : ℝ)| = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [hs', one_mul]
  exact rho_mem h

/-- **The sum of Lemma 6.17(b) lies in `sumDisc3`** (with `ε₁ = 1`). -/
theorem sumDisc3_mem (h : rho0OK = true) {B1 B2 B3 : QDisc} {b1 b2 b3 : ℂ} (h1 : B1.Mem b1) (h2 : B2.Mem b2)
    (h3 : B3.Mem b3) {e2 e3 s1 s2 s3 : ℤ} (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (hs3 : s3 = 1 ∨ s3 = -1) :
    (sumDisc3 B1 B2 B3 e2 e3 s1 s2 s3).Mem
      (b1 * (1 + Complex.I * ((s1 : ℂ) * (rho : ℂ))) + (e2 : ℂ) * (b2 * (1 + Complex.I * ((s2 : ℂ) * (rho : ℂ)))) +
        (e3 : ℂ) * (b3 * (1 + Complex.I * ((s3 : ℂ) * (rho : ℂ))))) := by
  unfold sumDisc3
  have q2 := qsmul_mem (e2 : ℚ) (qmul_mem h2 (factorDisc_mem h hs2))
  have q3 := qsmul_mem (e3 : ℚ) (qmul_mem h3 (factorDisc_mem h hs3))
  push_cast at q2 q3
  exact qadd_mem (qadd_mem (qmul_mem h1 (factorDisc_mem h hs1)) q2) q3

end Lean6.Special.D88.Boxes
