import Lean6.Special.K4.E4.AlgebraIds
import Mathlib.Tactic.Linarith

/-!
# The remaining steps of cases (I)–(III) in the proof of Lemma 7.7

The steps of the hand proof that divide or exclude cases, with `w = j` a root of `w² + w + 1 = 0` in `ℂ`; the
polynomial identities are in `AlgebraIds`. `caseIII` is the whole argument of case (III): the four equations in
`s₀, …, s₃` and `Σ p³ = 0` (that is `3 s₁ s₂ s₃ = s₀³`) force `s = 0`.
-/

namespace Lean6.Special.K4.E4.Alg

variable {w : ℂ}

/-- `j` is not real. -/
theorem omega_ne_real (hw : w ^ 2 + w + 1 = 0) (c : ℝ) : w ≠ c := by
  intro h
  rw [h] at hw
  have h2 : ((c ^ 2 + c + 1 : ℝ) : ℂ) = 0 := by push_cast; exact hw
  have h3 : c ^ 2 + c + 1 = 0 := by exact_mod_cast h2
  nlinarith [sq_nonneg (c + 1 / 2)]

theorem ne_21 (hw : w ^ 2 + w + 1 = 0) : (21 : ℂ) - 3 * w ≠ 0 := fun h =>
  omega_ne_real hw 7 (by push_cast; linear_combination (-1 / 3 : ℂ) * h)

theorem ne_14 (hw : w ^ 2 + w + 1 = 0) : (1 : ℂ) - 4 * w ≠ 0 := fun h =>
  omega_ne_real hw (1 / 4) (by push_cast; linear_combination (-1 / 4 : ℂ) * h)

theorem ne_w24 (hw : w ^ 2 + w + 1 = 0) : w ^ 2 - 4 ≠ 0 := by
  intro h
  have h5 : w = -5 := by linear_combination hw - h
  rw [h5] at h
  norm_num at h

theorem ne_46 (hw : w ^ 2 + w + 1 = 0) : (4 : ℂ) + 6 * w ≠ 0 := fun h =>
  omega_ne_real hw (-2 / 3) (by push_cast; linear_combination (1 / 6 : ℂ) * h)

/-- Case (I), all `p_k = r ≠ 0`: `r = 3` and `Σ p³ = 108`. -/
theorem caseI_equal (r : ℂ) (hr : r ≠ 0) (h : r ^ 2 + r = 4 * r) : r = 3 ∧ 4 * r ^ 3 = 108 := by
  have h3 : r = 3 := by
    have : r * (r - 3) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hr
    · linear_combination h0
  exact ⟨h3, by rw [h3]; norm_num⟩

/-- Case (II), `p₂ = p₃ = a = −ζ b`, `p₁ = p₄ = b ≠ 0`: the two equations divided by `b`. -/
theorem caseII_equal_div (z a b : ℂ) (hb : b ≠ 0) (ha : a = -z * b) (h2 : b + a + b = a ^ 2)
    (h1 : a + a + w * b = b ^ 2) : 2 - z = z ^ 2 * b ∧ b = w - 2 * z := by
  subst ha
  have e2 : b * (2 - z - z ^ 2 * b) = 0 := by linear_combination h2
  have e1 : b * (w - 2 * z - b) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp e2 with h | h
  · exact absurd h hb
  rcases mul_eq_zero.mp e1 with h' | h'
  · exact absurd h' hb
  exact ⟨by linear_combination h, by linear_combination -h'⟩

/-- The cube roots of unity are `1, j, j²`. -/
theorem cube_roots (hw : w ^ 2 + w + 1 = 0) (z : ℂ) (hz : z ^ 3 = 1) : z = 1 ∨ z = w ∨ z = w ^ 2 := by
  have h0 := cube_roots_factor w z hw
  have h : (z - 1) * (z - w) * (z - w ^ 2) = 0 := by linear_combination h0 + hz
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (Or.inl (by linear_combination h))
  · exact Or.inr (Or.inr (by linear_combination h))

/-- Case (II): `ζ² − 4ζ + j ≠ 0` for `ζ = 1, j, j²`. -/
theorem caseII_equal_fails (hw : w ^ 2 + w + 1 = 0) (z : ℂ) (hz : z = 1 ∨ z = w ∨ z = w ^ 2) :
    z ^ 2 - 4 * z + w ≠ 0 := by
  intro h
  rcases hz with rfl | rfl | rfl
  · exact omega_ne_real hw 3 (by push_cast; linear_combination h)
  · exact omega_ne_real hw (-1 / 4) (by push_cast; linear_combination (-1 / 4 : ℂ) * h + (1 / 4 : ℂ) * hw)
  · exact omega_ne_real hw (-2 / 3) (by
      push_cast; linear_combination (1 / 6 : ℂ) * h + (-(1 / 6 : ℂ) * w ^ 2 + (1 / 6 : ℂ) * w + 2 / 3) * hw)

/-- Case (II), the root of `2a(1 − 4j) + 2 − 2j`. -/
theorem caseII_b_root (a : ℂ) (h : 2 * a * (1 - 4 * w) + 2 - 2 * w = 0) : a * (1 - 4 * w) = w - 1 := by
  linear_combination (1 / 2 : ℂ) * h

/-- Case (II), the root of `2b(j² − 4) + 2 − 2j`. -/
theorem caseII_c_root (b : ℂ) (h : 2 * b * (w ^ 2 - 4) + 2 - 2 * w = 0) : b * (w ^ 2 - 4) = w - 1 := by
  linear_combination (1 / 2 : ℂ) * h

/-- **Case (III)**: the four equations and `3 s₁ s₂ s₃ = s₀³` force `s = 0` (so `p = 0`). -/
theorem caseIII (hw : w ^ 2 + w + 1 = 0) (s0 s1 s2 s3 : ℂ) (e0 : s0 ^ 2 + s1 ^ 2 + s2 ^ 2 + s3 ^ 2 = 0)
    (e1 : s1 * (4 - s0) = s2 * s3) (e2 : s2 * (2 * (-2 - 2 * w) - s0) = s1 * s3)
    (e3 : s3 * (2 * (2 * w) - s0) = s1 * s2) (hc : 3 * s1 * s2 * s3 - s0 ^ 3 = 0) :
    s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 := by
  have hw0 : w ≠ 0 := fun h => omega_ne_real hw 0 (by simpa using h)
  have hw1 : (-2 - 2 * w : ℂ) ≠ 0 := fun h => omega_ne_real hw (-1) (by push_cast; linear_combination (-1 / 2 : ℂ) * h)
  by_cases h : s1 * s2 * s3 = 0
  · have hs0 : s0 = 0 := by
      have : s0 ^ 3 = 0 := by linear_combination (3 : ℂ) * h - hc
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    subst hs0
    rcases mul_eq_zero.mp h with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · subst h1
        have hs2 : s2 = 0 := by
          have : s2 * (2 * (-2 - 2 * w)) = 0 := by linear_combination e2
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd (by linear_combination (1 / 2 : ℂ) * h) hw1
        have hs3 : s3 = 0 := by
          have : s3 * (4 * w) = 0 := by linear_combination e3
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd (by linear_combination (1 / 4 : ℂ) * h) hw0
        exact ⟨rfl, rfl, hs2, hs3⟩
      · subst h2
        have hs1 : s1 = 0 := by linear_combination (1 / 4 : ℂ) * e1
        subst hs1
        have hs3 : s3 = 0 := by
          have : s3 * (4 * w) = 0 := by linear_combination e3
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd (by linear_combination (1 / 4 : ℂ) * h) hw0
        exact ⟨rfl, rfl, rfl, hs3⟩
    · subst h3
      have hs1 : s1 = 0 := by linear_combination (1 / 4 : ℂ) * e1
      subst hs1
      have hs2 : s2 = 0 := by
        have : s2 * (2 * (-2 - 2 * w)) = 0 := by linear_combination e2
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (by linear_combination (1 / 2 : ℂ) * h) hw1
      exact ⟨rfl, rfl, hs2, rfl⟩
  · exfalso
    have h1 : s1 ≠ 0 := fun h0 => h (by rw [h0]; ring)
    have h2 : s2 ≠ 0 := fun h0 => h (by rw [h0]; ring)
    have h3 : s3 ≠ 0 := fun h0 => h (by rw [h0]; ring)
    have hA : (s1 ^ 2 - (2 * (-2 - 2 * w) - s0) * (2 * (2 * w) - s0)) * (s2 * s3) = 0 := by
      linear_combination (-(s3 * (2 * (2 * w) - s0))) * e2 + (-(s1 * s3)) * e3
    have hB : (s2 ^ 2 - (4 - s0) * (2 * (2 * w) - s0)) * (s1 * s3) = 0 := by
      linear_combination (-(s3 * (2 * (2 * w) - s0))) * e1 + (-(s2 * s3)) * e3
    have hC : (s3 ^ 2 - (4 - s0) * (2 * (-2 - 2 * w) - s0)) * (s1 * s2) = 0 := by
      linear_combination (-(s2 * (2 * (-2 - 2 * w) - s0))) * e1 + (-(s2 * s3)) * e2
    have hA' := (mul_eq_zero.mp hA).resolve_right (mul_ne_zero h2 h3)
    have hB' := (mul_eq_zero.mp hB).resolve_right (mul_ne_zero h1 h3)
    have hC' := (mul_eq_zero.mp hC).resolve_right (mul_ne_zero h1 h2)
    have hs0 : s0 ^ 2 = 0 := by
      linear_combination (1 / 4 : ℂ) * e0 - (1 / 4 : ℂ) * hA' - (1 / 4 : ℂ) * hB' - (1 / 4 : ℂ) * hC' +
        (4 : ℂ) * hw
    have : s0 = 0 := pow_eq_zero_iff (by norm_num) |>.mp hs0
    subst this
    apply h
    linear_combination (1 / 3 : ℂ) * hc

end Lean6.Special.K4.E4.Alg
