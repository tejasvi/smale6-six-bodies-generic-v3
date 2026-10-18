import Lean6.Special.Comp.D98.UPoly
import Mathlib

/-!
# Dense integer polynomials: semantics

`toPoly p` is the polynomial of `ℤ[X]` with coefficient list `p`. The operations of
`Lean6.Special.Comp.D98.UPoly` are those of `ℤ[X]` (`toPoly_add`, `toPoly_mul`, `toPoly_deriv`, `toPoly_comp`, …), a
successful identity test is an identity in `ℤ[X]` (`eqv_sound`), and `degLead_sound` reads off the degree and the
leading coefficient.
-/

namespace Lean6.Special.D98

open Polynomial Lean6.Special.Comp.D98

/-- The polynomial with coefficient list `p` (constant term first). -/
noncomputable def toPoly : UP → ℤ[X]
  | [] => 0
  | a :: p => C a + X * toPoly p

@[simp] theorem toPoly_nil : toPoly [] = 0 := rfl

@[simp] theorem toPoly_cons (a : ℤ) (p : UP) : toPoly (a :: p) = C a + X * toPoly p := rfl

theorem toPoly_add : ∀ p q : UP, toPoly (UP.add p q) = toPoly p + toPoly q
  | [], q => by simp [UP.add]
  | a :: p, [] => by simp [UP.add]
  | a :: p, b :: q => by
    simp only [UP.add, toPoly_cons, toPoly_add p q, C_add]
    ring

theorem toPoly_neg (p : UP) : toPoly (UP.neg p) = -toPoly p := by
  induction p with
  | nil => simp [UP.neg]
  | cons a p ih =>
    simp only [UP.neg, List.map_cons, toPoly_cons] at ih ⊢
    rw [ih, C_neg]
    ring

theorem toPoly_sub (p q : UP) : toPoly (UP.sub p q) = toPoly p - toPoly q := by
  rw [UP.sub, toPoly_add, toPoly_neg, sub_eq_add_neg]

theorem toPoly_scale (c : ℤ) (p : UP) : toPoly (UP.scale c p) = C c * toPoly p := by
  induction p with
  | nil => simp [UP.scale]
  | cons a p ih =>
    simp only [UP.scale, List.map_cons, toPoly_cons] at ih ⊢
    rw [ih, C_mul]
    ring

theorem toPoly_mul : ∀ p q : UP, toPoly (UP.mul p q) = toPoly p * toPoly q
  | [], _ => by simp [UP.mul]
  | a :: p, [] => by simp [UP.mul]
  | a :: p, b :: q => by
    rw [UP.mul, toPoly_add, toPoly_scale, toPoly_cons 0, toPoly_mul p (b :: q), toPoly_cons a]
    simp only [C_0]
    ring

theorem toPoly_pow (p : UP) : ∀ n, toPoly (UP.pow p n) = toPoly p ^ n
  | 0 => by simp [UP.pow]
  | n + 1 => by rw [UP.pow, toPoly_mul, toPoly_pow p n, pow_succ]

theorem toPoly_deriv : ∀ p : UP, toPoly (UP.deriv p) = derivative (toPoly p)
  | [] => by simp [UP.deriv]
  | a :: p => by
    rw [UP.deriv, toPoly_add, toPoly_cons 0, toPoly_deriv p, toPoly_cons]
    simp only [C_0, zero_add, derivative_add, derivative_C, derivative_mul, derivative_X, one_mul]
    try ring

theorem toPoly_comp (p q : UP) : toPoly (UP.comp p q) = (toPoly p).comp (toPoly q) := by
  induction p with
  | nil => simp [UP.comp]
  | cons a p ih =>
    have e : UP.comp (a :: p) q = UP.add [a] (UP.mul q (UP.comp p q)) := rfl
    rw [e, toPoly_add, toPoly_mul, ih, toPoly_cons, toPoly_cons a]
    simp only [toPoly_nil, mul_zero, add_zero, add_comp, C_comp, mul_comp, X_comp]
    try ring

theorem toPoly_isZero : ∀ p : UP, UP.isZero p = true → toPoly p = 0
  | [], _ => rfl
  | a :: p, h => by
    simp only [UP.isZero, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [toPoly_cons, h.1, toPoly_isZero p h.2]
    simp

/-- **The identity test is sound.** -/
theorem eqv_sound {p q : UP} (h : UP.eqv p q = true) : toPoly p = toPoly q := by
  have := toPoly_isZero _ h
  rw [toPoly_sub] at this
  exact sub_eq_zero.mp this

/-- **Degree and leading coefficient**: a list of `d + 1` coefficients ending with `lc ≠ 0`. -/
theorem degLead_sound : ∀ {p : UP} {d : ℕ} {lc : ℤ}, UP.degLead p d lc = true →
    (toPoly p).natDegree = d ∧ (toPoly p).leadingCoeff = lc
  | [], d, lc, h => by simp [UP.degLead] at h
  | [a], d, lc, h => by
    simp only [UP.degLead, List.length_singleton, List.getLast?_singleton, Bool.and_eq_true, beq_iff_eq,
      Option.some.injEq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hd, ha⟩, -⟩ := h
    subst ha
    simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, natDegree_C, leadingCoeff_C]
    exact ⟨by omega, by simp⟩
  | a :: b :: p, d, lc, h => by
    simp only [UP.degLead, List.length_cons, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hd, hl⟩, hlc⟩ := h
    have hl' : (b :: p).getLast? = some lc := by
      rw [List.getLast?_cons_cons] at hl
      exact hl
    have ih := degLead_sound (p := b :: p) (d := d - 1) (lc := lc) (by
      simp only [UP.degLead, List.length_cons, hl', Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
      exact ⟨⟨by omega, trivial⟩, hlc⟩)
    obtain ⟨h1, h2⟩ := ih
    have hq0 : toPoly (b :: p) ≠ 0 := by
      intro h0
      rw [h0, leadingCoeff_zero] at h2
      exact hlc h2.symm
    have hXq : (X * toPoly (b :: p)).natDegree = d := by
      rw [natDegree_X_mul hq0, h1]
      omega
    have hlt : (C a).natDegree < (X * toPoly (b :: p)).natDegree := by
      rw [natDegree_C, hXq]
      omega
    rw [toPoly_cons a]
    refine ⟨?_, ?_⟩
    · rw [natDegree_add_eq_right_of_natDegree_lt hlt, hXq]
    · rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hlt), mul_comm X, leadingCoeff_mul_X, h2]

end Lean6.Special.D98
