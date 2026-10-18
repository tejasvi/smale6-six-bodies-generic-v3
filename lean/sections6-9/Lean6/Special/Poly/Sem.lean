import Lean6.Special.Comp.Poly
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Evaluation of sparse polynomials

`Poly.eval h x p` evaluates the list `p` at the point `x : ℕ → R` of a commutative ring `R`, through a coefficient map
`h : C.Hom R` (a map `α → R` that turns the operations of `C` into those of `R`). Every operation of
`Lean6.Special.Comp.Poly` commutes with evaluation (`eval_add`, `eval_mul`, `eval_normalize`, `eval_subst`, …), so
`isZero_sound`: if `isZero C p = true`, then `p` evaluates to `0` at every point of every such ring; with `R` a ring of
polynomials this is an identity of polynomials.
-/

namespace Lean6.Special

open Lean6.Special.Comp

/-- A map of coefficients into a commutative ring that respects the operations of `C`. -/
structure Comp.Coeff.Hom {α : Type} (C : Coeff α) (R : Type*) [CommRing R] where
  f : α → R
  map_zero : f C.zero = 0
  map_one : f C.one = 1
  map_add : ∀ a b, f (C.add a b) = f a + f b
  map_mul : ∀ a b, f (C.mul a b) = f a * f b
  map_neg : ∀ a, f (C.neg a) = -f a
  map_isZero : ∀ a, C.isZero a = true → f a = 0

namespace Mono

variable {R : Type*} [CommRing R]

/-- The value of a monomial whose first exponent belongs to the variable `i`. -/
def eval (x : ℕ → R) : Mono → ℕ → R
  | [], _ => 1
  | e :: m, i => x i ^ e * eval x m (i + 1)

theorem eval_mul (x : ℕ → R) : ∀ (m k : Mono) (i : ℕ), eval x (Mono.mul m k) i = eval x m i * eval x k i
  | [], k, i => by simp [Mono.mul, eval]
  | a :: m, [], i => by simp [Mono.mul, eval]
  | a :: m, b :: k, i => by
    simp only [Mono.mul, eval, eval_mul x m k (i + 1), pow_add]
    ring

theorem eval_trim (x : ℕ → R) : ∀ (m : Mono) (i : ℕ), eval x (Mono.trim m) i = eval x m i
  | [], i => rfl
  | a :: m, i => by
    simp only [Mono.trim]
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
      obtain ⟨ha, ht⟩ := h
      have := eval_trim x m (i + 1)
      rw [ht] at this
      simp only [eval, ha, pow_zero, one_mul]
      rw [← this]
      rfl
    · simp only [eval, eval_trim x m (i + 1)]

theorem eval_replicate_zero (x : ℕ → R) : ∀ (n : ℕ) (m : Mono) (i : ℕ),
    eval x (List.replicate n 0 ++ m) i = eval x m (i + n)
  | 0, m, i => by simp
  | n + 1, m, i => by
    simp only [List.replicate_succ, List.cons_append, eval, pow_zero, one_mul]
    rw [eval_replicate_zero x n m (i + 1)]
    congr 1
    omega

theorem eval_var (x : ℕ → R) (j : ℕ) : eval x (Mono.var j) 0 = x j := by
  simp [Mono.var, eval_replicate_zero, eval]

end Mono

namespace Poly

variable {α : Type} {C : Coeff α} {R : Type*} [CommRing R]

/-- The value of a polynomial at `x`. -/
def eval (h : C.Hom R) (x : ℕ → R) (p : Poly α) : R :=
  (p.map fun t => h.f t.1 * Mono.eval x t.2 0).sum

variable (h : C.Hom R) (x : ℕ → R)

@[simp] theorem eval_nil : eval h x [] = 0 := rfl

@[simp] theorem eval_cons (t : α × Mono) (p : Poly α) :
    eval h x (t :: p) = h.f t.1 * Mono.eval x t.2 0 + eval h x p := by
  simp [eval]

theorem eval_append (p q : Poly α) : eval h x (p ++ q) = eval h x p + eval h x q := by
  simp [eval]

theorem eval_add (p q : Poly α) : eval h x (Poly.add p q) = eval h x p + eval h x q :=
  eval_append h x p q

theorem eval_const (c : α) : eval h x (Poly.const c) = h.f c := by
  simp [Poly.const, Mono.eval]

theorem eval_var (j : ℕ) : eval h x (Poly.var C j) = x j := by
  simp [Poly.var, Mono.eval_var, h.map_one]

theorem eval_neg (p : Poly α) : eval h x (Poly.neg C p) = -eval h x p := by
  induction p with
  | nil => simp [Poly.neg]
  | cons t p ih =>
    simp only [Poly.neg, List.map_cons, eval_cons, h.map_neg] at ih ⊢
    rw [ih]
    ring

theorem eval_sub (p q : Poly α) : eval h x (Poly.sub C p q) = eval h x p - eval h x q := by
  rw [Poly.sub, eval_append, eval_neg]
  ring

theorem eval_mulTerm (c : α) (m : Mono) (p : Poly α) :
    eval h x (Poly.mulTerm C c m p) = h.f c * Mono.eval x m 0 * eval h x p := by
  induction p with
  | nil => simp [Poly.mulTerm]
  | cons t p ih =>
    simp only [Poly.mulTerm, List.map_cons, eval_cons, h.map_mul, Mono.eval_mul] at ih ⊢
    rw [ih]
    ring

theorem eval_mul (p q : Poly α) : eval h x (Poly.mul C p q) = eval h x p * eval h x q := by
  induction p with
  | nil => simp [Poly.mul]
  | cons t p ih =>
    simp only [Poly.mul, List.flatMap_cons, eval_append, eval_cons] at ih ⊢
    rw [ih, eval_mulTerm]
    ring

theorem eval_sum (ps : List (Poly α)) : eval h x (Poly.sum ps) = (ps.map (eval h x)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [Poly.sum, List.flatten_cons, eval_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem eval_combineAux : ∀ (p : Poly α) (cur : α × Mono) (acc : Poly α),
    eval h x (Poly.combineAux C p cur acc) = eval h x p + (h.f cur.1 * Mono.eval x cur.2 0) + eval h x acc
  | [], cur, acc => by simp [Poly.combineAux]
  | t :: rest, cur, acc => by
    simp only [Poly.combineAux]
    split
    · rename_i heq
      have heq' : t.2 = cur.2 := by simpa using heq
      rw [eval_combineAux rest _ acc]
      simp only [eval_cons, h.map_add, heq']
      ring
    · rw [eval_combineAux rest t (cur :: acc)]
      simp only [eval_cons]
      ring

theorem eval_combine (p : Poly α) : eval h x (Poly.combine C p) = eval h x p := by
  cases p with
  | nil => rfl
  | cons t rest =>
    simp only [Poly.combine, eval_combineAux, eval_cons, eval_nil]
    ring

theorem eval_filter_nonzero (p : Poly α) :
    eval h x (p.filter fun t => !C.isZero t.1) = eval h x p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [List.filter_cons]
    split
    · simp only [eval_cons, ih]
    · rename_i hz
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hz
      simp only [eval_cons, ih, h.map_isZero _ (by simpa using hz), zero_mul, zero_add]

theorem eval_perm {p q : Poly α} (hpq : p.Perm q) : eval h x p = eval h x q := by
  unfold eval
  exact (hpq.map _).sum_eq

theorem eval_trimAll (p : Poly α) :
    eval h x (p.map fun t => (t.1, Mono.trim t.2)) = eval h x p := by
  induction p with
  | nil => rfl
  | cons t p ih => simp only [List.map_cons, eval_cons, ih, Mono.eval_trim]

theorem eval_normalize (p : Poly α) : eval h x (Poly.normalize C p) = eval h x p := by
  unfold Poly.normalize
  rw [eval_filter_nonzero, eval_combine, eval_perm h x (List.mergeSort_perm _ _), eval_trimAll]

/-- **The zero test is sound.** -/
theorem isZero_sound {p : Poly α} (hp : Poly.isZero C p = true) : eval h x p = 0 := by
  rw [← eval_normalize h x p]
  unfold Poly.isZero at hp
  rw [List.isEmpty_iff.mp hp]
  rfl

/-- **The identity test is sound.** -/
theorem eqv_sound {p q : Poly α} (hpq : Poly.eqv C p q = true) : eval h x p = eval h x q := by
  have := isZero_sound h x hpq
  rw [eval_sub] at this
  exact sub_eq_zero.mp this

theorem eval_pow (p : Poly α) : ∀ n, eval h x (Poly.pow C p n) = eval h x p ^ n
  | 0 => by simp [Poly.pow, eval_const, h.map_one]
  | n + 1 => by rw [Poly.pow, eval_normalize, eval_mul, eval_pow p n, pow_succ]

theorem eval_substMono (σ : ℕ → Poly α) :
    ∀ (m : Mono) (i : ℕ), eval h x (Poly.substMono C σ m i) = Mono.eval (fun j => eval h x (σ j)) m i
  | [], i => by simp [Poly.substMono, eval_const, h.map_one, Mono.eval]
  | e :: m, i => by
    rw [Poly.substMono, eval_normalize, eval_mul, eval_pow, eval_substMono σ m (i + 1)]
    rfl

/-- **Substitution**: evaluating `subst σ p` at `x` is evaluating `p` at the values of the `σ j`. -/
theorem eval_subst (σ : ℕ → Poly α) (p : Poly α) :
    eval h x (Poly.subst C σ p) = eval h (fun j => eval h x (σ j)) p := by
  rw [Poly.subst, eval_normalize]
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [List.flatMap_cons, eval_append, ih, eval_mul, eval_const, eval_substMono, eval_cons]

end Poly

/-! ## Coefficient maps -/

/-- `ℤ` into any commutative ring. -/
def intHom (R : Type*) [CommRing R] : intC.Hom R where
  f := fun a => (a : R)
  map_zero := by simp [intC]
  map_one := by simp [intC]
  map_add := by intro a b; simp [intC]
  map_mul := by intro a b; simp [intC]
  map_neg := by intro a; simp [intC]
  map_isZero := by intro a ha; simp [intC] at ha; simp [ha]

/-- `ℚ` into any field of characteristic zero. -/
def ratHom (K : Type*) [Field K] [CharZero K] : ratC.Hom K where
  f := fun a => (a : K)
  map_zero := by simp [ratC]
  map_one := by simp [ratC]
  map_add := by intro a b; simp [ratC]
  map_mul := by intro a b; simp [ratC]
  map_neg := by intro a; simp [ratC]
  map_isZero := by intro a ha; simp [ratC] at ha; simp [ha]

/-- `ℤ/p` (natural numbers modulo `p`) into `ZMod p`, for `p > 0`. -/
def modHom (p : ℕ) [NeZero p] : (modC p).Hom (ZMod p) where
  f := fun a => (a : ZMod p)
  map_zero := by simp [modC]
  map_one := by simp [modC]
  map_add := by intro a b; simp [modC, ZMod.natCast_mod]
  map_mul := by intro a b; simp [modC, ZMod.natCast_mod]
  map_neg := by
    intro a
    simp only [modC, ZMod.natCast_mod]
    have hle : a % p ≤ p := (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))).le
    rw [Nat.cast_sub hle, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
  map_isZero := by
    intro a ha
    simp only [modC, beq_iff_eq] at ha
    rw [← ZMod.natCast_mod, ha, Nat.cast_zero]

/-- `ℤ[j]` into a commutative ring with an element `ω`, `ω² + ω + 1 = 0`. -/
def zjHom (R : Type*) [CommRing R] (ω : R) (hω : ω ^ 2 + ω + 1 = 0) : zjC.Hom R where
  f := fun x => (x.1 : R) + (x.2 : R) * ω
  map_zero := by simp [zjC]
  map_one := by simp [zjC]
  map_add := by intro a b; simp [zjC]; ring
  map_mul := by
    intro a b
    simp only [zjC, Int.cast_sub, Int.cast_mul, Int.cast_add]
    linear_combination (-(a.2 : R) * (b.2 : R)) * hω
  map_neg := by intro a; simp [zjC]; ring
  map_isZero := by
    intro a ha
    simp only [zjC, Bool.and_eq_true, beq_iff_eq] at ha
    simp [ha.1, ha.2]

end Lean6.Special
