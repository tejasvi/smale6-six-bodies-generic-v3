import L6KSpec.TropMem
import L6SoundKSpec.TropNorm
import Mathlib.Data.List.GetD

/-!
# Lemma 6.19(a)(i): the systems with `normalizeK` have the values of lean6_special's, and `checkMemK` is sound

`eval_substK`, `eval_powK`: as `Poly.eval_subst`, `Poly.eval_pow`. The systems of `L6KSpec.TropMem` have, at every
point of every commutative ring, the values of those of `Lean6.Special.Comp.D88.Trop.Sys` (`eval_n4FK`, `eval_n4σK`,
`eval_n4relK`, and the same for `KC`). `mem_soundK` is lean6_special's `mem_sound` for `checkMemK`.
-/

namespace L6KSpec.Trop

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.D88.Trop

section Gen

variable {α : Type} {C : Coeff α} {R : Type*} [CommRing R] (h : C.Hom R) (x : ℕ → R)

theorem eval_powK (p : Poly α) : ∀ n, Poly.eval h x (powK C p n) = Poly.eval h x p ^ n
  | 0 => by simp [powK, Poly.eval_const, h.map_one]
  | n + 1 => by rw [powK, eval_normalizeK, Poly.eval_mul, eval_powK p n, pow_succ]

theorem eval_substMonoK (σ : ℕ → Poly α) :
    ∀ (m : Mono) (i : ℕ), Poly.eval h x (substMonoK C σ m i) = Mono.eval (fun j => Poly.eval h x (σ j)) m i
  | [], i => by simp [substMonoK, Poly.eval_const, h.map_one, Mono.eval]
  | e :: m, i => by
    rw [substMonoK, eval_normalizeK, Poly.eval_mul, eval_powK, eval_substMonoK σ m (i + 1)]
    rfl

/-- **Substitution**, as `Poly.eval_subst`. -/
theorem eval_substK (σ : ℕ → Poly α) (p : Poly α) :
    Poly.eval h x (substK C σ p) = Poly.eval h (fun j => Poly.eval h x (σ j)) p := by
  rw [substK, eval_normalizeK]
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [List.flatMap_cons, Poly.eval_append, ih, Poly.eval_mul, Poly.eval_const, eval_substMonoK, Poly.eval_cons]

end Gen

section Sys

variable {R : Type*} [CommRing R] (x : ℕ → R)

theorem eval_eqnK {B B' : Bodies} (hp : B'.p0 = B.p0) (hm : B'.mu0 = B.mu0) {Z Z' : ℕ → Poly ℤ}
    (hZ : ∀ k, Poly.eval (intHom R) x (Z' k) = Poly.eval (intHom R) x (Z k)) (k : ℕ) :
    Poly.eval (intHom R) x (eqnK B' Z' k) = Poly.eval (intHom R) x (B.eqn Z k) := by
  simp only [eqnK, Bodies.eqn, psK, ps, pmK, pm, psumK, psum, eval_normalizeK, Poly.eval_normalize, Poly.eval_sub,
    Poly.eval_mul, Poly.eval_sum, List.map_map, Function.comp_def, eval_powK, Poly.eval_pow, Bodies.mu, Bodies.P, hp,
    hm, hZ]

theorem eval_DK {B B' : Bodies} (hp : B'.p0 = B.p0)
    (hX : ∀ k, Poly.eval (intHom R) x (B'.X k) = Poly.eval (intHom R) x (B.X k))
    (hY : ∀ k, Poly.eval (intHom R) x (B'.Y k) = Poly.eval (intHom R) x (B.Y k)) (k l : ℕ) :
    Poly.eval (intHom R) x (DK B' k l) = Poly.eval (intHom R) x (B.D k l) := by
  simp only [DK, Bodies.D, psK, ps, pmK, pm, eval_normalizeK, Poly.eval_normalize, Poly.eval_sub, Poly.eval_mul,
    eval_powK, Poly.eval_pow, Bodies.P, hp, hX, hY]

/-! ## N4 -/

theorem eval_n4X : ∀ k, Poly.eval (intHom R) x (n4BodiesK.X k) = Poly.eval (intHom R) x (n4Bodies.X k)
  | 0 | 1 | 2 | 3 | _ + 4 => by
    simp only [n4BodiesK, n4Bodies, paK, pa, pmK, pm, psumK, psum, eval_normalizeK, Poly.eval_normalize,
      Poly.eval_add, Poly.eval_mul, Poly.eval_sum, List.map_cons, List.map_nil]

theorem eval_n4Y : ∀ k, Poly.eval (intHom R) x (n4BodiesK.Y k) = Poly.eval (intHom R) x (n4Bodies.Y k)
  | 0 | 1 | 2 | 3 | _ + 4 => by
    simp only [n4BodiesK, n4Bodies, pmK, pm, psumK, psum, eval_normalizeK, Poly.eval_normalize, Poly.eval_mul,
      Poly.eval_sum, List.map_cons, List.map_nil]

theorem eval_n4FK : n4FK.map (Poly.eval (intHom R) x) = n4F.map (Poly.eval (intHom R) x) := by
  have hX := eval_eqnK x (B := n4Bodies) (B' := n4BodiesK) rfl rfl (eval_n4X x)
  have hY := eval_eqnK x (B := n4Bodies) (B' := n4BodiesK) rfl rfl (eval_n4Y x)
  have hD := eval_DK x (B := n4Bodies) (B' := n4BodiesK) rfl (eval_n4X x) (eval_n4Y x)
  simp only [n4FK, n4F, Bodies.Xeq, Bodies.Yeq, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    hX, hY, hD]

theorem eval_n4σK : ∀ j, Poly.eval (intHom R) x (n4σK j) = Poly.eval (intHom R) x (n4σ j)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | _ + 11 => by
    simp only [n4σK, n4σ, psK, ps, eval_normalizeK, Poly.eval_normalize, Poly.eval_sub, eval_n4X, eval_n4Y]

theorem eval_n4relK : Poly.eval (intHom R) x n4relK = Poly.eval (intHom R) x n4rel := by
  simp only [n4relK, n4rel, psK, ps, pmK, pm, eval_normalizeK, Poly.eval_normalize, Poly.eval_sub, Poly.eval_mul]

/-! ## KC -/

theorem eval_kcX : ∀ k, Poly.eval (intHom R) x (kcBodiesK.X k) = Poly.eval (intHom R) x (kcBodies.X k)
  | 0 | 1 | 2 | 3 | _ + 4 => rfl

theorem eval_kcY : ∀ k, Poly.eval (intHom R) x (kcBodiesK.Y k) = Poly.eval (intHom R) x (kcBodies.Y k)
  | 0 | 1 | 2 | 3 | _ + 4 => rfl

theorem eval_kcFK : kcFK.map (Poly.eval (intHom R) x) = kcF.map (Poly.eval (intHom R) x) := by
  have hX := eval_eqnK x (B := kcBodies) (B' := kcBodiesK) rfl rfl (eval_kcX x)
  have hY := eval_eqnK x (B := kcBodies) (B' := kcBodiesK) rfl rfl (eval_kcY x)
  have hD := eval_DK x (B := kcBodies) (B' := kcBodiesK) rfl (eval_kcX x) (eval_kcY x)
  simp only [kcFK, kcF, Bodies.Xeq, Bodies.Yeq, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    hX, hY, hD]

theorem eval_kcσK : ∀ j, Poly.eval (intHom R) x (kcσK j) = Poly.eval (intHom R) x (kcσ j)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | _ + 11 => by
    simp only [kcσK, kcσ, psK, ps, eval_normalizeK, Poly.eval_normalize, Poly.eval_sub, eval_kcX, eval_kcY]

theorem eval_kcrelK : Poly.eval (intHom R) x kcrelK = Poly.eval (intHom R) x kcrel := by
  simp only [kcrelK, kcrel, psK, ps, pmK, pm, eval_normalizeK, Poly.eval_normalize, Poly.eval_sub, Poly.eval_mul]

end Sys

/-! ## The membership check -/

/-- **`mem_sound` for `checkMemK`.** -/
theorem mem_soundK {σ : ℕ → Poly ℤ} {F : List (Poly ℤ)} {rel : Poly ℤ} {G : List GPoly}
    {cofs : List (List (Poly ℤ))} {c0s : List (Poly ℤ)} (h : checkMemK σ F rel G cofs c0s = true) {i : ℕ}
    (hi : i < G.length) {R : Type*} [CommRing R] (x : ℕ → R) (hrel : Poly.eval (intHom R) x rel = 0) :
    Poly.eval (intHom R) (fun j => Poly.eval (intHom R) x (σ j)) (flat G[i]) =
      (((cofs.getD i []).zip F).map fun cf => Poly.eval (intHom R) x cf.1 * Poly.eval (intHom R) x cf.2).sum := by
  simp only [checkMemK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hl1, hl2⟩, -⟩, hall⟩ := h
  have hz : i < (G.zip (cofs.zip c0s)).length := by simp [hi, ← hl1, ← hl2]
  have hm := hall _ (List.getElem_mem hz)
  simp only [List.getElem_zip] at hm
  have h0 := isZeroK_sound (intHom R) x hm
  rw [Poly.eval_sub, eval_substK, Poly.eval_add, Poly.eval_sum, Poly.eval_mul, hrel, mul_zero, add_zero,
    sub_eq_zero] at h0
  rw [h0, List.map_map]
  have hc : cofs.getD i [] = cofs[i]'(by omega) := List.getD_eq_getElem _ _ _
  rw [hc]
  congr 1
  refine List.map_congr_left fun cf _ => ?_
  simp [Poly.eval_mul]

/-- Replacing the second factors by lists with the same values. -/
theorem zip_map_eq {α β γ : Type*} [Mul γ] (f : α → γ) (g : β → γ) :
    ∀ (C : List α) (A B : List β), A.map g = B.map g →
      (C.zip A).map (fun cf => f cf.1 * g cf.2) = (C.zip B).map (fun cf => f cf.1 * g cf.2)
  | [], _, _, _ => rfl
  | _ :: _, [], [], _ => rfl
  | _ :: _, [], _ :: _, h => absurd h (by simp)
  | _ :: _, _ :: _, [], h => absurd h (by simp)
  | c :: C, a :: A, b :: B, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.map_cons, h.1, zip_map_eq f g C A B h.2]

end L6KSpec.Trop
