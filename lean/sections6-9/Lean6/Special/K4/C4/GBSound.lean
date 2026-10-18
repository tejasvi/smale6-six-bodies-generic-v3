import Lean6.Special.Comp.K4.C4.GB
import Lean6.Special.Poly.Sem
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

/-!
# Soundness of the Buchberger engine

Fix a point `x` of a commutative ring `R` at which every input polynomial vanishes. Every operation of the engine
that produces a polynomial (`axpy`, `mulT`, `monic`, `spoly`, `reduceAux`) maps polynomials vanishing at `x` to
polynomials vanishing at `x` (`eval_axpyAux`, `eval_mulT`, `eval_reduceAux`), so every element of the basis vanishes
at `x` (`inv_run`). If the engine reports a constant `a` with `a ≢ 0 (mod p)`, then `a = 0` in `R`, which is
impossible in a nontrivial `ZMod p`-algebra for a prime `p` (`unitTest_sound`).
-/

namespace Lean6.Special.K4.C4

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.GB

/-- Compose a coefficient map with a ring homomorphism. -/
def homComp {α : Type} {C : Coeff α} {R S : Type*} [CommRing R] [CommRing S] (h : C.Hom R) (φ : R →+* S) :
    C.Hom S where
  f a := φ (h.f a)
  map_zero := by simp [h.map_zero]
  map_one := by simp [h.map_one]
  map_add a b := by simp [h.map_add]
  map_mul a b := by simp [h.map_mul]
  map_neg a := by simp [h.map_neg]
  map_isZero a ha := by simp [h.map_isZero a ha]

/-- The coefficient map `ℕ → ZMod p → R` of a `ZMod p`-algebra. -/
def algH (p : ℕ) [NeZero p] (R : Type*) [CommRing R] [Algebra (ZMod p) R] : (modC p).Hom R :=
  homComp (modHom p) (algebraMap (ZMod p) R)

theorem algH_f (p : ℕ) [NeZero p] (R : Type*) [CommRing R] [Algebra (ZMod p) R] (a : ℕ) :
    (algH p R).f a = algebraMap (ZMod p) R (a : ZMod p) := rfl

section Mono

variable {R : Type*} [CommRing R] (x : ℕ → R)

theorem mono_eval_append_zeros : ∀ (m : Mono) (k i : ℕ),
    Mono.eval x (m ++ List.replicate k 0) i = Mono.eval x m i
  | [], k, i => by
    induction k generalizing i with
    | zero => rfl
    | succ k ih =>
      simp only [List.nil_append, List.replicate_succ, Mono.eval, pow_zero, one_mul] at ih ⊢
      exact ih _
  | e :: m, k, i => by
    simp only [List.cons_append, Mono.eval, mono_eval_append_zeros m k (i + 1)]

theorem mono_eval_pad (n : ℕ) (m : Mono) (i : ℕ) : Mono.eval x (pad n m) i = Mono.eval x m i :=
  mono_eval_append_zeros x m _ i

theorem mono_eval_zeros : ∀ (m : Mono) (i : ℕ), m.all (· == 0) = true → Mono.eval x m i = 1
  | [], _, _ => rfl
  | e :: m, i, hm => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hm
    simp only [Mono.eval, hm.1, pow_zero, one_mul]
    exact mono_eval_zeros m (i + 1) hm.2

theorem mono_eval_replicate_zero (k i : ℕ) : Mono.eval x (List.replicate k 0) i = 1 :=
  mono_eval_zeros x _ i (by simp [List.all_eq_true])

end Mono

section Engine

variable {p : ℕ} {R : Type*} [CommRing R] (h : (modC p).Hom R) (x : ℕ → R)

theorem eval_reverseAux (l r : Poly ℕ) : Poly.eval h x (l.reverseAux r) = Poly.eval h x l + Poly.eval h x r := by
  rw [List.reverseAux_eq, Poly.eval_append, Poly.eval_perm h x (List.reverse_perm l)]

theorem eval_reverse (l : Poly ℕ) : Poly.eval h x l.reverse = Poly.eval h x l :=
  Poly.eval_perm h x (List.reverse_perm l)

theorem hneg (c b : ℕ) : h.f ((modC p).neg ((modC p).mul c b)) = -(h.f c * h.f b) := by
  rw [h.map_neg, h.map_mul]

theorem eval_axpyAux (c : ℕ) (m : Mono) (f g acc : Poly ℕ) :
    Poly.eval h x (axpyAux p c m f g acc) =
      Poly.eval h x acc + Poly.eval h x f - h.f c * Mono.eval x m 0 * Poly.eval h x g := by
  induction f, g, acc using axpyAux.induct p c m with
  | case1 f acc =>
    rw [axpyAux.eq_1, eval_reverseAux]
    simp
  | case2 b k g acc ih =>
    rw [axpyAux.eq_2, ih]
    simp only [Poly.eval_cons, Poly.eval_nil, hneg, Mono.eval_mul]
    ring
  | case3 a mf f b k g acc mk hmk d hd ih =>
    have hmk2 : (mf == Mono.mul m k) = true := hmk
    have hd2 : ((modC p).add a ((modC p).neg ((modC p).mul c b)) == 0) = true := hd
    have hmk' : mf = Mono.mul m k := by simpa using hmk2
    have hd' : h.f a - h.f c * h.f b = 0 := by
      have h0 : (modC p).add a ((modC p).neg ((modC p).mul c b)) = 0 := by simpa using hd2
      have := congrArg h.f h0
      simp only [h.map_add, hneg] at this
      rw [show (0 : ℕ) = (modC p).zero from rfl, h.map_zero] at this
      linear_combination this
    rw [axpyAux.eq_3]
    simp only [hmk2, hd2, ↓reduceIte]
    rw [ih]
    simp only [Poly.eval_cons, hmk', Mono.eval_mul]
    linear_combination (-(Mono.eval x m 0 * Mono.eval x k 0)) * hd'
  | case4 a mf f b k g acc mk hmk d hd ih =>
    have hmk2 : (mf == Mono.mul m k) = true := hmk
    have hd2 : ¬((modC p).add a ((modC p).neg ((modC p).mul c b)) == 0) = true := hd
    have hmk' : mf = Mono.mul m k := by simpa using hmk2
    simp only [d] at ih
    rw [axpyAux.eq_3]
    simp only [hmk2, hd2, ↓reduceIte, Bool.false_eq_true]
    rw [ih]
    simp only [Poly.eval_cons, hmk', Mono.eval_mul, h.map_add, hneg]
    ring
  | case5 a mf f b k g acc mk hmk hgt ih =>
    have hmk2 : ¬(mf == Mono.mul m k) = true := hmk
    have hgt2 : grevGt mf (Mono.mul m k) = true := hgt
    rw [axpyAux.eq_3]
    simp only [hmk2, hgt2, ↓reduceIte, Bool.false_eq_true]
    rw [ih]
    simp only [Poly.eval_cons]
    ring
  | case6 a mf f b k g acc mk hmk hgt ih =>
    have hmk2 : ¬(mf == Mono.mul m k) = true := hmk
    have hgt2 : ¬grevGt mf (Mono.mul m k) = true := hgt
    simp only [mk] at ih
    rw [axpyAux.eq_3]
    simp only [hmk2, hgt2, ↓reduceIte, Bool.false_eq_true]
    rw [ih]
    simp only [Poly.eval_cons, hneg, Mono.eval_mul]
    ring

theorem eval_axpy (c : ℕ) (m : Mono) (f g : Poly ℕ) :
    Poly.eval h x (axpy p c m f g) = Poly.eval h x f - h.f c * Mono.eval x m 0 * Poly.eval h x g := by
  rw [axpy, eval_axpyAux]
  simp

theorem eval_mulT (c : ℕ) (m : Mono) (g : Poly ℕ) :
    Poly.eval h x (mulT p c m g) = h.f c * Mono.eval x m 0 * Poly.eval h x g := by
  induction g with
  | nil => simp [mulT]
  | cons t g ih =>
    simp only [mulT, List.map_cons, Poly.eval_cons] at ih ⊢
    rw [ih, h.map_mul, Mono.eval_mul]
    ring

theorem eval_monic_eq_zero {g : Poly ℕ} (hg : Poly.eval h x g = 0) : Poly.eval h x (monic p g) = 0 := by
  cases g with
  | nil => rfl
  | cons t g =>
    obtain ⟨a, m⟩ := t
    simp only [monic, eval_mulT, hg, mul_zero]

theorem eval_spoly_eq_zero {f g : Poly ℕ} (hf : Poly.eval h x f = 0) (hg : Poly.eval h x g = 0) :
    Poly.eval h x (spoly p f g) = 0 := by
  unfold spoly
  split
  · simp only [eval_axpy, eval_mulT, hf, hg, mul_zero, sub_zero]
  · rfl

theorem eval_reduceAux (basis : Array (Poly ℕ)) (lead : Array Mono) (idx : List ℕ)
    (hB : ∀ i, Poly.eval h x (basis.getD i []) = 0) (fuel : ℕ) (hh out : Poly ℕ) :
    Poly.eval h x (reduceAux p basis lead idx fuel hh out) = Poly.eval h x out + Poly.eval h x hh := by
  induction fuel, hh, out using reduceAux.induct p basis lead idx with
  | case1 hh out => rw [reduceAux, eval_reverseAux]
  | case2 n out => rw [reduceAux, eval_reverse]; simp
  | case3 fuel a m hh out hf ih =>
    rw [reduceAux, hf]
    simp only [ih, Poly.eval_cons]
    ring
  | case4 fuel a m hh out i hf g hg ih =>
    have hg2 : basis.getD i [] = [] := hg
    rw [reduceAux, hf]
    simp only [hg2]
    rw [ih]
    simp only [Poly.eval_cons]
    ring
  | case5 fuel a m hh out i hf g b k tail hg ih =>
    have hg2 : basis.getD i [] = (b, k) :: tail := hg
    have ih2 := ih
    simp only [g, hg2] at ih2
    rw [reduceAux, hf]
    simp only [hg2]
    rw [ih2, eval_axpy, ← hg2, hB i]
    ring

end Engine

section Run

variable {p : ℕ} {R : Type*} [CommRing R] (h : (modC p).Hom R) (x : ℕ → R)

theorem getD_push {α : Type*} (a : Array α) (v d : α) (i : ℕ) :
    (a.push v).getD i d = if i < a.size then a.getD i d else if i = a.size then v else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h1 : i < a.size
  · have h2 : i ≠ a.size := by omega
    simp [h1, h2]
  · by_cases h3 : i = a.size
    · simp [h3]
    · have h4 : a[i]? = none := Array.getElem?_eq_none (by omega)
      simp [h1, h3, h4]

theorem isUnitPoly_nil : isUnitPoly p [] = false := rfl

/-- The invariant: every basis element vanishes at `x`, and `found` has a witness. -/
def Good (s : St) : Prop :=
  (∀ i, Poly.eval h x (s.basis.getD i []) = 0) ∧ (s.found = true → ∃ i, isUnitPoly p (s.basis.getD i []) = true)

theorem good_addPoly {s : St} (hs : Good h x s) {hh : Poly ℕ} (hz : Poly.eval h x hh = 0) (sg : ℕ) :
    Good h x (addPoly p s hh sg) := by
  have hm := eval_monic_eq_zero h x hz
  unfold addPoly
  generalize monic p hh = g at hm
  cases g with
  | nil => exact hs
  | cons t tl =>
    obtain ⟨a, m⟩ := t
    dsimp only
    refine ⟨fun i => ?_, fun hf => ?_⟩
    · show Poly.eval h x ((s.basis.push _).getD i []) = 0
      rw [getD_push]
      by_cases h1 : i < s.basis.size
      · rw [if_pos h1]; exact hs.1 i
      · rw [if_neg h1]
        by_cases h2 : i = s.basis.size
        · rw [if_pos h2]; exact hm
        · rw [if_neg h2]; rfl
    · show ∃ i, isUnitPoly p ((s.basis.push _).getD i []) = true
      simp only [update, Bool.or_eq_true] at hf
      rcases hf with hf | hf
      · obtain ⟨i, hi⟩ := hs.2 hf
        refine ⟨i, ?_⟩
        rw [getD_push]
        have : i < s.basis.size := by
          by_contra hc
          have h0 : s.basis.getD i [] = [] := by
            simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hc), Option.getD_none]
          rw [h0] at hi
          exact absurd hi (by simp [isUnitPoly_nil])
        rw [if_pos this]
        exact hi
      · refine ⟨s.basis.size, ?_⟩
        rw [getD_push, if_neg (lt_irrefl _), if_pos rfl]
        exact hf

theorem good_step (rfuel : ℕ) {s : St} (hs : Good h x s) : Good h x (step p rfuel s) := by
  unfold step
  split
  · exact hs
  · rename_i q qs _
    have hs' : Good h x ⟨s.basis, s.lead, s.sugar, s.act, qs, s.found⟩ := hs
    have hr : Poly.eval h x
        (reduceAux p s.basis s.lead s.act rfuel (spoly p (s.basis.getD q.i []) (s.basis.getD q.j [])) []) = 0 := by
      rw [eval_reduceAux h x _ _ _ hs.1]
      simp only [Poly.eval_nil, zero_add]
      exact eval_spoly_eq_zero h x (hs.1 _) (hs.1 _)
    dsimp only
    generalize reduceAux p s.basis s.lead s.act rfuel (spoly p (s.basis.getD q.i []) (s.basis.getD q.j [])) [] = r
      at hr
    cases r with
    | nil => exact hs'
    | cons t tl => exact good_addPoly h x hs' hr _

theorem good_loop (rfuel : ℕ) : ∀ (fuel : ℕ) {s : St}, Good h x s → Good h x (loop p rfuel fuel s)
  | 0, s, hs => hs
  | fuel + 1, s, hs => by
    unfold loop
    split
    · exact hs
    · exact good_loop rfuel fuel (good_step h x rfuel hs)

theorem good_init_step (n rfuel : ℕ) {s : St} (hs : Good h x s) {f : Poly ℕ}
    (hf : Poly.eval h x (prep p n f) = 0) :
    Good h x (let f := prep p n f
      let hh := reduceAux p s.basis s.lead s.act rfuel f []
      match hh with
      | [] => s
      | (_, m) :: _ => addPoly p s hh (mdeg m)) := by
  have hr : Poly.eval h x (reduceAux p s.basis s.lead s.act rfuel (prep p n f) []) = 0 := by
    rw [eval_reduceAux h x _ _ _ hs.1, hf]
    simp
  dsimp only
  generalize reduceAux p s.basis s.lead s.act rfuel (prep p n f) [] = r at hr
  cases r with
  | nil => exact hs
  | cons t tl =>
    obtain ⟨a, m⟩ := t
    exact good_addPoly h x hs hr _

theorem good_init (n rfuel : ℕ) (F : List (Poly ℕ)) (hF : ∀ f ∈ F, Poly.eval h x (prep p n f) = 0) :
    Good h x (init p n rfuel F) := by
  unfold init
  suffices ∀ (G : List (Poly ℕ)) (s : St), Good h x s → (∀ f ∈ G, Poly.eval h x (prep p n f) = 0) →
      Good h x (G.foldl (fun s f =>
        let f := prep p n f
        let hh := reduceAux p s.basis s.lead s.act rfuel f []
        match hh with
        | [] => s
        | (_, m) :: _ => addPoly p s hh (mdeg m)) s) from
    this F _ ⟨fun i => by simp [Array.getD], fun hf => absurd hf (by decide)⟩ hF
  intro G
  induction G with
  | nil => intro s hs _; exact hs
  | cons f G ih =>
    intro s hs hG
    simp only [List.foldl_cons]
    exact ih _ (good_init_step h x n rfuel hs (hG f List.mem_cons_self)) (fun g hg => hG g (List.mem_cons_of_mem _ hg))

end Run

section Final

/-- `prep` does not change the value for the coefficient map of a `ZMod p`-algebra. -/
theorem eval_prep (p : ℕ) [NeZero p] (R : Type*) [CommRing R] [Algebra (ZMod p) R] (x : ℕ → R) (n : ℕ)
    (f : Poly ℕ) : Poly.eval (algH p R) x (prep p n f) = Poly.eval (algH p R) x f := by
  unfold prep
  rw [Poly.eval_perm _ x (List.mergeSort_perm _ _)]
  induction f with
  | nil => rfl
  | cons t f ih =>
    simp only [List.map_cons, List.filter_cons]
    split
    · simp only [Poly.eval_cons, ih, algH_f, ZMod.natCast_mod, mono_eval_pad]
    · rename_i hz
      simp only [bne_iff_ne, ne_eq, not_not] at hz
      have h0 : algebraMap (ZMod p) R ((t.1 : ℕ) : ZMod p) = 0 := by
        rw [← ZMod.natCast_mod, hz, Nat.cast_zero, map_zero]
      simp only [Poly.eval_cons, ih, algH_f, h0, zero_mul, zero_add]

/-- **Soundness of the engine.** If `unitTest p n fuel rfuel F = true` for a prime `p`, the polynomials `F` have no
common zero in any nontrivial commutative `ZMod p`-algebra. -/
theorem unitTest_sound (p : ℕ) [Fact p.Prime] {n fuel rfuel : ℕ} {F : List (Poly ℕ)}
    (hT : unitTest p n fuel rfuel F = true) (R : Type*) [CommRing R] [Nontrivial R] [Algebra (ZMod p) R]
    (x : ℕ → R) : ¬ ∀ f ∈ F, Poly.eval (algH p R) x f = 0 := by
  intro hF
  have hG := good_loop (algH p R) x rfuel fuel
    (good_init (algH p R) x n rfuel F (fun f hf => by rw [eval_prep]; exact hF f hf))
  obtain ⟨i, hi⟩ := hG.2 hT
  have hz := hG.1 i
  generalize (loop p rfuel fuel (init p n rfuel F)).basis.getD i [] = g at hi hz
  unfold isUnitPoly at hi
  split at hi
  · rename_i a m
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [Poly.eval_cons, Poly.eval_nil, add_zero, algH_f, mono_eval_zeros x m 0 hi.2, mul_one] at hz
    have h1 : ((a : ℕ) : ZMod p) = 0 := (algebraMap (ZMod p) R).injective (by rw [hz, map_zero])
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hi.1 (Nat.mod_eq_zero_of_dvd h1)
  · exact absurd hi (by simp)

end Final

end Lean6.Special.K4.C4
