import L6KSpec.C4Check
import Mathlib

/-!
# Soundness of the kernel check of a cofactor certificate modulo a prime

`cofmod_sound`: if every bucket passes `bucketOKp p`, every product occurs exactly once (`coverOK`) and the parts of
`h` make up `h` (`hOK`), then in every commutative ring in which `p = 0`, at every assignment at which all generators
vanish, `h` vanishes. The cofactors are the sums of their pieces; they are never formed. The keys and the values of
packed polynomials are those of lean6 (`L6.Poly`); the lemmas on term lists those of the F4 kernel modules of
`lean6` (`L6SoundK.F4`), with the comparison of a bucket modulo `p` (`bucket_soundp`).
-/

namespace L6KSpec.C4

open Finset

/-! ## Keys: no carry between bytes -/

/-- The exponent of variable `i` in a key. -/
def keyExp (key i : Nat) : Nat := (key >>> (8 * i)) % 256

theorem keyExp_eq_div (k i : ℕ) : keyExp k i = k / 256 ^ i % 256 := by
  unfold keyExp
  rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ (8 * i) = 256 ^ i by rw [pow_mul]; norm_num]

theorem two_mul_mod_lt (a : ℕ) : ∀ i : ℕ, (∀ j < i, keyExp a j < 128) → 2 * (a % 256 ^ i) < 256 ^ i
  | 0, _ => by simp [Nat.mod_one]
  | i + 1, h => by
    have ih := two_mul_mod_lt a i (fun j hj => h j (by omega))
    have hb := h i (by omega)
    rw [keyExp_eq_div] at hb
    rw [Nat.mod_pow_succ, pow_succ]
    have hP : 0 < 256 ^ i := by positivity
    nlinarith

theorem keyExp_add (a b i : ℕ) (ha : ∀ j ≤ i, keyExp a j < 128) (hb : ∀ j ≤ i, keyExp b j < 128) :
    keyExp (a + b) i = keyExp a i + keyExp b i := by
  have la := two_mul_mod_lt a i (fun j hj => ha j hj.le)
  have lb := two_mul_mod_lt b i (fun j hj => hb j hj.le)
  have ha' := ha i le_rfl
  have hb' := hb i le_rfl
  simp only [keyExp_eq_div] at ha' hb' ⊢
  set P := 256 ^ i with hPdef
  have hP : 0 < P := by positivity
  have e : a + b = (a % P + b % P) + P * (a / P + b / P) := by
    have := Nat.div_add_mod a P; have := Nat.div_add_mod b P; ring_nf; omega
  have hlt : a % P + b % P < P := by omega
  rw [e, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hlt, zero_add, Nat.add_mod]
  rw [Nat.mod_eq_of_lt (by omega : a / P % 256 + b / P % 256 < 256)]

/-- Keys whose first `nv` exponents are all `< 128`. -/
def SmallKey (nv k : ℕ) : Prop := ∀ i < nv, keyExp k i < 128

/-! ## Values -/

section Eval

variable {R : Type*} [CommRing R]

/-- The monomial of a key at an assignment. -/
def monoEval (nv : ℕ) (φ : ℕ → R) (k : ℕ) : R := ∏ i ∈ range nv, φ i ^ keyExp k i

/-- The value of a packed polynomial at an assignment. -/
def eval (nv : ℕ) (φ : ℕ → R) (p : KPoly) : R := (p.map fun t => (t.2 : R) * monoEval nv φ t.1).sum

@[simp] theorem eval_nil (nv : ℕ) (φ : ℕ → R) : eval nv φ [] = 0 := rfl

theorem eval_cons (nv : ℕ) (φ : ℕ → R) (t : ℕ × ℤ) (p : KPoly) :
    eval nv φ (t :: p) = (t.2 : R) * monoEval nv φ t.1 + eval nv φ p := by
  simp [eval]

theorem eval_append (nv : ℕ) (φ : ℕ → R) (p q : KPoly) : eval nv φ (p ++ q) = eval nv φ p + eval nv φ q := by
  simp [eval, List.sum_append]

theorem eval_perm (nv : ℕ) (φ : ℕ → R) {p q : KPoly} (h : p.Perm q) : eval nv φ p = eval nv φ q :=
  (h.map _).sum_eq

theorem monoEval_add (nv : ℕ) (φ : ℕ → R) {a b : ℕ} (ha : SmallKey nv a) (hb : SmallKey nv b) :
    monoEval nv φ (a + b) = monoEval nv φ a * monoEval nv φ b := by
  unfold monoEval
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [keyExp_add a b i (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega)), pow_add]

theorem monoEval_zero (nv : ℕ) (φ : ℕ → R) : monoEval nv φ 0 = 1 := by
  unfold monoEval
  exact prod_eq_one fun i _ => by simp [keyExp]

end Eval

/-! ## Term lists with natural coefficients -/

section Den

variable {R : Type*} [CommRing R] (nv : ℕ) (φ : ℕ → R)

/-- The value of a term list with natural coefficients. -/
def den (l : NTerms) : R := (l.map fun t => (t.2 : R) * monoEval nv φ t.1).sum

@[simp] theorem den_nil : den nv φ [] = 0 := rfl

theorem den_cons (t : ℕ × ℕ) (l : NTerms) : den nv φ (t :: l) = (t.2 : R) * monoEval nv φ t.1 + den nv φ l := by
  simp [den]

theorem den_append (a b : NTerms) : den nv φ (a ++ b) = den nv φ a + den nv φ b := by
  simp [den, List.sum_append]

theorem den_shift {k : ℕ} (c : ℕ) (hk : SmallKey nv k) :
    ∀ {l : NTerms}, (∀ t ∈ l, SmallKey nv t.1) → den nv φ (shift k c l) = (c : R) * monoEval nv φ k * den nv φ l
  | [], _ => by simp [shift]
  | t :: l, hl => by
    have e : shift k c (t :: l) = (t.1 + k, t.2 * c) :: shift k c l := rfl
    rw [e, den_cons, den_cons, den_shift c hk (fun u hu => hl u (List.mem_cons_of_mem _ hu)),
      monoEval_add nv φ (hl t List.mem_cons_self) hk]
    push_cast
    ring

/-- Scaling by `c` (the shift by the key `0`) multiplies the value by `c`, for any keys. -/
theorem den_shift0 (c : ℕ) : ∀ l : NTerms, den nv φ (shift 0 c l) = (c : R) * den nv φ l
  | [] => by simp [shift]
  | t :: l => by
    have e : shift 0 c (t :: l) = (t.1 + 0, t.2 * c) :: shift 0 c l := rfl
    rw [e, den_cons, den_cons, den_shift0 c l, Nat.add_zero]
    push_cast
    ring

/-- **Merging adds the values**, for any fuel. -/
theorem den_merge : ∀ (f : ℕ) (a b : NTerms), den nv φ (merge f a b) = den nv φ a + den nv φ b
  | 0, a, b => den_append nv φ a b
  | f + 1, [], b => by
    show den nv φ b = _
    simp
  | f + 1, x :: a, [] => by
    show den nv φ (x :: a) = _
    simp
  | f + 1, x :: a, y :: b => by
    have e : merge (f + 1) (x :: a) (y :: b) =
        Bool.rec (Bool.rec ((y.1, y.2) :: merge f (x :: a) b) ((x.1, x.2 + y.2) :: merge f a b) (Nat.beq x.1 y.1))
          ((x.1, x.2) :: merge f a (y :: b)) (Nat.blt x.1 y.1) := rfl
    rw [e]
    cases hlt : Nat.blt x.1 y.1
    · cases heq : Nat.beq x.1 y.1
      · show den nv φ ((y.1, y.2) :: merge f (x :: a) b) = _
        simp only [den_cons, den_merge f]
        ring
      · show den nv φ ((x.1, x.2 + y.2) :: merge f a b) = _
        have hxy : x.1 = y.1 := Nat.eq_of_beq_eq_true heq
        simp only [den_cons, den_merge f]
        rw [hxy]
        push_cast
        ring
    · show den nv φ ((x.1, x.2) :: merge f a (y :: b)) = _
      simp only [den_cons, den_merge f]
      ring

theorem den_mergeRound (f : ℕ) : ∀ ls : List NTerms,
    ((mergeRound f ls).map (den nv φ)).sum = (ls.map (den nv φ)).sum
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
    rw [mergeRound, List.map_cons, List.sum_cons, den_merge, den_mergeRound f rest]
    simp [add_assoc]

theorem den_foldr (f : ℕ) : ∀ ls : List NTerms, den nv φ (ls.foldr (merge f) []) = (ls.map (den nv φ)).sum
  | [] => rfl
  | l :: ls => by rw [List.foldr_cons, den_merge, den_foldr f ls, List.map_cons, List.sum_cons]

/-- **Merging a list of term lists adds their values.** -/
theorem den_mergeAll (f : ℕ) : ∀ (r : ℕ) (ls : List NTerms), den nv φ (mergeAll f r ls) = (ls.map (den nv φ)).sum
  | 0, ls => den_foldr nv φ f ls
  | r + 1, ls => by
    show den nv φ (mergeAll f r (mergeRound f ls)) = _
    rw [den_mergeAll f r, den_mergeRound]

/-- **Coefficients divisible by `p` give the value `0`** where `p = 0`. -/
theorem den_zeroMod {p : ℕ} (hp : (p : R) = 0) : ∀ {l : NTerms}, zeroMod p l = true → den nv φ l = 0
  | [], _ => rfl
  | t :: l, h => by
    change (Nat.beq (t.2 % p) 0 && zeroMod p l) = true at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h1)
    rw [den_cons, den_zeroMod hp h2, hq]
    push_cast
    rw [hp]
    ring

end Den

theorem guards_spec {G : ℕ} : ∀ {l : NTerms}, guards G l = true → ∀ t ∈ l, Nat.land t.1 G = 0
  | [], _ => by simp
  | t :: l, h => by
    change Bool.rec false (guards G l) (Nat.beq (Nat.land t.1 G) 0) = true at h
    cases hb : Nat.beq (Nat.land t.1 G) 0
    · rw [hb] at h
      exact (Bool.false_ne_true h).elim
    · rw [hb] at h
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Nat.eq_of_beq_eq_true hb
      · exact guards_spec h u hu

theorem testBit_guardMask : ∀ {n i : ℕ}, i < n → (guardMask n).testBit (8 * i + 7) = true
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    rw [guardMask, Nat.testBit_lor, Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact Or.inl (testBit_guardMask h)
    · exact Or.inr (Nat.testBit_two_pow_self)

/-- **Guarded keys have small exponents**: if the bits 7 of the bytes `0, …, nv - 1` of `k` are clear, every
exponent of `k` among the first `nv` variables is `< 128`. -/
theorem smallKey_of_guard {nv k : ℕ} (h : Nat.land k (guardMask nv) = 0) : SmallKey nv k := by
  intro i hi
  have hb : k.testBit (8 * i + 7) = false := by
    have h' := congrArg (fun x => x.testBit (8 * i + 7)) h
    change (k &&& guardMask nv).testBit (8 * i + 7) = (0 : ℕ).testBit (8 * i + 7) at h'
    rw [Nat.testBit_land, testBit_guardMask hi, Bool.and_true, Nat.zero_testBit] at h'
    exact h'
  have h7 : (k >>> (8 * i)).testBit 7 = false := by
    rw [Nat.testBit_shiftRight]
    exact hb
  rw [Nat.testBit_eq_decide_div_mod_eq] at h7
  have h7' : ¬ (k >>> (8 * i) / 128 % 2 = 1) := by simpa using h7
  show (k >>> (8 * i)) % 256 < 128
  omega

/-! ## Codes, buckets and the cover -/

theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (f : α → List β) (g : β → M) :
    ∀ l : List α, ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_map_flatMap f g l, List.map_cons, List.sum_cons]

theorem nth_mem {α : Type} {d : α} : ∀ {l : List α} {i : ℕ}, i < l.length → nth d l i ∈ l
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: _, _ + 1, h => List.mem_cons_of_mem _ (nth_mem (Nat.lt_of_succ_lt_succ h))

theorem nth_mem_or {α : Type} {d : α} : ∀ (l : List α) (i : ℕ), nth d l i ∈ l ∨ nth d l i = d
  | [], _ => Or.inr rfl
  | _ :: _, 0 => Or.inl List.mem_cons_self
  | _ :: l, i + 1 => (nth_mem_or l i).imp (List.mem_cons_of_mem _) id

theorem sum_range_nth {α : Type} {M : Type*} [AddCommMonoid M] (d : α) (F : α → M) :
    ∀ l : List α, ((List.range l.length).map fun j => F (nth d l j)).sum = (l.map F).sum
  | [] => rfl
  | x :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.map_cons,
      List.sum_cons]
    congr 1
    exact sum_range_nth d F l

theorem code_div {i j q : ℕ} (hj : j < 64) (hq : q < 2 ^ 20) : code i j q / 2 ^ 26 = i := by
  unfold code
  omega

theorem code_mid {i j q : ℕ} (hj : j < 64) (hq : q < 2 ^ 20) : code i j q / 2 ^ 20 % 64 = j := by
  unfold code
  omega

theorem code_mod {i j q : ℕ} (hq : q < 2 ^ 20) : code i j q % 2 ^ 20 = q := by
  unfold code
  omega

section Values

variable {R : Type*} [CommRing R] (nv : ℕ) (φ : ℕ → R)

/-- The value of a piece. -/
def pval (P : Piece) : R := den nv φ P.pos - den nv φ P.neg

/-- The value of a term. -/
def tval (t : ℕ × ℤ) : R := (t.2 : R) * monoEval nv φ t.1

theorem eval_eq_tval (p : KPoly) : eval nv φ p = (p.map (tval nv φ)).sum := rfl

theorem eval_signed (P : Piece) : eval nv φ (signed P) = pval nv φ P := by
  have h1 : ∀ l : NTerms, eval nv φ (l.map fun t => (t.1, (t.2 : ℤ))) = den nv φ l := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih =>
      rw [List.map_cons, eval_cons, den_cons, ih]
      push_cast
      ring
  have h2 : ∀ l : NTerms, eval nv φ (l.map fun t => (t.1, -(t.2 : ℤ))) = - den nv φ l := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.map_cons, eval_cons, den_cons, ih]
      push_cast
      ring
  unfold signed pval
  rw [eval_append, h1, h2]
  ring

theorem eval_flatMap_signed : ∀ parts : List Piece,
    eval nv φ (parts.flatMap signed) = (parts.map (pval nv φ)).sum
  | [] => rfl
  | P :: parts => by
    rw [List.flatMap_cons, eval_append, eval_signed, eval_flatMap_signed parts, List.map_cons, List.sum_cons]

theorem sides_spec {G : ℕ} (hG : G = guardMask nv) (gens : List KPoly) (pcs : List (List Piece)) :
    ∀ ts : List ℕ, ts.all (codeOK G gens pcs) = true →
      ((sides gens pcs ts).1.map (den nv φ)).sum - ((sides gens pcs ts).2.map (den nv φ)).sum =
        (ts.map fun t => tval nv φ (genTerm gens t) * pval nv φ (piece pcs t)).sum
  | [], _ => by
    show (0 : R) - 0 = 0
    ring
  | t :: ts, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ht, hts⟩ := h
    have ih := sides_spec hG gens pcs ts hts
    change (Nat.beq (Nat.land (genTerm gens t).1 G) 0 && guards G (piece pcs t).pos &&
      guards G (piece pcs t).neg) = true at ht
    simp only [Bool.and_eq_true] at ht
    obtain ⟨⟨hk, hp⟩, hn⟩ := ht
    subst hG
    have sk : SmallKey nv (genTerm gens t).1 := smallKey_of_guard (Nat.eq_of_beq_eq_true hk)
    have sp : ∀ u ∈ (piece pcs t).pos, SmallKey nv u.1 := fun u hu => smallKey_of_guard (guards_spec hp u hu)
    have sn : ∀ u ∈ (piece pcs t).neg, SmallKey nv u.1 := fun u hu => smallKey_of_guard (guards_spec hn u hu)
    have e : sides gens pcs (t :: ts) = Int.rec (motive := fun _ => List NTerms × List NTerms)
        (fun c => (shift (genTerm gens t).1 c (piece pcs t).pos :: (sides gens pcs ts).1,
          shift (genTerm gens t).1 c (piece pcs t).neg :: (sides gens pcs ts).2))
        (fun c => (shift (genTerm gens t).1 (c + 1) (piece pcs t).neg :: (sides gens pcs ts).1,
          shift (genTerm gens t).1 (c + 1) (piece pcs t).pos :: (sides gens pcs ts).2))
        (genTerm gens t).2 := rfl
    rw [e, List.map_cons, List.sum_cons, ← ih]
    unfold tval pval
    cases hc : (genTerm gens t).2 with
    | ofNat c =>
      simp only [List.map_cons, List.sum_cons, den_shift nv φ c sk sp, den_shift nv φ c sk sn,
        Int.ofNat_eq_coe, Int.cast_natCast]
      ring
    | negSucc c =>
      simp only [List.map_cons, List.sum_cons, den_shift nv φ (c + 1) sk sp, den_shift nv φ (c + 1) sk sn,
        Int.cast_negSucc]
      push_cast
      ring

/-- **A bucket that passes its check modulo `p` is an identity** where `p = 0`: the sum of its products is its part
of `h`. -/
theorem bucket_soundp {p G F r : ℕ} (hG : G = guardMask nv) (hp1 : 1 ≤ p) (hp0 : (p : R) = 0)
    {gens : List KPoly} {pcs : List (List Piece)} {ts : List ℕ} {hp : Piece}
    (h : bucketOKp p G F r gens pcs ts hp = true) :
    (ts.map fun t => tval nv φ (genTerm gens t) * pval nv φ (piece pcs t)).sum = pval nv φ hp := by
  unfold bucketOKp at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hc, hz⟩ := h
  have e := den_zeroMod nv φ hp0 hz
  simp only [den_mergeAll, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_map,
    Function.comp_def, den_shift0, List.sum_map_mul_left] at e
  have hcast : ((p - 1 : ℕ) : R) = -1 := by
    rw [Nat.cast_sub hp1, hp0]
    ring
  rw [hcast] at e
  rw [← sides_spec nv φ hG gens pcs ts hc]
  unfold pval
  linear_combination e

/-- The sum over all codes is `Σᵢ gᵢ · cᵢ`, with `cᵢ` the sum of the pieces of cofactor `i`. -/
theorem sum_allCodes {gens : List KPoly} {pcs : List (List Piece)} (hg : ∀ g ∈ gens, g.length ≤ 64)
    (hp : ∀ l ∈ pcs, l.length ≤ 2 ^ 20) :
    ((allCodes gens pcs).map fun t => tval nv φ (genTerm gens t) * pval nv φ (piece pcs t)).sum =
      ((List.range gens.length).map fun i => eval nv φ (nth [] gens i) *
        ((List.range (nth [] pcs i).length).map fun q => pval nv φ (nth ⟨[], []⟩ (nth [] pcs i) q)).sum).sum := by
  unfold allCodes
  rw [sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have hgi : (nth [] gens i).length ≤ 64 := hg _ (nth_mem (List.mem_range.mp hi))
  have hpi : (nth [] pcs i).length ≤ 2 ^ 20 := by
    rcases nth_mem_or pcs i with h | h
    · exact hp _ h
    · rw [h]
      norm_num
  rw [sum_map_flatMap, eval_eq_tval, ← sum_range_nth (0, 0) (tval nv φ) (nth [] gens i), ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj' : j < 64 := lt_of_lt_of_le (List.mem_range.mp hj) hgi
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun q hq' => ?_)
  have hq'' : q < 2 ^ 20 := lt_of_lt_of_le (List.mem_range.mp hq') hpi
  simp only [Function.comp, genTerm, piece, code_div hj' hq'', code_mid hj' hq'', code_mod hq'']

end Values

theorem mergeR_perm : ∀ (f : ℕ) (a b : List ℕ), (mergeR f a b).Perm (a ++ b)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, x :: a, [] => by
    show (x :: a).Perm ((x :: a) ++ [])
    rw [List.append_nil]
  | f + 1, x :: a, y :: b => by
    show (Bool.rec (motive := fun _ => List ℕ) (y :: mergeR f (x :: a) b) (x :: mergeR f a (y :: b)) (Nat.ble x y)).Perm _
    cases Nat.ble x y
    · exact ((mergeR_perm f (x :: a) b).cons y).trans List.perm_middle.symm
    · exact (mergeR_perm f a (y :: b)).cons x

theorem msortR_perm : ∀ (d : ℕ) (l : List ℕ), (msortR d l).Perm l
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => List.Perm.refl _
  | d + 1, x :: y :: l => by
    show (mergeR (x :: y :: l).length (msortR d ((x :: y :: l).take ((x :: y :: l).length / 2)))
      (msortR d ((x :: y :: l).drop ((x :: y :: l).length / 2)))).Perm _
    refine (mergeR_perm _ _ _).trans (((msortR_perm d _).append (msortR_perm d _)).trans ?_)
    rw [List.take_append_drop]

theorem coverOK_spec {D : ℕ} {gens : List KPoly} {pcs : List (List Piece)} {ts : List ℕ}
    (h : coverOK D gens pcs ts = true) :
    (∀ g ∈ gens, g.length ≤ 64) ∧ (∀ l ∈ pcs, l.length ≤ 2 ^ 20) ∧ ts.Perm (allCodes gens pcs) := by
  unfold coverOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.ble_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rw [← h3]
  exact (msortR_perm D ts).symm

theorem chainOK_cover : ∀ (L : List (ℕ × ℕ)) (lo : ℕ), chainOK lo L = true →
    ∀ c, lo ≤ c → ∃ lh ∈ L, inIvl lh.1 lh.2 c = true
  | [], _, h, _, _ => by simp [chainOK] at h
  | [(a, b)], lo, h, c, hc => by
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨(a, b), List.mem_singleton_self _, ?_⟩
    simp [inIvl, h.1, h.2, hc]
  | (a, b) :: (a', b') :: rest, lo, h, c, hc => by
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hab⟩, hr⟩ := h
    by_cases hcb : c < b
    · refine ⟨(a, b), List.mem_cons_self, ?_⟩
      have hb : b ≠ 0 := by omega
      simp [inIvl, hc, hcb, hb]
    · obtain ⟨lh, hm, hin⟩ := chainOK_cover ((a', b') :: rest) b hr c (by omega)
      exact ⟨lh, List.mem_cons_of_mem _ hm, hin⟩

theorem ivlCheck_spec {C R : List ℕ} {lo hi : ℕ} (h : ivlCheck C R lo hi = true) :
    (C.filter (inIvl lo hi)).Perm (R.filter (inIvl lo hi)) := by
  unfold ivlCheck at h
  rw [beq_iff_eq] at h
  refine (msortR_perm 20 _).symm.trans ?_
  rw [h]
  exact msortR_perm 20 _

/-- **The intervals give the global comparison.** -/
theorem perm_of_ivls {C R : List ℕ} {L : List (ℕ × ℕ)} (hc : chainOK 0 L = true)
    (h : L.all (fun lh => ivlCheck C R lh.1 lh.2) = true) : C.Perm R := by
  refine List.perm_iff_count.mpr fun c => ?_
  obtain ⟨lh, hm, hin⟩ := chainOK_cover L 0 hc c (Nat.zero_le c)
  have := (ivlCheck_spec (List.all_eq_true.mp h lh hm)).count_eq c
  rwa [List.count_filter hin, List.count_filter hin] at this

theorem coverIvl_spec {gens : List KPoly} {pcs : List (List Piece)} {ts : List ℕ} {L : List (ℕ × ℕ)}
    (hh : coverHead gens pcs L = true) (hl : L.all (fun lh => ivlCheck ts (allCodes gens pcs) lh.1 lh.2) = true) :
    (∀ g ∈ gens, g.length ≤ 64) ∧ (∀ l ∈ pcs, l.length ≤ 2 ^ 20) ∧ ts.Perm (allCodes gens pcs) := by
  unfold coverHead at hh
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.ble_eq] at hh
  obtain ⟨⟨h1, h2⟩, h3⟩ := hh
  exact ⟨h1, h2, perm_of_ivls h3 hl⟩

/-- The inverse of `termCode`. -/
def decodeTerm (CB n : ℕ) : ℕ × ℤ :=
  (n / 2 ^ (CB + 1), if n % 2 ^ (CB + 1) % 2 = 0 then ((n % 2 ^ (CB + 1) / 2 : ℕ) : ℤ)
    else Int.negSucc (n % 2 ^ (CB + 1) / 2))

theorem decodeTerm_termCode {CB k : ℕ} {c : ℤ} (hc : c.natAbs < 2 ^ CB) :
    decodeTerm CB (termCode CB k c) = (k, c) := by
  have hM : 0 < 2 ^ (CB + 1) := by positivity
  cases c with
  | ofNat n =>
    have hn : n < 2 ^ CB := by simpa using hc
    have hz : 2 * n < 2 ^ (CB + 1) := by rw [pow_succ]; omega
    have e : termCode CB k (Int.ofNat n) = 2 * n + k * 2 ^ (CB + 1) := by
      unfold termCode
      show k * 2 ^ (CB + 1) + 2 * n = _
      ring
    unfold decodeTerm
    rw [e, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hz, zero_add, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hz]
    simp
  | negSucc n =>
    have hn : n + 1 < 2 ^ CB := by simpa [Int.natAbs_negSucc] using hc
    have hz : 2 * n + 1 < 2 ^ (CB + 1) := by rw [pow_succ]; omega
    have e : termCode CB k (Int.negSucc n) = (2 * n + 1) + k * 2 ^ (CB + 1) := by
      unfold termCode
      show k * 2 ^ (CB + 1) + (2 * n + 1) = _
      ring
    unfold decodeTerm
    rw [e, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hz, zero_add, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hz]
    have h1 : (2 * n + 1) % 2 = 1 := by omega
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp [h1, h2]

theorem hOK_perm {CB D : ℕ} {h : KPoly} {parts : List Piece} (hh : hOK CB D h parts = true) :
    (parts.flatMap signed).Perm h := by
  unfold hOK at hh
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, beq_iff_eq] at hh
  obtain ⟨hb, he⟩ := hh
  have hp : ((parts.flatMap signed).map fun t => termCode CB t.1 t.2).Perm (h.map fun t => termCode CB t.1 t.2) := by
    refine (msortR_perm D _).symm.trans ?_
    rw [he]
    exact msortR_perm D _
  have e1 : parts.flatMap signed =
      ((parts.flatMap signed).map fun t => termCode CB t.1 t.2).map (decodeTerm CB) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id (parts.flatMap signed)]
    exact List.map_congr_left fun t ht =>
      (decodeTerm_termCode (hb t (List.mem_append_left _ ht))).symm
  have e2 : h = (h.map fun t => termCode CB t.1 t.2).map (decodeTerm CB) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id h]
    exact List.map_congr_left fun t ht => (decodeTerm_termCode (hb t (List.mem_append_right _ ht))).symm
  rw [e1, e2]
  exact hp.map _

/-- **Soundness of the kernel check of a cofactor certificate modulo `p`**: in every commutative ring in which
`p = 0`, at every assignment at which all generators vanish, `h` vanishes. -/
theorem cofmod_sound_of {nv p D CB : ℕ} {gens : List KPoly} {h : KPoly} {pcs : List (List Piece)}
    {bks : List (ℕ × ℕ × List ℕ × Piece)} (hp1 : 1 ≤ p)
    (hb : bks.all (fun b => bucketOKp p (guardMask nv) b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true)
    (hc : (∀ g ∈ gens, g.length ≤ 64) ∧ (∀ l ∈ pcs, l.length ≤ 2 ^ 20) ∧
      (bks.flatMap fun b => b.2.2.1).Perm (allCodes gens pcs))
    (hh : hOK CB D h (bks.map fun b => b.2.2.2) = true)
    {R : Type*} [CommRing R] (hp0 : (p : R) = 0) (φ : ℕ → R) (hg : ∀ g ∈ gens, eval nv φ g = 0) :
    eval nv φ h = 0 := by
  obtain ⟨hg16, hp20, hperm⟩ := hc
  rw [← eval_perm _ φ (hOK_perm hh), eval_flatMap_signed, List.map_map]
  have e1 : (bks.map ((pval nv φ) ∘ fun b => b.2.2.2)).sum =
      ((bks.flatMap fun b => b.2.2.1).map fun t => tval nv φ (genTerm gens t) * pval nv φ (piece pcs t)).sum := by
    rw [sum_map_flatMap]
    refine congrArg List.sum (List.map_congr_left fun b hb' => ?_)
    exact (bucket_soundp nv φ rfl hp1 hp0 (List.all_eq_true.mp hb b hb')).symm
  rw [e1, (hperm.map _).sum_eq, sum_allCodes nv φ hg16 hp20]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  show eval nv φ (nth [] gens i) * _ = 0
  rw [hg _ (nth_mem (List.mem_range.mp hi)), zero_mul]

/-- **Soundness**, with the cover checked in one declaration. -/
theorem cofmod_sound {nv p D CB : ℕ} {gens : List KPoly} {h : KPoly} {pcs : List (List Piece)}
    {bks : List (ℕ × ℕ × List ℕ × Piece)} (hp1 : 1 ≤ p)
    (hb : bks.all (fun b => bucketOKp p (guardMask nv) b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true)
    (hc : coverOK D gens pcs (bks.flatMap fun b => b.2.2.1) = true)
    (hh : hOK CB D h (bks.map fun b => b.2.2.2) = true)
    {R : Type*} [CommRing R] (hp0 : (p : R) = 0) (φ : ℕ → R) (hg : ∀ g ∈ gens, eval nv φ g = 0) :
    eval nv φ h = 0 :=
  cofmod_sound_of hp1 hb (coverOK_spec hc) hh hp0 φ hg

/-- **Soundness**, with the cover compared by intervals. -/
theorem cofmod_sound_ivl {nv p D CB : ℕ} {gens : List KPoly} {h : KPoly} {pcs : List (List Piece)}
    {bks : List (ℕ × ℕ × List ℕ × Piece)} {L : List (ℕ × ℕ)} (hp1 : 1 ≤ p)
    (hb : bks.all (fun b => bucketOKp p (guardMask nv) b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true)
    (hc : coverHead gens pcs L = true)
    (hl : L.all (fun lh => ivlCheck (bks.flatMap fun b => b.2.2.1) (allCodes gens pcs) lh.1 lh.2) = true)
    (hh : hOK CB D h (bks.map fun b => b.2.2.2) = true)
    {R : Type*} [CommRing R] (hp0 : (p : R) = 0) (φ : ℕ → R) (hg : ∀ g ∈ gens, eval nv φ g = 0) :
    eval nv φ h = 0 :=
  cofmod_sound_of hp1 hb (coverIvl_spec hc hl) hh hp0 φ hg

end L6KSpec.C4
