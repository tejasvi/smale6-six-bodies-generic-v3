import L6K.F4.Check
import L6Sound.Poly.Sound

/-!
# Term lists with natural coefficients: their values

`den nv φ l` is the value of a term list `l` (natural coefficients) at an assignment `φ`, as `L6.Poly.eval` for
integer coefficients. Shifting by a monomial multiplies the value (for keys with small exponents), merging adds the
values (for any fuel and any order of the inputs), and `listEq` is equality.
-/

namespace L6K.F4

open L6.Poly Finset

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

end Den

theorem listEq_eq : ∀ {a b : NTerms}, listEq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h (by decide)
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h (by decide)
  | x :: a, y :: b, h => by
    change ((Nat.beq x.1 y.1 && Nat.beq x.2 y.2) && listEq a b) = true at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [listEq_eq h3, Prod.ext (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)]

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

end L6K.F4
