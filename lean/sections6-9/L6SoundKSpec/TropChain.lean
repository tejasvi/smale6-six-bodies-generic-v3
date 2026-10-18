import L6KSpec.TropChain
import L6SoundKSpec.C4Cert
import L6SoundKSpec.TropLeaf

/-!
# Soundness of the chains of identities

`chainStep_sound`: where `p = 0`, a checked step gives `T[k] = Σ c · X^m · T[r]` (values `den` of `L6KSpec.C4`).
`chain_vanish`: if the first `n` entries of the table vanish at a point and the steps are checked and in order, all
entries up to the last element vanish there. `sysEmpty_of_chain`: if the inputs of the table are the polynomials of a
system (sorted by key), the steps are checked and the last element is the constant `1`, the system has no common zero
in any field of characteristic `p` (in particular none in the torus).
-/

namespace L6KSpec.Trop

open L6KSpec.C4 Lean6.Special Lean6.Special.Comp Lean6.Special.D88.Trop

section Chain

variable {R : Type*} [CommRing R] (nv : ℕ) (φ : ℕ → R)

theorem nth_guards {G : ℕ} {T : List NTerms} (hT : T.all (guards G) = true) (i : ℕ) :
    guards G (nth [] T i) = true := by
  rcases nth_mem_or T i with h | h
  · exact List.all_eq_true.mp hT _ h
  · rw [h]; rfl

/-- **One identity of a chain**: where `p = 0`, `T[k]` is the sum of the products of its cofactor terms. -/
theorem chainStep_sound {p G : ℕ} (hG : G = guardMask nv) (hp1 : 1 ≤ p) (hp0 : (p : R) = 0) {T : List NTerms}
    (hT : T.all (guards G) = true) {s : ChainStep} (h : chainStepOK p G T s = true) :
    den nv φ (nth [] T s.1) =
      (s.2.2.2.map fun t => (t.2.2 : R) * monoEval nv φ t.2.1 * den nv φ (nth [] T t.1)).sum := by
  simp only [chainStepOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hk, hz⟩ := h
  have h0 := den_zeroMod nv φ hp0 hz
  rw [den_mergeAll, List.map_cons, List.sum_cons, den_shift0, List.map_map] at h0
  have hsmall : ∀ i, ∀ t ∈ nth [] T i, SmallKey nv t.1 := fun i t ht =>
    smallKey_of_guard (hG ▸ guards_spec (nth_guards hT i) t ht)
  have e : (s.2.2.2.map ((den nv φ) ∘ fun t => shift t.2.1 t.2.2 (nth [] T t.1))) =
      s.2.2.2.map fun t => (t.2.2 : R) * monoEval nv φ t.2.1 * den nv φ (nth [] T t.1) := by
    refine List.map_congr_left fun t ht => ?_
    have hm : SmallKey nv t.2.1 := smallKey_of_guard (by simpa [hG] using hk t ht)
    exact den_shift nv φ t.2.2 hm (hsmall t.1)
  rw [e] at h0
  have hp' : ((p - 1 : ℕ) : R) = -1 := by
    rw [Nat.cast_sub hp1, hp0, Nat.cast_one, zero_sub]
  rw [hp', neg_one_mul, neg_add_eq_zero] at h0
  exact h0

/-- **The chain**: where `p = 0` and the first `n` entries vanish, every entry up to the last step vanishes. -/
theorem chain_vanish {p G : ℕ} (hG : G = guardMask nv) (hp1 : 1 ≤ p) (hp0 : (p : R) = 0) {T : List NTerms}
    (hT : T.all (guards G) = true) :
    ∀ (steps : List ChainStep) (n : ℕ), (∀ i < n, den nv φ (nth [] T i) = 0) →
      steps.all (chainStepOK p G T) = true → chainOrder steps n = true →
      ∀ i < n + steps.length, den nv φ (nth [] T i) = 0
  | [], n, hin, _, _ => fun i hi => hin i (by simpa using hi)
  | s :: rest, n, hin, hall, hord => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    change (Nat.beq s.1 n && s.2.2.2.all (fun t => Nat.blt t.1 n) && chainOrder rest (n + 1)) = true at hord
    simp only [Bool.and_eq_true, List.all_eq_true] at hord
    obtain ⟨⟨hn, hlt⟩, hrest⟩ := hord
    have hn' : s.1 = n := Nat.eq_of_beq_eq_true hn
    have h0 : den nv φ (nth [] T n) = 0 := by
      rw [← hn', chainStep_sound nv φ hG hp1 hp0 hT hall.1]
      refine List.sum_eq_zero fun v hv => ?_
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
      have htn : t.1 < n := by simpa using hlt t ht
      rw [hin t.1 htn, mul_zero]
    have hin' : ∀ i < n + 1, den nv φ (nth [] T i) = 0 := fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact hin i h
      · rw [h]; exact h0
    intro i hi
    exact chain_vanish hG hp1 hp0 hT rest (n + 1) hin' hall.2 hrest i (by simp at hi; omega)

end Chain

/-! ## The inputs of the table: a system of polynomials -/

theorem mergeN_perm : ∀ (f : ℕ) (a b : NTerms), (mergeN f a b).Perm (a ++ b)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, x :: a, [] => by
    show (x :: a).Perm ((x :: a) ++ [])
    rw [List.append_nil]
  | f + 1, x :: a, y :: b => by
    show (Bool.rec (motive := fun _ => NTerms) (y :: mergeN f (x :: a) b) (x :: mergeN f a (y :: b))
      (Nat.ble x.1 y.1)).Perm _
    cases Nat.ble x.1 y.1
    · exact ((mergeN_perm f (x :: a) b).cons y).trans List.perm_middle.symm
    · exact (mergeN_perm f a (y :: b)).cons x

theorem sortN_perm : ∀ (d : ℕ) (l : NTerms), (sortN d l).Perm l
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => List.Perm.refl _
  | d + 1, x :: y :: l => by
    show (mergeN (x :: y :: l).length (sortN d ((x :: y :: l).take ((x :: y :: l).length / 2)))
      (sortN d ((x :: y :: l).drop ((x :: y :: l).length / 2)))).Perm _
    refine (mergeN_perm _ _ _).trans (((sortN_perm d _).append (sortN_perm d _)).trans ?_)
    rw [List.take_append_drop]

theorem den_perm {R : Type*} [CommRing R] (nv : ℕ) (φ : ℕ → R) {l l' : NTerms} (h : l.Perm l') :
    den nv φ l = den nv φ l' :=
  (h.map _).sum_eq

/-- A term list of `toN` has the value of the polynomial. -/
theorem den_toN {p : ℕ} [NeZero p] {K : Type*} [CommRing K] [CharP K p] (nv : ℕ) (x : ℕ → K) :
    ∀ (f : Comp.Poly ℕ), (∀ t ∈ f, t.2.length ≤ nv ∧ ∀ e ∈ t.2, e < 256) →
      den nv x (toN f) = Poly.eval (modHomK p K) x f
  | [], _ => rfl
  | t :: f, hf => by
    have ht := hf t List.mem_cons_self
    have ih := den_toN nv x f fun u hu => hf u (List.mem_cons_of_mem _ hu)
    show den nv x ((packKey t.2, t.1) :: toN f) = _
    rw [den_cons, Poly.eval_cons, ih]
    dsimp only
    rw [monoEval_packKey nv x t.2 ht.1 ht.2]
    simp [modHomK]

/-- **A checked chain from a system to the constant `1`**: the system has no common zero in the torus (nor anywhere)
of any field of characteristic `p`. -/
theorem sysEmpty_of_chain {p : ℕ} [NeZero p] {s : List (Comp.Poly ℕ)} (hs : sysSmall 17 s = true) (hp1 : 1 ≤ p)
    {T : List NTerms} (hT : T.all (guards (guardMask 17)) = true)
    (hin : (List.range s.length).all (fun i => nth [] T i == sortN 40 (toN (s.getD i []))) = true)
    {steps : List ChainStep} (hall : steps.all (chainStepOK p (guardMask 17) T) = true)
    (hord : chainOrder steps s.length = true) (hne : 0 < steps.length)
    (hlast : nth [] T (s.length + steps.length - 1) = [(0, 1)]) :
    TorusEmptySys p s := by
  intro K _ _ x _
  by_contra hall'
  push Not at hall'
  have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
  have hin' : ∀ i < s.length, den 17 x (nth [] T i) = 0 := by
    intro i hi
    have he : nth [] T i = sortN 40 (toN (s.getD i [])) := by
      have := List.all_eq_true.mp hin i (List.mem_range.mpr hi)
      simpa using this
    have hmem : s.getD i [] ∈ s := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    rw [he, den_perm 17 x (sortN_perm 40 _), den_toN 17 x _ (sysSmall_spec hs _ hmem)]
    exact hall' _ hmem
  have h := chain_vanish 17 x rfl hp1 hp0 hT steps s.length hin' hall hord (s.length + steps.length - 1) (by omega)
  rw [hlast, den_cons, den_nil, monoEval_zero] at h
  simp at h

end L6KSpec.Trop
