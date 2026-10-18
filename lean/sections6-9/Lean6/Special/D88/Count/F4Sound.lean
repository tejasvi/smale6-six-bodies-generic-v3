import Lean6.Special.Comp.D88.Count.F4
import Lean6.Special.K4.C4.GBSound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Soundness of the F4 engine

Fix a commutative `ZMod p`-algebra `R` and a point `x : ℕ → R`. A key `k` stands for the monomial
`monoK x n k = ∏ᵢ xᵢ ^ expK k i` (`Mono.eval` of `decK n k`); a key polynomial `f` for `evalS f`, the sum of its
coefficients times its monomials; a row `r` of a matrix with column keys `cols` for `rowVal cols r`; a dense vector
`acc` for `evalDense cols acc`.

Every constructor of `Good` preserves vanishing at `x`, given that the inputs vanish (`good_sound`):
* a monomial multiple (`shiftS`): for valid keys of total degree at most `L`, adding keys and subtracting `Bⁿ − 1` is
  multiplying monomials (`shift_key`, from `encLow_add` and `decK_encK`);
* a scalar multiple; the conversion of a polynomial into a row (all or nothing, `rowVal_toColImpl`) and back
  (`decodeV`, all or nothing on the validity of the keys);
* the reduction of a row: every update of the dense accumulator adds a multiple of a pivot row
  (`evalDense_addMulAux`), so the value is unchanged when the pivot rows vanish (`rowVal_reduceC`).

Hence every polynomial of the output basis vanishes at every common zero of the inputs (`f4_good`).
-/

namespace Lean6.Special.D88.Count

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.Count Lean6.Special.K4.C4 Finset

/-! ## Small facts -/

theorem L_eq : L = 31 := rfl
theorem B_eq : B = 32 := rfl
theorem B_pos (n : ℕ) : 0 < B ^ n := pow_pos (by decide) n
theorem one_le_B_pow (n : ℕ) : 1 ≤ B ^ n := B_pos n

theorem aGetD_lt {a : Array ℕ} {t : ℕ} (ht : t < a.size) : a.getD t 0 = a[t] := by simp [ht]
theorem aGetD_ge {a : Array ℕ} {t : ℕ} (ht : a.size ≤ t) : a.getD t 0 = 0 := by
  simp [Array.getElem?_eq_none ht]
theorem aGetD_map {a : Array ℕ} {g : ℕ → ℕ} {t : ℕ} (ht : t < a.size) : (a.map g).getD t 0 = g (a.getD t 0) := by
  simp [ht]
theorem lGetD_lt {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]
theorem lGetD_ge {l : List ℕ} {i : ℕ} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_push_lt {xs : Array ℕ} {a t : ℕ} (h : t < xs.size) : (xs.push a).getD t 0 = xs.getD t 0 := by
  simp [Array.getElem?_push, h, Nat.ne_of_lt h]
theorem getD_push_eq {xs : Array ℕ} {a : ℕ} : (xs.push a).getD xs.size 0 = a := by
  simp
theorem getD_set_ne {xs : Array ℕ} {j v i : ℕ} (hj : j < xs.size) (h : i ≠ j) :
    (xs.set j v hj).getD i 0 = xs.getD i 0 := by
  simp [Ne.symm h]
theorem getD_set_eq {xs : Array ℕ} {j v : ℕ} (hj : j < xs.size) : (xs.set j v hj).getD j 0 = v := by
  simp [hj]

theorem list_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ m, ((List.range m).map g).sum = ∑ i ∈ range m, g i
  | 0 => rfl
  | m + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range g m, sum_range_succ]; simp

/-! ## Keys -/

theorem encLow_le : ∀ (e : List ℕ), encLow e ≤ B ^ e.length - 1
  | [] => by simp [encLow]
  | a :: e => by
    have ih := encLow_le e
    have hpos := one_le_B_pow e.length
    simp only [encLow, List.length_cons, pow_succ]
    have h1 : L - a ≤ 31 := by rw [L_eq]; omega
    generalize B ^ e.length = c at ih hpos ⊢
    rw [B_eq]
    have h2 : 32 * encLow e ≤ 32 * c - 32 := by
      have := Nat.mul_le_mul_left 32 ih
      rw [Nat.mul_sub, mul_one] at this
      exact this
    rw [mul_comm c 32]
    omega

theorem encLow_lt (e : List ℕ) : encLow e < B ^ e.length := by
  have := encLow_le e
  have := one_le_B_pow e.length
  omega

/-- The degree of the key of a list of length `n`. -/
theorem encK_div {n : ℕ} {e : List ℕ} (he : e.length = n) : encK n e / B ^ n = e.sum := by
  unfold encK
  have hlt : encLow e < B ^ n := he ▸ encLow_lt e
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (B_pos n), Nat.div_eq_of_lt hlt, zero_add]

/-- The digits of the low part. -/
theorem encLow_digit : ∀ (e : List ℕ) (i : ℕ), i < e.length → (∀ a ∈ e, a ≤ L) →
    encLow e / B ^ i % B = L - e.getD i 0
  | [], i, h, _ => by simp at h
  | a :: e, 0, _, hle => by
    simp only [encLow, pow_zero, Nat.div_one, List.getD_cons_zero]
    have ha : L - a < B := by rw [L_eq, B_eq]; omega
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  | a :: e, i + 1, h, hle => by
    simp only [List.length_cons] at h
    have ih := encLow_digit e i (by omega) (fun b hb => hle b (List.mem_cons_of_mem _ hb))
    simp only [encLow, List.getD_cons_succ]
    have ha : L - a < B := by rw [L_eq, B_eq]; omega
    rw [pow_succ, mul_comm (B ^ i) B, ← Nat.div_div_eq_div_mul]
    rw [show (L - a + B * encLow e) / B = encLow e by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < B), Nat.div_eq_of_lt ha, zero_add]]
    exact ih

/-- The digits of a key. -/
theorem encK_digit {n : ℕ} {e : List ℕ} (he : e.length = n) (hle : ∀ a ∈ e, a ≤ L) {i : ℕ} (hi : i < n) :
    encK n e / B ^ i % B = L - e.getD i 0 := by
  unfold encK
  obtain ⟨d, rfl⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  have hpow : B ^ (i + 1 + d) = B ^ i * (B * B ^ d) := by rw [pow_add, pow_succ]; ring
  rw [hpow, show e.sum * (B ^ i * (B * B ^ d)) + encLow e = encLow e + B ^ i * (e.sum * (B * B ^ d)) by ring,
    Nat.add_mul_div_left _ _ (B_pos i),
    show e.sum * (B * B ^ d) = B * (e.sum * B ^ d) by ring, Nat.add_mul_mod_self_left]
  exact encLow_digit e i (by omega) hle

theorem decK_length (n k : ℕ) : (decK n k).length = n := by simp [decK]

/-- **Decoding a key gives back the exponents.** -/
theorem decK_encK {n : ℕ} {e : List ℕ} (he : e.length = n) (hle : ∀ a ∈ e, a ≤ L) : decK n (encK n e) = e := by
  apply List.ext_getElem
  · simp [decK, he]
  · intro i h1 h2
    have hi : i < n := by simpa [decK] using h1
    simp only [decK, List.getElem_map, List.getElem_range, expK]
    rw [encK_digit he hle hi, lGetD_lt h2]
    have := hle _ (List.getElem_mem h2)
    omega

/-- A valid key is the key of its exponents, of degree at most `L`. -/
theorem validK_spec {n k : ℕ} (h : validK n k = true) : encK n (decK n k) = k ∧ (decK n k).sum ≤ L := by
  simp only [validK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨h.2, ?_⟩
  have := encK_div (decK_length n k)
  rw [h.2] at this
  rw [← this]
  exact h.1

theorem le_L_of_sum {e : List ℕ} (h : e.sum ≤ L) : ∀ a ∈ e, a ≤ L :=
  fun _ ha => (List.le_sum_of_mem ha).trans h

/-- Componentwise sums of lists. -/
theorem encLow_add : ∀ (e f : List ℕ), e.length = f.length → (∀ i, e.getD i 0 + f.getD i 0 ≤ L) →
    encLow e + encLow f = encLow (List.zipWith (· + ·) e f) + (B ^ e.length - 1)
  | [], [], _, _ => by simp [encLow]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: e, b :: f, h, hs => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have hab : a + b ≤ L := by simpa using hs 0
    have ih := encLow_add e f h (fun i => by simpa using hs (i + 1))
    have hpos := one_le_B_pow e.length
    simp only [encLow, List.zipWith_cons_cons, List.length_cons, pow_succ]
    generalize B ^ e.length = c at ih hpos ⊢
    generalize encLow (List.zipWith (· + ·) e f) = z at ih ⊢
    rw [B_eq]
    rw [L_eq] at hab ⊢
    rw [mul_comm c 32]
    have h32 : 32 * c - 1 = 31 + 32 * (c - 1) := by omega
    rw [h32]
    have e1 : 31 - a + 32 * encLow e + (31 - b + 32 * encLow f) =
        (31 - a + (31 - b)) + 32 * (encLow e + encLow f) := by ring
    rw [e1, ih]
    have e2 : 32 * (z + (c - 1)) = 32 * z + 32 * (c - 1) := by ring
    rw [e2]
    omega

theorem sum_zipWith_add : ∀ (e f : List ℕ), e.length = f.length →
    (List.zipWith (· + ·) e f).sum = e.sum + f.sum
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: e, b :: f, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zipWith_cons_cons, List.sum_cons, sum_zipWith_add e f h]
    ring

theorem length_zipWith_add {e f : List ℕ} (h : e.length = f.length) :
    (List.zipWith (· + ·) e f).length = e.length := by simp [h]

theorem getD_zipWith_add {e f : List ℕ} (h : e.length = f.length) (i : ℕ) :
    (List.zipWith (· + ·) e f).getD i 0 = e.getD i 0 + f.getD i 0 := by
  rcases lt_or_ge i e.length with hi | hi
  · rw [lGetD_lt (by rw [length_zipWith_add h]; exact hi), lGetD_lt hi, lGetD_lt (by omega)]
    simp
  · rw [lGetD_ge (by rw [length_zipWith_add h]; exact hi), lGetD_ge hi, lGetD_ge (by omega)]

/-- **Adding keys**: for valid keys whose degrees add up to at most `L`. -/
theorem shift_key {n k m : ℕ} (hk : validK n k = true) (hm : validK n m = true) (hd : k / B ^ n + m / B ^ n ≤ L) :
    validK n (k + m - (B ^ n - 1)) = true ∧
      decK n (k + m - (B ^ n - 1)) = List.zipWith (· + ·) (decK n k) (decK n m) := by
  obtain ⟨ek, -⟩ := validK_spec hk
  obtain ⟨em, -⟩ := validK_spec hm
  set e := decK n k with he
  set f := decK n m with hf
  have hel : e.length = n := decK_length n k
  have hfl : f.length = n := decK_length n m
  have hdk : k / B ^ n = e.sum := by rw [← ek]; exact encK_div hel
  have hdm : m / B ^ n = f.sum := by rw [← em]; exact encK_div hfl
  rw [hdk, hdm] at hd
  have hlen : e.length = f.length := by omega
  have hcomp : ∀ i, e.getD i 0 + f.getD i 0 ≤ L := by
    intro i
    rcases lt_or_ge i n with hi | hi
    · have h1 : e.getD i 0 ≤ e.sum := by
        rw [lGetD_lt (by omega)]; exact List.le_sum_of_mem (List.getElem_mem _)
      have h2 : f.getD i 0 ≤ f.sum := by
        rw [lGetD_lt (by omega)]; exact List.le_sum_of_mem (List.getElem_mem _)
      omega
    · rw [lGetD_ge (by omega), lGetD_ge (by omega)]
      simp [L]
  set g := List.zipWith (· + ·) e f with hg
  have hgl : g.length = n := by rw [hg, length_zipWith_add hlen, hel]
  have hsum : g.sum = e.sum + f.sum := sum_zipWith_add e f hlen
  have hgle : ∀ a ∈ g, a ≤ L := le_L_of_sum (by rw [hsum]; exact hd)
  have hkey : k + m - (B ^ n - 1) = encK n g := by
    rw [← ek, ← em]
    unfold encK
    have hadd := encLow_add e f hlen hcomp
    rw [hel, ← hg] at hadd
    rw [hsum, add_mul]
    have hpos := one_le_B_pow n
    generalize B ^ n = c at hadd hpos ⊢
    generalize e.sum * c = u1 at ⊢
    generalize f.sum * c = u2 at ⊢
    omega
  rw [hkey]
  refine ⟨?_, decK_encK hgl hgle⟩
  simp only [validK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨?_, by rw [decK_encK hgl hgle]⟩
  rw [encK_div hgl, hsum]
  exact hd

/-! ## Values -/

variable {p : ℕ} {R : Type*} [CommRing R] [Algebra (ZMod p) R] (x : ℕ → R) (n : ℕ)

/-- The monomial of a key. -/
noncomputable def monoK (k : ℕ) : R := Mono.eval x (decK n k) 0

/-- The coefficient map. -/
noncomputable abbrev cf (p : ℕ) (R : Type*) [CommRing R] [Algebra (ZMod p) R] (a : ℕ) : R :=
  algebraMap (ZMod p) R (a : ZMod p)

/-- The value of a key polynomial. -/
noncomputable def evalS (f : SPoly) : R :=
  ∑ t ∈ range f.keys.size, cf p R (f.coefs.getD t 0) * monoK x n (f.keys.getD t 0)

/-- The term of index `t` of a row (zero if its column is out of range). -/
noncomputable def rowTerm (cols : Array ℕ) (r : CRow) (t : ℕ) : R :=
  if r.idx.getD t 0 < cols.size then cf p R (r.coef.getD t 0) * monoK x n (cols.getD (r.idx.getD t 0) 0) else 0

/-- The value of a row of the matrix with column keys `cols`. -/
noncomputable def rowVal (cols : Array ℕ) (r : CRow) : R := ∑ t ∈ range r.idx.size, rowTerm (p := p) x n cols r t

/-- The value of a dense vector. -/
noncomputable def evalDense (cols acc : Array ℕ) : R :=
  ∑ j ∈ range acc.size, cf p R (acc.getD j 0) * monoK x n (cols.getD j 0)

/-- All keys valid. -/
def AllValid (f : SPoly) : Prop := ∀ t < f.keys.size, validK n (f.keys.getD t 0) = true

theorem monoK_shift {k m : ℕ} (hk : validK n k = true) (hm : validK n m = true)
    (hd : k / B ^ n + m / B ^ n ≤ L) : monoK x n (k + m - (B ^ n - 1)) = monoK x n k * monoK x n m := by
  unfold monoK
  rw [(shift_key hk hm hd).2]
  have hl : (decK n k).length = (decK n m).length := by simp [decK_length]
  have : List.zipWith (· + ·) (decK n k) (decK n m) = Mono.mul (decK n k) (decK n m) := by
    clear hk hm hd
    generalize decK n k = e at hl ⊢
    generalize decK n m = f at hl ⊢
    induction e generalizing f with
    | nil => cases f <;> simp_all [Mono.mul]
    | cons a e ih =>
      cases f with
      | nil => simp at hl
      | cons b f =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp [Mono.mul, ih f hl]
  rw [this, Mono.eval_mul]

/-! ## Coefficient arithmetic -/

theorem cf_mod (a : ℕ) : cf p R (a % p) = cf p R a := by simp [cf, ZMod.natCast_mod]

theorem cf_mul_mod (a c : ℕ) : cf p R (a * c % p) = cf p R a * cf p R c := by
  simp [cf, ZMod.natCast_mod]

theorem cf_add_mul (a c b : ℕ) : cf p R (a + c * b) = cf p R a + cf p R c * cf p R b := by
  simp [cf]

theorem cf_add_mod (a b : ℕ) : cf p R ((a + b % p) % p) = cf p R a + cf p R b := by
  simp [cf, ZMod.natCast_mod]

theorem cf_eq_zero_of_mod {a : ℕ} (h : a % p = 0) : cf p R a = 0 := by
  rw [← cf_mod, h]
  simp [cf]

/-! ## Polynomial operations -/

theorem evalS_zero : evalS (p := p) x n SPoly.zero = (0 : R) := by simp [evalS, SPoly.zero]

theorem allValid_zero : AllValid n SPoly.zero := by intro t ht; simp [SPoly.zero] at ht

theorem shiftS_sound {Bn m : ℕ} (hBn : Bn = B ^ n) {f : SPoly} (hv : AllValid n f)
    (h0 : evalS (p := p) x n f = (0 : R)) :
    AllValid n (shiftS n Bn m f) ∧ evalS (p := p) x n (shiftS n Bn m f) = (0 : R) := by
  unfold shiftS
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Array.all_eq_true] at hc
    obtain ⟨hm, hall⟩ := hc
    have hdeg : ∀ t < f.keys.size, f.keys.getD t 0 / B ^ n + m / B ^ n ≤ L := by
      intro t ht
      have := hall t ht
      rw [aGetD_lt ht, ← hBn]
      simpa using this
    have hval : ∀ t < f.keys.size, validK n (f.keys.getD t 0) = true := hv
    constructor
    · intro t ht
      simp only [Array.size_map] at ht
      rw [aGetD_map ht, hBn]
      exact (shift_key (hval t ht) hm (hdeg t ht)).1
    · unfold evalS at h0 ⊢
      simp only [Array.size_map]
      have : ∀ t ∈ range f.keys.size,
          cf p R (f.coefs.getD t 0) * monoK x n ((f.keys.map fun k => k + m - (Bn - 1)).getD t 0) =
            monoK x n m * (cf p R (f.coefs.getD t 0) * monoK x n (f.keys.getD t 0)) := by
        intro t ht
        rw [mem_range] at ht
        rw [aGetD_map ht, hBn, monoK_shift x n (hval t ht) hm (hdeg t ht)]
        ring
      rw [sum_congr rfl this, ← mul_sum, h0, mul_zero]
  · exact ⟨allValid_zero n, evalS_zero x n⟩

theorem coefs_map_getD (a : Array ℕ) (c t : ℕ) :
    cf p R ((a.map fun b => b * c % p).getD t 0) = cf p R (a.getD t 0) * cf p R c := by
  rcases lt_or_ge t a.size with ht | ht
  · rw [aGetD_map ht, cf_mul_mod]
  · rw [aGetD_ge (by simpa using ht), aGetD_ge ht]
    simp [cf]

theorem scaleS_sound {c : ℕ} {f : SPoly} (hv : AllValid n f) (h0 : evalS (p := p) x n f = (0 : R)) :
    AllValid n (scaleS p c f) ∧ evalS (p := p) x n (scaleS p c f) = (0 : R) := by
  refine ⟨hv, ?_⟩
  unfold evalS at h0 ⊢
  simp only [scaleS]
  have : ∀ t ∈ range f.keys.size,
      cf p R ((f.coefs.map fun a => a * c % p).getD t 0) * monoK x n (f.keys.getD t 0) =
        cf p R c * (cf p R (f.coefs.getD t 0) * monoK x n (f.keys.getD t 0)) := by
    intro t _
    rw [coefs_map_getD]
    ring
  rw [sum_congr rfl this, ← mul_sum, h0, mul_zero]

/-! ## Rows -/

theorem rowVal_zero (cols : Array ℕ) : rowVal (p := p) x n cols CRow.zero = (0 : R) := by
  simp [rowVal, CRow.zero]

theorem evalS_push (ks cs : Array ℕ) (hs : ks.size = cs.size) (a b : ℕ) :
    evalS (p := p) x n ⟨ks.push a, cs.push b⟩ = evalS (p := p) x n ⟨ks, cs⟩ + cf p R b * monoK x n a := by
  unfold evalS
  simp only [Array.size_push]
  rw [sum_range_succ]
  congr 1
  · refine sum_congr rfl fun t ht => ?_
    rw [mem_range] at ht
    rw [getD_push_lt ht, getD_push_lt (show t < cs.size by omega)]
  · rw [getD_push_eq, hs, getD_push_eq]

theorem decodeCAux_val (cols : Array ℕ) (r : CRow) :
    ∀ (k : ℕ) (ks cs : Array ℕ), ks.size = cs.size →
      evalS (p := p) x n (decodeCAux cols r k ks cs) =
        evalS (p := p) x n ⟨ks, cs⟩ + ∑ t ∈ Ico k r.idx.size, rowTerm (p := p) x n cols r t := by
  intro k
  induction h : r.idx.size - k generalizing k with
  | zero =>
    intro ks cs _
    unfold decodeCAux
    rw [dite_eq_right (by omega), Ico_eq_empty_of_le (by omega), sum_empty, add_zero]
  | succ d ih =>
    intro ks cs hs
    have hk : k < r.idx.size := by omega
    unfold decodeCAux
    rw [dite_eq_left hk, sum_eq_sum_Ico_succ_bot hk]
    simp only
    by_cases hj : r.idx[k] < cols.size
    · rw [dite_eq_left hj, ih (k + 1) (by omega) _ _ (by simp [hs]), evalS_push x n ks cs hs]
      have ht : rowTerm (p := p) x n cols r k = cf p R (r.coef.getD k 0) * monoK x n cols[r.idx[k]] := by
        unfold rowTerm
        rw [aGetD_lt hk, ite_eq_left hj, aGetD_lt hj]
      rw [ht]
      ring
    · rw [dite_eq_right hj, ih (k + 1) (by omega) _ _ hs]
      have ht : rowTerm (p := p) x n cols r k = 0 := by
        unfold rowTerm
        rw [aGetD_lt hk, ite_eq_right hj]
      rw [ht, zero_add]

/-- **The value of the polynomial of a row.** -/
theorem evalS_decodeC (cols : Array ℕ) (r : CRow) :
    evalS (p := p) x n (decodeC cols r) = rowVal (p := p) x n cols r := by
  unfold decodeC rowVal
  rw [decodeCAux_val x n cols r 0 #[] #[] rfl, range_eq_Ico]
  simp [evalS]

theorem decodeV_sound (cols : Array ℕ) (r : CRow) (h0 : rowVal (p := p) x n cols r = (0 : R)) :
    AllValid n (decodeV n cols r) ∧ evalS (p := p) x n (decodeV n cols r) = (0 : R) := by
  unfold decodeV
  dsimp only
  split
  · rename_i hc
    rw [Array.all_eq_true] at hc
    refine ⟨fun t ht => ?_, by rw [evalS_decodeC]; exact h0⟩
    rw [aGetD_lt ht]
    exact hc t ht
  · exact ⟨allValid_zero n, evalS_zero x n⟩

theorem colsMatch_spec (cols idx keys : Array ℕ) :
    ∀ k, colsMatch cols idx keys k = true → ∀ t, k ≤ t → t < idx.size → cols[idx[t]!]? = keys[t]? := by
  intro k
  induction h : idx.size - k generalizing k with
  | zero =>
    intro _ t hkt ht
    omega
  | succ d ih =>
    intro hm t hkt ht
    unfold colsMatch at hm
    have hk : k < idx.size := by omega
    rw [dite_eq_left hk] at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    rcases Nat.eq_or_lt_of_le hkt with heq | hlt
    · subst heq
      rw [getElem!_pos idx k ht]
      exact hm.1
    · exact ih (k + 1) (by omega) hm.2 t hlt ht

/-- **A polynomial as a row**: all or nothing. -/
theorem rowVal_toColImpl (cols : Array ℕ) (look : ℕ → ℕ) (f : SPoly) :
    rowVal (p := p) x n cols (toColImpl cols look f) = evalS (p := p) x n f ∨
      rowVal (p := p) x n cols (toColImpl cols look f) = (0 : R) := by
  unfold toColImpl
  dsimp only
  split
  · rename_i hc
    left
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hsz, hm⟩ := hc
    have hspec := colsMatch_spec cols (f.keys.map look) f.keys 0 hm
    unfold rowVal evalS
    simp only [Array.size_map]
    refine sum_congr rfl fun t ht => ?_
    rw [mem_range] at ht
    have hmt := hspec t (Nat.zero_le _) (by simpa using ht)
    rw [getElem!_pos _ t (by simpa using ht)] at hmt
    rw [Array.getElem?_eq_getElem ht] at hmt
    have hin : (f.keys.map look)[t]'(by simpa using ht) < cols.size := by
      by_contra hno
      rw [Array.getElem?_eq_none (by omega)] at hmt
      simp at hmt
    have hcol : cols[(f.keys.map look)[t]'(by simpa using ht)] = f.keys[t] := by
      rw [Array.getElem?_eq_getElem hin] at hmt
      simpa using hmt
    unfold rowTerm
    simp only
    rw [aGetD_lt (by simpa using ht), ite_eq_left hin, aGetD_lt hin, hcol, aGetD_lt ht]
  · right
    exact rowVal_zero x n cols

theorem scaleR_val (cols : Array ℕ) (c : ℕ) (r : CRow) :
    rowVal (p := p) x n cols (scaleR p c r) = cf p R c * rowVal (p := p) x n cols r := by
  unfold rowVal
  rw [mul_sum]
  refine sum_congr rfl fun t _ => ?_
  unfold rowTerm scaleR
  simp only
  split
  · rw [coefs_map_getD]; ring
  · ring

/-! ## Dense vectors -/

theorem evalDense_set (cols acc : Array ℕ) (j v : ℕ) (hj : j < acc.size) :
    evalDense (p := p) x n cols (acc.set j v hj) =
      evalDense (p := p) x n cols acc + (cf p R v - cf p R acc[j]) * monoK x n (cols.getD j 0) := by
  unfold evalDense
  simp only [Array.size_set]
  have hmem : j ∈ range acc.size := mem_range.mpr hj
  rw [← add_sum_erase _ _ hmem, ← add_sum_erase _ _ hmem]
  have hrest : ∑ i ∈ (range acc.size).erase j, cf p R ((acc.set j v hj).getD i 0) * monoK x n (cols.getD i 0) =
      ∑ i ∈ (range acc.size).erase j, cf p R (acc.getD i 0) * monoK x n (cols.getD i 0) := by
    refine sum_congr rfl fun i hi => ?_
    rw [mem_erase] at hi
    rw [getD_set_ne hj hi.1]
  rw [hrest, getD_set_eq hj, aGetD_lt hj]
  ring

theorem addMulAux_size (c : ℕ) (idx coef : Array ℕ) :
    ∀ k (acc : Array ℕ), (addMulAux c idx coef k acc).size = acc.size := by
  intro k
  induction h : idx.size - k generalizing k with
  | zero =>
    intro acc
    unfold addMulAux
    rw [dite_eq_right (by omega)]
  | succ d ih =>
    intro acc
    unfold addMulAux
    rw [dite_eq_left (by omega)]
    dsimp only
    rw [ih (k + 1) (by omega)]
    split <;> simp

/-- **One addition** of a multiple of a row to the dense vector. -/
theorem evalDense_addMulAux (cols : Array ℕ) (c : ℕ) (idx coef : Array ℕ) :
    ∀ k (acc : Array ℕ),
      evalDense (p := p) x n cols (addMulAux c idx coef k acc) = evalDense (p := p) x n cols acc +
        cf p R c * ∑ t ∈ Ico k idx.size, (if idx.getD t 0 < acc.size then
          cf p R (coef.getD t 0) * monoK x n (cols.getD (idx.getD t 0) 0) else (0 : R)) := by
  intro k
  induction h : idx.size - k generalizing k with
  | zero =>
    intro acc
    unfold addMulAux
    rw [dite_eq_right (by omega), Ico_eq_empty_of_le (by omega), sum_empty, mul_zero, add_zero]
  | succ d ih =>
    intro acc
    have hk : k < idx.size := by omega
    unfold addMulAux
    rw [dite_eq_left hk, sum_eq_sum_Ico_succ_bot hk, aGetD_lt hk]
    simp only
    by_cases hj : idx[k] < acc.size
    · rw [dite_eq_left hj, ih (k + 1) (by omega), Array.size_set, evalDense_set x n cols acc _ _ hj, cf_add_mul,
        ite_eq_left hj]
      ring
    · rw [dite_eq_right hj, ih (k + 1) (by omega), ite_eq_right hj]
      ring

theorem addRowAux_size (p : ℕ) (idx coef : Array ℕ) :
    ∀ k (acc : Array ℕ), (addRowAux p idx coef k acc).size = acc.size := by
  intro k
  induction h : idx.size - k generalizing k with
  | zero =>
    intro acc
    unfold addRowAux
    rw [dite_eq_right (by omega)]
  | succ d ih =>
    intro acc
    unfold addRowAux
    rw [dite_eq_left (by omega)]
    dsimp only
    rw [ih (k + 1) (by omega)]
    split <;> simp

theorem evalDense_addRowAux (cols : Array ℕ) (idx coef : Array ℕ) :
    ∀ k (acc : Array ℕ),
      evalDense (p := p) x n cols (addRowAux p idx coef k acc) = evalDense (p := p) x n cols acc +
        ∑ t ∈ Ico k idx.size, (if idx.getD t 0 < acc.size then
          cf p R (coef.getD t 0) * monoK x n (cols.getD (idx.getD t 0) 0) else (0 : R)) := by
  intro k
  induction h : idx.size - k generalizing k with
  | zero =>
    intro acc
    unfold addRowAux
    rw [dite_eq_right (by omega), Ico_eq_empty_of_le (by omega), sum_empty, add_zero]
  | succ d ih =>
    intro acc
    have hk : k < idx.size := by omega
    unfold addRowAux
    rw [dite_eq_left hk, sum_eq_sum_Ico_succ_bot hk, aGetD_lt hk]
    simp only
    by_cases hj : idx[k] < acc.size
    · rw [dite_eq_left hj, ih (k + 1) (by omega), Array.size_set, evalDense_set x n cols acc _ _ hj, cf_add_mod,
        ite_eq_left hj]
      ring
    · rw [dite_eq_right hj, ih (k + 1) (by omega), ite_eq_right hj]
      ring

theorem evalDense_replicate (cols : Array ℕ) (m : ℕ) :
    evalDense (p := p) x n cols (Array.replicate m 0) = (0 : R) := by
  unfold evalDense
  refine sum_eq_zero fun j hj => ?_
  rw [mem_range, Array.size_replicate] at hj
  rw [aGetD_lt (by simpa using hj)]
  simp [cf]

theorem rowVal_eq_sum (cols : Array ℕ) (r : CRow) :
    rowVal (p := p) x n cols r = ∑ t ∈ Ico 0 r.idx.size, (if r.idx.getD t 0 < cols.size then
      cf p R (r.coef.getD t 0) * monoK x n (cols.getD (r.idx.getD t 0) 0) else (0 : R)) := by
  rw [← range_eq_Ico]
  rfl

theorem evalDense_toDense (cols : Array ℕ) (r : CRow) :
    evalDense (p := p) x n cols (toDense p cols.size r) = rowVal (p := p) x n cols r := by
  unfold toDense
  rw [evalDense_addRowAux, evalDense_replicate, zero_add, Array.size_replicate, rowVal_eq_sum]

theorem reduceDenseAux_size (p : ℕ) (pivs : Array (Option CRow)) (ncols : ℕ) :
    ∀ j (acc : Array ℕ), (reduceDenseAux p pivs ncols j acc).size = acc.size := by
  intro j
  induction h : ncols - j generalizing j with
  | zero =>
    intro acc
    unfold reduceDenseAux
    rw [ite_eq_right (by omega)]
  | succ d ih =>
    intro acc
    unfold reduceDenseAux
    rw [ite_eq_left (by omega)]
    dsimp only
    split
    · exact ih (j + 1) (by omega) acc
    · split
      · rw [ih (j + 1) (by omega), addMulAux_size]
      · exact ih (j + 1) (by omega) acc

/-- **The dense reduction** does not change the value when the pivot rows vanish. -/
theorem evalDense_reduceDenseAux (cols : Array ℕ) (pivs : Array (Option CRow))
    (hpiv : ∀ (j : ℕ) (q : CRow), pivs[j]? = some (some q) → rowVal (p := p) x n cols q = (0 : R)) (ncols : ℕ) :
    ∀ j (acc : Array ℕ), acc.size = cols.size →
      evalDense (p := p) x n cols (reduceDenseAux p pivs ncols j acc) = evalDense (p := p) x n cols acc := by
  intro j
  induction h : ncols - j generalizing j with
  | zero =>
    intro acc _
    unfold reduceDenseAux
    rw [ite_eq_right (by omega)]
  | succ d ih =>
    intro acc hacc
    unfold reduceDenseAux
    rw [ite_eq_left (by omega)]
    dsimp only
    split
    · exact ih (j + 1) (by omega) acc hacc
    · split
      · rename_i q hq
        rw [ih (j + 1) (by omega) _ (by rw [addMulAux_size]; exact hacc), evalDense_addMulAux]
        have : ∑ t ∈ Ico 0 q.idx.size, (if q.idx.getD t 0 < acc.size then
            cf p R (q.coef.getD t 0) * monoK x n (cols.getD (q.idx.getD t 0) 0) else (0 : R)) =
            rowVal (p := p) x n cols q := by
          rw [rowVal_eq_sum, hacc]
        rw [this, hpiv j q hq, mul_zero, add_zero]
      · exact ih (j + 1) (by omega) acc hacc

theorem toSparseAux_val (cols acc : Array ℕ) (hacc : acc.size = cols.size) :
    ∀ j (is cs : Array ℕ), is.size = cs.size → (∀ t < is.size, is[t]! < cols.size) →
      rowVal (p := p) x n cols (toSparseAux p acc j is cs) = rowVal (p := p) x n cols ⟨is, cs⟩ +
        ∑ i ∈ Ico j acc.size, cf p R (acc.getD i 0) * monoK x n (cols.getD i 0) := by
  intro j
  induction h : acc.size - j generalizing j with
  | zero =>
    intro is cs _ _
    unfold toSparseAux
    rw [dite_eq_right (by omega), Ico_eq_empty_of_le (by omega), sum_empty, add_zero]
  | succ d ih =>
    intro is cs hs hin
    have hj : j < acc.size := by omega
    unfold toSparseAux
    rw [dite_eq_left hj]
    dsimp only
    rw [sum_eq_sum_Ico_succ_bot hj, aGetD_lt hj]
    split
    · rename_i hz
      have hz' : acc[j] % p = 0 := by
        rcases (by simpa using hz : acc[j] = 0 ∨ acc[j] % p = 0) with h0 | h0
        · rw [h0, Nat.zero_mod]
        · exact h0
      rw [ih (j + 1) (by omega) is cs hs hin, cf_eq_zero_of_mod hz', zero_mul, zero_add]
    · rename_i hz
      have hin' : ∀ t < (is.push j).size, (is.push j)[t]! < cols.size := by
        intro t ht
        simp only [Array.size_push] at ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
        · rw [getElem!_pos _ t (by simp; omega), Array.getElem_push_lt ht]
          have := hin t ht
          rwa [getElem!_pos _ t ht] at this
        · rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]
          omega
      rw [ih (j + 1) (by omega) _ _ (by simp [hs]) hin']
      have hpush : rowVal (p := p) x n cols ⟨is.push j, cs.push (acc[j] % p)⟩ =
          rowVal (p := p) x n cols ⟨is, cs⟩ + cf p R (acc[j] % p) * monoK x n (cols.getD j 0) := by
        unfold rowVal
        simp only [Array.size_push]
        rw [sum_range_succ]
        congr 1
        · refine sum_congr rfl fun t ht => ?_
          rw [mem_range] at ht
          unfold rowTerm
          simp only
          rw [getD_push_lt ht, getD_push_lt (show t < cs.size by omega)]
        · unfold rowTerm
          simp only
          rw [getD_push_eq, hs, getD_push_eq, ite_eq_left (by omega)]
      rw [hpush, cf_mod]
      ring

/-- **The value of a reduced row** equals that of the row, when the pivot rows vanish. -/
theorem rowVal_reduceC (cols : Array ℕ) (pivs : Array (Option CRow))
    (hpiv : ∀ (j : ℕ) (q : CRow), pivs[j]? = some (some q) → rowVal (p := p) x n cols q = (0 : R))
    (start : ℕ) (r : CRow) :
    rowVal (p := p) x n cols (reduceC p cols.size pivs start r) = rowVal (p := p) x n cols r := by
  unfold reduceC
  have hsz : (reduceDenseAux p pivs cols.size start (toDense p cols.size r)).size = cols.size := by
    rw [reduceDenseAux_size]
    unfold toDense
    rw [addRowAux_size, Array.size_replicate]
  rw [toSparseAux_val x n cols _ hsz 0 #[] #[] rfl (by intro t ht; simp at ht)]
  rw [show rowVal (p := p) x n cols ⟨#[], #[]⟩ = (0 : R) by simp [rowVal], zero_add, ← range_eq_Ico]
  show evalDense (p := p) x n cols (reduceDenseAux p pivs cols.size start (toDense p cols.size r)) = _
  rw [evalDense_reduceDenseAux x n cols pivs hpiv cols.size start (toDense p cols.size r)
    (by unfold toDense; rw [addRowAux_size, Array.size_replicate]), evalDense_toDense]

/-! ## The predicate -/

/-- What a derivable object satisfies. -/
def Sem (o : Obj) : Prop :=
  match o with
  | .abs f => AllValid n f ∧ evalS (p := p) x n f = (0 : R)
  | .row cols r => rowVal (p := p) x n cols r = (0 : R)

/-- **Every derivable object vanishes** at a common zero of the inputs. -/
theorem good_sound {Bn : ℕ} {F : List SPoly} (hBn : Bn = B ^ n)
    (hF : ∀ f ∈ F, AllValid n f ∧ evalS (p := p) x n f = (0 : R)) {o : Obj} (h : Good n Bn p F o) :
    Sem (p := p) x n o := by
  induction h with
  | zero => exact ⟨allValid_zero n, evalS_zero x n⟩
  | input hf => exact hF _ hf
  | shift m _ ih => exact shiftS_sound x n hBn ih.1 ih.2
  | scaleA c _ ih => exact scaleS_sound x n ih.1 ih.2
  | ofRow _ ih => exact decodeV_sound x n _ _ ih
  | ofAbs cols look _ ih =>
    show rowVal (p := p) x n cols (toColImpl cols look _) = 0
    rcases rowVal_toColImpl (p := p) x n cols look _ with h | h
    · rw [h]; exact ih.2
    · exact h
  | reduce pivs start _ _ ihp ihr =>
    show rowVal (p := p) x n _ (reduceC p _ pivs start _) = 0
    rw [rowVal_reduceC x n _ pivs (fun (j : ℕ) (q : CRow) hq => ihp j q hq) start]
    exact ihr
  | scaleR c _ ih =>
    show rowVal (p := p) x n _ (scaleR p c _) = 0
    rw [scaleR_val, show rowVal (p := p) x n _ _ = (0 : R) from ih, mul_zero]

/-! ## Inputs and outputs -/

theorem mono_eval_pad : ∀ (m0 : ℕ) (m : Mono) (i : ℕ), (m.drop m0).all (· == 0) = true →
    Mono.eval x ((List.range m0).map (fun j => m.getD j 0)) i = Mono.eval x m i
  | 0, m, i, h => by
    simp only [List.drop_zero] at h
    simp [Mono.eval, mono_eval_zeros x m i h]
  | m0 + 1, [], i, _ => by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.getD_nil, List.map_map, Mono.eval, pow_zero, one_mul]
    have := mono_eval_pad m0 [] (i + 1) (by simp)
    simp only [Function.comp_def, List.getD_nil] at this ⊢
    rw [this]
    rfl
  | m0 + 1, a :: m, i, h => by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.getD_cons_zero, List.map_map, Mono.eval]
    have hcomp : ((fun j => (a :: m).getD j 0) ∘ Nat.succ) = fun j => m.getD j 0 := by
      funext j; simp
    rw [hcomp]
    simp only [List.drop_succ_cons] at h
    rw [mono_eval_pad m0 m (i + 1) h]

theorem monoK_monoKey {m : Mono} (hv : validK n (monoKey n m) = true) (hd : (m.drop n).all (· == 0) = true) :
    monoK x n (monoKey n m) = Mono.eval x m 0 := by
  unfold monoK monoKey at *
  set e := (List.range n).map (fun i => m.getD i 0) with he
  have hel : e.length = n := by simp [he]
  have hsum : e.sum ≤ L := by
    simp only [validK, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [← encK_div hel]
    exact hv.1
  rw [decK_encK hel (le_L_of_sum hsum), he, mono_eval_pad x n m 0 hd]

theorem evalS_ofList (ts : List (ℕ × ℕ)) :
    evalS (p := p) x n ⟨(ts.map Prod.fst).toArray, (ts.map Prod.snd).toArray⟩ =
      (ts.map fun q => cf p R q.2 * monoK x n q.1).sum := by
  unfold evalS
  simp only [List.size_toArray, List.length_map]
  rw [← list_sum_range]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getElem_map, List.getElem_range, h1]

/-- **The encoding of an input** has the value of the input (or is `0`). -/
theorem encodeInput_sound [NeZero p] (f : Poly ℕ) :
    AllValid n (encodeInput n p f) ∧ (evalS (p := p) x n (encodeInput n p f) =
      Poly.eval (algH p R) x f ∨ evalS (p := p) x n (encodeInput n p f) = (0 : R)) := by
  unfold encodeInput
  dsimp only
  split
  · rename_i hok
    rw [List.all_eq_true] at hok
    set g := Poly.normalize (modC p) f
    set ts := (g.map (fun t => (monoKey n t.2, t.1 % p))).mergeSort (fun a b => decide (b.1 ≤ a.1))
    have hperm : ts.Perm (g.map (fun t => (monoKey n t.2, t.1 % p))) := List.mergeSort_perm _ _
    constructor
    · intro t ht
      simp only [List.size_toArray, List.length_map] at ht
      rw [aGetD_lt (by simpa using ht)]
      simp only [List.getElem_toArray, List.getElem_map]
      have hmem : ts[t] ∈ g.map (fun t => (monoKey n t.2, t.1 % p)) := hperm.subset (List.getElem_mem _)
      obtain ⟨u, hu, hut⟩ := List.mem_map.mp hmem
      rw [← hut]
      have := hok u hu
      simp only [Bool.and_eq_true] at this
      exact this.1
    · left
      rw [evalS_ofList]
      rw [(hperm.map _).sum_eq]
      rw [← Poly.eval_normalize (algH p R) x f]
      show _ = Poly.eval (algH p R) x g
      unfold Poly.eval
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      have := hok u hu
      simp only [Bool.and_eq_true] at this
      simp only [Function.comp_apply]
      rw [cf_mod, monoK_monoKey x n this.1 this.2, algH_f]
  · exact ⟨allValid_zero n, Or.inr (evalS_zero x n)⟩

theorem eval_toPolyS [NeZero p] (f : SPoly) : Poly.eval (algH p R) x (toPolyS n f) = evalS (p := p) x n f := by
  unfold toPolyS Poly.eval evalS
  rw [List.map_map, ← list_sum_range]
  rfl

/-- **Soundness of the F4 engine**: every polynomial of the output basis vanishes at every common zero of the inputs,
in every commutative `ZMod p`-algebra. -/
theorem f4_good (c : Cfg) [NeZero c.p] (F : List (Poly ℕ)) (R : Type*) [CommRing R] [Algebra (ZMod c.p) R]
    (x : ℕ → R) (hF : ∀ f ∈ F, Poly.eval (algH c.p R) x f = 0) :
    ∀ g ∈ f4Basis c F, Poly.eval (algH c.p R) x g = 0 := by
  intro g hg
  unfold f4Basis at hg
  simp only [List.mem_map, List.mem_filter, List.mem_range] at hg
  obtain ⟨i, -, rfl⟩ := hg
  have hin : ∀ f ∈ encInputs c F, AllValid c.n f ∧ evalS (p := c.p) x c.n f = (0 : R) := by
    intro f hf
    unfold encInputs at hf
    obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hf
    obtain ⟨hv, he⟩ := encodeInput_sound (p := c.p) x c.n f0
    refine ⟨hv, ?_⟩
    rcases he with he | he
    · rw [he]; exact hF f0 hf0
    · exact he
  have hsem := good_sound (p := c.p) x c.n (Bn := c.Bn) rfl hin ((f4State c F).basis.getD i default).2
  rw [eval_toPolyS]
  exact hsem.2

end Lean6.Special.D88.Count
