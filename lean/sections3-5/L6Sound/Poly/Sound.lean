import Mathlib
import L6Poly.Basic

/-!
# Soundness of the cofactor certificates (Lemma 5.2)

A packed polynomial `p : L6.Poly.Poly` (module `L6Poly.Basic`) is read in a commutative ring `R` at an assignment
`φ : ℕ → R` of the variables (variables `0, …, 5` are the masses, variable `6 + j` is the unknown `x_j`) through
`eval nv φ p = Σ c · Π_{i<nv} φ(i)^(exponent of i)`.

* `eval_normalize`: normalization does not change the value (it permutes the terms and adds equal keys);
* `eval_mulRaw`: the termwise product is the product of the values, when every exponent of both factors is `< 128`
  (`keyBounded`), so that adding keys adds exponents;
* **`checkParsed_sound`**: if a parsed certificate passes `checkParsed`, then in every commutative ring and at every
  assignment at which all generators vanish, `h` vanishes; `h` involves only the masses; and `h` is nonzero at the
  point `hPoint F` (so it is a nonzero polynomial);
* **`checkCert_sound`**: the same for the text of a certificate.

With the generators the initial forms of a core (with `m_F = 1` if `F ≥ 0`), this is the certificate of Lemma 5.2:
a nonzero `h(m)` that vanishes wherever the core has a common zero.
-/

namespace L6.Poly

open Finset

/-! ## No carry between bytes (as in the five-body development) -/

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

theorem smallKey_of_keyBounded {nv k : ℕ} (h : keyBounded nv k = true) : SmallKey nv k := by
  unfold keyBounded at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact h.2

/-! ## Evaluation -/

section Eval

variable {R : Type*} [CommRing R]

/-- The monomial of a key at an assignment. -/
def monoEval (nv : ℕ) (φ : ℕ → R) (k : ℕ) : R := ∏ i ∈ range nv, φ i ^ keyExp k i

/-- The value of a packed polynomial at an assignment. -/
def eval (nv : ℕ) (φ : ℕ → R) (p : Poly) : R := (p.map fun t => (t.2 : R) * monoEval nv φ t.1).sum

@[simp] theorem eval_nil (nv : ℕ) (φ : ℕ → R) : eval nv φ [] = 0 := rfl

theorem eval_cons (nv : ℕ) (φ : ℕ → R) (t : ℕ × ℤ) (p : Poly) :
    eval nv φ (t :: p) = (t.2 : R) * monoEval nv φ t.1 + eval nv φ p := by
  simp [eval]

theorem eval_append (nv : ℕ) (φ : ℕ → R) (p q : Poly) : eval nv φ (p ++ q) = eval nv φ p + eval nv φ q := by
  simp [eval, List.sum_append]

theorem eval_perm (nv : ℕ) (φ : ℕ → R) {p q : Poly} (h : p.Perm q) : eval nv φ p = eval nv φ q :=
  (h.map _).sum_eq

theorem eval_reverse (nv : ℕ) (φ : ℕ → R) (p : Poly) : eval nv φ p.reverse = eval nv φ p :=
  eval_perm nv φ (List.reverse_perm p)

theorem eval_neg (nv : ℕ) (φ : ℕ → R) (p : Poly) : eval nv φ (neg p) = - eval nv φ p := by
  unfold neg
  induction p with
  | nil => simp
  | cons t p ih => rw [List.map_cons, eval_cons, eval_cons, ih]; push_cast; ring

theorem eval_flatten (nv : ℕ) (φ : ℕ → R) (ls : List Poly) :
    eval nv φ ls.flatten = (ls.map (eval nv φ)).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => rw [List.flatten_cons, eval_append, ih, List.map_cons, List.sum_cons]

/-- `combineRev` keeps the value: the accumulator in reverse, plus the pending term, plus the rest. -/
theorem eval_combineRev (nv : ℕ) (φ : ℕ → R) :
    ∀ (rest : Poly) (k : ℕ) (c : ℤ) (acc : Poly),
      eval nv φ (combineRev k c acc rest) = eval nv φ acc + (c : R) * monoEval nv φ k + eval nv φ rest
  | [], k, c, acc => by
    unfold combineRev
    split_ifs with hc
    · subst hc; simp
    · rw [eval_cons, eval_nil]; ring
  | u :: rest, k, c, acc => by
    unfold combineRev
    split_ifs with hk hc
    · rw [eval_combineRev nv φ rest k (c + u.2) acc, eval_cons, ← hk]; push_cast; ring
    · subst hc
      rw [eval_combineRev nv φ rest u.1 u.2 acc, eval_cons]; push_cast; ring
    · rw [eval_combineRev nv φ rest u.1 u.2 ((k, c) :: acc), eval_cons, eval_cons]; ring

theorem eval_combineSorted (nv : ℕ) (φ : ℕ → R) (p : Poly) : eval nv φ (combineSorted p) = eval nv φ p := by
  cases p with
  | nil => rfl
  | cons t rest =>
    unfold combineSorted
    rw [eval_reverse, eval_combineRev, eval_cons]; simp

/-- **Normalization keeps the value.** -/
theorem eval_normalize (nv : ℕ) (φ : ℕ → R) (p : Poly) : eval nv φ (normalize p) = eval nv φ p := by
  unfold normalize
  rw [eval_combineSorted]
  exact eval_perm nv φ (List.mergeSort_perm _ _)

theorem monoEval_add (nv : ℕ) (φ : ℕ → R) {a b : ℕ} (ha : SmallKey nv a) (hb : SmallKey nv b) :
    monoEval nv φ (a + b) = monoEval nv φ a * monoEval nv φ b := by
  unfold monoEval
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [keyExp_add a b i (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega)), pow_add]

/-- **The termwise product is the product**, for keys with small exponents. -/
theorem eval_mulRaw (nv : ℕ) (φ : ℕ → R) {p q : Poly} (hp : ∀ t ∈ p, SmallKey nv t.1)
    (hq : ∀ t ∈ q, SmallKey nv t.1) : eval nv φ (mulRaw p q) = eval nv φ p * eval nv φ q := by
  unfold mulRaw
  induction p with
  | nil => simp [eval]
  | cons a p ih =>
    rw [List.flatMap_cons, eval_append, ih (fun t ht => hp t (by simp [ht])), eval_cons, add_mul]
    congr 1
    have ha := hp a (by simp)
    clear ih
    induction q with
    | nil => simp [eval]
    | cons b q ihq =>
      rw [List.map_cons, eval_cons, eval_cons, ihq (fun t ht => hq t (by simp [ht])),
        monoEval_add nv φ ha (hq b (by simp))]
      push_cast; ring

/-- The value of `Σ cofᵢ · genᵢ` (termwise products, flattened). -/
theorem eval_combination (nv : ℕ) (φ : ℕ → R) :
    ∀ (cofs gens : List Poly), (∀ p ∈ cofs ++ gens, ∀ t ∈ p, SmallKey nv t.1) →
      eval nv φ (List.zipWith mulRaw cofs gens).flatten =
        (List.zipWith (fun c g => eval nv φ c * eval nv φ g) cofs gens).sum
  | [], _, _ => by simp [eval]
  | _ :: _, [], _ => by simp [eval]
  | c :: cofs, g :: gens, h => by
    rw [List.zipWith_cons_cons, List.flatten_cons, eval_append,
      eval_mulRaw nv φ (h c (by simp)) (h g (by simp)),
      eval_combination nv φ cofs gens (fun p hp => h p (by
        rcases List.mem_append.mp hp with hp | hp <;> simp [hp])),
      List.zipWith_cons_cons, List.sum_cons]

/-- The sum is zero when every generator vanishes. -/
theorem sum_zipWith_eq_zero (cofs gens : List R) (hg : ∀ g ∈ gens, g = 0) :
    (List.zipWith (fun c g => c * g) cofs gens).sum = 0 := by
  induction cofs generalizing gens with
  | nil => simp
  | cons c cofs ih =>
    cases gens with
    | nil => simp
    | cons g gens =>
      rw [List.zipWith_cons_cons, List.sum_cons, hg g (by simp),
        ih gens (fun x hx => hg x (by simp [hx]))]
      simp

end Eval

/-! ## The integer evaluation of the checker -/

theorem prod_range_list (f : ℕ → ℤ) : ∀ n, ∏ i ∈ range n, f i = ((List.range n).map f).prod
  | 0 => by simp
  | n + 1 => by
    rw [prod_range_succ, List.range_succ, List.map_append, List.prod_append, prod_range_list f n]; simp

theorem foldl_mul_pow (pt : Array ℤ) (k : ℕ) :
    ∀ (L : List ℕ) (m : ℤ), L.foldl (fun m i => m * pt.getD i 0 ^ keyExp k i) m =
      m * (L.map fun i => pt.getD i 0 ^ keyExp k i).prod
  | [], m => by simp
  | i :: L, m => by
    rw [List.foldl_cons, foldl_mul_pow pt k L, List.map_cons, List.prod_cons]; ring

theorem foldl_eval (nv : ℕ) (pt : Array ℤ) :
    ∀ (p : Poly) (acc : ℤ), p.foldl (fun acc t => acc + t.2 * (List.range nv).foldl
        (fun m i => m * pt.getD i 0 ^ keyExp t.1 i) 1) acc =
      acc + eval nv (fun i => pt.getD i 0) p
  | [], acc => by simp
  | t :: p, acc => by
    rw [List.foldl_cons, foldl_eval nv pt p, eval_cons, foldl_mul_pow, one_mul]
    unfold monoEval
    rw [prod_range_list]
    push_cast; ring

/-- `evalAt` is the value at the integer point. -/
theorem evalAt_eq (nv : ℕ) (pt : Array ℤ) (p : Poly) : evalAt nv pt p = eval nv (fun i => pt.getD i 0) p := by
  unfold evalAt
  rw [foldl_eval]; simp

/-! ## The certificates -/

/-- The conditions checked by `checkParsed`, unpacked. -/
theorem checkParsed_spec {c : Cert} (hc : checkParsed c = true) :
    (∀ p ∈ c.gens ++ c.cofs ++ [c.h], ∀ t ∈ p, keyBounded (6 + c.nvar) t.1 = true) ∧
    (∀ t ∈ c.h, t.1 < 256 ^ 6) ∧
    (normalize ((List.zipWith mulRaw c.cofs c.gens).flatten ++ neg c.h)).isEmpty = true ∧
    evalAt 6 (hPoint c.fixed) c.h ≠ 0 := by
  unfold checkParsed at hc
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hkb⟩, _⟩, hh⟩, hn⟩, hz⟩ := hc
  exact ⟨fun p hp t ht => hkb p hp t ht, fun t ht => hh t ht, hn, hz⟩

/-- **Soundness of a certificate (vanishing).** If a parsed certificate passes `checkParsed`, then in every
commutative ring, at every assignment at which all generators vanish, `h` vanishes. -/
theorem checkParsed_vanish {c : Cert} (hc : checkParsed c = true) {R : Type*} [CommRing R] (φ : ℕ → R)
    (hg : ∀ g ∈ c.gens, eval (6 + c.nvar) φ g = 0) : eval (6 + c.nvar) φ c.h = 0 := by
  obtain ⟨hkb, -, hn, -⟩ := checkParsed_spec hc
  have hsmall : ∀ p ∈ c.cofs ++ c.gens, ∀ t ∈ p, SmallKey (6 + c.nvar) t.1 := by
    intro p hp t ht
    refine smallKey_of_keyBounded (hkb p ?_ t ht)
    rcases List.mem_append.mp hp with hp | hp <;> simp [hp]
  have h0 : eval (6 + c.nvar) φ (normalize ((List.zipWith mulRaw c.cofs c.gens).flatten ++ neg c.h)) = 0 := by
    rw [List.isEmpty_iff.mp hn]; rfl
  rw [eval_normalize, eval_append, eval_neg, eval_combination _ φ _ _ hsmall] at h0
  have hz : (List.zipWith (fun a b => eval (6 + c.nvar) φ a * eval (6 + c.nvar) φ b) c.cofs c.gens).sum = 0 := by
    have := sum_zipWith_eq_zero (c.cofs.map (eval (6 + c.nvar) φ)) (c.gens.map (eval (6 + c.nvar) φ))
      (fun g hg' => by
        obtain ⟨g', hg'', rfl⟩ := List.mem_map.mp hg'
        exact hg g' hg'')
    rw [List.zipWith_map] at this
    exact this
  rw [hz, zero_add, neg_eq_zero] at h0
  exact h0

/-- `h` involves only the masses: its value depends only on the first six variables. -/
theorem eval_h_masses {c : Cert} (hc : checkParsed c = true) {R : Type*} [CommRing R] (φ : ℕ → R) :
    eval (6 + c.nvar) φ c.h = eval 6 φ c.h := by
  obtain ⟨-, hh, -, -⟩ := checkParsed_spec hc
  unfold eval
  congr 1
  refine List.map_congr_left fun t ht => ?_
  congr 1
  unfold monoEval
  rw [prod_range_add]
  have : ∏ i ∈ range c.nvar, φ (6 + i) ^ keyExp t.1 (6 + i) = 1 := by
    refine prod_eq_one fun i _ => ?_
    have hlt := hh t ht
    have : keyExp t.1 (6 + i) = 0 := by
      rw [keyExp_eq_div]
      have : t.1 / 256 ^ (6 + i) = 0 := by
        apply Nat.div_eq_of_lt
        calc t.1 < 256 ^ 6 := hlt
          _ ≤ 256 ^ (6 + i) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [this]
    rw [this, pow_zero]
  rw [this, mul_one]

/-- **Soundness of a certificate (nonzero).** `h` is nonzero at the integer point `hPoint F`. -/
theorem checkParsed_nonzero {c : Cert} (hc : checkParsed c = true) :
    eval 6 (fun i => (hPoint c.fixed).getD i (0 : ℤ)) c.h ≠ 0 := by
  obtain ⟨-, -, -, hz⟩ := checkParsed_spec hc
  rwa [evalAt_eq] at hz

/-- **Soundness of a certificate text.** If `checkCert s` passes, `s` parses to a certificate whose `h` involves only
the masses, vanishes wherever all generators vanish (in every commutative ring), and is nonzero at `hPoint F`. -/
theorem checkCert_sound {s : String} (hs : checkCert s = true) :
    ∃ c, parseCert s = some c ∧
      (∀ {R : Type} [CommRing R] (φ : ℕ → R), (∀ g ∈ c.gens, eval (6 + c.nvar) φ g = 0) → eval 6 φ c.h = 0) ∧
      eval 6 (fun i => (hPoint c.fixed).getD i (0 : ℤ)) c.h ≠ 0 := by
  unfold checkCert at hs
  cases hp : parseCert s with
  | none => simp [hp] at hs
  | some c =>
    simp only [hp] at hs
    exact ⟨c, rfl, fun φ hg => by rw [← eval_h_masses hs φ]; exact checkParsed_vanish hs φ hg,
      checkParsed_nonzero hs⟩

/-- **The meaning of a certificate** (the interface shared with later versions): `h` vanishes, in every commutative
ring, wherever all generators vanish, and `h` is nonzero at the integer point `hPoint F`. -/
def CertMeaning (c : Cert) : Prop :=
  (∀ {R : Type} [CommRing R] (φ : ℕ → R), (∀ g ∈ c.gens, eval (6 + c.nvar) φ g = 0) → eval 6 φ c.h = 0) ∧
  eval 6 (fun i => (hPoint c.fixed).getD i (0 : ℤ)) c.h ≠ 0

/-- A parsed certificate that passes `checkParsed` has its meaning. -/
theorem checkParsed_meaning {c : Cert} (hc : checkParsed c = true) : CertMeaning c :=
  ⟨fun φ hg => by rw [← eval_h_masses hc φ]; exact checkParsed_vanish hc φ hg, checkParsed_nonzero hc⟩

/-- A certificate text that passes `checkCert` parses to a certificate with its meaning. -/
theorem checkCert_meaning {s : String} (hs : checkCert s = true) : ∃ c, parseCert s = some c ∧ CertMeaning c := by
  unfold checkCert at hs
  cases hp : parseCert s with
  | none => simp [hp] at hs
  | some c =>
    simp only [hp] at hs
    exact ⟨c, rfl, checkParsed_meaning hs⟩

end L6.Poly
